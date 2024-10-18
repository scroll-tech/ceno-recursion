# Register Allocation

This document records some thoughts about how to implement register allocation in circ_blocks

## Difference from Traditional Register Allocation

Traditional register allocation records the live range of every register, constructs an inteference graph, and solves a coloring problem. This is not necessarily the best approach for circ_blocks for the following reasons:

1. In circ_blocks, we don't have an explicit upper bound on number of registers. Moreover, we want the number of registers to be close to specific values, i.e. when adding in reserved registers should be close to a power of 2 (??? Debatable, since number of witnesses might still be much larger).
2. We only care about the **number of registers** during block transition (??? Debatable, since number of witnesses also matter). For instance, if block 0 initiates a new scope (a@0 -> a@1), and the subsequent block 1 exits the scope (a@1 -> a@0), it doesn't matter which of a@0 / a@1 got pushed onto the stack.
3. For each block, the input variables and output variables are stored separately in the witnesses. As a result, there is no need to force the same variable in the input & output to use the same register.
4. Stack is write-once, so we need to worry about stack coherence: i.e. can we still make sure %SP and %BP are correct?

## Proposed Solution without Spilling

Disregarding spilling, the minimum number of registers we need is the maximum number of live variables _in scope_ during a block transition, plus the number of reserved registers (??? Can we remove these as well?). Moreover, since input variables and output variables are unrelated within each block, we can perform register allocation separately on the inputs and outputs of a block.

However, what needs to be considered is the block transition. If block 1 precedes block 2, then the Var -> Reg Map needs to be the same for the OUTPUT 1 and the INPUT 2. If block 3 also precedes block 2, then the Var -> Reg Map of OUTPUT 3 should also match OUTPUT 1. We call one such set of input / output states a _transition state_. The strategy is thus to define one Var -> Reg Map per transition state, as well as program input / output.

## From Continuation Passing to Revserse Spilling

Due to the write-once nature of memory, spilling becomes a difficult task. This is because the write-once restriction forces memory to operate like a stack simulation (see stack_simulation.md), with explicit stack and base pointer. To illustrate the problem, consider a control-flow sequence of block A -> B -> C -> D. Suppose that variable X is used in A and C, while variable X is used in B and D, one cannot spill X at A and load at C, while simultaneously spill Y at B and load Y at D, since this breaks the stack simulation. As a result, scope change + continaution passing should remain the main method to limit the number of variables in the transition state.

Instead of reasoning about spilling, we reason about **reverse spilling**, where we attempt to avoid continuation passing by renaming variables. The main motivation is that since the I/O width is the same across all blocks, any transition state that does not fully utilize the width is wasted. In the case that the width is unfulfilled, we should include variables in previous scopes to reduce memory accesses.

### General Approach & Challenges

To motivate the framework below, we begin by setting up a general approach:
1. During block generation, rename variables on scope change to avoid any continuation passing, with the only exception of spilling `%RP` before a function call.
2. After liveness analysis, determine the I/O width as well as every spill candidate.
3. Rank every spill candidate by the number of transition states they are spillable in. Continually picking and removing the candidates with the top rank until size of every transition state is within I/O width.
4. Finally, traverse through the program and insert `PUSH` and `POP` instructions to spill all picked candidates.

The major challenge to this approach is that a spill candidate does not correspond to one variable, but rather one _location_ of a variable. To illustrate, see the following example:
```python
int a0 = 0
{
  int a1 = 0
  # TRANSITION 1: a.0, a.1
  ...
}
{
  int a1 = 1
  # TRANSITION 2: a.0, a.1
  ...
}
```
In this example, `a0` is shadowed by `a1` in both transition 1 and transition 2 and thus is a spill candidate in both blocks. However, these two spills can be performed independently. It might be the case that only the transition 1 exceeds io width, and so `a0` only needs to be spilled in transition 1.

This example shows that one cannot simply use the candidate name (i.e. `a0`) to mark spill candidates. Further remark that SSA would not solve the problem in the example either. Rather, each shadowing of the variable in a new scope results in a _new location_ where the variable can be spilled. We denote each candidate as `(variable, location)`, and transform the above example to:
```python
int a0 = 0
{
  int a1.loc0 = 0
  # TRANSITION 1: a.0, a.1.loc0
  ...
}
{
  int a1.loc1 = 1
  # TRANSITION 2: a.0, a.1.loc1
  ...
}
```
In transition 1, the spill candidate is `(a0, loc0)` and in transition 2, the candidate is `(a0, loc1)`. The two spill candidates are now distinguishable.

This relationship between variables and locations also manifest as the difference between spilling a variable and removing it from the transition states. To demonstrate, consider the following example:
```python
int a0 = 0
{
  int a1.loc0 = 0
  foo()
  ...
}
{
  int a1.loc1 = 1
  foo()
  ...
}
```
There are three variables alive in the function `foo`: `a0, a1.loc0, a1.loc1`, and two spill candidates: `(a0, loc0)` and `(a0, loc1)`. However, spilling the candidate `(a0, loc0)` does not remove `a0` from the transition state, because `a0` is still in scope when called from `loc1`. Similarly, only spilling `(a0, loc0)` is also insufficient. Thus, a variable should only be removed from the transition state if **it is spilled in all locations**.

### A Framework with Static Analysis

With the above challenges in mind, we incorporate Static Analysis into our general approach to provide a detailed framework:
1. During block generation
  - Rename variables on scope change to avoid any continuation passing, with the only exception of spilling `%RP` before a function call
  - For every variable, append its function name, scope, and location to it. e.g. `a -> main.a1.0`
2. A liveness analysis computes the set of live variables for each **transition state (TS)**. 
3. After liveness analysis
  - Iterate through all transition states to obtain the **io width**, defined as the maximum number of variables alive & in-scope within a TS.
  - For each TS, define its **spill size** as (number of live variables - io_width).
  - A forward analysis to find all spill candidates:
    - STATE: set of all spilled variables in the form of `(candidate, location)`, where
      - `location` also includes scope information of when the spill should be popped
    - GEN:
      - When a variable is declared and _alive by the end of the block_, if it shadows any candidates that are _alive by the end of the block and not spilled_, add `(candidate, location)` to program state.
      - When a function is called, for every variable that is _alive by the end of the function call and not spilled_, add `(candidate, location)` to program state
    - KILL: Every time a scope is exited, check all spilled variables. If `location` of any candidate no longer matches the scope, pop the spilled variable.
    - JOIN: states are joined through set union
  - At the end of the forward analysis, we obtain a list of spill candidates for every transition state.
5. To rank the spill candidates, we repeat the following process until spill size is 0 for all transition states
  - Use a list `spills` to keep track of the candidates that are selected to be spilled
  - Iterate through all transition states and keep track of how many times each spill candidate appears.
  - Add the candidate with the most appearance to `spills`, remove the candidate from all transition states, recompute the size of the TS and spill size
6. One final static analysis **on each function separately**:
    - STATE: the entire memory stack, including variables and types
    - GEN:
      - When a variable is declared and _alive by the end of the block_, if it is a location in `spills` and any variables it shadows is not in stack and alive by the end of the block, insert PUSH statement and add the variable to stack
      - When a function is called and if it is a location in `spills`, for every variable it shadows that is _alive by the end of the function call and not spilled_, insert PUSH statement and add the variable to stack
    - KILL: Every time a scope is exited, pop the stack and restore the variables using POP statements accordingly.