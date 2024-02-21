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

The major challenge to this approach is that one variable does not correspond to one spill candidate. To illustrate, see the following example:
```python
int a.0 = 0
{
  int a.1 = 0
  # TRANSITION 1: a.0, a.1
  ...
}
{
  int a.1 = 1
  # TRANSITION 2: a.0, a.1
  ...
}
```
In this example, `a.0` is shadowed by `a.1` in both transition 1 and transition 2 and thus is a spill candidate in both blocks. However, these two spills can be performed independently. It might be the case that only the transition 1 exceeds io width, and so `a.0` only needs to be spilled in transition 1.

This example shows that one cannot simply use the candidate name (i.e. `a.0`) to mark spill candidates. Further remark that SSA would not solve the problem in the example either. Instead, we introduce the _version number_ everytime a variable is defined in a new scope. Furthermore, each spill candidate is now denoted as `(shadower, candidate)`, where `shadower` is the variable that shadows the candidate. The above example is now transformed to:
```python
int a.0.0 = 0
{
  int a.1.0 = 0
  # TRANSITION 1: a.0.0, a.1.0
  ...
}
{
  int a.1.1 = 1
  # TRANSITION 2: a.0.0, a.1.1
  ...
}
```
In transition 1, the spill candidate is `(a.1.0, a.0.0)` and in transition 2, the candidate is `(a.1.1, a.0.0)`. The two spill candidates are now distinguishable.

The above problem is further complicated by the usage of function calls, where the removal of a spill candidate does not always correspond to the removal of a live variable in a transition state. To demonstrate, consider the following example:
```python
int a.0.0 = 0
{
  int a.1.0 = 0
  foo()
  ...
}
{
  int a.1.1 = 1
  foo()
  ...
}
```
There are three variables alive in the function `foo`: `a.0.0, a.1.0, a.1.1`, and two spill candidates: `(a.1.0, a.0.0)` and `(a.1.1, a.0.0)`. However, removing the candidate `(a.1.0, a.0.0)` does not remove `a.0.0` from live variables, because `a.0.0` is still alive during a different function call, i.e. the one that produced the spill candidate `(a.1.1, a.0.0)`. However, not spilling `(a.1.0, a.0.0)` also leads to `a.0.0` always being alive. Thus extra caution needs to be made on how to quantify the effect of spilling `(a.1.0, a.0.0)`.

### A Framework with Static Analysis

With the above challenges in mind, we incorporate Static Analysis into our general approach to provide a detailed framework:
1. During block generation
  - Rename variables on scope change to avoid any continuation passing, with the only exception of spilling `%RP` before a function call
  - For every variable, append its function name, scope, and version to it. e.g. `a -> a.main.1.0`
2. After liveness analysis
  - Iterate through all transition states to obtain the io width as well as the spill size (number of live variables - io_width) for every transition state.
  - A forward analysis to find all spill candidates:
    - STATE: set of all spilled variables in the form of `(shadower, candidate, pop_info)`, where `pop_info` indicates when to pop the spilled variable out
      - `shadower` is either a variable name or a function name
    - GEN:
      - When a variable is declared and _alive by the end of the block_, if it shadows any variables that are _alive by the end of the block and not spilled_, add `(shadower, candidate, pop_info)` to program state.
      - When a function is called, for every variable that is _alive by the end of the function call and not spilled_, add `(callee_name, candidate, pop_info)` to program state
    - KILL: Every time a scope is exited, check all spilled variables. If `pop_info` of any candidate matches the new scope, pop the spilled variable.
      - For simplicity, we assume that there is always a block per scope during scope changes.
  - At the end of the forward analysis, we obtain a list of spill candidates for every transition state.
3. To rank the spill candidates, we repeat the following process until spill size is 0 for all transition states
  - Use a list `spills` to keep track of the candidates that actually will be spilled
  - Iterate through all transition states and keep track of how many times each spill candidate appears.
  - Add the candidate with the most appearance to `spills`, remove the candidate from all transition states, recompute the number of live variables and spill size
4. One final static analysis **on each function separately**:
    - STATE: the entire memory stack, including variables and types
    - GEN:
      - When a variable is declared and _alive by the end of the block_, if it is a shadower in `spills` and any variables it shadows is not in stack and alive by the end of the block, insert PUSH statement and add the variable to stack
      - When a function is called and if it is a shadower in `spills`, for every variable it shadows that is _alive by the end of the function call and not spilled_, insert PUSH statement and add the variable to stack
    - KILL: Every time a scope is exited, pop the stack and restore the variables using POP statements accordingly.