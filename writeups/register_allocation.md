# Register Allocation

This document records some thoughts about how to implement register allocation in circ_blocks

## Difference from Traditional Register Allocation

Traditional register allocation records the live range of every register, constructs an inteference graph, and solves a coloring problem. This is not necessarily the best approach for circ_blocks for the following reasons:

1. In circ_blocks, we don't have an explicit upper bound on number of registers. Moreover, we want the number of registers to be close to specific values, i.e. when adding in reserved registers should be close to a power of 2 (??? Debatable, since number of witnesses might still be much larger).
2. We only care about the number of registers during block transition (??? Debatable, since number of witnesses also matter). For instance, if block 0 initiates a new scope (a@0 -> a@1), and the subsequent block 1 exits the scope (a@1 -> a@0), it doesn't matter which of a@0 / a@1 got pushed onto the stack.
3. For each block, the input variables and output variables are stored separately in the witnesses. As a result, there is no need to force the same variable in the input & output to use the same register.
4. Stack is write-once, so we need to worry about stack coherence: i.e. can we still make sure %SP and %BP are correct?

## Proposed Solution

Disregarding spilling, the minimum number of registers we need is the maximum number of live variables during a block transition, plus the number of reserved registers (??? Can we remove these as well?). Moreover, since input variables and output variables are unrelated within each block, we can perform register allocation separately on the inputs and outputs of a block.

However, what needs to be considered is the block transition. If block 1 precedes block 2, then the Var -> Reg Map needs to be the same for the OUTPUT 1 and the INPUT 2. If block 3 also precedes block 2, then the Var -> Reg Map of OUTPUT 3 should also match OUTPUT 1. We call one such set of input / output states a _transition state_. The strategy is thus to define one Var -> Reg Map per transition state, as well as program input / output.

## From Continuation Passing to Revserse Spilling

Due to the write-once nature of memory, spilling becomes a difficult task. This is because the write-once restriction forces memory to operate like a stack simulation (see stack_simulation.md), with explicit stack and base pointer. To illustrate the problem, consider a control-flow sequence of block A -> B -> C -> D. Suppose that variable X is used in A and C, while variable X is used in B and D, one cannot spill X at A and load at C, while simultaneously spill Y at B and load Y at D, since this breaks the stack simulation. As a result, scope change + continaution passing should remain the main method to limit the number of variables in the transition state.

Instead of reasoning about spilling, we reason about **reverse spilling**, where we attempt to avoid continuation passing by renaming variables. The main motivation is that since the I/O width is set, any transition state that does not fully utilize the width is wasted. In the case that the width is unfulfilled, we should pass variables in previous scopes to reduce memory accesses.

### A general framework

To facilitate reverse spilling, we propose that stack operations should only be added at the end of optimization, not at the beginning. In particular,
* During block generation, variables of **every scope of every function** should be assigned a different suffix. This includes different scopes that have the same depth.
* During initial optimization, we add every live variable of every scope to the input / output of each block.
* Once liveness analysis / dead block elmination concludes, infer the minimum io width: i.e. the number of variables in the transition state if all older scopes of a variable is spilled.
* Next for each block whose input / output size exceeds io width, decide what variable of the older scope to spill, based on:
  * If we want to spill a variable, always spill the one with the oldest scope
  * If we want to choose between variables, always spill the one that is used across most block input / outputs
  * Note: two variables are considered the same across multiple blocks if:
    1. They share the same scope number
    2. The same variable of the next scope also share the same scope number