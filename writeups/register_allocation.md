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

## The Case to Preserve Continuation Passing