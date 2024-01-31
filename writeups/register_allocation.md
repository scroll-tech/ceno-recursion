# Register Allocation

This document records some thoughts about how to implement register allocation in circ_blocks

## Difference from Traditional Register Allocation

Traditional register allocation records the live range of every register, constructs an inteference graph, and solves a coloring problem. This is not necessarily the best approach for circ_blocks for the following reasons:

1. In circ_blocks, we don't have an explicit upper bound on number of registers. Moreover, we want the number of registers to be close to specific values, i.e. when adding in reserved registers should be close to a power of 2 (??? Debatable, since number of witnesses might still be much larger).
2. We only care about the number of registers during block transition (??? Debatable, since number of witnesses also matter). For instance, if block 0 initiates a new scope (a@0 -> a@1), and the subsequent block 1 exits the scope (a@1 -> a@0), it doesn't matter which of a@0 / a@1 got pushed onto the stack.
3. Stack is write-once, so we need to worry about stack coherence: i.e. can we still make sure %SP and %BP are correct?

## Analysis

1. There is no reason why a variable name should be assigned multiple registers.

## Solutions

### Simpliest Solution

Keep the scoping stack as is, liveness analysis on variables with different names, allocate the first empty register when encountering a new variable -- this might be good enough.

### More Complicated Solution

Keep track of the distance till the next reference of each scope of each variable. Push those longer ones onto stack.
Q: How to keep track of the stack?