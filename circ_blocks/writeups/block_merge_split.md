# Merge Basic Blocks

This documents discusses the motivation & implementation of merging basic blocks.

## Motivation

The motivation for merging & splitting basic blocks originates from the observation that length of basic block varies. However, the backend requires the size of the instance for each block to be fixed. Since the runtime of the sumcheck protocol is proportional to the size of the largest instance, any gap between block size & instance size constitutes a "waste" in computation. There are two ways to reduce this gap:
1. Splitting basic blocks: Split the largest blocks into multiple chunks, reducing the size of the largest instance. This is the unpreferred method since the addition of each block adds a new transition state and thus adds to the cost of consistency check & permutation. Furthermore, splitting a block might result in previously intermediate witnesses being added to transition states, further add to the cost of consistency & permutation.
2. Merging basic blocks: Merge smaller blocks to increase their size. This is the more difficult approach but is more effective. If done correctly, block merges can reduce the number of transition states without modifying the contents within each one. However, merging basic blocks requires knowledge on structure and potentially semantics of the whole program. **In this document, we focus on merging basic blocks.**

## Preliminaries & Assumptions
We base the process on a few assumptions:
1. The number of constraints corresponding to each block can be easily obtained. At worst case we translate blocks into constraints and count, so this assumption is reasonable.
2. The program has limited structure: i.e., no pointer, jumps, or recursion. This assumption is already employed by other analyses.

We choose to perform block merges immediately before register spilling, since spilling introduces memory operations that would complicate the merge process. Furthermore, block merges would inevitably introduce branching within each block, which would complicate traditional analyses like liveness and alias, and thus should be placed after them.

## Merge Component
The key idea behind block merge is the concept of a **merge component**. A component is consisted of a set of blocks, which includes a **head** block that domintes, and a **tail** block that post-dominates every block in the component. Intuitively, once a component head is executed, the component tail is guaranteed to be executed, and every block executed between the head and the tail will be in the component. Finally, to facilitate spilling, we require the head and the tail to be _of the same scope_.

The concept of merge component aligned well with the simple code structure presented by ZoKrates. In particular, every branching and loop statement naturally form a merge component. However, there are two notable exceptions where a component does not exist:
1. The program / function returns before the end of the loop / branch
2. The loop / branch invokes a function call
In both cases, _any loop or branching_ that involves return or function call can no longer be considered merge components.

## The Merge Process
The implementation of block merges can be viewed as a three-stage process:
1. Iterate through the blocks and estimate the number of constraints for each block
2. A backward analysis to find all merge components as well as the number of constraints fo each component
3. For each component with fewer constraints than the _merge threshold_, merge the component and update component graph

### Estimate Constraints & Merge Threshold
Currently, the number of constraints for each block is obtained by simply converting them into R1CS and count. Once we obtain these numbers, merge threshold is computed as
```rust
THRESHOLD = max(MIN_BLOCK_SIZE, max(num_constraints).next_power_of_two())
```
where `MIN_BLOCK_SIZE` is set to 1024.

### Find Merge Components & Their Size
We observe that every (head, tail) pair, if valid, uniquely defines a component. Furthermore, for every block $b$, there is at most one component where $b$ is the component head. Thus, all components of a program can be represented using the following data structure:
> For every block, there exist a component where it is the head, mark with the label of the tail block, otherwise mark with NAC

To obtain the tail labels, we perform a backward analysis within each function, with:
- STATE: tail blocks of every scope. If the scope is higher than the scope of the block, set it to BOT.
- JOIN: similar to element-wise constant propagation.
  - For every successor, replace **its** component tail with itself, and then perform element-wise join.
- GEN: GEN is implied by JOIN
- KILL: KILL is also largely implied by JOIN, with the exception of a function call. During if the block is a caller to a function, set every entry of the state to BOT.

We further record the number of constraints for each block through two more states: `count` and `agg_count`:
- STATE: `count` records the number of constraints for the current component, `agg_count` records the number of constraints for the previous component
- JOIN:
  - `count[i] = num_constraints[i] + sum(count[s] * num_iteration[s]) + num_constraints[t]`, where `i` is the current block, `s` are all successors with higher scope than the current block, and `t` is the tail of the component. If `t` does not exist, `count[i] = 0`
  - `agg_count[i] = num_constraints[i] + sum(count[s]) + agg_count[t]`. If `t` does not exist, `agg_count[i] = num_constraints[i]`

Finally, we can obtain the size of each component through `count[component_head]`.

### Merge Blocks
The final step is to perform the actual merge. This step is very similar to counting the size of the components, except:
1. We only want to compute program states that are in the component we want to merge, to prevent space usage
2. When unrolling a loop, we not only want to unroll the content of the loop, but also the condition, which requires some assumptions on the shape of the terminator.

The exact protocol is as follows:
Repeat the below process until no more merge is performed:
- Iterate through the blocks, if the size of the merge component (if exist) < merge threshold start backward analysis from the component tail:
  - STATE: list of merged instructions
  - JOIN: convert the block terminator to a conditional statement.
    - For every branch, if the corresponding block is of a higher scope, add the merged instructions of the block to the branch
    - If the corresponding block is in a loop, assert that the other branch must _not_ be of a higher scope. If so, copy the instruction together with the branch condition number of iteration times.
    - Append the state of the next block of the curret scope (tail of the sub-component) to the end of the conditional statement.
- If a component is produced:
  - Replace the instructions in the head with the component
  - Replace the terminator of the head with the terminator of the tail
  - Mark everything else in the component as dead
  - If tail is the head of another component, head is now the head of the component. Recompute number of constraints of that component

## Other Notes
During the implementation of block merge, we made the following modifications:
1. Every loop now has an explicit head and tail, both set to be empty. These will be eliminated later.
2. Since conditional statements imply scoping, we can no longer set every definition to be typed definition. A pass at the end of all analysis reverts all _fake_ typed definition back to assignee.