# Bound the Number of Proofs

One challenge for circ_blocks is to bound the number of proofs in the backend, ie. bound the total number of block executions for any program. This value determines the size of numerous instances in the backend. Since the opening of commitment is square root to the size of the instance, even a constant factor reduction on the bound can substantially improve prover and verifier time. Below we investigate several different approaches to solve this problem.

## Assumptions
There are two assumptions we need to take:
1. There are no function pointer. Thus, for every function call, the function to be called is known and the value of the return block is also known.
2. There are no `jump` or `goto` statements. There is also no recursion.
3. The bound on the number of iterations for every loop is known. This can be achieved through either impose limitations on what kind of loops are accepted, or allow programmer to manually specify the upper bound of a given loop.

## Naive Approach #1
Our first naive approach can summarized as: bound the number of executions of each block separately, and add them up altogether. This is further divided into three steps:
* During block generation, the generator use loop information to bound the number of executions of each block _during one execution of the function_.
* During optimization, the optimizer uses CFG information on function calls to bound the number of executions of each function and subsequently the total number of executions of each block.
* Finally, circ_blocks sums up the total number of executions of each block to obtain the final number of proofs bound.

One can see that this approach is extremely simple. However, it fails to take branching into consideration. Whenever we encounter an if / else statement, only one of the branches can be executed. To address this issue, we introduce the following approaches.

## Naive Approach #2
Our second approach is a slight improvemne upon the first one. We preserve the first two steps of Approach #1 to obtain the total number of executions of each block. Next, we use a DP algorithm that records, for each block `b`:
* The path from `b` to any program exit block that results in the most executions of blocks. In particular, the set of blocks that are on the path.
* Sum over the total number of executions of each block in the set.
We run a DP algorithm that starts from the program exit blocks. For every block it processes, it finds the successor with the most number of executions sum, and sets its path to be itself appended to the path of that successor. After some handling of loops, we set total number of proofs to be the number of executions sum of the program entry block.

At a glance, it seems like this approach solves the problem: for every branching, the block preceeds the if / else statement can only pick either the successor representing the if branch or the successor representing the else branch. However, this observation no longer hold when the branching statement is present inside a loop. The branching can go either way for different iterations, but what we really want is for every iteration to always pick the more "expensive" branch.

## Approach #3
It seems clear from the shortcoming of approach #2 that we should start by thinking about loops. The easiest way to deal with it is surprisingly, ignore it. The reason is that, when bounding the total number of execution of a block within a function, the number of iterations is already taken into consideration, so there is no need for loops. This derives the following strategy:
* Eliminate all loops of the CFG
* Perform Naive Approach #2 on the loopless CFG
> **Note**: one might be tempted to run DFS on the CFG to remove backedges. However, this is both incorrect and unnecessary. Incorrect because under different traverse rules, backedges might not be equal to the returning edge in a loop. Unnecessary because the way blocks are generated ensures that returning edge in a loop always start from a block with a higher label to one with a lower label.

Wait, but what about function calls? Recall that how we bound the number of executions of each block is: `number of executions within the function * number of executions of the function`. However, number of executions of the function itself can be subject to the branching problem. Furthermore, even the most precise function execution bound is not good enough. To illustrate, consider the following case:
> There are two functions A and B. In the if branch, A is executed 3 times while B is executed 5 times. In the else branch, A is executed 5 times and B is executed 3 times.
Both A and B have execution bound as 5, but in no case would both functions be executed 5 times.

Note that this is not an issue for individual blocks, because the lack of `jump` statements ensures that no block will be executed in both an if branch and an else branch.

## Approach #4
To take function calls into consideration, we revise the above approach:
* Differentiate between function call edges, function return edges, and normal transition edges.
* Perform a topological sort on all functions based on call graph.
* Starting from the function on top of the top sort:
  * Similar as the DP algorithm described in Approach #3, start from the function exit block and process in reverse order:
    * For every block, only record the maximum number of block executions until _the end of the function_.
    * For any caller block to another function, by definition of top sort, that function must have already been processed. The maximum number of block execution `M_b` is given by
      `M_b = M_h * E_b + M_r`
      where `M_h` is the maximum number of block execution at the callee function header, `E_b` is the number of executions of the caller, and `M_r` is the maximum number of block execution at the return block of the function.
  * Only process its predecessors **in the function** if values of the block have been changed. If the block is only reachable from another function, process the caller block of that function.
  * Once a function is processed, obtain the total number of proofs during one execution of the function at the function entry block.
* Finally, obtain total number of proofs through the entry block.

## Note:
This still does not give us a 100% tight upperbound. The reason is that in a loop, a branch might never be taken by all iterations (e.g. condition on parity of the iteration counter).