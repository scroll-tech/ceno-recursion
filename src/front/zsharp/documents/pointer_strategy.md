# Stack Simulation

This file demonstrates the stack construction (simulation) in the current circ block system.

## Preliminaries

There are three factors that contributes to the current stack construction:

1. There are infinitely many registers, which can represent infinitely many variables, as long as they have a unique identifier. 

    This implies that we don't need to store every local variable onto the stack.

2. We use continuation passing, so there are no ways to explicitly handle scopings.

    This implies that we need to use stack frame not just for function calls, but also scoping change.

3. Every cell in RAM is write-once, meaning that once a cell is occupied, its content cannot be altered.

    This means that we cannot `pop` a stack, and consequently the entire concept of stack needs to be simulated.

NOTE: Stack frame is *NOT* related to blocks. While most push / pops occur during block transition, this is not always the case. From now on I'll avoid mentioning the term "block".

## Redefine Stack Frame

The first step is to alter the definition of stack frame. We define 3 operations related to a stack:

1. `init` initializes a new stack frame. It pushes the current base pointer (`%BP`) onto the stack and updates `%BP` to point to that address. More about `%BP` later.
2. `push` pushes a value (persumably from a variable) onto the stack. It does not alter stack frame.
3. `pop` reads a value from the stack frame. Generally speaking all values of a stack frame are popped out at the same time, including `%BP`. In this example we use `pop` to mean popping out everything in the current stack frame.

In traditional x86 / ARM definition, each stack frame corresponds to a function call. For instance, if A calls B and B calls C, we would expect 3 frames, corresponding to A, B, C. In circ block, however, due to the lack of explicit scoping, we need a stack frame for each scope we have. Specifically, an `init` occurs either:
* AFTER we enter a new scope, or
* RIGHT BEFORE we call a function

and `pop` occurs either:
* RIGHT BEFORE we exit a scope, or
* RIGHT AFTER we return from a function call, before assigning the return value

and `push` only occurs:
* when we redefine an existing variable in a new scope, push the old value of the variable onto stack
* when we prepare to enter a function call, push the value of EVERY variable onto stack, after `init` and before handling function arguments

Generally speaking, stack frames generated from scoping changes and function calls look different. In this case, we argue that if `init`, `push`, and `pop` are done correctly, then the procedure is sound:

1. A new scope within the same function can only be entered from and exited to the same outer scope. As a result,
    
    - when we are in any scope, we know exactly what variables have been defined in the outer scope, so we can `init` inside the scope.
    - after a variable is redefined in the current scope, any changes to it is unrelated to the outer scope, so we can `pop` before exiting the scope.

    And from the perspective of the outer scope, its variables have never been redefined by the inner scope, which is exactly what we want.

2. During the period after a function call and before its return value is assigned to a variable, NO value of the variables in the current function will be altered, so we can safely `push` them before func call and `pop` them afterwards.

## Stack Frame Content

As stated above, each stack frame is consisted of:

index | content
--|------
0 | `%BP`
1 | other variables
2 | ...

## Stack and Base Pointers

As discussed early, despite the name `pop`, we cannot actually pop the stack since it is write-once. Instead, we use two pointers `%SP` and `%BP` to simulate `push` and `pop`:

- `%SP` always points to the address that marks the beginning of the *newest* stack frame. Since the size of the RAM (stack) can only grow, `%SP` cannot be decremented.

- `%BP` always points to the address that marks the beginning of the *current* stack frame. Note that `%BP` matches with `%SP` most of the time, but their values differ between a `pop` and the next `init`.

The two pointers are handled in the following process:

1. At the beginning of the program, set `%SP = 0; %BP = 0`.

2. `init` can be expressed as: `MEM[%SP] = %BP; %BP = %SP; %SP++`

3. `push x` can be expressed as: `MEM[%SP] = x; %SP++`

4. We can consolidate multiple `%SP++` into one. e.g. `init; push x; push y` can be `MEM[%SP] = %BP; %BP = %SP; MEM[%SP + 1] = x; MEM[%SP + 2] = y; %SP += 3`.

5. We don't have to do `%SP += ?` until the next `init` or `pop`, so let's append `%SP += ?` to the beginning of `init` and `pop`.

6. We don't need to do `init` unless we encounter a `push x`, so we can combine them to `if (first push of the stack frame) do init; push x`. So `init` only needs to handle `%SP += ?`.

Now, for every scope, define a variable `offset` initialized to 0 to record the difference between the value of `%SP` and the actual size of RAM. Note that `offset = 0` means that no `push` has occurred in the current stack frame. Furthermore, record a mapping `var_assg` from each offset value to name of the corresponding variable stored in stack. Stack operations will now look as follows:
```
// INIT UPDATE
if offset > 0
    WRITE "%SP += <offset>"
    offset = 0
endif

// MAYBE INIT; PUSH X
if offset == 0
    WRITE "MEM[%SP] = %BP"
    WRITE "%BP = %SP"
    offset += 1
    var_assg ++ (0, "%BP")
endif
WRITE "MEM[%SP + <offset>] = X"
offset += 1
var_assg ++ (offset, "X")

// POP
call UPDATE
for pair in var_assg.reverse()
    WRITE "MEM[%BP + <pair.offset>] = <pair.var_name>"
endfor

// replace every "init" with INIT UPDATE
// replace every "push X" with MAYBE INIT; PUSH X
```

(I know this is ugly, but you'll see why.)

Note:
*  `<offset>`, a constant, is the value of `offset` at the point of invocation. Same for `<pair.offset>` and `<pair.var_name`>.
* We need to load `var_assg` out in reverse so that `%BP` is updated last.
* We can't eliminate `pop` even if `offset = 0`. The reason is shown by the next section.

To prove the above set up is correct, we need to talk about the issue below first.

## Multiple Stack Frames within the Same Scope

The above setup implicitly solves an issue, which is nevertheless worth mentioning. We demonstrate it using the following example:

```
 1 def main() -> field:
 2     field a = 5
 3     field b = 4
 4     for field i in 0..X do
 5         field a = 10
 6         for field j in 0..Y do
 7             field a = 20
 8         endfor
 9         field b = 20
10     endfor
11     return a + b
```
where `X` and `Y` are unknown at compile time.

The example is converted to:
```
 1 def main() -> field:
       INIT UPDATE
 2     field a = 5
 3     field b = 4
 4     for field i in 0..X do
           INIT UPDATE
           MAYBE INIT; PUSH a 
 5         field a = 10
 6         for field j in 0..Y do
               INIT UPDATE
               MAYBE INIT; PUSH a
 7             field a = 20
               POP
 8         endfor
           MAYBE INIT; PUSH b
 9         field b = 20
           POP
10     endfor
11     return a + b
```
One might naively conclude that there are 3 stack frames in the code, corresponding to the 3 `INIT UPDATE`. However, note that `PUSH a` on line 4 and `PUSH b` on line 8, despite being in the same scope, do not occupy consecutive addresses in the memory, as they are separated by the stack frame of the `for j` loop. In fact, since `Y` is unknown at compile time, we can't even statically determine the gap between the two addresses.

Instead, line 5 and line 9 are in two different stack frames. This is due `POP` on line 7 resetting `offset` to 0, causing `MAYBE INIT` on line 8 to trigger and initialize a new frame. (`INIT UPDATE` was handled by `POP`, so we have a complete stack frame initialization process).

With the original `INIT` and `PUSH`, the code should look like this:
```
 4     for field i in 0..X do
           INIT
           PUSH a 
 5         field a = 10
 6         for field j in 0..Y do
               INIT
               PUSH a
 7             field a = 20
               POP
 8         endfor
           INIT
           PUSH b
 9         field b = 20
           POP
           POP
10     endfor
```
Note that this does not invalidate the fact that line 5 and line 9 are in the same scope. If line 9 were `field a = 20`, it would be a shadowing and it won't be preceded by a `PUSH`.

Also, line 5 and 9 share the same `var_assg`, which now looks like:

`offset`   | 0     | 1   | 0     | 1
-----------|-------|-----|-------|----
`var_name` | `%BP` | `a` | `%BP` | `b`

This is acceptable because the 2 frames always pop at the same time (and thus technically we should only have one `POP` on line 9). 

This also answers the question of why we need a `POP` when `offset = 0`, because we might have other stack frames within the same scope. On the other hand, if the stack frame is empty, then `var_assg` is empty and `POP` would not be executed anyways.

To conclude, `MAYBE INIT` will be triggered if a `PUSH` is not preceded by a `PUSH` or an `INIT UPDATE`. Since both operations update `%SP` and `offset`, `INIT_UPDATE` can create a new stack frame with no problem.

## Proof

Now we can prove the correctness of our construct, first a recap:
```
// INIT UPDATE
if offset > 0
    WRITE "%SP += <offset>"
    offset = 0
endif

// MAYBE INIT; PUSH X
if offset == 0
    WRITE "MEM[%SP] = %BP"
    WRITE "%BP = %SP"
    offset += 1
    var_assg.append(0, "%BP")
endif
WRITE "MEM[%SP + <offset>] = X"
offset += 1
var_assg.append(offset, "X")

// POP
call UPDATE
for pair in var_assg.reverse()
    WRITE "MEM[%BP + <pair.offset>] = <pair.var_name>"
endfor
```

We can make the following observations:

1. `%SP + <offset>` is always the size of RAM, so the memory is indeed write-once. The value of `offset` is always known at compile time.
2. If we need to store an old value, we store it. This is the definition of `PUSH` and this is how we implented it.
3. `var_assg` can only grow so we wouldn't lose any information on current stack frame.
4. Every scope must have a `POP` at the end, even if the `POP` does nothing.
5. The only part of the program where `%BP != %SP` is after an `INIT UPDATE` or `POP` and before the next `MAYBE INIT; PUSH`. Since RAM cannot be alterred without a `PUSH`, we can conclude that every time we write `var_assg.append(offset, "X")`, it must also be the case that `MEM[%BP + <offset>] = X`. If `%BP` is correct, then `POP` is correct.
6. `%BP` can only be updated to 2 values: the beginning address of a new stack frame or the last value of itself, both syncing with grow and shrink of the stack. This means that `%BP` always points to the beginning of the current stack frame, and the address pointed by `%BP` is always the beginning of the last stack frame.