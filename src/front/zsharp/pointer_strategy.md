# Stack Simulation

This file demonstrates the stack construction (simulation) in the current circ block system.

## Preliminaries

There are three factors that contributes to the current stack construction:

1. There are infinitely many registers, which can represent infinitely many variables, as long as they have unique identifier. 

This implies that we don't need to store every local variable onto the stack.

2. We use continuation passing, so there are no ways to explicitly handle scopings.

This implies that we need to use stack frame no just for function calls, but also scoping change.

3. Every cell in RAM is write-once, meaning that once a cell is occupied, its content cannot be altered.

This means that we cannot `pop` a stack, and consequently the entire concept of stack needs to be simulated.

NOTE: Stack frame is *NOT* related to blocks. While most push / pops occur during block transition, this is not always the case. From now on I'll avoid mentioning the term "block".

## Redefine Stack Frame

The first step alter the definition of stack frame. In the current system, there are two cases that can invoke a `push` onto the stack:
    
1. A variable declaration which overwrites its old value in a previous scope (in the same function).
    
2. Invoking a function call (technically only if there are parameters / local variables in the current function.).

There are also two cases that can invoke a purported `pop`:

1. Right before we exit a scope.

2. Right after evaluating a function call, before we process the function output (e.g. assign it to the LHS variable).

## Stack and Base Pointers

As discussed early, despite the name `pop`, we cannot actually pop the stack since it is write-once. Instead, we use two pointers `%SP` and `%BP` to simulate `push` and `pop`:

- `%SP` always points to the address that marks the beginning of the *current* stack frame. Since the size of the RAM (stack) can only grow, `%SP` cannot be decremented.

- `%BP` always points to the address that marks the beginning of the *purportedly last* stack frame. Note that `%BP` might not point to the actual last stack frame, as the example below demonstrates.

Consider the following stack operations:
```
<Local Var A>
PUSH
    <Local Var B>
    PUSH
        ...
    POP
    <Local Var C>
    PUSH
        ...
    POP
    <Local Var D>
    // Line X
```
Assume that no more local variables are introduced in the "`...`" sections, then we have `<A>` stored in frame depth 0; `<B>`, `<C>` and `<D>` stored in frame depth 1. However, since RAM is write-once, `<A>`, `<B>`, `<C>`, `<D>` are actually stored sequentially, taking up slot 0, 1, 2, and 3. As a result, `<D>` is slot 3 in the memory, but purportedly stack frame 1, directly above `<A>`.

Thus, when we reach `Line X`, we should expect `%SP = 3, %BP = 0`.

## Stack Frame Content

Content of each stack frame is generated using the following procedure: 

1. The first element of each stack frame always stores `%BP`, which points to the beginning of the stack frame purportedly immediately below it. Stack frame 0 stores a dummy value as its first element.

2. Whenever a variable is redefined that overwrites its old value in another scope, push the *old value* onto the current stack frame.

3. When we encounter a function call, push *all* variables currently in scope (defined in current or previous scope) onto the stack.

## Example

We now provide an example of the procedure, before presenting a pseudocode of it.

Consider the following code:
```
def add(field a, field b) -> field:
    return a + b

def main() -> field:
    field a = 5
    field b = 4
    for field i in 0..4 do
        field a = 10
        for field k in 0..2 do
            a = a + 1
            field a = 20
        endfor
        b = add(add(a, b), b)
    endfor
    return b
```

The function `main` would be transformed as follows:

```
// push var, addr
// pop var, addr
// %ret is the return register of a function

def main() -> field:
    field %SP = 0
    field %BP = 0
    field a = 5
    field b = 4
    for field i in 0..4 do

        push %BP, %SP + 0
        push   a, %SP + 1
        field a = 10
        %BP = %SP
        %SP = %SP + 2

        for field k in 0..2 do
            a = a + 1

            push %BP, %SP + 0
            push   a, %SP + 1
            field a = 20
            %BP = %SP
            %SP = %SP + 2

            pop   a, %BP + 1
            pop %BP, %BP + 0
        endfor

        push %BP, %SP + 0
        push   a, %SP + 1
        push   b, %SP + 2
        %BP = %SP
        %SP = %SP + 3
        CALL add(a, b)
        pop   b, %BP + 2
        pop   a, %BP + 1
        pop %BP, %BP + 0

        field ret0 = %ret
        
        push %BP, %SP + 0
        push   a, %SP + 1
        push   b, %SP + 2
        %BP = %SP
        %SP = %SP + 3
        CALL add(ret0, b)        
        pop   b, %BP + 2
        pop   a, %BP + 1
        pop %BP, %BP + 0

        b = %ret

        pop   a, %BP + 1
        pop %BP, %BP + 0
    endfor

    %ret = b
```

Note that in this example, block 2 defines `a` in a *new* scope (shadowing does not count), and thus pushes the previous `a` onto the stack, resulting in a `STACK PUSH` before the End Block. Without this definition, it would have no "local" variables and would not need this process. Finally, calling of the function `add` requires a new stack frame, pushed at the end of Block 4 and popped at the beginning of Block 5.