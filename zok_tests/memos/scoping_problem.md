# Problem with Scoping

Consider the following code:

```
field a = 1
field b = 2
for i in 0..X
    field a = 3
    for j in 0..Y
        field a = 4
    endfor
    field b = 5
endfor
```

To completely adhere to continuation passing style, we should do

```
Block 0:
    field a = 1
    field b = 2
    i = 0
Transition: i < X ? Block 1 : Block 4

Block 1:
    push a -> stack
    field a = 3
    j = 0
Transition: j < Y ? Block 2 : Block 3

Block 2:
    push a -> stack
    field a = 4
    j = j + 1
    pop a <- stack
Transition: j < Y ? Block 2 : Block 3

Block 3:
    push b -> stack
    field b = 5
    i = i + 1
    pop b <- stack
    pop a <- stack
Transition: i < X ? Block 1 : Block 4
```

This is completely cool on its own since in Block 3 we should have `STACK[0] = a` and `STACK[1] = b`, but if we add write-once RAM into the picture, then we have:
* `STACK[0]` stores `a` in Block 1
* `STACK[1..Y+1]` stores `a` in Block 2
* `STACK[Y+1]` stores `b` in Block 3

`Y` is not known at compile time, and to make matter even worse, consider:

```
field a = 1
field b = 2
field c = 3
for i in 0..X
    field a = 4
    <LOOP Y>
    field b = 5
    <LOOP Z>
    field c = 6
endfor
```
If `<LOOP Y>` and `<LOOP Z>` are complicated enough, we literally wouldn't know where in stack `b` is by the time we pop it out just before `endfor`.

## Conclusion

Index in stack might not be compile-time, or even run-time knowledge, when we combine continuation passing with write-once memory.