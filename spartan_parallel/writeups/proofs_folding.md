# Folding `mem_addr_comb` into `perm_root`

## Original Approach
Originally, `perm_root` takes in the following witnesses:
* w0: challenges, `tau, r, r^2, ...`
* w1: one block_inputs entry, `i0, i1, ...`
* w2: one block_inputs entry dot product <r>, `i0, r * i1, r^2 * i2, r^3 * i3, ...`
* w3: `v, x, _, _`, where
  * `v`: valid bit, should match `i0`
  * `x`: one root of the polynomial: `v * (tau - i0 - r * i1 - r^2 * i2 - ...)`

And `mem_addr_comb` takes in:
* w0: challenges, `tau, r, _, _`
* w1: one memory entry, `valid, addr, val, D`
* w2: intermediate computation, `r * val, 0, 0, 0`
* w3: `v, x, _, _`, where
  * `v`: valid bit, should match `valid`
  * `x`: one root of the polynomial: `v * (tau - addr - r * val)`, wehre `r * val` is expressed using w2[0]

In which we note:
1. `valid` is used by `mem_cohere` and should not be removed
2. `D` in w1 is used by `mem_cohere`, but cannot appear in the root
3. `x` matches with the corresponding root in `mem_extract`, and we restrict that the value of `x` must be able to obtain using one additional witness (in our case, w2[0])
4. w3 must be of form `v, x, _, _`, whereas content of w2 is unrestricted

## Folding
If we try to apply `perm_root` on a memory entry to form w3 = `v, x, _, _`, we encounter the following problems:
1. `D` will be included in w3, which we don't want
2. Even if we remove `D`, x = `v * (tau - valid - r * addr - r^2 * val)`, which cannot be expressed using one additional variable, as we need either:
  * `Z1 = r * addr`, `Z2 = r^2 * val`, or
  * `Z1 = r * val`, `Z2 = r * (addr - Z1)`

To solve this problem, we start with an observation, which is that in `perm_root`, `i0` is always the valid bit, assigned to 0 or 1. Furthermore, the value of `i0` can always be inferred from the root, since `x = 0` iff `i0 = 0` except with neligible probability. Thus, it is not necessary to include `i0` in the root. Moreover, since the inputs contain another dummy value, we can place that value at `i1`, and avoid adding `i1` to the permutation. Now, we have
```
x = i0 * (tau - i2 - r * i3 - r^2 * i4 - ...)
```
With the new `x` we can rewrite memory entry as `valid, D, addr, val`, so a root for one memory entry will be
```
x = valid * (tau - addr - r * val)
```

# Folding `consis_comb` into `perm_root`

The above transformation allows us to perform another proof folding: `consis_comb` into `perm_root`

## Original Approach
After the previous folding, `consis_comb` takes in the following witnesses:
* w0: challenges, `tau, r, r^2, ...`
* w1: one block_inputs entry, `v, _, i0, i1, ..., o0, o1, ...`
* **consis_w2**: one block_inputs entry dot product <r>, `i, o, i0, r * i1, r^2 * i2, ..., o0, r * o1, r^2 * o2, ...`

where `i = v * (v + i0 + r * i1 + r^2 * i2 + ...)` and `o = v * (v + o0 + r * o1 + r^2 * o2 + ...)` are the only witnesses used elsewhere

Note:
* If `v = 0`, then soundness requires `i = 0` and `o = 0`
* If `v != 0`, then soundness requires `i != 0` and `o != 0`
* The above construction satisfies the requirement because `v` can only be 0 or 1, and block correctness restricts `i0` & `o0` to never be -1

## Folding

We note that w2 for `consis_comb` is extremely similar to w2 of `perm_root`, which is expressed as
* **perm_root_w2**: `_, _, i0, r * i1, r^2 * i2, ..., r^n * o0, r^(n + 1) * o1, ...`, where `n` is the size of the input

Observe that we don't really need `i0` to appear in w2, so we can three empty slots at the front of perm_root_w2.

The only thing left is to add `i` and `o` to perm_root_w2 and assert:
1. `i = v * (v + i0 + r * i1 + r^2 * i2 + ...)`
2. `Zo * r^n = r^n * o0 + r^(n + 1) * o1, ...`
3. `o = v * (v + Zo)`

So, with three additional constraints, we can use perm_root_w2 to express consis_w2:
* **perm_root_w2**: `i, o, Zo, r * i1, r^2 * i2, ..., r^n * o0, r^(n + 1) * o1, ...`, where `n` is the size of the input