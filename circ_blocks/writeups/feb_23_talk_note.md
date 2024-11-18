# Verifiable Computation / Probabilistic Proofs
* **Goal**: verify the correctness of execution in polylog time.
* **Note**: orthogonal to zero-knowledge

## Example
```python
def add(field b, field c) -> field:
    return b + c

def main(field a, field b)-> field:
    a = a + 1
    for field i in 0..2 do
        if i == 0 then
            field b = add(a, b)
            a = a + b
        endif
    endfor
    a = a + 1
    return add(a, b)

INPUT: a = 2, b = 3
OUTPUT: RET = 13
```

* **Goal**: convert to an arithmetic circuit and verify correctness

## Traditional Approach

### Phase 1: Circuit Generation (PUBLIC)

#### Step 1: Unroll, Flatten, SSA
Constraints are represented in fields mod prime
```python
INTPUT: a0, b0
    a1 = a0 + 1        -> a1 - a0 - 1 = 0
    # LOOP
    i0 = 0             -> i0 = 0
    # IT 1
    if i0 == 0 then    -> Z0 * i0 = 0
        b1 = a1 + b0   -> Z0 * (b1 - a1 - b0) = 0
        a2 = a1 + b1   -> Z0 * (a2 - a1 - b1) = 0
    else               -> (1 - Z0) * (i0 * W0 - 1) = 0 -> i0 * W0 = T0 + 1; (1 - Z0) * T0 = 0
        b1 = b0        -> (1 - Z0) * (b1 - b0) = 0
        a2 = a1        -> (1 - Z0) * (a2 - a1) = 0
    endif
    i1 = i0 + 1        -> ...
    # IT 2
    if i1 == 0 then
        b2 = a2 + b1
        a3 = a2 + b2
    else
        b2 = b1
        a3 = a2
    endif
    i2 = i1 + 1
    # END LOOP
    a4 = a3 + 1
OUTPUT: RET = a4 + b0
```

#### Step 2: Into Constraints: Az * Bz = Cz
```
INPUT: a0 = 2, b0 = 3
  A           B               C
  0           0               a1 - a0 - 1
  0           0               i0
  Z0          i0              0
  Z0          b1 - a1 - b0    0
  Z0          a2 - a1 - b1    0
  i0          W0              T0 + 1        # Two constraints to represent (1 - Z0) * (i0 * W0 - 1) = 0
  1 - Z0      T0              0
  1 - Z0      b1 - b0         0
  1 - Z0      a2 - a1         0
  ...
```

#### Step 3: Into Circuits (Matrices)
```
C Matrix (M x N)
    1  a0  b0  a1  i0  Z0  b1  a2  W0  T0  i1  Z1  b2  a3  W1  T1  i2  a4 RET
0  -1  -1   0   1   0   0 ...
1   0   0   0   0   1   0 ...
2   0 ...
3   0 ...
4   0 ...
5   1   0   0   0   0   0   0   0   0   1   0 ...
6   0 ...
```

### Phase 2: Witness Generation (PROVER)
```
Z Vector (length-N)
    1  a0  b0  a1  i0  Z0  b1  a2  W0  T0  i1  Z1  b2  a3  W1  T1  i2  a4 RET
    1   2   3   3   0   1   6   9   0  -1   1   0   6   9   1   0   2  10  13
```

### Phase 3: Circuit Verification (PROVER + VERIFIER)
Prove Az * Bz - Cz = 0 for all constraints: M constraints, each with length-N vector dot products
```
A0z * B0z - C0z = 0
A1z * B1z - C1z = 0
A2z * B2z - C2z = 0
```

#### Step 1: Prove that the right-hand side is always 0 (m = log M)
- Sum everything up
- Random linear combination
- Three polynomials (Az, Bz, Cz) with m variables
- Sumcheck protocol
- Returns: length-m vector rx, Az(rx), Bz(rx), Cz(rx)

#### Step 2: Evaluate Az(rx), Bz(rx), Cz(rx) (n = log N)
- Three sumchecks on `A(rx) * z = Az(rx), B(rx) * z = Bz(rx), C(rx) * z = Cz(rx)`
- One sumcheck `ABC(rx) = rA * A(rx) + rB * B(rx) + rc * C(rx)`
- Returns: length-n vector ry, ABC(rx)(ry), z(ry)

#### Step 3: Polynomial evaluation on random point
- Naive evaluation on A, B, C, z
- Polynomial commitment

### Analysis
Main problem is inflexibility

## New Approach

### Phase 1: Block Generation (PUBLIC)
```
BLOCK 0 (main)
  a0 = a0 + 1
  i0 = 0
T: i0 == 2 ? (i0 == 0 ? -> 1 : -> 3) : -> 4

BLOCK 1 (main)
    b2 = a0
    c0 = b0
    %RP = 2
T: -> 6

BLOCK 2 (main)
    b1 = %RET
    a0 = a0 + b1
T: -> 3

BLOCK 3 (main)
    i0 = i0 + 1
T: i0 == 2 ? (i0 == 0 ? -> 1 : -> 3) : -> 4

BLOCK 4 (main)
    a0 = a0 + 1
    b2 = a0
    c0 = b0
    %RP = 6
T: -> 6

BLOCK 5
T: PROG TERM

BLOCK 6
    %RET = b2 + c0
T: -> %RP
```

### Phase 2: Register Allocation
```python
# %iBN, %i0 -> a0, %i1 -> b0
BLOCK 0 (main)
  assert(%iBN == 0)
  %o0 = %i0 + 1
  %o1 = %i1
  %o2 = 0
  %oBN = %o2 == 2 ? (%o2 == 0 ? -> 1 : -> 3) : -> 4
# %oBN, %o0 -> a0, %o1 -> b0, %o2 -> i0

# %iBN, %i0 -> a0, %i1 -> b0, %i2 -> i0
BLOCK 1 (main)
    assert(%iBN == 1)
    %o0 = %i0
    %o1 = %i1
    STORE(0, %i0)
    STORE(1, %i1)
    STORE(2, %i2)
    %o2 = 2
    %oBN = 6
# %oBN, %o0 -> b2, %o1 -> c0, %o2 -> %RP

# %iBN, %i0 -> %RET
BLOCK 2 (main)
    assert(%iBN == 2)
    LOAD(2, %o2)
    LOAD(1, %o1)
    LOAD(0, %w0)
    %w1 = %i0
    %o0 = %w0 + %w1
    %oBN = 3
# %oBN, %o0 -> a0, %o1 -> b0, %o2 -> i0

# %iBN, %i0 -> a0, %i1 -> b0, %i2 -> i0
BLOCK 3 (main)
    assert(%iBN == 3)
    %o0 = %i0
    %o1 = %i1
    %o2 = %i2 + 1
    %oBN = %o2 == 2 ? (%o2 == 0 ? -> 1 : -> 3) : -> 4
# %oBN, %o0 -> a0, %o1 -> b0, %o2 -> i0

# %iBN, %i0 -> a0, %i1 -> b0, %i2 -> i0
BLOCK 4 (main)
    assert(%iBN == 4)
    %o0 = %i0 + 1
    %o1 = %i1
    %o2 = 6
    %oBN = 6
# %oBN, %o0 -> b2, %o1 -> c0, %o2 -> %RP

# %iBN, %i0 -> %RET
BLOCK 5
    assert(%iBN == 5)
    %oBN = 7
# PROG TERM

# %iBN, %i0 -> b2, %i1 -> c0, %i2 -> %RP
BLOCK 6
    assert(%iBN == 6)
    %o0 = %i0 + %i1
    %oBN = %RP
# %oBN, %o0 -> %RET
```

### Phase 3: Witness Generation

#### Execution Order
```
    %iBN   %i0   %i1   %i2   %oBN   %o0   %o1   %o2   |   %w0
0      0     2     3     0      1     3     3     0         0
1      1     2     3     0      6     3     3     2         0
2      6     2     3     2      2     5     0     0         0
3      2     5     0     0      3     9     3     0         2
4      3     7     3     0      3     9     3     1         0
5      3     7     3     0      4     9     3     2         0
6      4     7     3     2    ...
```

#### Block Order
```
BLOCK 3
    %iBN   %i0   %i1   %i2   %oBN   %o0   %o1   %o2   |   %w0
0      3     7     3     0      3     9     3     1         0
1      3     7     3     0      4     9     3     2         0

BLOCK 6
0      6     2     3     2      2     5     0     0         0
1    ...

BLOCK 0
0      0     2     3     0      1     3     3     0         0

...
```

### Phase 4: Circuits

#### Block Correctness
Feed witnesses in block order to satisfy block instances.

#### Consistency
Check that output of previous block is input of the next block in execution order.

#### Permutation
Fingerprinting
```
CHALLENGE
    tau   r   r^2   r^3   r^4   ...
```
For each row
```
ROOT = tau - %iBN - r * %i0 - r^2 * %i1 - r^3 * %i2 - ...
```

#### Memory
