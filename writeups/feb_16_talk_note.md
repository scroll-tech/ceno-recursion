# Verifiable Computation / Probabilistic Proofs
* **Goal**: verify the correctness of execution in polylog time.
* **Note**: orthogonal to zero-knowledge

## Example
```pascal
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
```pascal
INTPUT: a0, b0
    a1 = a0 + 1        -> a1 - a0 - 1 = 0
    // LOOP
    i0 = 0             -> i0 = 0
    // IT 1
    if i0 == 0 then    -> Z0 * i0 = 0
        b1 = a1 + b0   -> Z0 * (b1 - a1 - b0) = 0
        a2 = a1 + b1   -> Z0 * (a2 - a1 - b1) = 0
    else               -> (1 - Z0) * (i0 * W0 - 1) = 0 -> i0 * W0 = T0 + 1; (1 - Z0) * T0 = 0
        b1 = b0        -> (1 - Z0) * (b1 - b0) = 0
        a2 = a1        -> (1 - Z0) * (a2 - a1) = 0
    endif
    i1 = i0 + 1        -> ...
    // IT 2
    if i1 == 0 then
        b2 = a2 + b1
        a3 = a2 + b2
    else
        b2 = b1
        a3 = a2
    endif
    i2 = i1 + 1
    // END LOOP
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
  i0          W0              T0 + 1        // Two constraints to represent (1 - Z0) * (i0 * W0 - 1) = 0
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

#### Step 2: Prove that Az, Bz, Cz are computed correctly (n = log N)
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
```pascal
// BLOCK 1
// INPUT: a, b
    a = a + 1
    i = 0
// TRANSITION: i == 2 ? -> 2 : -> 5
// OUTPUT: a, b, i

// BLOCK 2
// INPUT: a, b, i
// TRANSITION: i == 0 ? -> 3 : -> 4
// OUTPUT: a, b, i

// BLOCK 3
// INPUT: a, b, i

// TRANSITION: i == 0 ? -> 3 : -> 4
// OUTPUT: a, b, i

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