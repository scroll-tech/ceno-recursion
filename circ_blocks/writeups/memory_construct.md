# Memory Construction

## Original Approach
The original memory operations are denoted as a quadruple:
- `(addr, val, ls, ts)`
For consistency check, permutate:
- First by address
- Then by timestamp
And check:
1. `addr[i] <= addr[i+1]` [34]
2. `if addr[i] == addr[i+1] then ts[i] <= ts[i+1]` [>34]
3. `if addr[i] == addr[i+1] && ls[i+1] == LOAD then val[i] == val[i+1]` [~4]
4. `if addr[i] != addr[i+1] then ls[i+1] == STORE` [~3]

## Simplified Approach
The simplified memory operations are still denoted as a quadruple:
- `(addr, val, ls, ts)`
For consistency check, permutate:
- First by address
- Then by timestamp
For every ARRAY INIT or MALLOC:
- Always allocate consecutive addresses
And only increment the timestamp if any address is OVERWRITTEN (determined at compile time)
And check:
1. `addr[i] == addr[i+1 || addr[i] + 1 = addr[i+1]` [1]
2. `if addr[i] == addr[i+1] then ts[i] <= ts[i+1]` [>34]
3. `if addr[i] == addr[i+1] && ls[i+1] == LOAD then val[i] == val[i+1]` [~4]
4. `if addr[i] != addr[i+1] then ls[i+1] == STORE` [~3]
Translating into constraints:
- Each access is of form `v, D1, addr, val, ls, ts, _, _`, with accesories `D2, eq, b0, b1, b2, ...`
1. `(v[i] - 1) * v[i+1] = 0`
2. `v[i+1] * (1 - addr[i+1] + addr[i]) * (addr[i+1] - addr[i]) = 0`
3. `v[i+1] * (1 - addr[i+1] + addr[i]) * (ts[i+1] - ts[i]) = eq + b0 + 2 * b1 + ...`
4. `v[i+1] * (1 - addr[i+1] + addr[i]) * (ls[i+1] - STORE) * (val[i+1] - val[i]) = 0`
5. `v[i+1] * (addr[i+1] - addr[i]) * (ls[i+1] - STORE)`
So, if we set `STORE <- 0`
1. `D1 = v[i+1] * (1 - addr[i+1] + addr[i])`
2. `D2 = D1 * (ls[i+1] - STORE)`
3. `(v[i] - 1) * v[i+1] = 0`
4. `D1 * (addr[i+1] - addr[i]) = 0`
5. `D1 * (ts[i+1] - ts[i]) = eq + b0 + 2 * b1 + ...`
6. `D2 * (val[i+1] - val[i]) = 0`
7. `(1 - D1) * (ls[i+1] - STORE) = 0`
Note that constraint 7 works because:
- If `v[i+1] == 1`, then `(1 - D1) == v[i+1] * (addr[i+1] - addr[i])`
- If `v[i+1] == 0`, then `ls[i+1] == 0`


## Write-Once Approach
The write-once memory operations are denoted as a quadruple:
- `(phy_addr, val, vir_addr, ls, ts)`
During constraint generation, 
- Virtual address 0 is skipped, AND
for every STORE:
- Perform a LOAD to obtain the previous physical address: `phy_addr, val = 0, vir_addr, ls = LOAD, ts`
- Increment the timestamp
- Invalidate the previous physical address: `phy_addr, val = 0, vir_addr = 0, ls = STORE, ts`
  - Assert that the two `phy_addr` are the same
- Allocate a new physical address: `phy_addr, val, vir_addr, ls = STORE, ts`
  - Assert that `phy_addr == ts`
For consistency check, permutate `(phy_addr, val, vir_addr, ls, ts)`:
- First by physical address
- Then by timestamp
And check:
1. `phy_addr[i] == phy_addr[i+1] || phy_addr[i] + 1 == phy_addr[i+1]`
2. `phy_addr[i] == phy_addr[i+1] => val[i] == val[i+1]`
3. `phy_addr[i] == phy_addr[i+1] => vir_addr[i] == vir_addr[i+1] || vir_addr[i+1] == 0`
4. `phy_addr[i] == phy_addr[i+1] => ts[i] <= ts[i+1]`
5. `phy_addr[i] + 1 == phy_addr[i+1] => ls[i+1] == STORE`

> Note 1: since timestamp is only incremented at STORE, timestamp is the same as the size of the allocated memory

> Note 2: `phy_addr[i] == phy_addr[i+1] => ls[i+1] == LOAD` is unsound for step 5, because the prover can allocate a new physical address for every LOAD

## Lazy Approach
For every memory operation at execution time, introduce the following triple:
- `(vir_addr, val, ts)`
In addition, a hidden fourth variable `phy_addr` only visible to the prover.
During constraint generation, 
- Virtual address & physical address 0 are skipped
For every STORE:
- Increment the timestamp
- Invalidate the previous physical address: `vir_addr = 0, val = 0, ts`
- Allocate a new physical address: implicit
- Perform the store: `vir_addr, val, ts`
For every LOAD:
- Perform the load: `vir_addr, val, ts`
For every DUMMY_LOAD:
- Insert a dummy invalidation: `vir_addr, val, ts`
- Insert a dummy load: `vir_addr, val, ts`
For consistency check, permutate `(vir_addr, val, ts)`:
- First by `phy_addr`,
- Then by `ts`
For the address-ordered pair, non-deterministically append sorted `phy_addr` to it to form `(phy_addr, vir_addr, val, ts)`, then check:
1. `phy_addr[i] == phy_addr[i+1] || phy_addr[i] + 1 == phy_addr[i+1]`
2. `phy_addr[i] == phy_addr[i+1] => val[i] == val[i+1]`
3. `phy_addr[i] == phy_addr[i+1] => vir_addr[i] == vir_addr[i+1] || vir_addr[i+1] == 0`
4. `phy_addr[i] == phy_addr[i+1] => ts[i] <= ts[i+1]`
5. `phy_addr[i] + 1 == phy_addr[i+1] => phy_addr[i+1] == ts[i+1]`

Proof:
1. Every physical address correspond to the same (vir, val) pair
Q0: The prover can just claim every phy is 0. Although this is easily fixable
2. For every increment in Timestamp (every STORE), the prover can only allocate one physical memory address
Q1: What is preventing the prover from invalidating the wrong cell?
3. If the STORE changes the value stored in that memory cell, then the prover has no choice but to allocate the new phy address to the new value
4. If the STORE does not change the value stored in that memory cell, then:
Q2: The prover can pass the STORE as a LOAD and claim some other LOAD is a STORE