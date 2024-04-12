# Memory Construction

## Original Approach
The original memory operations are denoted as a quadruple:
- `(addr, val, io, ts)`
For consistency check, permutate:
- First by address
- Then by timestamp
And check:
1. `addr[i] <= addr[i+1]` [34]
2. `if addr[i] == addr[i+1] then ts[i] <= ts[i+1]` [>34]
3. `if addr[i] == addr[i+1] && io[i+1] == READ then val[i] == val[i+1]` [~4]
4. `if addr[i] != addr[i+1] then io[i+1] == WRITE` [~3]

## Write-Once Approach
The write-once memory operations are denoted as a quadruple:
- `(phy_addr, val, vir_addr, ts)`
During constraint generation, 
- Virtual address 0 is skipped, AND
for every WRITE:
- Invalidate the previous physical address
- Allocate a new physical address
- Increment the timestamp
For consistency check, permutate:
- First by physical address
- Then by timestamp
And check:
1. `phy_addr[i] == phy_addr[i+1] || phy_addr[i] + 1 == phy_addr[i+1]`
2. `phy_addr[i] == phy_addr[i+1] => val[i] == val[i+1]`
3. `phy_addr[i] == phy_addr[i+1] => vir_addr[i] == vir_addr[i+1] || vir_addr[i+1] == 0`
4. `phy_addr[i] == phy_addr[i+1] => ts[i] <= ts[i+1]`