# Packing complete residue blocks in four passes

Take $n>h>g>k>1$ and gaps $(h,g,k,1)$. At a fixed threshold on independent continuous uniform keys, the marked keys in each first-pass chain form a prefix with independent length across chains. If $n=mh+r$, the first $r$ chains have length $m+1$ and the rest length $m$. Their prefix laws differ.

Assume $\gcd(h,g,k)=1$ and write $e=\gcd(h,g)$, $d=\gcd(g,k)$. The next two gaps preserve slots modulo $d$. Within a fixed residue class, group source chains so that a block uses chains of equal length and visits each of $J=g/(ed)$ cyclic starting positions once. This permits summation over starting positions with the same prefix law.

Take consecutive eligible source indices separately in each physical interval of long or short chains. Every run of $J$ covers one period. Rounding separately gives the common block count
$$q=d(\lfloor r/g\rfloor+\lfloor(h-r)/g\rfloor)\ge d(\lfloor h/g\rfloor-1).$$
Thus even at $\lfloor h/g\rfloor=2$ each group admits $d$ blocks. Within a single residue class the boundary remainders give a finer packing calculation. Lean covers the physical placement, cyclic coverage and rounding estimates. Turning these fluctuations into enough surviving inversions for every four-pass table is a further step; the global exponent $25/18$ is a candidate.

[FiberPacking.lean](https://github.com/EternalYMZ/Four-pass-Shellsort-bounds/blob/6bc015e6b704f5911713a58c4f476dcf71514998/Shellsort/FiberPacking.lean) · [WidthMultiplicity.lean](https://github.com/EternalYMZ/Four-pass-Shellsort-bounds/blob/6bc015e6b704f5911713a58c4f476dcf71514998/Shellsort/WidthMultiplicity.lean)
