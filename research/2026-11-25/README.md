# Accumulated error and two sharp examples for predetermined gap words

Miaozhen Yu · 25 November 2026

A predetermined word $(h_1,\ldots,h_p)$, $1\le h_r\le n$, acts by ordinary linear insertion on each residue chain of a permutation of $n$ distinct ranks. Repeated or increasing gaps are permitted. Let $C$ count all key comparisons, including failed stops, and $M$ count successful shifts. Divide consecutive ranks into buckets of size at most $b$. The per-pass color cost $f_h$ counts strict chain inversions plus the indicators that the current color exceeds the preceding minimum. The distance between two color arrays is $D(z,w)=\sum_i|z_i-w_i|$. J1–J7 are local research labels. The one-pass counting proof, quadratic displacement estimate, stability lemma and exact uniform-mean analyzer are in [P02](https://github.com/EternalYMZ/Three-pass-Shellsort-inversion-error/blob/main/research/2026-11-25/README.md).

## J4. Accumulating state and cost error

Write $\mu_0$ for the true initial color law and $\nu_r$ for proposed approximations after pass $r$. In the finite color space, $W_1$ is the minimum expected $D$ over couplings. Suppose
$\varepsilon_0\ge W_1(\mu_0,\nu_0)$ and
$\varepsilon_s\ge W_1((S_{h_s})_\#\nu_{s-1},\nu_s)$.
As chain sorting contracts $D$, pushing any coupling through the pass does not increase its mean distance. The triangle inequality now bounds the entrance-law error of pass $r$ by $\sum_{s=0}^{r-1}\varepsilon_s$. The one-pass Lipschitz constant $\lambda_h=\lceil n/h\rceil-1$ gives

$$
\widehat C=\sum_{r=1}^p\mathbb E_{\nu_{r-1}} f_{h_r},\qquad
A=\sum_{r=1}^{p}\lambda_{h_r}\sum_{s=0}^{r-1}\varepsilon_s,\qquad
\widehat C-A\le\mathbb E C\le\widehat C+A+B .
$$

Here $B$ bounds the sum of the **true** expected single-pass bucket omissions. Their sign is nonnegative by J1. A universal choice is $p\sum_B\binom{|B|}{2}$, or $(p-1)\sum_B\binom{|B|}{2}$ when the first pass is handled exactly and the formula starts at the suffix. J2 supplies smaller choices based on the true displacement or squared displacement entering each pass. The error introduced after pass $p$ has zero weight. The initial law may be arbitrary when the stated coupling and omission bounds are available. Replacing the exact states by a proposed approximation requires an actual bound on its local $\varepsilon_s$. To infer a leading term on scale $T$, one needs $A+B=o(T)$.

There are $S=\sum_r(n-h_r)$ insertions. Each makes at least one comparison and contributes at most one failed stop, giving $\max(S,M)\le C\le S+M$. Viewing a shift as an adjacent swap within its chain shows that each swap reduces the global inversion count by at least one. Under the uniform original permutation, $\mathbb EC\le S+n(n-1)/4$. The scan term remains explicit when the number of passes grows.

A second pointwise estimate is $M_r\le(Q_{r-1}-Q_r)/(2h_r)$ for $Q=\sum_i(x_i-i)^2$. An adjacent chain swap of inverted ranks $a>b$ reduces $Q$ by $2h_r(a-b)$. R11 also allows a pass at a gap already guaranteed sorted by the additive semigroup of earlier gaps to be omitted from the state updates. Such a pass still costs exactly $n-h_r$ comparisons. [Earlier semigroup and displacement results](https://github.com/EternalYMZ/Project-S/blob/2a6361e542e9a34018736fd831a43cc52f2fcfb0/research/2026-11-25/subsorting.md)

## J6. A strictly decreasing word with quadratic pointwise omission

Let $n=2N$ and start from $(N,0,N+1,1,\ldots,2N-1,N-1)$. Run $h_j=2N-2j+1$ for $j=1,\ldots,N$. After pass $j$, for $0\le i<N$,

$$
x^{(j)}_{2i}=N+i-(j-i)_+,\qquad
x^{(j)}_{2i+1}=i+(i-N+j+1)_+.
$$

At step $j$ put $k=N-j$. The even-to-odd adjacent chain edges have endpoints $2i,2(i+k)+1$ for $0\le i<j$. Substitution of the previous formula gives the consecutive values $(k+2i+1,k+2i)$. The $j$ edges are disjoint. Every odd-to-even adjacent chain edge has right value at least three above its left value before these swaps, hence remains increasing afterwards. This proves the state formula inductively and accounts for exactly $j$ shifts. With buckets $\{0,1\},\{2,3\},\ldots$ all $j$ shifts are omitted precisely when $j$ and $N$ have the same parity. The total omitted successes are $\lfloor(N+1)^2/4\rfloor$. For even $N$ this is $n^2/16+n/4$. This fixed input excludes a pass-independent pointwise $O(nb)$ estimate even for decreasing gaps. On the smaller input $(2,1,3,0)$, gaps $(2,3,1)$ exchange the same pair of ranks $(1,0)$ twice.

## J7. An exact obstruction under the uniform input law

On $n=2N\ge2$ take uniform original ranks and the fixed word $(2,2N-1,2N-3,\ldots,1)$. The first gap sorts the two parity chains. In contrast to J6, for $n\ge4$ the word increases after its first pass. Let $R$ count only the same-bucket successful comparisons in the odd suffix, with the same width-two buckets. Then

$$
\mathbb E R=\frac{(N+1)4^N}{8\binom{2N}{N}}
\sim\frac{\sqrt{\pi}}{16\sqrt2}\,n^{3/2},\qquad
\mathbb E(C-C^{[2]})\ge\mathbb E R .
$$

Here $C^{[2]}$ sums the strict bucket proxy. The lower bound also holds if one charges the full true first pass. The leading coefficient describes the omitted successful comparisons in this suffix. The full comparison error also includes omitted stopping terms.

**Which ranks can swap?** Before odd gap $h$ all even distances and all larger odd distances are ordered. A chain inversion therefore has distance $h$. If its ranks are $a>b$ and $b<c<a$, the position of $c$ has the parity of one endpoint. If it has the parity of $a$, it must lie before $a$ by even-distance order, contradicting its order with $b$ at a larger odd distance. If it has the parity of $b$, it must lie after $b$, with the symmetric contradiction. Thus $a=b+1$. Exchanging consecutive ranks changes only the comparison between the two swapped positions among all fixed position pairs. It preserves the known orders, including inside a pass represented by adjacent chain swaps.

**Counting each adjacent rank pair.** After gap two write $\sigma_k=+1$ when rank $k$ occupies an even position and $-1$ otherwise, and $S_t=\sum_{k<t}\sigma_k$. The signs are a uniform balanced word of length $2N$. Exchanging $k$ and $k+1$ changes only $S_{k+1}$ by two. The change is always toward its final value $(k+1)\bmod 2$. Indeed let $a,b$ count the even and odd positions among ranks smaller than $k$. If $k$ is even-positioned, the positions are $2a,2b+1$ and an inversion requires $a\ge b+1$. Then $S_{k+1}=a-b+1\ge2$ drops by two. Otherwise the positions are $2b+1,2a$ and an inversion requires $b\ge a$, so $S_{k+1}=a-b-1\le-1$ increases by two. Parity prevents overshoot. Same-bucket pairs have even $k$, giving $R=\tfrac12\sum_{t\ \mathrm{odd}}|S_t-1|$ for every post-gap-two state.

**Summation.** At odd time $t=2a+1$ write $2N-t=2b+1$. The numbers of bridges with positive height $2r+1$ and its negative are equal. Their common count is $q_r=\binom{2a+1}{a+1+r}\binom{2b+1}{b-r}$. With out-of-range binomial coefficients zero, put $F_r=(a+r+1)(b+r+1)q_r/N$. The ratio of consecutive binomials gives $F_r-F_{r+1}=(2r+1)q_r$. Hence $\binom{2N}{N}\mathbb E|S_t-1|=\binom{2N}{N}\mathbb E|S_t|=2F_0$. Sum over $a+b=N-1$. Since $\sum_{a\ge0}(2a+1)\binom{2a}{a}z^a=(1-4z)^{-3/2}$, the convolution is $[z^{N-1}](1-4z)^{-3}=\binom{N+1}{2}4^{N-1}$. Substitution proves the finite formula; Stirling's formula gives its asymptotic. For all $N\ge1$ it also implies
$\mathbb ER\ge(N+1)\sqrt{3N+1}/8\ge\sqrt{3/2}\,n^{3/2}/16$, since the successive ratio of $\binom{2N}{N}/4^N$ is $(2N+1)/(2N+2)$ and its square is at most $(3N+1)/(3N+4)$.

## Reproduce the finite checks

Run from this directory with Python 3 and the standard library.

~~~sh
python cumulative_error_verifier.py
python project_s_average_counterexample_audit.py
~~~

Both implementations verify the per-rank trajectories on all 17,576 balanced states of sizes $2,4,\ldots,16$. The first also checks every pass of 128 pointwise examples, 1,599 second- and fourth-moment identities and 45,100 telescoping instances through $N=80$. Its [exact output](cumulative_error_results.json) includes $\mathbb ER=4096/715$ for $n=16$. These examples delimit uniform statements over **all** predetermined words. The global four-pass candidate and its unresolved probabilistic transfer retain their existing status. The analytical certificate and counterexamples above have no new [Lean root](../../Shellsort.lean).
