# 四遍 Shellsort 中能保留多少个完整的余数块？

设间隔依次为 $h,g,k,1$，其中 $n>h>g>k>1$。要给平均右移数找下界，需要知道前三遍之后还剩多少偏差。第一遍有个可直接利用的规律。用独立连续均匀键生成随机排列，固定键值阈值 $t$，每条 $h$ 链中低于 $t$ 的键在排好后占据一个前缀。不同链的前缀长度独立。若 $n=mh+r$，前 $r$ 条链长 $m+1$，其余链长 $m$，两种链的计数分布各不相同。

考虑 $\gcd(h,g,k)=1$ 的情形。记 $e=\gcd(h,g)$、$d=\gcd(g,k)$。后两种间隔 $g,k$ 都保持槽号模 $d$ 的余数，所以固定一个模 $d$ 的余类来数。该余类内，源链按其位置可再分组。目标是从每组取若干块，使每块由同一类源链构成，并在 $J=g/(ed)$ 个循环起点各出现一次。这样，计算一个给定位置被命中的概率时，可把同一种计数分布在所有起点上的贡献加在一起。混入长短不同的链就失去了这个依据。

**怎样保证一整块确实放得下？** 在每段长链或短链各自的物理位置区间内，从第一个符合余类的槽开始取连续源指标。每取 $J$ 个，起点就覆盖一个完整周期。两段分别取整，构造给出的共同块数为

$$
q=d\left(\left\lfloor r/g\right\rfloor+
         \left\lfloor(h-r)/g\right\rfloor\right)
  \ge d\left(\left\lfloor h/g\right\rfloor-1\right).
$$

Lean 已验证槽位属于相应长短链、连续指标的余数覆盖和上述取整界。当 $\lfloor h/g\rfloor=2$ 时，每组仍可保证 $d$ 块。只固定一个模 $d$ 余类时，还能利用各组的边界余量。精确最优块数已有解析推导，其中的取整求和已进入 Lean。要得到任意四遍表的平均成本下界，还需证明这些波动经过后续排序后能留下足够多的逆序。全域最优指数 $25/18$ 仍是候选。[完整块的物理位置](https://github.com/EternalYMZ/Four-pass-Shellsort-bounds/blob/6bc015e6b704f5911713a58c4f476dcf71514998/Shellsort/FiberPacking.lean) · [边界余量的取整求和](https://github.com/EternalYMZ/Four-pass-Shellsort-bounds/blob/6bc015e6b704f5911713a58c4f476dcf71514998/Shellsort/WidthMultiplicity.lean)
