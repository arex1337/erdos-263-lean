# The folklore growth criterion for irrationality sequences — human-readable proof

This is the human-readable companion to `Erdos263/Folklore.lean` (theorem
`folklore_criterion`). The Lean file is the proof of record; this document is the
same argument in prose, with the lemma correspondence noted.

**Theorem** (folklore criterion). *Let $(a_n)$ be a strictly increasing sequence
of positive integers, and suppose there exist $\varepsilon > 0$ and $c > 0$ such
that, for all sufficiently large $n$,
$$c\, a_n^{2+\varepsilon} \le a_{n+1}.$$
Then $(a_n)$ is an irrationality sequence: for **every** sequence $(b_n)$ of
positive integers with $b_n / a_n \to 1$, the sum $\sum_n 1/b_n$ is irrational.*

**Remark (the boundary).** The hypothesis fails for $a_n = 2^{2^n}$ by exactly an
$\varepsilon$: there $a_{n+1} = a_n^2$ identically, so
$a_{n+1}/a_n^{2+\varepsilon} = a_n^{-\varepsilon} \to 0$ for every
$\varepsilon > 0$. Whether $2^{2^n}$ is an irrationality sequence — Erdős Problem
263, Q1 — remains **open**; this theorem does not resolve it.

## Proof

Throughout, $0 < c \le 1$ without loss of generality, and "eventually" means "for
all $n$ past some threshold we are free to enlarge".

**Step 1 (bootstrap and forward iteration).** Since $c\,a_n^{2+\varepsilon} \le
a_{n+1}$ and $a_n \to \infty$, eventually $a_{n+1} \ge a_n^2$. Fix $M$ past the
threshold; induction gives
$$a_{M+k} \ge a_M^{2^k}.$$
Hence $\sum 1/a_n$ converges (compare a geometric series in the exponent), and
the tail satisfies
$$\sum_{n > N} \frac{1}{a_n} \le \frac{2}{a_{N+1}}.$$
*(Lean: `eventually_sq_le`, `pow_growth`, `summable_one_div_of_growth`,
`tail_le_two_div`.)*

**Step 2 (transfer to $(b_n)$).** Since $b_n/a_n \to 1$, eventually
$a_n/2 \le b_n \le 2a_n$. So $\sum 1/b_n$ converges, with the same tail estimate
up to a constant factor:
$$\sum_{n > N} \frac{1}{b_n} \le \frac{C_1}{a_{N+1}}.$$

**Step 3 (the integrality observation).** Suppose for contradiction that
$\sum_n 1/b_n = p/q$ with $p, q$ positive integers. For each $N$, multiply
through by $q \prod_{n \le N} b_n$: every term of the partial sum
$\sum_{n \le N} q\prod_{m \le N} b_m / b_n$ is an integer, so the remainder
$$q \Big(\prod_{n \le N} b_n\Big) \Big(\sum_{n > N} \frac{1}{b_n}\Big)$$
is also an integer, and it is **positive**. We show it tends to $0$, which is
absurd. *(Lean: `key_integrality`.)*

**Step 4 (backward iteration — the step most write-ups skip).** From
$c\,a_{n-1}^{2+\varepsilon} \le a_n$ we get, with $\theta = 1/(2+\varepsilon) < 1$,
$$a_{n-1} \le c^{-\theta}\, a_n^{\theta},$$
and iterating backwards,
$$a_{N-k} \le K\, a_N^{\theta^k}$$
for a constant $K$ depending only on $c$ and the threshold. Taking logs and
summing a geometric series in $\theta^k$ ($\sum_k \theta^k = 1/(1-\theta)$) gives
the product bound
$$\prod_{n \le N} a_n \le C^{N+1}\, a_N^{\sigma},
\qquad \sigma = \frac{1}{1-\theta} = \frac{2+\varepsilon}{1+\varepsilon}.$$
The point is $\sigma < 2 + \varepsilon$: the product of the first $N$ terms is
negligible next to $a_N^{2+\varepsilon}$. *(Lean: `backward_bound`,
`prod_bound`.)*

**Step 5 (contradiction).** Combine Steps 2–4, using $b_n \le 2a_n$ in the
product:
$$0 < q \Big(\prod_{n \le N} b_n\Big)\Big(\sum_{n>N} \frac1{b_n}\Big)
\le q\, C_2^{N+1}\, a_N^{\sigma} \cdot \frac{C_1}{a_{N+1}}
\le \frac{q\, C_1 C_2^{N+1}}{c}\, a_N^{\,\sigma - (2+\varepsilon)}.$$
Since $\sigma - (2+\varepsilon) = -\varepsilon(2+\varepsilon)/(1+\varepsilon) < 0$
and $a_N$ grows doubly exponentially while
$C_2^{N+1}$ grows only singly exponentially, the right side tends to $0$. A
sequence of positive integers cannot tend to $0$ — contradiction. $\blacksquare$

## Notes

- The same argument with $(b_n) = (a_n)$ yields the irrationality of
  $\sum 1/a_n$ itself whenever the growth condition holds; the special case
  $\sum_n 2^{-2^n}$ is proved separately in `Erdos263/Basic.lean`
  (`irrational_tsum_one_div_a₂₂`), where the tail bound is explicit.
- Kovač–Tao (arXiv:2406.17593) prove the complementary direction: slowly growing
  sequences ($a_{n+1}/a_n^2 \to 0$) are *not* irrationality sequences. Erdős
  263's Q1 sits exactly at the boundary $a_{n+1} \asymp a_n^2$, which neither
  result covers.

*This writeup was prepared with AI assistance and reviewed against the
machine-checked proof in `Erdos263/Folklore.lean`, which is authoritative.*
