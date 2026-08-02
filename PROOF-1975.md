# The monotone lim-criterion — a human-readable companion

**Theorem** (`irrational_of_oneSidedGrowth_monotone` in
`Erdos263/Erdos1975D.lean`). *Let `a` be a monotone sequence of positive
integers with `a_n^{1/2^n} → ∞`. Then `∑ 1/a_n` is irrational.*

This is Erdős's Theorem 1 (J. Math. Sci. 10 (1975), 1–7) at the lim level
for monotone sequences: the published theorem assumes the sequence
increasing with `a_n > n^{1+ε}` and `lim sup a_n^{1/2^n} = ∞`; the lim form
makes the polynomial-growth hypothesis automatic (`a_n ≥ 2^{2^n}`
eventually). The proof follows Erdős's own argument, formalized from his
scan (renyi.hu/~p_erdos/1976-44.pdf) via a disclosed page-image
transcription of equations (10)–(25).

## The proof

**Setup (the integrality machine).** Suppose `∑ 1/a_n = r ∈ ℚ`. Write
`P_N = ∏_{n≤N} a_n` and `T_N = ∑_{n>N} 1/a_n`. Then for every `N`,

```
m_N := r.den · P_N · T_N  is a positive integer.        (15)
```

(`one_le_prod_tail`; this is the paper's (15) and needs no monotonicity.)

**Case (9): spikes.** Suppose that for every `l ≥ 2` there are infinitely
many `j` with `a_{j+1} > P_j^l`. At such an index, the tail is at most
`2/a_{j+1}` (doubly-exponential decay of the summands), so
`m_j ≤ 2 r.den P_j / a_{j+1} ≤ 2 r.den / P_j^{l-1} → 0`, contradicting
(15). (`irrational_of_monotone_growth_and_spike_pow`; no monotonicity.)

**Case (10): the cap.** Otherwise there is an `l ≥ 2` with
`a_{j+1} ≤ P_j^l` for all large `j`. Induction gives the tower
`P_k ≤ P_{J₀}^{(l+1)^{k-J₀}}` — singly exponential in its exponent
(`cap_pow_tower`, the paper's (11)). Two inputs close this case:

- *Tail bound (the paper's (13)).* `T_k ≤ c·log a_{k+1} / a_{k+1}` by
  dyadic counting of the summands. This is the one place monotonicity is
  used: the initial segment of the tail is anchored at `a_{k+1}` via
  order. (`tail_le_loglog_of_monotone`.)
- *Escape records (the paper's (14)).* With `L_k := a_k^{1/2^k}` one has
  `lim sup L_k = ∞`, and Borel's argument (if records stop,
  `L_r ≤ (max_{k≤k₀} L_k)·∏(1+1/k²) < ∞`, contradiction) gives infinitely
  many `k` with `L_{k+1} > (1+1/k²)·max_{j≤k} L_j`.
  (`exists_escape_record`; no monotonicity.)

At an escape record, `P_k ≤ ((1+1/(k+1)²)⁻¹ · a_{k+1}^{1/2^{k+1}})^{2^{k+1}}`
(`prod_le_of_escape_record`, the paper's (17)), so the product loses a
factor `exp(Θ(2^k/k²))` against `a_{k+1}`. Feeding this and (13) into (15)
gives `a_{k+1} > exp((1+1/k²)^{2^k}/bc)`, which contradicts the tower for
large `k`. (`irrational_of_monotone_growth_case10`.)

The full statement is the disjunction of the two cases.
(`irrational_of_oneSidedGrowth_monotone`.)

## What is NOT proved here

- **The site's literal folklore form** (no monotonicity assumption): the
  only use of order is the initial-segment anchor in the (13) tail bound.
  A future-minimum anchor is under investigation; the statement currently
  stands as a `def` (`erdos_263_one_sided_folklore` in `OneSided.lean`),
  honestly unproved.
- **Q1** (`2^{2^n}` as an irrationality sequence): untouched, stated with
  an honest `sorry` in `Statement.lean`. The criterion fails for it by
  exactly an ε (`a_{n+1} = a_n²` identically).

## Verification

```
lake exe cache get && lake build     # Build completed successfully (8664 jobs)
grep -rn "sorry\|admit\|axiom" Erdos263.lean Erdos263/
# only Statement.lean:64 (the declared open Q1), plus comment mentions
#print axioms irrational_of_oneSidedGrowth_monotone
# [propext, Classical.choice, Quot.sound]
```

Developed with AI assistance under a machine-verification gate; the
Lean↔paper equation mapping rests on a disclosed human page-image
transcription of the renyi.hu scan, while the Lean statements and proofs
themselves are kernel-verified.
