# Erdős Problem 263 — Lean 4 formalization (irrationality sequences)

Machine-verified Lean 4 + Mathlib formalizations for
[Erdős Problem 263](https://www.erdosproblems.com/263) (irrationality sequences), by Kimi K3 and T. Alexander Lystad

**v2.0 headline (2026-08-02):** `erdos_263_one_sided_folklore_proof` —
**the site's literal folklore form, no monotonicity: every sequence of
positive integers `a` with `a_n^{1/2^n} → ∞` has irrational reciprocal
sum.** The proof sorts the sequence (non-decreasing rearrangement; the
root condition transfers by a counting lemma) and applies the v1.1 monotone
theorem. We are aware of no prior proof of the no-monotonicity form;
published proofs (Erdős 1975, Hančl 1993) assume increasing. Zero `sorry`;
axioms `[propext, Classical.choice, Quot.sound]` only. The limsup analogue
is false (lim is load-bearing; interleaved-Sylvester counterexample,
rational sum 3/2).

**v1.1 headline (2026-08-02):** `irrational_of_oneSidedGrowth_monotone` —
**for every monotone sequence of positive integers `a` with
`a_n^{1/2^n} → ∞`, the sum `∑ 1/a_n` is irrational.** This is Erdős's
Theorem 1 (J. Math. Sci. 10 (1975), 1–7) at the lim level for monotone
sequences. Zero `sorry`; axioms
`[propext, Classical.choice, Quot.sound]` only. *Classical landscape
note:* Badea's Theorem A (Acta Arith. 63 (1993), 313–323 — the
fast-growth criterion `a_{n+1} > a_n² − a_n + 1` ⟹ irrational) does NOT
subsume this case: its condition is pairwise and fails at dip indices,
which Erdős's record machinery (formalized here) handles.

## Contents

- `Erdos263/Erdos1975.lean`, `Erdos1975B.lean`, `Erdos1975C.lean`,
  `Erdos1975D.lean` — the Erdős-1975 development (41 declarations): the
  denominator-product recurrence, the integrality machine, the case-(9)
  spike theorem, the escape-record machinery, and the case-(12) assembly
  closing in `irrational_of_oneSidedGrowth_monotone`.
- `Erdos263/OneSided.lean` — fidelity-audited formal statement of the
  one-sided folklore form plus supporting zero-sorry lemmas (summability,
  the conditional per-N-gap reduction). The site's literal no-monotonicity
  form remains **open** — the gap is exactly the `Monotone` hypothesis in
  the dyadic tail bound.
- `Erdos263/Folklore.lean` — **`folklore_criterion`**: strictly increasing
  positive integers with `∃ ε > 0, ∃ c > 0, ∀ᶠ n, c·a_n^{2+ε} ≤ a_{n+1}` are
  irrationality sequences (for every `b_n/a_n → 1`, `∑ 1/b_n` is irrational).
  Complete proof, **zero `sorry`**.
- `Erdos263/Basic.lean` — supporting zero-`sorry` package, including
  `irrational_tsum_one_div_a₂₂` (`∑ 1/2^{2^n}` is irrational) and the boundary
  identity `a_{n+1} = a_n²` for `a_n = 2^{2^n}`.
- `Erdos263/Statement.lean` — fidelity-audited formal statement of the problem.
  Q1 (`2^{2^n}`) is stated with an honest `sorry` — it remains **open**; the
  criterion fails for it by exactly an ε.

## Verify it yourself

Requires [elan](https://leanprover-community.github.io/get_started.html) (Lean 4
toolchain manager):

```bash
git clone https://github.com/arex1337/erdos-263-lean
cd erdos-263-lean
lake exe cache get    # downloads the prebuilt Mathlib cache (~GB, one-time)
lake build            # expect: Build completed successfully (8664 jobs);
                      # sole sorry-warning: Statement.lean:63 declaration uses `sorry`
                      # (the declared open problem Q1)
grep -rn "sorry\|admit\|axiom" Erdos263.lean Erdos263/
# expect: only Statement.lean:64 (the open Q1) plus comment mentions
```

Optional independent axiom check, from a file importing `Erdos263`:

```lean
#print axioms irrational_of_oneSidedGrowth_monotone
-- expect: [propext, Classical.choice, Quot.sound]
```

## Provenance and verification tier

Developed with AI assistance (LLM agents) under a machine-verification gate:
clean `lake build`, zero `sorry` outside the declared open obligation, and
statement-fidelity audits against erdosproblems.com and the Erdős 1975 scan
(renyi.hu). The mapping from the Lean development to Erdős's published
equation numbers rests on a disclosed human page-image transcription of the
scan; the Lean statements and proofs themselves are kernel-verified. Lean
verifies proofs against the formal statement; fidelity audits comparing
statement to problem are documented but are not themselves machine-checked.
AI involvement is disclosed per Mathlib/Lean community conventions.

Archived releases: v1.0 https://doi.org/10.5281/zenodo.21736956 ·
v1.1 https://doi.org/10.5281/zenodo.21752787 ·
always-latest https://doi.org/10.5281/zenodo.21736955

License: Apache-2.0.
