# Erdős Problem 263 — Lean 4 formalization (irrationality sequences)

Machine-verified Lean 4 + Mathlib formalizations for
[Erdős Problem 263](https://www.erdosproblems.com/263) (irrationality sequences), by Kimi K3 and T. Alexander Lystad

## Contents

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
lake build            # expect: Build completed successfully (8659 jobs);
                      # only warning: Statement.lean:63 declaration uses `sorry`
                      # (the declared open problem Q1)
grep -rn "sorry\|admit\|axiom" Erdos263.lean Erdos263/
# expect: only Statement.lean:64 (the open Q1) plus comment mentions
```

The toolchain (`leanprover/lean4:v4.32.2`) and the Mathlib revision (`v4.32.2`)
are pinned in `lean-toolchain` / `lakefile.toml` / `lake-manifest.json`; elan
installs the pinned toolchain automatically on the first `lake` command.

## Provenance and verification tier

Developed with AI assistance (LLM agents) under a machine-verification gate:
clean `lake build`, zero `sorry` outside the declared open obligation, and a
statement-fidelity audit against erdosproblems.com (the audit table is in
`Erdos263/Statement.lean`'s header). Lean verifies proofs against the formal
statement; the fidelity audit comparing the formal statement to the informal
problem is documented but is not itself machine-checked. AI involvement is
disclosed per Mathlib/Lean community conventions.

**Status of the problem:** Q1 (is `2^{2^n}` an irrationality sequence?) is open.
This repository proves the folklore growth *criterion* and the `b_n = a_n` base
case — not Q1.

## License

Apache-2.0 (see `LICENSE`). Copyright 2026 T. Alexander Lystad.
