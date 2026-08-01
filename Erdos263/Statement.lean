/-
Erdős Problem #263 — formal statement (fidelity-audited).

Source of the informal statement: https://www.erdosproblems.com/263
(page last edited 2026-04-02; fetched 2026-07-31; LaTeX: /latex/263).

  "Let a_n be an increasing sequence of positive integers such that for every
   sequence of positive integers b_n with b_n/a_n → 1 the sum ∑ 1/b_n is
   irrational. Is a_n = 2^(2^n) such a sequence? Must such a sequence satisfy
   a_n^(1/n) → ∞?"

FIDELITY NOTES (the audit gate re-checks this table; see RESULTS.md):

1. "increasing" is REQUIRED and is formalized as `StrictMono a`. The site
   originally omitted it; DeepMind's Lean falsification of Q2 (2026, in
   FormalConjectures, `erdos_263.parts.ii`) uses a definition WITHOUT any
   monotonicity hypothesis, and its counterexample is NOT increasing. The
   community formalization therefore does not cover the corrected statement:
   our definition adds `StrictMono a` back. (Koizumi, arXiv:2504.05933,
   footnote 1, notes Erdős–Graham originally said strictly increasing and
   relaxes to non-decreasing; we follow Erdős–Graham / the site: strict.)

2. "for every sequence of positive integers b_n with b_n/a_n → 1": formalized
   as `(∀ n, 0 < b n) → Tendsto (fun n => (b n : ℝ) / (a n : ℝ)) atTop (𝓝 1)`.
   For positive sequences b/a → 1 ↔ a/b → 1; FormalConjectures uses a/b → 1.
   Equivalent — no fidelity loss.

3. "the sum ∑ 1/b_n is irrational": `Irrational (∑' n, 1 / (b n : ℝ))`.
   Note `∑'` is 0 for non-summable series, and 0 is rational, so the
   formalization correctly forces convergence too (a divergent b-series makes
   the implication's conclusion false — matching the informal reading, where
   the claim "the sum is irrational" presupposes convergence). No loss.

4. Q1 asks about the specific sequence n ↦ 2^(2^n), which IS strictly
   increasing (proved in `Basic.lean`), so Q1 is unaffected by the
   increasing-variant issue.

5. Q2's truth value is OPEN for the increasing variant (the published
   counterexample is not increasing). We therefore state Q2 as a `def` of the
   proposition under question, not as a theorem picking a side.
-/
import Mathlib

open Filter Topology
open scoped Topology

namespace Erdos263

/-- An **irrationality sequence** (Type 2, in the terminology of Kovač–Tao):
a strictly increasing sequence of positive integers `a` such that for EVERY
sequence of positive integers `b` with `b n / a n → 1`, the sum `∑' n, 1 / b n`
is irrational. Erdős Problem #263, statement of erdosproblems.com as of
2026-04-02 (with the required increasing hypothesis). -/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ StrictMono a ∧
  (∀ b : ℕ → ℕ, (∀ n, 0 < b n) →
    Tendsto (fun n => (b n : ℝ) / (a n : ℝ)) atTop (𝓝 1) →
    Irrational (∑' n, 1 / (b n : ℝ)))

/-- **Q1 (OPEN):** is `a_n = 2^(2^n)` an irrationality sequence?
This is the main open obligation of this project. The `sorry` here is the
honest marker of the gap: everything in `Basic.lean` is proved, this is not. -/
theorem erdos_263_q1 : IsIrrationalitySequence (fun n => 2 ^ 2 ^ n) := by
  sorry

/-- **Q2 (OPEN for the increasing variant):** must every irrationality sequence
satisfy `a_n^(1/n) → ∞`? Stated as a proposition; no side is taken.
(Without `StrictMono` inside `IsIrrationalitySequence`, this is FALSE —
DeepMind's Lean-verified counterexample, FormalConjectures `erdos_263.parts.ii`;
with `StrictMono`, no resolution is known to us as of 2026-07-31.) -/
def erdos_263_q2_statement : Prop :=
  ∀ a : ℕ → ℕ, IsIrrationalitySequence a →
    Tendsto (fun n => (a n : ℝ) ^ (1 / (n : ℝ))) atTop atTop

end Erdos263
