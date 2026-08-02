/-
Erdős Problem #263 — the ONE-SIDED FOLKLORE FORM.

Informal source (re-fetched 2026-08-01 with `Cache-Control: no-cache`;
page last edited 2026-04-02): https://www.erdosproblems.com/263 —

  "A folklore result states that ∑ 1/a_n is irrational whenever
   lim a_n^{1/2^n} = ∞."

Koizumi (arXiv:2504.05933v1, intro; stated as folklore without proof and
without a citation at that sentence — the paper cites Erdős–Graham
[Erdos_Graham_80] nearby, not here):
"if a sequence satisfies lim a_n^{2^{-n}} = ∞, then its reciprocal sum is
irrational."

FIDELITY NOTES (audit gate: compare against the site text above, line by line):

1. The hypothesis `lim a_n^{1/2^n} = ∞` is formalized as
   `Tendsto (fun n => (a n : ℝ) ^ (1 / (2 : ℝ) ^ n)) atTop atTop` (rpow;
   for positive `a n` this is exactly the real `2^n`-th root of `a n`
   tending to infinity). Neither the site nor Koizumi assumes monotonicity
   for THIS statement, so `OneSidedGrowth` has NO `StrictMono` — unlike
   `IsIrrationalitySequence` (the problem's Q1/Q2 notion, which does).
2. "a sequence" is of positive integers: `(∀ n, 0 < a n)`.
3. The conclusion is about the sequence ITSELF: `Irrational (∑' n, 1 / a n)`,
   NOT the perturbation form `IsIrrationalitySequence`. (The site derives the
   ratio-growth criterion, formalized in `Folklore.lean`, FROM this result.)
4. Indexing from n = 0 instead of n = 1 is immaterial (finite shift).
5. No convergence hypothesis: it is derivable (`summable_one_div_of_gap`,
   and independently `summable_one_div_of_oneSidedGrowth`).

SCOPE / STATUS (updated 2026-08-02): the full folklore theorem
(`erdos_263_one_sided_folklore`) is **PROVED** — zero-sorry in
`Erdos1975F.lean` (`erdos_263_one_sided_folklore_proof`), via the sorting
reduction: sort the sequence (non-decreasing rearrangement; the root
condition transfers by a counting lemma), then apply the monotone theorem
`irrational_of_oneSidedGrowth_monotone`. The direct product–tail route
documented below remains of independent interest:


* `OneSidedGrowth a → Summable (1/a)` (the hypothesis yields summability);
* the conditional theorem `irrational_tsum_one_div_of_perNGap`: the
  product–tail (integrality) method DOES prove irrationality under the
  per-index gap condition `PerNGap`. This isolates EXACTLY what the
  naive argument needs. (Note: `PerNGap` is believed strictly stronger than
  what the one-sided hypothesis gives — RESULTS.md §4 gives a HEURISTIC
  (not machine-checked) witness family suggesting that sequences with
  `a_n^{1/2^n} → ∞` exist for which the per-N gap fails at EVERY N, so the
  folklore theorem is not expected to follow from this reduction alone.
  The missing lemma is recorded in RESULTS.md.)

ZERO sorry/admit/axiom in this file.
-/
import Mathlib
import Erdos263.Folklore

open Filter Topology Finset
open scoped Topology

namespace Erdos263

variable {a : ℕ → ℕ}

/-- The one-sided growth hypothesis of the folklore result: `a` is a sequence
of positive integers with `a_n^{1/2^n} → ∞` (real `2^n`-th root tends to
infinity). NO monotonicity is assumed, matching the site's statement. -/
def OneSidedGrowth (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧
  Tendsto (fun n => (a n : ℝ) ^ (1 / (2 : ℝ) ^ n)) atTop atTop

/-- **The one-sided folklore form of Erdős #263 (PROVED 2026-08-02):** every
sequence of positive integers with `a_n^{1/2^n} → ∞` has irrational
reciprocal sum. PROVED zero-sorry in `Erdos1975F.lean`
(`erdos_263_one_sided_folklore_proof`) via the sorting reduction
(sort-then-apply the monotone theorem); see that file for the proof. -/
def erdos_263_one_sided_folklore : Prop :=
  ∀ a : ℕ → ℕ, OneSidedGrowth a → Irrational (∑' n, 1 / (a n : ℝ))

/-- **Per-index gap property** (the sufficient condition the product–tail
method needs): for every constant `B ≥ 2` there is an index `N` such that
`a_{N+1+k} ≥ (B·P_N)^{2^k}` for all `k`, where `P_N = ∏_{n ≤ N} a_n`. -/
def PerNGap (a : ℕ → ℕ) : Prop :=
  ∀ B : ℝ, 2 ≤ B → ∃ N : ℕ, ∀ k : ℕ,
    (B * ∏ n ∈ Finset.range (N + 1), (a n : ℝ)) ^ (2 ^ k) ≤ (a (N + 1 + k) : ℝ)

/-- One-sided growth implies `a_n ≥ 2^{2^n}` eventually (take the threshold
`u_n := a_n^{1/2^n} ≥ 2` and raise back to the `2^n`-th power). -/
lemma eventually_ge_of_oneSidedGrowth (hg : OneSidedGrowth a) :
    ∀ᶠ n in atTop, (a₂₂ n : ℝ) ≤ (a n : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := (tendsto_atTop_atTop.1 hg.2) 2
  refine eventually_atTop.2 ⟨N₀, fun n hn => ?_⟩
  have hbase : (0 : ℝ) ≤ (a n : ℝ) := by positivity
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hu : (2 : ℝ) ≤ (a n : ℝ) ^ (1 / (2 : ℝ) ^ n) := hN₀ n hn
  have key : ((a n : ℝ) ^ (1 / (2 : ℝ) ^ n)) ^ (2 ^ n) = (a n : ℝ) := by
    have hcast : (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ n := by push_cast; rfl
    rw [← Real.rpow_natCast (((a n : ℝ) ^ (1 / (2 : ℝ) ^ n))) (2 ^ n), hcast,
      ← Real.rpow_mul hbase]
    have hmul : (1 / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = 1 := div_mul_cancel₀ (1 : ℝ) h2n.ne'
    rw [hmul, Real.rpow_one]
  have hle : (2 : ℝ) ^ (2 ^ n) ≤ (a n : ℝ) :=
    key ▸ pow_le_pow_left₀ (by norm_num) hu (2 ^ n)
  have hcast2 : ((a₂₂ n : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ n) := by
    unfold a₂₂
    push_cast
    rfl
  rw [hcast2]
  exact hle

/-- One-sided growth implies summability of `∑ 1/a_n` (compare with
`∑ 1/2^{2^n}`, `Basic.summable_one_div_a₂₂`). -/
lemma summable_one_div_of_oneSidedGrowth (hg : OneSidedGrowth a) :
    Summable (fun n => 1 / (a n : ℝ)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_ge_of_oneSidedGrowth hg)
  have hshift22 : Summable (fun n => 1 / (a₂₂ (n + N₀) : ℝ)) :=
    (_root_.summable_nat_add_iff N₀).2 summable_one_div_a₂₂
  have hle : ∀ n : ℕ, (1 / (a (n + N₀) : ℝ)) ≤ 1 / (a₂₂ (n + N₀) : ℝ) := by
    intro n
    exact one_div_le_one_div_of_le (by exact_mod_cast a₂₂_pos (n + N₀))
      (hN₀ (n + N₀) (Nat.le_add_left N₀ n))
  have hsum : Summable (fun n => 1 / (a (n + N₀) : ℝ)) :=
    Summable.of_nonneg_of_le (fun n => one_div_nonneg.mpr (by positivity)) hle hshift22
  exact (_root_.summable_nat_add_iff N₀).1 hsum

/-- The gap property implies summability (the tail is dominated by a
geometric series with ratio `1/2`). -/
lemma summable_one_div_of_gap (hapos : ∀ n, 0 < a n) (hgap : PerNGap a) :
    Summable (fun n => 1 / (a n : ℝ)) := by
  obtain ⟨N, hN⟩ := hgap 2 (le_refl 2)
  have hPpos : (0 : ℝ) < ∏ n ∈ Finset.range (N + 1), (a n : ℝ) :=
    Finset.prod_pos (fun n _ => by exact_mod_cast hapos n)
  have hP1 : (1 : ℝ) ≤ ∏ n ∈ Finset.range (N + 1), (a n : ℝ) := by
    have h1 : (1 : ℕ) ≤ ∏ n ∈ Finset.range (N + 1), a n :=
      Finset.prod_pos (fun n _ => hapos n)
    exact_mod_cast h1
  have hx : (2 : ℝ) ≤ 2 * ∏ n ∈ Finset.range (N + 1), (a n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hP1 (by norm_num : (0 : ℝ) ≤ 2)
    simpa using h
  have hN' : ∀ k : ℕ, (2 * ∏ n ∈ Finset.range (N + 1), (a n : ℝ)) ^ (2 ^ k) ≤
      (a (k + (N + 1)) : ℝ) := by
    intro k
    have h := hN k
    rwa [show N + 1 + k = k + (N + 1) from by omega] at h
  have hterm : ∀ k : ℕ, (1 / (a (k + (N + 1)) : ℝ)) ≤ (1 / (2 : ℝ)) ^ k * (1 / 2) := by
    intro k
    have h3 : (2 : ℝ) ^ (k + 1) ≤ (a (k + (N + 1)) : ℝ) :=
      le_trans (le_trans (pow_le_pow_right₀ (by norm_num) (two_pow_ge_succ k))
        (pow_le_pow_left₀ (by norm_num) hx (2 ^ k))) (hN' k)
    calc (1 / (a (k + (N + 1)) : ℝ)) ≤ 1 / (2 : ℝ) ^ (k + 1) :=
          one_div_le_one_div_of_le (pow_pos (by norm_num) _) h3
    _ = (1 / (2 : ℝ)) ^ (k + 1) := by rw [div_pow, one_pow]
    _ = (1 / (2 : ℝ)) ^ k * (1 / 2) := by rw [pow_succ]
  have hgsumm : Summable (fun k : ℕ => (1 / (2 : ℝ)) ^ k * (1 / 2)) :=
    summable_geometric_two.mul_right _
  have hsum : Summable (fun k : ℕ => 1 / (a (k + (N + 1)) : ℝ)) :=
    Summable.of_nonneg_of_le (fun k => one_div_nonneg.mpr (by positivity)) hterm hgsumm
  exact (_root_.summable_nat_add_iff (N + 1)).1 hsum

/-- **Tail bound at a gap index:** if `a_{N+1+k} ≥ x^{2^k}` for all `k` with
`x := B·P_N ≥ 2`, then the tail `∑_{k ≥ 0} 1/a_{N+1+k}` is at most `2/x`
(geometric comparison, `2^k ≥ k+1`). -/
lemma tail_le_of_gap (hapos : ∀ n, 0 < a n) {B : ℝ} (hB : 2 ≤ B) {N : ℕ}
    (hgap : ∀ k : ℕ, (B * ∏ n ∈ Finset.range (N + 1), (a n : ℝ)) ^ (2 ^ k) ≤
      (a (N + 1 + k) : ℝ)) :
    (∑' k, 1 / (a (k + (N + 1)) : ℝ)) ≤
      2 / (B * ∏ n ∈ Finset.range (N + 1), (a n : ℝ)) := by
  have hPpos : (0 : ℝ) < ∏ n ∈ Finset.range (N + 1), (a n : ℝ) :=
    Finset.prod_pos (fun n _ => by exact_mod_cast hapos n)
  have hP1 : (1 : ℝ) ≤ ∏ n ∈ Finset.range (N + 1), (a n : ℝ) := by
    have h1 : (1 : ℕ) ≤ ∏ n ∈ Finset.range (N + 1), a n :=
      Finset.prod_pos (fun n _ => hapos n)
    exact_mod_cast h1
  set x : ℝ := B * ∏ n ∈ Finset.range (N + 1), (a n : ℝ) with hxdef
  have hx2 : (2 : ℝ) ≤ x := by
    calc (2 : ℝ) = 2 * 1 := by norm_num
    _ ≤ B * ∏ n ∈ Finset.range (N + 1), (a n : ℝ) :=
        mul_le_mul hB hP1 (by norm_num) (by linarith [hB])
  have hxpos : (0 : ℝ) < x := by linarith [hx2]
  have hN' : ∀ k : ℕ, x ^ (2 ^ k) ≤ (a (k + (N + 1)) : ℝ) := by
    intro k
    have h := hgap k
    rwa [show N + 1 + k = k + (N + 1) from by omega] at h
  have hterm : ∀ k : ℕ, (1 / (a (k + (N + 1)) : ℝ)) ≤ (1 / x) * (1 / x) ^ k := by
    intro k
    have h3 : x ^ (k + 1) ≤ (a (k + (N + 1)) : ℝ) :=
      le_trans (pow_le_pow_right₀ (by linarith [hx2] : (1 : ℝ) ≤ x)
        (two_pow_ge_succ k)) (hN' k)
    calc (1 / (a (k + (N + 1)) : ℝ)) ≤ 1 / x ^ (k + 1) :=
          one_div_le_one_div_of_le (pow_pos hxpos _) h3
    _ = (1 / x) ^ (k + 1) := by rw [div_pow, one_pow]
    _ = (1 / x) * (1 / x) ^ k := by rw [pow_succ']
  have h1x0 : (0 : ℝ) ≤ 1 / x := one_div_nonneg.mpr hxpos.le
  have h1x1 : 1 / x < 1 := (div_lt_one hxpos).mpr (by linarith [hx2])
  have hgsumm : Summable (fun k : ℕ => (1 / x) * (1 / x) ^ k) :=
    (summable_geometric_of_lt_one h1x0 h1x1).mul_left _
  have hlsumm : Summable (fun k : ℕ => 1 / (a (k + (N + 1)) : ℝ)) :=
    Summable.of_nonneg_of_le (fun k => one_div_nonneg.mpr (by positivity)) hterm hgsumm
  have hle : (∑' k, 1 / (a (k + (N + 1)) : ℝ)) ≤ ∑' k, (1 / x) * (1 / x) ^ k :=
    Summable.tsum_le_tsum hterm hlsumm hgsumm
  have hsum : (∑' k : ℕ, (1 / x) * (1 / x) ^ k) = (1 / x) * (1 / (1 - 1 / x)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one h1x0 h1x1, inv_eq_one_div]
  have hbound : (1 / x) * (1 / (1 - 1 / x)) ≤ 2 / x := by
    have h1m : (0 : ℝ) < 1 - 1 / x := by linarith [h1x1]
    have hy : 1 / (1 - 1 / x) ≤ 2 := by
      rw [div_le_iff₀ h1m]
      have h5 : 1 / x ≤ 1 / 2 := by
        rw [div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 1) hxpos
          (by norm_num : (0 : ℝ) < 2)]
        linarith [hx2]
      linarith [h5]
    calc (1 / x) * (1 / (1 - 1 / x)) ≤ (1 / x) * 2 :=
          mul_le_mul_of_nonneg_left hy h1x0
    _ = 2 / x := by rw [mul_comm, mul_one_div]
  calc (∑' k, 1 / (a (k + (N + 1)) : ℝ)) ≤ (1 / x) * (1 / (1 - 1 / x)) :=
        le_trans hle (le_of_eq hsum)
  _ ≤ 2 / x := hbound

/-- **Conditional one-sided folklore (VERIFIED REDUCTION):** if a sequence of
positive integers satisfies the per-index gap property `PerNGap`, then its
reciprocal sum is irrational. Proof: if `∑ 1/a_n = r ∈ ℚ`, integrality
(`key_integrality` with `b := a`) gives a positive integer
`z = r.den · P_N · T_N ≥ 1`; the gap at `B := 4·r.den` forces
`r.den · P_N · T_N ≤ 1/2` — contradiction. -/
theorem irrational_tsum_one_div_of_perNGap (hapos : ∀ n, 0 < a n) (hgap : PerNGap a) :
    Irrational (∑' n, 1 / (a n : ℝ)) := by
  have hsuma : Summable (fun n => 1 / (a n : ℝ)) := summable_one_div_of_gap hapos hgap
  rintro ⟨r, hr⟩
  have hdenpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  set B : ℝ := 4 * (r.den : ℝ) with hBdef
  have hB : (2 : ℝ) ≤ B := by
    have h1 : (1 : ℝ) ≤ (r.den : ℝ) := by exact_mod_cast r.den_pos
    linarith [h1]
  obtain ⟨N, hN⟩ := hgap B hB
  obtain ⟨z, hz⟩ := key_integrality hapos hsuma r hr N
  have hTpos : (0 : ℝ) < ∑' i, (1 / (a (i + (N + 1)) : ℝ)) :=
    tail_b_pos hapos hsuma N
  have hPpos : (0 : ℝ) < ∏ n ∈ Finset.range (N + 1), (a n : ℝ) :=
    Finset.prod_pos (fun n _ => by exact_mod_cast hapos n)
  have hzpos : (0 : ℤ) < z := by
    have h : (0 : ℝ) < (z : ℝ) := by
      rw [hz]
      exact mul_pos (mul_pos hdenpos hPpos) hTpos
    exact_mod_cast h
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by
    have h1z : (1 : ℤ) ≤ z := Int.lt_iff_add_one_le.1 hzpos
    exact_mod_cast h1z
  have hle := tail_le_of_gap hapos hB hN
  have hcom : (r.den : ℝ) * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
      (∑' i, (1 / (a (i + (N + 1)) : ℝ))) ≤ 2 * (r.den : ℝ) / B := by
    have h1 := mul_le_mul_of_nonneg_left hle (le_of_lt (mul_pos hdenpos hPpos))
    have h2 : (r.den : ℝ) * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
        (2 / (B * ∏ n ∈ Finset.range (N + 1), (a n : ℝ))) = 2 * (r.den : ℝ) / B := by
      rw [← mul_div_assoc,
        div_eq_div_iff (mul_pos (by linarith [hB] : (0 : ℝ) < B) hPpos).ne'
          (by linarith [hB] : (0 : ℝ) < B).ne']
      ring
    rw [h2] at h1
    exact h1
  have hfin : 2 * (r.den : ℝ) / B = 1 / 2 := by
    rw [hBdef,
      div_eq_div_iff (mul_pos (by norm_num : (0 : ℝ) < 4) hdenpos).ne'
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  rw [hz] at hz1
  linarith [hz1, hcom, hfin]

end Erdos263
