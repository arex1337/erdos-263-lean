/-
Erdős Problem #263: exact adapter for the literal
`FormalConjectures.ErdosProblems.263.lean` folklore declaration.

Formal Conjectures does not assume `∀ n, 0 < a n` in this variant. Its
root-growth hypothesis nevertheless implies that `a n` is nonzero eventually.
We replace the finitely many zero entries by one, apply the proved positive
one-sided folklore theorem, and then remove the resulting finite rational
correction from the reciprocal sum.

Every declaration in this file is fully checked by Lean.
-/
import Mathlib
import Erdos263.Erdos1975F

open Filter Topology Finset
open scoped Topology

namespace Erdos263

/-- Replace zero entries by one. This changes only finitely many entries under
the root-growth hypothesis used by `formalConjectures_folklore`. -/
def normalizeZeros (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  if a n = 0 then 1 else a n

lemma normalizeZeros_pos (a : ℕ → ℕ) (n : ℕ) : 0 < normalizeZeros a n := by
  simp only [normalizeZeros]
  split <;> omega

/-- The exact literal type of `erdos_263.variants.folklore` in
google-deepmind/formal-conjectures PR #4679's head.

Unlike `erdos_263_one_sided_folklore_proof`, this statement has no explicit
positivity hypothesis. The limit forces eventual positivity; normalizing the
finite exceptional prefix changes the sum by a rational number, which
preserves irrationality. -/
theorem formalConjectures_folklore (a : ℕ → ℕ)
    (ha : Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (2 ^ n : ℝ))) atTop atTop) :
    Irrational (∑' n, 1 / (a n : ℝ)) := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 ha) 1
  have hane : ∀ n ≥ N, a n ≠ 0 := by
    intro n hn han
    have hge := hN n hn
    have hexp : (1 / (2 ^ n : ℝ)) ≠ 0 := by positivity
    rw [han, Nat.cast_zero, Real.zero_rpow hexp] at hge
    norm_num at hge
  have heq : a =ᶠ[atTop] normalizeZeros a := by
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    simp [normalizeZeros, hane n hn]
  have hgrowth : Tendsto
      (fun n : ℕ => (normalizeZeros a n : ℝ) ^ (1 / (2 : ℝ) ^ n)) atTop atTop := by
    apply ha.congr'
    filter_upwards [heq] with n hn
    rw [hn]
  have hg : OneSidedGrowth (normalizeZeros a) :=
    ⟨normalizeZeros_pos a, hgrowth⟩
  have hirr : Irrational (∑' n, 1 / (normalizeZeros a n : ℝ)) :=
    erdos_263_one_sided_folklore_proof (normalizeZeros a) hg
  have hsum_norm : Summable (fun n => 1 / (normalizeZeros a n : ℝ)) :=
    summable_one_div_of_oneSidedGrowth hg
  have hterm_eq : (fun n => 1 / (normalizeZeros a n : ℝ)) =ᶠ[atTop]
      (fun n => 1 / (a n : ℝ)) := by
    filter_upwards [heq] with n hn
    rw [hn]
  have hsum_a : Summable (fun n => 1 / (a n : ℝ)) :=
    hsum_norm.congr_atTop hterm_eq
  have htail :
      (∑' i, 1 / (normalizeZeros a (i + N) : ℝ)) =
        ∑' i, 1 / (a (i + N) : ℝ) := by
    apply tsum_congr
    intro i
    simp [normalizeZeros, hane (i + N) (by omega)]
  let qnorm : ℚ := ∑ n ∈ Finset.range N, 1 / (normalizeZeros a n : ℚ)
  let qa : ℚ := ∑ n ∈ Finset.range N, 1 / (a n : ℚ)
  have hqnorm :
      ((qnorm : ℚ) : ℝ) = ∑ n ∈ Finset.range N, 1 / (normalizeZeros a n : ℝ) := by
    simp [qnorm, Rat.cast_sum]
  have hqa :
      ((qa : ℚ) : ℝ) = ∑ n ∈ Finset.range N, 1 / (a n : ℝ) := by
    simp [qa, Rat.cast_sum]
  have hdecomp_norm := hsum_norm.sum_add_tsum_nat_add N
  have hdecomp_a := hsum_a.sum_add_tsum_nat_add N
  have htotal :
      (∑' n, 1 / (a n : ℝ)) =
        (∑' n, 1 / (normalizeZeros a n : ℝ)) - (((qnorm - qa : ℚ) : ℝ)) := by
    rw [← hdecomp_a, ← hdecomp_norm, htail, Rat.cast_sub, hqnorm, hqa]
    ring
  rw [htotal]
  exact hirr.sub_ratCast (qnorm - qa)

end Erdos263
