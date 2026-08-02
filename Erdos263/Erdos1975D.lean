/-
Erdős Problem #263 — Erdős 1975 route, SESSION 4: the PLUS-slack
(escape) record machinery and the case-(12) assembly.

SIGN CORRECTION (audit finding F1): the page-image ground truth
(`code/phase1/erdos1975_eq10-25_transcription.md`, authoritative over the
garbled OCR text layer) shows the paper's (14) is
`L_{k+1} > (1 + 1/k²)·max_{j≤k} L_j` — PLUS slack — and (17) is
`n_{k+1} > M_k·(1+1/k²)^{2^{k+1}}`, and the paper's (10) cap is
`n_{k+1} < M_k^l` (a POWER of the product, not `l^{M_k}`). The
minus-slack versions (`exists_near_record`, `prod_le_of_near_record`) are
true but the mirror image of what the endgame needs. This file contains
the corrected machinery, and the case-(12) assembly
`irrational_of_monotone_growth_case10`.

ZERO sorry/admit/axiom in this file.
-/
import Mathlib
import Erdos263.Erdos1975C

open Filter Topology Finset
open scoped Topology

namespace Erdos263

variable {a : ℕ → ℕ}

/-! ### The convergent product `∏ (1 + 1/j²)` -/

/-- Telescoping product: `∏_{i<n} (i+2)/(i+1) = n+1` (in ℝ). -/
lemma prod_ratio_succ (n : ℕ) :
    ∏ i ∈ Finset.range n, ((i : ℝ) + 2) / ((i : ℝ) + 1) = (n : ℝ) + 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, ih]
      have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp [h1]
      push_cast
      ring

/-- Telescoping product: `∏_{i<n} (i+2)/(i+3) = 2/(n+2)` (in ℝ). -/
lemma prod_ratio_succ' (n : ℕ) :
    ∏ i ∈ Finset.range n, ((i : ℝ) + 2) / ((i : ℝ) + 3) = 2 / ((n : ℝ) + 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, ih]
      have h1 : ((k : ℝ) + 2) ≠ 0 := by positivity
      have h2 : ((k : ℝ) + 3) ≠ 0 := by positivity
      field_simp [h1, h2]
      push_cast
      ring

/-- **Convergent product bound:** `∏_{i<n} (1 + 1/(i+2)²) ≤ 2`. -/
lemma prod_one_add_inv_sq_le_two (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 + 1 / (((i : ℝ) + 2) ^ 2)) ≤ 2 := by
  have hfactor : ∀ i ∈ Finset.range n,
      (1 + 1 / (((i : ℝ) + 2) ^ 2)) ≤
        (((i : ℝ) + 2) / ((i : ℝ) + 1)) * (((i : ℝ) + 2) / ((i : ℝ) + 3)) := by
    intro i _
    have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (i : ℝ) + 3 := by positivity
    have key : (1 + 1 / (((i : ℝ) + 2) ^ 2)) * (((i : ℝ) + 1) * ((i : ℝ) + 3)) ≤
        ((i : ℝ) + 2) * ((i : ℝ) + 2) := by
      have h3 : ((i : ℝ) + 2) ^ 2 ≠ 0 := by positivity
      rw [one_add_div h3]
      have e : ((((i : ℝ) + 2) ^ 2 + 1) / ((i : ℝ) + 2) ^ 2) *
          (((i : ℝ) + 1) * ((i : ℝ) + 3)) =
          ((((i : ℝ) + 2) ^ 2 + 1) * (((i : ℝ) + 1) * ((i : ℝ) + 3))) /
            (((i : ℝ) + 2) ^ 2) := by
        rw [div_mul_eq_mul_div]
      rw [e, div_le_iff₀ (by positivity : (0 : ℝ) < ((i : ℝ) + 2) ^ 2)]
      nlinarith [sq_nonneg ((i : ℝ) + 2)]
    calc (1 + 1 / (((i : ℝ) + 2) ^ 2))
        = ((1 + 1 / (((i : ℝ) + 2) ^ 2)) * (((i : ℝ) + 1) * ((i : ℝ) + 3))) /
            (((i : ℝ) + 1) * ((i : ℝ) + 3)) := by
            rw [mul_div_assoc, div_self (mul_pos h1 h2).ne', mul_one]
      _ ≤ (((i : ℝ) + 2) * ((i : ℝ) + 2)) / (((i : ℝ) + 1) * ((i : ℝ) + 3)) :=
            (div_le_div_iff_of_pos_right (mul_pos h1 h2)).mpr key
      _ = (((i : ℝ) + 2) / ((i : ℝ) + 1)) * (((i : ℝ) + 2) / ((i : ℝ) + 3)) := by
            rw [div_mul_div_comm]
  have hprod := Finset.prod_le_prod (fun i _ => by positivity) hfactor
  rw [Finset.prod_mul_distrib, prod_ratio_succ, prod_ratio_succ'] at hprod
  have h5 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  calc ∏ i ∈ Finset.range n, (1 + 1 / (((i : ℝ) + 2) ^ 2))
      ≤ ((n : ℝ) + 1) * (2 / ((n : ℝ) + 2)) := hprod
    _ ≤ 2 := by
        rw [← mul_div_assoc, div_le_iff₀ h5]
        nlinarith [h5]

/-- **The accumulating escape factor is bounded:**
`∏_{j<m} (1 + 1/(k₀+1+j)²) ≤ 4`. -/
lemma prod_escape_factor_le_four (k₀ m : ℕ) :
    ∏ j ∈ Finset.range m, (1 + 1 / (((k₀ : ℝ) + 1 + (j : ℝ)) ^ 2)) ≤ 4 := by
  have hper : ∀ j ∈ Finset.range m,
      (1 + 1 / (((k₀ : ℝ) + 1 + (j : ℝ)) ^ 2)) ≤
        (1 + 1 / ((1 : ℝ) + (j : ℝ)) ^ 2) := by
    intro j _
    have h1 : (0 : ℝ) < (1 : ℝ) + (j : ℝ) := by positivity
    have h2 : (1 : ℝ) + (j : ℝ) ≤ (k₀ : ℝ) + 1 + (j : ℝ) := by
      have h3 : (0 : ℝ) ≤ (k₀ : ℝ) := by positivity
      linarith [h3]
    have h4 : ((1 : ℝ) + (j : ℝ)) ^ 2 ≤ ((k₀ : ℝ) + 1 + (j : ℝ)) ^ 2 :=
      pow_le_pow_left₀ h1.le h2 _
    have h5 : 1 / (((k₀ : ℝ) + 1 + (j : ℝ)) ^ 2) ≤ 1 / ((1 : ℝ) + (j : ℝ)) ^ 2 :=
      one_div_le_one_div_of_le (pow_pos h1 _) h4
    linarith [h5]
  have hprod := Finset.prod_le_prod (fun j _ => by positivity) hper
  have hbound2 : ∏ j ∈ Finset.range m, (1 + 1 / ((1 : ℝ) + (j : ℝ)) ^ 2) ≤ 4 := by
    cases m with
    | zero => simp
    | succ m' =>
        rw [Finset.prod_range_succ']
        have e2 : (1 + 1 / ((1 : ℝ) + ((0 : ℕ) : ℝ)) ^ 2) = 2 := by norm_num
        have e3 : (∏ j ∈ Finset.range m',
            (1 + 1 / ((1 : ℝ) + ((j + 1 : ℕ) : ℝ)) ^ 2)) =
            ∏ j ∈ Finset.range m', (1 + 1 / (((j : ℝ) + 2) ^ 2)) := by
          apply Finset.prod_congr rfl
          intro j _
          congr 3
          push_cast
          ring
        rw [e3, e2]
        have h3 := prod_one_add_inv_sq_le_two m'
        have hnn : (0 : ℝ) ≤ ∏ j ∈ Finset.range m', (1 + 1 / (((j : ℝ) + 2) ^ 2)) := by
          apply Finset.prod_nonneg
          intro j _
          positivity
        nlinarith [h3, hnn]
  exact le_trans hprod hbound2

/-- Every factor of the escape product is at least 1. -/
lemma one_le_prod_escape_factor (k₀ m : ℕ) :
    (1 : ℝ) ≤ ∏ j ∈ Finset.range m, (1 + 1 / (((k₀ : ℝ) + 1 + (j : ℝ)) ^ 2)) := by
  apply Finset.one_le_prod
  intro j _
  nlinarith [show (0 : ℝ) < 1 / (((k₀ : ℝ) + 1 + (j : ℝ)) ^ 2) from by positivity]

/-- The escape-factor product is monotone in the length. -/
lemma prod_escape_factor_mono (k₀ : ℕ) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    (∏ j ∈ Finset.range m₁, (1 + 1 / (((k₀ : ℝ) + 1 + (j : ℝ)) ^ 2))) ≤
      (∏ j ∈ Finset.range m₂, (1 + 1 / (((k₀ : ℝ) + 1 + (j : ℝ)) ^ 2))) := by
  rw [show m₂ = m₁ + (m₂ - m₁) from by omega]
  rw [Finset.prod_range_add]
  apply le_mul_of_one_le_right_nn (by positivity)
  apply Finset.one_le_prod
  intro j _
  nlinarith [show (0 : ℝ) < 1 / (((k₀ : ℝ) + 1 + ((m₁ + j : ℕ) : ℝ)) ^ 2) from by
    positivity]

/-! ### The escape record (PLUS slack) -/

/-- **Escape records exist** (Erdős 1975, eq. (14) as transcribed from the
page image; Borel's idea): if `L → ∞` and `L ≥ 0`, then for every `k₀`
there is a `k ≥ k₀` whose next term escapes every previous term by the
factor `1 + 1/(k+1)²`: `(1 + 1/(k+1)²)·L_j < L_{k+1}` for all `j ≤ k`. -/
theorem exists_escape_record {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hL0 : ∀ n, 0 ≤ L n) (k₀ : ℕ) :
    ∃ k ≥ k₀, ∀ j ≤ k, (1 + 1 / ((k : ℝ) + 1) ^ 2) * L j < L (k + 1) := by
  by_contra h
  push Not at h
  set B := (Finset.range (k₀ + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos k₀)⟩ L
    with hBdef
  have hBi : ∀ i ≤ k₀, L i ≤ B := by
    intro i hi
    have hmem : i ∈ Finset.range (k₀ + 1) := Finset.mem_range.2 (by omega)
    exact Finset.le_sup' L hmem
  have hB0 : (0 : ℝ) ≤ B := le_trans (hL0 0)
    (Finset.le_sup' L (Finset.mem_range.2 (Nat.succ_pos k₀)))
  have hbound : ∀ j m : ℕ, m ≤ j → L (k₀ + 1 + m) ≤
      (∏ jj ∈ Finset.range (m + 1), (1 + 1 / (((k₀ : ℝ) + 1 + (jj : ℝ)) ^ 2))) * B := by
    intro j
    induction j with
    | zero =>
        intro m hm
        rw [Nat.le_zero.1 hm]
        obtain ⟨i, hi, hLi⟩ := h k₀ (le_refl _)
        have h1 : L (k₀ + 1 + 0) ≤ (1 + 1 / ((k₀ : ℝ) + 1) ^ 2) * B := by
          calc L (k₀ + 1 + 0) ≤ (1 + 1 / ((k₀ : ℝ) + 1) ^ 2) * L i := hLi
            _ ≤ (1 + 1 / ((k₀ : ℝ) + 1) ^ 2) * B :=
                mul_le_mul_of_nonneg_left (hBi i hi) (by positivity)
        have h2 : (∏ jj ∈ Finset.range (0 + 1), (1 + 1 / (((k₀ : ℝ) + 1 + (jj : ℝ)) ^ 2))) =
            (1 + 1 / ((k₀ : ℝ) + 1) ^ 2) := by
          rw [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
          congr 3
          push_cast
          ring
        rw [h2]
        exact h1
    | succ j ih =>
        intro m hm
        rcases (Nat.le_iff_lt_or_eq.1 hm) with hlt | heq
        · exact ih m (by omega)
        · subst heq
          obtain ⟨i', hi', hLi'⟩ := h (k₀ + 1 + j) (by omega)
          have hstep : L (k₀ + 1 + (j + 1)) ≤
              (1 + 1 / (((k₀ : ℝ) + 1 + (((j + 1 : ℕ) : ℝ))) ^ 2)) * L i' := by
            have e : k₀ + 1 + (j + 1) = (k₀ + 1 + j) + 1 := by ring
            rw [e]
            have e2 : (((k₀ + 1 + j : ℕ) : ℝ) + 1) =
                ((k₀ : ℝ) + 1 + (((j + 1 : ℕ) : ℝ))) := by
              push_cast
              ring
            rw [e2] at hLi'
            exact hLi'
          have hcase : i' ≤ k₀ ∨ k₀ + 1 ≤ i' := by omega
          rw [show j + 1 + 1 = (j + 1) + 1 from by omega, Finset.prod_range_succ]
          rcases hcase with hik | hik
          · have hP1 := one_le_prod_escape_factor k₀ (j + 1)
            calc L (k₀ + 1 + (j + 1))
                ≤ (1 + 1 / (((k₀ : ℝ) + 1 + (((j + 1 : ℕ) : ℝ))) ^ 2)) * L i' := hstep
              _ ≤ (1 + 1 / (((k₀ : ℝ) + 1 + (((j + 1 : ℕ) : ℝ))) ^ 2)) *
                    ((∏ jj ∈ Finset.range (j + 1),
                      (1 + 1 / (((k₀ : ℝ) + 1 + (jj : ℝ)) ^ 2))) * B) :=
                  mul_le_mul_of_nonneg_left
                    (le_trans (hBi i' hik) (le_mul_of_one_le_left_nn hB0 hP1))
                    (by positivity)
              _ = ((∏ jj ∈ Finset.range (j + 1),
                      (1 + 1 / (((k₀ : ℝ) + 1 + (jj : ℝ)) ^ 2))) *
                    (1 + 1 / (((k₀ : ℝ) + 1 + (((j + 1 : ℕ) : ℝ))) ^ 2))) * B := by ring
          · obtain ⟨m', hm', rfl⟩ : ∃ m' ≤ j, i' = k₀ + 1 + m' :=
              ⟨i' - (k₀ + 1), by omega, by omega⟩
            have hih := ih m' hm'
            have hPmono := prod_escape_factor_mono k₀ (by omega : m' + 1 ≤ j + 1)
            calc L (k₀ + 1 + (j + 1))
                ≤ (1 + 1 / (((k₀ : ℝ) + 1 + (((j + 1 : ℕ) : ℝ))) ^ 2)) *
                    L (k₀ + 1 + m') := hstep
              _ ≤ (1 + 1 / (((k₀ : ℝ) + 1 + (((j + 1 : ℕ) : ℝ))) ^ 2)) *
                    ((∏ jj ∈ Finset.range (j + 1),
                      (1 + 1 / (((k₀ : ℝ) + 1 + (jj : ℝ)) ^ 2))) * B) :=
                  mul_le_mul_of_nonneg_left
                    (le_trans hih (mul_le_mul_of_nonneg_right hPmono hB0)) (by positivity)
              _ = ((∏ jj ∈ Finset.range (j + 1),
                      (1 + 1 / (((k₀ : ℝ) + 1 + (jj : ℝ)) ^ 2))) *
                    (1 + 1 / (((k₀ : ℝ) + 1 + (((j + 1 : ℕ) : ℝ))) ^ 2))) * B := by ring
  have hbound' : ∀ n ≥ k₀ + 1, L n ≤ 4 * B := by
    intro n hn
    have h1 := hbound (n - (k₀ + 1)) (n - (k₀ + 1)) (le_refl _)
    have e : k₀ + 1 + (n - (k₀ + 1)) = n := by omega
    rw [e] at h1
    have h2 := prod_escape_factor_le_four k₀ (n - (k₀ + 1) + 1)
    have hnn : (0 : ℝ) ≤ ∏ jj ∈ Finset.range (n - (k₀ + 1) + 1),
        (1 + 1 / (((k₀ : ℝ) + 1 + (jj : ℝ)) ^ 2)) := by
      apply Finset.prod_nonneg
      intro jj _
      positivity
    nlinarith [h1, h2, hnn, hB0]
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (hL.eventually_gt_atTop (4 * B))
  have h1 := hn₁ (max n₁ (k₀ + 1)) (le_max_left _ _)
  have h2 := hbound' (max n₁ (k₀ + 1)) (le_max_right _ _)
  linarith

/-! ### The (17) product bound at an escape record -/

/-- `((2^{2^t})^{1/2^t}) = 2`. -/
lemma two_pow_root_self (t : ℕ) :
    (((2 : ℝ) ^ (2 ^ t)) ^ (1 / (2 : ℝ) ^ t)) = 2 := by
  have h1 : ((2 : ℝ) ^ (2 ^ t)) = ((2 : ℝ) ^ (((2 ^ t : ℕ)) : ℝ)) := by
    rw [Real.rpow_natCast]
  rw [h1, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
  have h2 : ((2 ^ t : ℕ) : ℝ) * (1 / (2 : ℝ) ^ t) = 1 := by
    push_cast
    exact mul_one_div_cancel (pow_ne_zero _ (by norm_num))
  rw [h2, Real.rpow_one]

/-- **Product bound at an escape record** (the paper's (17)
`n_{k+1} > M_k·(1+1/k²)^{2^{k+1}}`, restated). -/
lemma prod_le_of_escape_record (hapos : ∀ n, 0 < a n) {k : ℕ} (hk : 1 ≤ k)
    (hrec : ∀ j ≤ k, (1 + 1 / ((k : ℝ) + 1) ^ 2) *
      ((a j : ℝ) ^ (1 / (2 : ℝ) ^ j)) <
        (a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))
    (hO2 : (2 : ℝ) ^ (2 ^ (k + 1)) ≤ (a (k + 1) : ℝ)) :
    (∏ j ∈ Finset.range (k + 1), (a j : ℝ)) ≤
      (((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) *
        ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ (k + 1)) := by
  have hcpos : (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1) ^ 2 := by positivity
  set c : ℝ := (1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹ with hcdef
  have hL2 : (2 : ℝ) ≤ (a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)) := by
    nth_rewrite 1 [← two_pow_root_self (k + 1)]
    exact Real.rpow_le_rpow (by positivity) hO2 (by positivity)
  have hc1 : (1 : ℝ) ≤ c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1))) := by
    have hle : (1 + 1 / ((k : ℝ) + 1) ^ 2) ≤ 2 := by
      have h2 : (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [show (0 : ℝ) < (k : ℝ) + 1 from by positivity]
      nlinarith [h2, show (0 : ℝ) < 1 / ((k : ℝ) + 1) ^ 2 from by positivity]
    have hcge : (1 / 2 : ℝ) ≤ c := by
      rw [hcdef, inv_eq_one_div]
      exact one_div_le_one_div_of_le hcpos hle
    calc (1 : ℝ) = (1 / 2 : ℝ) * 2 := by norm_num
      _ ≤ c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1))) :=
          mul_le_mul hcge hL2 (by norm_num) (by positivity)
  have hbound : ∀ j ≤ k, (a j : ℝ) ≤
      (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ j) := by
    intro j hj
    have hLj : (a j : ℝ) ^ (1 / (2 : ℝ) ^ j) <
        c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1))) := by
      have h := hrec j hj
      have h1 : (a j : ℝ) ^ (1 / (2 : ℝ) ^ j) =
          (1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹ *
            ((1 + 1 / ((k : ℝ) + 1) ^ 2) * ((a j : ℝ) ^ (1 / (2 : ℝ) ^ j))) :=
        (inv_mul_cancel_left₀ hcpos.ne' _).symm
      rw [h1]
      exact mul_lt_mul_of_pos_left h (inv_pos.2 hcpos)
    have h2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (a j : ℝ) ^ (1 / (2 : ℝ) ^ j))
      hLj.le (2 ^ j)
    rwa [rpow_root_two_pow_self j] at h2
  have hprod : (∏ j ∈ Finset.range (k + 1), (a j : ℝ)) ≤
      ∏ j ∈ Finset.range (k + 1),
        (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ j) :=
    Finset.prod_le_prod (fun j _ => by positivity)
      (fun j hj => hbound j (Finset.mem_range.1 hj |> Nat.lt_succ_iff.1))
  have hsum : ∑ j ∈ Finset.range (k + 1), (2 : ℕ) ^ j = 2 ^ (k + 1) - 1 :=
    sum_range_two_pow k
  have hexp : (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ (k + 1) - 1) ≤
      (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ (k + 1)) := by
    have hexp1 : (2 : ℕ) ^ (k + 1) - 1 ≤ (2 : ℕ) ^ (k + 1) := by
      have h1 : (1 : ℕ) ≤ (2 : ℕ) ^ (k + 1) := Nat.one_le_two_pow
      omega
    exact pow_le_pow_right₀ hc1 hexp1
  calc (∏ j ∈ Finset.range (k + 1), (a j : ℝ))
      ≤ ∏ j ∈ Finset.range (k + 1),
          (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ j) := hprod
    _ = (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^
          (∑ j ∈ Finset.range (k + 1), 2 ^ j) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ (k + 1)) := by
        rw [hsum]
        exact hexp

/-! ### The (11) tower from the power cap -/

/-- **The paper's (11):** if `a_{j+1} ≤ P_j^l` for all `j ≥ J₀` (the power
cap (10)), then `P_k ≤ P_{J₀}^{(l+1)^{k-J₀}}` for all `k ≥ J₀` — singly
exponential log-growth (NOT a tower). -/
lemma cap_pow_tower (hapos : ∀ n, 0 < a n) {l : ℕ} {J₀ : ℕ}
    (hcap : ∀ j ≥ J₀, (a (j + 1) : ℝ) ≤ (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ l)
    (k : ℕ) (hk : J₀ ≤ k) :
    (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) ≤
      (∏ i ∈ Finset.range (J₀ + 1), (a i : ℝ)) ^ ((l + 1) ^ (k - J₀)) := by
  induction k, hk using Nat.le_induction with
  | base =>
      rw [Nat.sub_self, pow_zero, pow_one]
  | succ k hk ih =>
      have hPpos : (0 : ℝ) < ∏ i ∈ Finset.range (k + 1), (a i : ℝ) :=
        Finset.prod_pos (fun i _ => by exact_mod_cast hapos i)
      have hcapk := hcap k hk
      have hsplit : (∏ i ∈ Finset.range (k + 1 + 1), (a i : ℝ)) =
          (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) * (a (k + 1) : ℝ) :=
        Finset.prod_range_succ (fun i => (a i : ℝ)) (k + 1)
      have hstep : (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) * (a (k + 1) : ℝ) ≤
          (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) ^ (l + 1) := by
        calc (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) * (a (k + 1) : ℝ)
            ≤ (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) *
              (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) ^ l :=
                mul_le_mul_of_nonneg_left hcapk hPpos.le
          _ = (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) ^ (l + 1) := by
                rw [pow_succ']
      calc (∏ i ∈ Finset.range (k + 1 + 1), (a i : ℝ))
          = (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) * (a (k + 1) : ℝ) := hsplit
        _ ≤ (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) ^ (l + 1) := hstep
        _ ≤ ((∏ i ∈ Finset.range (J₀ + 1), (a i : ℝ)) ^ ((l + 1) ^ (k - J₀))) ^ (l + 1) :=
              pow_le_pow_left₀ (by positivity) ih (l + 1)
        _ = (∏ i ∈ Finset.range (J₀ + 1), (a i : ℝ)) ^
              ((l + 1) ^ (k - J₀) * (l + 1)) := by rw [← pow_mul]
        _ = (∏ i ∈ Finset.range (J₀ + 1), (a i : ℝ)) ^ ((l + 1) ^ (k + 1 - J₀)) := by
              rw [show (k + 1 - J₀) = (k - J₀) + 1 from by omega, pow_succ]

/-! ### Helpers for the case-(12) assembly -/

/-- `n⁴ ≤ 2^n` for `n ≥ 16` (self-contained induction). -/
lemma two_pow_ge_four (n : ℕ) (hn : 16 ≤ n) : n ^ 4 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hk16 : 16 ≤ k := hk
      have hstep : (k + 1) ^ 4 ≤ 2 * k ^ 4 := by
        have e : (k + 1) ^ 4 = k ^ 4 + 4 * k ^ 3 + 6 * k ^ 2 + 4 * k + 1 := by ring
        rw [e]
        have h1 : 4 * k ^ 3 + 6 * k ^ 2 + 4 * k + 1 ≤ k ^ 4 := by
          have h2 : k ^ 4 = k * k ^ 3 := by ring
          rw [h2]
          nlinarith [hk16, pow_pos (by omega : 0 < k) 2, pow_pos (by omega : 0 < k) 3]
        omega
      calc (k + 1) ^ 4 ≤ 2 * k ^ 4 := hstep
        _ ≤ 2 * 2 ^ k := by gcongr
        _ = 2 ^ (k + 1) := by ring

/-- `Nat.log b (x^n) ≤ n·(Nat.log b x + 1)` for `b ≥ 2`, `x ≥ 1`. -/
lemma nat_log_pow_le {b x : ℕ} (hb : 1 < b) (hx : 1 ≤ x) (n : ℕ) :
    Nat.log b (x ^ n) ≤ n * (Nat.log b x + 1) := by
  have h1 : x < b ^ (Nat.log b x + 1) := Nat.lt_pow_succ_log_self hb x
  have h2 : x ^ n ≤ (b ^ (Nat.log b x + 1)) ^ n := Nat.pow_le_pow_left h1.le n
  have h3 : (b ^ (Nat.log b x + 1)) ^ n = b ^ ((Nat.log b x + 1) * n) := by
    rw [← pow_mul]
  have h4 : x ^ n ≤ b ^ ((Nat.log b x + 1) * n) := by rwa [h3] at h2
  have h5 : x ^ n ≠ 0 := pow_ne_zero n (by omega)
  have h6 : x ^ n < b ^ ((Nat.log b x + 1) * n + 1) :=
    lt_of_le_of_lt h4 (pow_lt_pow_right₀ hb (Nat.lt_succ_self _))
  have h7 : Nat.log b (x ^ n) < (Nat.log b x + 1) * n + 1 := by
    by_contra hge
    push Not at hge
    have h8 := (Nat.le_log_iff_pow_le hb h5).1 hge
    exact not_lt_of_ge h8 h6
  have h9 : (Nat.log b x + 1) * n = n * (Nat.log b x + 1) := by ring
  omega

/-- `Nat.log b (x·y) ≤ Nat.log b x + Nat.log b y + 1` for `b ≥ 2`, `x, y ≥ 1`. -/
lemma nat_log_mul_le {b x y : ℕ} (hb : 1 < b) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Nat.log b (x * y) ≤ Nat.log b x + Nat.log b y + 1 := by
  have h1 : x < b ^ (Nat.log b x + 1) := Nat.lt_pow_succ_log_self hb x
  have h2 : y < b ^ (Nat.log b y + 1) := Nat.lt_pow_succ_log_self hb y
  have h3 : x * y < b ^ (Nat.log b x + 1) * b ^ (Nat.log b y + 1) := by
    calc x * y < b ^ (Nat.log b x + 1) * y := by
          have hX : (0 : ℕ) < b ^ (Nat.log b x + 1) := by positivity
          exact mul_lt_mul_of_pos_right h1 (by omega)
      _ ≤ b ^ (Nat.log b x + 1) * b ^ (Nat.log b y + 1) :=
          Nat.mul_le_mul (le_refl _) h2.le
  have h4 : b ^ (Nat.log b x + 1) * b ^ (Nat.log b y + 1) =
      b ^ (Nat.log b x + Nat.log b y + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have h5 : x * y < b ^ (Nat.log b x + Nat.log b y + 2) := by rwa [h4] at h3
  have h6 : x * y ≠ 0 := by positivity
  have h7 : Nat.log b (x * y) < Nat.log b x + Nat.log b y + 2 := by
    by_contra hge
    push Not at hge
    have h8 := (Nat.le_log_iff_pow_le hb h6).1 hge
    exact not_lt_of_ge h8 h5
  omega

/-- `(1 + 1/(k+1)²)^{(k+1)²} ≥ 2`. -/
lemma one_add_inv_sq_pow_ge_two (k : ℕ) :
    (2 : ℝ) ≤ (1 + 1 / (((k : ℝ) + 1) ^ 2)) ^ ((k + 1) ^ 2) := by
  have h2 := one_add_mul_le_pow
    (by linarith [show (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) ^ 2 from by positivity] :
      (-2 : ℝ) ≤ 1 / ((k : ℝ) + 1) ^ 2) ((k + 1) ^ 2)
  have h3 : (((k + 1) ^ 2 : ℕ) : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) = 1 := by
    have h4 : (((k + 1) ^ 2 : ℕ) : ℝ) = ((k : ℝ) + 1) ^ 2 := by
      push_cast
      ring
    rw [h4]
    field_simp [(by positivity : ((k : ℝ) + 1) ^ 2 ≠ 0)]
  calc (2 : ℝ) = 1 + 1 := by norm_num
    _ = 1 + (((k + 1) ^ 2 : ℕ) : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) := by rw [h3]
    _ ≤ (1 + 1 / ((k : ℝ) + 1) ^ 2) ^ ((k + 1) ^ 2) := h2

/-- **The escape lower bound:** `(1+1/(k+1)²)^{2^{k+1}} ≥ 2^{2^k/(k+1)²}`. -/
lemma escape_factor_pow_ge (k : ℕ) :
    (2 : ℝ) ^ (2 ^ k / (k + 1) ^ 2) ≤
      (1 + 1 / ((k : ℝ) + 1) ^ 2) ^ (2 ^ (k + 1)) := by
  have hbase := one_add_inv_sq_pow_ge_two k
  have hge : (2 : ℝ) ^ (2 ^ k / (k + 1) ^ 2) ≤
      ((1 + 1 / ((k : ℝ) + 1) ^ 2) ^ ((k + 1) ^ 2)) ^ (2 ^ k / (k + 1) ^ 2) :=
    pow_le_pow_left₀ (by norm_num) hbase _
  have hmerge : ((1 + 1 / ((k : ℝ) + 1) ^ 2) ^ ((k + 1) ^ 2)) ^ (2 ^ k / (k + 1) ^ 2) =
      (1 + 1 / ((k : ℝ) + 1) ^ 2) ^ ((k + 1) ^ 2 * (2 ^ k / (k + 1) ^ 2)) := by
    rw [← pow_mul]
  have hdiv : (k + 1) ^ 2 * (2 ^ k / (k + 1) ^ 2) ≤ 2 ^ (k + 1) := by
    have h := Nat.div_mul_le_self (2 ^ k) ((k + 1) ^ 2)
    rw [Nat.mul_comm] at h
    exact h.trans (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Nat.le_succ k))
  have hbase1 : (1 : ℝ) ≤ 1 + 1 / ((k : ℝ) + 1) ^ 2 := by
    nlinarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) ^ 2 from by positivity]
  calc (2 : ℝ) ^ (2 ^ k / (k + 1) ^ 2)
      ≤ ((1 + 1 / ((k : ℝ) + 1) ^ 2) ^ ((k + 1) ^ 2)) ^ (2 ^ k / (k + 1) ^ 2) := hge
    _ = (1 + 1 / ((k : ℝ) + 1) ^ 2) ^ ((k + 1) ^ 2 * (2 ^ k / (k + 1) ^ 2)) := hmerge
    _ ≤ (1 + 1 / ((k : ℝ) + 1) ^ 2) ^ (2 ^ (k + 1)) :=
        pow_le_pow_right₀ hbase1 hdiv

/-- `Nat.log 2` is monotone. -/
lemma nat_log_mono {x y : ℕ} (h : x ≤ y) : Nat.log 2 x ≤ Nat.log 2 y := by
  rcases eq_or_ne y 0 with rfl | hy
  · have hx : x = 0 := by omega
    rw [hx, Nat.log_zero_right]
  · by_contra hge
    push Not at hge
    have hx0 : x ≠ 0 := by
      intro hx0
      subst hx0
      rw [Nat.log_zero_right] at hge
      omega
    have h1 := (Nat.le_log_iff_pow_le (show (1 : ℕ) < 2 by norm_num) hx0).1
      (by omega : Nat.log 2 y + 1 ≤ Nat.log 2 x)
    have h3 : y < 2 ^ (Nat.log 2 y + 1) := Nat.lt_pow_succ_log_self (by norm_num) y
    omega

/-- **The loglog bound under the tower.** -/
lemma istar_bound (hapos : ∀ n, 0 < a n) {l J₀ k : ℕ} (hkJ : J₀ ≤ k)
    (hcapN : a (k + 1) ≤ (∏ i ∈ Finset.range (k + 1), a i) ^ l)
    (htowN : (∏ i ∈ Finset.range (k + 1), a i) ≤
      (∏ i ∈ Finset.range (J₀ + 1), a i) ^ ((l + 1) ^ (k - J₀))) :
    (Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4 ≤
      (2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) : ℝ) *
        (((l + 1 : ℕ) : ℝ) ^ k) + (2 * l + 4 : ℝ) := by
  have hP1 : 1 ≤ ∏ i ∈ Finset.range (J₀ + 1), a i := Finset.prod_pos (fun i _ => hapos i)
  have hPk : 1 ≤ ∏ i ∈ Finset.range (k + 1), a i := Finset.prod_pos (fun i _ => hapos i)
  have h1 : Nat.log 2 (a (k + 1)) ≤ Nat.log 2 ((∏ i ∈ Finset.range (k + 1), a i) ^ l) :=
    nat_log_mono hcapN
  have h2 : Nat.log 2 ((∏ i ∈ Finset.range (k + 1), a i) ^ l) ≤
      l * (Nat.log 2 (∏ i ∈ Finset.range (k + 1), a i) + 1) :=
    nat_log_pow_le (by norm_num) hPk l
  have h3 : Nat.log 2 (∏ i ∈ Finset.range (k + 1), a i) ≤
      Nat.log 2 ((∏ i ∈ Finset.range (J₀ + 1), a i) ^ ((l + 1) ^ (k - J₀))) :=
    nat_log_mono htowN
  have h4 : Nat.log 2 ((∏ i ∈ Finset.range (J₀ + 1), a i) ^ ((l + 1) ^ (k - J₀))) ≤
      ((l + 1) ^ (k - J₀)) * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) :=
    nat_log_pow_le (by norm_num) hP1 _
  have h5 : (l + 1) ^ (k - J₀) ≤ (l + 1) ^ k :=
    pow_le_pow_right₀ (by omega : 1 ≤ l + 1) (Nat.sub_le k J₀)
  have h7 : Nat.log 2 (∏ i ∈ Finset.range (k + 1), a i) ≤
      (l + 1) ^ k * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) :=
    le_trans h3 (le_trans h4 (Nat.mul_le_mul h5 (le_refl _)))
  have h8' : l * Nat.log 2 (∏ i ∈ Finset.range (k + 1), a i) ≤
      l * ((l + 1) ^ k * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1)) :=
    Nat.mul_le_mul (le_refl l) h7
  have h6 : Nat.log 2 (a (k + 1)) ≤
      l * ((l + 1) ^ k * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1)) + l := by
    have h9 : l * (Nat.log 2 (∏ i ∈ Finset.range (k + 1), a i) + 1) =
        l * Nat.log 2 (∏ i ∈ Finset.range (k + 1), a i) + l := by ring
    rw [h9] at h2
    omega
  have h8 : Nat.log 2 (2 * Nat.log 2 (a (k + 1))) ≤ 2 * Nat.log 2 (a (k + 1)) :=
    Nat.log_le_self 2 _
  have h9 : Nat.log 2 (2 * Nat.log 2 (a (k + 1))) + 4 ≤
      2 * l * ((l + 1) ^ k * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1)) +
        2 * l + 4 := by
    have h10 : 2 * Nat.log 2 (a (k + 1)) ≤
        2 * (l * ((l + 1) ^ k * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1)) + l) :=
      Nat.mul_le_mul (le_refl 2) h6
    calc Nat.log 2 (2 * Nat.log 2 (a (k + 1))) + 4
        ≤ 2 * Nat.log 2 (a (k + 1)) + 4 := by omega
      _ ≤ 2 * (l * ((l + 1) ^ k * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1)) + l) + 4 := by
          omega
      _ = 2 * l * ((l + 1) ^ k * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1)) +
            2 * l + 4 := by ring
  have h10 : ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) + 4 : ℕ) : ℝ) ≤
      ((2 * l * ((l + 1) ^ k * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1)) +
        2 * l + 4 : ℕ) : ℝ) := by
    exact_mod_cast h9
  calc ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4)
      = ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) + 4 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 * l * ((l + 1) ^ k * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1)) +
          2 * l + 4 : ℕ) : ℝ) := h10
    _ = (2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) : ℝ) *
          (((l + 1 : ℕ) : ℝ) ^ k) + (2 * l + 4 : ℝ) := by push_cast; ring

theorem irrational_of_monotone_growth_case10 (hg : OneSidedGrowth a)
    (hmono : Monotone a) {l : ℕ}
    (hcap : ∀ᶠ j in atTop, (a (j + 1) : ℝ) ≤ (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ l) :
    Irrational (∑' n, 1 / (a n : ℝ)) := by
  have hapos : ∀ n, 0 < a n := hg.1
  have hsum : Summable (fun n => 1 / (a n : ℝ)) := summable_one_div_of_oneSidedGrowth hg
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 hcap
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_ge_of_oneSidedGrowth hg)
  rintro ⟨r, hr⟩
  have hq : (1 : ℝ) ≤ (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hqpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hge : ∀ i ≥ N₀ + 1, (2 : ℝ) ^ (2 ^ i) ≤ (a i : ℝ) := by
    intro i hi
    have h1 := hN₀ i (by omega)
    have hcast : ((a₂₂ i : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ i) := by
      unfold a₂₂
      push_cast
      rfl
    rwa [hcast] at h1
  -- the escape record, chosen beyond all thresholds
  set D : ℕ := r.den * (2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) +
    (2 * l + 4)) with hDdef
  set K₀ : ℕ := max (max (max J₀ (N₀ + 1)) 16)
    (max (2 * (Nat.log 2 (2 * (l + 1)) + 1)) (Nat.log 2 D + 1)) with hK₀def
  have hL : Tendsto (fun n => (a n : ℝ) ^ (1 / (2 : ℝ) ^ n)) atTop atTop := hg.2
  have hL0 : ∀ n, 0 ≤ (a n : ℝ) ^ (1 / (2 : ℝ) ^ n) := fun n => by positivity
  obtain ⟨k, hk, hrec⟩ := exists_escape_record hL hL0 K₀
  have hkJ : J₀ ≤ k := by
    have h1 : J₀ ≤ K₀ :=
      le_trans (le_max_left J₀ (N₀ + 1))
        (le_trans (le_max_left (max J₀ (N₀ + 1)) 16) (le_max_left _ _))
    exact le_trans h1 hk
  have hkN : N₀ + 1 ≤ k := by
    have h1 : N₀ + 1 ≤ K₀ :=
      le_trans (le_max_right J₀ (N₀ + 1))
        (le_trans (le_max_left (max J₀ (N₀ + 1)) 16) (le_max_left _ _))
    exact le_trans h1 hk
  have hk16 : 16 ≤ k := le_trans (le_trans (le_max_right (max J₀ (N₀ + 1)) 16) (le_max_left _ _)) hk
  have hk1 : 1 ≤ k := by omega
  have hO2 : (2 : ℝ) ^ (2 ^ (k + 1)) ≤ (a (k + 1) : ℝ) := hge (k + 1) (by omega)
  -- (15): integrality
  have hm := one_le_prod_tail hapos hsum hr k
  -- (13): the loglog tail bound
  have hT := tail_le_loglog_of_monotone hapos hsum hmono hge k hkN
  -- (16): the loglog cap
  have h16 : (a (k + 1) : ℝ) ≤ (r.den : ℝ) * (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) *
      ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) := by
    have hPpos : (0 : ℝ) < ∏ i ∈ Finset.range (k + 1), (a i : ℝ) :=
      Finset.prod_pos (fun i _ => by exact_mod_cast hapos i)
    have hApos : (0 : ℝ) < (a (k + 1) : ℝ) := by exact_mod_cast hapos _
    have h1 : (1 : ℝ) ≤ (r.den : ℝ) * (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) *
        (((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) / (a (k + 1) : ℝ)) :=
      le_trans hm (mul_le_mul_of_nonneg_left hT (le_of_lt (mul_pos hqpos hPpos)))
    have h3 := mul_le_mul_of_nonneg_left h1 hApos.le
    rw [mul_one] at h3
    have e : (a (k + 1) : ℝ) * ((r.den : ℝ) * (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) *
        (((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) / (a (k + 1) : ℝ))) =
        (r.den : ℝ) * (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) *
          ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) := by
      field_simp [hApos.ne']
    rw [e] at h3
    exact h3
  -- (17): the product bound at the escape record
  have h17 := prod_le_of_escape_record hapos hk1 hrec hO2
  have h17' : (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) ≤
      ((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1)) * (a (k + 1) : ℝ) := by
    have e1 : (((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) *
        ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ (k + 1)) =
        ((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1)) * (a (k + 1) : ℝ) := by
      rw [mul_pow, rpow_root_two_pow_self (k + 1)]
    rwa [e1] at h17
  -- combine (16) and (17): 1 ≤ q·(i*+4)·c^{2^{k+1}}
  have hcomb : (1 : ℝ) ≤ (r.den : ℝ) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) *
      ((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1)) := by
    have hApos : (0 : ℝ) < (a (k + 1) : ℝ) := by exact_mod_cast hapos _
    have h5 : (r.den : ℝ) * ((∏ i ∈ Finset.range (k + 1), (a i : ℝ)) *
        ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4)) ≤
        (r.den : ℝ) * ((((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1)) * (a (k + 1) : ℝ)) *
          ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h17'
          (show (0 : ℝ) ≤ (↑(Nat.log 2 (2 * Nat.log 2 (a (k + 1)))) + 4) from
            add_nonneg (Nat.cast_nonneg _) (by norm_num))) hqpos.le
    have h1 : (a (k + 1) : ℝ) ≤ (r.den : ℝ) * ((((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1)) *
        (a (k + 1) : ℝ)) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4)) := by
      have h6 : (a (k + 1) : ℝ) ≤
          (r.den : ℝ) * ((∏ i ∈ Finset.range (k + 1), (a i : ℝ)) *
            ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4)) := by
        have h7 : (a (k + 1) : ℝ) ≤
            (r.den : ℝ) * (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) *
              ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) := h16
        rwa [show (r.den : ℝ) * (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) *
          ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) =
          (r.den : ℝ) * ((∏ i ∈ Finset.range (k + 1), (a i : ℝ)) *
            ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4)) from by ring] at h7
      have h8 : (a (k + 1) : ℝ) ≤
          (r.den : ℝ) * ((((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1)) * (a (k + 1) : ℝ)) *
            ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4)) :=
        le_trans h6 h5
      exact h8
    have h2 : (1 : ℝ) * (a (k + 1) : ℝ) ≤
        ((r.den : ℝ) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) *
          ((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1))) * (a (k + 1) : ℝ) := by
      rw [one_mul]
      calc (a (k + 1) : ℝ)
          ≤ (r.den : ℝ) * (((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1)) *
            (a (k + 1) : ℝ) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4)) := h1
        _ = ((r.den : ℝ) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) *
              ((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1))) * (a (k + 1) : ℝ) := by ring
    exact le_of_mul_le_mul_right h2 hApos
  -- the escape lower bound: 2^{2^k/(k+1)²} ≤ q·(i*+4)
  have hlarge := escape_factor_pow_ge k
  have hmain : (2 : ℝ) ^ (2 ^ k / (k + 1) ^ 2) ≤
      (r.den : ℝ) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) := by
    have hce : (0 : ℝ) < ((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1)) := by positivity
    have h3 : ((r.den : ℝ) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) *
        ((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1))) *
        (((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1)))⁻¹ =
        (r.den : ℝ) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) := by
      rw [mul_assoc, mul_inv_cancel₀ hce.ne', mul_one]
    have h4 := mul_le_mul_of_nonneg_right hcomb (inv_nonneg.2 hce.le)
    rw [h3, one_mul] at h4
    have h6 : (((1 + 1 / ((k : ℝ) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 1)))⁻¹ =
        (1 + 1 / ((k : ℝ) + 1) ^ 2) ^ (2 ^ (k + 1)) := by
      rw [← inv_pow, inv_inv]
    rw [h6] at h4
    exact le_trans hlarge h4
  -- the i*+4 upper bound from the tower
  have hcapN : a (k + 1) ≤ (∏ i ∈ Finset.range (k + 1), a i) ^ l := by
    have h1 := hJ₀ k hkJ
    have h2 : ((∏ i ∈ Finset.range (k + 1), a i : ℕ) : ℝ) ^ l =
        (∏ i ∈ Finset.range (k + 1), (a i : ℝ)) ^ l := by push_cast; rfl
    rw [← h2] at h1
    have h3 : (((∏ i ∈ Finset.range (k + 1), a i) ^ l : ℕ) : ℝ) =
        ((∏ i ∈ Finset.range (k + 1), a i : ℕ) : ℝ) ^ l := by push_cast; rfl
    rw [← h3] at h1
    exact_mod_cast h1
  have htowN : (∏ i ∈ Finset.range (k + 1), a i) ≤
      (∏ i ∈ Finset.range (J₀ + 1), a i) ^ ((l + 1) ^ (k - J₀)) := by
    have h1 := cap_pow_tower hapos hJ₀ k hkJ
    have h2 : ((∏ i ∈ Finset.range (J₀ + 1), a i : ℕ) : ℝ) ^ ((l + 1) ^ (k - J₀)) =
        (∏ i ∈ Finset.range (J₀ + 1), (a i : ℝ)) ^ ((l + 1) ^ (k - J₀)) := by
      push_cast
      rfl
    rw [← h2] at h1
    have h3 : (((∏ i ∈ Finset.range (J₀ + 1), a i) ^ ((l + 1) ^ (k - J₀)) : ℕ) : ℝ) =
        ((∏ i ∈ Finset.range (J₀ + 1), a i : ℕ) : ℝ) ^ ((l + 1) ^ (k - J₀)) := by
      push_cast
      rfl
    rw [← h3] at h1
    exact_mod_cast h1
  have hi := istar_bound hapos hkJ hcapN htowN
  -- the final fight
  have hupper : (r.den : ℝ) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) <
      (2 : ℝ) ^ (k ^ 2 / 2) := by
    have hC : ((2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) : ℝ) *
        (((l + 1 : ℕ) : ℝ) ^ k) + (2 * l + 4 : ℝ)) ≤
        ((2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) + (2 * l + 4) : ℝ)) *
          (((l + 1 : ℕ) : ℝ) ^ k) := by
      have h1 : (2 * l + 4 : ℝ) ≤ (2 * l + 4 : ℝ) * (((l + 1 : ℕ) : ℝ) ^ k) :=
        le_mul_of_one_le_right_nn (by positivity)
          (one_le_pow₀ (by exact_mod_cast (by omega : (1 : ℕ) ≤ l + 1) : (1 : ℝ) ≤ ((l + 1 : ℕ) : ℝ)))
      have h2 : ((2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) : ℝ) +
          (2 * l + 4 : ℝ)) =
          ((2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) + (2 * l + 4) : ℝ)) := by
        push_cast
        ring
      calc (2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) : ℝ) *
          (((l + 1 : ℕ) : ℝ) ^ k) + (2 * l + 4 : ℝ)
          ≤ (2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) : ℝ) *
            (((l + 1 : ℕ) : ℝ) ^ k) + (2 * l + 4 : ℝ) * (((l + 1 : ℕ) : ℝ) ^ k) := by
            linarith [h1]
        _ = ((2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) : ℝ) +
              (2 * l + 4 : ℝ)) * (((l + 1 : ℕ) : ℝ) ^ k) := by ring
        _ = ((2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) + (2 * l + 4) : ℝ)) *
              (((l + 1 : ℕ) : ℝ) ^ k) := by rw [h2]
    have hD1 : ((r.den : ℝ) * ((2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) +
        (2 * l + 4) : ℝ))) < (2 : ℝ) ^ k := by
      have h3 : D < 2 ^ (Nat.log 2 D + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
      have h4 : 2 ^ (Nat.log 2 D + 1) ≤ 2 ^ k :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by
          have h5 : Nat.log 2 D + 1 ≤ K₀ := le_trans (le_max_right _ _) (le_max_right _ _)
          omega)
      have h6 : r.den * (2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) +
        (2 * l + 4)) < 2 ^ k := by
        rw [hDdef] at h3
        exact h3.trans_le h4
      have h7 : ((r.den * (2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) +
          (2 * l + 4)) : ℕ) : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h6
      push_cast at h7
      exact h7
    have h8 : (2 : ℝ) ^ k * (((l + 1 : ℕ) : ℝ) ^ k) = ((2 * (l + 1) : ℕ) : ℝ) ^ k := by
      have h9 : ((2 * (l + 1) : ℕ) : ℝ) = (2 : ℝ) * (((l + 1 : ℕ) : ℝ)) := by
        push_cast
        ring
      rw [h9, mul_pow]
    have h9 : ((2 * (l + 1) : ℕ) : ℝ) ^ k ≤
        (2 : ℝ) ^ (k * (Nat.log 2 (2 * (l + 1)) + 1)) := by
      have h10 : 2 * (l + 1) ≤ 2 ^ (Nat.log 2 (2 * (l + 1)) + 1) :=
        Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) _)
      have h11 : ((2 * (l + 1) : ℕ) : ℝ) ^ k ≤
          ((2 ^ (Nat.log 2 (2 * (l + 1)) + 1) : ℕ) : ℝ) ^ k := by
        have h12 : (2 * (l + 1)) ^ k ≤ (2 ^ (Nat.log 2 (2 * (l + 1)) + 1)) ^ k :=
          pow_le_pow_left₀ (by omega) h10 k
        exact_mod_cast h12
      have h13 : ((2 ^ (Nat.log 2 (2 * (l + 1)) + 1) : ℕ) : ℝ) ^ k =
          (2 : ℝ) ^ (k * (Nat.log 2 (2 * (l + 1)) + 1)) := by
        push_cast
        rw [← pow_mul, mul_comm]
      rwa [h13] at h11
    have h14 : k * (Nat.log 2 (2 * (l + 1)) + 1) ≤ k ^ 2 / 2 := by
      have h15 : 2 * (Nat.log 2 (2 * (l + 1)) + 1) ≤ k := by
        have h16 : 2 * (Nat.log 2 (2 * (l + 1)) + 1) ≤ K₀ :=
          le_trans (le_max_left _ _) (le_max_right _ _)
        omega
      have h17 : k * ((Nat.log 2 (2 * (l + 1)) + 1) * 2) ≤ k * k :=
        Nat.mul_le_mul (le_refl k) (by omega)
      have h18 : k * (Nat.log 2 (2 * (l + 1)) + 1) * 2 ≤ k * k := by
        calc k * (Nat.log 2 (2 * (l + 1)) + 1) * 2
            = k * ((Nat.log 2 (2 * (l + 1)) + 1) * 2) := by ring
          _ ≤ k * k := h17
      exact (Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 2)).2 (by
        calc k * (Nat.log 2 (2 * (l + 1)) + 1) * 2 ≤ k * k := h18
          _ = k ^ 2 := by ring)
    calc (r.den : ℝ) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4)
        ≤ (r.den : ℝ) * ((2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) : ℝ) *
            (((l + 1 : ℕ) : ℝ) ^ k) + (2 * l + 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hi hqpos.le
      _ ≤ ((r.den : ℝ) * ((2 * l * (Nat.log 2 (∏ i ∈ Finset.range (J₀ + 1), a i) + 1) +
          (2 * l + 4) : ℝ))) * (((l + 1 : ℕ) : ℝ) ^ k) := by
        have h10 := mul_le_mul_of_nonneg_left hC hqpos.le
        rwa [← mul_assoc] at h10
      _ < (2 : ℝ) ^ k * (((l + 1 : ℕ) : ℝ) ^ k) :=
          mul_lt_mul_of_pos_right hD1 (pow_pos (by positivity : (0 : ℝ) < ((l + 1 : ℕ) : ℝ)) k)
      _ = ((2 * (l + 1) : ℕ) : ℝ) ^ k := h8
      _ ≤ (2 : ℝ) ^ (k * (Nat.log 2 (2 * (l + 1)) + 1)) := h9
      _ ≤ (2 : ℝ) ^ (k ^ 2 / 2) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h14
  have hlower : (2 : ℝ) ^ (k ^ 2 / 2) ≤ (2 : ℝ) ^ (2 ^ k / (k + 1) ^ 2) := by
    have h1 : k ^ 2 / 2 ≤ k ^ 4 / (k + 1) ^ 2 := by
      have h2 : (k ^ 2 / 2) * (k + 1) ^ 2 ≤ k ^ 4 := by
        have h3 : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by
          nlinarith [hk16, pow_pos (by omega : 0 < k) 2]
        calc (k ^ 2 / 2) * (k + 1) ^ 2
            ≤ (k ^ 2 / 2) * (2 * k ^ 2) := Nat.mul_le_mul (le_refl _) h3
          _ = (k ^ 2 / 2 * 2) * k ^ 2 := by ring
          _ ≤ k ^ 2 * k ^ 2 := by
              have hd : k ^ 2 / 2 * 2 ≤ k ^ 2 := Nat.div_mul_le_self (k ^ 2) 2
              exact Nat.mul_le_mul hd (le_refl _)
          _ = k ^ 4 := by ring
      exact (Nat.le_div_iff_mul_le (pow_pos (by omega : 0 < k + 1) 2)).2 h2
    have h4 : k ^ 4 / (k + 1) ^ 2 ≤ 2 ^ k / (k + 1) ^ 2 :=
      Nat.div_le_div_right (two_pow_ge_four k hk16)
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_trans h1 h4)
  have hfinal : (2 : ℝ) ^ (k ^ 2 / 2) ≤ (r.den : ℝ) * ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) :=
    le_trans hlower hmain
  exact absurd hfinal (not_le_of_gt hupper)

/-- **Case (9) at lim level under `Monotone a`, power-of-product spike:**
if `a` is monotone with `a_n^{1/2^n} → ∞` and the spike
`(∏_{i≤j} a_i)³ < a_{j+1}` happens frequently, then `∑' 1/a` is
irrational. (The loglog cap `a_{j+1} ≤ q·P_j·(i*+4)` bootstraps to
`a_{j+1} ≤ 64·(q·P_j)²`; the cubic spike then forces `P_j < 64·q²`,
contradicting `P_j ≥ 2^{2^j}`.) -/
theorem irrational_of_monotone_growth_and_spike_pow (hg : OneSidedGrowth a)
    (hmono : Monotone a)
    (hspike : ∃ᶠ j in atTop, (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 3 <
      (a (j + 1) : ℝ)) :
    Irrational (∑' n, 1 / (a n : ℝ)) := by
  have hapos : ∀ n, 0 < a n := hg.1
  have hsum : Summable (fun n => 1 / (a n : ℝ)) := summable_one_div_of_oneSidedGrowth hg
  rintro ⟨r, hr⟩
  set q : ℝ := (r.den : ℝ) with hqdef
  have hq : (1 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast r.den_pos
  have hqpos : (0 : ℝ) < q := by linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_ge_of_oneSidedGrowth hg)
  obtain ⟨j, hj, hsp⟩ := (Filter.frequently_atTop.1 hspike)
    (max (N₀ + 1) (Nat.ceil (64 * q ^ 2 + 1)))
  have hjN : N₀ ≤ j := le_trans (le_trans (Nat.le_succ N₀) (le_max_left _ _)) hj
  have hT := tail_le_loglog_of_monotone hapos hsum hmono (M := N₀)
    (fun i hi => by
      have h1 := hN₀ i (by omega)
      have hcast : ((a₂₂ i : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ i) := by
        unfold a₂₂
        push_cast
        rfl
      rwa [hcast] at h1) j (by omega)
  have hm := one_le_prod_tail hapos hsum hr j
  have hPpos : (0 : ℝ) < ∏ i ∈ Finset.range (j + 1), (a i : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hapos i)
  have hApos : (0 : ℝ) < (a (j + 1) : ℝ) := by exact_mod_cast hapos _
  have hcap : (a (j + 1) : ℝ) ≤ q * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) *
      ((Nat.log 2 (2 * Nat.log 2 (a (j + 1))) : ℝ) + 4) := by
    have h1 : (1 : ℝ) ≤ q * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) *
        (((Nat.log 2 (2 * Nat.log 2 (a (j + 1))) : ℝ) + 4) / (a (j + 1) : ℝ)) :=
      le_trans hm (mul_le_mul_of_nonneg_left hT (le_of_lt (mul_pos hqpos hPpos)))
    have h3 := mul_le_mul_of_nonneg_left h1 hApos.le
    rw [mul_one] at h3
    have e : (a (j + 1) : ℝ) * (q * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) *
        (((Nat.log 2 (2 * Nat.log 2 (a (j + 1))) : ℝ) + 4) / (a (j + 1) : ℝ))) =
        q * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) *
          ((Nat.log 2 (2 * Nat.log 2 (a (j + 1))) : ℝ) + 4) := by
      field_simp [hApos.ne']
    rw [e] at h3
    exact h3
  have hboot : (a (j + 1) : ℝ) ≤ 64 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 := by
    have hA0 : (0 : ℝ) ≤ (a (j + 1) : ℝ) := by positivity
    have hA1 : (1 : ℝ) ≤ (a (j + 1) : ℝ) := by exact_mod_cast hapos _
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (a (j + 1) : ℝ) := by
      rw [Real.le_sqrt (show (0 : ℝ) ≤ (1 : ℝ) by norm_num) hA0, one_pow]
      exact hA1
    have hi : ((Nat.log 2 (2 * Nat.log 2 (a (j + 1))) : ℝ) + 4) ≤
        8 * Real.sqrt (a (j + 1) : ℝ) := by
      have h1 : (Nat.log 2 (2 * Nat.log 2 (a (j + 1))) : ℝ) ≤
          2 * (Nat.log 2 (a (j + 1)) : ℝ) := by
        have hle := Nat.log_le_self 2 (2 * Nat.log 2 (a (j + 1)))
        exact_mod_cast hle
      have h2 : (Nat.log 2 (a (j + 1)) : ℝ) ≤ 2 * Real.sqrt (a (j + 1) : ℝ) :=
        log2_le_two_sqrt _ (hapos _)
      linarith [h1, h2, hsqrt1]
    have hcap2 : (a (j + 1) : ℝ) ≤ q * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) *
        (8 * Real.sqrt (a (j + 1) : ℝ)) :=
      le_trans hcap (mul_le_mul_of_nonneg_left hi (le_of_lt (mul_pos hqpos hPpos)))
    have hsqrtA : Real.sqrt (a (j + 1) : ℝ) ≤
        8 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ)) := by
      have hAsq : (a (j + 1) : ℝ) =
          Real.sqrt (a (j + 1) : ℝ) * Real.sqrt (a (j + 1) : ℝ) :=
        (Real.mul_self_sqrt hA0).symm
      have h5 : Real.sqrt (a (j + 1) : ℝ) * Real.sqrt (a (j + 1) : ℝ) ≤
          (8 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ))) *
            Real.sqrt (a (j + 1) : ℝ) := by
        calc Real.sqrt (a (j + 1) : ℝ) * Real.sqrt (a (j + 1) : ℝ)
            = (a (j + 1) : ℝ) := hAsq.symm
          _ ≤ q * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) *
              (8 * Real.sqrt (a (j + 1) : ℝ)) := hcap2
          _ = (8 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ))) *
              Real.sqrt (a (j + 1) : ℝ) := by ring
      exact le_of_mul_le_mul_right h5 (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hA1))
    calc (a (j + 1) : ℝ)
        = Real.sqrt (a (j + 1) : ℝ) * Real.sqrt (a (j + 1) : ℝ) :=
          (Real.mul_self_sqrt hA0).symm
      _ ≤ (8 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ))) *
          (8 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ))) :=
          mul_le_mul hsqrtA hsqrtA (Real.sqrt_nonneg _)
            (by positivity : (0 : ℝ) ≤ 8 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ)))
      _ = 64 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 := by ring
  have hPnatR : ((∏ i ∈ Finset.range (j + 1), a i : ℕ) : ℝ) =
      ∏ i ∈ Finset.range (j + 1), (a i : ℝ) := by
    push_cast
    rfl
  have hsp' : (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 3 <
      64 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 :=
    lt_of_lt_of_le hsp hboot
  have hPgt : (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) < 64 * q ^ 2 := by
    have h1 : (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 3 =
        (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) *
          (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 := by ring
    rw [h1] at hsp'
    have h2 : (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 =
        q ^ 2 * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 := by ring
    rw [h2] at hsp'
    have h3 : (0 : ℝ) < (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 := pow_pos hPpos 2
    have h4 : 64 * (q ^ 2 * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2) =
        (64 * q ^ 2) * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 := by ring
    have h5 : (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) *
        (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 <
        (64 * q ^ 2) * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 := by
      calc (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) *
          (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2
          < 64 * (q ^ 2 * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2) := hsp'
        _ = (64 * q ^ 2) * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 := h4
    exact lt_of_mul_lt_mul_right h5 h3.le
  have hPlarge : (64 * q ^ 2 : ℝ) ≤ ∏ i ∈ Finset.range (j + 1), (a i : ℝ) := by
    have hPj : (a j : ℝ) ≤ ∏ i ∈ Finset.range (j + 1), (a i : ℝ) := by
      have h2 : a j ≤ ∏ i ∈ Finset.range (j + 1), a i :=
        Finset.single_le_prod' (fun i _ => hapos i)
          (Finset.mem_range.2 (by omega))
      exact_mod_cast h2
    have hP2 : (2 : ℝ) ^ (2 ^ j) ≤ (a j : ℝ) := by
      have h1 := hN₀ j hjN
      have hcast : ((a₂₂ j : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ j) := by
        unfold a₂₂
        push_cast
        rfl
      rwa [hcast] at h1
    have hPnat : (Nat.ceil (64 * q ^ 2 + 1) : ℕ) ≤ ∏ i ∈ Finset.range (j + 1), a i := by
      have h1 : (2 : ℕ) ^ (2 ^ j) ≤ a j := by
        have h2 := hP2
        have hcast : ((2 ^ (2 ^ j) : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ j) := by push_cast; rfl
        rw [← hcast] at h2
        exact_mod_cast h2
      have h3 : (2 : ℕ) ^ j ≤ 2 ^ (2 ^ j) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt Nat.lt_two_pow_self)
      have h4 : (2 : ℕ) ^ j ≥ j + 1 := two_pow_ge_succ j
      have h5 : (2 : ℕ) ^ (2 ^ j) ≤ ∏ i ∈ Finset.range (j + 1), a i := by
        have h6 : a j ≤ ∏ i ∈ Finset.range (j + 1), a i :=
          Finset.single_le_prod' (fun i _ => hapos i)
            (Finset.mem_range.2 (by omega))
        exact le_trans h1 h6
      have h7 : Nat.ceil (64 * q ^ 2 + 1) ≤ 2 ^ (2 ^ j) := by omega
      exact le_trans h7 h5
    have h6 : ((Nat.ceil (64 * q ^ 2 + 1) : ℕ) : ℝ) ≤ ∏ i ∈ Finset.range (j + 1), (a i : ℝ) := by
      rw [← hPnatR]
      exact_mod_cast hPnat
    have h7 : (64 * q ^ 2 + 1 : ℝ) ≤ ((Nat.ceil (64 * q ^ 2 + 1) : ℕ) : ℝ) :=
      Nat.le_ceil _
    nlinarith [h6, h7, hq]
  exact absurd hPgt (not_lt_of_ge hPlarge)

/-- **THE MONOTONE LIM THEOREM (Erdős's Theorem 1 at the lim level):**
if `a` is monotone and `a_n^{1/2^n} → ∞`, then `∑' 1/a` is irrational.
This is the full folklore form for monotone sequences, proved via
Erdős's (9)/(10) dichotomy on the power-of-product cap: the cap case is
`irrational_of_monotone_growth_case10` (the (11) tower + escape records
+ (15)–(17)), and the spike case (take `l = 3`) is
`irrational_of_monotone_growth_and_spike_pow`. -/
theorem irrational_of_oneSidedGrowth_monotone (hg : OneSidedGrowth a)
    (hmono : Monotone a) :
    Irrational (∑' n, 1 / (a n : ℝ)) := by
  by_cases h10 : ∃ l : ℕ, ∀ᶠ j in atTop,
    (a (j + 1) : ℝ) ≤ (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ l
  · obtain ⟨l, hcap⟩ := h10
    exact irrational_of_monotone_growth_case10 hg hmono hcap
  · push Not at h10
    have hsp3 : ∃ᶠ j in atTop,
        (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 3 < (a (j + 1) : ℝ) := h10 3
    exact irrational_of_monotone_growth_and_spike_pow hg hmono hsp3

end Erdos263
