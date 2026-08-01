/-
Erdős Problem #263 — supporting lemmas (ZERO sorry in this file).

All results here are Lean-verified. The open problem itself (Q1) lives in
`Statement.lean`; this file proves the machine-checkable infrastructure around it:

* `a₂₂_succ_sq`        — the exact-boundary identity a_{n+1} = a_n² for a_n = 2^(2^n)
* `a₂₂_strictMono`     — 2^(2^n) is strictly increasing (Q1 well-posedness)
* `summable_one_div_a₂₂` — ∑ 1/2^(2^n) converges
* `tail_bound`         — effective tail bound ∑_{i≥N+1} 1/2^(2^i) < 2 / 2^(2^(N+1))
* `irrational_tsum_one_div_a₂₂` — ∑ 1/2^(2^n) is irrational
    (the base case b_n = a_n of Q1; classical elementary proof:
     if the sum were p/q, then q·2^(2^N)·(tail_N) would be a positive integer
     strictly below 1 for N large — contradiction).
-/
import Mathlib
import Erdos263.Statement

open Filter Topology Finset
open scoped Topology

namespace Erdos263

/-- The Q1 sequence `a_n = 2^(2^n)` (natural-number valued). -/
def a₂₂ (n : ℕ) : ℕ := 2 ^ 2 ^ n

lemma a₂₂_pos (n : ℕ) : 0 < a₂₂ n := pow_pos (by norm_num) _

lemma a₂₂_ge_two (n : ℕ) : 2 ≤ a₂₂ n := by
  have h : (2 : ℕ) ^ 1 ≤ 2 ^ 2 ^ n :=
    pow_le_pow_right₀ (by norm_num) (Nat.one_le_two_pow)
  rw [pow_one] at h
  exact h

/-- **Exact-boundary identity:** for `a_n = 2^(2^n)`, `a_{n+1} = a_n²` EXACTLY.
This is why both known criteria miss Q1 by an epsilon: Kovač–Tao needs
`a_{n+1}/a_n² → 0`, the folklore criterion needs `a_{n+1}/a_n^{2+ε} ↛ 0`. -/
theorem a₂₂_succ_sq (n : ℕ) : a₂₂ (n + 1) = (a₂₂ n) ^ 2 := by
  show (2 : ℕ) ^ (2 ^ (n + 1)) = (2 ^ 2 ^ n) ^ 2
  rw [pow_succ 2 n, pow_mul]

/-- The sequence `2^(2^n)` is strictly increasing — so Q1's instance satisfies
the (corrected) increasing hypothesis. -/
theorem a₂₂_strictMono : StrictMono a₂₂ := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [a₂₂_succ_sq, pow_two]
  have hpos := a₂₂_pos n
  have h2 := a₂₂_ge_two n
  calc a₂₂ n = a₂₂ n * 1 := (mul_one _).symm
  _ < a₂₂ n * a₂₂ n := mul_lt_mul_of_pos_left h2 hpos

lemma a₂₂_ge_two_pow (n : ℕ) : 2 ^ n ≤ a₂₂ n := by
  have h : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
  exact pow_le_pow_right₀ (by norm_num) h

lemma one_div_a₂₂_pos (n : ℕ) : (0 : ℝ) < 1 / (a₂₂ n : ℝ) :=
  one_div_pos.mpr (by exact_mod_cast a₂₂_pos n)

/-- `∑ 1/2^(2^n)` converges. -/
theorem summable_one_div_a₂₂ : Summable (fun n => 1 / (a₂₂ n : ℝ)) := by
  apply Summable.of_nonneg_of_le (f := fun n => (1 / 2 : ℝ) ^ n)
  · intro n
    exact (one_div_a₂₂_pos n).le
  · intro n
    have hle : (2 : ℝ) ^ n ≤ (a₂₂ n : ℝ) := by exact_mod_cast a₂₂_ge_two_pow n
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    calc (1 / (a₂₂ n : ℝ)) ≤ 1 / (2 : ℝ) ^ n := one_div_le_one_div_of_le hpos hle
    _ = (1 / 2 : ℝ) ^ n := by rw [div_pow, one_pow]
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- Helper: `n + 1 ≤ 2^n` (self-contained, avoids reliance on Mathlib naming). -/
lemma two_pow_ge_succ (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      omega

/-- Key exponent inequality: `2^(N+1) + i ≤ 2^i * 2^(N+1)`. -/
lemma exponent_ineq (N i : ℕ) : 2 ^ (N + 1) + i ≤ 2 ^ i * 2 ^ (N + 1) := by
  have hi : i + 1 ≤ 2 ^ i := two_pow_ge_succ i
  have hM : 1 ≤ 2 ^ (N + 1) := Nat.one_le_two_pow
  have hstep : i ≤ 2 ^ (N + 1) * i := by
    calc i = 1 * i := (one_mul i).symm
    _ ≤ 2 ^ (N + 1) * i := mul_le_mul_left hM i
  calc 2 ^ (N + 1) + i ≤ 2 ^ (N + 1) + 2 ^ (N + 1) * i := by
        have h := hstep
        omega
  _ = 2 ^ (N + 1) * (i + 1) := by ring
  _ ≤ 2 ^ (N + 1) * 2 ^ i := mul_le_mul_right hi _
  _ = 2 ^ i * 2 ^ (N + 1) := by ring

/-- Strict version for `i ≥ 1`. -/
lemma exponent_ineq_strict (N : ℕ) {i : ℕ} (hi : 1 ≤ i) :
    2 ^ (N + 1) + i < 2 ^ i * 2 ^ (N + 1) := by
  have h2i : i + 1 ≤ 2 ^ i := two_pow_ge_succ i
  have hM : (1 : ℕ) < 2 ^ (N + 1) := by
    have h : (2 : ℕ) ^ 1 ≤ 2 ^ (N + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_add_left 1 N)
    rw [pow_one] at h
    exact h
  have hstep : i < 2 ^ (N + 1) * i := by
    calc i = 1 * i := (one_mul i).symm
    _ < 2 ^ (N + 1) * i := mul_lt_mul_of_pos_right hM (by omega)
  calc 2 ^ (N + 1) + i < 2 ^ (N + 1) + 2 ^ (N + 1) * i := by
        have h := hstep
        omega
  _ = 2 ^ (N + 1) * (i + 1) := by ring
  _ ≤ 2 ^ (N + 1) * 2 ^ i := mul_le_mul_right h2i _
  _ = 2 ^ i * 2 ^ (N + 1) := by ring

/-- Per-term tail estimate: `1/a₂₂(i + (N+1)) ≤ (1/2^(2^(N+1))) * (1/2)^i`. -/
lemma term_bound (N i : ℕ) :
    (1 / (a₂₂ (i + (N + 1)) : ℝ)) ≤ (1 / (2 : ℝ) ^ (2 ^ (N + 1))) * (1 / 2 : ℝ) ^ i := by
  have hexp : 2 ^ (N + 1) + i ≤ 2 ^ (i + (N + 1)) := by
    rw [pow_add (2 : ℕ) i (N + 1)]
    exact exponent_ineq N i
  have hgrow : (2 : ℕ) ^ (2 ^ (N + 1) + i) ≤ a₂₂ (i + (N + 1)) :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hgrow' : (2 : ℝ) ^ (2 ^ (N + 1)) * 2 ^ i ≤ (a₂₂ (i + (N + 1)) : ℝ) := by
    rw [pow_add (2 : ℕ) (2 ^ (N + 1)) i] at hgrow
    exact_mod_cast hgrow
  have hpos : (0 : ℝ) < 2 ^ (2 ^ (N + 1)) * 2 ^ i := by positivity
  calc (1 / (a₂₂ (i + (N + 1)) : ℝ))
      ≤ 1 / ((2 : ℝ) ^ (2 ^ (N + 1)) * 2 ^ i) := one_div_le_one_div_of_le hpos hgrow'
  _ = (1 / (2 : ℝ) ^ (2 ^ (N + 1))) * (1 / 2 : ℝ) ^ i := by
        rw [div_pow, one_pow, one_div, one_div, mul_inv, one_div]

/-- Per-term strict tail estimate at `i ≥ 1`. -/
lemma term_bound_strict (N : ℕ) {i : ℕ} (hi : 1 ≤ i) :
    (1 / (a₂₂ (i + (N + 1)) : ℝ)) < (1 / (2 : ℝ) ^ (2 ^ (N + 1))) * (1 / 2 : ℝ) ^ i := by
  have hexp : 2 ^ (N + 1) + i < 2 ^ (i + (N + 1)) := by
    rw [pow_add (2 : ℕ) i (N + 1)]
    exact exponent_ineq_strict N hi
  have hgrow : (2 : ℕ) ^ (2 ^ (N + 1) + i) < a₂₂ (i + (N + 1)) :=
    pow_lt_pow_right₀ (by norm_num) hexp
  have hgrow' : (2 : ℝ) ^ (2 ^ (N + 1)) * 2 ^ i < (a₂₂ (i + (N + 1)) : ℝ) := by
    rw [pow_add (2 : ℕ) (2 ^ (N + 1)) i] at hgrow
    exact_mod_cast hgrow
  have hpos : (0 : ℝ) < 2 ^ (2 ^ (N + 1)) * 2 ^ i := by positivity
  calc (1 / (a₂₂ (i + (N + 1)) : ℝ))
      < 1 / ((2 : ℝ) ^ (2 ^ (N + 1)) * 2 ^ i) := one_div_lt_one_div_of_lt hpos hgrow'
  _ = (1 / (2 : ℝ) ^ (2 ^ (N + 1))) * (1 / 2 : ℝ) ^ i := by
        rw [div_pow, one_pow, one_div, one_div, mul_inv, one_div]

/-- **Effective tail bound:** `∑_{i ≥ N+1} 1/2^(2^i) < 2 / 2^(2^(N+1))`.
Written for the shifted series `∑' i, 1/a₂₂(i + (N+1))`. -/
theorem tail_bound (N : ℕ) :
    ∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ)) < 2 / (2 : ℝ) ^ (2 ^ (N + 1)) := by
  set c : ℝ := 1 / (2 : ℝ) ^ (2 ^ (N + 1)) with hc
  have hgsumm : Summable (fun i => c * (1 / 2 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left c
  have hle : ∀ i, (1 / (a₂₂ (i + (N + 1)) : ℝ)) ≤ c * (1 / 2 : ℝ) ^ i :=
    fun i => term_bound N i
  have hlt : (1 / (a₂₂ (1 + (N + 1)) : ℝ)) < c * (1 / 2 : ℝ) ^ 1 :=
    term_bound_strict N (le_refl 1)
  have h0 : ∀ i, (0 : ℝ) ≤ 1 / (a₂₂ (i + (N + 1)) : ℝ) :=
    fun i => (one_div_a₂₂_pos _).le
  have hmain : ∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ)) < ∑' i, c * (1 / 2 : ℝ) ^ i :=
    Summable.tsum_lt_tsum_of_nonneg h0 hle hlt hgsumm
  have hsum : ∑' i, c * (1 / 2 : ℝ) ^ i = c * 2 := by
    rw [tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)]
    norm_num
  calc ∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ))
      < ∑' i, c * (1 / 2 : ℝ) ^ i := hmain
  _ = c * 2 := hsum
  _ = 2 / (2 : ℝ) ^ (2 ^ (N + 1)) := by rw [hc]; ring

/-- The partial sum times `2^(2^N)` is a natural number:
`2^(2^N) * ∑_{n ≤ N} 1/2^(2^n) = ∑_{n ≤ N} 2^(2^N - 2^n)`. -/
lemma partial_sum_int (N : ℕ) :
    ∃ K : ℕ, (2 : ℝ) ^ (2 ^ N) *
      (∑ n ∈ Finset.range (N + 1), (1 / (a₂₂ n : ℝ))) = K := by
  use ∑ n ∈ Finset.range (N + 1), 2 ^ (2 ^ N - 2 ^ n)
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ≤ N := by
    simp only [Finset.mem_range] at hn
    omega
  have hexp : 2 ^ n ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hn'
  have hcast : ((a₂₂ n : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ n) := by simp [a₂₂]
  rw [hcast, one_div, ← pow_sub₀ (2 : ℝ) (by norm_num) hexp]

/-- **Main supporting theorem (Lean-verified target):**
`∑_n 1/2^(2^n)` is irrational — the base case `b_n = a_n` of Q1. -/
theorem irrational_tsum_one_div_a₂₂ : Irrational (∑' n, 1 / (a₂₂ n : ℝ)) := by
  rintro ⟨r, hr⟩
  have hq0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hqne : (r.den : ℝ) ≠ 0 := ne_of_gt hq0
  have hrpq : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    conv_lhs => rw [← Rat.num_div_den r]
    exact Rat.cast_div _ _
  have hsplit : ∀ N : ℕ, (∑ n ∈ Finset.range (N + 1), (1 / (a₂₂ n : ℝ))) +
      ∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ)) = ∑' n, 1 / (a₂₂ n : ℝ) := by
    intro N
    exact summable_one_div_a₂₂.sum_add_tsum_nat_add (N + 1)
  have htail_pos : ∀ N : ℕ, 0 < ∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ)) := by
    intro N
    have hs : Summable (fun i => (1 / (a₂₂ (i + (N + 1)) : ℝ))) :=
      (_root_.summable_nat_add_iff (N + 1)).2 summable_one_div_a₂₂
    have h := Summable.tsum_lt_tsum_of_nonneg (f := fun _ : ℕ => (0 : ℝ))
      (g := fun i => (1 / (a₂₂ (i + (N + 1)) : ℝ))) (i := 0)
      (fun _ => le_refl _) (fun i => (one_div_a₂₂_pos (i + (N + 1))).le)
      (one_div_a₂₂_pos (0 + (N + 1))) hs
    simpa using h
  -- Choose N so large that `2*q < 2^(2^N)`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * r.den < 2 ^ (2 ^ N) := by
    use 2 * r.den
    have h1 : 2 * r.den + 1 ≤ 2 ^ (2 * r.den) := two_pow_ge_succ (2 * r.den)
    have h2 : (2 : ℕ) ^ (2 * r.den) ≤ 2 ^ (2 ^ (2 * r.den)) := by
      apply pow_le_pow_right₀ (by norm_num)
      exact Nat.le_of_lt Nat.lt_two_pow_self
    omega
  obtain ⟨K, hK⟩ := partial_sum_int N
  -- The quantity z = q · 2^(2^N) · tail_N is an integer in (0,1): contradiction
  have hz_eq : (r.den : ℝ) * (2 : ℝ) ^ (2 ^ N) *
      (∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ))) =
      (((2 : ℤ) ^ (2 ^ N) * r.num - r.den * K : ℤ) : ℝ) := by
    have hsum : (r.den : ℝ) * (2 : ℝ) ^ (2 ^ N) * (∑' n, 1 / (a₂₂ n : ℝ)) =
        (2 : ℝ) ^ (2 ^ N) * r.num := by
      rw [← hr, hrpq]
      field_simp
    have hpart : (r.den : ℝ) * (2 : ℝ) ^ (2 ^ N) *
        (∑ n ∈ Finset.range (N + 1), (1 / (a₂₂ n : ℝ))) = (r.den : ℝ) * K := by
      rw [mul_assoc, hK]
    have htail : ∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ)) =
        (∑' n, 1 / (a₂₂ n : ℝ)) -
          (∑ n ∈ Finset.range (N + 1), (1 / (a₂₂ n : ℝ))) := by
      have h := hsplit N
      linarith
    rw [htail, mul_sub, hsum, hpart]
    push_cast
    ring
  have hz_pos : (0 : ℝ) < (r.den : ℝ) * (2 : ℝ) ^ (2 ^ N) *
      (∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ))) :=
    mul_pos (mul_pos hq0 (by positivity)) (htail_pos N)
  have hz_lt_one : (r.den : ℝ) * (2 : ℝ) ^ (2 ^ N) *
      (∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ))) < 1 := by
    have hb := tail_bound N
    have hstep : (r.den : ℝ) * (2 : ℝ) ^ (2 ^ N) *
        (∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ))) <
        (r.den : ℝ) * (2 : ℝ) ^ (2 ^ N) * (2 / (2 : ℝ) ^ (2 ^ (N + 1))) :=
      mul_lt_mul_of_pos_left hb (mul_pos hq0 (by positivity))
    have hsq : (2 : ℝ) ^ (2 ^ (N + 1)) = ((2 : ℝ) ^ (2 ^ N)) ^ 2 := by
      rw [← pow_mul, pow_succ 2 N]
    have h2q : (2 : ℝ) * r.den < (2 : ℝ) ^ (2 ^ N) := by exact_mod_cast hN
    calc (r.den : ℝ) * (2 : ℝ) ^ (2 ^ N) * (∑' i, (1 / (a₂₂ (i + (N + 1)) : ℝ)))
        < (r.den : ℝ) * (2 : ℝ) ^ (2 ^ N) * (2 / (2 : ℝ) ^ (2 ^ (N + 1))) := hstep
    _ = 2 * r.den / (2 : ℝ) ^ (2 ^ N) := by
          rw [hsq, sq]
          field_simp
    _ < 1 := by
          rw [div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 ^ N))]
          exact h2q
  rw [hz_eq] at hz_pos hz_lt_one
  have h1 : (0 : ℤ) < (2 : ℤ) ^ (2 ^ N) * r.num - r.den * K := by
    exact_mod_cast hz_pos
  have h2 : (2 : ℤ) ^ (2 ^ N) * r.num - r.den * K < 1 := by
    exact_mod_cast hz_lt_one
  omega

/-- **Boundary witness:** the ratio `a_{n+1}/a_n²` is CONSTANT 1, hence tends to 1 —
not to 0 (Kovač–Tao's non-example hypothesis) and not to +∞; and
`liminf a_{n+1}/a_n^{2+ε} = 0` for every ε > 0 (folklore sufficiency hypothesis).
This is the precise sense in which Q1 sits exactly at the boundary. -/
theorem a₂₂_ratio_boundary :
    Tendsto (fun n => (a₂₂ (n + 1) : ℝ) / (a₂₂ n : ℝ) ^ 2) atTop (𝓝 1) := by
  have h : ∀ n : ℕ, (a₂₂ (n + 1) : ℝ) / (a₂₂ n : ℝ) ^ 2 = 1 := by
    intro n
    have hne : ((a₂₂ n : ℝ)) ≠ 0 := by exact_mod_cast (a₂₂_pos n).ne'
    rw [a₂₂_succ_sq, Nat.cast_pow, div_self (pow_ne_zero _ hne)]
  simp only [h]
  exact tendsto_const_nhds

end Erdos263
