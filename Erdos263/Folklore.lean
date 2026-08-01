/-
Erdős Problem #263 — the FOLKLORE CRITERION for irrationality sequences.

Informal source (fetched 2026-08-01 with `Cache-Control: no-cache`;
page last edited 2026-04-02): https://www.erdosproblems.com/263 —

  "A folklore result states that ∑ 1/a_n is irrational whenever
   lim a_n^{1/2^n} = ∞. [...] On the other hand, if
       liminf a_{n+1} / a_n^{2+ε} > 0
   for some ε > 0 then the above folklore result implies that a_n is such an
   irrationality sequence."

Koizumi (arXiv:2504.05933v1, intro; fetched 2026-08-01) states the same
folklore result ("if a sequence satisfies lim a_n^{2^{-n}} = ∞, then its
reciprocal sum is irrational") and notes that any sequence with
a_n^{2^{-n}} → ∞ is a Type 2 irrationality sequence (terminology of
Kovač–Tao, arXiv:2406.17593).

PROOF ROUTE (standard tail-domination; the same iteration pattern as
Koizumi's proof of his Theorem 1, eq. (1.2)): suppose ∑ 1/b_n = p/q. With
P_N := ∏_{n ≤ N} b_n and T_N := ∑_{n > N} 1/b_n, the number q·P_N·T_N is a
POSITIVE INTEGER (all partial sums clear denominators). The growth
condition gives:

  (i)   eventually a_{n+1} ≥ a_n², hence a_{N+k} ≥ a_N^{2^k} and
        T_N ≤ 4 / a_{N+1}        (forward iteration; geometric series, 2^k ≥ k+1);
  (ii)  backward control a_{N-k} ≤ K·a_N^{θ^k} with θ := 1/(2+ε), hence
        ∏_{n ≤ N} a_n ≤ C^{N+1}·a_N^{σ}, σ := (2+ε)/(1+ε) < 2+ε;
  (iii) since a_N grows doubly exponentially by (i), D^{N+1} ≤ a_N^{δ/2}
        eventually for any constant D, where δ := (2+ε) − σ > 0.

With b_n ≤ 2a_n eventually, q·P_N·T_N ≤ (4q·C_b/c)·(2C)^{N+1}·a_N^{-δ} < 1 for
all large N — an integer in (0,1), contradiction.

FIDELITY NOTES (audit gate: compare against the site text above, line by line):

1. "liminf a_{n+1}/a_n^{2+ε} > 0 for some ε > 0" is unpacked as
   `∃ ε > 0, ∃ c > 0, ∀ᶠ n, c * (a n)^(2+ε) ≤ a (n+1)` — this is exactly
   liminf > 0 for a positive sequence (c ≤ a_{n+1}/a_n^{2+ε} eventually).
2. "increasing" (the problem's standing hypothesis) is `StrictMono a`;
   positivity of a is explicit. No convergence hypothesis is needed: the
   growth condition implies summability (proved here, `summable_one_div_of_growth`).
3. The conclusion is `IsIrrationalitySequence a` from `Statement.lean`, i.e.
   "a_n is such an irrationality sequence" with the corrected (increasing)
   definition: for EVERY positive b with b_n/a_n → 1, ∑' 1/b_n is irrational.
4. Indexing from n = 0 (ℕ) instead of n = 1 is immaterial (finite shift).
5. The site's first form (lim a_n^{1/2^n} = ∞ ⇒ irrational sum) is NOT
   formalized here; only the ratio-growth criterion the site derives from it.
-/
import Mathlib
import Erdos263.Basic

open Filter Topology Finset
open scoped Topology

namespace Erdos263

variable {a : ℕ → ℕ}

/-! ### ℝ-specialized multiplication monotonicity helpers

The unbundled `MulLeftMono`/`MulRightMono` typeclass instances do not exist
for `ℝ` (multiplication by a negative flips the order), so lemmas requiring
them (`le_mul_of_one_le_left`, `le_mul_of_one_le_right`, `pow_le_pow_left'`,
`mul_lt_mul''`) cannot be used here. These local replacements are proved
directly from `mul_nonneg`/`mul_pos`. -/

lemma mul_le_mul_nn_left {x y c : ℝ} (h : x ≤ y) (hc : 0 ≤ c) : c * x ≤ c * y := by
  have h2 : 0 ≤ c * (y - x) := mul_nonneg hc (sub_nonneg_of_le h)
  linarith [h2]

lemma mul_le_mul_nn_right {x y c : ℝ} (h : x ≤ y) (hc : 0 ≤ c) : x * c ≤ y * c := by
  have h2 : 0 ≤ (y - x) * c := mul_nonneg (sub_nonneg_of_le h) hc
  linarith [h2]

lemma le_mul_of_one_le_right_nn {x c : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c) : x ≤ x * c := by
  have h2 : 0 ≤ x * (c - 1) := mul_nonneg hx (sub_nonneg_of_le hc)
  linarith [h2]

lemma le_mul_of_one_le_left_nn {x c : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c) : x ≤ c * x := by
  have h2 : 0 ≤ (c - 1) * x := mul_nonneg (sub_nonneg_of_le hc) hx
  linarith [h2]

lemma mul_lt_mul_pos_right {x y c : ℝ} (h : x < y) (hc : 0 < c) : x * c < y * c := by
  have h2 : 0 < (y - x) * c := mul_pos (sub_pos_of_lt h) hc
  linarith [h2]

/-! ### Elementary growth facts -/

/-- A strictly increasing `f : ℕ → ℕ` dominates the identity. -/
lemma self_le_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) : n ≤ f n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hf (Nat.lt_succ_self k)))

lemma tendsto_atTop_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f) :
    Tendsto (fun n => (f n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => ((n : ℝ))) (g := fun n => (f n : ℝ))
    (fun n => by exact_mod_cast self_le_of_strictMono hf n)
  exact tendsto_natCast_atTop_atTop

/-- `2^n ≥ (n+1)²` for `n ≥ 6` (self-contained exp-beats-polynomial step). -/
lemma two_pow_ge_sq_add_one (n : ℕ) (hn : 6 ≤ n) : (n + 1) ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hk2 : (2 : ℕ) ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left (by omega : 2 ≤ k) 2
      have h1 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      have h2 : 2 * (k + 1) + 1 ≤ (k + 1) ^ 2 := by rw [h1]; omega
      calc (k + 1 + 1) ^ 2 = (k + 1) ^ 2 + (2 * (k + 1) + 1) := by ring
      _ ≤ 2 ^ k + (2 * (k + 1) + 1) := by omega
      _ ≤ 2 ^ k + 2 ^ k := by exact Nat.add_le_add_left (le_trans h2 ih) _
      _ = 2 ^ (k + 1) := by ring

/-- For any fixed `t`, eventually `(n+1)·t ≤ 2^n` (exponential dominates linear). -/
lemma two_pow_eventually_dominates (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) * t ≤ 2 ^ n := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max t 0)
  refine eventually_atTop.2 ⟨max 6 m, fun n hn => ?_⟩
  have hn6 : 6 ≤ n := le_trans (le_max_left _ _) hn
  have hnm : m ≤ n := le_trans (le_max_right _ _) hn
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ n := by
    exact_mod_cast two_pow_ge_sq_add_one n hn6
  have ht2 : t ≤ (n : ℝ) + 1 := by
    have h1 : max t 0 < (m : ℝ) := hm
    have h2 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
    have h3 : t ≤ max t 0 := le_max_left _ _
    linarith
  calc ((n : ℝ) + 1) * t ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) :=
        mul_le_mul_nn_left ht2 (by positivity)
  _ = ((n : ℝ) + 1) ^ 2 := by rw [pow_two]
  _ ≤ 2 ^ n := hsq

/-! ### The quadratic bootstrap and forward growth -/

/-- The growth condition `c·a_n^{2+ε} ≤ a_{n+1}` with `a_n → ∞` eventually
yields the quadratic step `a_n² ≤ a_{n+1}` (the `c·a_n^ε ≥ 1` bootstrap). -/
lemma eventually_sq_le (hapos : ∀ n, 0 < a n) (hmono : StrictMono a)
    {ε : ℝ} (hε : 0 < ε) {c : ℝ} (hc : 0 < c)
    (hgrowth : ∀ᶠ n in atTop, c * (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ)) :
    ∀ᶠ n in atTop, (a n : ℝ) ^ 2 ≤ (a (n + 1) : ℝ) := by
  have hta : Tendsto (fun n => (a n : ℝ)) atTop atTop := tendsto_atTop_of_strictMono hmono
  have htp : Tendsto (fun n => (a n : ℝ) ^ ε) atTop atTop := (tendsto_rpow_atTop hε).comp hta
  have hev1 : ∀ᶠ n in atTop, (1 / c) ≤ (a n : ℝ) ^ ε := htp.eventually_ge_atTop _
  filter_upwards [hgrowth, hev1] with n hn h1c
  have hx : (0 : ℝ) < a n := by exact_mod_cast hapos n
  have hsplit : (a n : ℝ) ^ (2 + ε) = (a n : ℝ) ^ 2 * (a n : ℝ) ^ ε := by
    rw [Real.rpow_add hx (2 : ℝ) ε, Real.rpow_two]
  have h1 : (1 : ℝ) ≤ c * (a n : ℝ) ^ ε := by
    rw [div_le_iff₀ hc] at h1c
    rwa [mul_comm] at h1c
  rw [hsplit] at hn
  calc (a n : ℝ) ^ 2 ≤ (a n : ℝ) ^ 2 * (c * (a n : ℝ) ^ ε) :=
      le_mul_of_one_le_right_nn (by positivity) h1
  _ = c * ((a n : ℝ) ^ 2 * (a n : ℝ) ^ ε) := by ring
  _ ≤ (a (n + 1) : ℝ) := hn

/-- Forward iteration of the quadratic step: `a (M+k) ≥ a_M^{2^k}`. -/
lemma pow_growth (_hapos : ∀ n, 0 < a n) {M : ℕ}
    (hsq : ∀ m ≥ M, (a m : ℝ) ^ 2 ≤ (a (m + 1) : ℝ)) (k : ℕ) :
    (a M : ℝ) ^ (2 ^ k) ≤ (a (M + k) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : (a (M + k) : ℝ) ^ 2 ≤ (a (M + k + 1) : ℝ) :=
        hsq (M + k) (Nat.le_add_right M k)
      have h2 : ((a M : ℝ) ^ (2 ^ k)) ^ 2 ≤ (a (M + k) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) ih 2
      have h3 : (a M : ℝ) ^ (2 ^ (k + 1)) = ((a M : ℝ) ^ (2 ^ k)) ^ 2 := by
        rw [pow_succ 2 k, ← pow_mul]
      have h4 : M + (k + 1) = M + k + 1 := by ring
      rw [h3, h4]
      exact le_trans h2 h1

/-! ### Summability and the tail bound -/

/-- Summability of `∑ 1/a_n` from the quadratic step (comparison with the
geometric series, using `2^k ≥ k+1`). -/
lemma summable_one_div_of_sq (hapos : ∀ n, 0 < a n) {M : ℕ} (hM2 : 2 ≤ a M)
    (hsq : ∀ m ≥ M, (a m : ℝ) ^ 2 ≤ (a (m + 1) : ℝ)) :
    Summable (fun n => 1 / (a n : ℝ)) := by
  have hM2r : (2 : ℝ) ≤ a M := by exact_mod_cast hM2
  have hterm : ∀ k : ℕ, (1 / (a (k + M) : ℝ)) ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    have hg := pow_growth hapos hsq k
    have hadd : M + k = k + M := by ring
    rw [hadd] at hg
    have hA : (2 : ℝ) ^ (2 ^ k) ≤ (a (k + M) : ℝ) :=
      le_trans (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hM2r _) hg
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ k) := by positivity
    calc (1 / (a (k + M) : ℝ)) ≤ 1 / (2 : ℝ) ^ (2 ^ k) :=
          one_div_le_one_div_of_le hpos hA
    _ = (1 / 2 : ℝ) ^ (2 ^ k) := by rw [div_pow, one_pow]
    _ ≤ (1 / 2 : ℝ) ^ (k + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (two_pow_ge_succ k)
    _ ≤ (1 / 2 : ℝ) ^ k :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
  have hsumm : Summable (fun k : ℕ => 1 / (a (k + M) : ℝ)) := by
    apply Summable.of_nonneg_of_le (f := fun k : ℕ => (1 / 2 : ℝ) ^ k)
    · intro k; exact one_div_nonneg.mpr (by positivity)
    · exact hterm
    · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact (summable_nat_add_iff M).1 hsumm

/-- The folklore growth condition implies `∑ 1/a_n` converges (no separate
convergence hypothesis is needed in the criterion). -/
lemma summable_one_div_of_growth (hapos : ∀ n, 0 < a n) (hmono : StrictMono a)
    {ε : ℝ} (hε : 0 < ε) {c : ℝ} (hc : 0 < c)
    (hgrowth : ∀ᶠ n in atTop, c * (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ)) :
    Summable (fun n => 1 / (a n : ℝ)) := by
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (eventually_sq_le hapos hmono hε hc hgrowth)
  have ha1 : 2 ≤ a (max N₂ 1) := by
    have h1 : a 1 ≥ 2 := by
      have h01 := hmono (by norm_num : (0 : ℕ) < 1)
      have hp0 := hapos 0
      omega
    have h2 : a 1 ≤ a (max N₂ 1) := hmono.monotone (by omega)
    omega
  exact summable_one_div_of_sq hapos ha1 (fun m hm => hN₂ m (by omega))

/-- **Tail domination (the T2 core lemma):** under the quadratic step from `M`
on, the tail of `∑ 1/a_n` after `M` is at most `2 / a_{M+1}`. This is the
general-`a` analogue of `tail_bound` in `Basic.lean`. -/
lemma tail_le_two_div (hapos : ∀ n, 0 < a n) {M : ℕ} (hM2 : 2 ≤ a M)
    (hsq : ∀ m ≥ M, (a m : ℝ) ^ 2 ≤ (a (m + 1) : ℝ)) :
    ∑' i, (1 / (a (i + (M + 1)) : ℝ)) ≤ 2 / (a (M + 1) : ℝ) := by
  have hM1 : (2 : ℝ) ≤ a (M + 1) := by
    have h := hsq M (le_refl M)
    have hM2r : (2 : ℝ) ≤ a M := by exact_mod_cast hM2
    calc (2 : ℝ) ≤ (a M : ℝ) ^ 2 := by nlinarith [hM2r]
    _ ≤ (a (M + 1) : ℝ) := h
  have hA0 : (0 : ℝ) < a (M + 1) := by linarith [hM1]
  have h1A : (1 : ℝ) ≤ a (M + 1) := by linarith [hM1]
  have hterm : ∀ i : ℕ, (1 / (a (i + (M + 1)) : ℝ)) ≤
      (1 / (a (M + 1) : ℝ)) * (1 / (a (M + 1) : ℝ)) ^ i := by
    intro i
    have hg := pow_growth hapos (M := M + 1) (fun m hm => hsq m (by omega)) i
    have hadd : M + 1 + i = i + (M + 1) := by ring
    rw [hadd] at hg
    have hApos : (0 : ℝ) < (a (M + 1) : ℝ) ^ (2 ^ i) := pow_pos hA0 _
    have hx0 : (0 : ℝ) ≤ 1 / (a (M + 1) : ℝ) := one_div_nonneg.mpr hA0.le
    have hx1 : 1 / (a (M + 1) : ℝ) ≤ 1 := (div_le_one hA0).mpr h1A
    calc (1 / (a (i + (M + 1)) : ℝ)) ≤ 1 / (a (M + 1) : ℝ) ^ (2 ^ i) :=
          one_div_le_one_div_of_le hApos hg
    _ = (1 / (a (M + 1) : ℝ)) ^ (2 ^ i) := by rw [div_pow, one_pow]
    _ ≤ (1 / (a (M + 1) : ℝ)) ^ (i + 1) :=
          pow_le_pow_of_le_one hx0 hx1 (two_pow_ge_succ i)
    _ = (1 / (a (M + 1) : ℝ)) * (1 / (a (M + 1) : ℝ)) ^ i := by rw [pow_succ']
  have hx1lt : 1 / (a (M + 1) : ℝ) < 1 := (div_lt_one hA0).mpr (by linarith [hM1])
  have hx0 : (0 : ℝ) ≤ 1 / (a (M + 1) : ℝ) := one_div_nonneg.mpr hA0.le
  have hgsumm : Summable (fun i : ℕ => (1 / (a (M + 1) : ℝ)) * (1 / (a (M + 1) : ℝ)) ^ i) :=
    (summable_geometric_of_lt_one hx0 hx1lt).mul_left _
  have hlsumm : Summable (fun i : ℕ => 1 / (a (i + (M + 1)) : ℝ)) := by
    apply Summable.of_nonneg_of_le (f := fun i : ℕ =>
      (1 / (a (M + 1) : ℝ)) * (1 / (a (M + 1) : ℝ)) ^ i)
    · intro i; exact one_div_nonneg.mpr (by positivity)
    · exact hterm
    · exact hgsumm
  have hle : ∑' i, (1 / (a (i + (M + 1)) : ℝ)) ≤
      ∑' i, (1 / (a (M + 1) : ℝ)) * (1 / (a (M + 1) : ℝ)) ^ i :=
    Summable.tsum_le_tsum hterm hlsumm hgsumm
  have hsum : ∑' i, (1 / (a (M + 1) : ℝ)) * (1 / (a (M + 1) : ℝ)) ^ i =
      (1 / (a (M + 1) : ℝ)) * (1 / (1 - 1 / (a (M + 1) : ℝ))) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1lt, inv_eq_one_div]
  have hbound : (1 / (a (M + 1) : ℝ)) * (1 / (1 - 1 / (a (M + 1) : ℝ))) ≤
      2 / (a (M + 1) : ℝ) := by
    have h1m : (0 : ℝ) < 1 - 1 / (a (M + 1) : ℝ) := by linarith [hx1lt, hA0]
    rw [le_div_iff₀ hA0]
    calc (1 / (a (M + 1) : ℝ)) * (1 / (1 - 1 / (a (M + 1) : ℝ))) * (a (M + 1) : ℝ)
        = 1 / (1 - 1 / (a (M + 1) : ℝ)) := by field_simp [hA0.ne', h1m.ne']
    _ ≤ 2 := by
        rw [div_le_iff₀ h1m]
        have h5 : 1 / (a (M + 1) : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 1) hA0
            (by norm_num : (0 : ℝ) < 2)]
          linarith [hM1]
        linarith [h5]
  calc ∑' i, (1 / (a (i + (M + 1)) : ℝ)) ≤
        (1 / (a (M + 1) : ℝ)) * (1 / (1 - 1 / (a (M + 1) : ℝ))) :=
      le_trans hle (le_of_eq hsum)
  _ ≤ 2 / (a (M + 1) : ℝ) := hbound

/-- Tail positivity (needed to make the integer in the final contradiction
strictly positive). -/
lemma tail_pos (hapos : ∀ n, 0 < a n) {M : ℕ} (hM2 : 2 ≤ a M)
    (hsq : ∀ m ≥ M, (a m : ℝ) ^ 2 ≤ (a (m + 1) : ℝ)) :
    (0 : ℝ) < ∑' i, (1 / (a (i + (M + 1)) : ℝ)) := by
  have hsumm : Summable (fun i : ℕ => 1 / (a (i + (M + 1)) : ℝ)) :=
    (_root_.summable_nat_add_iff (M + 1)).2 (summable_one_div_of_sq hapos hM2 hsq)
  have h := Summable.tsum_lt_tsum_of_nonneg (f := fun _ : ℕ => (0 : ℝ))
    (g := fun i : ℕ => (1 / (a (i + (M + 1)) : ℝ))) (i := 0)
    (fun _ => le_refl _) (fun i => one_div_nonneg.mpr (by positivity))
    (one_div_pos.mpr (by exact_mod_cast hapos (0 + (M + 1)))) hsumm
  simpa using h

/-! ### Backward iteration: the product bound -/

/-- Backward control: from `c'·a_n^{2+ε} ≤ a_{n+1}` for `n ≥ N₀` (with
`0 < c' ≤ 1`) and `θ` with `(2+ε)·θ = 1`, each earlier term is bounded by a
later one: `a_{N-k} ≤ K·a_N^{θ^k}` for a constant `K ≥ 1`. The constant
works because `σ·θ + 1 = σ` for `σ := 1/(1-θ)`. -/
lemma backward_bound (hapos : ∀ n, 0 < a n) {ε : ℝ} (hε : 0 < ε)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hθ : (2 + ε) * θ = 1)
    {c' : ℝ} (hc'0 : 0 < c') (hc'1 : c' ≤ 1) {N₀ : ℕ}
    (hg : ∀ n ≥ N₀, c' * (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {N k : ℕ}, N₀ + k ≤ N →
      (a (N - k) : ℝ) ≤ K * (a N : ℝ) ^ (θ ^ k) := by
  have h2ε : (0 : ℝ) < 2 + ε := by linarith
  have h1mθ : (0 : ℝ) < 1 - θ := by linarith
  set σ : ℝ := 1 / (1 - θ) with hσdef
  have hσeq : σ * (1 - θ) = 1 := by rw [hσdef]; field_simp [h1mθ.ne']
  have hσ0 : (0 : ℝ) < σ := by rw [hσdef]; positivity
  have hσ1 : (1 : ℝ) ≤ σ := by
    rw [hσdef, le_div_iff₀ h1mθ, one_mul]
    linarith [hθ0.le]
  set K₁ : ℝ := 1 / (c' : ℝ) ^ θ with hK₁def
  have hc'θ1 : (c' : ℝ) ^ θ ≤ 1 := Real.rpow_le_one hc'0.le hc'1 hθ0.le
  have hK₁1 : (1 : ℝ) ≤ K₁ := by
    rw [hK₁def, le_div_iff₀ (Real.rpow_pos_of_pos hc'0 θ), one_mul]
    exact hc'θ1
  have hK₁0 : (0 : ℝ) < K₁ := lt_of_lt_of_le zero_lt_one hK₁1
  have step : ∀ n ≥ N₀, (a n : ℝ) ≤ K₁ * (a (n + 1) : ℝ) ^ θ := by
    intro n hn
    have hx : (0 : ℝ) < a n := by exact_mod_cast hapos n
    have h1 : (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ) / c' := by
      rw [le_div_iff₀ hc'0, mul_comm]
      exact hg n hn
    have h2 : ((a n : ℝ) ^ (2 + ε)) ^ θ ≤ ((a (n + 1) : ℝ) / c') ^ θ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) h1 hθ0.le
    rw [← Real.rpow_mul hx.le (2 + ε) θ, hθ, Real.rpow_one] at h2
    rw [Real.div_rpow (by positivity) hc'0.le θ] at h2
    have e : (a (n + 1) : ℝ) ^ θ / (c' : ℝ) ^ θ = K₁ * (a (n + 1) : ℝ) ^ θ := by
      rw [hK₁def, div_eq_inv_mul, one_div, mul_comm]
    rwa [e] at h2
  refine ⟨K₁ ^ σ, Real.one_le_rpow hK₁1 hσ0.le, fun {N k} hNk => ?_⟩
  induction k generalizing N with
  | zero =>
      simp only [Nat.sub_zero, pow_zero, Real.rpow_one]
      calc (a N : ℝ) ≤ K₁ * a N := le_mul_of_one_le_left_nn (by positivity) hK₁1
      _ ≤ K₁ ^ σ * a N := by
          apply mul_le_mul_nn_right _ (by positivity)
          nth_rewrite 1 [← Real.rpow_one K₁]
          exact Real.rpow_le_rpow_of_exponent_le hK₁1 hσ1
  | succ k ih =>
      have hNk' : N₀ + k ≤ N := by omega
      have hM : N₀ ≤ N - (k + 1) := by omega
      have hMk : N - k = N - (k + 1) + 1 := by omega
      have hih := ih hNk'
      rw [hMk] at hih
      calc (a (N - (k + 1)) : ℝ) ≤ K₁ * (a (N - (k + 1) + 1) : ℝ) ^ θ := step _ hM
      _ ≤ K₁ * (K₁ ^ σ * (a N : ℝ) ^ (θ ^ k)) ^ θ :=
          mul_le_mul_nn_left (Real.rpow_le_rpow (by positivity) hih hθ0.le) hK₁0.le
      _ = K₁ * ((K₁ ^ σ) ^ θ * ((a N : ℝ) ^ (θ ^ k)) ^ θ) := by
          rw [Real.mul_rpow (Real.rpow_nonneg hK₁0.le _)
            (Real.rpow_nonneg (by positivity) _)]
      _ = K₁ * ((K₁ ^ σ) ^ θ) * (a N : ℝ) ^ (θ ^ k * θ) := by
          rw [← Real.rpow_mul (by positivity) (θ ^ k) θ]; ring
      _ = K₁ ^ (σ * θ + 1) * (a N : ℝ) ^ (θ ^ (k + 1)) := by
          have e1 : K₁ * ((K₁ ^ σ) ^ θ) = K₁ ^ (σ * θ + 1) := by
            rw [← Real.rpow_mul hK₁0.le σ θ]
            nth_rewrite 1 [← Real.rpow_one K₁]
            rw [← Real.rpow_add hK₁0, add_comm (1 : ℝ) (σ * θ)]
          have e2 : (θ : ℝ) ^ k * θ = θ ^ (k + 1) := by rw [pow_succ]
          rw [e1, e2]
      _ ≤ K₁ ^ σ * (a N : ℝ) ^ (θ ^ (k + 1)) := by
          apply mul_le_mul_nn_right _ (Real.rpow_nonneg (by positivity) _)
          apply Real.rpow_le_rpow_of_exponent_le hK₁1
          have h2 : σ * θ + 1 = σ := by
            have h3 : σ * (1 - θ) = σ - σ * θ := by ring
            rw [hσeq] at h3
            linarith
          rw [h2]

/-- **Product bound:** the product of the first `N+1` terms is
sub-`a_{N+1}`: `∏_{n ≤ N} a_n ≤ C^{N+1}·a_N^{σ}` with
`σ = (2+ε)/(1+ε) < 2+ε`. This is the analytic heart of the criterion. -/
lemma prod_bound (hapos : ∀ n, 0 < a n) (hmono : StrictMono a)
    {ε : ℝ} (hε : 0 < ε) {c : ℝ} (hc : 0 < c)
    (hgrowth : ∀ᶠ n in atTop, c * (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ N in atTop,
      (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) ≤
        C ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε)) := by
  have h2ε : (0 : ℝ) < 2 + ε := by linarith
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  set c' := min c 1 with hc'def
  have hc'0 : 0 < c' := lt_min hc zero_lt_one
  have hc'1 : c' ≤ 1 := min_le_right _ _
  have hg' : ∀ᶠ n in atTop, c' * (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ) := by
    filter_upwards [hgrowth] with n hn
    have h0 : (0 : ℝ) ≤ (a n : ℝ) ^ (2 + ε) := Real.rpow_nonneg (by positivity) _
    have h1 : c' ≤ c := min_le_left _ _
    have h2 : c' * (a n : ℝ) ^ (2 + ε) ≤ c * (a n : ℝ) ^ (2 + ε) := by
      have h3 : 0 ≤ (c - c') * ((a n : ℝ) ^ (2 + ε)) :=
        mul_nonneg (sub_nonneg_of_le h1) h0
      linarith [h3]
    exact le_trans h2 hn
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hg'
  set θ : ℝ := 1 / (2 + ε) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one h2ε]
    linarith
  have hθ : (2 + ε) * θ = 1 := by
    rw [hθdef]
    field_simp [h2ε.ne']
  obtain ⟨K, hK1, hK⟩ := backward_bound hapos hε hθ0 hθ1 hθ hc'0 hc'1 hN₀
  have h1mθid : (1 : ℝ) - θ = (1 + ε) / (2 + ε) := by
    rw [hθdef, eq_div_iff h2ε.ne', sub_mul, div_mul_cancel₀ 1 h2ε.ne']
    ring
  have hσid : 1 / (1 - θ) = (2 + ε) / (1 + ε) := by
    rw [h1mθid, one_div_div]
  have key : ∀ N ≥ N₀, (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) ≤
      ((a N₀ : ℝ) ^ N₀ * K) ^ (N + 1) * (a N : ℝ) ^ (1 / (1 - θ)) := by
    intro N hN
    have hsplit : N + 1 = N₀ + (N + 1 - N₀) := by omega
    nth_rewrite 1 [hsplit]
    rw [Finset.prod_range_add]
    have hf1 : (∏ n ∈ Finset.range N₀, (a n : ℝ)) ≤ (a N₀ : ℝ) ^ N₀ := by
      have h1 : ∀ i ∈ Finset.range N₀, (a i : ℝ) ≤ (a N₀ : ℝ) := by
        intro i hi
        have hi' : i < N₀ := Finset.mem_range.1 hi
        have h : a i ≤ a N₀ := hmono.monotone (by omega)
        exact_mod_cast h
      calc (∏ n ∈ Finset.range N₀, (a n : ℝ))
          ≤ ∏ _n ∈ Finset.range N₀, ((a N₀ : ℝ)) :=
            Finset.prod_le_prod (fun i _ => by positivity) h1
      _ = (a N₀ : ℝ) ^ N₀ := by rw [Finset.prod_const, Finset.card_range]
    have hterm : ∀ k ∈ Finset.range (N + 1 - N₀),
        (a (N₀ + k) : ℝ) ≤ K * (a N : ℝ) ^ (θ ^ (N - N₀ - k)) := by
      intro k hk
      have hk' : k < N + 1 - N₀ := Finset.mem_range.1 hk
      have hle : N₀ + (N - (N₀ + k)) ≤ N := by omega
      have heq : N - (N - (N₀ + k)) = N₀ + k := by omega
      have hexp : N - (N₀ + k) = N - N₀ - k := by omega
      have h := hK (N := N) (k := N - (N₀ + k)) hle
      rw [heq, hexp] at h
      exact h
    have hf2 : (∏ k ∈ Finset.range (N + 1 - N₀), (a (N₀ + k) : ℝ)) ≤
        K ^ (N + 1 - N₀) * (a N : ℝ) ^ (1 / (1 - θ)) := by
      have haN1 : (1 : ℝ) ≤ a N := by exact_mod_cast hapos N
      have haN0 : (0 : ℝ) < a N := by positivity
      calc (∏ k ∈ Finset.range (N + 1 - N₀), (a (N₀ + k) : ℝ))
          ≤ ∏ k ∈ Finset.range (N + 1 - N₀),
              (K * (a N : ℝ) ^ (θ ^ (N - N₀ - k))) :=
            Finset.prod_le_prod (fun i _ => by positivity) hterm
      _ = (∏ _k ∈ Finset.range (N + 1 - N₀), K) *
            ∏ k ∈ Finset.range (N + 1 - N₀), ((a N : ℝ) ^ (θ ^ (N - N₀ - k))) :=
            Finset.prod_mul_distrib
      _ = K ^ (N + 1 - N₀) *
            ∏ k ∈ Finset.range (N + 1 - N₀), ((a N : ℝ) ^ (θ ^ (N - N₀ - k))) := by
            rw [Finset.prod_const, Finset.card_range]
      _ = K ^ (N + 1 - N₀) *
            (a N : ℝ) ^ (∑ k ∈ Finset.range (N + 1 - N₀), θ ^ (N - N₀ - k)) := by
            rw [← Real.rpow_sum_of_pos haN0]
      _ ≤ K ^ (N + 1 - N₀) * (a N : ℝ) ^ (1 / (1 - θ)) := by
            apply mul_le_mul_nn_left _ (pow_nonneg (by linarith [hK1]) _)
            apply Real.rpow_le_rpow_of_exponent_le haN1
            have hrefl : (∑ k ∈ Finset.range (N + 1 - N₀), θ ^ (N - N₀ - k)) =
                ∑ j ∈ Finset.range (N + 1 - N₀), θ ^ j := by
              have h := Finset.sum_range_reflect (fun j => θ ^ j) (N + 1 - N₀)
              rw [← h]
              apply Finset.sum_congr rfl
              intro k hk
              have hk' : k < N + 1 - N₀ := Finset.mem_range.1 hk
              congr 1
              omega
            rw [hrefl]
            have hθ1' : θ ≠ 1 := ne_of_lt hθ1
            rw [geom_sum_eq hθ1']
            have hnn : (0 : ℝ) ≤ θ ^ (N + 1 - N₀) := by positivity
            have h1mθ : (0 : ℝ) < 1 - θ := by linarith
            have heq : (θ ^ (N + 1 - N₀) - 1) / (θ - 1) =
                (1 - θ ^ (N + 1 - N₀)) / (1 - θ) := by
              have e1 : θ ^ (N + 1 - N₀) - 1 = -(1 - θ ^ (N + 1 - N₀)) := by ring
              have e2 : θ - 1 = -(1 - θ) := by ring
              rw [e1, e2, neg_div_neg_eq]
            rw [heq, div_le_div_iff_of_pos_right h1mθ]
            linarith
    calc (∏ n ∈ Finset.range N₀, (a n : ℝ)) *
          ∏ k ∈ Finset.range (N + 1 - N₀), (a (N₀ + k) : ℝ)
        ≤ (a N₀ : ℝ) ^ N₀ * (K ^ (N + 1 - N₀) * (a N : ℝ) ^ (1 / (1 - θ))) :=
          mul_le_mul hf1 hf2 (by positivity) (by positivity)
    _ ≤ ((a N₀ : ℝ) ^ N₀ * K) ^ (N + 1) * (a N : ℝ) ^ (1 / (1 - θ)) := by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
          rw [mul_pow]
          have hb : (1 : ℝ) ≤ (a N₀ : ℝ) ^ N₀ := one_le_pow₀ (by exact_mod_cast hapos N₀)
          have h1 : (a N₀ : ℝ) ^ N₀ ≤ ((a N₀ : ℝ) ^ N₀) ^ (N + 1) := by
            nth_rewrite 1 [← pow_one ((a N₀ : ℝ) ^ N₀)]
            exact pow_le_pow_right₀ hb (by omega : 1 ≤ N + 1)
          exact mul_le_mul h1 (pow_le_pow_right₀ hK1 (by omega : N + 1 - N₀ ≤ N + 1))
            (pow_nonneg (by linarith [hK1]) _) (by positivity)
  refine ⟨(a N₀ : ℝ) ^ N₀ * K, ?_, eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩⟩
  · have hb : (1 : ℝ) ≤ (a N₀ : ℝ) ^ N₀ := one_le_pow₀ (by exact_mod_cast hapos N₀)
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
    _ ≤ (a N₀ : ℝ) ^ N₀ * K := mul_le_mul hb hK1 (by norm_num) (by positivity)
  · rw [← hσid]
    exact key N hN

/-! ### The beat lemma: doubly-exponential growth beats any geometric factor -/

/-- From the quadratic step, `a_N ≥ 2^{2^{N-M}}`; hence for ANY constant
`D ≥ 1` and any `η > 0`, eventually `D^{N+1} ≤ a_N^η`. -/
lemma eventually_pow_le_rpow (hapos : ∀ n, 0 < a n) (hmono : StrictMono a)
    (hsq : ∀ᶠ n in atTop, (a n : ℝ) ^ 2 ≤ (a (n + 1) : ℝ))
    {D : ℝ} (hD : 1 ≤ D) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N in atTop, D ^ (N + 1) ≤ (a N : ℝ) ^ η := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hsq
  set M := max M₀ 1 with hMdef
  have hM2 : 2 ≤ a M := by
    have h1 : a 1 ≥ 2 := by
      have h01 := hmono (by norm_num : (0 : ℕ) < 1)
      have hp0 := hapos 0
      omega
    have h2 : a 1 ≤ a M := hmono.monotone (by omega)
    omega
  have hMsq : ∀ m ≥ M, (a m : ℝ) ^ 2 ≤ (a (m + 1) : ℝ) := fun m hm => hM₀ m (by omega)
  have hgrow : ∀ N ≥ M, (2 : ℝ) ^ (2 ^ (N - M)) ≤ (a N : ℝ) := by
    intro N hN
    have h := pow_growth hapos hMsq (N - M)
    have h2 : M + (N - M) = N := by omega
    rw [h2] at h
    exact le_trans (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by exact_mod_cast hM2 : (2 : ℝ) ≤ a M) _) h
  obtain ⟨d₀, hd₀⟩ := exists_nat_gt D
  set d := max d₀ 1 with hddef
  have hDd : D ≤ (2 : ℝ) ^ d := by
    have h1 : D < (d₀ : ℝ) := hd₀
    have h2n : d₀ ≤ 2 ^ d₀ := Nat.le_of_lt Nat.lt_two_pow_self
    have h2 : (d₀ : ℝ) ≤ (2 : ℝ) ^ d₀ := by exact_mod_cast h2n
    have h3 : (2 : ℝ) ^ d₀ ≤ (2 : ℝ) ^ d :=
      pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    linarith
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1
    (two_pow_eventually_dominates ((d : ℝ) * (2 ^ M) / η))
  refine eventually_atTop.2 ⟨max M n₁, fun N hN => ?_⟩
  have hNM : M ≤ N := le_trans (le_max_left _ _) hN
  have hNn : n₁ ≤ N := le_trans (le_max_right _ _) hN
  have h2M : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  have hexp : ((N : ℝ) + 1) * (d : ℝ) ≤ (2 : ℝ) ^ (N - M) * η := by
    have h1 := hn₁ N hNn
    have h2 : (2 : ℝ) ^ N = (2 : ℝ) ^ (N - M) * (2 : ℝ) ^ M := by
      rw [← pow_add]
      congr 1
      omega
    calc ((N : ℝ) + 1) * (d : ℝ)
        = ((N : ℝ) + 1) * ((d : ℝ) * (2 ^ M) / η) * (η / (2 ^ M)) := by
          field_simp [hη.ne', h2M.ne']
      _ ≤ (2 : ℝ) ^ N * (η / (2 ^ M)) :=
          mul_le_mul_nn_right h1 (div_nonneg hη.le (by positivity))
      _ = (2 : ℝ) ^ (N - M) * η := by
          rw [h2]
          field_simp [h2M.ne']
  calc D ^ (N + 1) ≤ ((2 : ℝ) ^ d) ^ (N + 1) :=
        pow_le_pow_left₀ (by linarith [hD] : (0 : ℝ) ≤ D) hDd _
  _ = (2 : ℝ) ^ (d * (N + 1)) := by rw [pow_mul]
  _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (N - M) * η) := by
        rw [← Real.rpow_natCast (2 : ℝ) (d * (N + 1))]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        push_cast
        linarith [hexp]
  _ = ((2 : ℝ) ^ (2 ^ (N - M))) ^ η := by
        rw [← Real.rpow_natCast (2 : ℝ) (2 ^ (N - M)),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        push_cast
        ring
  _ ≤ (a N : ℝ) ^ η :=
        Real.rpow_le_rpow (by positivity) (hgrow N hNM) hη.le

/-! ### The b-side: comparison from `b_n / a_n → 1` -/

/-- From `b_n/a_n → 1`, eventually `a_n/2 ≤ b_n ≤ 2a_n`. -/
lemma eventually_b_bounds (hapos : ∀ n, 0 < a n) {b : ℕ → ℕ}
    (hlim : Tendsto (fun n => (b n : ℝ) / (a n : ℝ)) atTop (𝓝 1)) :
    (∀ᶠ n in atTop, (a n : ℝ) / 2 ≤ (b n : ℝ)) ∧
      (∀ᶠ n in atTop, (b n : ℝ) ≤ 2 * (a n : ℝ)) := by
  have h := (Metric.tendsto_nhds.1 hlim) (1 / 2) (by norm_num)
  have h2 : ∀ᶠ n in atTop, |(b n : ℝ) / (a n : ℝ) - 1| < 1 / 2 := by
    filter_upwards [h] with n hn
    rwa [Real.dist_eq] at hn
  have hpos : ∀ n, (0 : ℝ) < a n := fun n => by exact_mod_cast hapos n
  refine ⟨?_, ?_⟩ <;> filter_upwards [h2] with n hn
  · have h3 : (1 : ℝ) / 2 < (b n : ℝ) / (a n : ℝ) := by
      have := abs_lt.1 hn
      linarith
    rw [lt_div_iff₀ (hpos n)] at h3
    linarith [h3]
  · have h3 : (b n : ℝ) / (a n : ℝ) < 3 / 2 := by
      have := abs_lt.1 hn
      linarith
    rw [div_lt_iff₀ (hpos n)] at h3
    linarith [h3]

/-- Summability of `∑ 1/b_n` by comparison with `2/a_n`. -/
lemma summable_one_div_b (hapos : ∀ n, 0 < a n) {b : ℕ → ℕ} (_hbpos : ∀ n, 0 < b n)
    (hsuma : Summable (fun n => 1 / (a n : ℝ)))
    (hlim : Tendsto (fun n => (b n : ℝ) / (a n : ℝ)) atTop (𝓝 1)) :
    Summable (fun n => 1 / (b n : ℝ)) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (eventually_b_bounds hapos hlim).1
  have hterm : ∀ k : ℕ, (1 / (b (k + N₁) : ℝ)) ≤ 2 * (1 / (a (k + N₁) : ℝ)) := by
    intro k
    have h1 := hN₁ (k + N₁) (Nat.le_add_left N₁ k)
    have ha0 : (0 : ℝ) < a (k + N₁) := by exact_mod_cast hapos _
    calc (1 / (b (k + N₁) : ℝ)) ≤ 1 / ((a (k + N₁) : ℝ) / 2) :=
          one_div_le_one_div_of_le (by linarith [ha0]) h1
    _ = 2 * (1 / (a (k + N₁) : ℝ)) := by rw [one_div_div, mul_one_div]
  have hsumm : Summable (fun k : ℕ => 1 / (b (k + N₁) : ℝ)) := by
    apply Summable.of_nonneg_of_le (f := fun k : ℕ => 2 * (1 / (a (k + N₁) : ℝ)))
    · intro k; exact one_div_nonneg.mpr (by positivity)
    · exact hterm
    · exact (((_root_.summable_nat_add_iff N₁).2 hsuma).mul_left 2)
  exact (summable_nat_add_iff N₁).1 hsumm

/-- The b-tail is at most twice the a-tail. -/
lemma tail_b_le_two_tail_a (hapos : ∀ n, 0 < a n) {b : ℕ → ℕ}
    (hsuma : Summable (fun n => 1 / (a n : ℝ)))
    (hsumb : Summable (fun n => 1 / (b n : ℝ))) {N₁ : ℕ}
    (hbge : ∀ n ≥ N₁, (a n : ℝ) / 2 ≤ (b n : ℝ)) (N : ℕ) (hN : N₁ ≤ N + 1) :
    ∑' i, (1 / (b (i + (N + 1)) : ℝ)) ≤ 2 * ∑' i, (1 / (a (i + (N + 1)) : ℝ)) := by
  have hterm : ∀ i : ℕ, (1 / (b (i + (N + 1)) : ℝ)) ≤
      2 * (1 / (a (i + (N + 1)) : ℝ)) := by
    intro i
    have h1 := hbge (i + (N + 1)) (by omega)
    have ha0 : (0 : ℝ) < a (i + (N + 1)) := by exact_mod_cast hapos _
    calc (1 / (b (i + (N + 1)) : ℝ)) ≤ 1 / ((a (i + (N + 1)) : ℝ) / 2) :=
          one_div_le_one_div_of_le (by linarith [ha0]) h1
    _ = 2 * (1 / (a (i + (N + 1)) : ℝ)) := by rw [one_div_div, mul_one_div]
  have hsb : Summable (fun i : ℕ => 1 / (b (i + (N + 1)) : ℝ)) :=
    (_root_.summable_nat_add_iff (N + 1)).2 hsumb
  have hsa : Summable (fun i : ℕ => 2 * (1 / (a (i + (N + 1)) : ℝ))) :=
    (((_root_.summable_nat_add_iff (N + 1)).2 hsuma).mul_left 2)
  have hle := Summable.tsum_le_tsum hterm hsb hsa
  rwa [tsum_mul_left] at hle

/-- The b-tail is strictly positive. -/
lemma tail_b_pos {b : ℕ → ℕ} (hbpos : ∀ n, 0 < b n)
    (hsumb : Summable (fun n => 1 / (b n : ℝ))) (N : ℕ) :
    (0 : ℝ) < ∑' i, (1 / (b (i + (N + 1)) : ℝ)) := by
  have hsumm : Summable (fun i : ℕ => 1 / (b (i + (N + 1)) : ℝ)) :=
    (_root_.summable_nat_add_iff (N + 1)).2 hsumb
  have h := Summable.tsum_lt_tsum_of_nonneg (f := fun _ : ℕ => (0 : ℝ))
    (g := fun i : ℕ => (1 / (b (i + (N + 1)) : ℝ))) (i := 0)
    (fun _ => le_refl _) (fun i => one_div_nonneg.mpr (by positivity))
    (one_div_pos.mpr (by exact_mod_cast hbpos (0 + (N + 1)))) hsumm
  simpa using h

/-! ### The integrality machine -/

/-- If `∑ 1/b_n = r ∈ ℚ`, then `q·P_N·T_N ∈ ℤ` where `q = r.den`,
`P_N = ∏_{n ≤ N} b_n` and `T_N` is the tail. -/
lemma key_integrality {b : ℕ → ℕ} (hbpos : ∀ n, 0 < b n)
    (hsumb : Summable (fun n => 1 / (b n : ℝ))) (r : ℚ)
    (hr : (r : ℝ) = ∑' n, 1 / (b n : ℝ)) (N : ℕ) :
    ∃ z : ℤ, (z : ℝ) = (r.den : ℝ) * (∏ n ∈ Finset.range (N + 1), (b n : ℝ)) *
      (∑' i, 1 / (b (i + (N + 1)) : ℝ)) := by
  set P : ℕ := ∏ n ∈ Finset.range (N + 1), b n with hPdef
  have hdiv : ∀ n ∈ Finset.range (N + 1), b n ∣ P := fun n hn => dvd_prod_of_mem b hn
  set K : ℕ → ℕ := fun n => P / b n with hKdef
  have hcast : ∀ n ∈ Finset.range (N + 1), ((K n : ℕ) : ℝ) = (P : ℝ) / (b n : ℝ) := by
    intro n hn
    rw [hKdef]
    exact Nat.cast_div (hdiv n hn) (by exact_mod_cast (hbpos n).ne')
  have hq0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hsplit : (∑ n ∈ Finset.range (N + 1), (1 / (b n : ℝ))) +
      ∑' i, (1 / (b (i + (N + 1)) : ℝ)) = ∑' n, 1 / (b n : ℝ) :=
    hsumb.sum_add_tsum_nat_add (N + 1)
  have htail : (∑' i, (1 / (b (i + (N + 1)) : ℝ))) =
      (r : ℝ) - ∑ n ∈ Finset.range (N + 1), (1 / (b n : ℝ)) := by
    rw [← hr] at hsplit
    linarith
  have hqr : (r.den : ℝ) * (r : ℝ) = (r.num : ℝ) := by
    have hrpq : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
      conv_lhs => rw [← Rat.num_div_den r]
      exact Rat.cast_div _ _
    have hqne : (r.den : ℝ) ≠ 0 := ne_of_gt hq0
    rw [hrpq]
    field_simp [hqne]
  have hpart : (P : ℝ) * (∑ n ∈ Finset.range (N + 1), (1 / (b n : ℝ))) =
      ∑ n ∈ Finset.range (N + 1), (K n : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [mul_one_div, ← hcast n hn]
  refine ⟨(r.num : ℤ) * (P : ℤ) - (r.den : ℤ) * ∑ n ∈ Finset.range (N + 1), (K n : ℤ), ?_⟩
  push_cast
  rw [← Nat.cast_prod, ← hPdef, htail, mul_sub, mul_right_comm _ _ (r : ℝ), hqr,
    mul_assoc, hpart]

/-! ### The folklore criterion -/

/-- **The folklore criterion:** if `a` is a strictly increasing sequence of
positive integers and `liminf a_{n+1}/a_n^{2+ε} > 0` for some `ε > 0`
(unpacked as `c·a_n^{2+ε} ≤ a_{n+1}` eventually), then `a` is an
irrationality sequence: for EVERY positive `b` with `b_n/a_n → 1`,
`∑' 1/b_n` is irrational. This is the criterion stated on
erdosproblems.com/263 (fetched 2026-08-01), which the site derives from the
folklore result on `lim a_n^{1/2^n} = ∞`. -/
theorem folklore_criterion (hapos : ∀ n, 0 < a n) (hmono : StrictMono a)
    {ε : ℝ} (hε : 0 < ε) {c : ℝ} (hc : 0 < c)
    (hgrowth : ∀ᶠ n in atTop, c * (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ)) :
    IsIrrationalitySequence a := by
  have h2ε : (0 : ℝ) < 2 + ε := by linarith
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  refine ⟨hapos, hmono, ?_⟩
  intro b hbpos hlim
  have hsuma : Summable (fun n => 1 / (a n : ℝ)) :=
    summable_one_div_of_growth hapos hmono hε hc hgrowth
  have hsumb : Summable (fun n => 1 / (b n : ℝ)) :=
    summable_one_div_b hapos hbpos hsuma hlim
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (eventually_sq_le hapos hmono hε hc hgrowth)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hgrowth
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (eventually_b_bounds hapos hlim).1
  obtain ⟨N₁', hN₁'⟩ := eventually_atTop.1 (eventually_b_bounds hapos hlim).2
  set M := max (max (max N₂ N₀) N₁) (max N₁' 1) with hMdef
  have hM2 : 2 ≤ a M := by
    have h1 : a 1 ≥ 2 := by
      have h01 := hmono (by norm_num : (0 : ℕ) < 1)
      have hp0 := hapos 0
      omega
    have h2 : a 1 ≤ a M := hmono.monotone (by omega)
    omega
  have hMsq : ∀ m ≥ M, (a m : ℝ) ^ 2 ≤ (a (m + 1) : ℝ) := fun m hm => hN₂ m (by omega)
  have hMgrow : ∀ m ≥ M, c * (a m : ℝ) ^ (2 + ε) ≤ (a (m + 1) : ℝ) :=
    fun m hm => hN₀ m (by omega)
  have hMb : ∀ n ≥ M, (a n : ℝ) / 2 ≤ (b n : ℝ) := fun n hn => hN₁ n (by omega)
  have hMb2 : ∀ n ≥ M, (b n : ℝ) ≤ 2 * (a n : ℝ) := fun n hn => hN₁' n (by omega)
  obtain ⟨C, hC1, hC⟩ := prod_bound hapos hmono hε hc hgrowth
  set δ : ℝ := (2 + ε) * ε / (1 + ε) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    exact div_pos (mul_pos h2ε hε) h1ε
  have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ
  have hσδ : (2 + ε) / (1 + ε) - (2 + ε) = -δ := by
    rw [hδdef]
    field_simp [h1ε.ne']
    ring
  have hbeat : ∀ᶠ N in atTop, (2 * C) ^ (N + 1) ≤ (a N : ℝ) ^ (δ / 2) :=
    eventually_pow_le_rpow hapos hmono (eventually_sq_le hapos hmono hε hc hgrowth)
      (by linarith [hC1] : (1 : ℝ) ≤ 2 * C) hδ2
  -- by contradiction: assume the total is rational
  rintro ⟨r, hr⟩
  have hbig : ∀ᶠ N in atTop,
      (4 * (r.den : ℝ) * (∏ n ∈ Finset.range M, (b n : ℝ)) / c) <
        (a N : ℝ) ^ (δ / 2) := by
    have ht : Tendsto (fun n => (a n : ℝ) ^ (δ / 2)) atTop atTop :=
      (tendsto_rpow_atTop hδ2).comp (tendsto_atTop_of_strictMono hmono)
    exact ht.eventually_gt_atTop _
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 ((hC.and hbeat).and hbig)
  set N := max M N₃ with hNdef
  have hNM : M ≤ N := le_max_left _ _
  have hNN₃ : N₃ ≤ N := le_max_right _ _
  obtain ⟨⟨hPN, hbeatN⟩, hbigN⟩ := hN₃ N hNN₃
  obtain ⟨z, hz⟩ := key_integrality hbpos hsumb r hr N
  have hq0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hPpos : (0 : ℝ) < ∏ n ∈ Finset.range (N + 1), (b n : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hbpos i)
  have hTpos : (0 : ℝ) < ∑' i, (1 / (b (i + (N + 1)) : ℝ)) :=
    tail_b_pos hbpos hsumb N
  have hz_pos : (0 : ℝ) < (z : ℝ) := by
    rw [hz]
    exact mul_pos (mul_pos hq0 hPpos) hTpos
  have hA0 : (0 : ℝ) < (a N : ℝ) := by exact_mod_cast hapos N
  have hN2 : 2 ≤ a N := by
    have hle : a M ≤ a N := hmono.monotone hNM
    omega
  have hNsq : ∀ m ≥ N, (a m : ℝ) ^ 2 ≤ (a (m + 1) : ℝ) := fun m hm => hMsq m (by omega)
  have hTail : ∑' i, (1 / (b (i + (N + 1)) : ℝ)) ≤
      4 / (c * (a N : ℝ) ^ (2 + ε)) := by
    have h1 : ∑' i, (1 / (b (i + (N + 1)) : ℝ)) ≤
        2 * ∑' i, (1 / (a (i + (N + 1)) : ℝ)) :=
      tail_b_le_two_tail_a hapos hsuma hsumb hMb N (by omega)
    have h2 : ∑' i, (1 / (a (i + (N + 1)) : ℝ)) ≤ 2 / (a (N + 1) : ℝ) :=
      tail_le_two_div hapos hN2 hNsq
    have hgrowN := hMgrow N hNM
    have hpos1 : (0 : ℝ) < (a (N + 1) : ℝ) := by exact_mod_cast hapos (N + 1)
    have hpos2 : (0 : ℝ) < c * (a N : ℝ) ^ (2 + ε) :=
      mul_pos hc (Real.rpow_pos_of_pos hA0 _)
    have h3 : 1 / (a (N + 1) : ℝ) ≤ 1 / (c * (a N : ℝ) ^ (2 + ε)) :=
      one_div_le_one_div_of_le hpos2 hgrowN
    calc ∑' i, (1 / (b (i + (N + 1)) : ℝ)) ≤ 2 * (2 / (a (N + 1) : ℝ)) :=
          le_trans h1 (mul_le_mul_nn_left h2 (by norm_num))
    _ = 4 * (1 / (a (N + 1) : ℝ)) := by ring
    _ ≤ 4 * (1 / (c * (a N : ℝ) ^ (2 + ε))) :=
          mul_le_mul_nn_left h3 (by norm_num)
    _ = 4 / (c * (a N : ℝ) ^ (2 + ε)) := by ring
  have hPb : (∏ n ∈ Finset.range (N + 1), (b n : ℝ)) ≤
      (∏ n ∈ Finset.range M, (b n : ℝ)) * (2 ^ (N + 1) *
        ∏ n ∈ Finset.range (N + 1), (a n : ℝ)) := by
    have hsplitN : N + 1 = M + (N + 1 - M) := by omega
    nth_rewrite 1 [hsplitN]
    rw [Finset.prod_range_add]
    apply mul_le_mul_nn_left _ (by positivity)
    calc (∏ k ∈ Finset.range (N + 1 - M), (b (M + k) : ℝ))
        ≤ ∏ k ∈ Finset.range (N + 1 - M), (2 * (a (M + k) : ℝ)) :=
          Finset.prod_le_prod (fun i _ => by exact_mod_cast (hbpos _).le)
            (fun i hi => hMb2 (M + i) (by omega))
    _ = 2 ^ (N + 1 - M) * ∏ k ∈ Finset.range (N + 1 - M), (a (M + k) : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ ≤ 2 ^ (N + 1) * ∏ n ∈ Finset.range (N + 1), (a n : ℝ) := by
          have hsub : (∏ k ∈ Finset.range (N + 1 - M), (a (M + k) : ℝ)) ≤
              ∏ n ∈ Finset.range (N + 1), (a n : ℝ) := by
            nth_rewrite 2 [hsplitN]
            rw [Finset.prod_range_add]
            apply le_mul_of_one_le_left_nn (by positivity)
            calc (1 : ℝ) = ∏ _i ∈ Finset.range M, (1 : ℝ) := by rw [Finset.prod_const_one]
            _ ≤ ∏ i ∈ Finset.range M, (a i : ℝ) :=
                Finset.prod_le_prod (fun i _ => by norm_num)
                  (fun i _ => by exact_mod_cast hapos i)
          exact mul_le_mul
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) hsub
            (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
            (pow_nonneg (by norm_num) _)
  have hlt : (z : ℝ) < 1 := by
    rw [hz]
    have hCa : (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) ≤
        C ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε)) := hPN
    have h2Ca : 2 ^ (N + 1) * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) ≤
        2 ^ (N + 1) * (C ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε))) :=
      mul_le_mul_nn_left hCa (pow_nonneg (by norm_num) _)
    have h3Ca : (∏ n ∈ Finset.range M, (b n : ℝ)) * (2 ^ (N + 1) *
        ∏ n ∈ Finset.range (N + 1), (a n : ℝ)) ≤
        (∏ n ∈ Finset.range M, (b n : ℝ)) * (2 ^ (N + 1) *
          (C ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε)))) :=
      mul_le_mul_nn_left h2Ca (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
    have hfirst : (r.den : ℝ) * (∏ n ∈ Finset.range (N + 1), (b n : ℝ)) ≤
        (r.den : ℝ) * ((∏ n ∈ Finset.range M, (b n : ℝ)) * (2 ^ (N + 1) *
          (C ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε))))) :=
      mul_le_mul_nn_left (le_trans hPb h3Ca) hq0.le
    have hbig0 : (0 : ℝ) ≤ (∏ n ∈ Finset.range M, (b n : ℝ)) * (2 ^ (N + 1) *
        (C ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε)))) :=
      mul_nonneg (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
        (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (pow_nonneg (by linarith [hC1]) _)
            (Real.rpow_nonneg (by positivity) _)))
    have hstep1 : (r.den : ℝ) * (∏ n ∈ Finset.range (N + 1), (b n : ℝ)) *
        (∑' i, (1 / (b (i + (N + 1)) : ℝ))) ≤
        (r.den : ℝ) * ((∏ n ∈ Finset.range M, (b n : ℝ)) * (2 ^ (N + 1) *
          (C ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε))))) *
          (4 / (c * (a N : ℝ) ^ (2 + ε))) :=
      mul_le_mul hfirst hTail hTpos.le (mul_nonneg hq0.le hbig0)
    apply lt_of_le_of_lt hstep1
    have hmerge : (a N : ℝ) ^ ((2 + ε) / (1 + ε)) / (a N : ℝ) ^ (2 + ε) =
        (a N : ℝ) ^ (-δ) := by
      rw [← Real.rpow_sub hA0, hσδ]
    have h1 : (a N : ℝ) ^ (2 + ε) ≠ 0 := (Real.rpow_pos_of_pos hA0 _).ne'
    have h2 : c ≠ 0 := hc.ne'
    have hpow : (2 : ℝ) ^ (N + 1) * (C ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε))) =
        (2 * C) ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε)) := by
      rw [mul_pow]
      ring
    have heq : (r.den : ℝ) * ((∏ n ∈ Finset.range M, (b n : ℝ)) * (2 ^ (N + 1) *
          (C ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε))))) *
          (4 / (c * (a N : ℝ) ^ (2 + ε))) =
        (4 * (r.den : ℝ) * (∏ n ∈ Finset.range M, (b n : ℝ)) / c) *
          ((2 * C) ^ (N + 1)) * ((a N : ℝ) ^ (-δ)) := by
      rw [hpow]
      rw [show (r.den : ℝ) * ((∏ n ∈ Finset.range M, (b n : ℝ)) *
            ((2 * C) ^ (N + 1) * (a N : ℝ) ^ ((2 + ε) / (1 + ε)))) *
            (4 / (c * (a N : ℝ) ^ (2 + ε))) =
          ((4 * (r.den : ℝ) * (∏ n ∈ Finset.range M, (b n : ℝ)) / c) *
            ((2 * C) ^ (N + 1))) *
            ((a N : ℝ) ^ ((2 + ε) / (1 + ε)) / (a N : ℝ) ^ (2 + ε)) from by
        field_simp [h1, h2]]
      rw [hmerge]
    rw [heq]
    have hK0 : (0 : ℝ) < (a N : ℝ) ^ (δ / 2) := Real.rpow_pos_of_pos hA0 _
    have hcb0 : (0 : ℝ) ≤ 4 * (r.den : ℝ) * (∏ n ∈ Finset.range M, (b n : ℝ)) / c := by
      apply div_nonneg _ hc.le
      apply mul_nonneg (mul_nonneg (by norm_num) hq0.le)
      exact Finset.prod_nonneg (fun i _ => by exact_mod_cast (hbpos i).le)
    calc (4 * (r.den : ℝ) * (∏ n ∈ Finset.range M, (b n : ℝ)) / c) *
            ((2 * C) ^ (N + 1)) * ((a N : ℝ) ^ (-δ))
        < (a N : ℝ) ^ (δ / 2) * (a N : ℝ) ^ (δ / 2) * (a N : ℝ) ^ (-δ) := by
          apply mul_lt_mul_pos_right _ (Real.rpow_pos_of_pos hA0 _)
          have hXB : (4 * (r.den : ℝ) * (∏ n ∈ Finset.range M, (b n : ℝ)) / c) *
              ((2 * C) ^ (N + 1)) ≤
              (4 * (r.den : ℝ) * (∏ n ∈ Finset.range M, (b n : ℝ)) / c) *
              ((a N : ℝ) ^ (δ / 2)) :=
            mul_le_mul_nn_left hbeatN hcb0
          have hAB : (4 * (r.den : ℝ) * (∏ n ∈ Finset.range M, (b n : ℝ)) / c) *
              ((a N : ℝ) ^ (δ / 2)) <
              (a N : ℝ) ^ (δ / 2) * (a N : ℝ) ^ (δ / 2) :=
            mul_lt_mul_pos_right hbigN hK0
          exact lt_of_le_of_lt hXB hAB
    _ = (a N : ℝ) ^ (δ / 2 + δ / 2 + -δ) := by
          rw [← Real.rpow_add hA0, ← Real.rpow_add hA0]
    _ = 1 := by
          have h0 : δ / 2 + δ / 2 + -δ = (0 : ℝ) := by ring
          rw [h0, Real.rpow_zero]
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hz_pos
  have hz1 : z < 1 := by
    have h2 : (z : ℝ) < ((1 : ℤ) : ℝ) := by
      rw [Int.cast_one]
      exact hlt
    exact Int.cast_lt.mp h2
  omega

end Erdos263
