/-
Erdős Problem #263 — Erdős 1975 route, SESSION 2: threshold-`B` machinery.

Builds on `Erdos1975.lean` (run-4 session 1). What this file actually is
(after the session-2 audit-fix):

* `eventually_rpow_ge_of_oneSidedGrowth` — the threshold-`B` form of O2:
  for `0 ≤ B`, eventually `B^{2^n} ≤ a_n`.
* `tail_le_of_ge_rpow` — if `a_i ≥ B^{2^i}` for all `i ≥ M+1` with
  `2 ≤ B`, then `T_M ≤ 2·(1/B)^{2^{M+1}}` (crude doubly-exponential tail
  bound, monotone-free).
* `le_rpow_self` — `x ≤ l^x` for `2 ≤ l`, `0 ≤ x`.
* `rpow_root_two_pow_self` — `((a_n)^{1/2^n})^{2^n} = a_n`.
* `sum_range_two_pow` — `∑_{j≤k} 2^j = 2^{k+1} - 1` (ℕ).
* `prod_le_of_near_record` — the product bound at a (1−1/(k+1)²)-record
  (session 3; INTERIM sign — the paper's (14) is (1+1/k²) PLUS slack, see
  `erdos1975_eq10-25_transcription.md` and `Erdos1975D.lean` for the
  corrected escape-record machinery).

The session-2 case-split WORK is elsewhere: case (9) is CLOSED in
`Erdos1975C.lean` (`irrational_of_monotone_growth_and_spike`, under
`Monotone a`); case (10) is OPEN — see the SESSION-2 WALL comment below
(the `P_k ≤ l^{c·2^k}` induction was machine-refuted; the cap yields only
Erdős's (11) tower, and the tower fight needs the paper's (13)–(17)).

MONOTONICITY ANSWER (definitive, see PROGRESS-onesided.md): the recurrence,
integrality, and the crude tail bounds are monotone-free; the spike case
(9) is the unique place where the paper's argument anchors a tail bound at
`n_{k+1}` via order.

ZERO sorry/admit/axiom in this file.
-/
import Mathlib
import Erdos263.Erdos1975

open Filter Topology Finset
open scoped Topology

namespace Erdos263

variable {a : ℕ → ℕ}

/-! ### The doubly-exponential tail bound at an arbitrary threshold -/

/-- One-sided growth at threshold `B`: eventually `B^{2^n} ≤ a_n`
(generalization of `eventually_ge_of_oneSidedGrowth`, which is `B = 2`). -/
lemma eventually_rpow_ge_of_oneSidedGrowth (hg : OneSidedGrowth a) (B : ℝ)
    (hB : 0 ≤ B) :
    ∀ᶠ n in atTop, B ^ (2 ^ n) ≤ (a n : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := (tendsto_atTop_atTop.1 hg.2) (max B 0)
  refine eventually_atTop.2 ⟨N₀, fun n hn => ?_⟩
  have hbase : (0 : ℝ) ≤ (a n : ℝ) := by positivity
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hu : max B 0 ≤ (a n : ℝ) ^ (1 / (2 : ℝ) ^ n) := hN₀ n hn
  have hB0 : (0 : ℝ) ≤ B := hB
  have key : ((a n : ℝ) ^ (1 / (2 : ℝ) ^ n)) ^ (2 ^ n) = (a n : ℝ) := by
    have hcast : (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ n := by push_cast; rfl
    rw [← Real.rpow_natCast (((a n : ℝ) ^ (1 / (2 : ℝ) ^ n))) (2 ^ n), hcast,
      ← Real.rpow_mul hbase]
    have hmul : (1 / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = 1 := div_mul_cancel₀ (1 : ℝ) h2n.ne'
    rw [hmul, Real.rpow_one]
  have hle : (max B 0) ^ (2 ^ n) ≤ (a n : ℝ) :=
    key ▸ pow_le_pow_left₀ (le_max_right _ _) hu (2 ^ n)
  have hle' : B ^ (2 ^ n) ≤ (max B 0) ^ (2 ^ n) :=
    pow_le_pow_left₀ hB0 (le_max_left _ _) _
  exact le_trans hle' hle

/-- **Tail bound at threshold `B`:** if `B^{2^i} ≤ a_i` for all `i ≥ M+1`
with `2 ≤ B`, then `T_M ≤ 2·(1/B)^{2^{M+1}}`. -/
lemma tail_le_of_ge_rpow (_hapos : ∀ n, 0 < a n)
    (hsum : Summable (fun n => 1 / (a n : ℝ))) {B : ℝ} (hB : 2 ≤ B) {M : ℕ}
    (hge : ∀ i ≥ M + 1, B ^ (2 ^ i) ≤ (a i : ℝ)) :
    (∑' i, 1 / (a (i + (M + 1)) : ℝ)) ≤ 2 * (1 / B) ^ (2 ^ (M + 1)) := by
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hterm : ∀ i : ℕ, (1 / (a (i + (M + 1)) : ℝ)) ≤
      (1 / B : ℝ) ^ (2 ^ (M + 1)) * (1 / B : ℝ) ^ i := by
    intro i
    have hexp : (2 : ℕ) ^ (M + 1) + i ≤ 2 ^ (i + (M + 1)) := by
      calc (2 : ℕ) ^ (M + 1) + i
          ≤ (2 : ℕ) ^ (M + 1) + (2 : ℕ) ^ (M + 1) * i := by
            have h3 : i ≤ 2 ^ (M + 1) * i := by
              calc i = 1 * i := by rw [one_mul]
                _ ≤ 2 ^ (M + 1) * i := by
                      gcongr
                      exact Nat.one_le_two_pow
            omega
        _ = (2 : ℕ) ^ (M + 1) * (i + 1) := by ring
        _ ≤ (2 : ℕ) ^ (M + 1) * (2 : ℕ) ^ i := by
              gcongr
              exact two_pow_ge_succ i
        _ = (2 : ℕ) ^ (i + (M + 1)) := by
              rw [pow_add]
              ring
    have hpow : B ^ (2 ^ (M + 1) + i) ≤ (a (i + (M + 1)) : ℝ) := by
      have h1 := hge (i + (M + 1)) (by omega)
      have h2 : B ^ (2 ^ (M + 1) + i) ≤ B ^ (2 ^ (i + (M + 1))) :=
        pow_le_pow_right₀ hB1 (by exact_mod_cast hexp)
      exact le_trans h2 h1
    calc (1 / (a (i + (M + 1)) : ℝ)) ≤ 1 / B ^ (2 ^ (M + 1) + i) :=
          one_div_le_one_div_of_le (pow_pos (by linarith) _) hpow
      _ = (1 / B : ℝ) ^ (2 ^ (M + 1) + i) := by rw [div_pow, one_pow]
      _ = (1 / B : ℝ) ^ (2 ^ (M + 1)) * (1 / B : ℝ) ^ i := by rw [pow_add]
  have hlsumm : Summable (fun i : ℕ => 1 / (a (i + (M + 1)) : ℝ)) :=
    (_root_.summable_nat_add_iff (M + 1)).2 hsum
  have hgsumm : Summable (fun i : ℕ => (1 / B : ℝ) ^ (2 ^ (M + 1)) * (1 / B : ℝ) ^ i) :=
    ((summable_geometric_of_lt_one (by positivity)
      ((div_lt_one (by linarith : (0 : ℝ) < B)).mpr (by linarith))).mul_left _)
  have hle := Summable.tsum_le_tsum hterm hlsumm hgsumm
  have hsum2 : (∑' i : ℕ, (1 / B : ℝ) ^ (2 ^ (M + 1)) * (1 / B : ℝ) ^ i) ≤
      2 * (1 / B : ℝ) ^ (2 ^ (M + 1)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity)
      ((div_lt_one (by linarith : (0 : ℝ) < B)).mpr (by linarith)), inv_eq_one_div]
    have h1B : (0 : ℝ) < 1 / B := by positivity
    have h1B1 : (1 : ℝ) / B ≤ 1 / 2 :=
      (div_le_div_iff_of_pos_left (by norm_num) (by linarith) (by norm_num)).mpr hB
    have h3 : (1 : ℝ) / (1 - 1 / B) ≤ 2 := by
      rw [div_le_iff₀ (by linarith [h1B1] : (0 : ℝ) < 1 - 1 / B)]
      linarith [h1B1]
    calc (1 / B : ℝ) ^ (2 ^ (M + 1)) * (1 / (1 - 1 / B))
        ≤ (1 / B : ℝ) ^ (2 ^ (M + 1)) * 2 :=
          mul_le_mul_of_nonneg_left h3 (pow_nonneg (by positivity) _)
      _ = 2 * (1 / B : ℝ) ^ (2 ^ (M + 1)) := by ring
  exact le_trans hle hsum2

/-! ### The cap induction: `P_k ≤ l^{c·2^k}` -/

/-- Auxiliary: `x ≤ l^x` for `2 ≤ l` and `0 ≤ x`. -/
lemma le_rpow_self {l : ℝ} (hl : 2 ≤ l) (x : ℝ) (hx : 0 ≤ x) : x ≤ l ^ x := by
  have hl1 : (1 : ℝ) ≤ l := by linarith
  by_cases hx1 : x ≤ 1
  · calc x ≤ 1 := hx1
      _ ≤ l ^ x := Real.one_le_rpow hl1 hx
  · push Not at hx1
    have h1 : (x : ℝ) ≤ (2 : ℝ) ^ x := by
      have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx
      have h2 : (2 : ℝ) ^ (Nat.floor x : ℕ) ≤ (2 : ℝ) ^ x := by
        rw [← Real.rpow_natCast (2 : ℝ) (Nat.floor x)]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
      have h3 : x < ((Nat.floor x : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
      have h4 : ((Nat.floor x : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.floor x : ℕ) := by
        have h5 : Nat.floor x + 1 ≤ 2 ^ Nat.floor x := two_pow_ge_succ _
        exact_mod_cast h5
      linarith [h3, h4, h2]
    calc x ≤ (2 : ℝ) ^ x := h1
      _ ≤ l ^ x := Real.rpow_le_rpow (by norm_num) (by linarith) hx

/-- The `2^n`-th root raised back: `((a_n)^{1/2^n})^{2^n} = a_n`. -/
lemma rpow_root_two_pow_self (n : ℕ) :
    ((a n : ℝ) ^ (1 / (2 : ℝ) ^ n)) ^ (2 ^ n) = (a n : ℝ) := by
  have hbase : (0 : ℝ) ≤ (a n : ℝ) := by positivity
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hcast : (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ n := by push_cast; rfl
  rw [← Real.rpow_natCast (((a n : ℝ) ^ (1 / (2 : ℝ) ^ n))) (2 ^ n), hcast,
    ← Real.rpow_mul hbase]
  have hmul : (1 / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = 1 := div_mul_cancel₀ (1 : ℝ) h2n.ne'
  rw [hmul, Real.rpow_one]

/-- `∑_{j ≤ k} 2^j = 2^{k+1} - 1` (ℕ, self-contained). -/
lemma sum_range_two_pow (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (2 : ℕ) ^ j = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
      rw [Finset.sum_range_succ, ih, h2]
      have h1 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      omega

/-- **Product bound at a near-record index** (the product-side of Erdős's
(14)-machinery): writing `L_j := a_j^{1/2^j}`, if
`(1 - 1/(k+1)²)·L_j < L_{k+1}` for all `j ≤ k`, then
`∏_{j ≤ k} a_j ≤ ((1 - 1/(k+1)²)⁻¹·L_{k+1})^{2^{k+1}}`. -/
lemma prod_le_of_near_record (hapos : ∀ n, 0 < a n) {k : ℕ} (hk : 1 ≤ k)
    (hrec : ∀ j ≤ k, (1 - 1 / ((k : ℝ) + 1) ^ 2) *
      ((a j : ℝ) ^ (1 / (2 : ℝ) ^ j)) <
        (a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1))) :
    (∏ j ∈ Finset.range (k + 1), (a j : ℝ)) ≤
      (((1 - 1 / ((k : ℝ) + 1) ^ 2)⁻¹) *
        ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ (k + 1)) := by
  have hcpos : (0 : ℝ) < 1 - 1 / ((k : ℝ) + 1) ^ 2 := by
    have h1 : (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 1) (by positivity)
        (by norm_num : (0 : ℝ) < 4)]
      have h2 : ((2 : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
        have h3 : (2 : ℕ) ≤ k + 1 := by omega
        exact_mod_cast h3
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ ((k : ℝ) + 1) ^ 2 := by
            apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2
    have h3 : (0 : ℝ) < (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by positivity
    linarith [h1, h3]
  set c : ℝ := (1 - 1 / ((k : ℝ) + 1) ^ 2)⁻¹ with hcdef
  have hc : (1 : ℝ) ≤ c := by
    rw [hcdef]
    exact (one_le_inv₀ hcpos).mpr (sub_le_self _ (by positivity))
  have hL1 : (1 : ℝ) ≤ (a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)) :=
    Real.one_le_rpow (by exact_mod_cast hapos (k + 1)) (by positivity)
  have hbound : ∀ j ≤ k, (a j : ℝ) ≤
      (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ j) := by
    intro j hj
    have hLj : (a j : ℝ) ^ (1 / (2 : ℝ) ^ j) <
        c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1))) := by
      have h := hrec j hj
      have h1 : (a j : ℝ) ^ (1 / (2 : ℝ) ^ j) =
          (1 - 1 / ((k : ℝ) + 1) ^ 2)⁻¹ *
            ((1 - 1 / ((k : ℝ) + 1) ^ 2) * ((a j : ℝ) ^ (1 / (2 : ℝ) ^ j))) :=
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
    have hbase1 : (1 : ℝ) ≤ c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1))) := by
      calc (1 : ℝ) ≤ c * 1 := by rw [mul_one]; exact hc
        _ ≤ c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1))) :=
            mul_le_mul_of_nonneg_left hL1 (by linarith [hc])
    exact pow_le_pow_right₀ hbase1 hexp1
  calc (∏ j ∈ Finset.range (k + 1), (a j : ℝ))
      ≤ ∏ j ∈ Finset.range (k + 1),
          (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ j) := hprod
    _ = (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^
          (∑ j ∈ Finset.range (k + 1), 2 ^ j) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ (c * ((a (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)))) ^ (2 ^ (k + 1)) := by
        rw [hsum]
        exact hexp

/-! ### SESSION-2 WALL (documented, see PROGRESS-onesided.md)

The case-(10) closure attempt (`P_k ≤ l^{c·2^k}` from `a_{j+1} ≤ l^{P_j}`)
is FALSE: the invariant self-destructs at k=3 already for l=2
(`P_3 ≤ 2048 = 2^11 > 2^8 = l^{c·2^3}` with c=1). The cap (10) yields only
TOWER bounds on `P_k` — this is exactly Erdős's (11) — and fighting the
tower needs the paper's (13)–(17) (records + sharp tail bound), whose OCR
is garbled and which session 2 could not reconstruct reliably. The false
lemma and the unfinished `irrational_of_oneSidedGrowth_and_cap` were
REMOVED (the Lean kernel rejected the false invariant step — the machine
caught a genuine math error before any claim was made).

What survives, zero-sorry: the threshold-`B` machinery above
(`eventually_rpow_ge_of_oneSidedGrowth`, `tail_le_of_ge_rpow`,
`le_rpow_self`). -/

end Erdos263
