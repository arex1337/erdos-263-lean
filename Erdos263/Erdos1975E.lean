/-
Erdos1975E.lean — SESSION 5 (2026-08-02): the future-min
(monotonicity-free) residue of the 1975 closing chain.

New file; NO refactor of run-2/3/4 files. The run-4 headline
`irrational_of_oneSidedGrowth_monotone` (Erdos1975D.lean) is untouched and
remains the published result of this project.

`tail_le_loglog_of_future_min` is `tail_le_loglog_of_monotone`
(Erdos1975C.lean) with the hypothesis `Monotone a` REMOVED. The mono proof
uses monotonicity in exactly one place — the initial-segment anchor
`a_{k+1} ≤ a_i` for `i ∈ [k+1, i*]` (Erdos1975C.lean lines 95–98). Here the
anchor is replaced by a lower bound `m` on the future window
`[k+1, i*]` (the intended `m` is the future minimum
`min_{i ∈ [k+1, i*]} a_i`), yielding

  T_k ≤ (log₂(2·log₂ a_{k+1}) + 4) / m.

HONEST-GAP NOTE (why this does not close the folklore form): the uniform
growth hypothesis `hge : ∀ i ≥ M+1, 2^{2^i} ≤ a_i` is RETAINED — it is
itself only derivable from `OneSidedGrowth` via monotonicity (the lim-sup
subsequence propagates to all large indices), so this lemma is the exact
monotone-free core, not the full folklore step. And even granting `hge`,
combining this bound with the escape-record product bound
`P_k ≤ c^{2^{k+1}}·a_{k+1}` (Erdos1975D `prod_le_of_escape_record`) through
the integrality machine `1 ≤ q·P_k·T_k` yields only
`m_k / a_{k+1} ≤ q·c^{2^{k+1}}·(i*+4) → 0` — forced deep relative dips after
each record, NOT a contradiction: record–dip alternation is consistent with
`1 ≤ q·P_n·T_n` at every index. See PROGRESS-onesided.md, session 5, for the
full negative map.

The file carries `set_option maxHeartbeats 1200000` like Erdos1975C:
unification against `Nat.log` terms (well-founded recursion) is
finite-but-heavy.

ZERO sorry/admit/axiom in this file.
-/
import Mathlib
import Erdos263.Erdos1975C

set_option maxHeartbeats 1200000

open Filter Topology Finset
open scoped Topology

namespace Erdos263

variable {a : ℕ → ℕ}

/-- **Future-min-anchored loglog tail bound (monotonicity-free).** For `a`
with `2^{2^i} ≤ a_i` from `M+1` on, `k ≥ M+1`, and `m` a positive lower
bound of the window `[k+1, i*]` with `i* := log₂(2·log₂ a_{k+1})`:
`T_k := ∑' i, 1/a_{i+(k+1)} ≤ (i* + 4)/m`.
This is `tail_le_loglog_of_monotone` with `Monotone a` dropped; the initial
segment is anchored at `m` instead of `a_{k+1}`. -/
lemma tail_le_loglog_of_future_min (hapos : ∀ n, 0 < a n)
    (hsum : Summable (fun n => 1 / (a n : ℝ)))
    {M : ℕ} (hge : ∀ i ≥ M + 1, (2 : ℝ) ^ (2 ^ i) ≤ (a i : ℝ)) (k : ℕ)
    (hk : M + 1 ≤ k) (m : ℕ) (hmpos : 0 < m)
    (hm : ∀ i ∈ Finset.Icc (k + 1) (Nat.log 2 (2 * Nat.log 2 (a (k + 1)))),
      m ≤ a i) :
    (∑' i, 1 / (a (i + (k + 1)) : ℝ)) ≤
      ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) / (m : ℝ) := by
  set A := a (k + 1) with hAdef
  set istar := Nat.log 2 (2 * Nat.log 2 A) with histar
  have hApos : 0 < A := hapos _
  have hAr : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hApos
  have hm0r : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hA2 : (2 : ℕ) ^ (2 ^ (k + 1)) ≤ A := by
    have h := hge (k + 1) (by omega)
    have hcast : ((2 ^ (2 ^ (k + 1)) : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ (k + 1)) := by
      push_cast
      rfl
    rw [← hcast] at h
    exact_mod_cast h
  have hlogA : 2 ^ (k + 1) ≤ Nat.log 2 A :=
    Nat.le_log_of_pow_le (by norm_num) hA2
  have histar_ge : k + 2 ≤ istar := by
    have h1 : 2 ^ (k + 2) ≤ 2 * Nat.log 2 A := by
      calc 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
        _ ≤ 2 * Nat.log 2 A := by
            gcongr
    have hne : (2 * Nat.log 2 A) ≠ 0 := by
      have h2 : (1 : ℕ) ≤ Nat.log 2 A := le_trans Nat.one_le_two_pow hlogA
      omega
    exact (Nat.le_log_iff_pow_le (by norm_num) hne).2 h1
  -- the window bound at i = k+1 gives m ≤ A
  have hmA : m ≤ A := by
    have hmem : k + 1 ∈ Finset.Icc (k + 1) istar := by
      rw [Finset.mem_Icc]
      omega
    exact hm (k + 1) hmem
  have hmAr : (m : ℝ) ≤ (A : ℝ) := by exact_mod_cast hmA
  -- split the tail at j₀ = i*+1-(k+1)
  have hsplit : (∑' i, 1 / (a (i + (k + 1)) : ℝ)) =
      (∑ j ∈ Finset.range (istar + 1 - (k + 1)), 1 / (a (j + (k + 1)) : ℝ)) +
        ∑' j, 1 / (a (j + (istar + 1 - (k + 1)) + (k + 1)) : ℝ) := by
    have hs : Summable (fun j => 1 / (a (j + (k + 1)) : ℝ)) :=
      (_root_.summable_nat_add_iff (k + 1)).2 hsum
    exact (hs.sum_add_tsum_nat_add (istar + 1 - (k + 1))).symm
  -- part 1: the initial segment, future-min-anchored (THE mono-free step)
  have hpart1 : (∑ j ∈ Finset.range (istar + 1 - (k + 1)),
      1 / (a (j + (k + 1)) : ℝ)) ≤ (istar : ℝ) / (m : ℝ) := by
    have hterm : ∀ j ∈ Finset.range (istar + 1 - (k + 1)),
        1 / (a (j + (k + 1)) : ℝ) ≤ 1 / (m : ℝ) := by
      intro j hj
      have hjmem : j + (k + 1) ∈ Finset.Icc (k + 1) istar := by
        rw [Finset.mem_Icc]
        have hj' := Finset.mem_range.1 hj
        omega
      have hle : (m : ℝ) ≤ (a (j + (k + 1)) : ℝ) := by
        exact_mod_cast hm _ hjmem
      exact one_div_le_one_div_of_le hm0r hle
    calc (∑ j ∈ Finset.range (istar + 1 - (k + 1)), 1 / (a (j + (k + 1)) : ℝ))
        ≤ ∑ _j ∈ Finset.range (istar + 1 - (k + 1)), (1 / (m : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = ((istar + 1 - (k + 1) : ℕ) : ℝ) * (1 / (m : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (istar : ℝ) * (1 / (m : ℝ)) := by
          have h1 : ((istar + 1 - (k + 1) : ℕ) : ℝ) ≤ (istar : ℝ) := by
            exact_mod_cast (by omega : istar + 1 - (k + 1) ≤ istar)
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (istar : ℝ) / (m : ℝ) := by rw [mul_one_div]
  -- part 2: per-index doubly-exponential domination (anchored at A, then
  -- transferred to m via m ≤ A); NO monotonicity in this part either
  have hkey : ∀ t : ℕ, istar + 1 ≤ t →
      (1 / (a t : ℝ)) ≤ (4 / (A : ℝ)) * (1 / 2 : ℝ) ^ t := by
    intro t ht
    have ht1 : 1 ≤ t := by omega
    have htM : M + 1 ≤ t := by omega
    -- 2^t ≥ (t-1) + log₂ A
    have hsucc : (2 : ℕ) ^ t = 2 * 2 ^ (t - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos (by omega : 0 < t)]
      rw [pow_succ', Nat.pred_eq_sub_one]
    have hexp : (t - 1) + Nat.log 2 A ≤ 2 ^ t := by
      have hA1 : Nat.log 2 A ≤ 2 ^ (t - 1) := by
        have h1 : 2 * Nat.log 2 A < 2 ^ (istar + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num) _
        have h2 : 2 ^ (istar + 1) ≤ 2 ^ t :=
          pow_le_pow_right₀ (by norm_num) ht
        have h3 : 2 * Nat.log 2 A ≤ 2 ^ t := le_trans h1.le h2
        omega
      have hA2' : t - 1 ≤ 2 ^ (t - 1) := by
        have := two_pow_ge_succ (t - 1)
        omega
      have h5 : (t - 1) + Nat.log 2 A ≤ 2 ^ (t - 1) + 2 ^ (t - 1) :=
        add_le_add hA2' hA1
      have h6 : 2 ^ (t - 1) + 2 ^ (t - 1) = 2 ^ t := by
        rw [hsucc]
        ring
      omega
    have h2pow : (2 : ℝ) ^ (2 ^ t) ≥ (2 : ℝ) ^ ((t - 1) + Nat.log 2 A) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hsplt : (2 : ℝ) ^ (((t - 1) + Nat.log 2 A : ℕ)) =
        (2 : ℝ) ^ (t - 1) * (2 : ℝ) ^ (Nat.log 2 A) := by rw [pow_add]
    have hlogpow : (A : ℝ) ≤ 2 * (2 : ℝ) ^ (Nat.log 2 A) := by
      have h1 : A < 2 ^ (Nat.log 2 A + 1) := Nat.lt_pow_succ_log_self (by norm_num) A
      have h2 : (2 : ℝ) ^ (Nat.log 2 A + 1) = 2 * (2 : ℝ) ^ (Nat.log 2 A) := by
        rw [pow_succ']
      have h3 : ((2 ^ (Nat.log 2 A + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (Nat.log 2 A + 1) := by
        push_cast
        rfl
      have h4 : (A : ℝ) < (2 : ℝ) ^ (Nat.log 2 A + 1) := by
        rw [← h3]
        exact_mod_cast h1
      rw [h2] at h4
      linarith [h4]
    have hbig : (A : ℝ) / 2 * (2 : ℝ) ^ (t - 1) ≤ (a t : ℝ) := by
      have h1 : (2 : ℝ) ^ (2 ^ t) ≤ (a t : ℝ) := hge t htM
      have hcast : ((2 ^ (t - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (t - 1) := by push_cast; rfl
      calc (A : ℝ) / 2 * (2 : ℝ) ^ (t - 1)
          ≤ (2 : ℝ) ^ (Nat.log 2 A) * (2 : ℝ) ^ (t - 1) := by
            have hle1 : (A : ℝ) / 2 ≤ (2 : ℝ) ^ (Nat.log 2 A) := by linarith [hlogpow]
            exact mul_le_mul_of_nonneg_right hle1 (by positivity)
        _ = (2 : ℝ) ^ ((t - 1) + Nat.log 2 A) := by rw [hsplt]; ring
        _ ≤ (2 : ℝ) ^ (2 ^ t) := h2pow
        _ ≤ (a t : ℝ) := h1
    have hpos2 : (0 : ℝ) < (A : ℝ) / 2 * (2 : ℝ) ^ (t - 1) := by positivity
    calc (1 / (a t : ℝ)) ≤ 1 / ((A : ℝ) / 2 * (2 : ℝ) ^ (t - 1)) :=
          one_div_le_one_div_of_le hpos2 hbig
      _ = (4 / (A : ℝ)) * (1 / 2 : ℝ) ^ t := by
          have hsuccR : (2 : ℝ) ^ t = 2 * (2 : ℝ) ^ (t - 1) := by exact_mod_cast hsucc
          have hX : (2 : ℝ) ^ (t - 1) ≠ 0 := by positivity
          rw [div_pow, one_pow, hsuccR]
          field_simp [hAr.ne', hX, (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
  -- transfer the part-2 anchor from A to m
  have hkeym : ∀ t : ℕ, istar + 1 ≤ t →
      (1 / (a t : ℝ)) ≤ (4 / (m : ℝ)) * (1 / 2 : ℝ) ^ t := by
    intro t ht
    refine le_trans (hkey t ht) ?_
    have h4 : (4 : ℝ) / (A : ℝ) ≤ 4 / (m : ℝ) := by
      have h1 : (1 : ℝ) / (A : ℝ) ≤ 1 / (m : ℝ) :=
        one_div_le_one_div_of_le hm0r hmAr
      calc (4 : ℝ) / (A : ℝ) = 4 * (1 / (A : ℝ)) := by rw [mul_one_div]
        _ ≤ 4 * (1 / (m : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 4 / (m : ℝ) := by rw [mul_one_div]
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have hpart2 : (∑' j, 1 / (a (j + (istar + 1 - (k + 1)) + (k + 1)) : ℝ)) ≤
      4 / (m : ℝ) := by
    have hidx : ∀ j : ℕ, j + (istar + 1 - (k + 1)) + (k + 1) = j + (istar + 1) :=
      fun j => by omega
    have hterm : ∀ j : ℕ, 1 / (a (j + (istar + 1 - (k + 1)) + (k + 1)) : ℝ) ≤
        (4 / (m : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * (1 / 2 : ℝ) ^ j) := by
      intro j
      rw [hidx j]
      have h1 := hkeym (j + (istar + 1)) (by omega)
      calc 1 / (a (j + (istar + 1)) : ℝ)
          ≤ (4 / (m : ℝ)) * (1 / 2 : ℝ) ^ (j + (istar + 1)) := h1
        _ = (4 / (m : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * (1 / 2 : ℝ) ^ j) := by
            rw [pow_add]
            ring
    have hs : Summable (fun j => 1 / (a (j + (istar + 1 - (k + 1)) + (k + 1)) : ℝ)) := by
      have hs' : Summable (fun j => 1 / (a (j + (k + 1)) : ℝ)) :=
        (_root_.summable_nat_add_iff (k + 1)).2 hsum
      exact (_root_.summable_nat_add_iff (istar + 1 - (k + 1))).2 hs'
    have hgs : Summable (fun j : ℕ =>
        (4 / (m : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * (1 / 2 : ℝ) ^ j)) :=
      (summable_geometric_two.mul_left ((1 / 2 : ℝ) ^ (istar + 1))).mul_left (4 / (m : ℝ))
    have hle := Summable.tsum_le_tsum hterm hs hgs
    have hsum2 : (∑' j : ℕ, (4 / (m : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) *
        (1 / 2 : ℝ) ^ j)) = (4 / (m : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * 2) := by
      rw [tsum_mul_left, tsum_mul_left, tsum_geometric_two]
    have hhalf : (1 / 2 : ℝ) ^ (istar + 1) ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ (istar + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by rw [pow_one]
    rw [hsum2] at hle
    have hfin : (4 / (m : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * 2) ≤ 4 / (m : ℝ) := by
      have hc : (1 / 2 : ℝ) ^ (istar + 1) * 2 ≤ 1 := by linarith [hhalf]
      calc (4 / (m : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * 2)
          ≤ (4 / (m : ℝ)) * 1 := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = 4 / (m : ℝ) := by rw [mul_one]
    exact le_trans hle hfin
  calc (∑' i, 1 / (a (i + (k + 1)) : ℝ))
      = (∑ j ∈ Finset.range (istar + 1 - (k + 1)), 1 / (a (j + (k + 1)) : ℝ)) +
          ∑' j, 1 / (a (j + (istar + 1 - (k + 1)) + (k + 1)) : ℝ) := hsplit
    _ ≤ (istar : ℝ) / (m : ℝ) + 4 / (m : ℝ) := add_le_add hpart1 hpart2
    _ = ((istar : ℝ) + 4) / (m : ℝ) := by rw [add_div]

end Erdos263
