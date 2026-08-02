/-
Erdős Problem #263 — Erdős 1975 route, SESSION 2 (continued): the
mono-anchored loglog tail bound AND the case-(9) theorem.

Contents (all zero-sorry):
* `tail_le_loglog_of_monotone` — the mono-anchored loglog bound below;
* `sq_le_two_pow_succ`, `two_pow_ge_cub`, `log2_le_two_sqrt` — bootstrap
  helpers (`n² ≤ 2^{n+1}`, `n³ ≤ 2^n` for `n ≥ 10`, `log₂ A ≤ 2√A`);
* `irrational_of_monotone_growth_and_spike` — **Erdős's case (9), closed
  at the lim level under plain `Monotone`**: the loglog bound caps the
  spike at `a_{j+1} ≤ q·P_j·(i*+4)`, the bootstrap gives
  `a_{j+1} ≤ 64·(q·P_j)²`, and the spike at `l' := 64·q²+1` contradicts
  `(64q²+1)^{P_j} ≤ 2^{P_j}`-vs-`P_j³` once `P_j` is large.

The file carries `set_option maxHeartbeats 1200000`: unification against
`Nat.log` terms (well-founded recursion) is finite-but-heavy, and the
default 200000 heartbeats are not enough for the kernel re-check.

THE MONO-ANCHORED TAIL BOUND: for a monotone sequence with `a_i ≥ 2^{2^i}`
eventually, the tail after `k` is bounded by
`(log₂(2·log₂ a_{k+1}) + 4)/a_{k+1}` — anchored at the FIRST tail term
`a_{k+1}`, not at the future minimum. The anchor uses monotonicity exactly
once: on the initial index segment `[k+1, i*]` (with
`i* := log₂(2·log₂ a_{k+1})`) one has `a_i ≥ a_{k+1}`; the long segment
`i > i*` is handled per-index by `2^{2^i} ≥ 2^{i-1}·(a_{k+1}/2)` (no
monotonicity there).

This is the bound Erdős's case-(9) argument needs (his Lemma gives the
weaker power-saving `c·n_{k+1}^{-ε/(1+ε)}` under `n_k > k^{1+ε}`; under the
lim hypothesis the doubly-exponential growth gives the sharper loglog
form). The anchor at `a_{k+1}` is precisely where the paper's argument uses
monotonicity — see PROGRESS-onesided.md for the full monotonicity analysis.

ZERO sorry/admit/axiom in this file.
-/
import Mathlib
import Erdos263.Erdos1975B

set_option maxHeartbeats 1200000

open Filter Topology Finset
open scoped Topology

namespace Erdos263

variable {a : ℕ → ℕ}

/-- **Mono-anchored loglog tail bound.** For `a` monotone with
`2^{2^i} ≤ a_i` from `M+1` on and `k ≥ M+1`:
`T_k := ∑' i, 1/a_{i+(k+1)} ≤ (log₂(2·log₂ a_{k+1}) + 4)/a_{k+1}`. -/
lemma tail_le_loglog_of_monotone (hapos : ∀ n, 0 < a n)
    (hsum : Summable (fun n => 1 / (a n : ℝ))) (hmono : Monotone a)
    {M : ℕ} (hge : ∀ i ≥ M + 1, (2 : ℝ) ^ (2 ^ i) ≤ (a i : ℝ)) (k : ℕ)
    (hk : M + 1 ≤ k) :
    (∑' i, 1 / (a (i + (k + 1)) : ℝ)) ≤
      ((Nat.log 2 (2 * Nat.log 2 (a (k + 1))) : ℝ) + 4) / (a (k + 1) : ℝ) := by
  set A := a (k + 1) with hAdef
  set istar := Nat.log 2 (2 * Nat.log 2 A) with histar
  have hApos : 0 < A := hapos _
  have hAr : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hApos
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
  -- split the tail at j₀ = i*+1-(k+1)
  have hsplit : (∑' i, 1 / (a (i + (k + 1)) : ℝ)) =
      (∑ j ∈ Finset.range (istar + 1 - (k + 1)), 1 / (a (j + (k + 1)) : ℝ)) +
        ∑' j, 1 / (a (j + (istar + 1 - (k + 1)) + (k + 1)) : ℝ) := by
    have hs : Summable (fun j => 1 / (a (j + (k + 1)) : ℝ)) :=
      (_root_.summable_nat_add_iff (k + 1)).2 hsum
    exact (hs.sum_add_tsum_nat_add (istar + 1 - (k + 1))).symm
  -- part 1: the initial segment, monotone-anchored
  have hpart1 : (∑ j ∈ Finset.range (istar + 1 - (k + 1)),
      1 / (a (j + (k + 1)) : ℝ)) ≤ (istar : ℝ) / (A : ℝ) := by
    have hterm : ∀ j ∈ Finset.range (istar + 1 - (k + 1)),
        1 / (a (j + (k + 1)) : ℝ) ≤ 1 / (A : ℝ) := by
      intro j hj
      have hj2 : j ≤ istar := by
        have := Finset.mem_range.1 hj
        omega
      have hmono' : (a (k + 1) : ℝ) ≤ (a (j + (k + 1)) : ℝ) := by
        have := hmono (by omega : k + 1 ≤ j + (k + 1))
        exact_mod_cast this
      exact one_div_le_one_div_of_le hAr hmono'
    calc (∑ j ∈ Finset.range (istar + 1 - (k + 1)), 1 / (a (j + (k + 1)) : ℝ))
        ≤ ∑ _j ∈ Finset.range (istar + 1 - (k + 1)), (1 / (A : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = ((istar + 1 - (k + 1) : ℕ) : ℝ) * (1 / (A : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (istar : ℝ) * (1 / (A : ℝ)) := by
          have h1 : ((istar + 1 - (k + 1) : ℕ) : ℝ) ≤ (istar : ℝ) := by
            exact_mod_cast (by omega : istar + 1 - (k + 1) ≤ istar)
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (istar : ℝ) / (A : ℝ) := by rw [mul_one_div]
  -- part 2: per-index doubly-exponential domination
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
  have hpart2 : (∑' j, 1 / (a (j + (istar + 1 - (k + 1)) + (k + 1)) : ℝ)) ≤
      4 / (A : ℝ) := by
    have hidx : ∀ j : ℕ, j + (istar + 1 - (k + 1)) + (k + 1) = j + (istar + 1) :=
      fun j => by omega
    have hterm : ∀ j : ℕ, 1 / (a (j + (istar + 1 - (k + 1)) + (k + 1)) : ℝ) ≤
        (4 / (A : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * (1 / 2 : ℝ) ^ j) := by
      intro j
      rw [hidx j]
      have h1 := hkey (j + (istar + 1)) (by omega)
      calc 1 / (a (j + (istar + 1)) : ℝ)
          ≤ (4 / (A : ℝ)) * (1 / 2 : ℝ) ^ (j + (istar + 1)) := h1
        _ = (4 / (A : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * (1 / 2 : ℝ) ^ j) := by
            rw [pow_add]
            ring
    have hs : Summable (fun j => 1 / (a (j + (istar + 1 - (k + 1)) + (k + 1)) : ℝ)) := by
      have hs' : Summable (fun j => 1 / (a (j + (k + 1)) : ℝ)) :=
        (_root_.summable_nat_add_iff (k + 1)).2 hsum
      exact (_root_.summable_nat_add_iff (istar + 1 - (k + 1))).2 hs'
    have hgs : Summable (fun j : ℕ =>
        (4 / (A : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * (1 / 2 : ℝ) ^ j)) :=
      (summable_geometric_two.mul_left ((1 / 2 : ℝ) ^ (istar + 1))).mul_left (4 / (A : ℝ))
    have hle := Summable.tsum_le_tsum hterm hs hgs
    have hsum2 : (∑' j : ℕ, (4 / (A : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) *
        (1 / 2 : ℝ) ^ j)) = (4 / (A : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * 2) := by
      rw [tsum_mul_left, tsum_mul_left, tsum_geometric_two]
    have hhalf : (1 / 2 : ℝ) ^ (istar + 1) ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ (istar + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by rw [pow_one]
    rw [hsum2] at hle
    have hfin : (4 / (A : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * 2) ≤ 4 / (A : ℝ) := by
      have hc : (1 / 2 : ℝ) ^ (istar + 1) * 2 ≤ 1 := by linarith [hhalf]
      calc (4 / (A : ℝ)) * ((1 / 2 : ℝ) ^ (istar + 1) * 2)
          ≤ (4 / (A : ℝ)) * 1 := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = 4 / (A : ℝ) := by rw [mul_one]
    exact le_trans hle hfin
  calc (∑' i, 1 / (a (i + (k + 1)) : ℝ))
      = (∑ j ∈ Finset.range (istar + 1 - (k + 1)), 1 / (a (j + (k + 1)) : ℝ)) +
          ∑' j, 1 / (a (j + (istar + 1 - (k + 1)) + (k + 1)) : ℝ) := hsplit
    _ ≤ (istar : ℝ) / (A : ℝ) + 4 / (A : ℝ) := add_le_add hpart1 hpart2
    _ = ((istar : ℝ) + 4) / (A : ℝ) := by rw [add_div]

/-! ### Case (9): the spike case, closed under `Monotone a` -/

/-- `n² ≤ 2^{n+1}` for all `n` (self-contained induction). -/
lemma sq_le_two_pow_succ (n : ℕ) : n ^ 2 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h4 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
      have h1 : (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
      have h2 : 2 * k + 1 ≤ 2 ^ (k + 1) := by
        have h3 : k < 2 ^ k := Nat.lt_two_pow_self
        have h5 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      rw [h4, h1]
      omega

/-- `n³ ≤ 2^n` for `n ≥ 10` (self-contained induction). -/
lemma two_pow_ge_cub (n : ℕ) (hn : 10 ≤ n) : n ^ 3 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hk10 : 10 ≤ k := hk
      have hkk : k ≤ k ^ 2 := by
        calc k = k * 1 := by rw [mul_one]
          _ ≤ k * k := by
              gcongr
              omega
          _ = k ^ 2 := by ring
      have hstep : (k + 1) ^ 3 ≤ 2 * k ^ 3 := by
        have e : (k + 1) ^ 3 = k ^ 3 + 3 * k ^ 2 + 3 * k + 1 := by ring
        have h1 : 3 * k ^ 2 + 3 * k + 1 ≤ k ^ 3 := by
          have h2 : 3 * k ^ 2 + 3 * k + 1 ≤ 7 * k ^ 2 := by omega
          have h3 : 7 * k ^ 2 ≤ k ^ 3 := by
            have e2 : k ^ 3 = k ^ 2 * k := by ring
            rw [e2]
            calc 7 * k ^ 2 ≤ k * k ^ 2 := by
                  gcongr
                  omega
              _ = k ^ 2 * k := by ring
          omega
        rw [e]
        omega
      calc (k + 1) ^ 3 ≤ 2 * k ^ 3 := hstep
        _ ≤ 2 * 2 ^ k := by gcongr
        _ = 2 ^ (k + 1) := by ring

/-- `log₂ A ≤ 2·√A` (from `2^{log₂ A} ≤ A` and `n² ≤ 2^{n+1}`; no `logb`). -/
lemma log2_le_two_sqrt (A : ℕ) (hA : 0 < A) :
    (Nat.log 2 A : ℝ) ≤ 2 * Real.sqrt (A : ℝ) := by
  have hn : (Nat.log 2 A : ℝ) ^ 2 ≤ 2 * (A : ℝ) := by
    have h1 : (Nat.log 2 A) ^ 2 ≤ 2 * A := by
      have h2 := Nat.pow_log_le_self 2 hA.ne'
      have h3 := sq_le_two_pow_succ (Nat.log 2 A)
      calc (Nat.log 2 A) ^ 2 ≤ 2 ^ (Nat.log 2 A + 1) := h3
        _ = 2 * 2 ^ Nat.log 2 A := by ring
        _ ≤ 2 * A := by gcongr
    exact_mod_cast h1
  have hsqrt : (Nat.log 2 A : ℝ) = Real.sqrt ((Nat.log 2 A : ℝ) ^ 2) := by
    rw [Real.sqrt_sq (by positivity)]
  have h2 : Real.sqrt (2 : ℝ) ≤ 2 :=
    le_trans (Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 4))
      (by rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)])
  rw [hsqrt]
  calc Real.sqrt ((Nat.log 2 A : ℝ) ^ 2) ≤ Real.sqrt (2 * (A : ℝ)) :=
        Real.sqrt_le_sqrt hn
    _ = Real.sqrt 2 * Real.sqrt (A : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * Real.sqrt (A : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)

/-- **Case (9) closes under `Monotone a` (Erdős's spike case at lim level):**
if `a` is monotone with `a_n^{1/2^n} → ∞` and for every `l ≥ 2` the spike
`l^{P_j} < a_{j+1}` happens frequently, then `∑' 1/a` is irrational.
Proof: the loglog tail bound caps the spike: `a_{j+1} ≤ q·P_j·(i*+4)`
(with `i* = log₂(2·log₂ a_{j+1})`); the bootstrap `i*+4 ≤ 8·√(a_{j+1})`
yields `a_{j+1} ≤ 64·(q·P_j)²`; the spike at `l' := 64·q²+1` gives
`(64q²+1)^{P_j} < 64·(q·P_j)² ≤ P_j³ ≤ 2^{P_j} ≤ l'^{P_j}` — contradiction
once `P_j ≥ max 10 (64q²+1)`. -/
theorem irrational_of_monotone_growth_and_spike (hg : OneSidedGrowth a)
    (hmono : Monotone a)
    (hspike : ∀ l : ℝ, 2 ≤ l → ∃ᶠ j in atTop,
      l ^ (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) < (a (j + 1) : ℝ)) :
    Irrational (∑' n, 1 / (a n : ℝ)) := by
  have hapos : ∀ n, 0 < a n := hg.1
  have hsum : Summable (fun n => 1 / (a n : ℝ)) := summable_one_div_of_oneSidedGrowth hg
  rintro ⟨r, hr⟩
  set q : ℝ := (r.den : ℝ) with hqdef
  have hq : (1 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast r.den_pos
  have hqpos : (0 : ℝ) < q := by linarith
  set l' : ℝ := 64 * q ^ 2 + 1 with hl'def
  have hl' : 2 ≤ l' := by rw [hl'def]; nlinarith [hq]
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_ge_of_oneSidedGrowth hg)
  have hlargenat : (65 : ℕ) ≤ Nat.ceil (64 * q ^ 2 + 1) := by
    have h4 : (65 : ℝ) ≤ 64 * q ^ 2 + 1 := by nlinarith [hq]
    have h5 : (65 : ℝ) ≤ ((Nat.ceil (64 * q ^ 2 + 1) : ℕ) : ℝ) :=
      le_trans h4 (Nat.le_ceil _)
    exact_mod_cast h5
  obtain ⟨j, hj, hsp⟩ := (Filter.frequently_atTop.1 (hspike l' hl'))
    (max (N₀ + 1) (Nat.ceil (64 * q ^ 2 + 1)))
  have hjN : N₀ ≤ j := le_trans (le_trans (Nat.le_succ N₀) (le_max_left _ _)) hj
  have hjC : Nat.ceil (64 * q ^ 2 + 1) ≤ j := le_trans (le_max_right _ _) hj
  -- the loglog cap at the spike index
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
  -- the bootstrap: a_{j+1} ≤ 64·(q·P_j)²
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
  -- P_j is large
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
  have hP10 : (10 : ℕ) ≤ ∏ i ∈ Finset.range (j + 1), a i :=
    le_trans (le_trans (by norm_num : (10 : ℕ) ≤ 65) hlargenat) hPnat
  -- the final contradiction
  have hPnatR : ((∏ i ∈ Finset.range (j + 1), a i : ℕ) : ℝ) =
      ∏ i ∈ Finset.range (j + 1), (a i : ℝ) := by
    push_cast
    rfl
  have hgt : 64 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 <
      l' ^ (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) := by
    have hcub : ((∏ i ∈ Finset.range (j + 1), a i : ℕ) : ℝ) ^ 3 ≤
        (2 : ℝ) ^ ((∏ i ∈ Finset.range (j + 1), a i : ℕ) : ℝ) := by
      have h1 := two_pow_ge_cub _ hP10
      have h2 : (((∏ i ∈ Finset.range (j + 1), a i) ^ 3 : ℕ) : ℝ) ≤
          ((2 ^ (∏ i ∈ Finset.range (j + 1), a i) : ℕ) : ℝ) := by
        exact_mod_cast h1
      have hcast1 : (((∏ i ∈ Finset.range (j + 1), a i) ^ 3 : ℕ) : ℝ) =
          ((∏ i ∈ Finset.range (j + 1), a i : ℕ) : ℝ) ^ 3 := by push_cast; rfl
      have hcast2 : ((2 ^ (∏ i ∈ Finset.range (j + 1), a i) : ℕ) : ℝ) =
          (2 : ℝ) ^ ((∏ i ∈ Finset.range (j + 1), a i : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.rpow_natCast, Nat.cast_ofNat]
      rwa [hcast1, hcast2] at h2
    have hPgt : (64 * q ^ 2 : ℝ) < ∏ i ∈ Finset.range (j + 1), (a i : ℝ) := by
      have h1 : ((Nat.ceil (64 * q ^ 2 + 1) : ℕ) : ℝ) ≤
          ∏ i ∈ Finset.range (j + 1), (a i : ℝ) := by
        rw [← hPnatR]
        exact_mod_cast hPnat
      have h2 : (64 * q ^ 2 + 1 : ℝ) ≤ ((Nat.ceil (64 * q ^ 2 + 1) : ℕ) : ℝ) :=
        Nat.le_ceil _
      nlinarith [h1, h2, hq]
    have h3 : 64 * (q * ∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 =
        (64 * q ^ 2) * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 := by ring
    rw [h3]
    calc (64 * q ^ 2) * (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2
        < (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) *
          (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) ^ 2 :=
          mul_lt_mul_of_pos_right hPgt (pow_pos hPpos 2)
      _ = ((∏ i ∈ Finset.range (j + 1), a i : ℕ) : ℝ) ^ 3 := by
          rw [hPnatR]
          ring
      _ ≤ (2 : ℝ) ^ ((∏ i ∈ Finset.range (j + 1), a i : ℕ) : ℝ) := hcub
      _ = (2 : ℝ) ^ (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) := by
          rw [hPnatR]
      _ ≤ l' ^ (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) :=
          Real.rpow_le_rpow (by norm_num) hl' (by positivity)
  have hboot' : (a (j + 1) : ℝ) < l' ^ (∏ i ∈ Finset.range (j + 1), (a i : ℝ)) :=
    lt_of_le_of_lt hboot hgt
  exact absurd hsp (not_lt_of_ge hboot'.le)

end Erdos263
