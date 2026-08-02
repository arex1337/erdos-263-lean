/-
Erdős Problem #263 — the ERDŐS 1975 RECURRENCE CORE for the one-sided
folklore form (run 4, session 1).

Source: P. Erdős, *Some problems and results on the irrationality of the sum
of infinite series*, J. Math. Sci. 10 (1975), 1–7 (scan:
`problems/263/code/phase1/erdos_1975_renyi_scan.txt`; provenance:
`problems/263/ERDOS1975-SCOUT.md`). Route analysis and the exact status of
the missing lemma: `problems/263/lean/PROGRESS-onesided.md`.

WHAT IS HERE (all zero-sorry):

* `tail_succ` — the tail recursion `T_N = 1/a_{N+1} + T_{N+1}`;
* `prod_tail_recurrence` — the denominator-product recurrence
  `a_{N+1}·(q·P_N·T_N) = q·P_N + q·P_{N+1}·T_{N+1}` where `P_N = ∏_{n≤N} a_n`;
* `one_le_prod_tail` — if `∑' 1/a = r ∈ ℚ` then `1 ≤ r.den·P_N·T_N`
  (integrality, run-2 `key_integrality`, positivity from run-2 `tail_b_pos`);
* `cap_of_tail_small` — the CONDITIONAL growth cap:
  `1 ≤ q·P_N·T_N` and `T_{N+1} ≤ 1/(2·q·P_N)` imply `a_{N+1} ≤ 2·q·P_N`;
* `tail_le_two_pow` — if `2^{2^i} ≤ a_i` for all `i ≥ M+1` then
  `T_M ≤ 2·(1/2)^{2^{M+1}}` (geometric comparison; the O2 regime);
* `prod_cap_iter` — the cap iteration (ℕ): if `a_{n+1} ≤ C·P_n` for all
  `n ≥ N₂` then `a_{N₂+1+k} ≤ (C·P_{N₂})^{2^k}`;
* `not_tendsto_root_of_cap` — an eventual constant-factor product cap forces
  `a_n^{1/2^n}` to stay bounded, contradicting any `→ ∞` tendency;
* `cap_fails_often_of_oneSidedGrowth` — under the one-sided hypothesis, NO
  constant-factor product cap can hold eventually (the cap hypothesis of the
  naive route always fails infinitely often — machine-checked);
* `irrational_of_tail_small` — the CONDITIONAL irrationality theorem: if for
  EVERY `C > 0` the tails satisfy `T_{n+1} ≤ C/P_n` eventually, the sum is
  irrational. Its hypothesis is EXACTLY the missing lemma for the folklore
  form (see PROGRESS-onesided.md §"THE HOLE": it fails at spike indices, and
  the folklore theorem needs Erdős's adaptive-record endgame instead);
* `exists_near_record` — Borel's record lemma (Erdős 1975, eq. (14)): if
  `L → ∞` and `L ≥ 0`, then arbitrarily large near-record indices `k` exist
  with `L_{k+1} > (1 - 1/(k+1)²)·L_j` for all `j ≤ k`. This is the index
  supply for the adaptive endgame (session 2+). (INTERIM, minus-slack form:
  the paper's (14) has PLUS slack — see the page-image transcription; the
  corrected escape form is `exists_escape_record` in Erdos1975D.lean, which
  is what the closing chain uses. This lemma remains true but is unused by
  the closing chain.)

NO monotonicity is used anywhere in this file.

ZERO sorry/admit/axiom in this file.
-/
import Mathlib
import Erdos263.OneSided

open Filter Topology Finset
open scoped Topology

namespace Erdos263

variable {a : ℕ → ℕ}

/-! ### The tail recursion and the product recurrence -/

/-- **Tail recursion:** `T_N = 1/a_{N+1} + T_{N+1}` where
`T_N := ∑' i, 1/a_{i+(N+1)}`. -/
lemma tail_succ (hsum : Summable (fun n => 1 / (a n : ℝ))) (N : ℕ) :
    (∑' i, 1 / (a (i + (N + 1)) : ℝ)) =
      1 / (a (N + 1) : ℝ) + ∑' i, 1 / (a (i + (N + 2)) : ℝ) := by
  have h1 : Summable (fun i => 1 / (a (i + (N + 1)) : ℝ)) :=
    (_root_.summable_nat_add_iff (N + 1)).2 hsum
  have h2 := h1.tsum_eq_zero_add
  have e2 : ∀ i : ℕ, i + 1 + (N + 1) = i + (N + 2) := fun i => by ring
  rw [h2]
  have e1 : (0 : ℕ) + (N + 1) = N + 1 := by ring
  rw [e1]
  congr 1
  exact tsum_congr fun i => by rw [e2 i]

/-- **The denominator-product recurrence** (Erdős 1975, Theorem 1 machinery):
with `P_N = ∏_{n ≤ N} a_n` and `T_N` the tail,
`a_{N+1}·(q·P_N·T_N) = q·P_N + q·P_{N+1}·T_{N+1}`.
This is definition-chasing from `tail_succ` and `P_{N+1} = P_N·a_{N+1}`. -/
lemma prod_tail_recurrence (hapos : ∀ n, 0 < a n)
    (hsum : Summable (fun n => 1 / (a n : ℝ))) (q : ℝ) (N : ℕ) :
    (a (N + 1) : ℝ) * (q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
      (∑' i, 1 / (a (i + (N + 1)) : ℝ))) =
    q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) +
      q * (∏ n ∈ Finset.range (N + 2), (a n : ℝ)) *
        (∑' i, 1 / (a (i + (N + 2)) : ℝ)) := by
  rw [tail_succ hsum N]
  have hP : (∏ n ∈ Finset.range (N + 2), (a n : ℝ)) =
      (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) * (a (N + 1) : ℝ) :=
    Finset.prod_range_succ (fun n => (a n : ℝ)) (N + 1)
  rw [hP]
  have ha : (a (N + 1) : ℝ) ≠ 0 := by exact_mod_cast (hapos (N + 1)).ne'
  have hmul : (a (N + 1) : ℝ) * (1 / (a (N + 1) : ℝ)) = 1 := mul_one_div_cancel ha
  calc (a (N + 1) : ℝ) * (q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
        (1 / (a (N + 1) : ℝ) + ∑' i, 1 / (a (i + (N + 2)) : ℝ)))
      = q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
          ((a (N + 1) : ℝ) * (1 / (a (N + 1) : ℝ))) +
        q * ((∏ n ∈ Finset.range (N + 1), (a n : ℝ)) * (a (N + 1) : ℝ)) *
          (∑' i, 1 / (a (i + (N + 2)) : ℝ)) := by ring
    _ = q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) +
        q * ((∏ n ∈ Finset.range (N + 1), (a n : ℝ)) * (a (N + 1) : ℝ)) *
          (∑' i, 1 / (a (i + (N + 2)) : ℝ)) := by rw [hmul]; ring

/-- **Integrality packaging:** if `∑' 1/a = r ∈ ℚ`, then
`1 ≤ r.den·P_N·T_N` (the positive integer `m_N` of Erdős's proof; run-2
`key_integrality` at `b := a`). -/
lemma one_le_prod_tail (hapos : ∀ n, 0 < a n)
    (hsum : Summable (fun n => 1 / (a n : ℝ))) {r : ℚ}
    (hr : (r : ℝ) = ∑' n, 1 / (a n : ℝ)) (N : ℕ) :
    (1 : ℝ) ≤ (r.den : ℝ) * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
      (∑' i, 1 / (a (i + (N + 1)) : ℝ)) := by
  obtain ⟨z, hz⟩ := key_integrality hapos hsum r hr N
  have hTpos : (0 : ℝ) < ∑' i, (1 / (a (i + (N + 1)) : ℝ)) :=
    tail_b_pos hapos hsum N
  have hPpos : (0 : ℝ) < ∏ n ∈ Finset.range (N + 1), (a n : ℝ) :=
    Finset.prod_pos (fun n _ => by exact_mod_cast hapos n)
  have hqpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    rw [hz]
    exact mul_pos (mul_pos hqpos hPpos) hTpos
  have hz1 : (1 : ℤ) ≤ z := by
    have h0 : (0 : ℤ) < z := by exact_mod_cast hzpos
    omega
  calc (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
    _ = (r.den : ℝ) * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
          (∑' i, 1 / (a (i + (N + 1)) : ℝ)) := hz

/-! ### The conditional growth cap -/

/-- **The conditional growth cap** (Erdős 1975's `(10)`-case content, made
conditional): if `m_N = q·P_N·T_N ≥ 1` and the next tail is small,
`T_{N+1} ≤ 1/(2·q·P_N)`, then `a_{N+1} ≤ 2·q·P_N`.
Proof: `1/a_{N+1} = T_N − T_{N+1} ≥ 1/(q·P_N) − 1/(2·q·P_N) = 1/(2·q·P_N)`. -/
lemma cap_of_tail_small (hapos : ∀ n, 0 < a n)
    (hsum : Summable (fun n => 1 / (a n : ℝ))) {q : ℝ} (hq : 1 ≤ q) (N : ℕ)
    (hm : (1 : ℝ) ≤ q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
      (∑' i, 1 / (a (i + (N + 1)) : ℝ)))
    (hT : (∑' i, 1 / (a (i + (N + 2)) : ℝ)) ≤
      1 / (2 * q * ∏ n ∈ Finset.range (N + 1), (a n : ℝ))) :
    (a (N + 1) : ℝ) ≤ 2 * q * ∏ n ∈ Finset.range (N + 1), (a n : ℝ) := by
  have hPpos : (0 : ℝ) < ∏ n ∈ Finset.range (N + 1), (a n : ℝ) :=
    Finset.prod_pos (fun n _ => by exact_mod_cast hapos n)
  have hqpos : (0 : ℝ) < q := by linarith
  have hqPpos : (0 : ℝ) < q * ∏ n ∈ Finset.range (N + 1), (a n : ℝ) :=
    mul_pos hqpos hPpos
  rw [tail_succ hsum N] at hm
  have h1 : q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
      (∑' i, 1 / (a (i + (N + 2)) : ℝ)) ≤ 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hT (le_of_lt hqPpos)
    have e : q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
        (1 / (2 * q * ∏ n ∈ Finset.range (N + 1), (a n : ℝ))) = 1 / 2 := by
      field_simp [hqPpos.ne']
    rw [e] at hmul
    exact hmul
  have hm' : (1 : ℝ) ≤ q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
      (1 / (a (N + 1) : ℝ)) + q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
        (∑' i, 1 / (a (i + (N + 2)) : ℝ)) := by
    have e : q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
        (1 / (a (N + 1) : ℝ) + ∑' i, 1 / (a (i + (N + 2)) : ℝ)) =
        q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) * (1 / (a (N + 1) : ℝ)) +
        q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
          (∑' i, 1 / (a (i + (N + 2)) : ℝ)) := by ring
    rwa [e] at hm
  have h2 : (1 : ℝ) / 2 ≤ q * (∏ n ∈ Finset.range (N + 1), (a n : ℝ)) *
      (1 / (a (N + 1) : ℝ)) := by linarith [hm', h1]
  have ha : (0 : ℝ) < (a (N + 1) : ℝ) := by exact_mod_cast hapos (N + 1)
  rw [mul_one_div] at h2
  rw [le_div_iff₀ ha] at h2
  calc (a (N + 1) : ℝ) = 2 * ((1 : ℝ) / 2 * (a (N + 1) : ℝ)) := by ring
    _ ≤ 2 * q * ∏ n ∈ Finset.range (N + 1), (a n : ℝ) := by linarith [h2]

/-! ### The O2 tail bound -/

/-- **Tail bound in the doubly-exponential regime:** if `2^{2^i} ≤ a_i` for
all `i ≥ M+1`, then `T_M ≤ 2·(1/2)^{2^{M+1}}` (termwise comparison with a
geometric series; uses `2^{M+1} + i ≤ 2^{i+(M+1)}`). -/
lemma tail_le_two_pow (_hapos : ∀ n, 0 < a n)
    (hsum : Summable (fun n => 1 / (a n : ℝ))) {M : ℕ}
    (hge : ∀ i ≥ M + 1, (2 : ℝ) ^ (2 ^ i) ≤ (a i : ℝ)) :
    (∑' i, 1 / (a (i + (M + 1)) : ℝ)) ≤ 2 * (1 / 2 : ℝ) ^ (2 ^ (M + 1)) := by
  have hterm : ∀ i : ℕ, (1 / (a (i + (M + 1)) : ℝ)) ≤
      (1 / 2 : ℝ) ^ (2 ^ (M + 1)) * (1 / 2 : ℝ) ^ i := by
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
    have hpow : (2 : ℝ) ^ (2 ^ (M + 1) + i) ≤ (a (i + (M + 1)) : ℝ) := by
      have h1 := hge (i + (M + 1)) (by omega)
      have h2 : (2 : ℝ) ^ (2 ^ (M + 1) + i) ≤ (2 : ℝ) ^ (2 ^ (i + (M + 1))) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by exact_mod_cast hexp)
      exact le_trans h2 h1
    calc (1 / (a (i + (M + 1)) : ℝ)) ≤ 1 / (2 : ℝ) ^ (2 ^ (M + 1) + i) :=
          one_div_le_one_div_of_le (by positivity) hpow
      _ = (1 / 2 : ℝ) ^ (2 ^ (M + 1) + i) := by rw [div_pow, one_pow]
      _ = (1 / 2 : ℝ) ^ (2 ^ (M + 1)) * (1 / 2 : ℝ) ^ i := by rw [pow_add]
  have hlsumm : Summable (fun i : ℕ => 1 / (a (i + (M + 1)) : ℝ)) :=
    (_root_.summable_nat_add_iff (M + 1)).2 hsum
  have hgsumm : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (2 ^ (M + 1)) * (1 / 2 : ℝ) ^ i) :=
    summable_geometric_two.mul_left _
  have hle := Summable.tsum_le_tsum hterm hlsumm hgsumm
  have hsum2 : (∑' i : ℕ, (1 / 2 : ℝ) ^ (2 ^ (M + 1)) * (1 / 2 : ℝ) ^ i) =
      2 * (1 / 2 : ℝ) ^ (2 ^ (M + 1)) := by
    rw [tsum_mul_left, tsum_geometric_two, mul_comm]
  calc (∑' i, 1 / (a (i + (M + 1)) : ℝ))
      ≤ (∑' i : ℕ, (1 / 2 : ℝ) ^ (2 ^ (M + 1)) * (1 / 2 : ℝ) ^ i) := hle
    _ = 2 * (1 / 2 : ℝ) ^ (2 ^ (M + 1)) := hsum2

/-! ### The cap iteration and the bounded-root contradiction -/

/-- **Cap iteration (ℕ):** if `a_{n+1} ≤ C·P_n` for all `n ≥ N₂`, then
`a_{N₂+1+k} ≤ (C·P_{N₂})^{2^k}` (via `Q_{k+1} ≤ Q_k²` for
`Q_k := C·P_{N₂+k}`). No positivity or summability needed — the cap alone
drives the induction. -/
lemma prod_cap_iter {N₂ C : ℕ}
    (hcap : ∀ n ≥ N₂, a (n + 1) ≤ C * ∏ i ∈ Finset.range (n + 1), a i) (k : ℕ) :
    a (N₂ + 1 + k) ≤ (C * ∏ i ∈ Finset.range (N₂ + 1), a i) ^ (2 ^ k) := by
  have key : ∀ k : ℕ, C * ∏ i ∈ Finset.range (N₂ + k + 1), a i ≤
      (C * ∏ i ∈ Finset.range (N₂ + 1), a i) ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h1 : ∏ i ∈ Finset.range (N₂ + (k + 1) + 1), a i =
            (∏ i ∈ Finset.range (N₂ + k + 1), a i) * a (N₂ + k + 1) := by
          have e : N₂ + (k + 1) + 1 = (N₂ + k + 1) + 1 := by ring
          rw [e, Finset.prod_range_succ]
        have h2 : a (N₂ + k + 1) ≤ C * ∏ i ∈ Finset.range (N₂ + k + 1), a i :=
          hcap (N₂ + k) (by omega)
        calc C * ∏ i ∈ Finset.range (N₂ + (k + 1) + 1), a i
            = C * ((∏ i ∈ Finset.range (N₂ + k + 1), a i) * a (N₂ + k + 1)) := by
              rw [h1]
          _ ≤ C * ((∏ i ∈ Finset.range (N₂ + k + 1), a i) *
                (C * ∏ i ∈ Finset.range (N₂ + k + 1), a i)) := by
              gcongr
          _ = (C * ∏ i ∈ Finset.range (N₂ + k + 1), a i) ^ 2 := by ring
          _ ≤ ((C * ∏ i ∈ Finset.range (N₂ + 1), a i) ^ (2 ^ k)) ^ 2 := by
              gcongr
          _ = (C * ∏ i ∈ Finset.range (N₂ + 1), a i) ^ (2 ^ (k + 1)) := by
              rw [← pow_mul, ← pow_succ]
  have e : N₂ + 1 + k = N₂ + k + 1 := by ring
  rw [e]
  exact le_trans (hcap (N₂ + k) (by omega)) (key k)

/-- **Bounded roots from a cap:** an eventual constant-factor product cap
`a_{n+1} ≤ C·P_n` forces `a_n^{1/2^n}` to stay below the constant
`(C·P_{N₂})^{1/2^{N₂+1}}`, contradicting any tendency to `∞`. -/
lemma not_tendsto_root_of_cap (hapos : ∀ n, 0 < a n) {N₂ C : ℕ}
    (hcap : ∀ n ≥ N₂, a (n + 1) ≤ C * ∏ i ∈ Finset.range (n + 1), a i) :
    ¬ Tendsto (fun n => (a n : ℝ) ^ (1 / (2 : ℝ) ^ n)) atTop atTop := by
  intro hL
  have hC : 1 ≤ C := by
    rcases Nat.eq_zero_or_pos C with hC0 | hCpos
    · subst hC0
      have h := hcap N₂ (le_refl _)
      simp only [zero_mul, Nat.le_zero] at h
      exact absurd h (Nat.pos_iff_ne_zero.1 (hapos (N₂ + 1)))
    · exact hCpos
  set R : ℕ := C * ∏ i ∈ Finset.range (N₂ + 1), a i with hRdef
  have hR1' : 1 ≤ R := by
    rw [hRdef]
    calc (1 : ℕ) ≤ C * 1 := by rw [mul_one]; exact hC
      _ ≤ C * ∏ i ∈ Finset.range (N₂ + 1), a i := by
          gcongr
          exact Finset.prod_pos (fun i _ => hapos i)
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1'
  have hbound : ∀ k : ℕ, (a (N₂ + 1 + k) : ℝ) ^ (1 / (2 : ℝ) ^ (N₂ + 1 + k)) ≤
      (R : ℝ) ^ (1 / (2 : ℝ) ^ (N₂ + 1)) := by
    intro k
    have hk := prod_cap_iter hcap k
    have hkR : (a (N₂ + 1 + k) : ℝ) ≤ (R : ℝ) ^ (2 ^ k) := by
      have h := hk
      exact_mod_cast h
    have h1 := Real.rpow_le_rpow (by positivity) hkR
      (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ (N₂ + 1 + k))
    have h2 : ((R : ℝ) ^ (2 ^ k)) ^ (1 / (2 : ℝ) ^ (N₂ + 1 + k)) =
        (R : ℝ) ^ (1 / (2 : ℝ) ^ (N₂ + 1)) := by
      rw [← Real.rpow_natCast (R : ℝ) (2 ^ k),
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (R : ℝ))]
      congr 1
      have h2k : ((2 : ℝ) ^ (N₂ + 1 + k)) = (2 : ℝ) ^ (N₂ + 1) * (2 : ℝ) ^ k := by
        rw [← pow_add]
      have hpos1 : (2 : ℝ) ^ (N₂ + 1) ≠ 0 := by positivity
      have hpos2 : (2 : ℝ) ^ k ≠ 0 := by positivity
      push_cast
      rw [h2k]
      field_simp [hpos1, hpos2]
    calc (a (N₂ + 1 + k) : ℝ) ^ (1 / (2 : ℝ) ^ (N₂ + 1 + k))
        ≤ ((R : ℝ) ^ (2 ^ k)) ^ (1 / (2 : ℝ) ^ (N₂ + 1 + k)) := h1
      _ = (R : ℝ) ^ (1 / (2 : ℝ) ^ (N₂ + 1)) := h2
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
    (hL.eventually_gt_atTop ((R : ℝ) ^ (1 / (2 : ℝ) ^ (N₂ + 1))))
  have h1 := hk₀ (N₂ + 1 + k₀) (Nat.le_add_left k₀ (N₂ + 1))
  have h2 := hbound k₀
  linarith

/-- **No constant-factor product cap can hold eventually** under the one-sided
hypothesis: for every `C`, the inequality `a_{n+1} ≤ C·P_n` must fail
infinitely often. (Machine-checks that the naive recurrence route's cap
hypothesis is never free — the missing tail lemma is necessary.) -/
theorem cap_fails_often_of_oneSidedGrowth (hg : OneSidedGrowth a) (C : ℕ) :
    ¬ (∀ᶠ n : ℕ in atTop, a (n + 1) ≤ C * ∏ i ∈ Finset.range (n + 1), a i) := by
  intro h
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 h
  exact not_tendsto_root_of_cap hg.1 hN₂ hg.2

/-! ### The conditional irrationality theorem -/

/-- **Conditional irrationality (the recurrence-route reduction):** if the
tails are `o(1/P_n)` at every large index and for every constant — formally,
for every `C > 0`, eventually `T_{n+1} ≤ C/P_n` — then under the root-growth
hypothesis the sum is irrational. The tail hypothesis is EXACTLY the missing
lemma for the folklore form: it supplies the growth cap `a_{n+1} ≤ 2·q·P_n`
with `q` the assumed denominator, and `not_tendsto_root_of_cap` closes.
WARNING (PROGRESS-onesided.md): the hypothesis fails at spike indices; the
full folklore theorem needs Erdős's record-subsequence endgame. -/
theorem irrational_of_tail_small (hapos : ∀ n, 0 < a n)
    (hsum : Summable (fun n => 1 / (a n : ℝ)))
    (hL : Tendsto (fun n => (a n : ℝ) ^ (1 / (2 : ℝ) ^ n)) atTop atTop)
    (hts : ∀ C : ℝ, 0 < C → ∀ᶠ n : ℕ in atTop,
      (∑' i, 1 / (a (i + (n + 2)) : ℝ)) ≤
        C / ∏ i ∈ Finset.range (n + 1), (a i : ℝ)) :
    Irrational (∑' n, 1 / (a n : ℝ)) := by
  rintro ⟨r, hr⟩
  have hqpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    (hts (1 / (4 * (r.den : ℝ))) (by positivity))
  have hcap : ∀ n ≥ N₂, a (n + 1) ≤ (2 * r.den) * ∏ i ∈ Finset.range (n + 1), a i := by
    intro n hn
    have hm := one_le_prod_tail hapos hsum hr n
    have hT := hN₂ n hn
    have hPpos : (0 : ℝ) < ∏ i ∈ Finset.range (n + 1), (a i : ℝ) :=
      Finset.prod_pos (fun i _ => by exact_mod_cast hapos i)
    have hqP : (0 : ℝ) < (r.den : ℝ) * ∏ i ∈ Finset.range (n + 1), (a i : ℝ) :=
      mul_pos hqpos hPpos
    have hT' : (∑' i, 1 / (a (i + (n + 2)) : ℝ)) ≤
        1 / (2 * (r.den : ℝ) * ∏ i ∈ Finset.range (n + 1), (a i : ℝ)) := by
      calc (∑' i, 1 / (a (i + (n + 2)) : ℝ))
          ≤ (1 / (4 * (r.den : ℝ))) / ∏ i ∈ Finset.range (n + 1), (a i : ℝ) := hT
        _ = 1 / (4 * (r.den : ℝ) * ∏ i ∈ Finset.range (n + 1), (a i : ℝ)) := by
            rw [div_div]
        _ ≤ 1 / (2 * (r.den : ℝ) * ∏ i ∈ Finset.range (n + 1), (a i : ℝ)) := by
            apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * (r.den : ℝ) *
              ∏ i ∈ Finset.range (n + 1), (a i : ℝ))
            nlinarith [hqP]
    have hcapR := cap_of_tail_small hapos hsum
      (by exact_mod_cast r.den_pos : (1 : ℝ) ≤ (r.den : ℝ)) n hm hT'
    exact_mod_cast hcapR
  exact not_tendsto_root_of_cap hapos hcap hL

/-! ### Borel's record lemma (Erdős 1975, eq. (14)) -/

/-- **Near-record indices exist** (Erdős 1975, eq. (14); the idea is credited
to Borel): if `L → ∞` and `L ≥ 0`, then for every `k₀` there is a `k ≥ k₀`
whose next term beats every scaled-down previous term:
`L_{k+1} > (1 - 1/(k+1)²)·L_j` for all `j ≤ k` — equivalently
`L_{k+1} > (1 - 1/(k+1)²)·max_{j ≤ k} L_j` (since `1 - 1/(k+1)² ≥ 0`, the
two forms are equivalent).
Proof: otherwise each new term from `k₀` on is below the scaled value of some
earlier term, hence below some value of the initial segment `[0, k₀]` — so `L`
is bounded, contradicting `L → ∞`. -/
theorem exists_near_record {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hL0 : ∀ n, 0 ≤ L n) (k₀ : ℕ) :
    ∃ k ≥ k₀, ∀ j ≤ k, (1 - 1 / ((k : ℝ) + 1) ^ 2) * L j < L (k + 1) := by
  by_contra h
  push Not at h
  -- every term after `k₀` is below some initial-segment value
  have hbound : ∀ j : ℕ, ∀ m ≤ j, ∃ i ≤ k₀, L (k₀ + 1 + m) ≤ L i := by
    intro j
    induction j with
    | zero =>
        intro m hm
        rw [Nat.le_zero.1 hm]
        obtain ⟨i, hi, hLi⟩ := h k₀ (le_refl _)
        refine ⟨i, hi, le_trans hLi ?_⟩
        have hc : (0 : ℝ) ≤ 1 / ((k₀ : ℝ) + 1) ^ 2 := by positivity
        have hLi0 := hL0 i
        nlinarith [hc, hLi0]
    | succ j ih =>
        intro m hm
        rcases (Nat.le_iff_lt_or_eq.1 hm) with hlt | heq
        · exact ih m (by omega)
        · subst heq
          obtain ⟨i', hi', hLi'⟩ := h (k₀ + 1 + j) (by omega)
          have hfac : (1 - 1 / ((↑(k₀ + 1 + j) : ℝ) + 1) ^ 2) * L i' ≤ L i' := by
            have hc : (0 : ℝ) ≤ 1 / ((↑(k₀ + 1 + j) : ℝ) + 1) ^ 2 := by positivity
            have hLi0 := hL0 i'
            nlinarith [hc, hLi0]
          have hstep : L (k₀ + 1 + (j + 1)) ≤ L i' := by
            have e : k₀ + 1 + (j + 1) = (k₀ + 1 + j) + 1 := by ring
            rw [e]
            exact le_trans hLi' hfac
          rcases (Nat.le_iff_lt_or_eq.1 hi') with hlt' | heq'
          · rcases (lt_or_ge i' (k₀ + 1)) with hik | hik
            · exact ⟨i', Nat.lt_succ_iff.1 hik, hstep⟩
            · obtain ⟨i, hi, hLi⟩ := ih (i' - (k₀ + 1)) (by omega)
              have ei : k₀ + 1 + (i' - (k₀ + 1)) = i' := by omega
              rw [ei] at hLi
              exact ⟨i, hi, le_trans hstep hLi⟩
          · obtain ⟨i, hi, hLi⟩ := ih j (le_refl j)
            rw [heq'] at hstep
            exact ⟨i, hi, le_trans hstep hLi⟩
  set B := (Finset.range (k₀ + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos k₀)⟩ L
    with hBdef
  have hBi : ∀ i ≤ k₀, L i ≤ B := by
    intro i hi
    have hmem : i ∈ Finset.range (k₀ + 1) := Finset.mem_range.2 (by omega)
    exact Finset.le_sup' L hmem
  have hbound' : ∀ n ≥ k₀ + 1, L n ≤ B := by
    intro n hn
    obtain ⟨i, hi, hLi⟩ := hbound (n - (k₀ + 1)) (n - (k₀ + 1)) (le_refl _)
    have e : k₀ + 1 + (n - (k₀ + 1)) = n := by omega
    rw [e] at hLi
    exact le_trans hLi (hBi i hi)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (hL.eventually_gt_atTop B)
  have h1 := hn₁ (max n₁ (k₀ + 1)) (le_max_left _ _)
  have h2 := hbound' (max n₁ (k₀ + 1)) (le_max_right _ _)
  linarith

end Erdos263
