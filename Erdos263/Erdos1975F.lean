/-
Erdos1975F.lean — SESSION 6 (2026-08-02): the SORTING-LEMMA route; closes the
site-literal no-monotonicity folklore form.

New file; NO refactor of any earlier file. The run-4 headline
`irrational_of_oneSidedGrowth_monotone` (Erdos1975D.lean) is USED, not touched.

THE ARGUMENT (orchestrator's sorting lemma, paper-verified in
PROGRESS-onesided.md session 6 — no flaw found):
* `countLE a X` = #{i | a_i ≤ X} (finite under one-sided growth);
* `asort a hf m` = the least value v with countLE a v ≥ m+1 — the
  non-decreasing rearrangement, multiplicity built in:
  `asort_le_iff` gives {m | asort m ≤ X} equal-in-cardinal to {i | a_i ≤ X};
* growth transfers (`asort_core`): if `a_i ≥ (2B)^{2^i}` for i ≥ N, then for
  m ≥ N the sorted value `asort m > B^{2^m}` — otherwise the ≥ m+1 indices
  with a_i ≤ asort m would all lie in Iio N ∪ Ico N m, at most m of them;
* `sortPerm`: the fiber equivs (equal ncard per value) assemble via
  `Equiv.sigmaCongrRight` into a bijection φ with a = asort ∘ φ, so
  `Equiv.tsum_eq` identifies the two reciprocal sums;
* corollary `erdos_263_one_sided_folklore_proof`: asort is Monotone with
  OneSidedGrowth, so Erdos1975D's headline applies; rewrite the tsum.

ZERO sorry/admit/axiom in this file.
-/
import Mathlib
import Erdos263.Erdos1975D

open Filter Topology Finset
open scoped Topology

namespace Erdos263

variable {a : ℕ → ℕ}

/-- The counting function: number of indices with `a i ≤ X`. -/
noncomputable def countLE (a : ℕ → ℕ) (X : ℕ) : ℕ := Set.ncard {i : ℕ | a i ≤ X}

/-- `(Iio k).ncard = k` for naturals. -/
lemma ncard_Iio_nat (k : ℕ) : (Set.Iio k).ncard = k := by
  rw [Set.ncard_eq_toFinset_card _ (Set.finite_Iio k)]
  have hT : (Set.finite_Iio k).toFinset = Finset.range k := by
    ext j
    simp [Set.Finite.mem_toFinset, Finset.mem_range, Set.mem_Iio]
  rw [hT, Finset.card_range]

/-- The minimum in `asort` is over a nonempty set: the first `m+1` indices
all have value at most their sup. -/
lemma asort_exists (a : ℕ → ℕ) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) (m : ℕ) :
    ∃ X : ℕ, m + 1 ≤ countLE a X := by
  refine ⟨(Finset.range (m + 1)).sup a, ?_⟩
  have hsub : Set.Iio (m + 1) ⊆ {i : ℕ | a i ≤ (Finset.range (m + 1)).sup a} := by
    intro j hj
    simp only [Set.mem_Iio] at hj
    simp only [Set.mem_setOf_eq]
    exact Finset.le_sup (Finset.mem_range.2 hj)
  have h1 := Set.ncard_le_ncard hsub (hf _)
  rw [ncard_Iio_nat] at h1
  exact h1

/-- **The non-decreasing rearrangement** of `a` (with multiplicity):
`asort a hf m` is the least value attained by at least `m+1` indices. -/
noncomputable def asort (a : ℕ → ℕ) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite)
    (m : ℕ) : ℕ :=
  Nat.find (asort_exists a hf m)

/-- The defining equivalence of the rearrangement. -/
lemma asort_le_iff (a : ℕ → ℕ) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) (m X : ℕ) :
    asort a hf m ≤ X ↔ m + 1 ≤ countLE a X := by
  constructor
  · intro h
    have hsub : {i : ℕ | a i ≤ asort a hf m} ⊆ {i : ℕ | a i ≤ X} := by
      intro i hi
      simp only [Set.mem_setOf_eq] at hi ⊢
      exact le_trans hi h
    have h1 : m + 1 ≤ countLE a (asort a hf m) := Nat.find_spec (asort_exists a hf m)
    exact le_trans h1 (Set.ncard_le_ncard hsub (hf X))
  · intro h
    exact Nat.find_min' (asort_exists a hf m) h

/-- The rearrangement is non-decreasing. -/
lemma asort_mono (a : ℕ → ℕ) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) :
    Monotone (asort a hf) := by
  intro m m' hmm'
  rw [asort_le_iff a hf m (asort a hf m')]
  exact le_trans (by omega) (Nat.find_spec (asort_exists a hf m'))

/-- The rearrangement stays positive. -/
lemma asort_pos (hapos : ∀ n, 0 < a n) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite)
    (m : ℕ) : 0 < asort a hf m := by
  have h0 : countLE a 0 = 0 := by
    have he : {i : ℕ | a i ≤ 0} = (∅ : Set ℕ) := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      have := hapos i
      omega
    rw [countLE, he, Set.ncard_empty]
  by_contra h
  push_neg at h
  have h2 := (asort_le_iff a hf m 0).1 h
  rw [h0] at h2
  omega

/-- The sorted window below `X` is finite. -/
lemma finite_asort_le (a : ℕ → ℕ) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) (X : ℕ) :
    {m : ℕ | asort a hf m ≤ X}.Finite := by
  refine Set.Finite.subset (Set.finite_Iio (countLE a X)) ?_
  intro m hm
  simp only [Set.mem_setOf_eq] at hm
  have h := (asort_le_iff a hf m X).1 hm
  simp only [Set.mem_Iio]
  omega

/-- **The count identity:** the number of sorted positions with value ≤ X
equals the number of indices with value ≤ X. -/
lemma ncard_asort_le (a : ℕ → ℕ) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) (X : ℕ) :
    Set.ncard {m : ℕ | asort a hf m ≤ X} = countLE a X := by
  have hfin := finite_asort_le a hf X
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hT : hfin.toFinset = Finset.range (countLE a X) := by
    ext m
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_range]
    constructor
    · intro h
      have h2 := (asort_le_iff a hf m X).1 h
      omega
    · intro h
      exact (asort_le_iff a hf m X).2 (by omega)
  rw [hT, Finset.card_range]

/-- **Fiber equality:** each value occurs exactly as often in `asort` as in
`a` (multiplicity preservation). -/
lemma ncard_fiber_eq (hapos : ∀ n, 0 < a n) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite)
    (x : ℕ) :
    Set.ncard {m : ℕ | asort a hf m = x} = Set.ncard {i : ℕ | a i = x} := by
  by_cases hx : x = 0
  · subst hx
    have e1 : {m : ℕ | asort a hf m = 0} = (∅ : Set ℕ) := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      have h := asort_pos hapos hf m
      omega
    have e2 : {i : ℕ | a i = 0} = (∅ : Set ℕ) := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      have h := hapos i
      omega
    rw [e1, e2]
  · have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hx
    have key1 : {m : ℕ | asort a hf m = x} =
        {m : ℕ | asort a hf m ≤ x} \ {m : ℕ | asort a hf m ≤ x - 1} := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_diff]
      omega
    have key2 : {i : ℕ | a i = x} = {i : ℕ | a i ≤ x} \ {i : ℕ | a i ≤ x - 1} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_diff]
      omega
    have hsub1 : {m : ℕ | asort a hf m ≤ x - 1} ⊆ {m : ℕ | asort a hf m ≤ x} := by
      intro m hm
      simp only [Set.mem_setOf_eq] at hm ⊢
      omega
    have hsub2 : {i : ℕ | a i ≤ x - 1} ⊆ {i : ℕ | a i ≤ x} := by
      intro i hi
      simp only [Set.mem_setOf_eq] at hi ⊢
      omega
    rw [key1, key2, Set.ncard_sdiff hsub1 (finite_asort_le a hf (x - 1)),
      Set.ncard_sdiff hsub2 (hf (x - 1)), ncard_asort_le a hf x,
      ncard_asort_le a hf (x - 1)]
    rfl

/-- Small-value index sets are finite under one-sided growth (each value has
finitely many predecessors): eventually `a i ≥ (X+2)^{2^i} > X`. -/
lemma finite_smallSet_of_oneSidedGrowth (hg : OneSidedGrowth a) (X : ℕ) :
    {i : ℕ | a i ≤ X}.Finite := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hg.2) (X + 2)
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi
  by_contra hNimem
  have hNi : N ≤ i := not_lt.1 (by simpa using hNimem)
  have hge : (X + 2 : ℝ) ≤ (a i : ℝ) ^ (1 / (2 : ℝ) ^ i) := hN i hNi
  have hbase : (0 : ℝ) ≤ (a i : ℝ) := by positivity
  have h2n : (0 : ℝ) < (2 : ℝ) ^ i := by positivity
  have key : ((a i : ℝ) ^ (1 / (2 : ℝ) ^ i)) ^ (2 ^ i) = (a i : ℝ) := by
    have hcast : (((2 ^ i : ℕ)) : ℝ) = (2 : ℝ) ^ i := by push_cast; rfl
    rw [← Real.rpow_natCast ((a i : ℝ) ^ (1 / (2 : ℝ) ^ i)) (2 ^ i), hcast,
      ← Real.rpow_mul hbase]
    have hmul : (1 / (2 : ℝ) ^ i) * (2 : ℝ) ^ i = 1 := div_mul_cancel₀ (1 : ℝ) h2n.ne'
    rw [hmul, Real.rpow_one]
  have hle : (X + 2 : ℝ) ^ (2 ^ i) ≤ (a i : ℝ) := by
    have hle' : (X + 2 : ℝ) ^ (2 ^ i) ≤ ((a i : ℝ) ^ (1 / (2 : ℝ) ^ i)) ^ (2 ^ i) :=
      pow_le_pow_left₀ (by positivity) hge (2 ^ i)
    rwa [key] at hle'
  have hX2 : (X + 2 : ℝ) ≤ (X + 2 : ℝ) ^ (2 ^ i) := by
    calc (X + 2 : ℝ) = (X + 2 : ℝ) ^ (1 : ℕ) := by rw [pow_one]
      _ ≤ (X + 2 : ℝ) ^ (2 ^ i) := pow_le_pow_right₀ (by
        have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
        linarith) Nat.one_le_two_pow
  have hcontra : (X + 2 : ℝ) ≤ (a i : ℝ) := le_trans hX2 hle
  have hiX : (a i : ℝ) ≤ (X : ℝ) := by exact_mod_cast hi
  linarith

/-- **The counting core** (orchestrator's step ii): for `B ≥ 2`, eventually
the sorted `2^m`-th root exceeds `B`. If `asort m ≤ B^{2^m}` for `m ≥ N`,
then the `≥ m+1` indices with `a i ≤ asort m` would all satisfy `i < N` or
`N ≤ i < m` — at most `m` of them. -/
lemma asort_core (hg : OneSidedGrowth a) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite)
    (B : ℝ) (hB : 2 ≤ B) :
    ∃ N : ℕ, ∀ m ≥ N, B ≤ (asort a hf m : ℝ) ^ (1 / (2 : ℝ) ^ m) := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hg.2) (2 * B)
  have hraise : ∀ i ≥ N, (2 * B : ℝ) ^ (2 ^ i) ≤ (a i : ℝ) := by
    intro i hi
    have hge : (2 * B : ℝ) ≤ (a i : ℝ) ^ (1 / (2 : ℝ) ^ i) := hN i hi
    have hbase : (0 : ℝ) ≤ (a i : ℝ) := by positivity
    have h2n : (0 : ℝ) < (2 : ℝ) ^ i := by positivity
    have key : ((a i : ℝ) ^ (1 / (2 : ℝ) ^ i)) ^ (2 ^ i) = (a i : ℝ) := by
      have hcast : (((2 ^ i : ℕ)) : ℝ) = (2 : ℝ) ^ i := by push_cast; rfl
      rw [← Real.rpow_natCast ((a i : ℝ) ^ (1 / (2 : ℝ) ^ i)) (2 ^ i), hcast,
        ← Real.rpow_mul hbase]
      have hmul : (1 / (2 : ℝ) ^ i) * (2 : ℝ) ^ i = 1 := div_mul_cancel₀ (1 : ℝ) h2n.ne'
      rw [hmul, Real.rpow_one]
    have hle' : (2 * B : ℝ) ^ (2 ^ i) ≤ ((a i : ℝ) ^ (1 / (2 : ℝ) ^ i)) ^ (2 ^ i) :=
      pow_le_pow_left₀ (by positivity) hge (2 ^ i)
    rwa [key] at hle'
  refine ⟨N, fun m hm => ?_⟩
  have h0 : (0 : ℝ) ≤ B := by linarith
  have hgt : (B : ℝ) ^ (2 ^ m) < (asort a hf m : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have hcount : m + 1 ≤ countLE a (asort a hf m) := Nat.find_spec (asort_exists a hf m)
    have hle : countLE a (asort a hf m) ≤ N + (m - N) := by
      have hfin := hf (asort a hf m)
      rw [countLE, Set.ncard_eq_toFinset_card _ hfin]
      have hsub : hfin.toFinset ⊆ Finset.range N ∪ Finset.Ico N m := by
        intro i hi
        rw [Set.Finite.mem_toFinset] at hi
        simp only [Set.mem_setOf_eq] at hi
        by_cases hN2 : i < N
        · exact Finset.mem_union_left _ (Finset.mem_range.2 hN2)
        · push_neg at hN2
          have him : i < m := by
            have h1 : (2 * B : ℝ) ^ (2 ^ i) ≤ B ^ (2 ^ m) := by
              have h2 : (a i : ℝ) ≤ (asort a hf m : ℝ) := by exact_mod_cast hi
              exact le_trans (hraise i hN2) (le_trans h2 hcon)
            have hlog : Real.log ((2 * B : ℝ) ^ (2 ^ i)) ≤ Real.log (B ^ (2 ^ m)) :=
              Real.log_le_log (by positivity) h1
            rw [Real.log_pow, Real.log_pow] at hlog
            have hLB : (0 : ℝ) < Real.log B := Real.log_pos (by linarith)
            have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
            have hL2B : Real.log (2 * B) = Real.log 2 + Real.log B :=
              Real.log_mul (by norm_num) (by linarith : (B : ℝ) ≠ 0)
            have hLB2 : Real.log B < Real.log (2 * B) := by rw [hL2B]; linarith
            have h3 : ((2 ^ i : ℕ) : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
              have hL2Bpos : (0 : ℝ) < Real.log (2 * B) := by linarith
              have h4 : ((2 ^ i : ℕ) : ℝ) * Real.log (2 * B) <
                  ((2 ^ m : ℕ) : ℝ) * Real.log (2 * B) := by
                calc ((2 ^ i : ℕ) : ℝ) * Real.log (2 * B)
                    ≤ ((2 ^ m : ℕ) : ℝ) * Real.log B := hlog
                  _ < ((2 ^ m : ℕ) : ℝ) * Real.log (2 * B) :=
                      mul_lt_mul_of_pos_left hLB2 (by positivity)
              exact lt_of_mul_lt_mul_right h4 (le_of_lt hL2Bpos)
            have h5 : (2 ^ i : ℕ) < 2 ^ m := by exact_mod_cast h3
            by_contra hmi
            push_neg at hmi
            have h6 : (2 : ℕ) ^ m ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) hmi
            omega
          exact Finset.mem_union_right _ (Finset.mem_Ico.2 ⟨hN2, him⟩)
      calc (hfin.toFinset).card ≤ (Finset.range N ∪ Finset.Ico N m).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.range N).card + (Finset.Ico N m).card := Finset.card_union_le _ _
        _ = N + (m - N) := by rw [Finset.card_range, Nat.card_Ico]
    have hmN : N ≤ m := hm
    omega
  have key2 : ((B : ℝ) ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ m) = B := by
    rw [← Real.rpow_natCast B (2 ^ m)]
    have hcast : (((2 ^ m : ℕ)) : ℝ) = (2 : ℝ) ^ m := by push_cast; rfl
    rw [hcast, ← Real.rpow_mul h0]
    have h2n : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have hmul : (2 : ℝ) ^ m * (1 / (2 : ℝ) ^ m) = 1 := mul_one_div_cancel h2n.ne'
    rw [hmul, Real.rpow_one]
  rw [← key2]
  exact Real.rpow_le_rpow (pow_nonneg h0 _) (le_of_lt hgt) (by positivity)

/-- **Growth transfers to the rearrangement** (the sorting lemma proper). -/
lemma asort_tendsto (hg : OneSidedGrowth a) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) :
    Tendsto (fun m => (asort a hf m : ℝ) ^ (1 / (2 : ℝ) ^ m)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  obtain ⟨N, hN⟩ := asort_core hg hf (max B 2) (le_max_right B 2)
  exact ⟨N, fun m hm => le_trans (le_max_left B 2) (hN m hm)⟩

/-- The `a`-fiber of a value is finite. -/
lemma finite_fiber_a (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) (x : ℕ) :
    {i : ℕ | a i = x}.Finite :=
  (hf x).subset (fun i hi => by simpa using le_of_eq hi)

/-- The `asort`-fiber of a value is finite. -/
lemma finite_fiber_asort (hapos : ∀ n, 0 < a n) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite)
    (x : ℕ) : {m : ℕ | asort a hf m = x}.Finite :=
  (finite_asort_le a hf x).subset (fun m hm => by simpa using le_of_eq hm)

/-- **The fiber equiv** at each value (equal finite cardinalities). -/
noncomputable def fiberEquiv (hapos : ∀ n, 0 < a n)
    (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) (x : ℕ) :
    {i : ℕ // a i = x} ≃ {m : ℕ // asort a hf m = x} := by
  haveI : Fintype {i : ℕ // a i = x} := (finite_fiber_a hf x).fintype
  haveI : Fintype {m : ℕ // asort a hf m = x} := (finite_fiber_asort hapos hf x).fintype
  exact Fintype.equivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    show Nat.card ↥{i : ℕ | a i = x} = Nat.card ↥{m : ℕ | asort a hf m = x}
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact (ncard_fiber_eq hapos hf x).symm)

/-- The fiber equivs packaged over all values (dependency-free transport). -/
noncomputable def sortSigmaEquiv (hapos : ∀ n, 0 < a n)
    (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) :
    (Σ x : ℕ, {i : ℕ // a i = x}) ≃ (Σ x : ℕ, {m : ℕ // asort a hf m = x}) :=
  Equiv.sigmaCongrRight (fun x => fiberEquiv hapos hf x)

/-- The assembled map `i ↦ sorted position of i` is a bijection: it is the
composite of the value-tagging bijection, the fiber equiv, and the
position projection. -/
lemma sortPerm_bijective (hapos : ∀ n, 0 < a n)
    (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) :
    Function.Bijective (fun i => ((fiberEquiv hapos hf (a i)) ⟨i, rfl⟩).1) := by
  have hι : Function.Bijective
      (fun i : ℕ => (⟨a i, ⟨i, rfl⟩⟩ : Σ x : ℕ, {i : ℕ // a i = x})) := by
    constructor
    · intro i₁ i₂ h
      exact congrArg (fun s => s.2.1) h
    · rintro ⟨x, ⟨i, hi⟩⟩
      cases hi
      exact ⟨i, rfl⟩
  have hρ : Function.Bijective
      (fun s : (Σ x : ℕ, {m : ℕ // asort a hf m = x}) => s.2.1) := by
    constructor
    · rintro ⟨x, ⟨m, hm⟩⟩ ⟨y, ⟨n, hn⟩⟩ h
      have hmn : m = n := h
      subst hmn
      have hxy : x = y := hm.symm.trans hn
      subst hxy
      rfl
    · intro m
      exact ⟨⟨asort a hf m, ⟨m, rfl⟩⟩, rfl⟩
  have hcomp := hρ.comp ((sortSigmaEquiv hapos hf).bijective.comp hι)
  exact hcomp

/-- **The sorting permutation** of ℕ with `a = asort ∘ sortPerm`. -/
noncomputable def sortPerm (hapos : ∀ n, 0 < a n)
    (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) : ℕ ≃ ℕ :=
  Equiv.ofBijective _ (sortPerm_bijective hapos hf)

/-- The permutation indeed re-sorts: `asort (sortPerm i) = a i`. -/
lemma sortPerm_spec (hapos : ∀ n, 0 < a n) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite)
    (i : ℕ) : asort a hf (sortPerm hapos hf i) = a i := by
  show asort a hf ((fiberEquiv hapos hf (a i)) ⟨i, rfl⟩).1 = a i
  exact ((fiberEquiv hapos hf (a i)) ⟨i, rfl⟩).2

/-- **Tsum invariance under rearrangement** (positive terms): the reciprocal
sums of `a` and of its non-decreasing rearrangement coincide. -/
lemma tsum_asort_eq (hapos : ∀ n, 0 < a n) (hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite) :
    (∑' i, 1 / (a i : ℝ)) = ∑' m, 1 / (asort a hf m : ℝ) := by
  have h2 : (∑' i, 1 / (a i : ℝ)) =
      ∑' i, (fun m => 1 / (asort a hf m : ℝ)) (sortPerm hapos hf i) :=
    tsum_congr (fun i => by
      show 1 / (a i : ℝ) = 1 / (asort a hf (sortPerm hapos hf i) : ℝ)
      rw [sortPerm_spec hapos hf i])
  rw [h2]
  exact (sortPerm hapos hf).tsum_eq (fun m => 1 / (asort a hf m : ℝ))

/-- **THE NO-MONOTONICITY FOLKLORE FORM, CLOSED:** the site-literal statement
`erdos_263_one_sided_folklore` holds — every positive integer sequence with
`a_n^{1/2^n} → ∞` has irrational reciprocal sum, no monotonicity assumed.
Via the sorting lemma (`asort_tendsto`), tsum invariance (`tsum_asort_eq`),
and the run-4 monotone headline `irrational_of_oneSidedGrowth_monotone`. -/
theorem erdos_263_one_sided_folklore_proof : erdos_263_one_sided_folklore := by
  intro a hg
  have hf : ∀ X : ℕ, {i : ℕ | a i ≤ X}.Finite := finite_smallSet_of_oneSidedGrowth hg
  have hmono : Monotone (asort a hf) := asort_mono a hf
  have hsg : OneSidedGrowth (asort a hf) := ⟨asort_pos hg.1 hf, asort_tendsto hg hf⟩
  have hirr := irrational_of_oneSidedGrowth_monotone hsg hmono
  rwa [← tsum_asort_eq hg.1 hf] at hirr

end Erdos263
