/-
  Stage F — Criterion + headline P5.1, Thm 1.1 (`criterion_holds`, `erdos_477`).
  THE HEADLINE. Requires Stages D + E.

  This file proves the two assembly steps as SUPPORT lemmas, each taking its one
  not-yet-proved input as an EXPLICIT ARGUMENT (the frozen `criterion_holds` /
  `erdos_477` themselves never gain a hypothesis — a later iteration discharges
  the arguments with `badShift_bound_proof` / `criterion_holds_proof`):

  * `criterion_holds_of_badShift` (F1, SKETCH §8.1 / P5.1 / paper's Prop 5.2)
  * `erdos_477_of_criterion`      (F2, SKETCH §8.2 / paper's Thm 1.1)
-/
import Erdos477.Defs
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.Greedy.Basic

namespace Erdos477

open scoped BigOperators Classical

/-! ### F1 — the criterion `(H)` holds for `Bset`, given the bad-shift estimate -/

/-- Membership in the bad-shift set, unfolded. -/
theorem mem_Sset {c T t : ℤ} : t ∈ Sset c T ↔ t ∈ Finset.Icc (-T) T ∧ t ^ 13 - c ∈ Dset := by
  simp [Sset, Finset.mem_filter]

/-- `Sset c T` sits inside the two-sided interval `Icc (-T) T`. -/
theorem Sset_subset (c T : ℤ) : Sset c T ⊆ Finset.Icc (-T) T := Finset.filter_subset _ _

/-- The number of integers `t` with `|t| ≤ T` is exactly `2T + 1` (`T ≥ 0`). -/
theorem card_Icc_neg (T : ℤ) (hT : 0 ≤ T) :
    (((Finset.Icc (-T) T).card : ℤ)) = 2 * T + 1 := by
  rw [Int.card_Icc]
  rw [Int.toNat_of_nonneg (by omega)]
  ring

/-- Elementary sixth-power comparison: if `0 ≤ K` and `K ^ 6 < x` with `1 ≤ x`, then
`K * x ^ (5/6) < x`.  (This is the strict step of the pigeonhole count.) -/
theorem mul_rpow_lt_self {K x : ℝ} (_hK : 0 ≤ K) (hx : 1 ≤ x) (hKx : K ^ 6 < x) :
    K * x ^ ((5 : ℝ) / 6) < x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hrp : (0 : ℝ) ≤ x ^ ((5 : ℝ) / 6) := Real.rpow_nonneg hx0.le _
  have hpow : (x ^ ((5 : ℝ) / 6)) ^ (6 : ℕ) = x ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast (x ^ ((5 : ℝ) / 6)) 6, ← Real.rpow_mul hx0.le]
    norm_num
  have hlt : (K * x ^ ((5 : ℝ) / 6)) ^ (6 : ℕ) < x ^ (6 : ℕ) := by
    have h5 : (0 : ℝ) < x ^ (5 : ℕ) := pow_pos hx0 5
    calc (K * x ^ ((5 : ℝ) / 6)) ^ (6 : ℕ)
        = K ^ 6 * x ^ (5 : ℕ) := by rw [mul_pow, hpow]
      _ < x * x ^ (5 : ℕ) := by exact mul_lt_mul_of_pos_right hKx h5
      _ = x ^ (6 : ℕ) := by ring
  exact lt_of_pow_lt_pow_left₀ 6 hx0.le hlt

/-- **F1 (SKETCH §8.1, P5.1 / paper's Prop 5.2).** Given the bad-shift estimate
`hBS` for every `c ∉ Bset`, the set of thirteenth powers satisfies the greedy
criterion `(H)`: for every finite `C ⊆ ℤ ∖ Bset` there is `b ∈ Bset` with
`c - b ∉ Dset` for all `c ∈ C`. -/
theorem criterion_holds_of_badShift
    (hBS : ∀ c : ℤ, c ∉ Bset → ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6)) :
    ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) → ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset := by
  intro C hC
  classical
  -- A total choice of constants: the genuine `K_c` for `c ∈ C`, a dummy `1` elsewhere.
  have key : ∀ c : ℤ, ∃ K : ℝ, 1 ≤ K ∧ (c ∈ C → ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6)) := by
    intro c
    by_cases h : c ∈ C
    · obtain ⟨K, hK1, hK2⟩ := hBS c (hC c h)
      exact ⟨K, hK1, fun _ => hK2⟩
    · exact ⟨1, le_refl 1, fun hh => absurd hh h⟩
  choose KK hKK1 hKK2 using key
  -- `K := ∑_{c ∈ C} K_c`, over ALL of `C`.
  set K : ℝ := ∑ c ∈ C, KK c with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun c _ => le_trans zero_le_one (hKK1 c)
  -- an integer `T ≥ 1` with `(T : ℝ) > K ^ 6`
  set T : ℤ := max 1 (⌈K ^ 6⌉ + 1) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTge : ⌈K ^ 6⌉ + 1 ≤ T := le_max_right _ _
  have hKT : K ^ 6 < (T : ℝ) := by
    have h1 : K ^ 6 ≤ (⌈K ^ 6⌉ : ℝ) := Int.le_ceil _
    have h2 : ((⌈K ^ 6⌉ + 1 : ℤ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTge
    push_cast at h2
    linarith
  have hT1R : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT1
  -- the union of all bad sets
  set U : Finset ℤ := C.biUnion (fun c => Sset c T) with hUdef
  have hUsub : U ⊆ Finset.Icc (-T) T :=
    Finset.biUnion_subset.mpr fun c _ => Sset_subset c T
  -- counting: `|U| ≤ K * T ^ (5/6) < T < 2T + 1 = #Icc (-T) T`
  have hcard1 : (U.card : ℝ) ≤ ∑ c ∈ C, ((Sset c T).card : ℝ) := by
    have := Finset.card_biUnion_le (s := C) (t := fun c => Sset c T)
    calc (U.card : ℝ) ≤ ((∑ c ∈ C, (Sset c T).card : ℕ) : ℝ) := by exact_mod_cast this
      _ = ∑ c ∈ C, ((Sset c T).card : ℝ) := by push_cast; ring
  have hcard2 : ∑ c ∈ C, ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := by
    calc ∑ c ∈ C, ((Sset c T).card : ℝ)
        ≤ ∑ c ∈ C, KK c * (T : ℝ) ^ ((5 : ℝ) / 6) :=
          Finset.sum_le_sum fun c hc => hKK2 c hc T hT1
      _ = K * (T : ℝ) ^ ((5 : ℝ) / 6) := by rw [hKdef, Finset.sum_mul]
  have hstrict : (U.card : ℝ) < (T : ℝ) :=
    lt_of_le_of_lt (le_trans hcard1 hcard2) (mul_rpow_lt_self hK0 hT1R hKT)
  have hIcc : ((Finset.Icc (-T) T).card : ℤ) = 2 * T + 1 := card_Icc_neg T (by omega)
  have hlt : U.card < (Finset.Icc (-T) T).card := by
    have h1 : ((Finset.Icc (-T) T).card : ℝ) = 2 * (T : ℝ) + 1 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hIcc
    have h2 : (U.card : ℝ) < ((Finset.Icc (-T) T).card : ℝ) := by
      rw [h1]; linarith
    exact_mod_cast h2
  -- pigeonhole: some `t₀ ∈ Icc (-T) T` is bad for no `c ∈ C`
  have hex : ∃ t₀ ∈ Finset.Icc (-T) T, t₀ ∉ U := by
    by_contra h
    have hsub : Finset.Icc (-T) T ⊆ U := by
      intro t ht
      by_contra htU
      exact h ⟨t, ht, htU⟩
    exact absurd (Finset.card_le_card hsub) (not_le.mpr hlt)
  obtain ⟨t₀, ht₀mem, ht₀not⟩ := hex
  refine ⟨t₀ ^ 13, ⟨t₀, rfl⟩, ?_⟩
  intro c hc hmem
  -- `c - t₀ ^ 13 ∈ Dset` would put `t₀` into `Sset c T`, hence into `U`.
  have h' : t₀ ^ 13 - c ∈ Dset := (mem_D_symm_shift c t₀).mp hmem
  exact ht₀not (Finset.mem_biUnion.mpr ⟨c, hc, mem_Sset.mpr ⟨ht₀mem, h'⟩⟩)

/-! ### F2 — the headline, given the criterion -/

/-- **F2 (SKETCH §8.2, paper's Theorem 1.1).** Given the criterion `hcrit`, the
thirteenth powers tile `ℤ`: there is `A ⊆ ℤ` such that every `n` is UNIQUELY
`a + m ^ 13` with `a ∈ A`, `m ∈ ℤ`. -/
theorem erdos_477_of_criterion
    (hcrit : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) → ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n := by
  -- bridge the concrete `Dset` to the abstract difference set of `greedy_tiling`
  have H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x - y} := by
    intro C hC
    obtain ⟨b, hb, hcb⟩ := hcrit C hC
    refine ⟨b, hb, fun c hc => ?_⟩
    rw [← dset_eq_sub]
    exact hcb c hc
  obtain ⟨A, hA⟩ := greedy_tiling_proof Bset H
  refine ⟨A, fun n => ?_⟩
  obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, huniq⟩ := hA n
  obtain ⟨m, rfl⟩ := hb
  refine ⟨(a, m), ⟨ha, hab⟩, ?_⟩
  rintro ⟨a', m'⟩ ⟨ha', hab'⟩
  have h := huniq (a', m' ^ 13) ⟨ha', ⟨m', rfl⟩, hab'⟩
  have h1 : a' = a := congrArg Prod.fst h
  have h2 : m' ^ 13 = m ^ 13 := congrArg Prod.snd h
  have h3 : m' = m := pow13_eq_iff.mp h2
  simp [h1, h3]

end Erdos477
