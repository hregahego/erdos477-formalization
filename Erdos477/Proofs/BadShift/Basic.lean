/-
  Stage E — Bad-shift estimate P3.1 (BLUEPRINT Stage E, SKETCH §6). THE HEART.

  This file proves the FULL bad-shift estimate

    `badShift_bound_of_hexcl (c) (hc : c ∉ Bset) (hexcl) :
        ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T → ((Sset c T).card : ℝ) ≤ K * T ^ (5/6)`

  i.e. the conclusion of the frozen `badShift_bound` VERBATIM, with the
  degree-≤ 1 exclusion hypothesis `hexcl` of `heath_brown_diagonal_13` taken as
  an explicit argument of THIS SUPPORT LEMMA ONLY (Stage C proves it; iteration 3
  wires `badShift_bound_proof c hc := badShift_bound_of_hexcl c hc
  (no_linear_param_proof c hc)`). The frozen statement itself never gains a
  hypothesis.

  Structure (BLUEPRINT E1–E4 / SKETCH §6 Steps 0–4):
    E1  `pairOf`, `Phi`, `Phi_inj`, `Phi_sum`, `pairOf_ne`  — bad shift ↦ solution
    E2  `coord_bound`                                       — the `T^(13/12)` box
    E3  the single invocation of `heath_brown_diagonal_13` with `hexcl`
    E4  injective count + real-exponent bookkeeping, exponent exactly `5/6`.
-/
import Erdos477.Defs
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.Cofactor.Basic

namespace Erdos477

open scoped BigOperators Classical

namespace BadShift

private theorem odd13 : Odd (13 : ℕ) := ⟨6, by norm_num⟩

/-! ### Membership in the bad-shift set -/

theorem mem_Sset_iff {c T t : ℤ} :
    t ∈ Sset c T ↔ (-T ≤ t ∧ t ≤ T) ∧ t ^ 13 - c ∈ Dset := by
  simp [Sset, Finset.mem_filter, Finset.mem_Icc]

/-! ### E1 — from a bad shift to a solution of the diagonal equation -/

/-- For every `t`, a pair `(u,v)` witnessing `t ^ 13 - c = u ^ 13 - v ^ 13`
whenever `t ^ 13 - c ∈ Dset` (a junk value otherwise). -/
theorem pair_exists (c t : ℤ) :
    ∃ p : ℤ × ℤ, t ^ 13 - c ∈ Dset → t ^ 13 - c = p.1 ^ 13 - p.2 ^ 13 := by
  by_cases h : t ^ 13 - c ∈ Dset
  · obtain ⟨u, v, huv⟩ := h
    exact ⟨(u, v), fun _ => huv⟩
  · exact ⟨(0, 0), fun h' => absurd h' h⟩

/-- The classically chosen witness pair `(u_t, v_t)` of SKETCH §6 Step 1. -/
noncomputable def pairOf (c t : ℤ) : ℤ × ℤ := (pair_exists c t).choose

theorem pairOf_spec {c t : ℤ} (h : t ^ 13 - c ∈ Dset) :
    t ^ 13 - c = (pairOf c t).1 ^ 13 - (pairOf c t).2 ^ 13 :=
  (pair_exists c t).choose_spec h

/-- The crux where `c ∉ Bset` is used: the witnesses are DISTINCT. -/
theorem pairOf_ne {c t : ℤ} (hc : c ∉ Bset) (h : t ^ 13 - c ∈ Dset) :
    (pairOf c t).1 ≠ (pairOf c t).2 := by
  intro heq
  have hs := pairOf_spec h
  rw [heq] at hs
  exact hc ⟨t, by linarith [hs]⟩

/-- The paper's substitution `Φ t = (u_t, -v_t, -t)`. -/
noncomputable def Phi (c t : ℤ) : ℤ × ℤ × ℤ :=
  ((pairOf c t).1, -(pairOf c t).2, -t)

theorem Phi_inj (c : ℤ) : Function.Injective (Phi c) := by
  intro a b hab
  have h : (-a : ℤ) = -b := congrArg (fun p => p.2.2) hab
  linarith

theorem Phi_sum {c t : ℤ} (h : t ^ 13 - c ∈ Dset) :
    (Phi c t).1 ^ 13 + (Phi c t).2.1 ^ 13 + (Phi c t).2.2 ^ 13 = -c := by
  have hs := pairOf_spec h
  simp only [Phi, Odd.neg_pow odd13]
  linarith

/-! ### E2 — the coordinate bound `max(|u|,|v|) ≤ C_c · T^(13/12)` -/

/-- `C_c := (2 (1 + |c|))^(1/12) ≥ 1`. -/
noncomputable def Cc (c : ℤ) : ℝ := (2 * (1 + |(c : ℝ)|)) ^ ((1 : ℝ) / 12)

theorem one_le_Cc (c : ℤ) : 1 ≤ Cc c := by
  have h1 : (1 : ℝ) ≤ 2 * (1 + |(c : ℝ)|) := by
    have := abs_nonneg ((c : ℝ)); linarith
  calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 12) := (Real.one_rpow _).symm
    _ ≤ Cc c := Real.rpow_le_rpow (by norm_num) h1 (by norm_num)

theorem Cc_nonneg (c : ℤ) : 0 ≤ Cc c := le_trans zero_le_one (one_le_Cc c)

theorem Cc_pow12 (c : ℤ) : (Cc c) ^ (12 : ℕ) = 2 * (1 + |(c : ℝ)|) := by
  have h0 : (0 : ℝ) ≤ 2 * (1 + |(c : ℝ)|) := by
    have := abs_nonneg ((c : ℝ)); linarith
  rw [Cc, ← Real.rpow_natCast ((2 * (1 + |(c : ℝ)|)) ^ ((1 : ℝ) / 12)) 12,
    ← Real.rpow_mul h0]
  norm_num

/-- The box radius `X := C_c · T^(13/12)`. -/
noncomputable def Xb (c T : ℤ) : ℝ := Cc c * (T : ℝ) ^ ((13 : ℝ) / 12)

theorem one_le_Xb {c T : ℤ} (hT : 1 ≤ T) : 1 ≤ Xb c T := by
  have hTr : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have h2 : (1 : ℝ) ≤ (T : ℝ) ^ ((13 : ℝ) / 12) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((13 : ℝ) / 12) := (Real.one_rpow _).symm
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hTr (by norm_num)
  have h1 := one_le_Cc c
  rw [Xb]
  nlinarith

theorem Xb_nonneg {c T : ℤ} (hT : 1 ≤ T) : 0 ≤ Xb c T :=
  le_trans zero_le_one (one_le_Xb hT)

theorem T_le_Xb {c T : ℤ} (hT : 1 ≤ T) : (T : ℝ) ≤ Xb c T := by
  have hTr : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have h1 : (T : ℝ) ≤ (T : ℝ) ^ ((13 : ℝ) / 12) := by
    calc (T : ℝ) = (T : ℝ) ^ ((1 : ℝ)) := (Real.rpow_one _).symm
      _ ≤ (T : ℝ) ^ ((13 : ℝ) / 12) :=
          Real.rpow_le_rpow_of_exponent_le hTr (by norm_num)
  have h2 : (1 : ℝ) ≤ Cc c := one_le_Cc c
  have h3 : (0 : ℝ) ≤ (T : ℝ) ^ ((13 : ℝ) / 12) := Real.rpow_nonneg (by linarith) _
  rw [Xb]
  nlinarith

theorem Xb_pow12 {c T : ℤ} (hT : 1 ≤ T) :
    (Xb c T) ^ (12 : ℕ) = 2 * (1 + |(c : ℝ)|) * (T : ℝ) ^ (13 : ℕ) := by
  have hTr : (0 : ℝ) ≤ (T : ℝ) := by
    have : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    linarith
  have h : ((T : ℝ) ^ ((13 : ℝ) / 12)) ^ (12 : ℕ) = (T : ℝ) ^ (13 : ℕ) := by
    rw [← Real.rpow_natCast ((T : ℝ) ^ ((13 : ℝ) / 12)) 12, ← Real.rpow_mul hTr,
      ← Real.rpow_natCast ((T : ℝ)) 13]
    norm_num
  rw [Xb, mul_pow, Cc_pow12, h]

/-- **E2 (SKETCH §6 Step 2, eq. (4.2)).** Both witness coordinates lie in the box
of radius `X = C_c · T^(13/12)`. -/
theorem coord_bound (c : ℤ) (hc : c ∉ Bset) {T t : ℤ} (hT : 1 ≤ T)
    (ht : t ∈ Sset c T) :
    |((pairOf c t).1 : ℝ)| ≤ Xb c T ∧ |((pairOf c t).2 : ℝ)| ≤ Xb c T := by
  obtain ⟨⟨hT1, hT2⟩, hD⟩ := mem_Sset_iff.mp ht
  set u := (pairOf c t).1 with hu
  set v := (pairOf c t).2 with hv
  have hne : u ≠ v := pairOf_ne hc hD
  have hgap := pow13_gap u v hne
  -- `|u^13 - v^13| = |t^13 - c|`
  have hs : ((t : ℝ)) ^ 13 - (c : ℝ) = (u : ℝ) ^ 13 - (v : ℝ) ^ 13 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (pairOf_spec hD)
  -- the size chain
  have hTr : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have habs : |(t : ℝ)| ≤ (T : ℝ) := by
    rw [abs_le]; constructor <;> [exact_mod_cast hT1; exact_mod_cast hT2]
  have hT13 : (1 : ℝ) ≤ (T : ℝ) ^ (13 : ℕ) := one_le_pow₀ hTr
  have ht13 : |(t : ℝ)| ^ (13 : ℕ) ≤ (T : ℝ) ^ (13 : ℕ) :=
    pow_le_pow_left₀ (abs_nonneg _) habs 13
  have hchain : |(t : ℝ) ^ 13 - (c : ℝ)| ≤ (1 + |(c : ℝ)|) * (T : ℝ) ^ (13 : ℕ) := by
    have h1 : |(t : ℝ) ^ 13 - (c : ℝ)| ≤ |(t : ℝ) ^ 13| + |(c : ℝ)| := abs_sub _ _
    have h2 : |(t : ℝ) ^ 13| = |(t : ℝ)| ^ (13 : ℕ) := abs_pow _ _
    have h3 : |(c : ℝ)| ≤ |(c : ℝ)| * (T : ℝ) ^ (13 : ℕ) := by
      nlinarith [abs_nonneg ((c : ℝ))]
    rw [h2] at h1
    nlinarith
  -- `(1/2) m^12 ≤ (1+|c|) T^13`
  set m := max |(u : ℝ)| |(v : ℝ)| with hm
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (le_max_left _ _)
  have hkey : m ^ (12 : ℕ) ≤ (Xb c T) ^ (12 : ℕ) := by
    have h4 : (1 / 2 : ℝ) * m ^ 12 ≤ |(t : ℝ) ^ 13 - (c : ℝ)| := by
      rw [hs]; exact hgap
    rw [Xb_pow12 hT]
    nlinarith
  have hmX : m ≤ Xb c T :=
    le_of_pow_le_pow_left₀ (by norm_num) (Xb_nonneg hT) hkey
  exact ⟨le_trans (le_max_left _ _) hmX, le_trans (le_max_right _ _) hmX⟩

/-! ### Finiteness of the counted solution set -/

theorem mem_Icc_ceil {x : ℤ} {X : ℝ} (h : |(x : ℝ)| ≤ X) :
    x ∈ Set.Icc (-⌈X⌉) ⌈X⌉ := by
  have h1 : (((|x| : ℤ)) : ℝ) ≤ X := by rw [Int.cast_abs]; exact h
  have h2 : ((|x| : ℤ) : ℝ) ≤ ((⌈X⌉ : ℤ) : ℝ) := le_trans h1 (Int.le_ceil X)
  have h3 : (|x| : ℤ) ≤ ⌈X⌉ := by exact_mod_cast h2
  exact Set.mem_Icc.mpr (abs_le.mp h3)

theorem sol_finite (M : ℤ) (X : ℝ) :
    ({v : ℤ × ℤ × ℤ | v.1 ^ 13 + v.2.1 ^ 13 + v.2.2 ^ 13 = M ∧
        |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ X ∧ |(v.2.2 : ℝ)| ≤ X}).Finite := by
  have hfin : (Set.Icc (-⌈X⌉) ⌈X⌉ ×ˢ (Set.Icc (-⌈X⌉) ⌈X⌉ ×ˢ Set.Icc (-⌈X⌉) ⌈X⌉)).Finite :=
    (Set.finite_Icc _ _).prod ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))
  refine Set.Finite.subset hfin ?_
  rintro ⟨x, y, z⟩ ⟨-, hx, hy, hz⟩
  exact ⟨mem_Icc_ceil hx, mem_Icc_ceil hy, mem_Icc_ceil hz⟩

end BadShift

open BadShift in
/-- **Stage E (E1–E4), SKETCH §6 / paper's Proposition 4.1.**

The bad-shift estimate with the exponent exactly `5/6`, taking the degree-≤ 1
exclusion hypothesis `hexcl` (proved in Stage C as `no_linear_param`) as an
explicit argument. The conclusion is verbatim that of the frozen
`badShift_bound`. -/
theorem badShift_bound_of_hexcl (c : ℤ) (hc : c ∉ Bset)
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
        p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
        p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
        p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := by
  -- E3: the single invocation of the assumed certificate, with `hexcl` passed through.
  have hM : (-c) ≠ 0 := neg_ne_zero.mpr (not_B_ne_zero c hc)
  obtain ⟨K, hK1, hK⟩ := heath_brown_diagonal_13 (-c) hM hexcl
  refine ⟨max 1 (K * (Cc c) ^ ((10 : ℝ) / 13)), le_max_left _ _, ?_⟩
  intro T hT
  have hTr : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hX1 : (1 : ℝ) ≤ Xb c T := one_le_Xb hT
  -- E4a: `Φ` maps `Sset c T` injectively into the counted solution set.
  have hsub : ↑((Sset c T).image (Phi c)) ⊆
      {v : ℤ × ℤ × ℤ | v.1 ^ 13 + v.2.1 ^ 13 + v.2.2 ^ 13 = -c ∧
        |(v.1 : ℝ)| ≤ Xb c T ∧ |(v.2.1 : ℝ)| ≤ Xb c T ∧ |(v.2.2 : ℝ)| ≤ Xb c T} := by
    intro w hw
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    obtain ⟨⟨hT1, hT2⟩, hD⟩ := mem_Sset_iff.mp ht
    obtain ⟨hu, hv⟩ := coord_bound c hc hT ht
    refine ⟨Phi_sum hD, hu, ?_, ?_⟩
    · show |((-(pairOf c t).2 : ℤ) : ℝ)| ≤ Xb c T
      rw [Int.cast_neg, abs_neg]; exact hv
    · show |((-t : ℤ) : ℝ)| ≤ Xb c T
      rw [Int.cast_neg, abs_neg]
      have habs : |(t : ℝ)| ≤ (T : ℝ) := by
        rw [abs_le]; constructor <;> [exact_mod_cast hT1; exact_mod_cast hT2]
      exact le_trans habs (T_le_Xb hT)
  have hcard : ((Sset c T).image (Phi c)).card = (Sset c T).card :=
    Finset.card_image_of_injective _ (Phi_inj c)
  have hle : ((Sset c T).card : ℝ) ≤
      (({v : ℤ × ℤ × ℤ | v.1 ^ 13 + v.2.1 ^ 13 + v.2.2 ^ 13 = -c ∧
          |(v.1 : ℝ)| ≤ Xb c T ∧ |(v.2.1 : ℝ)| ≤ Xb c T ∧
          |(v.2.2 : ℝ)| ≤ Xb c T}).ncard : ℝ) := by
    have h := Set.ncard_le_ncard hsub (sol_finite (-c) (Xb c T))
    rw [Set.ncard_coe_finset, hcard] at h
    exact_mod_cast h
  have hHB := hK (Xb c T) hX1
  -- E4b: real-exponent bookkeeping — `(T^(13/12))^(10/13) = T^(5/6)`.
  have hpow : (Xb c T) ^ ((10 : ℝ) / 13)
      = (Cc c) ^ ((10 : ℝ) / 13) * (T : ℝ) ^ ((5 : ℝ) / 6) := by
    have h1 : (Xb c T) ^ ((10 : ℝ) / 13)
        = (Cc c) ^ ((10 : ℝ) / 13) * ((T : ℝ) ^ ((13 : ℝ) / 12)) ^ ((10 : ℝ) / 13) := by
      rw [Xb, Real.mul_rpow (Cc_nonneg c) (Real.rpow_nonneg (by linarith) _)]
    have h2 : ((T : ℝ) ^ ((13 : ℝ) / 12)) ^ ((10 : ℝ) / 13)
        = (T : ℝ) ^ ((5 : ℝ) / 6) := by
      rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ (T : ℝ))]
      norm_num
    rw [h1, h2]
  have hT56 : (0 : ℝ) ≤ (T : ℝ) ^ ((5 : ℝ) / 6) := Real.rpow_nonneg (by linarith) _
  have hmax : K * (Cc c) ^ ((10 : ℝ) / 13) ≤ max 1 (K * (Cc c) ^ ((10 : ℝ) / 13)) :=
    le_max_right _ _
  calc ((Sset c T).card : ℝ) ≤ _ := hle
    _ ≤ K * (Xb c T) ^ ((10 : ℝ) / 13) := hHB
    _ = (K * (Cc c) ^ ((10 : ℝ) / 13)) * (T : ℝ) ^ ((5 : ℝ) / 6) := by
        rw [hpow]; ring
    _ ≤ max 1 (K * (Cc c) ^ ((10 : ℝ) / 13)) * (T : ℝ) ^ ((5 : ℝ) / 6) :=
        mul_le_mul_of_nonneg_right hmax hT56

end Erdos477
