/-
  Stage ParamExclusion — the Route-A SPINE: `no_linear_param_proof`
  (TASKS.md Iteration 3, Agent 1; REVIEW.md iteration-2 required follow-up).

  This is the paper's Lemma 3.1 + Corollary 3.2 (SKETCH §5.2.2–5.2.3),
  dehomogenized with `R = 1` and specialized to polynomial parametrizations:
  for `c ∉ Bset` no triple `p₁, p₂, p₃ ∈ ℤ[T]` with
  `p₁¹³ + p₂¹³ + p₃¹³ = C (−c)` can have a nonconstant member.

  Argument by contradiction, casing exactly as the paper does on which of the
  four terms `P₁¹³, P₂¹³, P₃¹³, C c` (over `K := AlgebraicClosure ℚ`) are
  nonzero and on vanishing proper subsums:
    * Case ≤ 1 nonzero power (paper's Case C): descend `pᵢ¹³ = C (−c)` to ℤ and
      contradict `c ∉ Bset` via `mem_Bset_of_pairing`.
    * Case exactly two nonzero powers (paper's Case B): the THREE-term instance
      `r = 3` of the frozen axiom `brownawell_masser_P1_four_term`, giving
      `13e ≤ 1·(2e + 1 − 2)` — impossible.
    * Case all three nonzero, no vanishing proper subsum (paper's Case A): the
      FOUR-term instance `r = 4` of the same axiom, giving
      `13e ≤ 3·(3e + 1 − 2)` — impossible.
    * Case all three nonzero with a vanishing proper subsum (paper's Case D):
      `vanishing_subsum_pairing` splits the four terms into two vanishing
      pairs; the pair containing `C c` forces `pₖ¹³ = C (−c)`, and the descent
      contradicts `c ∉ Bset` again.

  Both the `r = 3` and `r = 4` branches invoke the frozen axiom
  `Erdos477.brownawell_masser_P1_four_term` (per USER_NOTES.md); Mathlib's
  Mason–Stothers (`Polynomial.abc`) is nowhere used, and the Route-B
  Vandermonde argument does not appear.

  `#print axioms Erdos477.no_linear_param_proof` must be EXACTLY
  {propext, Classical.choice, Quot.sound, Erdos477.brownawell_masser_P1_four_term}.
-/
import Erdos477.Defs
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.ParamExclusion.Basic
import Erdos477.Proofs.ParamExclusion.Degenerate

namespace Erdos477

/-! ### No vanishing proper subsum among three nonzero terms

The three-term analogue of the Case-D 2+2 classification: in a zero sum of
THREE nonzero terms, no proper nonempty subsum can vanish (a singleton subsum
contradicts nonzeroness; a pair forces the complementary singleton to vanish).
This is the paper's Case-B "first, a proper vanishing sub-sum among the three
nonzero terms is impossible" step. -/
theorem fin3_no_vanishing_subsum {M : Type*} [AddCommGroup M] (x : Fin 3 → M)
    (hsum : ∑ i, x i = 0) (hnz : ∀ i, x i ≠ 0) (I : Finset (Fin 3))
    (hne : I.Nonempty) (hproper : I ≠ Finset.univ) : ∑ i ∈ I, x i ≠ 0 := by
  intro hI
  have hcompl : ∑ i ∈ Iᶜ, x i = 0 := by
    have h := Finset.sum_add_sum_compl I x
    rw [hI, zero_add, hsum] at h
    exact h
  have hsingleton : ∀ J : Finset (Fin 3), J.card = 1 → ∑ i ∈ J, x i ≠ 0 := by
    intro J hJ1 hJ0
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hJ1
    exact hnz a (by simpa using hJ0)
  have hlt : I.card < 3 := by
    have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
    simpa using this
  have hpos : 0 < I.card := hne.card_pos
  interval_cases h : I.card
  · exact hsingleton I h hI
  · have hc1 : Iᶜ.card = 1 := by
      have := Finset.card_compl I
      simp only [Fintype.card_fin, h] at this
      omega
    exact hsingleton Iᶜ hc1 hcompl

/-! ### The two Brownawell–Masser branches (paper's Cases B and A)

Both lemmas invoke the frozen axiom `brownawell_masser_P1_four_term` — the
`r = 3` (Mason–Stothers, coefficient `binom(2,2) = 1`) and `r = 4`
(coefficient `binom(3,2) = 3`) instances the paper uses in Lemma 3.1. -/

/-- **Paper's Case B (`r = 3`).** Over an algebraically closed field of
characteristic zero, a polynomial identity `A¹³ + B¹³ + C γ = 0` with
`A, B ≠ 0`, `γ ≠ 0` forces both `A` and `B` constant: with
`S := roots (A·B) ∪ {∞}` the three terms are `S`-units summing to zero with no
vanishing proper subsum, the height is `≥ 13·max(deg A, deg B)` while
`|S| ≤ deg A + deg B + 1`, and `13e ≤ 1·(2e + 1 − 2)` is absurd. -/
theorem bm_no_three_term {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {γ : K} (hγ : γ ≠ 0) (A B : Polynomial K) (hA : A ≠ 0) (hB : B ≠ 0)
    (hid : A ^ 13 + B ^ 13 + Polynomial.C γ = 0)
    (hne : A.natDegree ≠ 0 ∨ B.natDegree ≠ 0) : False := by
  classical
  set q : Fin 3 → Polynomial K := ![A ^ 13, B ^ 13, Polynomial.C γ] with hq
  have hq0 : q 0 = A ^ 13 := by simp [hq]
  have hq1 : q 1 = B ^ 13 := by simp [hq]
  have hq2 : q 2 = Polynomial.C γ := by simp [hq]
  have hqnz : ∀ i, q i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [hq] using pow_ne_zero 13 hA
    · simpa [hq] using pow_ne_zero 13 hB
    · simpa [hq] using Polynomial.C_ne_zero.mpr hγ
  have hqsum : ∑ i, q i = 0 := by
    rw [Fin.sum_univ_three, hq0, hq1, hq2]
    exact hid
  set S : Finset (Option K) := ((A * B).roots.toFinset.image some) ∪ {none} with hS
  have hnoneS : (none : Option K) ∈ S := by
    rw [hS]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hmemS : ∀ x : K, (A * B).IsRoot x → some x ∈ S := by
    intro x hx
    rw [hS]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem some
      (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (mul_ne_zero hA hB)).mpr hx)))
  have hSA : IsSUnitP1 S (algebraMap (Polynomial K) (RatFunc K) A) :=
    isSUnitP1_algebraMap S A hA hnoneS fun x hx =>
      hmemS x (by rw [Polynomial.IsRoot, Polynomial.eval_mul, hx.eq_zero, zero_mul])
  have hSB : IsSUnitP1 S (algebraMap (Polynomial K) (RatFunc K) B) :=
    isSUnitP1_algebraMap S B hB hnoneS fun x hx =>
      hmemS x (by rw [Polynomial.IsRoot, Polynomial.eval_mul, hx.eq_zero, mul_zero])
  have hSunit : ∀ i, IsSUnitP1 S (algebraMap (Polynomial K) (RatFunc K) (q i)) := by
    intro i
    fin_cases i
    · simpa [hq, map_pow] using hSA.pow 13
    · simpa [hq, map_pow] using hSB.pow 13
    · simpa [hq, RatFunc.algebraMap_C] using isSUnitP1_C S hγ
  have hnotconst :
      ¬ ∀ i, ∃ a : K, algebraMap (Polynomial K) (RatFunc K) (q i) = RatFunc.C a := by
    intro hall
    rcases hne with hd | hd
    · obtain ⟨a, ha⟩ := hall 0
      rw [hq0] at ha
      have hC := (algebraMap_polynomial_eq_C_iff (A ^ 13) a).mp ha
      have hdeg := congrArg Polynomial.natDegree hC
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_C] at hdeg
      omega
    · obtain ⟨a, ha⟩ := hall 1
      rw [hq1] at ha
      have hC := (algebraMap_polynomial_eq_C_iff (B ^ 13) a).mp ha
      have hdeg := congrArg Polynomial.natDegree hC
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_C] at hdeg
      omega
  have hsum' : ∑ i, algebraMap (Polynomial K) (RatFunc K) (q i) = 0 := by
    rw [← map_sum, hqsum, map_zero]
  have hsubsum : ∀ I : Finset (Fin 3), I.Nonempty → I ≠ Finset.univ →
      ∑ i ∈ I, algebraMap (Polynomial K) (RatFunc K) (q i) ≠ 0 := by
    intro I hne' hproper h0
    have hval : algebraMap (Polynomial K) (RatFunc K) (∑ i ∈ I, q i) =
        algebraMap (Polynomial K) (RatFunc K) (0 : Polynomial K) := by
      rw [map_sum, map_zero]
      exact h0
    exact fin3_no_vanishing_subsum q hqsum hqnz I hne' hproper
      (RatFunc.algebraMap_injective K hval)
  have hBM := brownawell_masser_P1_four_term S 3 le_rfl
    (fun i => algebraMap (Polynomial K) (RatFunc K) (q i)) hSunit hnotconst hsum' hsubsum
  have hheight := projHeightP1_algebraMap (K := K) (r := 3) (by norm_num) q hqnz 2
    (by rw [hq2, Polynomial.natDegree_C])
  rw [hheight] at hBM
  have hcoeff : (((3 : ℕ) - 1).choose 2 : ℤ) = 1 := by decide
  rw [hcoeff, one_mul] at hBM
  have hcard := card_roots_option_none_le (A * B)
  rw [← hS] at hcard
  have hdmul : (A * B).natDegree = A.natDegree + B.natDegree :=
    Polynomial.natDegree_mul hA hB
  have hdq0 : (q 0).natDegree = 13 * A.natDegree := by
    rw [hq0, Polynomial.natDegree_pow]
  have hdq1 : (q 1).natDegree = 13 * B.natDegree := by
    rw [hq1, Polynomial.natDegree_pow]
  have hle0 : (q 0).natDegree ≤ Finset.univ.sup fun i => (q i).natDegree :=
    Finset.le_sup (f := fun i => (q i).natDegree) (Finset.mem_univ 0)
  have hle1 : (q 1).natDegree ≤ Finset.univ.sup fun i => (q i).natDegree :=
    Finset.le_sup (f := fun i => (q i).natDegree) (Finset.mem_univ 1)
  omega

/-- **Paper's Case A (`r = 4`).** Over an algebraically closed field of
characteristic zero, a polynomial identity `P₁¹³ + P₂¹³ + P₃¹³ + C γ = 0` with
all `Pᵢ ≠ 0`, `γ ≠ 0`, NO vanishing proper nonempty subsum, and some `Pᵢ`
nonconstant is absurd: with `S := roots (P₁·P₂·P₃) ∪ {∞}` the height is
`≥ 13·max deg Pᵢ` while `|S| ≤ deg P₁ + deg P₂ + deg P₃ + 1`, and
`13e ≤ 3·(3e + 1 − 2)` fails. -/
theorem bm_no_four_term {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {γ : K} (hγ : γ ≠ 0) (P₁ P₂ P₃ : Polynomial K)
    (h1 : P₁ ≠ 0) (h2 : P₂ ≠ 0) (h3 : P₃ ≠ 0)
    (hid : P₁ ^ 13 + P₂ ^ 13 + P₃ ^ 13 + Polynomial.C γ = 0)
    (hsub : ∀ I : Finset (Fin 4), I.Nonempty → I ≠ Finset.univ →
      ∑ i ∈ I,
        (![P₁ ^ 13, P₂ ^ 13, P₃ ^ 13, Polynomial.C γ] : Fin 4 → Polynomial K) i ≠ 0)
    (hne : P₁.natDegree ≠ 0 ∨ P₂.natDegree ≠ 0 ∨ P₃.natDegree ≠ 0) : False := by
  classical
  set q : Fin 4 → Polynomial K := ![P₁ ^ 13, P₂ ^ 13, P₃ ^ 13, Polynomial.C γ] with hq
  have hq0 : q 0 = P₁ ^ 13 := by simp [hq]
  have hq1 : q 1 = P₂ ^ 13 := by simp [hq]
  have hq2 : q 2 = P₃ ^ 13 := by simp [hq]
  have hq3 : q 3 = Polynomial.C γ := by simp [hq]
  have hqnz : ∀ i, q i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [hq] using pow_ne_zero 13 h1
    · simpa [hq] using pow_ne_zero 13 h2
    · simpa [hq] using pow_ne_zero 13 h3
    · simpa [hq] using Polynomial.C_ne_zero.mpr hγ
  have hqsum : ∑ i, q i = 0 := by
    rw [Fin.sum_univ_four, hq0, hq1, hq2, hq3]
    exact hid
  have hprod : P₁ * P₂ * P₃ ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) h3
  set S : Finset (Option K) := ((P₁ * P₂ * P₃).roots.toFinset.image some) ∪ {none} with hS
  have hnoneS : (none : Option K) ∈ S := by
    rw [hS]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hmemS : ∀ x : K, (P₁ * P₂ * P₃).IsRoot x → some x ∈ S := by
    intro x hx
    rw [hS]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem some
      (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hprod).mpr hx)))
  have hS1 : IsSUnitP1 S (algebraMap (Polynomial K) (RatFunc K) P₁) :=
    isSUnitP1_algebraMap S P₁ h1 hnoneS fun x hx =>
      hmemS x (by simp [Polynomial.IsRoot, Polynomial.eval_mul, hx.eq_zero])
  have hS2 : IsSUnitP1 S (algebraMap (Polynomial K) (RatFunc K) P₂) :=
    isSUnitP1_algebraMap S P₂ h2 hnoneS fun x hx =>
      hmemS x (by simp [Polynomial.IsRoot, Polynomial.eval_mul, hx.eq_zero])
  have hS3 : IsSUnitP1 S (algebraMap (Polynomial K) (RatFunc K) P₃) :=
    isSUnitP1_algebraMap S P₃ h3 hnoneS fun x hx =>
      hmemS x (by simp [Polynomial.IsRoot, Polynomial.eval_mul, hx.eq_zero])
  have hSunit : ∀ i, IsSUnitP1 S (algebraMap (Polynomial K) (RatFunc K) (q i)) := by
    intro i
    fin_cases i
    · simpa [hq, map_pow] using hS1.pow 13
    · simpa [hq, map_pow] using hS2.pow 13
    · simpa [hq, map_pow] using hS3.pow 13
    · simpa [hq, RatFunc.algebraMap_C] using isSUnitP1_C S hγ
  have hnotconst :
      ¬ ∀ i, ∃ a : K, algebraMap (Polynomial K) (RatFunc K) (q i) = RatFunc.C a := by
    intro hall
    have hkill : ∀ i : Fin 4, ∀ P : Polynomial K, q i = P ^ 13 → P.natDegree ≠ 0 → False := by
      intro i P hqi hdP
      obtain ⟨a, ha⟩ := hall i
      rw [hqi] at ha
      have hC := (algebraMap_polynomial_eq_C_iff (P ^ 13) a).mp ha
      have hdeg := congrArg Polynomial.natDegree hC
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_C] at hdeg
      omega
    rcases hne with hd | hd | hd
    · exact hkill 0 P₁ hq0 hd
    · exact hkill 1 P₂ hq1 hd
    · exact hkill 2 P₃ hq2 hd
  have hsum' : ∑ i, algebraMap (Polynomial K) (RatFunc K) (q i) = 0 := by
    rw [← map_sum, hqsum, map_zero]
  have hsubsum : ∀ I : Finset (Fin 4), I.Nonempty → I ≠ Finset.univ →
      ∑ i ∈ I, algebraMap (Polynomial K) (RatFunc K) (q i) ≠ 0 := by
    intro I hne' hproper h0
    have hval : algebraMap (Polynomial K) (RatFunc K) (∑ i ∈ I, q i) =
        algebraMap (Polynomial K) (RatFunc K) (0 : Polynomial K) := by
      rw [map_sum, map_zero]
      exact h0
    exact hsub I hne' hproper (RatFunc.algebraMap_injective K hval)
  have hBM := brownawell_masser_P1_four_term S 4 (by norm_num)
    (fun i => algebraMap (Polynomial K) (RatFunc K) (q i)) hSunit hnotconst hsum' hsubsum
  have hheight := projHeightP1_algebraMap (K := K) (r := 4) (by norm_num) q hqnz 3
    (by rw [hq3, Polynomial.natDegree_C])
  rw [hheight] at hBM
  have hcoeff : (((4 : ℕ) - 1).choose 2 : ℤ) = 3 := by decide
  rw [hcoeff] at hBM
  have hcard := card_roots_option_none_le (P₁ * P₂ * P₃)
  rw [← hS] at hcard
  have hdmul : (P₁ * P₂ * P₃).natDegree = P₁.natDegree + P₂.natDegree + P₃.natDegree := by
    rw [Polynomial.natDegree_mul (mul_ne_zero h1 h2) h3, Polynomial.natDegree_mul h1 h2]
  have hdq0 : (q 0).natDegree = 13 * P₁.natDegree := by
    rw [hq0, Polynomial.natDegree_pow]
  have hdq1 : (q 1).natDegree = 13 * P₂.natDegree := by
    rw [hq1, Polynomial.natDegree_pow]
  have hdq2 : (q 2).natDegree = 13 * P₃.natDegree := by
    rw [hq2, Polynomial.natDegree_pow]
  have hle0 : (q 0).natDegree ≤ Finset.univ.sup fun i => (q i).natDegree :=
    Finset.le_sup (f := fun i => (q i).natDegree) (Finset.mem_univ 0)
  have hle1 : (q 1).natDegree ≤ Finset.univ.sup fun i => (q i).natDegree :=
    Finset.le_sup (f := fun i => (q i).natDegree) (Finset.mem_univ 1)
  have hle2 : (q 2).natDegree ≤ Finset.univ.sup fun i => (q i).natDegree :=
    Finset.le_sup (f := fun i => (q i).natDegree) (Finset.mem_univ 2)
  omega

/-! ### The ℤ-level case wrappers (paper's Cases B and A/D over `ℤ[T]`) -/

/-- **Case exactly-two-nonzero over `ℤ[T]`** (paper's Case B): if
`a¹³ + b¹³ = C (−c)` with `a, b ≠ 0` and `c ≠ 0`, both are constant. Maps to
`K := AlgebraicClosure ℚ` and invokes the `r = 3` Brownawell–Masser branch. -/
theorem two_nonzero_natDegree_eq_zero (c : ℤ) (hc0 : c ≠ 0)
    (a b : Polynomial ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a ^ 13 + b ^ 13 = Polynomial.C (-c)) :
    a.natDegree = 0 ∧ b.natDegree = 0 := by
  by_contra hcon
  rw [not_and_or] at hcon
  have hinj : Function.Injective (algebraMap ℤ (AlgebraicClosure ℚ)) :=
    (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int
  set A := a.map (algebraMap ℤ (AlgebraicClosure ℚ)) with hA_def
  set B := b.map (algebraMap ℤ (AlgebraicClosure ℚ)) with hB_def
  have hA : A ≠ 0 := by
    rw [hA_def]; exact (Polynomial.map_ne_zero_iff hinj).mpr ha
  have hB : B ≠ 0 := by
    rw [hB_def]; exact (Polynomial.map_ne_zero_iff hinj).mpr hb
  have hγ : ((c : AlgebraicClosure ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hc0
  have hcast : (algebraMap ℤ (AlgebraicClosure ℚ)) (-c) = -((c : AlgebraicClosure ℚ)) := by
    rw [eq_intCast, Int.cast_neg]
  have hid : A ^ 13 + B ^ 13 + Polynomial.C ((c : AlgebraicClosure ℚ)) = 0 := by
    have hmap := congrArg (Polynomial.map (algebraMap ℤ (AlgebraicClosure ℚ))) h
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C] at hmap
    rw [← hA_def, ← hB_def, hcast, Polynomial.C_neg] at hmap
    linear_combination hmap
  have hdA : A.natDegree = a.natDegree := by
    rw [hA_def]; exact Polynomial.natDegree_map_eq_of_injective hinj a
  have hdB : B.natDegree = b.natDegree := by
    rw [hB_def]; exact Polynomial.natDegree_map_eq_of_injective hinj b
  refine bm_no_three_term hγ A B hA hB hid ?_
  rcases hcon with hd | hd
  · exact Or.inl (by rwa [hdA])
  · exact Or.inr (by rwa [hdB])

/-- **Case all-three-nonzero over `ℤ[T]`** (paper's Cases A and D): if
`p₁¹³ + p₂¹³ + p₃¹³ = C (−c)` with all `pᵢ ≠ 0` and `c ∉ Bset`, all three are
constant. Over `K := AlgebraicClosure ℚ` either some proper nonempty subsum of
the four terms vanishes — then `vanishing_subsum_pairing` gives a 2+2 split
whose `C c`-pair descends to `pₖ¹³ = C (−c)` in `ℤ[T]`, contradicting
`c ∉ Bset` (Case D) — or none does and the `r = 4` Brownawell–Masser branch
gives the height contradiction (Case A). -/
theorem three_nonzero_natDegree_eq_zero (c : ℤ) (hc : c ∉ Bset)
    (p₁ p₂ p₃ : Polynomial ℤ) (h1 : p₁ ≠ 0) (h2 : p₂ ≠ 0) (h3 : p₃ ≠ 0)
    (h : p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c)) :
    p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 := by
  classical
  by_contra hcon
  have hc0 : c ≠ 0 := ne_zero_of_notMem_Bset hc
  have hne0 : p₁.natDegree ≠ 0 ∨ p₂.natDegree ≠ 0 ∨ p₃.natDegree ≠ 0 := by tauto
  have hinj : Function.Injective (algebraMap ℤ (AlgebraicClosure ℚ)) :=
    (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int
  set P₁ := p₁.map (algebraMap ℤ (AlgebraicClosure ℚ)) with hP1_def
  set P₂ := p₂.map (algebraMap ℤ (AlgebraicClosure ℚ)) with hP2_def
  set P₃ := p₃.map (algebraMap ℤ (AlgebraicClosure ℚ)) with hP3_def
  have hP1 : P₁ ≠ 0 := by
    rw [hP1_def]; exact (Polynomial.map_ne_zero_iff hinj).mpr h1
  have hP2 : P₂ ≠ 0 := by
    rw [hP2_def]; exact (Polynomial.map_ne_zero_iff hinj).mpr h2
  have hP3 : P₃ ≠ 0 := by
    rw [hP3_def]; exact (Polynomial.map_ne_zero_iff hinj).mpr h3
  have hγ : ((c : AlgebraicClosure ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hc0
  have hcast : (algebraMap ℤ (AlgebraicClosure ℚ)) (-c) = -((c : AlgebraicClosure ℚ)) := by
    rw [eq_intCast, Int.cast_neg]
  have hid : P₁ ^ 13 + P₂ ^ 13 + P₃ ^ 13 + Polynomial.C ((c : AlgebraicClosure ℚ)) = 0 := by
    have hmap := congrArg (Polynomial.map (algebraMap ℤ (AlgebraicClosure ℚ))) h
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C] at hmap
    rw [← hP1_def, ← hP2_def, ← hP3_def, hcast, Polynomial.C_neg] at hmap
    linear_combination hmap
  set x : Fin 4 → Polynomial (AlgebraicClosure ℚ) :=
    ![P₁ ^ 13, P₂ ^ 13, P₃ ^ 13, Polynomial.C ((c : AlgebraicClosure ℚ))] with hx
  have hx0 : x 0 = P₁ ^ 13 := by simp [hx]
  have hx1 : x 1 = P₂ ^ 13 := by simp [hx]
  have hx2 : x 2 = P₃ ^ 13 := by simp [hx]
  have hx3 : x 3 = Polynomial.C ((c : AlgebraicClosure ℚ)) := by simp [hx]
  have hxsum : ∑ i, x i = 0 := by
    rw [Fin.sum_univ_four, hx0, hx1, hx2, hx3]
    exact hid
  have hxnz : ∀ i, x i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [hx] using pow_ne_zero 13 hP1
    · simpa [hx] using pow_ne_zero 13 hP2
    · simpa [hx] using pow_ne_zero 13 hP3
    · simpa [hx] using Polynomial.C_ne_zero.mpr hγ
  -- Case-D descent: a vanishing pair containing the `C c` slot contradicts `hc`.
  have hdescend : ∀ (p : Polynomial ℤ) (P : Polynomial (AlgebraicClosure ℚ)),
      P = p.map (algebraMap ℤ (AlgebraicClosure ℚ)) →
      P ^ 13 + Polynomial.C ((c : AlgebraicClosure ℚ)) = 0 → False := by
    intro p P hPdef hp
    rw [hPdef] at hp
    have hmapEq : (p ^ 13).map (algebraMap ℤ (AlgebraicClosure ℚ)) =
        (Polynomial.C (-c)).map (algebraMap ℤ (AlgebraicClosure ℚ)) := by
      rw [Polynomial.map_pow, Polynomial.map_C, hcast, Polynomial.C_neg]
      linear_combination hp
    exact hc (mem_Bset_of_pairing c p (polyMap_int_injective (AlgebraicClosure ℚ) hmapEq))
  have hkill : ∀ J : Finset (Fin 4), J.card = 2 → (3 : Fin 4) ∈ J →
      ∑ i ∈ J, x i = 0 → False := by
    intro J hJ2 h3J hJ0
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp
      (by rw [Finset.card_erase_of_mem h3J, hJ2] : (J.erase 3).card = 1)
    have hkJ : k ∈ J.erase 3 := by rw [hk]; exact Finset.mem_singleton_self k
    have hk3 : k ≠ 3 := Finset.ne_of_mem_erase hkJ
    have hpair : x 3 + x k = 0 := by
      have hins : J = insert (3 : Fin 4) (J.erase 3) := (Finset.insert_erase h3J).symm
      rw [hins, Finset.sum_insert (Finset.notMem_erase 3 J), hk,
        Finset.sum_singleton] at hJ0
      exact hJ0
    fin_cases k
    · simp [hx] at hpair
      exact hdescend p₁ P₁ hP1_def (by simp only [map_intCast]; linear_combination hpair)
    · simp [hx] at hpair
      exact hdescend p₂ P₂ hP2_def (by simp only [map_intCast]; linear_combination hpair)
    · simp [hx] at hpair
      exact hdescend p₃ P₃ hP3_def (by simp only [map_intCast]; linear_combination hpair)
    · exact absurd rfl hk3
  by_cases hvan : ∃ I : Finset (Fin 4), I.Nonempty ∧ I ≠ Finset.univ ∧ ∑ i ∈ I, x i = 0
  · -- paper's Case D
    obtain ⟨I, hIne, hIproper, hI0⟩ := hvan
    obtain ⟨I', hI'2, hI'ne, hI'0, hI'c0⟩ :=
      vanishing_subsum_pairing x hxsum hxnz I hIne hIproper hI0
    by_cases h3I : (3 : Fin 4) ∈ I'
    · exact hkill I' hI'2 h3I hI'0
    · have h3c : (3 : Fin 4) ∈ I'ᶜ := Finset.mem_compl.mpr h3I
      have hc2 : I'ᶜ.card = 2 := by
        have := Finset.card_compl I'
        simp only [Fintype.card_fin, hI'2] at this
        omega
      exact hkill I'ᶜ hc2 h3c hI'c0
  · -- paper's Case A
    push Not at hvan
    have hdP1 : P₁.natDegree = p₁.natDegree := by
      rw [hP1_def]; exact Polynomial.natDegree_map_eq_of_injective hinj p₁
    have hdP2 : P₂.natDegree = p₂.natDegree := by
      rw [hP2_def]; exact Polynomial.natDegree_map_eq_of_injective hinj p₂
    have hdP3 : P₃.natDegree = p₃.natDegree := by
      rw [hP3_def]; exact Polynomial.natDegree_map_eq_of_injective hinj p₃
    refine bm_no_four_term hγ P₁ P₂ P₃ hP1 hP2 hP3 hid (fun I hIne hIproper => ?_) ?_
    · exact hvan I hIne hIproper
    · rcases hne0 with hd | hd | hd
      · exact Or.inl (by rwa [hdP1])
      · exact Or.inr (Or.inl (by rwa [hdP2]))
      · exact Or.inr (Or.inr (by rwa [hdP3]))

/-! ### The spine: zero-pattern dispatch (paper's Lemma 3.1 + Corollary 3.2) -/

/-- **The Route-A core.** For `c ∉ Bset`, any `p₁, p₂, p₃ ∈ ℤ[T]` with
`p₁¹³ + p₂¹³ + p₃¹³ = C (−c)` are ALL constant — with no degree restriction
(the paper's Corollary 3.2 excludes every degree; the frozen `no_linear_param`
is the `deg ≤ 1` instance). Cases on which `pᵢ` vanish: all zero forces
`C (−c) = 0`; exactly one nonzero forces `pᵢ¹³ = C (−c)`, i.e. `c ∈ Bset`
(paper's Case C); exactly two nonzero is the `r = 3` Brownawell–Masser branch
(Case B); all three nonzero is Case A / Case D. -/
theorem no_linear_param_core (c : ℤ) (hc : c ∉ Bset) (p₁ p₂ p₃ : Polynomial ℤ)
    (h : p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c)) :
    p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 := by
  have hc0 : c ≠ 0 := ne_zero_of_notMem_Bset hc
  have h13 : (13 : ℕ) ≠ 0 := by norm_num
  rcases eq_or_ne p₁ 0 with rfl | h1
  · rcases eq_or_ne p₂ 0 with rfl | h2
    · rcases eq_or_ne p₃ 0 with rfl | h3
      · -- all three zero: `C (−c) = 0`, impossible
        exfalso
        rw [zero_pow h13, zero_add, zero_add] at h
        have hneg : -c = 0 := by rwa [eq_comm, Polynomial.C_eq_zero] at h
        exact hc0 (by omega)
      · -- only `p₃ ≠ 0` (paper's Case C)
        rw [zero_pow h13, zero_add, zero_add] at h
        exact absurd (mem_Bset_of_pairing c p₃ h) hc
    · rcases eq_or_ne p₃ 0 with rfl | h3
      · -- only `p₂ ≠ 0` (Case C)
        rw [zero_pow h13, zero_add, add_zero] at h
        exact absurd (mem_Bset_of_pairing c p₂ h) hc
      · -- `p₂, p₃ ≠ 0` (Case B)
        rw [zero_pow h13, zero_add] at h
        obtain ⟨hd2, hd3⟩ := two_nonzero_natDegree_eq_zero c hc0 p₂ p₃ h2 h3 h
        exact ⟨Polynomial.natDegree_zero, hd2, hd3⟩
  · rcases eq_or_ne p₂ 0 with rfl | h2
    · rcases eq_or_ne p₃ 0 with rfl | h3
      · -- only `p₁ ≠ 0` (Case C)
        rw [zero_pow h13, add_zero, add_zero] at h
        exact absurd (mem_Bset_of_pairing c p₁ h) hc
      · -- `p₁, p₃ ≠ 0` (Case B)
        rw [zero_pow h13, add_zero] at h
        obtain ⟨hd1, hd3⟩ := two_nonzero_natDegree_eq_zero c hc0 p₁ p₃ h1 h3 h
        exact ⟨hd1, Polynomial.natDegree_zero, hd3⟩
    · rcases eq_or_ne p₃ 0 with rfl | h3
      · -- `p₁, p₂ ≠ 0` (Case B)
        rw [zero_pow h13, add_zero] at h
        obtain ⟨hd1, hd2⟩ := two_nonzero_natDegree_eq_zero c hc0 p₁ p₂ h1 h2 h
        exact ⟨hd1, hd2, Polynomial.natDegree_zero⟩
      · -- all three nonzero (Cases A/D)
        exact three_nonzero_natDegree_eq_zero c hc p₁ p₂ p₃ h1 h2 h3 h

/-- **L2.1 — exclusion of linear parametrizations** (statement CHARACTER-EXACT
to the frozen `no_linear_param` of `Erdos477/Theorems.lean`), proved via the
paper's Route A: Lemma 3.1 + Corollary 3.2 through
`brownawell_masser_P1_four_term` in BOTH its `r = 4` and `r = 3` instances. -/
theorem no_linear_param_proof (c : ℤ) (hc : c ∉ Bset) :
    ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 :=
  fun p₁ p₂ p₃ h _ _ _ => no_linear_param_core c hc p₁ p₂ p₃ h

/-! ### Guardrail (BLUEPRINT "Cheat watch (Stage ParamExclusion)")

A genuinely nonconstant witness like `p₁ = X, p₂ = −X, p₃ = C b` with
`∑ pᵢ¹³ = C (−c)` forces `c ∈ Bset` — matching the paper's Case D pairing. -/
example (c b : ℤ)
    (h : (Polynomial.X : Polynomial ℤ) ^ 13 + (-Polynomial.X) ^ 13 +
      (Polynomial.C b) ^ 13 = Polynomial.C (-c)) : c ∈ Bset := by
  by_contra hc
  have hres := no_linear_param_core c hc _ _ _ h
  have hd := hres.1
  rw [Polynomial.natDegree_X] at hd
  exact one_ne_zero hd

end Erdos477
