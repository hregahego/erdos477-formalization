/-
  Stage ParamExclusion (Layer 2) — Route-A support toolbox: orders, S-units and
  heights on ℙ¹ for `RatFunc K` (SKETCH §5.2.1–5.2.2 "Case A/B" ingredients),
  per TASKS.md Iteration 2 Agent 2 and the 📝 SETUP decision in PROGRESS.md.

  Support lemmas ONLY: `no_linear_param` itself is NOT stated here (it stays
  frozen in `Erdos477/Theorems.lean` for the iteration-3 spine). Everything in
  this file is proved from Mathlib alone — no custom axiom is invoked
  (`#print axioms`: standard three at most; in particular neither
  `Erdos477.brownawell_masser_P1_four_term` nor
  `Erdos477.heath_brown_diagonal_13` may appear), and Mathlib's Mason–Stothers
  (`Polynomial.abc`) is nowhere used.

  Everything works against the frozen `ordAtP1`, `IsSUnitP1`, `projHeightP1`
  of `Erdos477/Defs.lean` (`Option K` models `ℙ¹_K`; `none` = ∞), over a
  general `{K : Type*} [Field K]`, adding `[IsAlgClosed K]` only where needed
  (the spine will instantiate `K := AlgebraicClosure ℚ`).
-/
import Erdos477.Defs

namespace Erdos477

open scoped Classical

variable {K : Type*} [Field K]

/-! ### Definitional unfoldings of the frozen `ordAtP1` -/

theorem ordAtP1_some_def (a : K) (f : RatFunc K) :
    ordAtP1 (some a) f = (f.num.rootMultiplicity a : ℤ) - (f.denom.rootMultiplicity a : ℤ) :=
  rfl

theorem ordAtP1_none_def (f : RatFunc K) : ordAtP1 (none : Option K) f = -f.intDegree :=
  rfl

/-! ### (a) Representation independence: `ordAtP1` through ANY nonzero fraction

The frozen `ordAtP1` is defined via the coprime `num`/`denom` of `RatFunc`.
These two lemmas let every later computation use an arbitrary representation
`f = p / q` with `p, q ≠ 0` (not necessarily coprime): cross-multiplying
`f.num * q = p * f.denom` and using additivity of `rootMultiplicity` and
`natDegree` over products cancels the common factor. -/

theorem ordAtP1_eq_of_div (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) (f : RatFunc K)
    (hf : f = algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q) :
    ∀ a : K, ordAtP1 (some a) f = (p.rootMultiplicity a : ℤ) - (q.rootMultiplicity a : ℤ) := by
  intro a
  have hf0 : f ≠ 0 := by
    rw [hf]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq)
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf0
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hcross : f.num * q = p * f.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hf
  have h1 : Polynomial.rootMultiplicity a (f.num * q) =
      Polynomial.rootMultiplicity a (p * f.denom) := by rw [hcross]
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hnum hq),
    Polynomial.rootMultiplicity_mul (mul_ne_zero hp hden)] at h1
  rw [ordAtP1_some_def]
  omega

theorem ordAtP1_none_eq (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) (f : RatFunc K)
    (hf : f = algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q) :
    ordAtP1 (none : Option K) f = (q.natDegree : ℤ) - (p.natDegree : ℤ) := by
  have hf0 : f ≠ 0 := by
    rw [hf]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq)
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf0
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hcross : f.num * q = p * f.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hf
  have h1 : (f.num * q).natDegree = (p * f.denom).natDegree := by rw [hcross]
  rw [Polynomial.natDegree_mul hnum hq, Polynomial.natDegree_mul hp hden] at h1
  rw [ordAtP1_none_def, RatFunc.intDegree]
  omega

/-! ### (b) Order computations: constants, polynomials, products, powers -/

theorem ratFuncC_ne_zero {a : K} (ha : a ≠ 0) : (RatFunc.C a : RatFunc K) ≠ 0 :=
  fun h => ha (RatFunc.C_injective (h.trans (map_zero RatFunc.C).symm))

theorem ordAtP1_C (a : K) (_ha : a ≠ 0) : ∀ P : Option K, ordAtP1 P (RatFunc.C a) = 0 := by
  intro P
  match P with
  | none => rw [ordAtP1_none_def, RatFunc.intDegree_C, neg_zero]
  | some b =>
    rw [ordAtP1_some_def, RatFunc.num_C, RatFunc.denom_C, Polynomial.rootMultiplicity_C,
      ← Polynomial.C_1, Polynomial.rootMultiplicity_C]
    simp

theorem ordAtP1_one (P : Option K) : ordAtP1 P (1 : RatFunc K) = 0 := by
  have h : (1 : RatFunc K) = RatFunc.C 1 := (map_one RatFunc.C).symm
  rw [h]
  exact ordAtP1_C 1 one_ne_zero P

theorem ordAtP1_algebraMap (p : Polynomial K) (a : K) :
    ordAtP1 (some a) (algebraMap (Polynomial K) (RatFunc K) p) = (p.rootMultiplicity a : ℤ) := by
  rw [ordAtP1_some_def, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, ← Polynomial.C_1,
    Polynomial.rootMultiplicity_C]
  simp

theorem ordAtP1_algebraMap_none (p : Polynomial K) :
    ordAtP1 (none : Option K) (algebraMap (Polynomial K) (RatFunc K) p) = -(p.natDegree : ℤ) := by
  rw [ordAtP1_none_def, RatFunc.intDegree_polynomial]

theorem ordAtP1_mul {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0) (P : Option K) :
    ordAtP1 P (f * g) = ordAtP1 P f + ordAtP1 P g := by
  match P with
  | none =>
    rw [ordAtP1_none_def, ordAtP1_none_def, ordAtP1_none_def, RatFunc.intDegree_mul hf hg]
    ring
  | some a =>
    have hrep : f * g = algebraMap (Polynomial K) (RatFunc K) (f.num * g.num) /
        algebraMap (Polynomial K) (RatFunc K) (f.denom * g.denom) := by
      rw [map_mul, map_mul, ← div_mul_div_comm, RatFunc.num_div_denom, RatFunc.num_div_denom]
    rw [ordAtP1_eq_of_div (f.num * g.num) (f.denom * g.denom)
      (mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg))
      (mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)) (f * g) hrep a,
      Polynomial.rootMultiplicity_mul
        (mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg)),
      Polynomial.rootMultiplicity_mul
        (mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)),
      ordAtP1_some_def, ordAtP1_some_def]
    push_cast
    ring

theorem ordAtP1_pow {f : RatFunc K} (hf : f ≠ 0) (n : ℕ) (P : Option K) :
    ordAtP1 P (f ^ n) = (n : ℤ) * ordAtP1 P f := by
  induction n with
  | zero => rw [pow_zero, ordAtP1_one]; simp
  | succ n ih =>
    rw [pow_succ, ordAtP1_mul (pow_ne_zero n hf) hf P, ih]
    push_cast
    ring

theorem ordAtP1_neg (f : RatFunc K) (P : Option K) : ordAtP1 P (-f) = ordAtP1 P f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [neg_zero]
  have hC : (RatFunc.C (-1 : K) : RatFunc K) ≠ 0 := ratFuncC_ne_zero (by norm_num)
  have hrep : -f = RatFunc.C (-1 : K) * f := by
    rw [map_neg, map_one, neg_one_mul]
  rw [hrep, ordAtP1_mul hC hf P, ordAtP1_C (-1 : K) (by norm_num) P, zero_add]

/-! ### (c) Constancy criteria (SKETCH §5.2.2 "Case C/D orders argument")

Over an algebraically closed field, a nonzero rational function with order `0`
at EVERY point of `ℙ¹` (zeros and poles nowhere) is a constant; consequently a
rational function whose 13th power is a nonzero constant is itself constant. -/

theorem exists_C_of_forall_ordAtP1_eq_zero [IsAlgClosed K] (f : RatFunc K) (hf : f ≠ 0)
    (h : ∀ P : Option K, ordAtP1 P f = 0) : ∃ a : K, f = RatFunc.C a := by
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  -- `num` and `denom` are coprime, so the vanishing order-difference at each
  -- point forces BOTH multiplicities to vanish: neither has any root.
  have hkey : ∀ a : K, ¬f.num.IsRoot a ∧ ¬f.denom.IsRoot a := by
    intro a
    have hord := h (some a)
    rw [ordAtP1_some_def] at hord
    have hcommon : ¬(f.num.IsRoot a ∧ f.denom.IsRoot a) := by
      rintro ⟨h1, h2⟩
      obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom f
      have heval := congrArg (Polynomial.eval a) huv
      simp [h1.eq_zero, h2.eq_zero] at heval
    constructor
    · intro h1
      have hm1 : 0 < f.num.rootMultiplicity a := (Polynomial.rootMultiplicity_pos hnum).mpr h1
      have hm2 : 0 < f.denom.rootMultiplicity a := by omega
      exact hcommon ⟨h1, (Polynomial.rootMultiplicity_pos hden).mp hm2⟩
    · intro h2
      have hm2 : 0 < f.denom.rootMultiplicity a := (Polynomial.rootMultiplicity_pos hden).mpr h2
      have hm1 : 0 < f.num.rootMultiplicity a := by omega
      exact hcommon ⟨(Polynomial.rootMultiplicity_pos hnum).mp hm1, h2⟩
  -- over an algebraically closed field, rootless nonzero polynomials are constants
  have hdnum : f.num.natDegree = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.num (by
      rw [Polynomial.degree_eq_natDegree hnum]
      exact_mod_cast hne)
    exact (hkey a).1 ha
  have hdden : f.denom.natDegree = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.denom (by
      rw [Polynomial.degree_eq_natDegree hden]
      exact_mod_cast hne)
    exact (hkey a).2 ha
  obtain ⟨cn, hcn⟩ : ∃ cn : K, f.num = Polynomial.C cn :=
    ⟨f.num.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hdnum⟩
  obtain ⟨cd, hcd⟩ : ∃ cd : K, f.denom = Polynomial.C cd :=
    ⟨f.denom.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hdden⟩
  refine ⟨cn / cd, ?_⟩
  rw [← RatFunc.num_div_denom f, hcn, hcd, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
    ← map_div₀]

theorem exists_C_of_pow13_eq_C [IsAlgClosed K] (f : RatFunc K) (a : K) (ha : a ≠ 0)
    (h : f ^ 13 = RatFunc.C a) : ∃ b : K, f = RatFunc.C b := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : (13 : ℕ) ≠ 0)] at h
    exact ratFuncC_ne_zero ha h.symm
  refine exists_C_of_forall_ordAtP1_eq_zero f hf fun P => ?_
  have h13 : ((13 : ℕ) : ℤ) * ordAtP1 P f = 0 := by
    rw [← ordAtP1_pow hf 13 P, h, ordAtP1_C a ha P]
  omega

/-! ### (d) S-unit constructors and closure properties -/

theorem isSUnitP1_C (S : Finset (Option K)) {a : K} (ha : a ≠ 0) :
    IsSUnitP1 S (RatFunc.C a) :=
  ⟨ratFuncC_ne_zero ha, fun P _ => ordAtP1_C a ha P⟩

theorem isSUnitP1_algebraMap (S : Finset (Option K)) (p : Polynomial K) (hp : p ≠ 0)
    (hnone : (none : Option K) ∈ S) (hroots : ∀ a : K, p.IsRoot a → some a ∈ S) :
    IsSUnitP1 S (algebraMap (Polynomial K) (RatFunc K) p) := by
  refine ⟨RatFunc.algebraMap_ne_zero hp, fun P hP => ?_⟩
  match P with
  | none => exact absurd hnone hP
  | some a =>
    rw [ordAtP1_algebraMap,
      Polynomial.rootMultiplicity_eq_zero (fun hroot => hP (hroots a hroot))]
    simp

theorem IsSUnitP1.mul {S : Finset (Option K)} {f g : RatFunc K}
    (hf : IsSUnitP1 S f) (hg : IsSUnitP1 S g) : IsSUnitP1 S (f * g) :=
  ⟨mul_ne_zero hf.1 hg.1, fun P hP => by
    rw [ordAtP1_mul hf.1 hg.1 P, hf.2 P hP, hg.2 P hP, add_zero]⟩

theorem IsSUnitP1.pow {S : Finset (Option K)} {f : RatFunc K}
    (hf : IsSUnitP1 S f) (n : ℕ) : IsSUnitP1 S (f ^ n) :=
  ⟨pow_ne_zero n hf.1, fun P hP => by rw [ordAtP1_pow hf.1 n P, hf.2 P hP, mul_zero]⟩

theorem IsSUnitP1.neg {S : Finset (Option K)} {f : RatFunc K}
    (hf : IsSUnitP1 S f) : IsSUnitP1 S (-f) :=
  ⟨neg_ne_zero.mpr hf.1, fun P hP => by rw [ordAtP1_neg, hf.2 P hP]⟩

/-! ### (e) The height computation (SKETCH §5.2.1, dehomogenized)

For a tuple of nonzero polynomials one of which is a nonzero constant, the
projective height is exactly the maximum of the degrees: at every finite point
all orders are `≥ 0` and the constant coordinate contributes `0`, so the
pointwise `⨅` vanishes and the `finsum` has support inside `{∞}`; at `∞` the
`⨅` of the `-(natDegree)`s is `-(max natDegree)`. -/

theorem projHeightP1_algebraMap {r : ℕ} (hr : 0 < r) (q : Fin r → Polynomial K)
    (hq : ∀ i, q i ≠ 0) (i₀ : Fin r) (h₀ : (q i₀).natDegree = 0) :
    projHeightP1 (fun i => algebraMap (Polynomial K) (RatFunc K) (q i)) =
      ((Finset.univ.sup fun i => (q i).natDegree : ℕ) : ℤ) := by
  haveI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  -- the distinguished constant coordinate has no roots
  have hrm₀ : ∀ a : K, (q i₀).rootMultiplicity a = 0 := by
    intro a
    apply Polynomial.rootMultiplicity_eq_zero
    intro hroot
    rw [Polynomial.eq_C_of_natDegree_eq_zero h₀] at hroot
    have hc : (q i₀).coeff 0 = 0 := by simpa [Polynomial.IsRoot] using hroot
    exact hq i₀ (by rw [Polynomial.eq_C_of_natDegree_eq_zero h₀, hc, Polynomial.C_0])
  -- at every finite point the pointwise minimum of the orders is 0
  have hfin : ∀ a : K,
      (⨅ i, ordAtP1 (some a) (algebraMap (Polynomial K) (RatFunc K) (q i))) = 0 := by
    intro a
    refine le_antisymm ?_ ?_
    · have hle : (⨅ i, ordAtP1 (some a) (algebraMap (Polynomial K) (RatFunc K) (q i))) ≤
          ordAtP1 (some a) (algebraMap (Polynomial K) (RatFunc K) (q i₀)) :=
        ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) i₀
      rwa [ordAtP1_algebraMap, hrm₀ a, Nat.cast_zero] at hle
    · refine le_ciInf fun i => ?_
      rw [ordAtP1_algebraMap]
      exact Int.natCast_nonneg _
  -- at ∞ the pointwise minimum is minus the maximal degree
  have hnone : (⨅ i, ordAtP1 (none : Option K) (algebraMap (Polynomial K) (RatFunc K) (q i))) =
      -((Finset.univ.sup fun i => (q i).natDegree : ℕ) : ℤ) := by
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin r))
      ⟨i₀, Finset.mem_univ i₀⟩ (fun i => (q i).natDegree)
    refine le_antisymm ?_ ?_
    · have hle : (⨅ i, ordAtP1 (none : Option K) (algebraMap (Polynomial K) (RatFunc K) (q i))) ≤
          ordAtP1 (none : Option K) (algebraMap (Polynomial K) (RatFunc K) (q i₁)) :=
        ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) i₁
      rw [ordAtP1_algebraMap_none] at hle
      rw [hi₁]
      exact hle
    · refine le_ciInf fun i => ?_
      rw [ordAtP1_algebraMap_none]
      have hle : (q i).natDegree ≤ Finset.univ.sup fun i => (q i).natDegree :=
        Finset.le_sup (f := fun i => (q i).natDegree) (Finset.mem_univ i)
      omega
  -- the finsum over ℙ¹ has support inside {∞}
  have hsum : (∑ᶠ P : Option K,
        ⨅ i, ordAtP1 P (algebraMap (Polynomial K) (RatFunc K) (q i))) =
      ⨅ i, ordAtP1 (none : Option K) (algebraMap (Polynomial K) (RatFunc K) (q i)) := by
    refine finsum_eq_single _ (none : Option K) fun P hP => ?_
    match P with
    | some a => exact hfin a
    | none => exact absurd rfl hP
  simp only [projHeightP1]
  rw [hsum, hnone, neg_neg]

/-! ### (f) The |S| count: roots of `p` together with ∞ -/

theorem card_roots_option_none_le (p : Polynomial K) :
    (((p.roots.toFinset.image (some : K → Option K)) ∪ {(none : Option K)}).card : ℤ) ≤
      (p.natDegree : ℤ) + 1 := by
  have h1 : ((p.roots.toFinset.image (some : K → Option K)) ∪ {(none : Option K)}).card ≤
      (p.roots.toFinset.image (some : K → Option K)).card + 1 :=
    le_trans (Finset.card_union_le _ _) (by simp)
  have h2 : (p.roots.toFinset.image (some : K → Option K)).card ≤ p.roots.toFinset.card :=
    Finset.card_image_le
  have h3 : p.roots.toFinset.card ≤ Multiset.card p.roots := p.roots.toFinset_card_le
  have h4 : Multiset.card p.roots ≤ p.natDegree := p.card_roots'
  omega

/-! ### (g) The nonconstancy bridge: `algebraMap` vs `RatFunc.C` -/

theorem algebraMap_polynomial_eq_C_iff (p : Polynomial K) (a : K) :
    algebraMap (Polynomial K) (RatFunc K) p = RatFunc.C a ↔ p = Polynomial.C a := by
  constructor
  · intro h
    apply RatFunc.algebraMap_injective K
    rw [h, RatFunc.algebraMap_C]
  · rintro rfl
    exact RatFunc.algebraMap_C a

end Erdos477
