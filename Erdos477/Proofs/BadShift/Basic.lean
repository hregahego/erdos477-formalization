/-
  Stage BadShift (Layer 3) — badShift_bound — the O_c(T^(5/6)) estimate (HEART; derives the
  diagonal-13 count from the general heath_brown_diagonal_13 axiom).

  ITERATION 1 (agent-iter1-4): the Heath-Brown SPECIALIZATION BRIDGE mandated by
  USER_NOTES.md ("axiomatize the general, derive the specific") and the SETUP 📝
  decision — the sketch's conditional diagonal-13 "AXIOM HB" (SKETCH.md §3,
  "recommended Lean form", modulo the ε-sign step, unnecessary since the frozen
  axiom takes arbitrary `N ≠ 0`) is PROVED here as `hb_diagonal_conditional`
  from the frozen general axiom `Erdos477.heath_brown_diagonal_13` (the paper's
  Theorem 2.2 in full generality).

  `badShift_bound` itself is NOT touched here: it needs `no_linear_param`
  (Stage ParamExclusion), not yet available. A later iteration combines that
  exclusion input with `hb_diagonal_conditional` below.

  Support declarations go in `namespace Erdos477` (never shadow a frozen name);
  the frozen statements themselves live untouched in `Erdos477/Theorems.lean`.
-/
import Erdos477.Defs
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.Cofactor.Basic
import Erdos477.Proofs.ParamExclusion.Spine

namespace Erdos477

open MvPolynomial

/-! ## The diagonal degree-13 ternary form -/

/-- The diagonal ternary form `X₀¹³ + X₁¹³ + X₂¹³ ∈ ℤ[X₀,X₁,X₂]` to which the
paper applies its Theorem 2.2 (the frozen axiom `heath_brown_diagonal_13`).
A support definition of Stage BadShift — deliberately NOT in `Defs.lean`. -/
noncomputable def diag13Form : MvPolynomial (Fin 3) ℤ :=
  X 0 ^ 13 + X 1 ^ 13 + X 2 ^ 13

/-- `diag13Form` is homogeneous of degree 13. -/
theorem diag13Form_isHomogeneous : diag13Form.IsHomogeneous 13 := by
  have h : ∀ i : Fin 3, (X i ^ 13 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 13 := fun i => by
    simpa only [one_mul] using (isHomogeneous_X ℤ i).pow 13
  exact ((h 0).add (h 1)).add (h 2)

/-- Evaluation of `diag13Form` at an integer triple is the diagonal sum of
thirteenth powers. -/
theorem diag13_eval (x : Fin 3 → ℤ) :
    MvPolynomial.eval x diag13Form = x 0 ^ 13 + x 1 ^ 13 + x 2 ^ 13 := by
  simp [diag13Form]

/-- `aeval` analogue of `diag13_eval`, for triples of one-variable integer
polynomials: substituting `p` into `diag13Form` yields `p₀¹³ + p₁¹³ + p₂¹³`.
Translates the frozen `IsParamOfDegLE` identity into the shape consumed by the
exclusion hypothesis of the bridge lemma. -/
theorem diag13_aeval (p : Fin 3 → Polynomial ℤ) :
    MvPolynomial.aeval p diag13Form = p 0 ^ 13 + p 1 ^ 13 + p 2 ^ 13 := by
  simp [diag13Form]

/-- The partial derivatives of `diag13Form` are `13·Xᵢ¹²`. -/
theorem diag13Form_pderiv (i : Fin 3) :
    MvPolynomial.pderiv i diag13Form = 13 * X i ^ 12 := by
  fin_cases i <;> simp [diag13Form]

/-- `diag13Form` is nonsingular: over `ℂ` its gradient `(13x₀¹², 13x₁¹², 13x₂¹²)`
vanishes only at the origin. -/
theorem diag13Form_nonsingular : IsNonsingularForm diag13Form := by
  intro x hx
  funext i
  have h : (13 : ℂ) * x i ^ 12 = 0 := by
    have h0 := hx i
    rw [diag13Form_pderiv] at h0
    simpa using h0
  have h12 : x i ^ 12 = 0 := by
    rcases mul_eq_zero.mp h with h13 | h12
    · norm_num at h13
    · exact h12
  exact pow_eq_zero_iff (by norm_num : (12 : ℕ) ≠ 0) |>.mp h12

/-! ## The bridge lemma: SKETCH §3's "AXIOM HB", proved from the general axiom -/

/-- **The Heath-Brown specialization bridge** — the conditional diagonal-13
count of `SKETCH.md` §3, PROVED from the frozen general axiom
`heath_brown_diagonal_13` (paper's Theorem 2.2) per `USER_NOTES.md`.

Given `M ≠ 0` and the exclusion input (every degree-≤1 polynomial solution of
`p₁¹³ + p₂¹³ + p₃¹³ = M` is constant — supplied downstream by
`no_linear_param` for `M = −c`), the number of integer solutions of
`x₀¹³ + x₁¹³ + x₂¹³ = M` in the box `max |xᵢ| ≤ X` is at most `K·X^(10/13)`,
with `K` depending only on `M`.

Bridge steps (SKETCH §3, "why this form is a faithful consequence", 1–4):
instantiate the axiom at `F := diag13Form`, `k := 13`, `cN := |M|`; note
`⌊13/10⌋ = 1` and `|M| ≤ |M|·X` for `X ≥ 1`; the exclusion hypothesis makes
`IsParamOfDegLE diag13Form M 1` contradictory, so no solution "lies on" a
parametrization and `HBSolutionSet` is the FULL box count. -/
theorem hb_diagonal_conditional (M : ℤ) (hM : M ≠ 0)
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
        p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C M →
        p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
        p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      (({x : Fin 3 → ℤ | MvPolynomial.eval x diag13Form = M ∧ ∀ i, |(x i : ℝ)| ≤ X}).ncard : ℝ)
        ≤ K * X ^ ((10 : ℝ) / 13) := by
  obtain ⟨K, hK1, hK⟩ := heath_brown_diagonal_13 diag13Form 13 (by norm_num)
    diag13Form_isHomogeneous diag13Form_nonsingular |(M : ℝ)|
  refine ⟨K, hK1, fun X hX => ?_⟩
  have hbox := hK M X hM hX (le_mul_of_one_le_right (abs_nonneg _) hX)
  have h1310 : (13 : ℕ) / 10 = 1 := by norm_num
  rw [h1310] at hbox
  have h13 : ((13 : ℕ) : ℝ) = 13 := by norm_num
  rw [h13] at hbox
  have hset : HBSolutionSet diag13Form M 1 X
      = {x : Fin 3 → ℤ | MvPolynomial.eval x diag13Form = M ∧ ∀ i, |(x i : ℝ)| ≤ X} := by
    ext x
    simp only [HBSolutionSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, h2, ?_⟩
      rintro ⟨p, ⟨hdeg, hnc, haev⟩, -⟩
      have hconst := hexcl (p 0) (p 1) (p 2) ((diag13_aeval p).symm.trans haev)
        (hdeg 0) (hdeg 1) (hdeg 2)
      refine hnc fun i => ?_
      fin_cases i
      · exact hconst.1
      · exact hconst.2.1
      · exact hconst.2.2
  rw [hset] at hbox
  exact hbox

/-! ## B1 (conditional): the bad-shift estimate modulo the exclusion input

`badShift_bound_of_hexcl` is EXACTLY the frozen `badShift_bound` conclusion,
with the exclusion statement `hexcl` (= the conclusion of the future
`no_linear_param c hc`) as an extra hypothesis on this SUPPORT lemma only.
The frozen `badShift_bound` in `Theorems.lean` stays untouched and un-restated;
once Stage ParamExclusion delivers `no_linear_param`, it is discharged as
`fun c hc => badShift_bound_of_hexcl c hc (no_linear_param_proof c hc)`.

Proof per SKETCH §6 (P3.1, Steps 0–4) / BLUEPRINT Stage BadShift B1:
each `t ∈ Sset c T` gives (choice) a pair `u ≠ v` with `t¹³ − c = u¹³ − v¹³`
(`u = v` would force `c = t¹³ ∈ Bset`, killed by the live `hc`); the injection
`Φ t = ![u, −v, −t]` (third coordinate recovers `t`) lands in the diagonal box
`{x | x₀¹³+x₁¹³+x₂¹³ = −c, max|xᵢ| ≤ X}` with `X := C_c·T^{13/12}`,
`C_c := (2(1+|c|))^{1/12}` (via `pow13_gap_proof`); `hb_diagonal_conditional`
counts the box by `K·X^{10/13}`, and `(T^{13/12})^{10/13} = T^{5/6}`. -/

theorem badShift_bound_of_hexcl (c : ℤ) (hc : c ∉ Bset)
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
        p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
        p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
        p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := by
  classical
  -- Step 0: `M := -c ≠ 0`
  have hM : (-c : ℤ) ≠ 0 := neg_ne_zero.mpr (ne_zero_of_notMem_Bset hc)
  -- Steps 3–4 input: the conditional Heath-Brown count at `M = -c`
  obtain ⟨K, hK1, hK⟩ := hb_diagonal_conditional (-c) hM hexcl
  -- the constant `C_c = (2(1+|c|))^{1/12} ≥ 1` of SKETCH §6 Step 2
  set Cc : ℝ := (2 * (1 + |(c : ℝ)|)) ^ ((1 : ℝ) / 12) with hCc_def
  have hbase1 : (1 : ℝ) ≤ 2 * (1 + |(c : ℝ)|) := by nlinarith [abs_nonneg (c : ℝ)]
  have hbase0 : (0 : ℝ) ≤ 2 * (1 + |(c : ℝ)|) := by linarith
  have hCc1 : (1 : ℝ) ≤ Cc := by
    rw [hCc_def]
    calc (1 : ℝ) = 1 ^ ((1 : ℝ) / 12) := (Real.one_rpow _).symm
      _ ≤ (2 * (1 + |(c : ℝ)|)) ^ ((1 : ℝ) / 12) :=
          Real.rpow_le_rpow zero_le_one hbase1 (by norm_num)
  have hCc0 : (0 : ℝ) ≤ Cc := zero_le_one.trans hCc1
  refine ⟨K * Cc ^ ((10 : ℝ) / 13), ?_, ?_⟩
  · -- `1 ≤ K_c = K · C_c^{10/13}`
    have h1 : (1 : ℝ) ≤ Cc ^ ((10 : ℝ) / 13) := by
      calc (1 : ℝ) = 1 ^ ((10 : ℝ) / 13) := (Real.one_rpow _).symm
        _ ≤ Cc ^ ((10 : ℝ) / 13) := Real.rpow_le_rpow zero_le_one hCc1 (by norm_num)
    nlinarith
  intro T hT
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := zero_le_one.trans hT1
  -- Step 2's box radius `X := C_c · T^{13/12}`
  set X : ℝ := Cc * (T : ℝ) ^ ((13 : ℝ) / 12) with hX_def
  have hTX : (T : ℝ) ≤ X := by
    rw [hX_def]
    calc (T : ℝ) = (T : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (T : ℝ) ^ ((13 : ℝ) / 12) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ ≤ Cc * (T : ℝ) ^ ((13 : ℝ) / 12) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hT0 _) hCc1
  have hX1 : (1 : ℝ) ≤ X := hT1.trans hTX
  -- Steps 1–2: each bad shift yields a boxed solution of the diagonal equation,
  -- with the third coordinate remembering the shift
  have key : ∀ t : ℤ, ∃ x : Fin 3 → ℤ, t ∈ Sset c T →
      (MvPolynomial.eval x diag13Form = -c ∧ ∀ i, |(x i : ℝ)| ≤ X) ∧ x 2 = -t := by
    intro t
    by_cases ht : t ∈ Sset c T
    swap
    · exact ⟨0, fun h => absurd h ht⟩
    have ht' := ht
    simp only [Sset, Finset.mem_filter, Finset.mem_Icc] at ht'
    obtain ⟨⟨htlo, hthi⟩, u, v, huv⟩ := ht'
    -- Step 1 claim: `u ≠ v` (else `c = t¹³ ∈ Bset`, contradicting `hc`)
    have hne : u ≠ v := by
      rintro rfl
      exact hc ⟨t, by linarith⟩
    -- Step 2: the size bound `max(|u|,|v|) ≤ X` from the gap bound
    have habs_t : |(t : ℝ)| ≤ (T : ℝ) := by
      rw [abs_le]
      exact ⟨by exact_mod_cast htlo, by exact_mod_cast hthi⟩
    have hgap := pow13_gap_proof u v hne
    have hcast : (u : ℝ) ^ 13 - (v : ℝ) ^ 13 = (t : ℝ) ^ 13 - (c : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) huv
      push_cast at h
      linarith
    have hTpow1 : (1 : ℝ) ≤ (T : ℝ) ^ (13 : ℕ) := one_le_pow₀ hT1
    have habs13 : |(t : ℝ) ^ 13| ≤ (T : ℝ) ^ (13 : ℕ) := by
      rw [abs_pow]
      gcongr
    have hrhs : |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| ≤ (1 + |(c : ℝ)|) * (T : ℝ) ^ (13 : ℕ) := by
      rw [hcast]
      calc |(t : ℝ) ^ 13 - (c : ℝ)| ≤ |(t : ℝ) ^ 13| + |(c : ℝ)| := abs_sub _ _
        _ ≤ (T : ℝ) ^ (13 : ℕ) + |(c : ℝ)| * (T : ℝ) ^ (13 : ℕ) := by
            have := le_mul_of_one_le_right (abs_nonneg (c : ℝ)) hTpow1
            linarith
        _ = (1 + |(c : ℝ)|) * (T : ℝ) ^ (13 : ℕ) := by ring
    have hmax0 : (0 : ℝ) ≤ max |(u : ℝ)| |(v : ℝ)| :=
      (abs_nonneg _).trans (le_max_left _ _)
    have hmax12 : max |(u : ℝ)| |(v : ℝ)| ^ 12
        ≤ 2 * (1 + |(c : ℝ)|) * (T : ℝ) ^ (13 : ℕ) := by
      nlinarith [hgap, hrhs]
    have hmaxX : max |(u : ℝ)| |(v : ℝ)| ≤ X := by
      have hid : max |(u : ℝ)| |(v : ℝ)|
          = (max |(u : ℝ)| |(v : ℝ)| ^ (12 : ℕ)) ^ ((1 : ℝ) / 12) := by
        rw [← Real.rpow_natCast (max |(u : ℝ)| |(v : ℝ)|) 12, ← Real.rpow_mul hmax0]
        norm_num
      rw [hid, hX_def]
      calc (max |(u : ℝ)| |(v : ℝ)| ^ (12 : ℕ)) ^ ((1 : ℝ) / 12)
          ≤ (2 * (1 + |(c : ℝ)|) * (T : ℝ) ^ (13 : ℕ)) ^ ((1 : ℝ) / 12) :=
            Real.rpow_le_rpow (pow_nonneg hmax0 _) hmax12 (by norm_num)
        _ = Cc * ((T : ℝ) ^ (13 : ℕ)) ^ ((1 : ℝ) / 12) := by
            rw [Real.mul_rpow hbase0 (pow_nonneg hT0 _)]
        _ = Cc * (T : ℝ) ^ ((13 : ℝ) / 12) := by
            rw [← Real.rpow_natCast (T : ℝ) 13, ← Real.rpow_mul hT0]
            norm_num
    -- assemble the boxed solution `Φ t = ![u, -v, -t]`
    refine ⟨![u, -v, -t], fun _ => ⟨⟨?_, ?_⟩, ?_⟩⟩
    · -- evaluation: `u¹³ + (−v)¹³ + (−t)¹³ = −c` (odd exponent)
      rw [diag13_eval]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      have hodd : Odd 13 := by decide
      rw [hodd.neg_pow v, hodd.neg_pow t]
      linarith
    · -- the coordinate bounds
      intro i
      fin_cases i
      · simpa using (le_max_left |(u : ℝ)| |(v : ℝ)|).trans hmaxX
      · simpa using (le_max_right |(u : ℝ)| |(v : ℝ)|).trans hmaxX
      · simpa using habs_t.trans hTX
    · rfl
  choose Φ hΦ using key
  -- Step 1 injectivity: the third coordinate recovers `t`
  have hinj : Set.InjOn Φ ↑(Sset c T) := by
    intro t ht t' ht' hEq
    have h2 : Φ t 2 = -t := (hΦ t (Finset.mem_coe.mp ht)).2
    have h2' : Φ t' 2 = -t' := (hΦ t' (Finset.mem_coe.mp ht')).2
    have : -t = -t' := by rw [← h2, ← h2', hEq]
    omega
  have himg : Φ '' ↑(Sset c T) ⊆
      {x : Fin 3 → ℤ | MvPolynomial.eval x diag13Form = -c ∧ ∀ i, |(x i : ℝ)| ≤ X} := by
    rintro x ⟨t, ht, rfl⟩
    exact (hΦ t (Finset.mem_coe.mp ht)).1
  -- the box is finite (inside a product of integer intervals)
  have hBoxFin :
      ({x : Fin 3 → ℤ | MvPolynomial.eval x diag13Form = -c ∧ ∀ i, |(x i : ℝ)| ≤ X}).Finite := by
    have hsub : {x : Fin 3 → ℤ | MvPolynomial.eval x diag13Form = -c ∧ ∀ i, |(x i : ℝ)| ≤ X}
        ⊆ Set.pi Set.univ fun _ : Fin 3 => (↑(Finset.Icc (-⌈X⌉) ⌈X⌉) : Set ℤ) := by
      rintro x ⟨-, hx⟩ i -
      simp only [Finset.coe_Icc, Set.mem_Icc]
      have h1 : ((x i : ℤ) : ℝ) ≤ ((⌈X⌉ : ℤ) : ℝ) :=
        (le_abs_self _).trans ((hx i).trans (Int.le_ceil X))
      have h2 : ((-⌈X⌉ : ℤ) : ℝ) ≤ ((x i : ℤ) : ℝ) := by
        push_cast
        have hna := neg_abs_le ((x i : ℤ) : ℝ)
        have hxi := hx i
        have hce := Int.le_ceil X
        linarith
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
    exact (Set.Finite.pi fun _ => (Finset.Icc _ _).finite_toSet).subset hsub
  -- Step 4: count through the injection, then the exponent identity
  calc ((Sset c T).card : ℝ)
      = (((Sset c T : Finset ℤ) : Set ℤ).ncard : ℝ) := by rw [Set.ncard_coe_finset]
    _ = ((Φ '' ↑(Sset c T)).ncard : ℝ) := by rw [hinj.ncard_image]
    _ ≤ (({x : Fin 3 → ℤ | MvPolynomial.eval x diag13Form = -c ∧
          ∀ i, |(x i : ℝ)| ≤ X}).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard himg hBoxFin
    _ ≤ K * X ^ ((10 : ℝ) / 13) := hK X hX1
    _ = K * Cc ^ ((10 : ℝ) / 13) * (T : ℝ) ^ ((5 : ℝ) / 6) := by
        rw [hX_def, Real.mul_rpow hCc0 (Real.rpow_nonneg hT0 _), ← Real.rpow_mul hT0]
        rw [show (13 : ℝ) / 12 * (10 / 13) = 5 / 6 by norm_num]
        ring

/-- **P3.1 — the bad-shift estimate** (statement CHARACTER-EXACT to the frozen
`badShift_bound` of `Erdos477/Theorems.lean`): the one-line discharge of the
conditional `badShift_bound_of_hexcl` above by the Route-A exclusion input
`Erdos477.no_linear_param_proof` (Stage ParamExclusion spine). Carries BOTH
permitted axioms: `heath_brown_diagonal_13` through the Heath-Brown count and
`brownawell_masser_P1_four_term` through the exclusion. -/
theorem badShift_bound_proof (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) :=
  badShift_bound_of_hexcl c hc (no_linear_param_proof c hc)

end Erdos477
