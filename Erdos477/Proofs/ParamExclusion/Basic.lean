/-
  Stage C — Parametrisation exclusion L2.1, Route B (proves `no_linear_param`).

  SKETCH §5.1 (Route B, elementary): a triple of polynomials of degree ≤ 1 whose
  thirteenth powers sum to the constant `-c` must consist of constants, provided
  `c ∉ Bset`.

  Route A (`brownawell_masser_P1_four_term`) is NOT used anywhere here.

  Contents:
    * `coeff_lin_pow13`      — the binomial coefficient formula for `(C a * X + C b) ^ 13`.
    * `two_nonzero_case`     — the `|I| = 2` crux: it forces `c ∈ Bset`.
    * `linear_coeff_vanish`  — the arithmetic core (C3): the four coefficient
                               equations `E₀, E₁, E₂, E₁₃` force `a₁ = a₂ = a₃ = 0`.
    * `no_linear_param_proof`— the frozen statement.
-/
import Erdos477.Defs
import Erdos477.Proofs.Elementary.Basic

namespace Erdos477

open Polynomial

/-- **C2 (coefficient extraction).** The `k`-th coefficient of `(a·X + b) ^ 13` is
`C(13,k) · a ^ k · b ^ (13 - k)` (for `k ≤ 13`). -/
theorem coeff_lin_pow13 (a b : ℤ) (k : ℕ) (hk : k ≤ 13) :
    ((C a * X + C b : Polynomial ℤ) ^ 13).coeff k
      = (Nat.choose 13 k : ℤ) * a ^ k * b ^ (13 - k) := by
  rw [add_pow, Polynomial.finsetSum_coeff]
  have key : ∀ m : ℕ, ((C a * X) ^ m * C b ^ (13 - m) * (Nat.choose 13 m : ℤ[X])).coeff k
      = if m = k then (Nat.choose 13 m : ℤ) * a ^ m * b ^ (13 - m) else 0 := by
    intro m
    have h : ((C a * X) ^ m * C b ^ (13 - m) * (Nat.choose 13 m : ℤ[X]))
        = C ((Nat.choose 13 m : ℤ) * a ^ m * b ^ (13 - m)) * X ^ m := by
      simp only [mul_pow, ← C_pow, ← C_eq_natCast, C_mul]
      ring
    rw [h, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hm : m = k
    · simp [hm]
    · simp [hm, Ne.symm hm]
  simp only [key]
  rw [Finset.sum_ite_eq' (Finset.range 14) k
    (fun m => (Nat.choose 13 m : ℤ) * a ^ m * b ^ (13 - m))]
  simp [Finset.mem_range, Nat.lt_succ_of_le hk]

/-- **C3, the `|I| = 2` case.** If exactly two of the leading coefficients are
nonzero (here `a` and `a'`), the top two coefficient equations force `a = -a'` and
`b' = -b`, so the two corresponding polynomials cancel and `c = (-b'') ^ 13 ∈ Bset`. -/
theorem two_nonzero_case (a a' b b' b'' c : ℤ) (ha' : a' ≠ 0)
    (E0 : a ^ 13 + a' ^ 13 = 0) (E1 : a ^ 12 * b + a' ^ 12 * b' = 0)
    (E13 : b ^ 13 + b' ^ 13 + b'' ^ 13 = -c) : c ∈ Bset := by
  have haa : a = -a' := pow13_eq_neg (by linarith)
  subst haa
  have h12 : (-a') ^ 12 * b + a' ^ 12 * b' = a' ^ 12 * (b + b') := by ring
  rw [h12] at E1
  have hb : b + b' = 0 := by
    rcases mul_eq_zero.mp E1 with h | h
    · exact absurd (pow_eq_zero_iff (n := 12) (by norm_num) |>.mp h) ha'
    · exact h
  have hb' : b' = -b := by linarith
  subst hb'
  refine ⟨-b'', ?_⟩
  have : b ^ 13 + (-b) ^ 13 = 0 := by ring
  have hcc : b'' ^ 13 = -c := by linarith
  linarith [hcc, (by ring : (-b'') ^ 13 = -(b'' ^ 13))]

/-- **C3 (arithmetic core).** The four coefficient equations coming from
`∑ pᵢ ^ 13 = C (-c)` force every leading coefficient to vanish, given `c ∉ Bset`. -/
theorem linear_coeff_vanish (c a₁ a₂ a₃ b₁ b₂ b₃ : ℤ) (hc : c ∉ Bset)
    (E0 : a₁ ^ 13 + a₂ ^ 13 + a₃ ^ 13 = 0)
    (E1 : a₁ ^ 12 * b₁ + a₂ ^ 12 * b₂ + a₃ ^ 12 * b₃ = 0)
    (E2 : a₁ ^ 11 * b₁ ^ 2 + a₂ ^ 11 * b₂ ^ 2 + a₃ ^ 11 * b₃ ^ 2 = 0)
    (E13 : b₁ ^ 13 + b₂ ^ 13 + b₃ ^ 13 = -c) :
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
  -- a singleton nonzero leading coefficient is impossible: `E0` makes it zero.
  have single : ∀ x y z : ℤ, x = 0 → y = 0 → x ^ 13 + y ^ 13 + z ^ 13 = 0 → z = 0 := by
    intro x y z hx hy h
    subst hx; subst hy
    have : z ^ 13 = 0 := by linarith [(by ring : (0:ℤ) ^ 13 = 0)]
    exact pow_eq_zero_iff (n := 13) (by norm_num) |>.mp this
  by_cases h1 : a₁ = 0 <;> by_cases h2 : a₂ = 0 <;> by_cases h3 : a₃ = 0
  · exact ⟨h1, h2, h3⟩
  -- exactly one nonzero
  · exact absurd (single a₁ a₂ a₃ h1 h2 E0) h3
  · exact absurd (single a₁ a₃ a₂ h1 h3 (by linarith)) h2
  · exact absurd (hc (two_nonzero_case a₂ a₃ b₂ b₃ b₁ c h3
      (by rw [h1] at E0; linarith [(by ring : (0:ℤ) ^ 13 = 0)])
      (by rw [h1] at E1; linarith [(by ring : (0:ℤ) ^ 12 * b₁ = 0)])
      (by linarith))) (by trivial)
  · exact absurd (single a₂ a₃ a₁ h2 h3 (by linarith)) h1
  · exact absurd (hc (two_nonzero_case a₁ a₃ b₁ b₃ b₂ c h3
      (by rw [h2] at E0; linarith [(by ring : (0:ℤ) ^ 13 = 0)])
      (by rw [h2] at E1; linarith [(by ring : (0:ℤ) ^ 12 * b₂ = 0)])
      (by linarith))) (by trivial)
  · exact absurd (hc (two_nonzero_case a₁ a₂ b₁ b₂ b₃ c h2
      (by rw [h3] at E0; linarith [(by ring : (0:ℤ) ^ 13 = 0)])
      (by rw [h3] at E1; linarith [(by ring : (0:ℤ) ^ 12 * b₃ = 0)])
      (by linarith))) (by trivial)
  -- all three nonzero: the Vandermonde / equal-ratio argument, over ℚ
  · exfalso
    have hA₁ : (a₁ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h1
    have hA₂ : (a₂ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h2
    have hA₃ : (a₃ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h3
    obtain ⟨q₁, hb₁⟩ : ∃ q : ℚ, (b₁ : ℚ) = q * (a₁ : ℚ) :=
      ⟨(b₁ : ℚ) / (a₁ : ℚ), by field_simp⟩
    obtain ⟨q₂, hb₂⟩ : ∃ q : ℚ, (b₂ : ℚ) = q * (a₂ : ℚ) :=
      ⟨(b₂ : ℚ) / (a₂ : ℚ), by field_simp⟩
    obtain ⟨q₃, hb₃⟩ : ∃ q : ℚ, (b₃ : ℚ) = q * (a₃ : ℚ) :=
      ⟨(b₃ : ℚ) / (a₃ : ℚ), by field_simp⟩
    have F0 : (a₁ : ℚ) ^ 13 + (a₂ : ℚ) ^ 13 + (a₃ : ℚ) ^ 13 = 0 := by exact_mod_cast E0
    have F1 : (a₁ : ℚ) ^ 13 * q₁ + (a₂ : ℚ) ^ 13 * q₂ + (a₃ : ℚ) ^ 13 * q₃ = 0 := by
      have : (a₁ : ℚ) ^ 12 * (b₁ : ℚ) + (a₂ : ℚ) ^ 12 * (b₂ : ℚ)
          + (a₃ : ℚ) ^ 12 * (b₃ : ℚ) = 0 := by exact_mod_cast E1
      rw [hb₁, hb₂, hb₃] at this
      linear_combination this
    have F2 : (a₁ : ℚ) ^ 13 * q₁ ^ 2 + (a₂ : ℚ) ^ 13 * q₂ ^ 2
        + (a₃ : ℚ) ^ 13 * q₃ ^ 2 = 0 := by
      have : (a₁ : ℚ) ^ 11 * (b₁ : ℚ) ^ 2 + (a₂ : ℚ) ^ 11 * (b₂ : ℚ) ^ 2
          + (a₃ : ℚ) ^ 11 * (b₃ : ℚ) ^ 2 = 0 := by exact_mod_cast E2
      rw [hb₁, hb₂, hb₃] at this
      linear_combination this
    have F13 : (b₁ : ℚ) ^ 13 + (b₂ : ℚ) ^ 13 + (b₃ : ℚ) ^ 13 = -(c : ℚ) := by
      exact_mod_cast E13
    -- `∑ wᵢ (qᵢ - qⱼ)(qᵢ - qₖ) = 0` isolates a single term
    have hw₁ : ((q₁ - q₂) * (q₁ - q₃)) = 0 := by
      have h : (a₁ : ℚ) ^ 13 * ((q₁ - q₂) * (q₁ - q₃)) = 0 := by
        linear_combination F2 - (q₂ + q₃) * F1 + q₂ * q₃ * F0
      rcases mul_eq_zero.mp h with h | h
      · exact absurd (pow_eq_zero_iff (n := 13) (by norm_num) |>.mp h) hA₁
      · exact h
    have hw₂ : ((q₂ - q₁) * (q₂ - q₃)) = 0 := by
      have h : (a₂ : ℚ) ^ 13 * ((q₂ - q₁) * (q₂ - q₃)) = 0 := by
        linear_combination F2 - (q₁ + q₃) * F1 + q₁ * q₃ * F0
      rcases mul_eq_zero.mp h with h | h
      · exact absurd (pow_eq_zero_iff (n := 13) (by norm_num) |>.mp h) hA₂
      · exact h
    have hw₃ : ((q₃ - q₁) * (q₃ - q₂)) = 0 := by
      have h : (a₃ : ℚ) ^ 13 * ((q₃ - q₁) * (q₃ - q₂)) = 0 := by
        linear_combination F2 - (q₁ + q₂) * F1 + q₁ * q₂ * F0
      rcases mul_eq_zero.mp h with h | h
      · exact absurd (pow_eq_zero_iff (n := 13) (by norm_num) |>.mp h) hA₃
      · exact h
    -- hence all three ratios coincide
    have h12 : q₁ = q₂ := by
      by_contra hne
      have e13 : q₁ = q₃ := by
        rcases mul_eq_zero.mp hw₁ with h | h
        · exact absurd (sub_eq_zero.mp h) hne
        · exact sub_eq_zero.mp h
      have e23 : q₂ = q₃ := by
        rcases mul_eq_zero.mp hw₂ with h | h
        · exact absurd (sub_eq_zero.mp h).symm hne
        · exact sub_eq_zero.mp h
      exact hne (e13.trans e23.symm)
    have h13 : q₁ = q₃ := by
      by_contra hne
      have e12 : q₁ = q₂ := h12
      have e23 : q₃ = q₂ := by
        rcases mul_eq_zero.mp hw₃ with h | h
        · exact absurd (sub_eq_zero.mp h).symm hne
        · exact sub_eq_zero.mp h
      exact hne (e12.trans e23.symm)
    -- common ratio ⇒ `-c = q₁ ^ 13 * (∑ aᵢ ^ 13) = 0`
    rw [hb₁, hb₂, hb₃, ← h12, ← h13] at F13
    have hc0 : (c : ℚ) = 0 := by linear_combination F13 - q₁ ^ 13 * F0
    have : c = 0 := by exact_mod_cast hc0
    exact hc (this ▸ zero_mem_B)

/-- **L2.1 / Stage C — the frozen `no_linear_param`.** For `c ∉ Bset`, every triple
of polynomials of degree ≤ 1 with `p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = C (-c)` consists of
constants. This is exactly the exclusion hypothesis `hexcl` of
`heath_brown_diagonal_13` at `M = -c`. -/
theorem no_linear_param_proof (c : ℤ) (hc : c ∉ Bset) :
    ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 := by
  intro p₁ p₂ p₃ hsum h1 h2 h3
  -- C1: write each `pᵢ` as `C aᵢ * X + C bᵢ`
  obtain ⟨a₁, b₁, hp₁⟩ : ∃ a b, p₁ = C a * X + C b :=
    ⟨_, _, eq_X_add_C_of_natDegree_le_one h1⟩
  obtain ⟨a₂, b₂, hp₂⟩ : ∃ a b, p₂ = C a * X + C b :=
    ⟨_, _, eq_X_add_C_of_natDegree_le_one h2⟩
  obtain ⟨a₃, b₃, hp₃⟩ : ∃ a b, p₃ = C a * X + C b :=
    ⟨_, _, eq_X_add_C_of_natDegree_le_one h3⟩
  -- C2: the coefficient equations
  have hco : ∀ k : ℕ, k ≤ 13 →
      (Nat.choose 13 k : ℤ) * a₁ ^ k * b₁ ^ (13 - k)
      + (Nat.choose 13 k : ℤ) * a₂ ^ k * b₂ ^ (13 - k)
      + (Nat.choose 13 k : ℤ) * a₃ ^ k * b₃ ^ (13 - k)
        = if k = 0 then -c else 0 := by
    intro k hk
    rw [← coeff_lin_pow13 a₁ b₁ k hk, ← coeff_lin_pow13 a₂ b₂ k hk,
      ← coeff_lin_pow13 a₃ b₃ k hk, ← Polynomial.coeff_add, ← Polynomial.coeff_add,
      ← hp₁, ← hp₂, ← hp₃, hsum]
    exact Polynomial.coeff_C
  have E0 : a₁ ^ 13 + a₂ ^ 13 + a₃ ^ 13 = 0 := by
    have := hco 13 (le_refl _); norm_num at this; linarith
  have E1' : (13 : ℤ) * (a₁ ^ 12 * b₁ + a₂ ^ 12 * b₂ + a₃ ^ 12 * b₃) = 0 := by
    have := hco 12 (by norm_num); norm_num at this; linarith
  have E2' : (78 : ℤ) * (a₁ ^ 11 * b₁ ^ 2 + a₂ ^ 11 * b₂ ^ 2 + a₃ ^ 11 * b₃ ^ 2) = 0 := by
    have := hco 11 (by norm_num)
    rw [show Nat.choose 13 11 = 78 from rfl] at this
    norm_num at this; linarith
  have E13 : b₁ ^ 13 + b₂ ^ 13 + b₃ ^ 13 = -c := by
    have := hco 0 (by norm_num); norm_num at this; linarith
  have E1 : a₁ ^ 12 * b₁ + a₂ ^ 12 * b₂ + a₃ ^ 12 * b₃ = 0 := by
    rcases mul_eq_zero.mp E1' with h | h
    · norm_num at h
    · exact h
  have E2 : a₁ ^ 11 * b₁ ^ 2 + a₂ ^ 11 * b₂ ^ 2 + a₃ ^ 11 * b₃ ^ 2 = 0 := by
    rcases mul_eq_zero.mp E2' with h | h
    · norm_num at h
    · exact h
  -- C3
  obtain ⟨ha₁, ha₂, ha₃⟩ := linear_coeff_vanish c a₁ a₂ a₃ b₁ b₂ b₃ hc E0 E1 E2 E13
  subst ha₁; subst ha₂; subst ha₃
  refine ⟨?_, ?_, ?_⟩ <;> simp [hp₁, hp₂, hp₃]

end Erdos477
