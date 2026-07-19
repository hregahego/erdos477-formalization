/-
  Stage B — Cofactor lower bound L1.1–L1.2 (support lemmas, no frozen theorem).

  Contents (BLUEPRINT Stage B, items B1–B3 = SKETCH §4):
    * `qcof_factor` (B1)  : `u ^ 13 - v ^ 13 = (u - v) * Qcof u v` over `ℤ`.
    * `qcof_lower`  (B2)  : `(1/2) * max |u| |v| ^ 12 ≤ Q(u,v)` for ALL reals,
                            with the honest explicit constant `1/2`.
    * `pow13_gap`   (B3)  : the gap bound for DISTINCT integers `u ≠ v`.

  Only `Erdos477.Defs` and Mathlib are used (Stage B consumes no Stage-A lemma).
-/
import Erdos477.Defs

namespace Erdos477

/-! ### B1 — the factorization `u ^ 13 - v ^ 13 = (u - v) * Q(u,v)` -/

/-- The factorization identity over an arbitrary commutative ring; the `ℤ`-level
statement `qcof_factor` and its real-valued counterpart used in `pow13_gap` are
both instances of it. -/
theorem sub_pow13_eq (R : Type*) [CommRing R] (u v : R) :
    u ^ 13 - v ^ 13 = (u - v) * ∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- **B1.** `u ^ 13 - v ^ 13 = (u - v) * Qcof u v`. -/
theorem qcof_factor (u v : ℤ) : u ^ 13 - v ^ 13 = (u - v) * Qcof u v :=
  sub_pow13_eq ℤ u v

/-- Guardrail for `qcof_factor` at the concrete pair `u = 2, v = 1`. -/
example : (2 : ℤ) ^ 13 - 1 ^ 13 = (2 - 1) * Qcof 2 1 := by
  norm_num [Qcof, Finset.sum_range_succ]

/-! ### B2 — the explicit cofactor lower bound with `κ = 1/2` -/

/-- Sum-of-squares identity behind the explicit bound: for all reals,
`2 * Q(u,v) = u ^ 12 + v ^ 12 + (six squares)`.

This is the algebraic core replacing the `s = v/u` substitution of SKETCH §4:
for odd `i`, `u^(i-1) v^(13-i) + 2 u^i v^(12-i) + u^(i+1) v^(11-i)` is the square
`(u^((i-1)/2) v^((13-i)/2) + u^((i+1)/2) v^((11-i)/2))^2`, and summing these six
squares accounts for every term of `2 Q` except `u ^ 12 + v ^ 12`. -/
theorem two_mul_qcof_eq (u v : ℝ) :
    2 * ∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i)
      = u ^ 12 + v ^ 12
        + (v ^ 6 + u * v ^ 5) ^ 2 + (u * v ^ 5 + u ^ 2 * v ^ 4) ^ 2
        + (u ^ 2 * v ^ 4 + u ^ 3 * v ^ 3) ^ 2 + (u ^ 3 * v ^ 3 + u ^ 4 * v ^ 2) ^ 2
        + (u ^ 4 * v ^ 2 + u ^ 5 * v) ^ 2 + (u ^ 5 * v + u ^ 6) ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- `max |u| |v| ^ 12 ≤ u ^ 12 + v ^ 12`. -/
theorem max_abs_pow12_le (u v : ℝ) : (max |u| |v|) ^ 12 ≤ u ^ 12 + v ^ 12 := by
  have hu : |u| ^ 12 = u ^ 12 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ 12)]
  have hv : |v| ^ 12 = v ^ 12 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ v ^ 12)]
  have hu0 : (0:ℝ) ≤ u ^ 12 := by positivity
  have hv0 : (0:ℝ) ≤ v ^ 12 := by positivity
  rcases max_cases |u| |v| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · rw [hu]; linarith
  · rw [hv]; linarith

/-- **B2 (L1.1).** The explicit cofactor lower bound, for ALL reals, with the
honest constant `1/2`:
`(1/2) * max |u| |v| ^ 12 ≤ ∑ i ∈ range 13, u ^ i * v ^ (12 - i)`. -/
theorem qcof_lower (u v : ℝ) :
    (1/2) * (max |u| |v|) ^ 12 ≤ ∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i) := by
  have hid := two_mul_qcof_eq u v
  have hmax := max_abs_pow12_le u v
  have h1 : (0:ℝ) ≤ (v ^ 6 + u * v ^ 5) ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ (u * v ^ 5 + u ^ 2 * v ^ 4) ^ 2 := sq_nonneg _
  have h3 : (0:ℝ) ≤ (u ^ 2 * v ^ 4 + u ^ 3 * v ^ 3) ^ 2 := sq_nonneg _
  have h4 : (0:ℝ) ≤ (u ^ 3 * v ^ 3 + u ^ 4 * v ^ 2) ^ 2 := sq_nonneg _
  have h5 : (0:ℝ) ≤ (u ^ 4 * v ^ 2 + u ^ 5 * v) ^ 2 := sq_nonneg _
  have h6 : (0:ℝ) ≤ (u ^ 5 * v + u ^ 6) ^ 2 := sq_nonneg _
  linarith

/-- Nonnegativity of the real cofactor (immediate corollary of `qcof_lower`). -/
theorem qcof_nonneg (u v : ℝ) :
    (0:ℝ) ≤ ∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i) := by
  have h0 : (0:ℝ) ≤ (1/2) * (max |u| |v|) ^ 12 := by positivity
  linarith [qcof_lower u v]

/-! ### B3 — the gap bound for distinct integers -/

/-- **B3 (L1.2).** For DISTINCT integers `u ≠ v`,
`(1/2) * max |u| |v| ^ 12 ≤ |u ^ 13 - v ^ 13|` (as reals). -/
theorem pow13_gap (u v : ℤ) (huv : u ≠ v) :
    (1/2) * (max |(u:ℝ)| |(v:ℝ)|) ^ 12 ≤ |(u:ℝ) ^ 13 - (v:ℝ) ^ 13| := by
  set Q : ℝ := ∑ i ∈ Finset.range 13, (u:ℝ) ^ i * (v:ℝ) ^ (12 - i) with hQdef
  have hfac : (u:ℝ) ^ 13 - (v:ℝ) ^ 13 = ((u:ℝ) - (v:ℝ)) * Q := sub_pow13_eq ℝ _ _
  have hQ0 : (0:ℝ) ≤ Q := qcof_nonneg _ _
  have hone : (1:ℝ) ≤ |(u:ℝ) - (v:ℝ)| := by
    have h : (1:ℤ) ≤ |u - v| := Int.one_le_abs (sub_ne_zero.mpr huv)
    have h' := (Int.cast_le (R := ℝ)).mpr h
    rwa [Int.cast_one, Int.cast_abs, Int.cast_sub] at h'
  calc (1/2) * (max |(u:ℝ)| |(v:ℝ)|) ^ 12 ≤ Q := qcof_lower _ _
    _ = 1 * Q := (one_mul Q).symm
    _ ≤ |(u:ℝ) - (v:ℝ)| * Q := mul_le_mul_of_nonneg_right hone hQ0
    _ = |(u:ℝ) - (v:ℝ)| * |Q| := by rw [abs_of_nonneg hQ0]
    _ = |((u:ℝ) - (v:ℝ)) * Q| := (abs_mul _ _).symm
    _ = |(u:ℝ) ^ 13 - (v:ℝ) ^ 13| := by rw [hfac]

end Erdos477
