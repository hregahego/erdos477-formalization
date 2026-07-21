/-
  Stage Cofactor (Layer 1) — pow13_sub_pow13_factor, cofactor_lower_bound (κ = 1/2), pow13_gap.

  C1 — `pow13_sub_pow13_factor_proof`: `u¹³ − v¹³ = (u − v) · Qcof u v` over ℤ,
       from the polymorphic `Qcof_mul_sub` (via `geom_sum₂_mul`).
  C2 — `cofactor_lower_bound_proof`:  `(1/2) · max |u| |v| ^ 12 ≤ Qcof u v` for ALL real
       `u v`, constant exactly 1/2, per SKETCH.md §4 L1.1 (symmetry + `s = v/u` reduction +
       geometric-sum lower bound `q(s) ≥ 1/2` on `[−1,1]`).
  C3 — `pow13_gap_proof`: gap bound for distinct integer thirteenth powers, from C1 + C2
       and `|u − v| ≥ 1`.

  Statements are CHARACTER-EXACT copies of the frozen types in `Erdos477/Theorems.lean`.
  No new axioms; everything here depends on at most {propext, Classical.choice, Quot.sound}.
-/
import Erdos477.Defs

namespace Erdos477

open Finset

/-! ### Support lemmas -/

/-- The cofactor sum against `u − v` telescopes to `u¹³ − v¹³` (polymorphic, so the same
lemma serves the ℤ factorization C1 and the ℝ manipulations in C3). -/
theorem Qcof_mul_sub {R : Type*} [CommRing R] (u v : R) :
    Qcof u v * (u - v) = u ^ 13 - v ^ 13 := by
  rw [Qcof]
  simpa using geom_sum₂_mul u v 13

/-- Symmetry of the cofactor: reindex the sum by `i ↦ 12 − i`. -/
theorem Qcof_comm {R : Type*} [CommRing R] (u v : R) : Qcof u v = Qcof v u := by
  rw [Qcof, Qcof, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have h1 : 13 - 1 - i = 12 - i := by omega
  have h2 : 12 - (12 - i) = i := by omega
  rw [h1, h2, mul_comm]

/-- The truncated geometric sum `q(s) = ∑_{j<13} sʲ` is at least `1/2` on `[−1, 1]`. -/
theorem geom13_ge_half {s : ℝ} (hs : |s| ≤ 1) :
    (1 / 2 : ℝ) ≤ ∑ j ∈ Finset.range 13, s ^ j := by
  obtain ⟨hlb, hub⟩ := abs_le.mp hs
  by_cases h0 : 0 ≤ s
  · -- `0 ≤ s`: every summand is nonnegative and the `j = 0` summand is `1`.
    have h1 : (1 : ℝ) ≤ ∑ j ∈ Finset.range 13, s ^ j := by
      calc (1 : ℝ) = s ^ 0 := (pow_zero s).symm
        _ ≤ ∑ j ∈ Finset.range 13, s ^ j :=
          Finset.single_le_sum (fun j _ => pow_nonneg h0 j)
            (Finset.mem_range.mpr (by norm_num))
    linarith
  · -- `−1 ≤ s < 0`: use `q(s) · (1 − s) = 1 − s¹³`, with `s¹³ < 0` and `0 < 1 − s ≤ 2`.
    rw [not_le] at h0
    have hgeom : (∑ j ∈ Finset.range 13, s ^ j) * (s - 1) = s ^ 13 - 1 := geom_sum_mul s 13
    have hmul : (∑ j ∈ Finset.range 13, s ^ j) * (1 - s) = 1 - s ^ 13 := by
      linear_combination -hgeom
    have hs13 : s ^ 13 < 0 := Odd.pow_neg (by norm_num) h0
    have h1s : (0 : ℝ) < 1 - s := by linarith
    have hkey : (1 / 2 : ℝ) * (1 - s) ≤ (∑ j ∈ Finset.range 13, s ^ j) * (1 - s) := by
      rw [hmul]; linarith
    exact le_of_mul_le_mul_right hkey h1s

/-- The asymmetric half of L1.1: the bound with `max |u| |v|` replaced by `|u|`,
under `|v| ≤ |u|`. -/
theorem cofactor_lower_bound_of_le {u v : ℝ} (hvu : |v| ≤ |u|) :
    (1 / 2 : ℝ) * |u| ^ 12 ≤ Qcof u v := by
  rcases eq_or_ne u 0 with hu | hu
  · -- `u = 0` forces `v = 0`; both sides vanish.
    have hv : v = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hu] using hvu) (abs_nonneg v))
    subst hu; subst hv
    norm_num [Qcof, Finset.sum_range_succ]
  · -- `u ≠ 0`: put `s = v / u ∈ [−1, 1]` and factor `Qcof u v = u¹² · q(s)`.
    set s : ℝ := v / u with hs_def
    have hu12 : (0 : ℝ) < u ^ 12 := by positivity
    have habs : |s| ≤ 1 := by
      rw [hs_def, abs_div, div_le_one (abs_pos.mpr hu)]
      exact hvu
    have hterm : ∀ i ∈ Finset.range 13, u ^ i * v ^ (12 - i) = u ^ 12 * s ^ (12 - i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hpow : u ^ i = u ^ 12 / u ^ (12 - i) := by
        rw [eq_div_iff (pow_ne_zero _ hu), ← pow_add]
        congr 1
        omega
      rw [hpow, hs_def, div_pow]
      ring
    have hfac : Qcof u v = u ^ 12 * ∑ j ∈ Finset.range 13, s ^ j := by
      rw [Qcof, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      congr 1
      have hreflect := Finset.sum_range_reflect (fun j => s ^ j) 13
      simpa using hreflect
    have hq := geom13_ge_half habs
    have h12eq : |u| ^ 12 = u ^ 12 := Even.pow_abs (by norm_num) u
    calc (1 / 2 : ℝ) * |u| ^ 12 = u ^ 12 * (1 / 2) := by rw [h12eq]; ring
      _ ≤ u ^ 12 * ∑ j ∈ Finset.range 13, s ^ j := by
          exact mul_le_mul_of_nonneg_left hq hu12.le
      _ = Qcof u v := hfac.symm

/-! ### The three frozen statements (types character-exact to `Erdos477/Theorems.lean`) -/

/-- **C1 / §4 display.** `u¹³ − v¹³ = (u − v) · Q(u,v)` over `ℤ`. -/
theorem pow13_sub_pow13_factor_proof (u v : ℤ) :
    u ^ 13 - v ^ 13 = (u - v) * Qcof u v := by
  rw [← Qcof_mul_sub u v, mul_comm]

/-- **C2 / L1.1 — explicit cofactor lower bound** (`κ = 1/2`), over `ℝ`. -/
theorem cofactor_lower_bound_proof (u v : ℝ) :
    (1 / 2 : ℝ) * max |u| |v| ^ 12 ≤ Qcof u v := by
  rcases le_total |v| |u| with h | h
  · rw [max_eq_left h]
    exact cofactor_lower_bound_of_le h
  · rw [max_eq_right h, Qcof_comm]
    exact cofactor_lower_bound_of_le h

/-- **C3 / L1.2 — gap bound** for distinct integer thirteenth powers. -/
theorem pow13_gap_proof (u v : ℤ) (huv : u ≠ v) :
    (1 / 2 : ℝ) * max |(u : ℝ)| |(v : ℝ)| ^ 12 ≤ |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| := by
  have hQ : (0 : ℝ) ≤ Qcof (u : ℝ) (v : ℝ) := by
    refine le_trans ?_ (cofactor_lower_bound_proof (u : ℝ) (v : ℝ))
    have hmax : (0 : ℝ) ≤ max |(u : ℝ)| |(v : ℝ)| := le_trans (abs_nonneg _) (le_max_left _ _)
    positivity
  have h1 : (1 : ℝ) ≤ |(u : ℝ) - (v : ℝ)| := by
    have hne : u - v ≠ 0 := sub_ne_zero.mpr huv
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ |((u - v : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hne
      _ = |(u : ℝ) - (v : ℝ)| := by push_cast; rfl
  have hfac : (u : ℝ) ^ 13 - (v : ℝ) ^ 13 = ((u : ℝ) - (v : ℝ)) * Qcof (u : ℝ) (v : ℝ) := by
    rw [← Qcof_mul_sub, mul_comm]
  calc (1 / 2 : ℝ) * max |(u : ℝ)| |(v : ℝ)| ^ 12
      ≤ Qcof (u : ℝ) (v : ℝ) := cofactor_lower_bound_proof (u : ℝ) (v : ℝ)
    _ = 1 * Qcof (u : ℝ) (v : ℝ) := (one_mul _).symm
    _ ≤ |(u : ℝ) - (v : ℝ)| * Qcof (u : ℝ) (v : ℝ) := mul_le_mul_of_nonneg_right h1 hQ
    _ = |(u : ℝ) - (v : ℝ)| * |Qcof (u : ℝ) (v : ℝ)| := by rw [abs_of_nonneg hQ]
    _ = |((u : ℝ) - (v : ℝ)) * Qcof (u : ℝ) (v : ℝ)| := (abs_mul _ _).symm
    _ = |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| := by rw [← hfac]

/-! ### Guardrail examples (BLUEPRINT "Cheat watch (Stage Cofactor)") -/

example : Qcof (1 : ℝ) (-1) = 1 := by norm_num [Qcof, Finset.sum_range_succ]

example : (1 / 2 : ℝ) * max |(1 : ℝ)| |(-1 : ℝ)| ^ 12 ≤ Qcof (1 : ℝ) (-1) :=
  cofactor_lower_bound_proof 1 (-1)

end Erdos477
