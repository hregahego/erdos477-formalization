/-
  Stage Elementary (Layer 0) — the objects `Bset` / `Dset`, and the L0.1–L0.6
  groundwork about them.

  Defines (the two set-level objects of the development; their binding modeling
  decisions, from `BLUEPRINT.md` Part −1 §2 / `USER_NOTES.md`, are quoted
  verbatim on the declarations below):
    * `Bset` — thirteenth powers as a `Set ℤ` carved by an existential, image
      form `b = m ^ 13`. Infinite; no positivity, no `b ≠ 0`. Exponent `13 : ℕ`.
    * `Dset` — the difference set encoded DIRECTLY as `u ^ 13 - v ^ 13`, NOT as
      the Minkowski difference `Bset - Bset`. Symmetry is a lemma
      (`Dset_neg_mem_proof` below), not baked in; the bridge
      `Dset_eq_Bset_sub` lives in `Proofs/Assembly`.
  Neither is needed to STATE the frozen headline `erdos_477`, so neither lives
  in the frozen `Erdos477/Defs.lean` — that file carries only the two assumed
  certificates and the definitions their statements quote.

  Proves (TASKS.md Iteration 1, Agent 2):
    * `Dset_neg_mem_proof`     — L0.2, CHARACTER-EXACT the frozen `Dset_neg_mem`
                                 type; witness swap `(u,v) ↦ (v,u)`, no sign
                                 manipulation.
    * `pow13_injective_proof`  — L0.3, CHARACTER-EXACT the frozen
                                 `pow13_injective` type; genuine injectivity on
                                 ALL of ℤ via `Odd.pow_injective`.
    * `zero_mem_Bset`          — L0.1 (witness `m = 0`).
    * `ne_zero_of_notMem_Bset` — L0.5 (contrapositive of L0.1).
    * `badShift_iff`           — L0.6 (two applications of L0.2).
    * `pow13_eq_neg`           — odd-power corollary `x¹³ = −y¹³ → x = −y`
                                 (used by ParamExclusion and Assembly).
    * `rat_pow13_int`          — L0.4 (rational 13th roots of integers are
                                 integers; ℤ integrally closed in ℚ) — needed
                                 by Route A.

  Support declarations live in `namespace Erdos477` and never shadow a frozen
  name; the frozen statements themselves live untouched in
  `Erdos477/Theorems.lean`.
-/
import Erdos477.Defs

namespace Erdos477

/-! ### The two set-level objects -/

/-- **D1 — `Bset`.** The set of thirteenth powers `{ m ^ 13 : m ∈ ℤ }` — the set
being tiled. Carved by an existential in image form `b = m ^ 13`; infinite. -/
def Bset : Set ℤ := {b | ∃ m : ℤ, b = m ^ 13}

/-- **D2 — `Dset`.** The difference set `B − B`, encoded directly as differences
of two thirteenth powers `u ^ 13 − v ^ 13` (NOT the Minkowski difference). -/
def Dset : Set ℤ := {d | ∃ u v : ℤ, d = u ^ 13 - v ^ 13}

/-! ### L0.1–L0.6 -/

/-- **L0.2 — `Dset` is symmetric.** From `d = u¹³ − v¹³` swap the witnesses:
`-d = v¹³ − u¹³`. -/
theorem Dset_neg_mem_proof {d : ℤ} (hd : d ∈ Dset) : -d ∈ Dset := by
  obtain ⟨u, v, rfl⟩ := hd
  exact ⟨v, u, by ring⟩

/-- **L0.3 — odd-power injectivity** of `m ↦ m¹³` on all of `ℤ` (13 is odd). -/
theorem pow13_injective_proof : Function.Injective (fun m : ℤ => m ^ 13) :=
  Odd.pow_injective (by decide)

/-- **L0.1 — `0 ∈ Bset`** (witness `m = 0`). -/
theorem zero_mem_Bset : (0 : ℤ) ∈ Bset :=
  ⟨0, by norm_num⟩

/-- **L0.5 — `c ∉ Bset → c ≠ 0`** (contrapositive of L0.1). -/
theorem ne_zero_of_notMem_Bset {c : ℤ} (hc : c ∉ Bset) : c ≠ 0 := by
  rintro rfl
  exact hc zero_mem_Bset

/-- **L0.6 — bad-shift membership reformulation:** each side is the negation of
the other, so L0.2 applies in both directions. -/
theorem badShift_iff {c t : ℤ} : c - t ^ 13 ∈ Dset ↔ t ^ 13 - c ∈ Dset := by
  constructor <;> intro h <;> simpa [neg_sub] using Dset_neg_mem_proof h

/-- **Odd-power sign corollary of L0.3:** `x¹³ = −(y¹³) → x = −y` (rewrite
`−(y¹³) = (−y)¹³`, then injectivity). -/
theorem pow13_eq_neg {x y : ℤ} (h : x ^ 13 = -(y ^ 13)) : x = -y := by
  apply pow13_injective_proof
  show x ^ 13 = (-y) ^ 13
  rw [Odd.neg_pow (by decide : Odd 13)]
  exact h

/-- **L0.4 — rational 13th roots of integers are integers.** A rational `d` with
`d¹³ = c ∈ ℤ` is a root of the monic integer polynomial `X¹³ − C c`, hence
integral over `ℤ`; `ℤ` is integrally closed in `ℚ`. -/
theorem rat_pow13_int : ∀ (c : ℤ) (d : ℚ), d ^ 13 = c → ∃ m : ℤ, (m : ℚ) = d := by
  intro c d h
  have hint : IsIntegral ℤ d := by
    refine ⟨Polynomial.X ^ 13 - Polynomial.C c,
      Polynomial.monic_X_pow_sub_C c (by norm_num), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    simp [h]
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨m, hm⟩

/-! ### Guardrail examples (BLUEPRINT "Cheat watch (Stage Elementary)") -/

example : (2 : ℤ) ^ 13 ≠ 3 ^ 13 := fun h => by
  have := pow13_injective_proof h
  norm_num at this

example : (-2 : ℤ) ^ 13 ≠ 2 ^ 13 := fun h => by
  have := pow13_injective_proof h
  norm_num at this

-- `Dset_neg_mem_proof` closes on an arbitrary opened witness:
example (u v : ℤ) : -(u ^ 13 - v ^ 13) ∈ Dset :=
  Dset_neg_mem_proof ⟨u, v, rfl⟩

end Erdos477
