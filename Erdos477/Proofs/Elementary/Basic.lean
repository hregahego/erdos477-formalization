/-
  Stage A — Elementary facts L0.1–L0.6 (support lemmas, no frozen theorem).

  Contents (BLUEPRINT Stage A, items A1–A6; SKETCH §2):
    * A1  `zero_mem_B`, `zero_mem_D`
    * A2  `dset_neg`                       (symmetry of `Dset`, by swapping `u,v`)
    * A3  `pow13_inj`, `pow13_eq_iff`, `pow13_eq_neg`
    * A4  `not_B_ne_zero`
    * A5  `mem_D_symm_shift`
    * A6  `dset_eq_sub`                    (set EQUALITY bridging `Dset` to `B - B`)

  All support declarations live in `namespace Erdos477`; never shadow a frozen name.
-/
import Erdos477.Defs

namespace Erdos477

/-! ### A1 (L0.1) — `0` lies in `Bset` and in `Dset` -/

/-- **A1 / L0.1.** `0` is a thirteenth power (witness `m = 0`). -/
theorem zero_mem_B : (0 : ℤ) ∈ Bset := ⟨0, by norm_num⟩

/-- **A1 / L0.1.** `0` lies in the difference set (witnesses `u = v = 0`). -/
theorem zero_mem_D : (0 : ℤ) ∈ Dset := ⟨0, 0, by norm_num⟩

/-! ### A2 (L0.2) — symmetry of `Dset` -/

/-- **A2 / L0.2.** `Dset` is symmetric: if `d ∈ Dset` then `-d ∈ Dset`. Proved by
SWAPPING the two witnesses `u, v` (no odd-power sign manipulation). -/
theorem dset_neg : ∀ d : ℤ, d ∈ Dset → -d ∈ Dset := by
  rintro d ⟨u, v, rfl⟩
  exact ⟨v, u, by ring⟩

/-! ### A3 (L0.3) — global injectivity of `m ↦ m ^ 13` on `ℤ` -/

private theorem odd_thirteen : Odd (13 : ℕ) := ⟨6, by norm_num⟩

/-- **A3 / L0.3.** `m ↦ m ^ 13` is injective on all of `ℤ` (13 is odd, so the
map is strictly monotone). -/
theorem pow13_inj : Function.Injective (fun m : ℤ => m ^ 13) :=
  (Odd.strictMono_pow (R := ℤ) odd_thirteen).injective

/-- **A3 / L0.3, corollary.** `x ^ 13 = y ^ 13 ↔ x = y` on `ℤ`. -/
theorem pow13_eq_iff {x y : ℤ} : x ^ 13 = y ^ 13 ↔ x = y :=
  ⟨fun h => pow13_inj h, fun h => by rw [h]⟩

/-- **A3 / L0.3, corollary.** `x ^ 13 = -(y ^ 13) → x = -y` on `ℤ`. -/
theorem pow13_eq_neg {x y : ℤ} (h : x ^ 13 = -(y ^ 13)) : x = -y := by
  refine pow13_inj ?_
  simpa using h.trans (Odd.neg_pow odd_thirteen y).symm

/-! ### A4 (L0.5) — a non-thirteenth-power is nonzero -/

/-- **A4 / L0.5.** If `c` is not a thirteenth power then `c ≠ 0` (from `zero_mem_B`). -/
theorem not_B_ne_zero : ∀ c : ℤ, c ∉ Bset → c ≠ 0 := by
  intro c hc h0
  exact hc (h0 ▸ zero_mem_B)

/-! ### A5 (L0.6) — shifted symmetry -/

/-- **A5 / L0.6.** `c - t ^ 13 ∈ Dset ↔ t ^ 13 - c ∈ Dset` (A2 in both directions). -/
theorem mem_D_symm_shift : ∀ c t : ℤ, c - t ^ 13 ∈ Dset ↔ t ^ 13 - c ∈ Dset := by
  intro c t
  constructor
  · intro h
    have := dset_neg _ h
    simpa using this
  · intro h
    have := dset_neg _ h
    simpa using this

/-! ### A6 — the bridge `Dset = Bset - Bset` -/

/-- **A6.** Genuine set equality bridging the concrete `Dset` with the abstract
difference set `{d | ∃ x ∈ B, ∃ y ∈ B, d = x - y}` used by `greedy_tiling`. -/
theorem dset_eq_sub : Dset = {d : ℤ | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x - y} := by
  ext d
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨u ^ 13, ⟨u, rfl⟩, v ^ 13, ⟨v, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨u, rfl⟩, y, ⟨v, rfl⟩, rfl⟩
    exact ⟨u, v, rfl⟩

end Erdos477
