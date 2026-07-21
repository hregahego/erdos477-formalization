/-
  Stage Greedy (Layer 4) — `greedy_tiling` — the self-contained combinatorial
  criterion (MILESTONE; independent of all number theory).

  Proves `Erdos477.greedy_tiling_proof`, whose statement is character-exact to
  the frozen `Erdos477.greedy_tiling` in `Erdos477/Theorems.lean`, following
  SKETCH.md §7 (L4.1): enumerate `ℤ` via `Denumerable`, build a greedy sequence
  `Aseq : ℕ → Finset ℤ` with invariants (I1) `D`-separatedness and (I2)
  coverage of the enumerated integers, and take `A = ⋃ j, Aseq j`.

  Everything here is generic in an abstract `B : Set ℤ`; the difference set is
  the abstract `{d | ∃ x ∈ B, ∃ y ∈ B, d = x - y}` (its symmetry is proved by
  swapping witnesses — `Dset` and `Dset_neg_mem` are never used).
-/
import Erdos477.Defs

namespace Erdos477

namespace Greedy

open scoped Classical

/-- The abstract difference set `B − B` of the criterion (generic in `B`;
deliberately NOT `Dset`). -/
def D (B : Set ℤ) : Set ℤ := {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}

/-- Abstract analogue of L0.2: the difference set is symmetric — swap the
witnesses `(x, y) ↦ (y, x)`. -/
theorem D_neg_mem {B : Set ℤ} {d : ℤ} (hd : d ∈ D B) : -d ∈ D B := by
  obtain ⟨x, hx, y, hy, rfl⟩ := hd
  exact ⟨y, hy, x, hx, by ring⟩

/-- Invariant `(I1)`: a finite set is `D`-separated. -/
def Separated (B : Set ℤ) (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → a - a' ∉ D B

/-- The enumeration `n₀, n₁, n₂, …` of `ℤ` (via `Denumerable ℤ`). -/
def enum : ℕ → ℤ := (Denumerable.eqv ℤ).symm

theorem enum_surjective : Function.Surjective enum :=
  (Denumerable.eqv ℤ).symm.surjective

section

variable {B : Set ℤ}
variable (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
    ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y})

/-- Case 2 setup: if `n` is not yet covered by `A + B`, then
`C = (A).image (n − ·)` avoids `B`. -/
theorem image_subset_compl {A : Finset ℤ} {n : ℤ}
    (hcase : ¬ ∃ a ∈ A, ∃ b ∈ B, a + b = n) :
    ∀ c ∈ A.image (fun a => n - a), c ∉ B := by
  intro c hc hcB
  rw [Finset.mem_image] at hc
  obtain ⟨a, ha, rfl⟩ := hc
  exact hcase ⟨a, ha, n - a, hcB, by ring⟩

include H

/-- `H` applied to `C = ∅` gives `B ≠ ∅`. -/
theorem B_nonempty : B.Nonempty := by
  obtain ⟨b, hb, -⟩ := H ∅ (by simp)
  exact ⟨b, hb⟩

/-- `0 ∈ B − B` (needs `B ≠ ∅`). -/
theorem zero_mem_D : (0 : ℤ) ∈ D B := by
  obtain ⟨b, hb⟩ := B_nonempty H
  exact ⟨b, hb, b, hb, by ring⟩

private theorem exists_good (C : Finset ℤ) :
    ∃ b : ℤ, (∀ c ∈ C, c ∉ B) → b ∈ B ∧ ∀ c ∈ C, c - b ∉ D B := by
  by_cases h : ∀ c ∈ C, c ∉ B
  · obtain ⟨b, hb, hav⟩ := H C h
    exact ⟨b, fun _ => ⟨hb, hav⟩⟩
  · exact ⟨0, fun hh => absurd hh h⟩

/-- The good `b ∈ B` chosen (classically) via `H` for a finite `C ⊆ ℤ \ B`
(junk value otherwise). -/
noncomputable def pick (C : Finset ℤ) : ℤ := (exists_good H C).choose

theorem pick_spec {C : Finset ℤ} (h : ∀ c ∈ C, c ∉ B) :
    pick H C ∈ B ∧ ∀ c ∈ C, c - pick H C ∉ D B :=
  (exists_good H C).choose_spec h

/-- One greedy step: keep `A` if `n ∈ A + B` already (Case 1); otherwise adjoin
`a_j = n − b_j` for the good `b_j` given by `H` on `C_j = (A).image (n − ·)`
(Case 2). -/
noncomputable def step (A : Finset ℤ) (n : ℤ) : Finset ℤ :=
  if ∃ a ∈ A, ∃ b ∈ B, a + b = n then A
  else insert (n - pick H (A.image fun a => n - a)) A

theorem subset_step (A : Finset ℤ) (n : ℤ) : A ⊆ step H A n := by
  unfold step
  split_ifs
  · exact Finset.Subset.refl A
  · exact Finset.subset_insert _ A

/-- After the step, `n` is covered by `(step A n) + B`. -/
theorem step_covers (A : Finset ℤ) (n : ℤ) :
    ∃ a ∈ step H A n, ∃ b ∈ B, a + b = n := by
  unfold step
  split_ifs with hcase
  · exact hcase
  · exact ⟨n - pick H (A.image fun a => n - a), Finset.mem_insert_self _ _,
      pick H (A.image fun a => n - a),
      (pick_spec H (image_subset_compl hcase)).1, by ring⟩

/-- The step preserves `D`-separatedness — SKETCH §7, Case 2, invariant (I1):
`a_j − a = (n_j − a) − b_j ∉ D` from the choice of `b_j`, and `a − a_j ∉ D` by
symmetry of the difference set. -/
theorem step_separated {A : Finset ℤ} (hA : Separated B A) (n : ℤ) :
    Separated B (step H A n) := by
  unfold step
  split_ifs with hcase
  · exact hA
  · have hav := (pick_spec H (image_subset_compl hcase)).2
    set b := pick H (A.image fun a => n - a) with hb
    have key : ∀ a ∈ A, n - b - a ∉ D B := by
      intro a ha hmem
      have heq : n - b - a = n - a - b := by ring
      rw [heq] at hmem
      exact hav (n - a) (Finset.mem_image_of_mem _ ha) hmem
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hxA
    · rcases Finset.mem_insert.mp hy with rfl | hyA
      · exact absurd rfl hxy
      · exact key y hyA
    · rcases Finset.mem_insert.mp hy with rfl | hyA
      · intro hmem
        have hneg := D_neg_mem hmem
        rw [neg_sub] at hneg
        exact key x hxA hneg
      · exact hA x hxA y hyA hxy

/-- SKETCH §9.5 item 9: in Case 2 the adjoined element `a_j = n − b_j` is
genuinely new — `a_j ∈ A` would force `0 = (n − a_j) − b_j ∉ D` by the choice
of `b_j`, contradicting `0 ∈ B − B` (from `B ≠ ∅`). -/
theorem step_new_notMem {A : Finset ℤ} {n : ℤ}
    (hcase : ¬ ∃ a ∈ A, ∃ b ∈ B, a + b = n) :
    n - pick H (A.image fun a => n - a) ∉ A := by
  intro hmem
  have hav := (pick_spec H (image_subset_compl hcase)).2
  set b := pick H (A.image fun a => n - a) with hb
  have h0 := hav (n - (n - b)) (Finset.mem_image_of_mem _ hmem)
  have heq : n - (n - b) - b = 0 := by ring
  rw [heq] at h0
  exact h0 (zero_mem_D H)

/-- The greedy sequence of finite approximants `A₀ ⊆ A₁ ⊆ A₂ ⊆ ⋯`; stage
`j + 1` handles the `j`-th enumerated integer `n_j = enum j`. -/
noncomputable def Aseq : ℕ → Finset ℤ
  | 0 => ∅
  | j + 1 => step H (Aseq j) (enum j)

theorem Aseq_zero : Aseq H 0 = ∅ := rfl

theorem Aseq_succ (j : ℕ) : Aseq H (j + 1) = step H (Aseq H j) (enum j) := rfl

theorem Aseq_subset_succ (j : ℕ) : Aseq H j ⊆ Aseq H (j + 1) := by
  rw [Aseq_succ]
  exact subset_step H _ _

/-- Monotonicity of the greedy sequence (the family is a chain). -/
theorem Aseq_subset_of_le {i j : ℕ} (hij : i ≤ j) : Aseq H i ⊆ Aseq H j := by
  induction hij with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact Finset.Subset.trans ih (Aseq_subset_succ H _)

/-- Invariant `(I1)` at every stage. -/
theorem Aseq_separated (j : ℕ) : Separated B (Aseq H j) := by
  induction j with
  | zero =>
    rw [Aseq_zero]
    intro a ha
    exact absurd ha (Finset.notMem_empty a)
  | succ j ih =>
    rw [Aseq_succ]
    exact step_separated H ih _

/-- Invariant `(I2)`: after stage `i + 1`, the `i`-th enumerated integer is
covered. -/
theorem Aseq_covers (i : ℕ) :
    ∃ a ∈ Aseq H (i + 1), ∃ b ∈ B, a + b = enum i := by
  rw [Aseq_succ]
  exact step_covers H _ _

end

end Greedy

/-- **L4.1 / paper's Lemma 5.1 — the greedy tiling criterion** (statement
character-exact to the frozen `Erdos477.greedy_tiling`): an abstract `B ⊆ ℤ`
satisfying the finite-avoidance hypothesis `H` has a tiling complement
`A = ⋃ j, Aseq j`, with the FULL `∃!` (existence and uniqueness of the pair). -/
theorem greedy_tiling_proof (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
         ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n := by
  refine ⟨⋃ j, (Greedy.Aseq H j : Set ℤ), fun n => ?_⟩
  -- Existence: `n = enum j` is covered at stage `j + 1` by (I2).
  obtain ⟨j, hj⟩ := Greedy.enum_surjective n
  obtain ⟨a, haj, b, hbB, hab⟩ := Greedy.Aseq_covers H j
  rw [hj] at hab
  refine ⟨(a, b), ⟨Set.mem_iUnion.mpr ⟨j + 1, Finset.mem_coe.mpr haj⟩, hbB, hab⟩, ?_⟩
  -- Uniqueness: both first coordinates live in a common stage of the chain;
  -- `D`-separatedness (I1) forces them equal, then cancel to equate the second.
  rintro ⟨a', b'⟩ ⟨ha', hb', hab'⟩
  have ha'm : a' ∈ ⋃ i, (Greedy.Aseq H i : Set ℤ) := ha'
  have hb'B : b' ∈ B := hb'
  have hab'' : a' + b' = n := hab'
  obtain ⟨j', ha'j⟩ := Set.mem_iUnion.mp ha'm
  have haU : a ∈ Greedy.Aseq H (max (j + 1) j') :=
    Greedy.Aseq_subset_of_le H (le_max_left _ _) haj
  have ha'U : a' ∈ Greedy.Aseq H (max (j + 1) j') :=
    Greedy.Aseq_subset_of_le H (le_max_right _ _) (Finset.mem_coe.mp ha'j)
  have haa' : a' = a := by
    by_contra hne
    have hD : a' - a ∈ Greedy.D B := ⟨b, hbB, b', hb'B, by omega⟩
    exact Greedy.Aseq_separated H (max (j + 1) j') a' ha'U a haU hne hD
  have hbb' : b' = b := by omega
  rw [haa', hbb']

/-- Guardrail (Cheat watch, Stage Greedy): instantiating `B = Set.univ`, the
criterion's hypothesis holds and yields the (degenerate) tiling. -/
example : ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ,
    ab.1 ∈ A ∧ ab.2 ∈ (Set.univ : Set ℤ) ∧ ab.1 + ab.2 = n :=
  greedy_tiling_proof Set.univ
    (fun _ hC => ⟨0, Set.mem_univ 0,
      fun c hc => absurd (Set.mem_univ c) (hC c hc)⟩)

end Erdos477
