/-
  Stage D — Greedy tiling criterion L4.1 (proves `greedy_tiling`). INDEPENDENT.

  `B : Set ℤ` is kept ABSTRACT throughout (never specialised to `Bset`), and the
  difference set is the ABSTRACT `Dabs B = {d | ∃ x ∈ B, ∃ y ∈ B, d = x - y}`
  occurring in the frozen statement (its symmetry is proved locally here, not
  imported from Stage A's concrete `dset_neg`).

  Contents (BLUEPRINT Stage D / SKETCH §7):
    * D1  `Aseq` — the greedy chain of finite sets, built by `Nat.rec` over an
      enumeration of `ℤ` (`Denumerable ℤ`), one step per integer.
    * D2  the invariants (I1) `Sep` (separation w.r.t. `Dabs B`) and (I2)
      coverage of the first `j` enumerated integers.
    * D3  the monotone chain `i ≤ j → Aseq i ⊆ Aseq j`.
    * D4  `greedy_tiling_proof` — existence AND uniqueness of the `(a,b)`
      decomposition for `A := ⋃ j, ↑(Aseq j)`.
-/
import Erdos477.Defs

namespace Erdos477

namespace Greedy

/-- The abstract difference set `B − B` appearing in the frozen statement of
`greedy_tiling`. -/
def Dabs (B : Set ℤ) : Set ℤ := {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}

variable {B : Set ℤ}

/-- **L0.2, abstract form.** `B − B` is symmetric — proved by swapping the two
witnesses (no sign manipulation on powers). -/
theorem neg_mem_Dabs {d : ℤ} (h : d ∈ Dabs B) : -d ∈ Dabs B := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h
  exact ⟨y, hy, x, hx, by ring⟩

/-- **L0.1, abstract form.** `0 ∈ B − B` as soon as `B` is nonempty. -/
theorem zero_mem_Dabs {b : ℤ} (hb : b ∈ B) : (0 : ℤ) ∈ Dabs B :=
  ⟨b, hb, b, hb, by ring⟩

/-- The greedy hypothesis `(H)` of `greedy_tiling`, phrased with `Dabs`
(definitionally the set-builder used in the frozen statement). -/
def Hyp (B : Set ℤ) : Prop :=
  ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) → ∃ b ∈ B, ∀ c ∈ C, c - b ∉ Dabs B

/-- Invariant **(I1)**: distinct elements of `S` differ by an element outside
`B − B`; equivalently the translates `a + B`, `a ∈ S`, are pairwise disjoint. -/
def Sep (B : Set ℤ) (S : Finset ℤ) : Prop :=
  ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a - a' ∉ Dabs B

theorem sep_empty : Sep B ∅ := by
  intro a ha
  exact absurd ha (Finset.notMem_empty a)

/-- `B` is nonempty: apply `(H)` to the empty `C`. -/
theorem nonempty_of_Hyp (H : Hyp B) : ∃ b, b ∈ B := by
  obtain ⟨b, hb, -⟩ := H ∅ (by simp)
  exact ⟨b, hb⟩

/-- **D1, one greedy step.** Any finite `S` extends to a finite `S'` that covers
`n` (i.e. `n ∈ S' + B`) and stays separated whenever `S` was. -/
theorem extend_exists (H : Hyp B) (S : Finset ℤ) (n : ℤ) :
    ∃ S' : Finset ℤ, S ⊆ S' ∧ (∃ a ∈ S', ∃ b ∈ B, a + b = n) ∧ (Sep B S → Sep B S') := by
  by_cases hcov : ∃ a ∈ S, ∃ b ∈ B, a + b = n
  · exact ⟨S, Finset.Subset.refl S, hcov, fun h => h⟩
  · push Not at hcov
    -- Case 2 of the sketch: `C = {n - a : a ∈ S}` misses `B` entirely.
    have hCB : ∀ c ∈ S.image (fun a => n - a), c ∉ B := by
      intro c hc hcB
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      exact hcov a ha (n - a) hcB (by ring)
    obtain ⟨b, hb, hbP⟩ := H (S.image (fun a => n - a)) hCB
    refine ⟨insert (n - b) S, Finset.subset_insert _ _,
      ⟨n - b, Finset.mem_insert_self _ _, b, hb, by ring⟩, ?_⟩
    intro hS a ha a' ha' hne
    -- separation of the new point `n - b` from every old point
    have key : ∀ x ∈ S, (n - b) - x ∉ Dabs B := by
      intro x hx
      have hmem : n - x ∈ S.image (fun a => n - a) :=
        Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have := hbP (n - x) hmem
      intro hcon
      exact this (by rw [show n - x - b = n - b - x by ring]; exact hcon)
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp ha' with rfl | ha'
      · exact absurd rfl hne
      · exact key a' ha'
    · rcases Finset.mem_insert.mp ha' with rfl | ha'
      · intro hcon
        refine key a ha ?_
        have := neg_mem_Dabs hcon
        rwa [show -(a - (n - b)) = n - b - a by ring] at this
      · exact hS a ha a' ha' hne

/-- The chosen greedy extension. -/
noncomputable def stepF (H : Hyp B) (S : Finset ℤ) (n : ℤ) : Finset ℤ :=
  (extend_exists H S n).choose

theorem subset_stepF (H : Hyp B) (S : Finset ℤ) (n : ℤ) : S ⊆ stepF H S n :=
  (extend_exists H S n).choose_spec.1

theorem cover_stepF (H : Hyp B) (S : Finset ℤ) (n : ℤ) :
    ∃ a ∈ stepF H S n, ∃ b ∈ B, a + b = n :=
  (extend_exists H S n).choose_spec.2.1

theorem sep_stepF (H : Hyp B) {S : Finset ℤ} (n : ℤ) (hS : Sep B S) :
    Sep B (stepF H S n) :=
  (extend_exists H S n).choose_spec.2.2 hS

/-- An enumeration of `ℤ` (`Denumerable ℤ`); surjective by construction. -/
def enum (j : ℕ) : ℤ := (Denumerable.eqv ℤ).symm j

theorem enum_surjective : Function.Surjective enum :=
  (Denumerable.eqv ℤ).symm.surjective

/-- **D1 — the greedy chain.** `Aseq 0 = ∅`; step `j` handles the integer
`enum j`. -/
noncomputable def Aseq (H : Hyp B) : ℕ → Finset ℤ
  | 0 => ∅
  | j + 1 => stepF H (Aseq H j) (enum j)

/-- **D2 (I1).** Every `Aseq j` is separated. -/
theorem Aseq_sep (H : Hyp B) : ∀ j, Sep B (Aseq H j)
  | 0 => sep_empty
  | j + 1 => sep_stepF H _ (Aseq_sep H j)

/-- **D3 — the chain is monotone.** -/
theorem Aseq_mono (H : Hyp B) {i j : ℕ} (hij : i ≤ j) : Aseq H i ⊆ Aseq H j := by
  induction j with
  | zero => simp_all
  | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with h | h
      · exact fun x hx => subset_stepF H _ _ (ih (Nat.lt_succ_iff.mp h) hx)
      · subst h; exact Finset.Subset.refl _

/-- **D2 (I2).** `Aseq j` covers the first `j` enumerated integers. -/
theorem Aseq_cover (H : Hyp B) : ∀ j : ℕ, ∀ i < j, ∃ a ∈ Aseq H j, ∃ b ∈ B, a + b = enum i := by
  intro j
  induction j with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ j ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · obtain ⟨a, ha, b, hb, hab⟩ := ih i h
        exact ⟨a, subset_stepF H _ _ ha, b, hb, hab⟩
      · subst h; exact cover_stepF H _ _

/-- **D4 — the tiling complement.** -/
def Aset (H : Hyp B) : Set ℤ := ⋃ j : ℕ, ((Aseq H j : Finset ℤ) : Set ℤ)

theorem mem_Aset {H : Hyp B} {a : ℤ} : a ∈ Aset H ↔ ∃ j, a ∈ Aseq H j := by
  simp [Aset]

end Greedy

open Greedy in
/-- **L4.1 (SKETCH §7, paper's Lemma 5.1) — the greedy tiling criterion.**
If every finite `C ⊆ ℤ∖B` admits `b ∈ B` with `(C − b) ∩ (B − B) = ∅`, then `B`
has a tiling complement `A`: every integer is *uniquely* `a + b` with `a ∈ A`,
`b ∈ B`. -/
theorem greedy_tiling_proof (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
         ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n := by
  have H' : Hyp B := H
  refine ⟨Aset H', fun n => ?_⟩
  -- existence: `n` is enumerated, hence covered at the next step
  obtain ⟨i, hi⟩ := enum_surjective n
  obtain ⟨a, ha, b, hb, hab⟩ := Aseq_cover H' (i + 1) i (Nat.lt_succ_self i)
  refine ⟨(a, b), ⟨mem_Aset.mpr ⟨i + 1, ha⟩, hb, by rw [hab, hi]⟩, ?_⟩
  -- uniqueness: two decompositions with distinct `a`'s would put `a - a'` in `B − B`
  rintro ⟨a', b'⟩ ⟨ha', hb', hab'⟩
  simp only at ha' hb' hab' ⊢
  obtain ⟨j', hj'⟩ := mem_Aset.mp ha'
  have hmemA : a ∈ Aseq H' (max (i + 1) j') := Aseq_mono H' (le_max_left _ _) ha
  have hmemA' : a' ∈ Aseq H' (max (i + 1) j') := Aseq_mono H' (le_max_right _ _) hj'
  have haa : a' = a := by
    by_contra hne
    refine Aseq_sep H' _ a' hmemA' a hmemA hne ?_
    refine ⟨b, hb, b', hb', ?_⟩
    have : a + b = a' + b' := by rw [hab, hi, hab']
    linarith
  subst haa
  have : b' = b := by
    have : a' + b = a' + b' := by rw [hab, hi, hab']
    linarith
  simp [this]

end Erdos477
