/-
  Stage ParamExclusion — degenerate/vanishing-subsum half of Route A
  (paper's Lemma 3.1, Cases C and D, specialized to polynomial
  parametrizations; SKETCH §5.2.2 and the derivation in §5.2.3).

  These are the branches of the paper's own argument that need NO
  Brownawell–Masser: elementary ℤ[T] consequences of the odd exponent 13.

  Proves (TASKS.md Iteration 2, Agent 3):
    * `polyInt_pow13_injective`   — `p¹³ = q¹³ → p = q` in `ℤ[T]`, by pointwise
                                    evaluation + `Polynomial.funext` (ℤ infinite).
    * `polyInt_pow13_eq_neg`      — `p¹³ = −q¹³ → p = −q` (13 odd).
    * `polyInt_pow13_eq_C`        — `p¹³ = C m → p = C b` with `b¹³ = m`
                                    (degree count).
    * `mem_Bset_of_pairing`       — Case-D payoff: `p¹³ = C (−c) → c ∈ Bset`
                                    (witness `−b`).
    * `vanishing_subsum_pairing`  — the generic Fin-4 classification: a proper
                                    nonempty vanishing subsum of a zero-sum of
                                    four nonzero terms forces a 2+2 splitting.
    * `polyMap_int_injective`     — `Polynomial.map (algebraMap ℤ K)` injective
                                    for `K` of characteristic zero.
    * `pow13_pair_descent`        — a vanishing 13th-power pair over `K`
                                    descends to `p¹³ = −q¹³` in `ℤ[T]`.

  Deliberately does NOT import `Erdos477.Proofs.ParamExclusion.Basic` (built
  concurrently) and does NOT state `no_linear_param` — per the BLUEPRINT
  "Cheat watch (Stage ParamExclusion)" box these are support lemmas only, and
  the Route-B Vandermonde argument is banned from the dependency path.
-/
import Erdos477.Defs
import Erdos477.Proofs.Elementary.Basic

namespace Erdos477

open Polynomial

/-! ### ℤ[T] consequences of the odd exponent (Cases C/D raw material) -/

/-- **Thirteenth powers are injective on `ℤ[T]`.** Evaluate at every integer,
apply the pointwise odd-power injectivity L0.3, and conclude by
`Polynomial.funext` (ℤ is infinite). -/
theorem polyInt_pow13_injective (p q : Polynomial ℤ) (h : p ^ 13 = q ^ 13) :
    p = q := by
  apply Polynomial.funext
  intro n
  have hn : (p.eval n) ^ 13 = (q.eval n) ^ 13 := by
    simpa [Polynomial.eval_pow] using congrArg (Polynomial.eval n) h
  exact pow13_injective_proof hn

/-- **Odd-power sign variant on `ℤ[T]`:** `p¹³ = −(q¹³) → p = −q` (rewrite
`−(q¹³) = (−q)¹³`, 13 odd, then injectivity). -/
theorem polyInt_pow13_eq_neg (p q : Polynomial ℤ) (h : p ^ 13 = -(q ^ 13)) :
    p = -q := by
  apply polyInt_pow13_injective
  rw [Odd.neg_pow (by decide : Odd 13)]
  exact h

/-- **Constant-forcing (degree count):** `p¹³ = C m` forces `p` constant, with
constant a 13th root of `m`. From `13 * p.natDegree = 0` conclude
`p.natDegree = 0`, then extract the constant. -/
theorem polyInt_pow13_eq_C (p : Polynomial ℤ) (m : ℤ) (h : p ^ 13 = Polynomial.C m) :
    ∃ b : ℤ, p = Polynomial.C b ∧ b ^ 13 = m := by
  have hdeg : 13 * p.natDegree = 0 := by
    have := congrArg Polynomial.natDegree h
    simpa [Polynomial.natDegree_pow, Polynomial.natDegree_C] using this
  have hp0 : p.natDegree = 0 := by omega
  obtain ⟨b, hb⟩ := Polynomial.natDegree_eq_zero.mp hp0
  refine ⟨b, hb.symm, ?_⟩
  have : Polynomial.C (b ^ 13) = Polynomial.C m := by
    rw [map_pow, hb]; exact h
  exact Polynomial.C_injective this

/-- **Case-D payoff:** if some `p ∈ ℤ[T]` satisfies `p¹³ = C (−c)` (the shape
forced on the pair containing the constant term in the 2+2 pairings of
SKETCH §5.2.2 Case D), then `c` is itself a thirteenth power: `b¹³ = −c`
gives `c = (−b)¹³`. -/
theorem mem_Bset_of_pairing (c : ℤ) (p : Polynomial ℤ)
    (h : p ^ 13 = Polynomial.C (-c)) : c ∈ Bset := by
  obtain ⟨b, -, hb13⟩ := polyInt_pow13_eq_C p (-c) h
  exact ⟨-b, by rw [Odd.neg_pow (by decide : Odd 13), hb13, neg_neg]⟩

/-! ### The generic vanishing-subsum classification (Case D opening) -/

/-- **2+2 splitting.** In any additive commutative group, if four nonzero terms
sum to zero and some proper nonempty subsum vanishes, then the four terms split
into two vanishing pairs: a vanishing subsum of length 1 contradicts
nonzeroness, and length 3 forces the complementary singleton to vanish, so only
the 2+2 pairings survive (SKETCH §5.2.2 Case D opening). -/
theorem vanishing_subsum_pairing {M : Type*} [AddCommGroup M] (x : Fin 4 → M)
    (hsum : ∑ i, x i = 0) (hnz : ∀ i, x i ≠ 0)
    (I : Finset (Fin 4)) (hne : I.Nonempty) (hproper : I ≠ Finset.univ)
    (hI : ∑ i ∈ I, x i = 0) :
    ∃ I' : Finset (Fin 4), I'.card = 2 ∧ I'.Nonempty ∧
      ∑ i ∈ I', x i = 0 ∧ ∑ i ∈ I'ᶜ, x i = 0 := by
  -- The complement of any vanishing subsum also vanishes.
  have hcompl : ∀ J : Finset (Fin 4), ∑ i ∈ J, x i = 0 → ∑ i ∈ Jᶜ, x i = 0 := by
    intro J hJ
    have h := Finset.sum_add_sum_compl J x
    rw [hJ, zero_add, hsum] at h
    exact h
  have hlt : I.card < 4 := by
    have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
    simpa using this
  have hpos : 0 < I.card := hne.card_pos
  -- A vanishing singleton subsum is impossible.
  have hsingleton : ∀ J : Finset (Fin 4), J.card = 1 → ∑ i ∈ J, x i ≠ 0 := by
    intro J hJ1 hJ0
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hJ1
    exact hnz a (by simpa using hJ0)
  interval_cases h : I.card
  · -- |I| = 1: contradicts nonzeroness.
    exact absurd hI (hsingleton I h)
  · -- |I| = 2: I itself is the vanishing pair.
    exact ⟨I, h, hne, hI, hcompl I hI⟩
  · -- |I| = 3: the complementary singleton vanishes — contradiction.
    have hc1 : Iᶜ.card = 1 := by
      have := Finset.card_compl I
      simp only [Fintype.card_fin, h] at this
      omega
    exact absurd (hcompl I hI) (hsingleton Iᶜ hc1)

/-! ### Base-change descent helpers (K-identities back to ℤ[T]) -/

/-- **`Polynomial.map (algebraMap ℤ K)` is injective** for any field `K` of
characteristic zero (in fact any `CharZero` ring): `Int.cast` is injective. -/
theorem polyMap_int_injective (K : Type*) [Field K] [CharZero K] :
    Function.Injective (Polynomial.map (algebraMap ℤ K)) :=
  Polynomial.map_injective _ fun _ _ h => by
    exact_mod_cast h

/-- **Descent of a vanishing 13th-power pair.** If the images of `p, q ∈ ℤ[T]`
in `K[T]` satisfy `(p.map φ)¹³ + (q.map φ)¹³ = 0`, the identity descends to
`p¹³ = −(q¹³)` in `ℤ[T]` (push `map` through `^`, `+`, `neg`; injectivity). -/
theorem pow13_pair_descent {K : Type*} [Field K] [CharZero K]
    (p q : Polynomial ℤ)
    (h : (p.map (algebraMap ℤ K)) ^ 13 + (q.map (algebraMap ℤ K)) ^ 13 = 0) :
    p ^ 13 = -(q ^ 13) := by
  have hmap : (p ^ 13 + q ^ 13).map (algebraMap ℤ K) =
      (0 : Polynomial ℤ).map (algebraMap ℤ K) := by
    simpa [Polynomial.map_add, Polynomial.map_pow] using h
  have hz : p ^ 13 + q ^ 13 = 0 := polyMap_int_injective K hmap
  linear_combination hz

/-! ### Guardrail examples -/

-- The 2+2 classification really excludes singleton/triple subsums: from a
-- concrete vanishing pair inside a four-term zero sum, we recover a pair.
example : ∃ I' : Finset (Fin 4), I'.card = 2 ∧ I'.Nonempty ∧
    ∑ i ∈ I', (![1, -1, 2, -2] : Fin 4 → ℤ) i = 0 ∧
    ∑ i ∈ I'ᶜ, (![1, -1, 2, -2] : Fin 4 → ℤ) i = 0 :=
  vanishing_subsum_pairing _ (by decide) (by decide)
    {0, 1} (by decide) (by decide) (by decide)

-- Case-D payoff at a concrete constant: `p = C 2`, `p¹³ = C 8192 = C (−(−8192))`
-- certifies `−8192 ∈ Bset`.
example : (-8192 : ℤ) ∈ Bset :=
  mem_Bset_of_pairing (-8192) (Polynomial.C 2) (by
    rw [← map_pow]; norm_num)

end Erdos477
