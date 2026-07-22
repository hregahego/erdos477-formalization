/-
  Erdős 477 — "The thirteenth powers have a tiling complement in ℤ".

  FROZEN assumed-certificate axioms, and the support definitions their
  statements quote.

  This file is BYTE-FROZEN after SETUP (pinned in `scripts/frozen.sha256`).
  Later stages may *characterize* these objects with support lemmas in
  `Erdos477/Proofs/**`, but may never redefine, rename, or alter a single
  character here. See `BLUEPRINT.md` Part −1 §2 and `USER_NOTES.md` for the
  binding modeling decisions.

  SCOPE. This file carries ONLY what the frozen material needs:
    * the two assumed-certificate axioms (below), and
    * the definitions their statements quote — `IsNonsingularForm`,
      `IsParamOfDegLE`, `LiesOnParamOfDegLE`, `HBSolutionSet` for Axiom 1;
      `ordAtP1`, `IsSUnitP1`, `projHeightP1` for Axiom 2.
  The frozen headline `erdos_477` of `Erdos477/Theorems.lean` is stated in raw
  ℤ-language (`∃ A : Set ℤ, ∀ n, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n`)
  and quotes NO definition at all — so nothing here exists on its account.

  Every other object of the development is a working definition of the proof
  layer and lives with the proofs that use it (its binding modeling decision
  travels with it, verbatim, in that file's header):
    * `Bset`, `Dset` — `Erdos477/Proofs/Elementary/Basic.lean`
    * `Qcof`         — `Erdos477/Proofs/Cofactor/Basic.lean`
    * `Sset`         — `Erdos477/Proofs/BadShift/Basic.lean`

  Assumed-certificate axioms (permitted by `USER_NOTES.md`; recorded in
  `scripts/ALLOWED_AXIOMS.txt`). Per `USER_NOTES.md`, BOTH are stated in the
  FULL GENERALITY of the paper's Section 2 ("Preliminary") — the general
  statement is axiomatized, every specialization the development consumes is a
  proof obligation in `Proofs/**`, never an assumption:
    * `heath_brown_diagonal_13`        — the paper's Theorem 2.2 (Heath-Brown
      2009, Thm 2): the determinant-method count for a GENERAL nonsingular
      ternary form of degree `k ≥ 3`, excluding solutions on nonconstant
      polynomial parametrizations of degree ≤ ⌊k/10⌋. (The name retains the
      historical `diagonal_13` tag fixed by `USER_NOTES.md`; the statement is
      NOT specialized to `k = 13` or to the diagonal form.)
    * `brownawell_masser_P1_four_term` — the paper's Theorem 2.1 (Brownawell–
      Masser 1986, genus-zero case; constants as in Corvaja–Zannier 2011): the
      S-unit height inequality on `ℙ¹` for GENERAL `r ≥ 3`. (The name retains
      the historical `four_term` tag fixed by `USER_NOTES.md`; the statement is
      NOT restricted to `r = 4`.)
-/
import Mathlib

namespace Erdos477

open scoped BigOperators Classical

/-! ## Support definitions for Axiom 1 (paper's Theorem 2.2, Heath-Brown)

The paper's Theorem 2.2 speaks of a *nonsingular ternary form*, of *polynomial
parametrizations*, and of solutions *lying on* one. These notions are defined
here, in the standard textbook way, so the axiom below can quote the theorem
verbatim. A ternary form is a homogeneous `F ∈ ℤ[X₁,X₂,X₃]`, modeled as
`MvPolynomial (Fin 3) ℤ` with `F.IsHomogeneous k`; an integer triple is
`x : Fin 3 → ℤ`. -/

/-- A ternary integral form is **nonsingular** if, over the algebraic closure
(modeled as `ℂ`, which contains `ℚ̄`; in characteristic zero this is the
standard equivalent of smoothness of the projective curve `F = 0`), the three
partial derivatives have no common zero besides the origin. -/
def IsNonsingularForm (F : MvPolynomial (Fin 3) ℤ) : Prop :=
  ∀ x : Fin 3 → ℂ, (∀ i, MvPolynomial.aeval x (MvPolynomial.pderiv i F) = 0) → x = 0

/-- A **polynomial parametrization of degree ≤ d** of the affine surface
`F = N`: a triple `p = (p₁, p₂, p₃)` of integer polynomials in one variable
`T`, each of degree at most `d`, *not all constant* (`natDegree = 0` means
constant, covering the zero polynomial), with `F(p₁(T), p₂(T), p₃(T)) = N`
identically as polynomials in `T`. -/
def IsParamOfDegLE (F : MvPolynomial (Fin 3) ℤ) (N : ℤ) (d : ℕ)
    (p : Fin 3 → Polynomial ℤ) : Prop :=
  (∀ i, (p i).natDegree ≤ d) ∧ (¬ ∀ i, (p i).natDegree = 0) ∧
    MvPolynomial.aeval p F = Polynomial.C N

/-- An integer solution `x` of `F = N` **lies on** a nonconstant polynomial
parametrization of degree ≤ `d` if `x = (p₁(t), p₂(t), p₃(t))` for such a
parametrization `p` and some `t ∈ ℤ`. -/
def LiesOnParamOfDegLE (F : MvPolynomial (Fin 3) ℤ) (N : ℤ) (d : ℕ)
    (x : Fin 3 → ℤ) : Prop :=
  ∃ p : Fin 3 → Polynomial ℤ,
    IsParamOfDegLE F N d p ∧ ∃ t : ℤ, ∀ i, (p i).eval t = x i

/-- The set counted by the paper's Theorem 2.2: integer solutions of `F(x) = N`
in the box `max_i |x_i| ≤ X` which do NOT lie on a nonconstant polynomial
parametrization of degree at most `d`. -/
def HBSolutionSet (F : MvPolynomial (Fin 3) ℤ) (N : ℤ) (d : ℕ) (X : ℝ) :
    Set (Fin 3 → ℤ) :=
  {x | MvPolynomial.eval x F = N ∧ (∀ i, |(x i : ℝ)| ≤ X) ∧
    ¬ LiesOnParamOfDegLE F N d x}

/-- **Axiom 1 — `heath_brown_diagonal_13`** = the paper's **Theorem 2.2**,
EXACTLY (Heath-Brown, *Sums and differences of three k-th powers*, J. Number
Theory 129 (2009), Theorem 2; the paper's reference [5]).

> Let `F ∈ ℤ[X₁,X₂,X₃]` be a nonsingular ternary form of degree `k ≥ 3`. Let
> `X ≥ 1`, and let `N` be a fixed nonzero integer with `|N| ≪_F X`. The number
> of integer solutions of `F(x₁,x₂,x₃) = N`, `max_i |x_i| ≤ X`, which do not
> lie on a nonconstant polynomial parametrization of degree at most `⌊k/10⌋`,
> is `O_F(X^{10/k})`.

Rendering of the asymptotic conventions with explicit constants, per
`USER_NOTES.md`: `cN` is the implied constant assumed in `|N| ≪_F X` (the
hypothesis becomes `|N| ≤ cN · X`), and the implied constant `K` of the
conclusion `O_F(X^{10/k})` is quantified AFTER `F` and `cN` but BEFORE `N` and
`X` — it depends on `F` and on `cN`, and on nothing else. (`1 ≤ K` is the usual
harmless normalization of an O-constant; `⌊k/10⌋` is ℕ-division `k / 10`;
`X^{10/k}` is `Real.rpow`.)

Assumed because the determinant method is far beyond current formalization
technology. Every specialization consumed downstream (in particular the
diagonal-13 conditional form of `SKETCH.md` §3) is PROVED from this axiom in
`Proofs/**` — see `USER_NOTES.md`, "axiomatize the general, derive the
specific". -/
axiom heath_brown_diagonal_13
    (F : MvPolynomial (Fin 3) ℤ) (k : ℕ) (hk : 3 ≤ k)
    (hform : F.IsHomogeneous k) (hns : IsNonsingularForm F) (cN : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (N : ℤ) (X : ℝ), N ≠ 0 → 1 ≤ X → |(N : ℝ)| ≤ cN * X →
      ((HBSolutionSet F N (k / 10) X).ncard : ℝ) ≤ K * X ^ ((10 : ℝ) / (k : ℝ))

/-! ## Support definitions for Axiom 2 (paper's Theorem 2.1, Brownawell–Masser)

The paper's Theorem 2.1 speaks of `S`-units of `k(t)^×` for a finite set `S` of
points of `ℙ¹_k`, of the order `ord_P` at every point `P` of `ℙ¹_k` (finite
points AND the point at infinity), and of the projective height
`H(u₁ : ⋯ : u_r) = −∑_P min_i ord_P(uᵢ)`. Over an algebraically closed `k` the
points of `ℙ¹_k` are exactly `k ∪ {∞}`, modeled here as `Option k` (`some a` a
finite point, `none` the point at infinity); `k(t)` is `RatFunc k`. -/

/-- **`ordAtP1`** — the order of a rational function `f ∈ k(t)` at a point of
`ℙ¹_k = k ∪ {∞}`: at a finite point `a` it is the multiplicity of `a` as a zero
of the numerator minus its multiplicity as a zero of the denominator (positive
at a zero of `f`, negative at a pole, `0` otherwise — `num` and `denom` are
coprime, so at most one term is nonzero); at `∞` it is
`deg(denom) − deg(num) = −intDegree f`. Junk at `f = 0` (harmless: Theorem 2.1
concerns `k(t)^×`). -/
noncomputable def ordAtP1 {k : Type*} [Field k] (P : Option k) (f : RatFunc k) : ℤ :=
  match P with
  | some a => (f.num.rootMultiplicity a : ℤ) - (f.denom.rootMultiplicity a : ℤ)
  | none => -f.intDegree

/-- **`IsSUnitP1`** — `f ∈ k(t)^×` is an `S`-unit for a finite set `S` of points
of `ℙ¹_k`: `f` is nonzero and all its zeros and poles (on all of `ℙ¹_k`,
including `∞`) lie inside `S`, i.e. `ord_P f = 0` off `S`. -/
def IsSUnitP1 {k : Type*} [Field k] (S : Finset (Option k)) (f : RatFunc k) : Prop :=
  f ≠ 0 ∧ ∀ P : Option k, P ∉ S → ordAtP1 P f = 0

/-- **`projHeightP1`** — the projective height of a tuple `u₁, …, u_r ∈ k(t)`,
with the paper's convention `H(u₁ : ⋯ : u_r) = −∑_{P ∈ ℙ¹_k} min_i ord_P(uᵢ)`.
The sum over all points of `ℙ¹_k` is a `finsum` (for nonzero `uᵢ` all but
finitely many summands vanish, so it is the honest finite sum); the minimum
over `i` is the conditionally-complete `⨅` on `ℤ` (the genuine minimum for the
nonempty index families, `r ≥ 3`, used in Theorem 2.1). -/
noncomputable def projHeightP1 {k : Type*} [Field k] {r : ℕ}
    (u : Fin r → RatFunc k) : ℤ :=
  -(∑ᶠ P : Option k, ⨅ i, ordAtP1 P (u i))

/-- **Axiom 2 — `brownawell_masser_P1_four_term`** = the paper's **Theorem 2.1**,
EXACTLY (Brownawell–Masser, *Vanishing sums in function fields*, Math. Proc.
Camb. Phil. Soc. 100 (1986), genus-zero case — the paper's reference [2]; height
convention and the three- and four-term constants as recalled by Corvaja–Zannier
2011, the paper's reference [3]).

> Let `k` be an algebraically closed field of characteristic zero, and let `S`
> be a finite set of points of `ℙ¹_k`. Let `u₁, …, u_r ∈ k(t)^×` be `S`-units
> (all zeros and poles inside `S`), with `r ≥ 3`, not all constant, satisfying
> `u₁ + ⋯ + u_r = 0`, and suppose that no proper nonempty sub-sum vanishes.
> With the projective height convention
> `H(u₁ : ⋯ : u_r) = −∑_{P ∈ ℙ¹_k} min_{1≤i≤r} ord_P(uᵢ)`, one has
> `H(u₁ : ⋯ : u_r) ≤ binom(r−1, 2) · (|S| − 2)`.

(For `r = 3` this is the Mason–Stothers inequality, coefficient
`binom(2,2) = 1`; for `r = 4` the coefficient is `binom(3,2) = 3`. Despite the
name — fixed by `USER_NOTES.md` — the statement is the full `r ≥ 3` theorem;
`r` is NOT hard-coded to `4`. The bound is stated in `ℤ`, with `|S| − 2` the
honest integer subtraction.)

Assumed because the proof needs generalized Wronskians over function fields and
the `r ≥ 4` cases are not in Mathlib. Every working reformulation the proofs
prefer (e.g. the bivariate-forms version "BM4" of `SKETCH.md` §5.2.1) is a
proof obligation derived from this axiom in `Proofs/**`, never an assumption.
Both the four-term (`r = 4`) and three-term (`r = 3`) applications in the
paper's Lemma 3.1 must invoke THIS axiom (not Mathlib's Mason–Stothers) — see
`USER_NOTES.md`. -/
axiom brownawell_masser_P1_four_term
    {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    (S : Finset (Option k)) (r : ℕ) (hr : 3 ≤ r)
    (u : Fin r → RatFunc k)
    (hSunit : ∀ i, IsSUnitP1 S (u i))
    (hnotconst : ¬ ∀ i, ∃ a : k, u i = RatFunc.C a)
    (hsum : ∑ i, u i = 0)
    (hsubsum : ∀ I : Finset (Fin r), I.Nonempty → I ≠ Finset.univ →
      ∑ i ∈ I, u i ≠ 0) :
    projHeightP1 u ≤ ((r - 1).choose 2 : ℤ) * ((S.card : ℤ) - 2)

end Erdos477
