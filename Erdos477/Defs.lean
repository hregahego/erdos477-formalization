/-
  Erdős 477 — "The thirteenth powers have a tiling complement in ℤ".

  FROZEN definitions and assumed-certificate axioms.

  This file is BYTE-FROZEN after SETUP (pinned in `scripts/frozen.sha256`).
  Later stages may *characterize* these objects with support lemmas in
  `Erdos477/Proofs/**`, but may never redefine, rename, or alter a single
  character here. See `BLUEPRINT.md` Part −1 §2 for the modeling decisions.

  Modeling decisions (binding; do not re-derive):
    * `Bset`  — thirteenth powers as a `Set ℤ` carved by an existential, image
      form `b = m ^ 13`. Infinite; no positivity, no `b ≠ 0`. Exponent `13 : ℕ`.
    * `Dset`  — the difference set encoded DIRECTLY as `u ^ 13 - v ^ 13`, NOT as
      the Minkowski difference `Bset - Bset`. Symmetry is a lemma (Stage A), not
      baked in. Bridge lemma `dset_eq_sub` lives in Stage A.
    * `Qcof`  — the full 13-term homogeneous cofactor `∑_{i<13} u^i v^(12-i)`,
      integer-valued, cast to ℝ where the explicit `κ = 1/2` bound is used.
    * `Sset`  — bad-shift set as a `Finset` (`.card` available), realised as a
      `filter` over the TWO-SIDED interval `Finset.Icc (-T) T` (the `2T+1` count
      is load-bearing). Predicate `t ^ 13 - c ∈ Dset` is classical/noncomputable.

  Assumed-certificate axioms (permitted by `USER_NOTES.md`; recorded in
  `scripts/ALLOWED_AXIOMS.txt`):
    * `heath_brown_diagonal_13`          — Heath-Brown's determinant-method count
      for the diagonal ternary form of degree 13, in the conditional form of
      `SKETCH.md` §3 (paper's Theorem 2.2).
    * `brownawell_masser_P1_four_term`   — the four-term Brownawell–Masser S-unit
      inequality on ℙ¹, in the concrete bivariate-forms formulation "BM4" of
      `SKETCH.md` §5.2.1 (paper's Theorem 2.1). Permitted so the paper-faithful
      Route A is available; the recommended Route B leaves it unused.
-/
import Mathlib

namespace Erdos477

open scoped BigOperators Classical

/-- **D1 — `Bset`.** The set of thirteenth powers `{ m ^ 13 : m ∈ ℤ }` — the set
being tiled. Carved by an existential in image form `b = m ^ 13`; infinite. -/
def Bset : Set ℤ := {b | ∃ m : ℤ, b = m ^ 13}

/-- **D2 — `Dset`.** The difference set `B − B`, encoded directly as differences
of two thirteenth powers `u ^ 13 − v ^ 13` (NOT the Minkowski difference). -/
def Dset : Set ℤ := {d | ∃ u v : ℤ, d = u ^ 13 - v ^ 13}

/-- **D3 — `Qcof`.** The degree-12 homogeneous cofactor `Q(u,v)` appearing in the
factorization `u ^ 13 − v ^ 13 = (u − v) · Q(u,v)`, as the 13-term sum
`∑_{i=0}^{12} u ^ i · v ^ (12 − i)` over `ℤ` (`12 − i : ℕ`, safe since `i ≤ 12`). -/
def Qcof (u v : ℤ) : ℤ := ∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i)

/-- **D4 — `Sset`.** The bad-shift set `S_c(T) = { t : |t| ≤ T ∧ t ^ 13 − c ∈ D }`,
as a `Finset` obtained by filtering the two-sided interval `Finset.Icc (-T) T`.
The membership predicate is not decidable constructively — classical, hence
`noncomputable`. -/
noncomputable def Sset (c T : ℤ) : Finset ℤ :=
  (Finset.Icc (-T) T).filter (fun t => t ^ 13 - c ∈ Dset)

/-- **A1 — Axiom `heath_brown_diagonal_13`** (paper's Theorem 2.2, Heath-Brown,
*Sums and differences of three k-th powers*, J. Number Theory 129 (2009), Thm 2).

Specialized, CONDITIONAL form for the diagonal ternary form of degree 13 (see
`SKETCH.md` §3): for every nonzero `M`, IF every affine-linear triple
`(p₁,p₂,p₃)` with `p₁^13 + p₂^13 + p₃^13 = C M` is a triple of constants (the
*exclusion hypothesis* `hexcl`), THEN the number of integer solutions of
`x^13 + y^13 + z^13 = M` in the box `max(|x|,|y|,|z|) ≤ X` is `≤ K · X^(10/13)`
for some real `K ≥ 1`.

The conditional shape avoids formalizing Heath-Brown's "lies on a polynomial
parametrization" predicate and the nonsingularity of the form; §3 points 1–4
justify this as a faithful (weakened) consequence of the published theorem. The
proof is the determinant method, far beyond current formalization technology —
hence assumed. Consumed only by `badShift_bound`. -/
axiom heath_brown_diagonal_13 (M : ℤ) (hM : M ≠ 0)
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
        p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C M →
        p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
        p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      (({v : ℤ × ℤ × ℤ | v.1 ^ 13 + v.2.1 ^ 13 + v.2.2 ^ 13 = M ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ X ∧ |(v.2.2 : ℝ)| ≤ X}).ncard : ℝ)
        ≤ K * X ^ ((10 : ℝ) / 13)

/-- **A2 — Axiom `brownawell_masser_P1_four_term`** (paper's Theorem 2.1,
Brownawell–Masser, *Vanishing sums in function fields*, Math. Proc. Camb. Phil.
Soc. 100 (1986); genus-zero case, constants as in Corvaja–Zannier 2011).

The four-term S-unit inequality on `ℙ¹`, in the concrete bivariate-forms
formulation "BM4" of `SKETCH.md` §5.2.1: over an algebraically closed field `k`
of characteristic zero, if `A₀,A₁,A₂,A₃ : k[S,T]` are nonzero homogeneous forms
of a common degree `d`, coprime (their only common divisors are units), summing
to `0`, with no proper nonempty sub-sum vanishing and not all pairwise ratios
`Aᵢ/Aⱼ` constant, then `d ≤ 3 · (z − 2)`, where `z` is the number of distinct
projective zeros of the product `A₀·A₁·A₂·A₃` (equivalently, distinct linear
factors over `k` up to scalar) — realised here as the `ncard` of the set of
points of `ℙ¹_k` at which the product vanishes.

Mathlib contains only the three-term case (Mason–Stothers, `Polynomial.abc`);
the four-term case uses generalized Wronskians over function fields and is not
formalized — hence assumed. Used only in the paper-faithful Route A of Stage C;
Route B (the recommended path) does not consume it. -/
axiom brownawell_masser_P1_four_term
    {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    (A : Fin 4 → MvPolynomial (Fin 2) k) (d : ℕ)
    (hne : ∀ i, A i ≠ 0)
    (hhom : ∀ i, (A i).IsHomogeneous d)
    (hcoprime : ∀ p : MvPolynomial (Fin 2) k, (∀ i, p ∣ A i) → IsUnit p)
    (hsum : ∑ i, A i = 0)
    (hsub : ∀ I : Finset (Fin 4), I.Nonempty → I ≠ Finset.univ → ∑ i ∈ I, A i ≠ 0)
    (hratio : ¬ ∀ i j : Fin 4, ∃ c : k, A i = MvPolynomial.C c * A j) :
    (d : ℤ) ≤ 3 * (({P : Projectivization k (Fin 2 → k) |
        MvPolynomial.eval P.rep (∏ i, A i) = 0}.ncard : ℤ) - 2)

end Erdos477
