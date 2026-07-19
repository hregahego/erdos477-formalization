# USER_NOTES — special instructions for this formalization

This file is **created by `setup.py`** and read by **`init.py`** (when it freezes
`Defs.lean`/`Theorems.lean`) and by **`loop.py`** (when it proves and audits).
Put any problem-specific guidance here **before you run `init.py`**. Everything in
this file is free-form prose that the init, worker, and review agents read for
context — write to a human, not to a parser.

By default the pipeline is **maximally strict**:

- the ONLY axioms any solved theorem may depend on are the Lean/Mathlib standard
  `{propext, Classical.choice, Quot.sound}`;
- no custom `axiom` declarations are allowed anywhere;
- **no frozen theorem may carry an extra hypothesis** that `SKETCH.md` does not
  state (the cardinal anti-cheat rule — this is NEVER relaxed).

Use the section below to widen the **axiom** policy in a controlled way. Anything
you do not describe here stays banned.

## Allowed axioms (assumed certificates)

Some facts are mathematically routine but **prohibitively expensive to PROVE in
Lean** — a specific large factorization, an explicit interpolant, the result of a
finite but huge case-check, a numeric certificate verified by external
computation. You may **assume such a fact as a Lean `axiom`** instead of proving
it, but ONLY if you describe it here.

> **Axioms, not hypotheses.** A certificate you want to assume must be introduced
> as an `axiom` (so it shows up in `#print axioms` and is checked deterministically
> by `verify.sh`). Do NOT bolt it onto a frozen theorem as a hypothesis `(h : …)`
> — added hypotheses remain forbidden and the faithfulness gate will reject them.

For each axiom you permit, describe in plain words:

- **what** it asserts (the exact mathematical statement being assumed);
- **why** it is assumed rather than proved (e.g. "verified by external
  computation; reproving in Lean is prohibitively slow");
- **where** it is used (which frozen theorem(s) depend on it).

`init.py` reads this section, declares the corresponding `axiom`(s) in
`Defs.lean` with faithful statements, and writes their fully-qualified names into
`scripts/ALLOWED_AXIOMS.txt`. From then on `verify.sh` permits exactly those
axiom names (in addition to the standard three) and **bans every other axiom**.

<!-- Describe the axioms you allow below, or write "None — no assumed axioms." -->

Two axioms are allowed: the two external theorems quoted in the paper's
"Preliminary" section (its Theorem 2.1, Brownawell–Masser, and Theorem 2.2,
Heath-Brown). Both are deep published results whose proofs are far beyond
current formalization technology; the whole point of the paper is how they are
*combined*, and that combination is what must be formalized without shortcuts.
Full statements, the specialized Lean-ready forms, and the justification that
the specialized forms are faithful consequences of the published theorems are
in `SKETCH.md` §3 (Heath-Brown) and §5.2.1 (Brownawell–Masser). Declare no
other axioms.

### Axiom 1: `heath_brown_diagonal_13` (paper's Theorem 2.2 — Heath-Brown)

- **What it asserts.** The specialized, conditional form of Heath-Brown's
  counting theorem for the diagonal ternary form of degree 13 (D. R.
  Heath-Brown, *Sums and differences of three k-th powers*, J. Number Theory
  129 (2009), Theorem 2). Exact statement to declare (from `SKETCH.md` §3):
  for every `M : ℤ`, `M ≠ 0`, IF every triple `p₁ p₂ p₃ : Polynomial ℤ` with
  `p₁^13 + p₂^13 + p₃^13 = Polynomial.C M` and `natDegree pᵢ ≤ 1` (i = 1,2,3)
  consists of constants (`natDegree pᵢ = 0`), THEN there is a real `K ≥ 1`
  such that for all real `X ≥ 1` the number of triples `(x,y,z) ∈ ℤ³` with
  `x^13 + y^13 + z^13 = M` and `|x|, |y|, |z| ≤ X` is at most
  `K * X^(10/13)`. (The integer-only variant — `count^13 ≤ K * X^10` for
  integer `X ≥ 1` — is an acceptable equivalent declaration; see `SKETCH.md`
  §9.4. Either form, but only one, should be declared.)
  The conditional shape is deliberate: it avoids formalizing Heath-Brown's
  "lies on a polynomial parametrization" exclusion predicate and the
  nonsingularity of the form; `SKETCH.md` §3 points 1–4 justify why this is a
  faithful (weakened) consequence of the published theorem, including the
  absorption of the side condition `|N| ≪_F X` and of the paper's
  `ε_c = sgn(−c)` normalization into the constant `K`.
- **Why assumed.** The proof is Heath-Brown's determinant method — deep
  analytic number theory (auxiliary polynomials, p-adic determinants) with no
  Lean formalization in existence; reproving it is far outside the scope of
  this project.
- **Where used.** Exactly one place: the bad-shift estimate
  `badShift_bound` (P3.1 in `SKETCH.md` §6 = paper's Proposition 4.1),
  Step 4. Nothing else may invoke it.

### Axiom 2: `brownawell_masser_P1_four_term` (paper's Theorem 2.1 — Brownawell–Masser)

- **What it asserts.** The four-term Brownawell–Masser S-unit inequality on
  ℙ¹ (W. D. Brownawell, D. W. Masser, *Vanishing sums in function fields*,
  Math. Proc. Camb. Phil. Soc. 100 (1986); genus-zero case, constants as in
  Corvaja–Zannier 2011). Declare it in the concrete bivariate-forms
  formulation "BM4" of `SKETCH.md` §5.2.1, which needs no ℙ¹/height API:
  if `k` is an algebraically closed field of characteristic zero and
  `A₁ A₂ A₃ A₄ : k[S,T]` are nonzero homogeneous forms of common degree `d`
  with `gcd(A₁,A₂,A₃,A₄) = 1`, `A₁ + A₂ + A₃ + A₄ = 0`, no proper nonempty
  sub-sum identically zero, and not all ratios `Aᵢ/Aⱼ` constant, then
  `d ≤ 3 * (z − 2)`, where `z` is the number of distinct projective zeros of
  `A₁·A₂·A₃·A₄` (distinct linear factors over `k`, up to scalar). This is the
  `r = 4` case of the paper's Theorem 2.1 with coefficient `binom(3,2) = 3`,
  transported to forms of common degree via the height computation
  `H = d` for coprime forms (see `SKETCH.md` §5.2.1).
- **Why assumed.** The published proof uses generalized Wronskians over
  function fields; Mathlib contains only the three-term case
  (Mason–Stothers, `Polynomial.abc` in
  `Mathlib/NumberTheory/FLT/MasonStothers.lean`). The three-term case must
  therefore be USED FROM MATHLIB, not axiomatized — this axiom covers the
  four-term case only.
- **Where used.** Only in the function-field exclusion of rational curves
  (paper's Lemma 3.1, Case A = `SKETCH.md` §5.2.2), which feeds Corollary 3.2
  and then the exclusion hypothesis of Axiom 1 inside `badShift_bound`.
  **Note:** `SKETCH.md` §5.1 (Route B) proves the needed degree-≤1 exclusion
  elementarily, in which case this axiom is declared but ends up unused by
  the final theorem — that is the preferred outcome. It is permitted so that
  the paper-faithful Route A (§5.2) is also available. If Route B succeeds,
  the final `#print axioms erdos_477` should show only
  `heath_brown_diagonal_13` beyond the standard three; with Route A it may
  additionally show `brownawell_masser_P1_four_term`. Both outcomes pass.
