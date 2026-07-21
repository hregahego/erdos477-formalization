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

Two axioms are permitted, and — see the requirement boxes below — **both are
MANDATORY**: the final theorem must actually depend on both of them, and each
must be stated **EXACTLY as the corresponding theorem of the paper** (*The
Thirteenth Powers Have a Tiling Complement in the Integers*, Liu–Peng–Yu–Tao–
Wang–Zhao; local copy `~/Downloads/auto_math_paper-6.pdf`), Theorems 2.1 and
2.2 in Section 2 ("Preliminary"). The paper's asymptotic conventions apply:
`U ≪_c V` means `|U| ≤ C(c)·V` for a constant depending at most on `c`;
similarly for `O_c(V)`.

**Guiding principle (applies throughout): axiomatize the GENERAL statement,
derive the specific.** Whenever an external result is assumed, the `axiom` must
be the cited theorem in its full published generality as quoted in the paper;
every specialized, reformulated, or instantiated version that the development
actually consumes must be **proved in Lean as a lemma from that axiom**. The
specialization bridges are proof obligations, never assumptions.

### Axiom 1: `Erdos477.heath_brown_diagonal_13` = paper's Theorem 2.2, EXACTLY

- **What it asserts — verbatim Theorem 2.2 (Heath-Brown).** Let
  `F ∈ ℤ[X₁,X₂,X₃]` be a nonsingular ternary form of degree `k ≥ 3`. Let
  `X ≥ 1`, and let `N` be a fixed nonzero integer with `|N| ≪_F X`. The number
  of integer solutions of `F(x₁,x₂,x₃) = N`, `max_i |x_i| ≤ X`, which do **not**
  lie on a nonconstant polynomial parametrization of degree at most `⌊k/10⌋`,
  is `O_F(X^{10/k})`. Here a polynomial parametrization means a triple
  `p₁, p₂, p₃ ∈ ℤ[T]`, not all constant, such that
  `F(p₁(T), p₂(T), p₃(T)) = N` identically; a solution *lies on* it if it
  equals `(p₁(t), p₂(t), p₃(t))` for some `t ∈ ℤ`.
- **EXACT-MATCH requirement (this OVERRIDES `SKETCH.md` §3).** The sketch
  directs axiomatizing only a specialized, conditional diagonal-13 instance
  ("AXIOM HB") to avoid defining "lies on a parametrization". **That advice is
  revoked.** The Lean `axiom` must be a faithful transcription of the *general*
  Theorem 2.2 exactly as quoted above: general nonsingular ternary form of
  degree `k ≥ 3`, the genuine "does not lie on a nonconstant polynomial
  parametrization of degree ≤ ⌊k/10⌋" exclusion (so the notion of lying on a
  parametrization must be *defined* in Lean), the side condition `|N| ≪_F X`,
  and the `O_F(X^{10/k})` conclusion — rendered with explicit constants in the
  standard way (the implied constant of the conclusion may depend on `F` and on
  the implied constant assumed in `|N| ≪_F X`, and on nothing else). No
  specialization to `k = 13`, no restriction to the diagonal form, no
  conditional reformulation, no added or dropped hypotheses.
- **Consequence: the sketch's AXIOM HB becomes a THEOREM.** The specialized
  conditional statement of `SKETCH.md` §3 must be **proved in Lean** from this
  axiom, following the bridge already spelled out in the sketch's "why this
  form is a faithful consequence" notes and the paper's Proposition 4.1:
  `ε·(X₁¹³+X₂¹³+X₃¹³)` with `ε = sgn(M)` is nonsingular of degree 13;
  `⌊13/10⌋ = 1`, and under the exclusion hypothesis no solution lies on a
  nonconstant parametrization of degree ≤ 1, so none is excluded from the
  count; the bounded range `1 ≤ X < |M|` is absorbed into the constant. These
  bridging steps are proof obligations, not assumptions.
- **Why it is assumed.** Theorem 2.2 is Theorem 2 of Heath-Brown, *Sums and
  differences of three k-th powers*, J. Number Theory 129 (2009) (reference [5]
  of the paper). The determinant method is far beyond current formalization
  technology.
- **Where it is used.** Paper's Proposition 4.1 (the bad-shift estimate,
  SKETCH §6–8): applied to `ε_c·(X₁¹³+X₂¹³+X₃¹³) = |c|` (equivalently
  `x¹³+y¹³+z¹³ = −c`) for each `c ∉ B`, after Corollary 3.2 (via Axiom 2)
  excludes nonconstant rational parametrizations, yielding
  `#solutions ≪_c X^{10/13}` and hence `|S_c(T)| ≪_c T^{5/6} = o(T)`.

### Axiom 2: `Erdos477.brownawell_masser_P1_four_term` = paper's Theorem 2.1, EXACTLY

- **What it asserts — verbatim Theorem 2.1 (Brownawell–Masser on ℙ¹).** Let
  `k` be an algebraically closed field of characteristic zero, and let `S` be a
  finite set of points of `ℙ¹_k`. Let `u₁, …, u_r ∈ k(t)^×` be `S`-units (all
  zeros and poles inside `S`), with `r ≥ 3`, not all constant, satisfying
  `u₁ + ⋯ + u_r = 0`, and suppose that no proper nonempty sub-sum vanishes.
  With the projective height convention
  `H(u₁ : ⋯ : u_r) = − ∑_{P ∈ ℙ¹_k} min_{1≤i≤r} ord_P(uᵢ)`, one has
  `H(u₁ : ⋯ : u_r) ≤ binom(r−1, 2) · (|S| − 2)`. (For `r = 3` this is the
  Mason–Stothers inequality, with coefficient 1; for `r = 4` the coefficient is
  `binom(3,2) = 3`.)
- **Naming note.** The axiom name is fixed as
  `brownawell_masser_P1_four_term` (the four-term instance is the one Mathlib
  lacks and the one driving Case A), but **despite the name the statement must
  be the full `r ≥ 3` theorem exactly as in the paper** — do NOT hard-code
  `r = 4` into the axiom.
- **EXACT-MATCH requirement (this OVERRIDES `SKETCH.md` §5.2.1).** The
  sketch's bivariate reformulation "Axiom candidate BM4" (homogeneous forms
  `A₁,…,A₄ ∈ k[S,T]`, `d ≤ 3(z−2)`) is **NOT acceptable as the axiom**. The
  Lean `axiom` must faithfully state Theorem 2.1 itself: `S`-units in
  `k(t)^×`, orders `ord_P` at points of `ℙ¹_k` (finite points *and* the point
  at infinity), the projective height convention as displayed, general `r ≥ 3`,
  the no-vanishing-proper-nonempty-sub-sum hypothesis, and the
  `binom(r−1,2)(|S|−2)` bound. Any working reformulation the proofs prefer
  (e.g. BM4, or a version for homogeneous forms) must be **derived from the
  axiom in Lean** via the height computation recorded in `SKETCH.md` §5.2.1
  (`H(A₁ : ⋯ : A₄) = d` for common-degree-`d` forms with no common zero) —
  again a proof obligation, not an assumption.
- **Why it is assumed.** This is the genus-zero case of Brownawell–Masser,
  *Vanishing sums in function fields* (1986) (paper's reference [2]), with the
  height convention and the three- and four-term constants as recalled by
  Corvaja–Zannier (2011) (paper's reference [3]). The proof needs generalized
  Wronskians; the `r ≥ 4` cases are not in Mathlib.
- **Where it is used.** Paper's Lemma 3.1 (SKETCH §5.2.2), which feeds
  Corollary 3.2: the **four-term case** (`r = 4`, coefficient 3) in the
  all-four-terms-nonzero case, giving `13e ≤ 3(4e − 2) = 12e − 6` —
  impossible; **and** the **three-term case** (`r = 3`, coefficient 1) in the
  exactly-three-terms-nonzero case, giving `13e ≤ 3e − 2` — impossible. The
  paper invokes both as instances of Theorem 2.1 ("the three-term
  Mason–Stothers case of Theorem 2.1"), so to be exactly faithful **both
  applications must be instances of this single axiom**. Do not substitute
  Mathlib's Mason–Stothers (`Polynomial.abc`) on the dependency path of the
  main theorem; it may at most appear in side lemmas used for cross-checking.

### ⚠ REQUIREMENT: both axioms MUST be used (paper faithfulness)

**This overrides the sketch's route recommendation.** `SKETCH.md` §5 offers two
proofs of the exclusion statement L2.1 and recommends Route B (the elementary
Vandermonde argument, no second axiom). **Do NOT take Route B.** To be
**completely faithful to the paper**, the formalization must follow **Route A**
(`SKETCH.md` §5.2): prove the exclusion of parametrized solutions via the
paper's Lemma 3.1 and Corollary 3.2, i.e. via the function-field argument that
invokes Theorem 2.1 (= `brownawell_masser_P1_four_term`) in its four-term and
three-term cases exactly as in the paper's Section 3.

Concretely, these are hard acceptance criteria, not preferences:

- Each axiom's Lean statement must be checkable, side by side against the PDF,
  as an exact transcription of Theorem 2.1 / Theorem 2.2 — same hypotheses,
  same conclusion, same generality. Reviewers must reject any strengthening,
  weakening, specialization, or reformulation *of the axioms themselves*;
  specializations belong in proved lemmas downstream of the axioms.
- `#print axioms` on the final theorem (`erdos_477`) must show **exactly**
  `{propext, Classical.choice, Quot.sound, Erdos477.heath_brown_diagonal_13,
  Erdos477.brownawell_masser_P1_four_term}` — i.e. the proof genuinely
  **depends on both** custom axioms. If `brownawell_masser_P1_four_term` is
  declared but the final theorem does not depend on it, the run is
  **unfaithful and must be rejected** in review, even though every proof
  compiles: it means the exclusion layer silently took Route B instead of the
  paper's argument.
- The Route B Vandermonde proof of L2.1 must **not** be used as the proof
  that feeds the main theorem (it may exist as a side lemma for comparison,
  but nothing on the dependency path of `erdos_477` may use it).
- Reviewers/auditors: when checking faithfulness, verify both axiom names
  appear in the `#print axioms erdos_477` output produced by `verify.sh`, and
  verify the axiom statements against the paper as above.

`init.py` should therefore declare **both** axioms and write **both**
fully-qualified names into `scripts/ALLOWED_AXIOMS.txt`.
