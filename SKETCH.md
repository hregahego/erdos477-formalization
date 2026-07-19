# Proof Sketch — Erdős Problem 477
## "The Thirteenth Powers Have a Tiling Complement in the Integers"

**Source:** `auto_math_paper-6.pdf` (Liu, Peng, Yu, Tao, Wang, Zhao).
**Purpose of this document:** a complete, formalization-ready proof sketch to be consumed by
`~/dev/formalization-script` for a Lean 4 + Mathlib formalization. Every lemma is stated
precisely, every proof is spelled out at the level of individual algebraic steps, all
implicit facts used by the paper are made explicit, and the two deep external inputs are
isolated as clearly-marked axiom candidates. Section 9 gives a concrete Lean decomposition.

---

## 0. Global definitions and notation

All variables range over `ℤ` unless stated otherwise.

- **B** := `{ b : ℤ | ∃ m : ℤ, b = m ^ 13 }` — the set of thirteenth powers.
- **D** := `B − B` = `{ d : ℤ | ∃ u v : ℤ, d = u ^ 13 − v ^ 13 }` — the difference set.
- **Q(u,v)** := `∑_{i=0}^{12} u^i · v^(12−i)` — the degree-12 homogeneous cofactor in the
  factorization `u^13 − v^13 = (u − v) · Q(u,v)`.
- For `c ∈ ℤ \ B` and `T ≥ 1`:
  **S_c(T)** := `{ t : ℤ | |t| ≤ T ∧ t^13 − c ∈ D }` — the set of "bad shifts".
- A set `A ⊆ ℤ` is a **tiling complement** for `B` if every `n ∈ ℤ` has a *unique*
  representation `n = a + b` with `a ∈ A`, `b ∈ B`.
- **Asymptotic notation** (paper, end of §1): `U ≪_c V` means `|U| ≤ C(c)·V` for a
  constant `C(c)` depending at most on `c`; similarly `O_c(V)`. This sketch replaces every
  `≪_c` / `O_c` by an explicit constant at the point of use, and also records the paper's
  original `≪_c` display alongside. Appendix A is a ledger matching every displayed
  equation of the paper to its location here.

### Main theorem (target statement)

> **Theorem 1.1.** There exists `A ⊆ ℤ` such that every `n ∈ ℤ` is represented uniquely as
> `n = a + m^13` with `a ∈ A`, `m ∈ ℤ`.

Suggested Lean statement:

```lean
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n
```

(Uniqueness is over the *pair* `(a, m)`. It decomposes into: uniqueness of `(a, b)` with
`b ∈ B`, plus injectivity of `m ↦ m^13` on `ℤ`; see L0.3 and Section 8.)

---

## 1. Architecture of the proof

The proof has five layers, from bottom to top:

```
[AXIOM HB]  Heath-Brown determinant-method count           (Section 3, axiom)
     │
[Step 2]    Exclusion of low-degree polynomial              (Section 5)
            parametrizations of x^13+y^13+z^13 = −c, c ∉ B
     │            (Route B: elementary, RECOMMENDED for Lean;
     │             Route A: paper's function-field proof, needs
     │             Brownawell–Masser [second axiom candidate])
     ▼
[Step 3]    Bad-shift estimate:  |S_c(T)| = O_c(T^{5/6})    (Section 6, Prop 4.1)
     │
[Step 4]    Greedy tiling criterion (pure combinatorics)    (Section 7, Lemma 5.1)
     │
[Step 5]    Verify the criterion for B, assemble Thm 1.1    (Section 8, Prop 5.2)
```

Dependency graph of the formal development:

- `L0.1–L0.6` (elementary facts) → used everywhere.
- `L2.1` (deg ≤ 1 exclusion) needs only `L0.3`, `L0.4` and Vandermonde determinants.
- `P3.1` (bad-shift estimate) needs `L0.*`, `L1.1` (cofactor bound), `L2.1`, and axiom `HB`.
- `L4.1` (greedy criterion) is self-contained combinatorics.
- `P5.1` needs `P3.1`; `Theorem` needs `L4.1` + `P5.1` + `L0.3`.

**Formalization boundary (important).** Exactly ONE deep analytic result must be assumed as
an axiom: Heath-Brown's counting theorem (Section 3), stated below in a specialized,
self-contained form. If Route B of Step 2 is followed (recommended), *nothing else* is
axiomatized: the entire function-field Section of the paper (Brownawell–Masser,
Mason–Stothers, Lemma 3.1, Corollary 3.2) becomes unnecessary, because Heath-Brown only
requires excluding parametrizations of degree ≤ ⌊13/10⌋ = 1, and that special case has the
elementary proof given in Section 5.1.

---

## 2. Elementary lemmas (Layer 0)

These are all trivial but used repeatedly; formalize them first.

**L0.1 (0 ∈ B, 0 ∈ D).** `0 = 0^13 ∈ B`; `0 = 0^13 − 0^13 ∈ D`.

**L0.2 (D is symmetric).** `d ∈ D → −d ∈ D`.
*Proof.* If `d = u^13 − v^13` then `−d = v^13 − u^13`. ∎
(No sign-of-odd-power manipulation needed — just swap `u` and `v`.)

**L0.3 (odd-power injectivity).** The map `m ↦ m^13` is strictly monotone, hence injective,
on `ℤ` (and on `ℝ`, `ℚ`).
*Proof.* `x ↦ x^13` is strictly increasing since 13 is odd. In Mathlib: look for
`Odd.pow_right_strictMono` / `Odd.strictMono` / `Odd.pow_left_injective` (exact name to be
found by the formalizer; the fact is available for odd exponents over linear ordered rings).
Consequence used often: `x^13 = y^13 → x = y`, and `x^13 = −y^13 → x = −y`
(rewrite `−y^13 = (−y)^13`). ∎

**L0.4 (integer 13th roots of integers).** If `c ∈ ℤ`, `d ∈ ℚ` and `d^13 = c`, then
`d ∈ ℤ` and hence `c ∈ B`.
*Proof.* `d` is a rational root of the monic integer polynomial `X^13 − c`; by the rational
root theorem (equivalently: `ℤ` is integrally closed in `ℚ`), `d ∈ ℤ`. ∎
*(Only needed if parametrizations over `ℚ` are considered. If the Heath-Brown axiom is
stated with `ℤ[T]` parametrizations — as in the paper — this lemma can be skipped, because
the relevant constant lands in `ℤ` directly.)*

**L0.5 (c ∉ B → c ≠ 0).** Immediate from L0.1.

**L0.6 (membership reformulation for bad shifts).** For `c, t : ℤ`:
`c − t^13 ∈ D ↔ t^13 − c ∈ D`.
*Proof.* L0.2 applied in both directions, since each side is the negation of the other. ∎

---

## 3. AXIOM: Heath-Brown's theorem (specialized)

The paper cites: D. R. Heath-Brown, *Sums and differences of three k-th powers*,
J. Number Theory 129 (2009), Theorem 2. Paper's statement (its Theorem 2.2):

> Let `F ∈ ℤ[X₁,X₂,X₃]` be a nonsingular ternary form of degree `k ≥ 3`. Let `X ≥ 1`, and
> let `N` be a fixed nonzero integer with `|N| ≪_F X`. The number of integer solutions of
> `F(x₁,x₂,x₃) = N`, `max |x_i| ≤ X`, which do **not** lie on a nonconstant polynomial
> parametrization of degree at most `⌊k/10⌋` is `O_F(X^{10/k})`.
> Here a polynomial parametrization is a triple `p₁,p₂,p₃ ∈ ℤ[T]`, not all constant, with
> `F(p₁(T),p₂(T),p₃(T)) = N` identically.

This is far beyond current formalization technology (the determinant method); it must be an
**axiom** in the Lean development. Do **not** axiomatize the general statement — axiomatize
only the specialized instance actually used, in a *conditional* form that avoids having to
define "lies on a parametrization":

> **AXIOM HB (recommended Lean form).** Let `M : ℤ`, `M ≠ 0`. Assume:
> *(exclusion hypothesis)* every triple `p₁ p₂ p₃ : Polynomial ℤ` with
> `p₁^13 + p₂^13 + p₃^13 = C M` and `natDegree pᵢ ≤ 1` for all `i` has all `pᵢ` constant.
> Then there is a constant `K ≥ 1` (depending on `M`) such that for every real `X ≥ 1`:
> `#{ (x,y,z) : ℤ³ | x^13 + y^13 + z^13 = M ∧ |x| ≤ X ∧ |y| ≤ X ∧ |z| ≤ X } ≤ K · X^(10/13)`.

```lean
axiom heath_brown_diagonal_13 (M : ℤ) (hM : M ≠ 0)
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
        p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C M →
        p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
        p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      (({v : ℤ × ℤ × ℤ | v.1 ^ 13 + v.2.1 ^ 13 + v.2.2 ^ 13 = M ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ X ∧ |(v.2.2 : ℝ)| ≤ X}).ncard : ℝ)
        ≤ K * X ^ ((10 : ℝ) / 13)
```

**Why this form is a faithful consequence of Heath-Brown's theorem:**

1. `F := ε·(X₁^13 + X₂^13 + X₃^13)` with `ε := sgn(M) ∈ {±1}` is a nonsingular form of
   degree `k = 13` (its gradient `(13εx₁^12, 13εx₂^12, 13εx₃^12)` vanishes only at the
   origin). Solutions of `x^13+y^13+z^13 = M` are exactly solutions of `F = |M|` with
   `N := |M| > 0` fixed and nonzero, and polynomial parametrizations correspond likewise
   (`ε·(∑ pᵢ^13) = |M| ↔ ∑ pᵢ^13 = M`). *Consequence: the paper's sign normalization
   `ε_c = sgn(−c)` is purely to match Heath-Brown's published statement; with the axiom
   stated for arbitrary nonzero `M` it disappears from the formal development entirely.*
2. `⌊k/10⌋ = ⌊13/10⌋ = 1`, so only parametrizations of degree ≤ 1 are relevant. Under the
   exclusion hypothesis no nonconstant one exists, hence *no solution is excluded* from
   Heath-Brown's count and the bound applies to *all* solutions in the box.
3. Heath-Brown's side condition `|N| ≪_F X` is absorbed into `K`: for the bounded range
   `1 ≤ X < |M|` the count is trivially at most `(2|M|+1)^3`, a constant depending only on
   `M`, which can be folded into `K`. So the axiom as stated (all `X ≥ 1`) is a true
   consequence.
4. A "polynomial parametrization of degree ≤ 1" means all `pᵢ` affine-linear
   (`pᵢ = aᵢT + bᵢ`), not all constant. Note `natDegree p = 0` covers both constants and
   the zero polynomial — exactly "constant".

**Axiom hygiene:** put this axiom alone in its own file (e.g. `Axioms.lean`) with a comment
citing Heath-Brown 2009, Theorem 2. The final `#print axioms erdos_477` should show only
this axiom plus the classical ones (`Classical.choice`, `propext`, `Quot.sound`).

*(Optional integer-only variant, avoiding `Real.rpow`: state the conclusion as
`∃ K : ℕ, ∀ X : ℤ, 1 ≤ X → (count X)^13 ≤ K * X^10`, where `count X` is the number of
solutions in the box `max(|x|,|y|,|z|) ≤ X`. This is equivalent up to renaming `K`
(`count ≤ K·X^{10/13} ⇒ count^13 ≤ K^13·X^10`) and makes Sections 6–8 pure integer
arithmetic. See Section 9.4.)*

---

## 4. Layer 1: the cofactor lower bound

The factorization used throughout (paper, proof of Prop. 4.1):

```
u^13 − v^13 = (u − v) · Q(u,v) ,
Q(u,v) = u^12 + u^11·v + u^10·v^2 + ⋯ + u·v^11 + v^12  =  ∑_{i=0}^{12} u^i v^(12−i) .
```

**Paper's original argument (for the record).** For real `(u,v) ≠ (0,0)` one has
`Q(u,v) > 0`: for `u ≠ v` it is the difference quotient of the strictly increasing
function `x ↦ x^13`, and on the diagonal `u = v` it takes the limiting value `13·u^12`.
By compactness of the set `{max(|u|,|v|) = 1}` and continuity, there is a constant
`κ > 0` such that

```
Q(u,v) ≥ κ · max(|u|,|v|)^12        for all (u,v) ∈ ℝ²
```

(homogeneity of degree 12 extends the bound from the compact set to all of `ℝ²`).

**This sketch replaces** the compactness argument by the same inequality with the
**explicit constant** `κ = 1/2` (L1.1 below), which is much friendlier to formalize
(no compactness, no `IsCompact.exists_isMinOn`, no extraction of an unnamed constant).
Every later step only uses the displayed inequality, so the two versions are
interchangeable; the paper's `≪_c` constants become explicit accordingly.

**L1.1 (explicit cofactor bound).** For all real `u, v`:
`Q(u,v) := ∑_{i=0}^{12} u^i v^(12−i) ≥ (1/2) · max(|u|,|v|)^12 ≥ 0`.

*Proof.*
1. *Symmetry.* `Q(u,v) = Q(v,u)` — reindex the sum by `i ↦ 12 − i`. Hence WLOG `|v| ≤ |u|`.
2. *Trivial case.* If `u = 0` then `v = 0` and both sides are `0`.
3. *Main case.* Let `u ≠ 0`, `s := v/u ∈ [−1, 1]`. Then
   `Q(u,v) = u^12 · q(s)` where `q(s) = ∑_{j=0}^{12} s^j`
   (factor `u^12` out of each term; note `u^12 = |u|^12 ≥ 0` as 12 is even, and
   `|u| = max(|u|,|v|)`).
4. *Claim: `q(s) ≥ 1/2` for `s ∈ [−1,1]`.*
   - If `0 ≤ s ≤ 1`: every summand `s^j ≥ 0` and the `j = 0` summand is `1`, so `q(s) ≥ 1`.
   - If `−1 ≤ s < 0`: use the geometric-sum identity `(1 − s) · q(s) = 1 − s^13`
     (Mathlib: `geom_sum_eq` / `geom_series` identities; here as the polynomial identity
     `(1−s)·∑_{j<13} s^j = 1 − s^13`, valid for all `s`). Since `s < 0` and 13 is odd,
     `s^13 < 0`, so `1 − s^13 ≥ 1`; and `0 < 1 − s ≤ 2`. Dividing, `q(s) ≥ 1/2`.
5. Combining: `Q(u,v) = |u|^12 · q(s) ≥ (1/2)·max(|u|,|v|)^12`. ∎

**L1.2 (gap bound for distinct integer 13th powers).** For distinct integers `u ≠ v`:
`|u^13 − v^13| ≥ (1/2) · max(|u|,|v|)^12` (as reals, after casting).

*Proof.* `u^13 − v^13 = (u − v) · Q(u,v)` (telescoping/geometric identity — verify by
`ring` after expanding the finite sum, or use `Commute.sub_pow`-style factorization
`a^n − b^n = (a−b)·∑ a^i b^(n−1−i)`; Mathlib candidates: `sub_pow_prime_ne_dvd…`, or prove
directly by `Finset.sum` telescoping). Distinct integers satisfy `|u − v| ≥ 1`, and
`Q(u,v) ≥ 0` by L1.1, so
`|u^13 − v^13| = |u − v| · Q(u,v) ≥ 1 · (1/2)·max(|u|,|v|)^12`. ∎

*(Aside for the formalizer: the sharper all-integer statement
`|u^13 − v^13| ≥ max(|u|,|v|)^12` for distinct integers is also true, but its proof needs
case analysis plus finite checks; the `1/2`-version above is uniform and clean. Use it.)*

---

## 5. Layer 2: exclusion of parametrized solutions

Goal of the layer: verify the exclusion hypothesis of AXIOM HB for `M = −c`, `c ∉ B`.

> **L2.1 (Needed statement).** Let `c ∈ ℤ`, `c ∉ B`. Then every triple
> `p₁, p₂, p₃ ∈ ℤ[T]` with `p₁^13 + p₂^13 + p₃^13 = −c` (as polynomials) and
> `deg pᵢ ≤ 1` for all `i` is a triple of constants.

Two independent proofs are given. **Route B is recommended for Lean** (elementary; no new
axioms). Route A is the paper's argument (Sections 2–3 of the paper), included for
fidelity and as an optional stretch goal; it proves a stronger statement (no nonconstant
*rational* parametrization of *any* degree) but requires a second axiom
(Brownawell–Masser 4-term).

### 5.1 Route B (recommended): elementary Vandermonde argument

*Proof of L2.1.* Write `pᵢ = aᵢT + bᵢ` with `aᵢ, bᵢ ∈ ℤ` (allowed since `deg pᵢ ≤ 1`).
Suppose toward contradiction that not all `pᵢ` are constant, i.e. the index set
`I := { i ∈ {1,2,3} | aᵢ ≠ 0 }` is nonempty.

**Step 1 (coefficient equations).** By the binomial theorem,
`pᵢ^13 = ∑_{j=0}^{13} C(13,j) · aᵢ^(13−j) · bᵢ^j · T^(13−j)`.
Equating coefficients of `T^(13−j)` in `∑ᵢ pᵢ^13 = −c` for `j = 0, 1, …, 12` (all these
powers of `T` have zero coefficient on the right, and `C(13,j) ≠ 0`):

```
(E_j)   ∑_{i=1}^{3} aᵢ^(13−j) · bᵢ^j = 0        for j = 0, 1, …, 12,
(E_13)  ∑_{i=1}^{3} bᵢ^13 = −c.
```

Terms with `i ∉ I` vanish in `(E_j)` for `j ≤ 12` (they contain the factor
`aᵢ^(13−j)` with `13 − j ≥ 1` and `aᵢ = 0`). So for `j = 0,…,12`:

```
(E'_j)   ∑_{i ∈ I} wᵢ · rᵢ^j = 0,   where  rᵢ := bᵢ/aᵢ ∈ ℚ,  wᵢ := aᵢ^13 ∈ ℚ \ {0},
```

using `aᵢ^(13−j) bᵢ^j = aᵢ^13 (bᵢ/aᵢ)^j` (division in `ℚ`; formalize `(E'_j)` over `ℚ`
after casting, or clear denominators — see the Lean note below).

**Step 2 (Vandermonde).** Let `ρ₁ < ρ₂ < … < ρ_s` be the distinct values among
`{rᵢ : i ∈ I}` (so `1 ≤ s ≤ 3`) and `W_k := ∑_{i ∈ I, rᵢ = ρ_k} wᵢ`. Then `(E'_j)` reads
`∑_{k=1}^{s} W_k · ρ_k^j = 0` for `j = 0, …, 12`; in particular for `j = 0, …, s−1`.
The `s×s` matrix `(ρ_k^j)` is a Vandermonde matrix with distinct nodes, hence invertible
(Mathlib: `Matrix.det_vandermonde`, nonzero since the `ρ_k` are distinct). Therefore
`W_k = 0` for every `k`.

**Step 3 (analysis of the groups).** Fix `k` and let `G_k := { i ∈ I | rᵢ = ρ_k }`;
`∑_{i ∈ G_k} aᵢ^13 = 0` with all `aᵢ ≠ 0`. Case on `|G_k|`:

- `|G_k| = 1`, say `G_k = {i}`: then `aᵢ^13 = 0`, so `aᵢ = 0` — **contradiction** with
  `i ∈ I`. Hence **no singleton group exists**; since the `G_k` partition `I ⊆ {1,2,3}`
  into non-singletons, either `s = 1` with `|I| ∈ {2,3}`, i.e. all elements of `I` share
  one ratio `r`.  (A partition of a ≤3-element set with no singleton part has exactly one
  part, of size 2 or 3 — note `s = 1` follows.)

So all `i ∈ I` share `r := bᵢ/aᵢ`, i.e. `bᵢ = r·aᵢ`, i.e. `pᵢ = aᵢ·(T + r)` for `i ∈ I`,
and `∑_{i ∈ I} aᵢ^13 = 0`.

- If `|I| = 3`: `∑ᵢ pᵢ^13 = (∑ᵢ aᵢ^13)·(T + r)^13 = 0`, so `−c = 0`, i.e.
  `c = 0 ∈ B` (L0.1) — contradiction with `c ∉ B`.
- If `|I| = 2`, say `I = {1,2}`: `a₁^13 = −a₂^13 = (−a₂)^13`, so `a₁ = −a₂` (L0.3), and
  `b₁ = r·a₁ = −r·a₂ = −b₂`, hence `p₁ = −p₂` and `p₁^13 + p₂^13 = 0`. Then
  `p₃^13 = −c`; `p₃ = b₃` is constant (`3 ∉ I`), so `c = −b₃^13 = (−b₃)^13 ∈ B` —
  contradiction.
- `|I| = 1` was already excluded (singleton group).

All cases are contradictory, so `I = ∅`: all `pᵢ` are constant. ∎

**Lean notes for Route B.**
- Work with `p : Polynomial ℤ`, extract `aᵢ = p.coeff 1`, `bᵢ = p.coeff 0` from
  `natDegree ≤ 1` (`Polynomial.eq_X_add_C_of_natDegree_le_one` or coeff-wise reasoning).
- Coefficient extraction of `(a•X + C b)^13`: `add_pow` (binomial theorem) +
  `Polynomial.coeff` lemmas; the coefficient of `T^(13−j)` in the sum is
  `C(13,j) · ∑ᵢ aᵢ^(13−j) bᵢ^j`.
- Instead of a literal `s×s` Vandermonde inverse, the cleanest formal path for Step 2–3
  is a direct case analysis on `|I| ∈ {1,2,3}` and on which of the ratios coincide
  (at most 3 rationals): each case uses only equations `(E'_0), (E'_1), (E'_2)` and
  2×2/3×3 Vandermonde determinants, or even bare-hands linear algebra:
  - `|I| = 1`: `(E'_0)` gives `w₁ = 0`, contradiction.
  - `|I| = 2`, `r₁ ≠ r₂`: `(E'_0), (E'_1)` give `w₁(r₁ − r₂) = 0` ⟹ `w₁ = 0`,
    contradiction. `r₁ = r₂`: proceed as in Step 3.
  - `|I| = 3`, all `rᵢ` distinct: 3×3 Vandermonde ⟹ all `wᵢ = 0`, contradiction.
    Two coincide (`r₁ = r₂ ≠ r₃` up to relabeling): reduce to the 2-node case with
    weights `w₁ + w₂` and `w₃` ⟹ `w₃ = 0`, contradiction. All equal: Step 3.
- Everything happens in `ℚ` (cast `aᵢ, bᵢ : ℤ` into `ℚ`; `rᵢ` needs division). The final
  conclusions `c = 0` / `c = (−b₃)^13` are integer statements; `b₃ ∈ ℤ` so no rational
  root theorem is needed.
- The identity `∑_{i∈I} pᵢ^13 = (∑_{i∈I} aᵢ^13)(T+r)^13` when `pᵢ = aᵢ(T+r)`: use
  `mul_pow` and factor the sum.

### 5.2 Route A (paper-faithful): function-field exclusion

This proves the stronger Corollary 3.2 of the paper. It needs the Brownawell–Masser
theorem; its 3-term case is Mason–Stothers (available in Mathlib:
`Mathlib/NumberTheory/FLT/MasonStothers.lean`, theorem `Polynomial.abc` — verify exact
form), but the **4-term case is not in Mathlib** and would itself have to be either
axiomatized or formalized from scratch (generalized Wronskians). This is why Route B is
recommended. Details follow for completeness.

#### 5.2.1 External input: Brownawell–Masser on ℙ¹ (paper's Theorem 2.1)

Exact statement (paper's Theorem 2.1):

> Let `k` be an algebraically closed field of characteristic zero, and let `S` be a
> finite set of points of `ℙ¹_k`. Let `u₁, …, u_r ∈ k(t)^×` be `S`-units (all zeros and
> poles inside `S`), with `r ≥ 3`, not all constant, satisfying
>
> ```
> u₁ + u₂ + ⋯ + u_r = 0 ,
> ```
>
> and suppose that no proper nonempty sub-sum vanishes. With the projective height
> convention
>
> ```
> H(u₁ : ⋯ : u_r)  =  − ∑_{P ∈ ℙ¹_k}  min_{1 ≤ i ≤ r} ord_P(uᵢ) ,
> ```
>
> one has
>
> ```
> H(u₁ : ⋯ : u_r)  ≤  binom(r−1, 2) · (|S| − 2) .
> ```
>
> For `r = 3` this is the Mason–Stothers inequality, with coefficient
> `binom(2,2) = 1`; for `r = 4` the coefficient is `binom(3,2) = 3`.

(The paper notes: this is the genus-zero case of Brownawell–Masser 1986; the height
convention and the three- and four-term constants are as recalled by Corvaja–Zannier
2011.)

Concrete bivariate reformulation suitable for an axiom (identifying points of `ℙ¹_k` with
linear forms up to scalar, `ord_P(form)` = multiplicity of the corresponding linear factor):

> **Axiom candidate BM4.** Let `k` be an algebraically closed field of characteristic 0 and
> `A₁, A₂, A₃, A₄ ∈ k[S,T]` nonzero homogeneous forms of common degree `d`, with
> `gcd(A₁,A₂,A₃,A₄) = 1`, `A₁ + A₂ + A₃ + A₄ = 0`, no proper nonempty sub-sum `≡ 0`, and
> not all ratios `Aᵢ/Aⱼ` constant. Let `z` := number of distinct projective zeros of
> `A₁A₂A₃A₄` (= distinct linear factors over `k` up to scalar). Then `d ≤ 3(z − 2)`.

(The height computation `H(A₁ : ⋯ : A₄) = d` for forms of common degree `d` without common
zero: at each finite point the minimum of the orders is 0 since not all `Aᵢ` vanish; the
standard normalization by `T^d` contributes `−d` at the point `[1:0]`; total `H = d`.)

#### 5.2.2 Lemma 3.1 of the paper

> **Lemma.** Let `N ∈ ℚ^×` and `X_N : X^13 + Y^13 + Z^13 = N·W^13 ⊂ ℙ³_ℚ`. If
> `N ∉ ℚ^13` then `X_N` contains no nonconstant `ℚ`-rational parametrized curve. If
> `N = d^13`, `d ∈ ℚ^×`, the images of nonconstant morphisms `ℙ¹ → X_N` are exactly the
> three lines `{X = −Y, Z = dW}`, `{X = −Z, Y = dW}`, `{Y = −Z, X = dW}`.

*Proof (full detail).* A nonconstant morphism `φ : ℙ¹_ℚ → X_N` is written
`φ = [F : G : H : R]` with `F, G, H, R ∈ ℚ[S,T]` homogeneous of common degree `e ≥ 1` and
**no common zero** (zero coordinate forms allowed). The defining equation gives the
polynomial identity

```
(3.1)   F^13 + G^13 + H^13 − N·R^13 = 0 .
```

Extend scalars to `ℚ̄` and case on how many of the four terms
`F^13, G^13, H^13, −N·R^13` are (identically) nonzero.

**Case A: all four nonzero, no proper nonempty sub-sum vanishes.**
Divide (3.1) by `F^13`: the four rational functions `1, (G/F)^13, (H/F)^13, −N(R/F)^13`
sum to zero, are `S`-units for `S :=` zeros of `F·G·H·R` in `ℙ¹_ℚ̄` (so `|S| ≤ 4e`, each
factor being a degree-`e` form with ≤ `e` distinct zeros), are not all constant (if
`G/F, H/F, R/F` were all constant, `φ` would be constant), and no proper sub-sum vanishes
(inherited from the terms of (3.1)). The height is
`H(F^13 : G^13 : H^13 : −N·R^13) = 13e` (forms of common degree `13e` with no common
zero — the constant `−N` doesn't change orders). Brownawell–Masser with `r = 4` gives
`13e ≤ 3(|S| − 2) ≤ 3(4e − 2) = 12e − 6`, i.e. `e ≤ −6` — **impossible**.

**Case B: exactly three terms nonzero.**
First, a proper vanishing sub-sum among the three nonzero terms is impossible: a minimal
one would have length ≤ 2; length 1 contradicts the terms being nonzero; length 2 forces
the complementary length-1 sub-sum (within the three-term identity) to vanish too,
again a contradiction. So no proper sub-sum vanishes. The three nonzero coordinate forms
have no common zero (the zero form vanishes identically, so the no-common-zero condition
of all four descends to the three). With `S :=` zeros of the product of the three forms,
`|S| ≤ 3e`, height `= 13e`, Mason–Stothers (`r = 3`) gives `13e ≤ |S| − 2 ≤ 3e − 2` —
**impossible**. Hence Case B never occurs.

**Case C: at most two terms nonzero.**
Zero nonzero terms would force all of `F, G, H, R ≡ 0`, contradicting no-common-zero.
One nonzero term summing to zero is absurd. Two nonzero terms: (3.1) says they are
negatives of each other; e.g. if the two nonzero coordinate forms are `P₁, P₂` (with
constants `λᵢ ∈ {1, −N}`), then `(P₁/P₂)^13` is a nonzero constant, and a rational
function with constant nonzero 13th power is constant (its order at every point satisfies
`13·ord_P = 0`). So `P₁/P₂` is constant and the other two coordinates are `≡ 0`, making
`φ` constant — **contradicts nonconstancy**.

**Case D: all four nonzero, some proper nonempty sub-sum vanishes.**
A vanishing sub-sum of length 1 contradicts nonzeroness; length 3 forces the
complementary length-1 sub-sum to vanish, same contradiction. Hence the four terms split
into **two vanishing pairs**. The three possible pairings:

1. The pairing

   ```
   F^13 + G^13 = 0 ,          H^13 − N·R^13 = 0 .
   ```

   *First equality ⟹ `F = −G`*: `(F/G)^13 = −1` with `F/G ∈ ℚ(S/T)`; a rational
   function whose 13th power is a nonzero constant is itself constant (orders argument as
   in Case C), and since `F/G` has `ℚ`-coefficients the constant lies in `ℚ`; the only
   rational solution of `x^13 = −1` is `x = −1`, because `ℚ` contains no nontrivial 13th
   root of unity and 13 is odd (L0.3 over `ℚ`). Hence `F = −G`.

   *Second equality ⟹ `N = d^13`*: it gives `(H/R)^13 = N` in `ℚ(S/T)`, so `H/R` is a
   rational function on `ℙ¹_ℚ̄`. For a point `P ∈ ℙ¹_ℚ̄`, let `ord_P(f)` denote the order
   of a nonzero rational function `f` at `P` (positive at a zero, negative at a pole,
   zero otherwise). Taking orders of `(H/R)^13 = N` at any `P ∈ ℙ¹_ℚ̄`:

   ```
   (3.2)   13 · ord_P(H/R) = ord_P(N) = 0 .
   ```

   Indeed `N ∈ ℚ^×` is a nonzero constant, so it has no zeros or poles on `ℙ¹_ℚ̄`.
   Therefore `ord_P(H/R) = 0` for every `P`, so `H/R` has neither zeros nor poles on
   `ℙ¹_ℚ̄` and is constant. Since `H/R ∈ ℚ(S/T)`, this constant lies in `ℚ`:

   ```
   H/R = d   for some d ∈ ℚ^× ,     and consequently     N = d^13 .
   ```

   The image of `φ` then lies in the line `X = −Y, Z = dW`.
2. The pairing `F^13 + H^13 = 0`, `G^13 − N·R^13 = 0` gives, in the same way,
   `F = −H`, `G/R = d ∈ ℚ^×`, `N = d^13`: line `X = −Z, Y = dW`.
3. The pairing `G^13 + H^13 = 0`, `F^13 − N·R^13 = 0` gives `G = −H`, `F/R = d`,
   `N = d^13`: line `Y = −Z, X = dW`.

**Conclusion.** A nonconstant `ℚ`-parametrized curve forces `N = d^13 ∈ ℚ^13` and image
one of the three lines. Conversely for `N = d^13` the three lines lie in `X_N` (e.g.
`[s : −s : d·t : t]` satisfies `s^13 + (−s)^13 + (dt)^13 = d^13·t^13 = N·t^13`) and are
`ℚ`-rational. ∎

#### 5.2.3 Corollary 3.2 of the paper, and derivation of L2.1

> **Corollary.** For `c ∈ ℤ \ B`, the affine surface `u^13 − v^13 − t^13 = −c` has no
> nonconstant rational parametrization over `ℚ`.

*Proof.* Substitute `X = u, Y = −v, Z = −t` (odd exponent: `(−v)^13 = −v^13`):
the equation becomes `X^13 + Y^13 + Z^13 = −c`, with projective closure
`X^13 + Y^13 + Z^13 = (−c)·W^13`, i.e. `N = −c`. Since 13 is odd, `−c ∈ ℚ^13 ↔ c ∈ ℚ^13`
(`−c = d^13 ↔ c = (−d)^13`), and for integer `c`, `c ∈ ℚ^13 ↔ c ∈ B` (L0.4). So `c ∉ B`
implies `N ∉ ℚ^13` and Lemma 3.1 applies: no nonconstant rational parametrized curve. ∎

*Derivation of L2.1 from the Corollary.* Given a nonconstant polynomial triple
`p₁, p₂, p₃ ∈ ℤ[T] ⊆ ℚ[T]` with `∑ pᵢ^13 = −c`, homogenize: let `e := max deg pᵢ ≥ 1`,
`Pᵢ(S,T) := T^e · pᵢ(S/T)` and `W := T^e`. Then `[P₁ : P₂ : P₃ : W]` defines a morphism
`ℙ¹ → ℙ³`: at points with `T ≠ 0` the coordinate `W ≠ 0`; at `[1 : 0]` the coordinate
`Pᵢ(1,0)` equals the degree-`e` coefficient of `pᵢ`, nonzero for at least one `i` by the
choice of `e`. It is nonconstant (some `pᵢ` nonconstant) and lands in `X_{−c}` — a
nonconstant rational parametrized curve, contradicting the Corollary. ∎

---

## 6. Layer 3: the bad-shift estimate (paper's Proposition 4.1)

> **P3.1.** For every `c ∈ ℤ \ B` there is a constant `K_c ≥ 1` such that for every
> integer `T ≥ 1`:  `|S_c(T)| ≤ K_c · T^(5/6)` (real inequality after casting).
> In particular `|S_c(T)| = o(T)`.

*Proof (full detail).*

**Step 0 (setup).** `S_c(T) = { t | −T ≤ t ≤ T ∧ t^13 − c ∈ D }` is finite (subset of an
integer interval). Fix `c ∉ B`; note `c ≠ 0` (L0.5), so `M := −c ≠ 0`.

**Step 1 (from a bad shift to a solution of the diagonal equation).** Let `t ∈ S_c(T)`.
By definition of `D` there are `u, v ∈ ℤ` with

```
(4.1)   t^13 − c = u^13 − v^13 ,      or equivalently      u^13 − v^13 − t^13 = −c .
```

*Claim: `u ≠ v`.* Since `c ∉ B`, we cannot have `u = v`, for then `t^13 − c = 0` and
`c = t^13 ∈ B` — contradiction.

Using classical choice, fix for each `t ∈ S_c(T)` one such pair `(u_t, v_t)`, and set
(the paper's substitution)

```
x := u_t ,      y := −v_t ,      z := −t .
```

Then (4.1) becomes (odd exponent: `(−v)^13 = −v^13`, `(−t)^13 = −t^13`)

```
(4.3)   x^13 + y^13 + z^13 = −c .
```

Write `Φ(t) := (x, y, z) = (u_t, −v_t, −t)`. **Φ is injective**: the third coordinate
recovers `t` (`t = −z`).

**Step 2 (size bound; paper's equation (4.2)).** Factor as in Section 4:

```
u^13 − v^13 = (u − v) · Q(u,v) ,      Q(u,v) = u^12 + u^11·v + ⋯ + u·v^11 + v^12 ,
```

with `Q(u,v) ≥ κ · max(|u|,|v|)^12`, `κ = 1/2` (L1.1; the paper obtains an unspecified
`κ > 0` by compactness — see Section 4). As `u_t ≠ v_t` are distinct integers,
`|u_t − v_t| ≥ 1`, and hence

```
κ · max(|u_t|,|v_t|)^12  ≤  |u_t^13 − v_t^13|  =  |t^13 − c|  ≤  T^13 + |c|  ≤  (1 + |c|)·T^13
```

(using `|t| ≤ T` and `T ≥ 1`, so `|c| ≤ |c|·T^13`; the paper writes this chain as
`κ max(|u|,|v|)^12 ≤ |u^13 − v^13| = |t^13 − c| ≪_c T^13`). Thus

```
(4.2)   max(|u_t|,|v_t|) ≪_c T^(13/12) ;
        explicitly:  max(|u_t|,|v_t|) ≤ (2(1 + |c|))^(1/12) · T^(13/12) .
```

By (4.2) and `|t| ≤ T ≤ T^(13/12) ≤ (2(1+|c|))^(1/12)·T^(13/12)` (the constant is ≥ 1),
every solution `(x, y, z) = Φ(t)` obtained from an element of `S_c(T)` satisfies

```
max(|x|, |y|, |z|) ≤ X ,      X := C_c · T^(13/12) ,   C_c := (2(1 + |c|))^(1/12) ≥ 1
```

(the paper: "for a suitable constant `C_c`"; `X ≥ 1` since `T ≥ 1`).

**Step 3 (the paper's ε_c-normalization, and the exclusion hypothesis).** The paper now
matches (4.3) to Heath-Brown's statement: let `ε_c := sgn(−c) ∈ {±1}` (well-defined since
`c ≠ 0`). Equation (4.3) is equivalent to

```
ε_c · (x^13 + y^13 + z^13) = |c| .
```

The form `ε_c·(X₁^13 + X₂^13 + X₃^13)` is nonsingular of degree 13 (gradient vanishes
only at the origin). For all sufficiently large `X` one has `|c| ≪ X`; the remaining
bounded range of `X` is absorbed by the implied constant. Since `⌊13/10⌋ = 1`,
Theorem 2.2 (Heath-Brown) excludes only nonconstant polynomial parametrizations of degree
at most one; Corollary 3.2 (Route A) excludes nonconstant rational parametrizations of
*any* degree on (4.3) — and L2.1 (Route B) excludes precisely the degree-≤1 polynomial
ones, which is all that is needed. Hence **no solutions of (4.3) are lost** in applying
Theorem 2.2.

In the axiom-form of Section 3 this entire step is a single invocation: L2.1 provides the
hypothesis `hexcl` of AXIOM HB for `M = −c ≠ 0` (the `ε_c`-normalization is absorbed into
the axiom's justification, Section 3 point 1).

**Step 4 (count).** AXIOM HB (equivalently, the paper's application of Theorem 2.2)
yields `K ≥ 1` depending only on `M = −c` such that

```
#{ (x,y,z) ∈ ℤ³ : x^13 + y^13 + z^13 = −c ,  max(|x|,|y|,|z|) ≤ X }  ≤  K · X^(10/13)
```

(the paper writes `≪_c X^(10/13)`). Each `t ∈ S_c(T)` gives at least one such triple
`Φ(t)`, and `Φ` is injective (Step 1), so

```
|S_c(T)|  ≤  #solutions  ≤  K · X^(10/13)
          =   K · C_c^(10/13) · (T^(13/12))^(10/13)
          =   K · C_c^(10/13) · T^(5/6)
```

(the paper: `|S_c(T)| ≪_c X^(10/13) ≪_c (T^(13/12))^(10/13) = T^(5/6)`). Set
`K_c := K · C_c^(10/13) = K · (2(1+|c|))^(5/78)` — any upper bound will do, e.g.
`K · (2(1+|c|))`, to keep exponent arithmetic minimal. ∎

**Lean notes.**
- Real-exponent arithmetic: `Real.rpow`; the identities needed are
  `(T^(13/12))^(10/13) = T^(10/12) = T^(5/6)` (via `Real.rpow_natCast`,
  `Real.rpow_mul` for `T ≥ 0`) — or avoid `rpow` entirely with the integer-only variant
  in Section 9.4 (`|S_c(T)|^156 ≤ K'_c · T^130`; note `5/6 = 130/156`,
  `156 = 12·13`, `130 = 10·13`).
- Finiteness of `S_c(T)`: define as `Finset.filter` over `Finset.Icc (−T) T` with
  classical decidability (`Classical.decPred`), or as a `Set` with an `ncard` and a
  `Set.Finite` proof by inclusion in `Set.Icc`.
- Choice of `(u_t, v_t)`: `Classical.choice` / `Exists.choose`; injectivity of `Φ` via
  third coordinate: `fun h => by injection`-style, `t = −(Φ t).2.2`.
- Card comparison: `Finset.card_le_card_of_injOn Φ` (image inside the solution set of the
  axiom).

---

## 7. Layer 4: the greedy tiling criterion (paper's Lemma 5.1)

This layer is pure combinatorics/set theory — no number theory. Formalize independently.

> **L4.1.** Let `B ⊆ ℤ`, `D := B − B`. Suppose that for every **finite** set
> `C ⊆ ℤ \ B` there exists `b ∈ B` such that
>
> ```
> (5.1)   (C − b) ∩ D = ∅        (i.e.  ∀ c ∈ C,  c − b ∉ D) .
> ```
>
> Then `B` has a tiling complement: there is `A ⊆ ℤ` such that every `n ∈ ℤ` has a unique
> representation `n = a + b`, `a ∈ A`, `b ∈ B`.
>
> (We refer to this hypothesis as `(H)` below.)

Remarks before the proof:
- `(H)` applied to `C = ∅` shows `B ≠ ∅`.
- `0 ∈ D` always (`b − b`), assuming `B ≠ ∅`.
- The key invariant is: `A` is *`D`-separated*, meaning `∀ a a' ∈ A, a ≠ a' → a − a' ∉ D`.
  `D`-separatedness ⟺ the translates `a + B` (`a ∈ A`) are pairwise disjoint:
  `(a + B) ∩ (a' + B) ≠ ∅ ↔ a − a' ∈ B − B = D` (from `a + b' = a' + b ⟹ a − a' = b − b'`).

*Proof (full detail).*

**Enumeration.** Fix a bijection `n : ℕ≥1 → ℤ`, writing `n₁, n₂, n₃, …` (Lean:
`Denumerable ℤ` provides `ℕ ≃ ℤ`; index from 0 if preferred).

**Recursive construction.** Define finite sets `A₀ ⊆ A₁ ⊆ A₂ ⊆ ⋯` with the invariants:

- `(I1)` `A_j` is `D`-separated;
- `(I2)` `n_i ∈ A_j + B` for every `i ≤ j`.

`A₀ := ∅` (both invariants trivially hold). Given `A_{j−1}`:

- **Case 1: `n_j ∈ A_{j−1} + B`.** Set `A_j := A_{j−1}`. `(I1)` unchanged; `(I2)`: for
  `i < j` by induction hypothesis, for `i = j` by the case assumption.
- **Case 2: `n_j ∉ A_{j−1} + B`.** Then for every `a ∈ A_{j−1}`: `n_j − a ∉ B`. Hence

  ```
  C_j := { n_j − a : a ∈ A_{j−1} }  ⊆  ℤ \ B,   finite.
  ```

  By `(H)` choose `b_j ∈ B` with `(C_j − b_j) ∩ D = ∅`, and set

  ```
  a_j := n_j − b_j ,     A_j := A_{j−1} ∪ {a_j} .
  ```

  Verification of the invariants:
  - `n_j = a_j + b_j ∈ A_j + B`, giving `(I2)` for `i = j`; for `i < j` use
    `A_{j−1} ⊆ A_j`.
  - `(I1)`: take distinct `a, a' ∈ A_j`. If both are in `A_{j−1}`, done by induction. The
    remaining case is (up to symmetry) `a' = a_j`, `a ∈ A_{j−1}`. Then

    ```
    a_j − a = (n_j − a) − b_j ∈ C_j − b_j ,   hence   a_j − a ∉ D ;
    ```

    and `a − a_j ∉ D` by symmetry of `D` (L0.2: `D = −D`). In the paper's phrasing: thus
    `(a_j + B) ∩ (a + B) = ∅` for every `a ∈ A_{j−1}`, because an intersection would
    imply `a_j − a ∈ B − B = D` (see the translate-disjointness remark before this
    proof).
  - (Also `a_j ∉ A_{j−1}`: if `a_j = a ∈ A_{j−1}` then `a_j − a = 0 ∈ D`, contradicting
    the previous point. So `A_j` genuinely grows and the "distinct" analysis above is
    exhaustive.)

**The complement.** `A := ⋃_{j≥0} A_j`.

- **Covering.** Every `n ∈ ℤ` equals `n_j` for some `j` (bijection), and
  `n_j ∈ A_j + B ⊆ A + B` by `(I2)`.
- **`A` is `D`-separated.** Distinct `a, a' ∈ A` lie in `A_i, A_{i'}`; since the family is
  a chain (monotone in `j`), both lie in `A_{max(i,i')}`, which is `D`-separated by `(I1)`.
- **Uniqueness.** Suppose `n = a + b = a' + b'` with `a, a' ∈ A`, `b, b' ∈ B`. If
  `a ≠ a'`, then `a − a' = b' − b ∈ B − B = D`, contradicting `D`-separatedness. So
  `a = a'`, and then `b = b'` by cancellation. ∎

**Lean notes.**
- Define `Aseq : ℕ → Finset ℤ` by `Nat.rec`; the choice of `b_j` in Case 2 uses
  `Classical` choice applied to `(H)` (package `(H)` as
  `∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) → ∃ b, b ∈ B ∧ ∀ c ∈ C, c − b ∉ D`).
- Case split `n_j ∈ A_{j−1} + B` is not decidable constructively — use
  `Classical.dec`/`open Classical` (fine: the theorem is an existence statement).
- Prove monotonicity `Aseq i ⊆ Aseq j` for `i ≤ j` by induction, then the chain argument.
- Prove `(I1)`/`(I2)` as one combined induction (a `structure` or an `And` in the motive).
- `C_j` as `(Aseq (j−1)).image (fun a => n_j − a)`.

---

## 8. Layer 5: verification of the criterion and final assembly

### 8.1 P5.1 (paper's Proposition 5.2)

> **P5.1.** `B = {m^13}` satisfies hypothesis `(H)` of L4.1: for every finite
> `C ⊆ ℤ \ B` there exists `b ∈ B` with `∀ c ∈ C, c − b ∉ D`.

*Proof (full detail).*
If `C = ∅`, take `b := 0 ∈ B` (L0.1); the condition is vacuous.

Otherwise: for fixed `c ∈ C`, a choice `b = t^13 ∈ B` is *bad for `c`* precisely when
`c − t^13 ∈ D`, which by L0.6 is equivalent to `t^13 − c ∈ D`. Thus the bad `t` with
`|t| ≤ T` are exactly the elements of `S_c(T)` (well-defined: `c ∈ C ⊆ ℤ \ B`).

By P3.1, `|S_c(T)| ≤ K_c · T^(5/6)` for all `T ≥ 1`. Let `K := ∑_{c ∈ C} K_c` (finite
sum, `K ≥ 1`). Choose an integer `T` with `T > K^6` and `T ≥ 1` (e.g. `T := ⌊K⌋^6 + ⌊K⌋ + 1`,
or any integer `> K^6`). Then

```
|⋃_{c ∈ C} S_c(T)| ≤ ∑_{c ∈ C} |S_c(T)| ≤ K · T^(5/6) < T^(1/6) · T^(5/6) = T < 2T + 1 ,
```

using `K < T^(1/6)` (from `T > K^6`, sixth roots; or argue with sixth powers:
`K^6 < T ⟹ (K·T^(5/6))^6 = K^6·T^5 < T^6`, so `K·T^(5/6) < T`).

The interval `{t : |t| ≤ T}` has `2T + 1` elements, strictly more than the union of the
bad sets. Hence there exists `t₀` with `|t₀| ≤ T` and `t₀ ∉ S_c(T)` for every `c ∈ C`.
Set `b := t₀^13 ∈ B`. For each `c ∈ C`: `t₀ ∉ S_c(T)` and `|t₀| ≤ T` force
`t₀^13 − c ∉ D`, i.e. (L0.6) `c − b ∉ D`. ∎

### 8.2 Proof of Theorem 1.1

By P5.1 the hypothesis of L4.1 holds for `B = {m^13 : m ∈ ℤ}`, so there is `A ⊆ ℤ` such
that every `n` has a unique representation `n = a + b`, `a ∈ A`, `b ∈ B`.

Upgrade to the `(a, m)`-form: given `n`, existence of `(a, m)` with `n = a + m^13` is
existence of `(a, b)` plus surjectivity of `m ↦ m^13` onto `B` (definition of `B`).
Uniqueness: if `a + m^13 = a' + m'^13` with `a, a' ∈ A`, then by uniqueness of the
`(a, b)`-representation, `a = a'` and `m^13 = m'^13`, whence `m = m'` by L0.3. ∎

---

## 9. Lean 4 formalization plan

### 9.1 Suggested file layout

```
Erdos477/
  Defs.lean          -- B, D, Q, S_c(T); L0.1–L0.6
  Axioms.lean        -- AXIOM HB only (with citation comment)
  Cofactor.lean      -- L1.1, L1.2 (real-valued, explicit κ = 1/2)
  ParamExclusion.lean-- L2.1 via Route B (Vandermonde / case analysis)
  BadShift.lean      -- P3.1
  Greedy.lean        -- L4.1 (fully self-contained; can be proven first/in parallel)
  Main.lean          -- P5.1 and erdos_477
```

### 9.2 Suggested formal statements (adapt as needed)

```lean
def Bset : Set ℤ := {b | ∃ m : ℤ, b = m ^ 13}
def Dset : Set ℤ := {d | ∃ u v : ℤ, d = u ^ 13 - v ^ 13}

-- L2.1
theorem no_linear_param (c : ℤ) (hc : c ∉ Bset) :
    ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0

-- P3.1 (real-exponent version)
theorem badShift_bound (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Finset.Icc (-T) T).filter (fun t => t ^ 13 - c ∈ Dset)).card
        ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6)

-- L4.1
theorem greedy_tiling (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
         ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n

-- final
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n
```

(Keep `Dset` and the `B − B` set defeq or provide a simp lemma
`Dset = {d | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x − y}`.)

### 9.3 Mathlib ingredients to locate

- Odd-power strict monotonicity/injectivity on `ℤ`/`ℝ`/`ℚ` (`Odd.pow_right_strictMono`,
  `Odd.strictMono`, `Odd.pow_left_injective` — search with `loogle`/`leansearch`).
- Geometric sum identity `(1 − s) * ∑_{j<n} s^j = 1 − s^n` (`geom_sum_mul`,
  `mul_geom_sum`, or `Finset.geom_sum_eq`).
- Factorization `a^n − b^n = (a − b) * ∑ a^i b^(n−1−i)`
  (`sub_mul_geom_sum₂`-style; in Mathlib `Commute.geom_sum₂_mul` /
  `geom_sum₂_mul_comm`: `(∑ i in range n, x^i * y^(n−1−i)) * (x − y) = x^n − y^n`).
- Vandermonde: `Matrix.vandermonde`, `Matrix.det_vandermonde` (product of differences);
  or hand-rolled 2×2/3×3 eliminations (likely simpler — see Route B Lean notes).
- Binomial theorem for polynomials: `add_pow`; coefficient extraction:
  `Polynomial.coeff_add`, `Polynomial.coeff_C_mul`, `Polynomial.coeff_X_pow`,
  `Polynomial.eq_X_add_C_of_natDegree_le_one`.
- Cardinalities: `Int.card_Icc` (`(Finset.Icc a b).card = (b + 1 − a).toNat`),
  `Finset.card_le_card_of_injOn`, `Finset.card_biUnion_le` (union of bad sets bound),
  `Finset.exists_mem_notMem`-style pigeonhole: from
  `(bad).card < (Finset.Icc (−T) T).card` conclude `∃ t ∈ Icc, t ∉ bad`
  (e.g. via `Finset.card_lt_card` and `Finset.ssubset_iff` / `Finset.exists_of_ssubset`
  applied to `bad ∩ Icc ⊆ Icc`).
- `Denumerable ℤ` (equiv `ℕ ≃ ℤ`) for the enumeration in L4.1.
- `Real.rpow` algebra: `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_le_rpow` — only if
  the real-exponent route is taken (see 9.4 for the alternative).
- Mason–Stothers (`Polynomial.abc`, file `Mathlib/NumberTheory/FLT/MasonStothers.lean`) —
  ONLY if Route A is attempted; not needed for Route B.

### 9.4 Optional integer-only variant (no `Real.rpow` anywhere)

All fractional exponents can be eliminated; this often halves the pain in Lean:

- **Axiom HB (integer form):** conclusion
  `∀ X : ℤ, 1 ≤ X → (count X)^13 ≤ K * X^10` with `K : ℤ`, where `count X` is the card of
  the solution Finset in the box `max(|x|,|y|,|z|) ≤ X`.
- **L1.2 (integer form):** `2 * |u^13 − v^13| ≥ max(|u|,|v|)^12` for distinct integers
  (multiply through by 2; prove via the `ℚ`- or `ℝ`-valued L1.1 and casting, keeping the
  *statement* integral).
- **Step 2 of P3.1:** define `X₀ : ℤ` as the least integer with `X₀ ≥ T` and
  `X₀^12 ≥ 2(1+|c|)·T^13` (exists; e.g. `X₀ ≤ 2(1+|c|)·T^2` crudely, but better keep it
  implicit via `Int.least` / explicit witness `X₀ := (2(1+|c|))·T^2` is TOO LOSSY — instead
  use minimality: then `(X₀ − 1)^12 < 2(1+|c|)T^13` or `X₀ ≤ max(T, 1) + …`; from
  `X₀ ≥ 2 ⟹ X₀ ≤ 2(X₀ − 1)` get `X₀^12 ≤ 2^12·(X₀−1)^12 < 2^12·2(1+|c|)·T^13`).
- **P3.1 (integer form):** `|S_c(T)|^156 ≤ K'_c * T^130` for all `T ≥ 1`
  (since `count^13 ≤ K·X₀^10` gives `count^156 = (count^13)^12 ≤ K^12·(X₀^12)^10
  ≤ K^12·(2^13(1+|c|))^10·T^130`; exponent check: `156 = 12·13`, `130 = 13·10`,
  and `130/156 = 5/6`).
- **P5.1:** need `∑_{c∈C} |S_c(T)| < 2T + 1`. From the 156-power bound: if
  `T > K'' · |C|^156` (with `K'' := max_c K'_c`), then for each `c`:
  `(|C| · |S_c(T)|)^156 ≤ |C|^156·K''·T^130 < T·T^130 ≤ T^156` (using `T ≥ 1`), so
  `|C| · |S_c(T)| < T`, hence `∑_c |S_c(T)| ≤ |C| · max_c |S_c(T)| < T < 2T + 1`.
  All in `ℤ`; the only analysis left in the whole development is inside the axiom.

### 9.5 Known pitfalls / fidelity checklist

1. **`0 ∈ B`** — do not forget `m = 0`; it gives `c ∉ B → c ≠ 0` (needed for `M ≠ 0` in
   the axiom) and the `C = ∅` case of P5.1.
2. **Symmetry of `D`** is used silently by the paper twice (L0.6 in P5.1; `a − a_j ∉ D`
   in L4.1). It's L0.2 — trivial but must be explicit in Lean.
3. **`u ≠ v` in Step 1 of P3.1** relies on `c ∉ B` — this is exactly where "bad shifts
   are constrained" comes from; don't lose the hypothesis.
4. **Uniqueness upgrade** from `(a, b)` pairs to `(a, m)` pairs needs L0.3
   (13 odd ⟹ `m ↦ m^13` injective). The paper mentions this in the final proof.
5. **Definition of `S_c(T)`** uses `|t| ≤ T`, giving `2T + 1` candidate shifts; the count
   comparison in P5.1 is strict (`< 2T+1`), which is what produces the good `t₀`.
6. **Choice** is used in three places (pair `(u_t, v_t)` in P3.1; `b_j` in L4.1; `t₀` in
   P5.1) — all fine classically; no constructive content is claimed.
7. **Degree convention**: `natDegree 0 = 0`; "not all constant" ⟺ `¬(∀ i, natDegree pᵢ = 0)`;
   the exclusion statement L2.1 is phrased so that the zero polynomial counts as constant
   (harmless: the conclusion is "all constant").
8. **Casting discipline**: `t^13` computed in `ℤ`, inequalities in `ℝ` (or stay in `ℤ`
   with 9.4). `|(t : ℝ)| = |t|` via `Int.cast_abs`/`abs_intCast`.
9. In L4.1, Case 2 must also establish `a_j ∉ A_{j−1}` (via `0 ∈ D`) so that
   `A_j = A_{j−1} ∪ {a_j}` has the separation property for *all* distinct pairs; the
   paper leaves this implicit.
10. The exponent chain must come out to exactly `5/6`:
    `max ≲ T^(13/12)` (from degree-12 cofactor vs degree-13 range) and
    `count ≲ X^(10/13)` (Heath-Brown) compose to `T^(13/12 · 10/13) = T^(5/6) = o(T)`.
    Any slack that degrades `13/12` to `2` (crude bounds) breaks `o(T)` — see the warning
    in 9.4 about not replacing `X₀` by `O(T^2)`.

### 9.6 What NOT to formalize

- The paper's Section 2 (Brownawell–Masser, Theorem 2.1) and Section 3 (Lemma 3.1,
  Corollary 3.2) are **not needed** under Route B. They exclude rational
  parametrizations of *all* degrees, but Heath-Brown's `⌊13/10⌋ = 1` means only linear
  parametrizations matter, and L2.1 (Route B) handles those elementarily. Formalizing
  Route A would require a second axiom (BM4) or a from-scratch Wronskian development —
  recommended only as a stretch goal.
- Heath-Brown's Theorem 2.2 in general form (nonsingular forms, "lies on a
  parametrization" predicate): the specialized conditional AXIOM HB avoids defining
  nonsingularity and the incidence predicate altogether.

### 9.7 Suggested build order (matches dependency graph)

1. `Defs.lean` + L0.* (minutes).
2. `Greedy.lean` / L4.1 — independent of everything else; good first target.
3. `Cofactor.lean` / L1.1–L1.2.
4. `ParamExclusion.lean` / L2.1 (Route B) — the most intricate elementary piece
   (binomial coefficient extraction + small linear algebra).
5. `Axioms.lean` — freeze the axiom statement early so `BadShift.lean` can proceed.
6. `BadShift.lean` / P3.1.
7. `Main.lean` / P5.1 + `erdos_477`.
8. Run `#print axioms erdos_477`; expect exactly
   `[Classical.choice, propext, Quot.sound, heath_brown_diagonal_13]`.

---

## 10. Summary of the mathematical content (one paragraph)

For `c` not a 13th power, a shift `t^13` is "bad" (i.e. `t^13 − c` is a difference of two
13th powers) only if the diagonal surface `x^13 + y^13 + z^13 = −c` has an integer point
with `z = −t` and all coordinates `≲ T^{13/12}` (the coordinate bound comes from the
degree-12 cofactor `Q` in `u^13 − v^13 = (u−v)Q(u,v)`, bounded below by
`½·max(|u|,|v|)^{12}`). The surface admits no nonconstant linear polynomial
parametrization (elementary Vandermonde argument; the paper proves the stronger statement
that it admits no rational curves at all, via Brownawell–Masser over function fields), so
Heath-Brown's determinant-method bound counts *all* such integer points:
`O_c((T^{13/12})^{10/13}) = O_c(T^{5/6}) = o(T)` bad shifts up to `T`. Since finitely many
constraints `c ∈ C` exclude only `o(T)` of the `2T+1` available shifts, a good shift
`b = t₀^{13}` always exists, and a greedy transfinite (in fact `ℕ`-indexed) construction
— add each integer in turn, translated by a good shift that keeps all chosen translates of
`B` disjoint — produces a set `A` whose translates of `B` partition `ℤ`: a tiling
complement for the thirteenth powers.

---

## Appendix A — Ledger: every displayed equation / step of the paper ↔ this sketch

Every numbered equation and every displayed formula of the paper appears in this sketch.
The table below is the completeness check; use it to audit the formalization for
paper-fidelity.

| Paper location | Exact content | Sketch location |
|---|---|---|
| §1, Thm 1.1 | `B = {m^13 : m ∈ ℤ}`; unique `n = a + m^13`, `a ∈ A`, `m ∈ ℤ` | §0 (defs + target statement); §8.2 |
| §1 | `D = B − B = {u^13 − v^13 : u, v ∈ ℤ}` | §0 |
| §1 (overview) | diagonal surface `u^13 − v^13 − t^13 = −c` for `c ∉ B` | §6 (4.1); §5.2.3 |
| §1 (notation) | `U ≪_c V` ⟺ `|U| ≤ C(c)·V`; `O_c(V)` | §0, last bullet |
| Thm 2.1 | `u₁ + ⋯ + u_r = 0`; height `H(u₁:⋯:u_r) = −∑_P min_i ord_P(uᵢ)`; bound `H ≤ binom(r−1,2)(|S|−2)`; `r = 3` = Mason–Stothers, coefficient 1 | §5.2.1 (verbatim); bivariate reformulation = axiom candidate BM4 |
| Thm 2.2 | nonsingular ternary form `F`, deg `k ≥ 3`; `F(x₁,x₂,x₃) = N`, `max|xᵢ| ≤ X`, `|N| ≪_F X`; count off parametrizations of degree ≤ `⌊k/10⌋` is `O_F(X^{10/k})`; parametrization = `p₁,p₂,p₃ ∈ ℤ[T]` not all constant with `F(p₁,p₂,p₃) = N` | §3 (statement quoted; specialized conditional form = AXIOM HB; points 1–4 justify each hypothesis transfer) |
| Lemma 3.1 | `X_N : X^13 + Y^13 + Z^13 = N·W^13 ⊂ ℙ³_ℚ`; `N ∉ ℚ^13` ⟹ no nonconstant ℚ-rational curve; `N = d^13` ⟹ exactly the lines `X=−Y,Z=dW`; `X=−Z,Y=dW`; `Y=−Z,X=dW` | §5.2.2 (statement + full proof) |
| Lemma 3.1 proof | `φ = [F : G : H : R]`, forms of common degree `e ≥ 1`, no common zero, zero coordinate forms allowed | §5.2.2, setup |
| (3.1) | `F^13 + G^13 + H^13 − N·R^13 = 0` | §5.2.2, display (3.1) |
| Case: 4 nonzero terms, no vanishing sub-sum | units `1, (G/F)^13, (H/F)^13, −N(R/F)^13`; `S` = zeros of `FGHR`, `|S| ≤ 4e`; `H(F^13:G^13:H^13:R^13) = 13e`; mult. by `N` height-invariant; `13e ≤ 3(|S|−2) ≤ 3(4e−2) = 12e−6`, impossible | §5.2.2, Case A |
| Case: exactly 3 nonzero terms | `|S| ≤ 3e`, height `13e`, `13e ≤ |S|−2 ≤ 3e−2`, impossible; a proper vanishing sub-sum among 3 terms forces a 1-term sub-sum to vanish — impossible | §5.2.2, Case B |
| Case: ≤ 2 nonzero terms | ratio of the two nonzero coordinate forms constant ⟹ image a point ⟹ contradicts nonconstancy | §5.2.2, Case C |
| Case: 4 nonzero + vanishing sub-sum | lengths 1, 3 impossible; split into two vanishing pairs; pairing `F^13 + G^13 = 0`, `H^13 − N·R^13 = 0` ⟹ `F = −G` (no nontrivial 13th roots of unity in ℚ, 13 odd) | §5.2.2, Case D, item 1 |
| (3.2) | `13·ord_P(H/R) = ord_P(N) = 0` | §5.2.2, Case D, display (3.2) |
| after (3.2) | `ord_P(H/R) = 0` ∀P ⟹ `H/R` no zeros/poles ⟹ constant; `H/R ∈ ℚ(S/T)` ⟹ `H/R = d ∈ ℚ^×`, `N = d^13` | §5.2.2, Case D, item 1 |
| other pairings | lines `X=−Z, Y=dW` and `Y=−Z, X=dW` in the same way | §5.2.2, Case D, items 2–3 |
| converse | for `N = d^13` the three lines lie in `X_N` and are ℚ-rational (e.g. `[s:−s:dt:t]`) | §5.2.2, Conclusion |
| Cor 3.2 | `u^13 − v^13 − t^13 = −c` has no nonconstant rational parametrization over ℚ for `c ∈ ℤ∖B`; substitution `X = u, Y = −v, Z = −t`; closure `X^13+Y^13+Z^13 = (−c)·W^13`; 13 odd ⟹ (`−c ∈ ℚ^13 ⟺ c ∈ ℚ^13`); integer `c`: `c ∈ ℚ^13 ⟺ c = m^13` | §5.2.3 (+ L0.4) |
| §4, def | `S_c(T) = {t ∈ ℤ : |t| ≤ T, t^13 − c ∈ B − B}` | §0 |
| Prop 4.1 | `|S_c(T)| = O_c(T^{5/6}) = o(T)` | §6, P3.1 (explicit `K_c`) |
| (4.1) | `t^13 − c = u^13 − v^13`, equivalently `u^13 − v^13 − t^13 = −c`; `c ∉ B ⟹ u ≠ v` | §6, Step 1 |
| §4 factorization | `u^13 − v^13 = (u−v)·Q(u,v)`, `Q = u^12 + u^11 v + ⋯ + u v^11 + v^12` | §4 (display); §6 Step 2 |
| §4 positivity | `Q > 0` for real `(u,v) ≠ (0,0)` (difference quotient; diagonal value `13u^12`); compactness on `max(|u|,|v|) = 1` ⟹ `Q(u,v) ≥ κ·max(|u|,|v|)^12` on ℝ² | §4 ("paper's original argument"); explicit `κ = 1/2` in L1.1 |
| §4 chain | `κ·max(|u|,|v|)^12 ≤ |u^13 − v^13| = |t^13 − c| ≪_c T^13` (via `|u − v| ≥ 1`) | §6, Step 2 |
| (4.2) | `max(|u|,|v|) ≪_c T^{13/12}` | §6, Step 2 (with explicit constant) |
| §4 substitution | `x = u, y = −v, z = −t` | §6, Step 1 |
| (4.3) | `x^13 + y^13 + z^13 = −c` | §6, Step 1 |
| §4 box | `max(|x|,|y|,|z|) ≤ X`, `X = C_c·T^{13/12}` | §6, Step 2 |
| §4 normalization | `ε_c = sgn(−c) ∈ {±1}`; (4.3) ⟺ `ε_c(x^13+y^13+z^13) = |c|`; form `ε_c(X₁^13+X₂^13+X₃^13)` nonsingular of degree 13; `|c| ≪ X` for large `X`, bounded range absorbed | §6, Step 3 (and §3, point 1/3, where it is absorbed into AXIOM HB) |
| §4 exclusion | `⌊13/10⌋ = 1`; Thm 2.2 excludes only nonconstant polynomial parametrizations of degree ≤ 1; Cor 3.2 excludes nonconstant rational parametrizations of any degree; no solutions of (4.3) lost | §6, Step 3; L2.1 (Route B) / §5.2.3 (Route A) |
| §4 count | `#{(x,y,z) ∈ ℤ³ : x^13+y^13+z^13 = −c, max(|x|,|y|,|z|) ≤ X} ≪_c X^{10/13}` | §6, Step 4 (= AXIOM HB conclusion) |
| §4 conclusion | each `t ∈ S_c(T)` gives ≥ 1 triple; `|S_c(T)| ≪_c X^{10/13} ≪_c (T^{13/12})^{10/13} = T^{5/6}` | §6, Steps 1 (injectivity) + 4 |
| Lemma 5.1, (5.1) | `(C − b) ∩ D = ∅` | §7, L4.1 statement |
| Lemma 5.1 proof | enumerate `ℤ` as `n₁, n₂, …`; finite `A₀ ⊂ A₁ ⊂ A₂ ⊂ ⋯`; translates `a + B`, `a ∈ A_j`, pairwise disjoint and covering `n₁, …, n_j` | §7, construction + invariants (I1), (I2) |
| Lemma 5.1 proof | `A₀ = ∅`; if `n_j ∈ A_{j−1} + B` set `A_j = A_{j−1}`; else `n_j − a ∉ B` ∀`a`, so `C_j = {n_j − a : a ∈ A_{j−1}} ⊂ ℤ∖B` | §7, Cases 1–2 |
| Lemma 5.1 proof | choose `b_j ∈ B` with `(C_j − b_j) ∩ D = ∅`; put `a_j = n_j − b_j`, `A_j = A_{j−1} ∪ {a_j}`; `n_j = a_j + b_j ∈ a_j + B` | §7, Case 2 |
| Lemma 5.1 proof | for old `a ∈ A_{j−1}`: `a_j − a = (n_j − a) − b_j ∉ D`; `(a_j+B) ∩ (a+B) = ∅` since intersection ⟹ `a_j − a ∈ B − B = D` | §7, Case 2 (I1) |
| Lemma 5.1 proof | `A = ⋃_{j≥0} A_j`; every integer eventually covered; translates pairwise disjoint; unique representation `a + b` | §7, "The complement" |
| Prop 5.2 | for fixed `c ∈ C`, `b = t^13` bad ⟺ `c − t^13 ∈ D`; `D` symmetric ⟺ `t^13 − c ∈ D`; bad `t` with `|t| ≤ T` = `S_c(T)`; each `o(T)` (Prop 4.1); `C` finite ⟹ union `o(T)`; `2T + 1` integers with `|t| ≤ T`; large `T` ⟹ some `t` avoids all; `b = t^13` satisfies `(C − b) ∩ D = ∅` | §8.1 (with explicit `T > K^6`) |
| Proof of Thm 1.1 | Prop 5.2 verifies Lemma 5.1's hypothesis; unique `n = a + b`; `m ↦ m^13` injective on ℤ ⟹ unique `n = a + m^13` | §8.2 (+ L0.3) |

**Deliberate deviations from the paper (both strictly conservative):**

1. §4/L1.1: the paper's compactness constant `κ` is instantiated as `κ = 1/2` with an
   elementary proof; every downstream inequality only becomes more explicit.
2. §5.1/L2.1 (Route B): the paper excludes rational parametrizations of *all* degrees
   via Thm 2.1 (Brownawell–Masser); the formal route needs only degree ≤ 1 (since
   `⌊13/10⌋ = 1`) and proves that case elementarily. The paper's full argument is
   retained as Route A (§5.2) with the 4-term Brownawell–Masser isolated as axiom
   candidate BM4.

Everything else follows the paper step-for-step.
