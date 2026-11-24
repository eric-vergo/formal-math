/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import Statement
import Comparator.VpVnp.Solution

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "The statement to trust" =>

%%%
tag := "chapter-statement"
file := "statement"
htmlSplit := .never
number := false
%%%

The file {repoFile "vp-vnp/Statement.lean"}[`Statement.lean`] is 98 lines long, imports `Mathlib`
and nothing else, and defines everything the results are stated with: circuits and their size, the
two polynomials, the bound, approximation, families, VP, its closure, VNP, and four propositions.
The theorems of `Solution.lean` have these propositions as their types. A check of the proofs
therefore establishes these propositions and no others, and what they mean is decided by this
file and by the Mathlib definitions it uses. The paper prints the file in Section 3 (pages 11–12,
in {repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) “so that a reader can check that it correctly
formalizes the statements in this paper”, and says of that comparison (Section Q.1, page 66):
“Whether the statements say what is meant was judged only by AI readers. No human mathematician
has checked the development, the statement file or the proofs.”

This chapter is written for that check. It shows every declaration of the file in the file's
order, the Lean source on the right as the build compiled it. On the left is a reading in standard
notation, and after each declaration a comparison with the definitions of the literature: where
the file follows them, where it takes a variant, and why the variant is equivalent, with the
argument or its source. *The readings and comparisons are this blueprint's gloss, written by an AI
model. No tool has checked them against the Lean statements and no human has reviewed them.* They
are one more reading of the kind the paper describes, laid out so that an expert can redo it in
one sitting. Statements about the literature are background, with a standard reference each; they
are not taken from the paper unless a page is given.

The file begins

```
import Mathlib

open MvPolynomial

universe u

namespace Statement
```

and ends with `end Statement`. Its module docstring reads “Definitions and statements, using
Mathlib only. The proofs are in Solution.lean.” Docstrings appear on the right with the code; they
are comments, and nothing below relies on them.

# The one line this build spells differently
%%%
tag := "statement-spelling"
%%%

The file shown in this chapter is not, character for character, the file the paper prints. It
differs in one line, in `Statement.Approximates`. The paper (Section 3, page 12) and the upstream
development, on Lean 4.33.1 with Mathlib at commit `0df444a360e`, have

```
    ∀ (d : V →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d q).coeff i = if i = 0 then coeff d f else 0
```

This build, on Lean 4.36.0 with Mathlib `v4.36.0`, has

```
    ∀ (d : V →₀ ℕ) (i : ℤ), i ≤ 0 → (q.coeff d).coeff i = if i = 0 then f.coeff d else 0
```

Upstream's `coeff d q` is Mathlib's function `MvPolynomial.coeff`, the coefficient of the monomial
$`x^d` in the polynomial $`q`. The newer Mathlib defines multivariate polynomials through a
structure whose field `coeff` holds the coefficients, has no function `MvPolynomial.coeff`, and
writes the same coefficient `q.coeff d`. The outer `.coeff i`, the coefficient of
$`\varepsilon^i` in a Laurent series, is spelled as before. No other line of the file differs:
the script {repoFile "vp-vnp/scripts/statement-diff.py"}[`scripts/statement-diff.py`] compares
every declaration of `Statement.lean`, of the challenge and the solution and of the `Paper`
library with upstream and reports this definition and three theorems of `Paper` as changed in
this spelling only, and everything else as the same
({ref "chapter-checking"}[How to check this yourself] gives the command and its output).

What supports the claim that the two spellings mean the same is of two kinds, and they should
not be confused.

- _Machine-checked, in this build._ The file
  {repoFile "vp-vnp/scripts/StatementSpelling.lean"}[`scripts/StatementSpelling.lean`] proves that
  `p.coeff d` is additive in `p` and is `a` at `d`, and `0` at every other exponent, on the
  monomial `monomial d a`; that any function with these two properties equals
  `fun d p ↦ p.coeff d` (by induction over polynomials); and that `Statement.Approximates`,
  written with any pair of functions that have the two properties in place of the two
  coefficients, is equivalent to `Statement.Approximates` as this build has it.
- _Cited, not machine-checked here._ That upstream's `MvPolynomial.coeff` has the two properties
  is the content of the lemmas `MvPolynomial.coeff_add` and `MvPolynomial.coeff_monomial` of the
  Mathlib revision upstream uses. Those lemmas live in a different Mathlib from the one this site
  is built with, so no single Lean run contains both spellings, and the identification of the
  printed definition with this build's rests on reading those two lemmas.

The file {repoFile "vp-vnp/PORTING.md"}[`PORTING.md`] sets the four statements side by side and
lists every other change the newer toolchain required, all of them in proofs.

Every verdict and every mark on this site is about the statements as this build spells them: the
five theorems as stated with `q.coeff d`, compiled with Lean 4.36.0 and Mathlib `v4.36.0`. The
checks of the paper's own development, on Lean 4.33.1, are reported by the paper (Section Q.1)
and are not repeated by this site.

# Circuits

:::definition "Statement.Computes" (lean := "Statement.Computes") (parent := "part-claim")
*Reading (gloss).* Let $`R` be a commutative semiring, $`V` a type of variables and
$`f \in R[x_v : v \in V]`. `Computes f s` holds when there is a sequence of polynomials
$`\ell_0, \ell_1, \ell_2, \ldots` in $`R[x_v : v \in V]` such that

- for every $`k < s`, the polynomial $`\ell_k` is a variable $`x_v`, or a constant $`a \in R`,
  or $`\ell_i + \ell_j` for some $`i, j < k`, or $`\ell_i \cdot \ell_j` for some $`i, j < k`
  (the case $`i = j` is allowed), and
- $`f = \ell_k` for some $`k < s`.

So `Computes f s` says: $`f` has an arithmetic circuit with at most $`s` gates. This is the model
of Section 1.3 of the paper (pages 3–4), where the size of a circuit is “the length of the list,
so that variables and constants are counted as gates”. The paper defines circuits over a
commutative ring; the file allows a commutative semiring (Section Q.3, page 68: “In the file
printed in Section 3 circuits and the classes VP and VNP are defined over commutative
semirings”), and every proposition of the file takes $`R` to be a field or the field of Laurent
series over one.
:::

*What counts.* A gate is an entry of the list. Variables and constants are gates and cost one
each; a variable or constant used several times is paid for once. Sum and product gates have
fan-in two and unbounded fan-out. There is no subtraction and no division gate, and no scalar
multiplication other than a product with a constant gate. Any element of $`R` may be a constant,
at the cost of one gate; when $`R` is a field $`F`, the constants are those of $`F`, not of a
subfield. The output may be any gate. The entries $`\ell_k` with $`k \ge s` are unconstrained and
play no role, and `Computes f 0` is false. The property is monotone in $`s`
({InlineLean.name}`Nc.Computes.mono`, for the definition {InlineLean.name}`Nc.Computes` of the
proof, which unfolds to this one).

*The object computed.* Each $`\ell_k` is a polynomial, an element of Mathlib's
`MvPolynomial V R`, and the conditions are equations between polynomials. A circuit must produce
$`f` as a formal polynomial, not a function that agrees with $`f` on some set of inputs. This is
the point at which the algebraic model differs from the Boolean one, and it is why the paper says
that its bound “does not apply to Boolean circuits” (page 1).

*Comparison with the standard model.* This is a straight-line program, equivalently a circuit
with gates $`+` and $`\times` of fan-in two, over $`R` with arbitrary constants: the model of
Valiant's classes (Valiant, _Completeness classes in algebra_, 1979; Bürgisser, _Completeness and
Reduction in Algebraic Complexity Theory_, 2000). Three conventions vary in the literature, and
none of them affects any statement of the file, each of which is insensitive to a constant factor
in the size.

- _Counting inputs._ The usual complexity measure counts the arithmetic operations and takes
  variables and constants as free inputs. The file counts them. The paper's footnote 2 (page 4):
  “Counting only the additions and multiplications would change the size by a factor of at most
  three.” The argument is elementary: input gates that no operation reads can be dropped, unless
  the output is itself an input, and $`t \ge 1` operation gates read at most $`2t` input gates,
  so the two counts $`t` and $`s` of a smallest circuit satisfy $`t \le s \le 3t`. It is not
  formalized (Section Q.3, page 70).
- _Subtraction._ Over a ring, $`\ell_i - \ell_j` is $`\ell_i + (-1) \cdot \ell_j`: three gates,
  one of them the constant $`-1`, shared by all subtractions.
- _Division._ The file has no division gate, as is standard for VP. (Strassen's elimination of
  divisions shows that they save at most a polynomial factor for polynomials of polynomially
  bounded degree over infinite fields; the paper does not use this and nothing here depends on
  it.)

For a lower bound, arbitrary constants at unit cost and unrestricted fan-out are the strong
choices: every circuit of a more restricted kind is a circuit in this sense.

# The two polynomials

:::definition "Statement.perm" (lean := "Statement.perm") (parent := "part-claim")
*Reading (gloss).* `perm F m` is the polynomial
$$`\sum_{\sigma \in S_m} \prod_{i} x_{\sigma(i),\, i}`
in the $`m^2` variables $`x_{i,j}`, $`(i,j) \in \{0, \ldots, m-1\}^2`, over the commutative
semiring `F`. The paper's $`\mathrm{PERM}_m` (page 1) is $`\sum_\sigma \prod_i x_{i,\sigma(i)}`;
“the two sums agree, as one sees by replacing $`\sigma` with its inverse” (Section Q.3, page 68).
:::

:::definition "Statement.hc" (lean := "Statement.hc") (parent := "part-claim")
*Reading (gloss).* `hc F m` is $`\sum_{\sigma} \prod_{i} x_{i,\sigma(i)}`, the sum over the
permutations $`\sigma` of $`\{0, \ldots, m-1\}` with `σ.IsCycleOn Set.univ`. Mathlib defines
`f.IsCycleOn s` as: $`f` maps $`s` bijectively to itself, and any two points of $`s` lie in the
same cycle of $`f`. On the whole set the first condition always holds, and the second says that
$`\sigma` has a single orbit. For $`m \ge 2` these are the $`(m-1)!` cyclic permutations of
length $`m`, and `hc F m` is the paper's $`\mathrm{HC}_m` (page 1), the Hamiltonian cycle
polynomial of the complete directed graph on $`m` vertices.
:::

*Small cases.* For $`m = 1` the identity qualifies and `hc F 1` is $`x_{0,0}`; for $`m = 0` the
one permutation of the empty set qualifies and `hc F 0` is $`1`. Neither matters: every statement
of the file concerns $`m \ge m_0` with $`m_0` chosen by the proof. `open Classical` supplies the
decidability instance that the filtered sum needs and does not change the polynomial.

*Comparison.* Both are the standard polynomials, the permanent written for the transposed
matrix. They are defined over every commutative semiring, so over a field of characteristic two
`perm F m` is the determinant, as the paper says (page 2).

# The bound

:::definition "Statement.Beyond" (lean := "Statement.Beyond") (parent := "part-claim")
*Reading (gloss).* `Beyond c m s` is the inequality
$$`m^{\,c\,(\log_2 m)^{1/3}} < s`
between real numbers, for a real $`c` and natural numbers $`m`, $`s`.
:::

*Parsing.* The exponent of `m` is `c * Real.logb 2 m ^ (1 / 3 : ℝ)`. Function application binds
tighter than `^`, and `^` tighter than `*`, so this is $`c \cdot ((\log_2 m)^{1/3})`.
`Real.logb 2` is the logarithm to base two, and `(1 / 3 : ℝ)` is the real number $`1/3`: the
type ascription matters, since `1 / 3` in the natural numbers would be $`0`. Both `^` are
Mathlib's real power. The inequality is strict, as in “more than”.

*The shape of the bound.* For $`m \ge 2`,
$`m^{c(\log m)^{1/3}} = 2^{c(\log m)^{4/3}}`; this is {InlineLean.name}`Paper.thm_main_form`.
In terms of the number $`n = m^2` of variables it is $`2^{c' (\log n)^{4/3}}` with
$`c' = 2^{-4/3} c`. For every $`c > 0` the bound eventually exceeds every polynomial in $`m`;
{InlineLean.name}`Paper.exists_beyond_poly` states that for all $`m_0` and $`C` there is
$`m \ge m_0` at which it is at least $`m^C + C`, which is the form the separations use. It is
quasi-polynomial: it lies below $`2^{(\log m)^{C}}` for every $`C > 4/3` and all large $`m`. For
$`m \in \{0, 1\}` the expression degenerates (Mathlib has $`\log_2 0 = 0`), which again does not
matter.

# The main theorem

:::definition "Statement.MainTheorem" (lean := "Statement.MainTheorem") (parent := "part-claim")
*Reading (gloss).*
$$`\exists\, c > 0 \;\; \forall\, p \in \mathbb{N} \;\; \exists\, m_0 \;\; \forall\, F \text{ a field of characteristic } p \;\; \forall\, m \ge m_0 \;\; \forall\, s :`
if $`\mathrm{HC}_m` has a circuit with at most $`s` gates over $`F`, then
$`m^{c(\log_2 m)^{1/3}} < s`; and if $`p \neq 2` and $`\mathrm{PERM}_m` has a circuit with at
most $`s` gates over $`F`, then $`m^{c(\log_2 m)^{1/3}} < s`.

This is Theorem 1.1 of the paper (page 2), which the paper proves as Theorem M.3: “There is an
absolute constant $`c > 0` such that for every $`p`, zero or prime, there is $`m_0` with the
following property. Over every field of characteristic $`p` and for every $`m \geq m_0`, every
circuit for $`\mathrm{HC}_m`, and every circuit for $`\mathrm{PERM}_m` if $`p \neq 2`, has more
than $`m^{c(\log m)^{1/3}}` gates.”
:::

*The quantifiers.* Their order is the content, and it is the order of the printed theorem.

- $`c` is chosen first. It does not depend on the characteristic, the field or $`m`.
- $`m_0` is chosen after $`p` and before $`F`. It depends on the characteristic only, and is the
  same for all fields of that characteristic, in particular for all their extensions. It is not
  uniform over characteristics.
- $`F` ranges over all fields of characteristic $`p` in the universe `u`, and `u` is a universe
  variable of the file: the theorem `Solution.mainTheorem : MainTheorem.{u}` is polymorphic in
  it, so the statement holds for fields in every universe. The variables $`x_{i,j}` are indexed
  by a type in the lowest universe, which is no restriction.
- “Every circuit has more than $`B` gates” is written as “for every $`s`, if a circuit with at
  most $`s` gates exists then $`B < s`”. The two agree: apply the second to the size of the
  given circuit.
- $`p` ranges over all natural numbers. `CharP F p` is Mathlib's predicate that $`F` has
  characteristic $`p`; a field has characteristic zero or a prime, so for other $`p` the clause
  is vacuous and nothing is claimed.

*What the existential quantifiers hide.* Any fixed $`c > 0` gives a superpolynomial bound, so no
choice of $`c` makes the statement weak in kind. The Lean proof gives the value
$`c = 1/1600^2 \approx 3.9 \cdot 10^{-7}`: the proof of `Paper.thm_allfields` begins by supplying
it. The statement does not record it. For $`m_0` neither the paper nor the Lean proof gives a
value; the paper (page 8): “In the contracting case the constants, among them $`m_0`, depend on
the integer $`\mu`, for which the proof gives no value, and this is why Theorem 1.1 comes with no
value for $`m_0`.”

*What the statement does and does not separate.* It excludes circuits of polynomial size for
$`\mathrm{HC}_m` over every field and for $`\mathrm{PERM}_m` outside characteristic two. It does
not exclude circuits of quasi-polynomial size $`2^{(\log m)^{C}}` with $`C > 4/3`, so it says
nothing about whether these families lie in classes defined by quasi-polynomial size. The best
upper bounds are of the form $`2^{O(m)}` (page 1).

# Approximate circuits

:::definition "Statement.Approximates" (lean := "Statement.Approximates") (parent := "part-claim")
*Reading (gloss).* Let $`F` be a field, $`F(\!(\varepsilon)\!)` the field of formal Laurent
series over $`F`, and $`f \in F[x_v : v \in V]`. `Approximates f s` holds when there is a
polynomial $`q \in F(\!(\varepsilon)\!)[x_v : v \in V]` such that

- $`q` has a circuit with at most $`s` gates over $`F(\!(\varepsilon)\!)`, in the sense of
  `Computes`, and
- for every monomial $`x^d`, the coefficient $`q_d \in F(\!(\varepsilon)\!)` of $`q` has no term
  $`\varepsilon^i` with $`i < 0`, and its term with $`\varepsilon^0` is the coefficient $`f_d` of
  $`f`.

Equivalently $`q = f + \varepsilon g` with every coefficient of $`g` in
$`F[\![\varepsilon]\!]`. This is Definition 1.3 of the paper (page 2), repeated as Definition
N.1: “A circuit over $`\Bbbk(\!(\varepsilon)\!)` _approximates_ a polynomial $`f` over $`\Bbbk`
if it computes a polynomial of the form $`f + \varepsilon g`, where $`g` is a polynomial all of
whose coefficients lie in $`\Bbbk[\![\varepsilon]\!]`.”

This is the declaration with the respelled line; see
{ref "statement-spelling"}[the section on that line].
:::

*The encoding.* Mathlib's `LaurentSeries F` is the ring of Hahn series over $`F` with exponents
in $`\mathbb{Z}`, that is, of formal series $`\sum_{i \ge i_0} a_i \varepsilon^i`, and `a.coeff i`
is $`a_i`. The condition is stated for all $`i \le 0` at once: the coefficient at
$`\varepsilon^i` is $`f_d` if $`i = 0` and $`0` otherwise. The constants of the circuit are
arbitrary Laurent series, with no bound on the order of their poles, and the error $`g` is
unrestricted.

*Relation to border complexity as usually defined.* The algebraic definition in the literature
(background: Bürgisser, _The complexity of factors of multivariate polynomials_, 2004, as this
blueprint recalls it; the source was not consulted for this text) takes circuits over the field
$`F(\varepsilon)` of rational functions that compute a polynomial whose coefficients are defined
at $`\varepsilon = 0` and which equals $`f` there. The file takes Laurent series as constants
and requires the output to lie in $`f + \varepsilon F[\![\varepsilon]\!][x]`. For the
definition in the form just stated, the two give the same sizes, in the gate count of this file:

- A circuit over $`F(\varepsilon)` is a circuit over $`F(\!(\varepsilon)\!)`, since
  $`F(\varepsilon) \subset F(\!(\varepsilon)\!)`, and a rational function defined at $`0` is a
  power series. So approximation in the usual sense with $`s` gates gives `Approximates f s`.
  This direction is elementary and is not stated in Lean.
- Conversely, the development proves that the constants can be truncated:
  {InlineLean.name}`Nc.Approximates.exists_laurentPolynomial` states that an approximating
  circuit with at most $`s` gates gives a polynomial $`p` over the Laurent polynomials
  $`F[\varepsilon, \varepsilon^{-1}]` with a circuit with at most $`s` gates over that ring and
  the same condition on its coefficients, and
  {InlineLean.name}`Nc.Approximates.of_laurentPolynomial` is the converse. These are stated for
  the definition {InlineLean.name}`Nc.Approximates` of the proof, whose body is that of
  `Statement.Approximates` (with a type of variables in any universe); Lean accepts the one for
  the other, as the `example` below shows. Since
  $`F[\varepsilon, \varepsilon^{-1}] \subset F(\varepsilon)`, and a Laurent polynomial without
  negative powers is a polynomial in $`\varepsilon`, this is approximation in the usual sense
  with $`s` gates. The truncation is the first step of the paper's proof of Lemma N.2 (page 62):
  “We cut every constant off above $`\varepsilon^N` with $`N = 2^L \Delta`, where no constant
  contains a power of $`\varepsilon` below $`\varepsilon^{-\Delta}`. Since the output has degree
  at most $`2^L` in the constants, the cut changes it only in the positive powers of
  $`\varepsilon`.”

The second direction in one statement, which compiles against this build after
`import Comparator.VpVnp.Solution` and `open MvPolynomial` (it was compiled again for this
revision) and is not part of the repository:

```
example {F V : Type} [Field F] (f : MvPolynomial V F) (s : ℕ) :
    Statement.Approximates f s ↔
      ∃ p : MvPolynomial V (LaurentPolynomial F), Statement.Computes p s ∧
        ∀ (d : V →₀ ℕ) (i : ℤ), i ≤ 0 → (p.coeff d).coeff i = if i = 0 then f.coeff d else 0 :=
  ⟨fun h => Nc.Approximates.exists_laurentPolynomial h,
   fun ⟨_, hp, h⟩ => Nc.Approximates.of_laurentPolynomial hp h⟩
```

What is and is not established, then. Machine-checked in this build: `Approximates f s` is
equivalent to the existence of a circuit with at most $`s` gates over
$`F[\varepsilon, \varepsilon^{-1}]` whose output has coefficients in $`F[\varepsilon]` and
reduces to $`f` at $`\varepsilon = 0`. Not machine-checked, and elementary: that such a circuit
is one over $`F(\varepsilon)`, and that a circuit over $`F(\varepsilon)` with output defined at
$`0` is one over $`F(\!(\varepsilon)\!)` with output in $`F[\![\varepsilon]\!][x]`; both are
the transport of a circuit along an injective ring homomorphism, which keeps the number of
gates. Not checked at all: that the definition recalled above is, word for word, that of the
cited source. The argument covers every variant in which the constants come from a ring between
$`F[\varepsilon, \varepsilon^{-1}]` and $`F(\!(\varepsilon)\!)` and the output is required to
have coefficients without negative powers of $`\varepsilon` and to reduce to $`f` at
$`\varepsilon = 0`; for a variant with another size measure it gives the same sizes only up to
the factor discussed under `Computes`.

On the closure in a topology, the paper (page 62): “Over an algebraically closed field, $`f` is
approximated with $`L` gates if and only if it lies in the Zariski closure of the polynomials
that have circuits with $`L` gates \[Ald84, Bür04\], but we do not use this fact.” Neither the
file nor the Lean proof refers to a topology.

:::definition "Statement.MainTheoremApprox" (lean := "Statement.MainTheoremApprox") (parent := "part-claim")
*Reading (gloss).* `MainTheorem` word for word, with `Approximates` in place of `Computes`: with
the same quantifiers, every circuit that approximates $`\mathrm{HC}_m`, and every circuit that
approximates $`\mathrm{PERM}_m` if $`p \neq 2`, has more than $`m^{c(\log_2 m)^{1/3}}` gates.
This is the first sentence of Theorem 1.4 of the paper (page 2), proved there as the first
assertion of Theorem N.5.
:::

A circuit over $`F` is an approximating circuit with $`g = 0`, so the approximate form of the
bound contains the exact one for the same $`c` and $`m_0`. The constant of the Lean proof is
again $`1/1600^2`. The two statements quantify their constants separately.

# Valiant's classes

:::definition "Statement.Family" (lean := "Statement.Family") (parent := "part-claim")
*Reading (gloss).* A family $`(f_n)_{n \in \mathbb{N}}` over $`F`: for each $`n` a finite type
$`X_n` of variables and a polynomial $`f_n \in F[x_v : v \in X_n]`.
:::

The types $`X_n` lie in the lowest universe; the coefficients may lie in any. Nothing ties
$`|X_n|` to $`n`; the classes below bound it. There is no uniformity condition, as in the
literature.

:::definition "Statement.VP" (lean := "Statement.VP") (parent := "part-claim")
*Reading (gloss).* $`(f_n) \in \mathrm{VP}(F)` when there is $`a \in \mathbb{N}` such that for
every $`n`
$$`|X_n| \le n^a + a, \qquad \deg f_n \le n^a + a, \qquad f_n \text{ has a circuit with at most } n^a + a \text{ gates.}`
This is the definition of Section 1.3 of the paper (page 4): “A family $`(f_n)` of polynomials
over a field is in VP if the number of variables of $`f_n`, its degree, and the size of the
smallest circuit that computes it are all bounded by polynomials in $`n`.”
:::

*Comparison.* These are Valiant's families of polynomially bounded degree and complexity
(Valiant, 1979; Bürgisser, 2000).

- “At most $`n^a + a` for all $`n`, for some $`a`” is the same as “at most $`P(n)` for some
  polynomial $`P`”: a polynomial is below $`n^a` for large $`n` and a suitable $`a`, and the
  summand $`a` covers the finitely many remaining $`n`, among them $`n = 0` and $`n = 1`.
- The degree is `totalDegree`, the total degree of the polynomial $`f_n`, not the formal degree
  of a circuit. Definitions of VP through circuits of polynomially bounded formal degree give
  the same class, by homogenization.
- The bounds hold for every $`n`, not for all large $`n`; with the summand $`a` this is no
  stronger.

:::definition "Statement.VPBar" (lean := "Statement.VPBar") (parent := "part-claim")
*Reading (gloss).* $`(f_n) \in \overline{\mathrm{VP}}(F)` when there is $`a` such that for every
$`n`: $`|X_n| \le n^a + a`, $`\deg f_n \le n^a + a`, and $`f_n` is approximated by a circuit with
at most $`n^a + a` gates. This is the last sentence of Definition 1.3 of the paper (page 2): “The
class $`\overline{\mathrm{VP}}` is defined like VP, with approximating circuits in place of
circuits.”
:::

The bounds on variables and degree are on $`f_n`; the approximating polynomial
$`f_n + \varepsilon g` may have larger degree. This is the closure of VP in the algebraic sense
(Bürgisser, 2004), by the equivalence above. $`\mathrm{VP}(F) \subseteq \overline{\mathrm{VP}}(F)`,
with the same $`a` and $`g = 0`.

:::definition "Statement.VNP" (lean := "Statement.VNP") (parent := "part-claim")
*Reading (gloss).* $`(f_n) \in \mathrm{VNP}(F)` when there are a function
$`r : \mathbb{N} \to \mathbb{N}` and polynomials $`g_n` in the variables $`X_n` and $`r(n)`
further variables $`e_1, \ldots, e_{r(n)}` such that the family $`(g_n)`, with these variables,
is in $`\mathrm{VP}(F)`, and for every $`n`
$$`f_n(x) = \sum_{e \in \{0,1\}^{r(n)}} g_n(x, e)`
as polynomials in the variables $`X_n`. This is the definition of Section 1.3 of the paper
(page 4): “The family is in VNP if
$`f_n(x) = \sum_{e \in \{0,1\}^{r(n)}} g_n(x, e)` for some family $`(g_n)` in VP.”
:::

*The defining sum and its bounds.* `aeval (Sum.elim X fun i => if e i then 1 else 0)` substitutes
each variable of $`X_n` by itself and $`e_i` by $`1` or $`0`; the sum is over all functions
`e : Fin (r n) → Bool`, and the equation is one between polynomials over $`F`. No bound on
$`r(n)` or on $`f_n` is stated, and none is missing: membership of $`(g_n)` in VP gives
$`|X_n| + r(n) \le n^a + a`, so the number of summation variables and the number of variables of
$`f_n` are polynomially bounded, and $`\deg f_n \le \deg g_n \le n^a + a`. The family $`(g_n)` is
indexed by the same $`n` as $`(f_n)`.

*Comparison.* This is Valiant's class of p-definable families in the form that is now standard
(Valiant, 1979; Bürgisser, 2000). As in the literature, the definition is the same in every
characteristic.

# The separations

:::definition "Statement.Separation" (lean := "Statement.Separation") (parent := "part-claim")
*Reading (gloss).* For every field $`F` (in the universe `u`),
$`\mathrm{VP}(F) \subsetneq \mathrm{VNP}(F)`. Mathlib's `⊂` on sets is
$`\mathrm{VP}(F) \subseteq \mathrm{VNP}(F)` together with
$`\mathrm{VNP}(F) \not\subseteq \mathrm{VP}(F)`. This is Corollary 1.2 of the paper (page 2):
“Over every field, VP is a proper subset of VNP.”
:::

:::definition "Statement.SeparationClosure" (lean := "Statement.SeparationClosure") (parent := "part-claim")
*Reading (gloss).* For every field $`F` (in the universe `u`),
$`\mathrm{VNP}(F) \not\subseteq \overline{\mathrm{VP}}(F)`. This is the second sentence of
Theorem 1.4 of the paper (page 2): “In particular
$`\mathrm{VNP} \not\subseteq \overline{\mathrm{VP}}` over every field.”
:::

*Could the separations hold for a degenerate reason?* Three checks.

- If no polynomial had a circuit in the sense of `Computes`, both classes would be empty and
  `VP F ⊂ VNP F` would be false. A proof of `Separation` therefore exhibits a member of VNP.
- The member is the family $`(\mathrm{HC}_n)`, in both separations.
  {InlineLean.name}`Paper.hc_mem_VNP` states its membership in VNP; its proof takes
  $`r(n) = n^2` summation variables and the exponent $`a = 700` for $`(g_n)`. Its exclusion from
  VP and from the closure of VP is the main theorem in its two forms, at the sizes $`n^a + a`, by
  {InlineLean.name}`Paper.exists_beyond_poly`. So the separations are corollaries of the lower
  bounds, as in the paper, and by no other route.
- $`\mathrm{VP} \subseteq \mathrm{VNP}` holds with $`r = 0`
  ({InlineLean.name}`Paper.vp_subset_vnp`). `SeparationClosure` implies the second half of
  `Separation`, since $`\mathrm{VP} \subseteq \overline{\mathrm{VP}}`.

These theorems are stated for the families `Nc.Family` of the proof, which have the same fields
under other names; `Solution.lean` converts between the two (`Solution.toNc`, `Solution.ofNc`).

# The fifth theorem

`Statement.lean` states four propositions. The fifth judged theorem,
`Solution.permanent_over_real`, is stated in the challenge and solution files themselves, with
the definitions above:

```
theorem permanent_over_real : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ,
    Computes (perm ℝ m) s → Beyond c m s
```

It is Theorem L.1 of the paper (page 59), the statement of the abstract: the bound for the
permanent over Mathlib's real numbers. It is the case $`p = 0`, $`F = \mathbb{R}` of
`MainTheorem`, with constants of its own. {ref "chapter-claim"}[What is claimed] shows it beside
the printed theorem.

# What the file rests on

The meaning of the file depends on the Mathlib definitions it uses, and a kernel check takes them
as given. They are: `MvPolynomial`, with `X`, `C`, `coeff`, `totalDegree` and `aeval`;
`LaurentSeries`, which is `HahnSeries ℤ`, with its `coeff`; `Equiv.Perm` and
`Equiv.Perm.IsCycleOn`; `Real.logb` and the real power; `Field`, `CommSemiring` and `CharP`;
`Fintype.card`; `Set` with `⊆` and `⊂`; the sum type with `Sum.elim`; finitely supported
functions `V →₀ ℕ` as exponents of monomials; and the sums and products over finite types. The
readings above take
each in its documented meaning at Mathlib `v4.36.0`. Two of them deserve a second look from a
reader who audits the file: `IsCycleOn` on `Set.univ`, read above as “a single cycle through all
points”, and the indexing of `HahnSeries.coeff`, read as the coefficient of $`\varepsilon^i`.

# Summary for an audit

:::table +header
*
  * Notion
  * In the file
  * Standard?
  * If a variant, why equivalent
*
  * circuit
  * straight-line program over $`R` with gates $`x_v`, $`a \in R`, $`+`, $`\times` of fan-in two; equations between formal polynomials
  * yes
  * —
*
  * size
  * number of gates, variables and constants included
  * variant
  * within a factor three of the operation count (paper, footnote 2; elementary; not in Lean)
*
  * constants
  * any element of the field, one gate each
  * yes
  * —
*
  * $`\mathrm{PERM}_m`, $`\mathrm{HC}_m`
  * $`\sum_\sigma \prod_i x_{\sigma(i),i}`; the sum of $`\prod_i x_{i,\sigma(i)}` over the $`m`-cycles
  * yes
  * transposition, by $`\sigma \mapsto \sigma^{-1}`
*
  * bound
  * $`m^{c(\log_2 m)^{1/3}} < s`, with $`\exists c\, \forall p\, \exists m_0\, \forall F\, \forall m \ge m_0`
  * as printed
  * equal to $`2^{c(\log m)^{4/3}}` for $`m \ge 2` (`Paper.thm_main_form`)
*
  * VP
  * $`|X_n|`, $`\deg f_n` and circuit size at most $`n^a + a`
  * yes
  * $`n^a + a` for some $`a` is a polynomial bound
*
  * VNP
  * $`f_n = \sum_{e \in \{0,1\}^{r(n)}} g_n(x, e)` with $`(g_n) \in \mathrm{VP}`
  * yes
  * —
*
  * approximation
  * a circuit over $`F(\!(\varepsilon)\!)` computing $`f + \varepsilon g`, $`g \in F[\![\varepsilon]\!][x]`
  * variant of the form with constants in $`F(\varepsilon)`
  * truncation of the constants (`Nc.Approximates.exists_laurentPolynomial`) and $`F(\varepsilon) \subset F(\!(\varepsilon)\!)`
*
  * $`\overline{\mathrm{VP}}`
  * VP with approximating circuits
  * yes, the closure of VP in the algebraic sense
  * —
:::

The places where a statement of the file could be read as stronger than it is: $`m_0` depends on
the characteristic; the bound is quasi-polynomial, not exponential; $`c` and $`m_0` are not part
of the statement, and $`m_0` is not known. This reading found no class that is empty or
everything by accident, no existential constant that can be chosen trivially, and no exponent
computed in the natural numbers.

The next chapter, {ref "chapter-checking"}[How to check this yourself], says how a reader checks
that the proofs prove these statements.
