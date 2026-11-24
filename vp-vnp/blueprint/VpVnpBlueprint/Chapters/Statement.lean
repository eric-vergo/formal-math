/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import Statement

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

The file {repoFile "vp-vnp/Statement.lean"}[`Statement.lean`] states the results of the paper
using Mathlib alone: it imports `Mathlib` and nothing else, and the theorems of `Solution.lean`
prove its five statements. The paper prints it in Section 3 (pages 11–12) “so that a reader can
check that it correctly formalizes the statements in this paper”. Lean checks the proofs of these
statements; whether the statements mean what the paper's sentences mean is checked by no machine,
and this is the place to check it.

Below, every declaration of the file is shown in the order of the file, with its Lean source and
docstring on the right as the build compiled it. On the left is a reading of the definition in
standard notation. *These readings are this blueprint's gloss, not the paper's text, and no tool
has checked them against the Lean statement.* Where a reading points to the paper, it names the
passage that the definition is meant to formalize. The file begins:

```
import Mathlib

open MvPolynomial

universe u

namespace Statement
```

and ends with `end Statement`. Its module docstring reads “Definitions and statements, using
Mathlib only. The proofs are in Solution.lean.”

# The one line this build spells differently
%%%
tag := "statement-spelling"
%%%

*(Structure in place; the wording of this section is to be finalised.)* The file printed in the
paper (Section 3, page 12) and upstream's `Statement.lean` write, in `Statement.Approximates`:

```
    ∀ (d : V →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d q).coeff i = if i = 0 then coeff d f else 0
```

This build, on Mathlib `v4.36.0`, which has no function `MvPolynomial.coeff` any more, writes:

```
    ∀ (d : V →₀ ℕ) (i : ℤ), i ≤ 0 → (q.coeff d).coeff i = if i = 0 then f.coeff d else 0
```

No other line of the file differs. The file
{repoFile "vp-vnp/scripts/StatementSpelling.lean"}[`scripts/StatementSpelling.lean`] proves, in
this build, that `p.coeff d` is additive in `p`, takes the value `a` at `d` on the monomial
`monomial d a` and `0` at every other exponent, and is the only function with these two laws. That
upstream's `MvPolynomial.coeff` has the same two laws is cited from the Mathlib revision upstream
uses (its lemmas `MvPolynomial.coeff_add` and `MvPolynomial.coeff_monomial`), not checked by a
machine in the same build as this file. {repoFile "vp-vnp/PORTING.md"}[`PORTING.md`] gives the
argument and lists the three other statements of the development with the same change.

Every verdict of this site, and every mark on its nodes, is about the statements as this build
spells them.

# Circuits and the two polynomials

:::definition "Statement.Computes" (lean := "Statement.Computes") (parent := "part-claim")
*Reading (gloss).* For a commutative semiring $`R`, a type of variables $`V` and
$`f \in R[x_v : v \in V]`, `Computes f s` holds when there are polynomials
$`\ell_0, \ell_1, \ldots` in $`R[x_v : v \in V]` such that each $`\ell_k` with $`k < s` is a
variable $`x_v`, a constant $`a \in R`, or $`\ell_i + \ell_j` or $`\ell_i \cdot \ell_j` for some
$`i, j < k`, and $`f = \ell_k` for some $`k < s`. So `Computes f s` says that $`f` has an
arithmetic circuit with at most $`s` gates, variables and constants counted as gates: the model of
Section 1.3 of the paper (pages 3–4). The values $`\ell_k` for $`k \geq s` play no role.
:::

:::definition "Statement.perm" (lean := "Statement.perm") (parent := "part-claim")
*Reading (gloss).* `perm F m` is the polynomial in the $`m^2` variables $`x_{i,j}`,
$`(i, j) \in \{0, \ldots, m-1\}^2`,
$$`\sum_{\sigma \in S_m} \prod_{i} x_{\sigma(i), i} \;=\; \sum_{\sigma \in S_m} \prod_{i} x_{i, \sigma(i)},`
the two sums being equal by $`\sigma \mapsto \sigma^{-1}`; this is $`\mathrm{PERM}_m` of the
paper (page 1), over the coefficients `F`.
:::

:::definition "Statement.hc" (lean := "Statement.hc") (parent := "part-claim")
*Reading (gloss).* `hc F m` is $`\sum_{\sigma} \prod_{i} x_{i, \sigma(i)}`, the sum over the
permutations $`\sigma` of $`\{0, \ldots, m-1\}` that form a single cycle through all points
(Mathlib's `σ.IsCycleOn Set.univ`). For $`m \geq 1` these are the $`(m-1)!` cyclic permutations,
so this is $`\mathrm{HC}_m` of the paper (page 1).
:::

:::definition "Statement.Beyond" (lean := "Statement.Beyond") (parent := "part-claim")
*Reading (gloss).* `Beyond c m s` is the inequality $`m^{c (\log_2 m)^{1/3}} < s` between real
numbers, with Mathlib's real powers and `Real.logb 2` for $`\log_2`.
:::

# The main theorem

:::definition "Statement.MainTheorem" (lean := "Statement.MainTheorem") (parent := "part-claim")
*Reading (gloss).* There is $`c > 0` such that for every natural number $`p` there is $`m_0` such
that for every field $`F` of characteristic $`p` (in the universe `u`), every $`m \geq m_0` and
every $`s`: if $`\mathrm{HC}_m` over $`F` has a circuit with at most $`s` gates then
$`s > m^{c(\log_2 m)^{1/3}}`, and, if $`p \neq 2`, the same for $`\mathrm{PERM}_m`. Since
“a circuit with at most $`s` gates exists” implies “$`s` exceeds the bound” for every $`s`, every
circuit has more than $`m^{c(\log_2 m)^{1/3}}` gates. For $`p` neither zero nor prime there is no
field of characteristic $`p`, and the condition holds trivially. This is Theorem 1.1 of the paper
(page 2).
:::

# Approximate circuits

:::definition "Statement.Approximates" (lean := "Statement.Approximates") (parent := "part-claim")
*Reading (gloss).* For a field $`F` and $`f \in F[x_v : v \in V]`, `Approximates f s` holds when
some polynomial $`q` in the variables $`x_v`, $`v \in V`, with coefficients in the field
$`F((\varepsilon))` of Laurent series over $`F`, has a circuit with at most $`s` gates over $`F((\varepsilon))` and, for every monomial
$`d`, the coefficient of $`q` at $`d` has the coefficient of $`\varepsilon^0` equal to that of
$`f` at $`d` and no terms $`\varepsilon^i` with $`i < 0`. That is, $`q = f + \varepsilon g` with
every coefficient of $`g` in $`F[[\varepsilon]]`: Definition 1.3 of the paper (page 2).
This build spells one coefficient differently from the file printed in the paper; see
{ref "statement-spelling"}[the section on that line] above.
:::

:::definition "Statement.MainTheoremApprox" (lean := "Statement.MainTheoremApprox") (parent := "part-claim")
*Reading (gloss).* `MainTheorem` with `Approximates` in place of `Computes`: the bound for
circuits that approximate $`\mathrm{HC}_m`, and $`\mathrm{PERM}_m` when $`p \neq 2`. This is the
first sentence of Theorem 1.4 of the paper (page 2).
:::

# Valiant's classes

:::definition "Statement.Family" (lean := "Statement.Family") (parent := "part-claim")
*Reading (gloss).* A family of polynomials $`(f_n)_{n \in \mathbb{N}}` over $`F`: for each $`n`
a finite type of variables and a polynomial $`f_n` in them.
:::

:::definition "Statement.VP" (lean := "Statement.VP") (parent := "part-claim")
*Reading (gloss).* A family $`(f_n)` is in VP when there is $`a \in \mathbb{N}` such that for
every $`n` the number of variables of $`f_n`, its total degree, and the size of some circuit for
it are at most $`n^a + a`. This is the definition of Section 1.3 of the paper (page 4), with
“bounded by polynomials in $`n`” written as $`n^a + a`.
:::

:::definition "Statement.VPBar" (lean := "Statement.VPBar") (parent := "part-claim")
*Reading (gloss).* The same as VP with `Approximates` in place of `Computes`: the class
$`\overline{\mathrm{VP}}` of Definition 1.3 of the paper (page 2). The bounds on the number of
variables and on the degree are those of $`f_n` itself.
:::

:::definition "Statement.VNP" (lean := "Statement.VNP") (parent := "part-claim")
*Reading (gloss).* A family $`(f_n)` is in VNP when there are $`r : \mathbb{N} \to \mathbb{N}`
and polynomials $`g_n(x, e)` in the variables of $`f_n` and $`r(n)` further variables such that
$`(g_n)` is in VP and
$$`f_n(x) = \sum_{e \in \{0,1\}^{r(n)}} g_n(x, e)`
as polynomials, for every $`n`. That $`r(n)` is polynomially bounded follows from $`(g_n)` being
in VP, which bounds its number of variables. This is the definition of Section 1.3 of the paper
(page 4).
:::

:::definition "Statement.Separation" (lean := "Statement.Separation") (parent := "part-claim")
*Reading (gloss).* For every field $`F` (in the universe `u`), $`\mathrm{VP}(F) \subsetneq
\mathrm{VNP}(F)`: VP is contained in VNP and the two differ. This is Corollary 1.2 of the paper
(page 2).
:::

:::definition "Statement.SeparationClosure" (lean := "Statement.SeparationClosure") (parent := "part-claim")
*Reading (gloss).* For every field $`F` (in the universe `u`),
$`\mathrm{VNP}(F) \not\subseteq \overline{\mathrm{VP}}(F)`. This is the second sentence of
Theorem 1.4 of the paper (page 2).
:::
