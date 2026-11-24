/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import VpVnpBlueprint.Chapters.Statement
import Comparator.VpVnp.Solution

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "What is claimed" =>

%%%
tag := "chapter-claim"
file := "what-is-claimed"
htmlSplit := .never
number := false
%%%

The paper states its results in Section 1.1 (page 2) and proves them in its appendix. They are
quoted below, each beside the theorem of {repoFile "vp-vnp/Comparator/VpVnp/Solution.lean"}[`Solution.lean`] that
formalizes it; the Lean statements are written with the definitions of `Statement.lean`, which
{ref "chapter-statement"}[the next chapter] shows in full. Appendix Q of the paper (pages 66–70)
names the Lean counterpart of every numbered statement (Table 3) and lists where the text and the
Lean development differ (Section Q.3). In the paper, “here and throughout, $`\log = \log_2`”
(page 2).

The model, in the paper's words (Section 1.3, pages 3–4): “An _arithmetic circuit_ over a
commutative ring $`R` is a finite list of polynomials over $`R`, each of which is a variable, a
constant from $`R`, or the sum or the product of two earlier entries of the list, which may be the
same entry. We call the entries of the list the _gates_ of the circuit, and we say that the
circuit _computes_ each of the polynomials in the list. The size of the circuit is the length of
the list, so that variables and constants are counted as gates.” For an $`m \times m` matrix of
variables $`x_{i,j}`, the paper's polynomials are (page 1)
$$`\mathrm{PERM}_m = \sum_{\sigma \in S_m} \prod_{i=1}^m x_{i,\sigma(i)} \quad\text{and}\quad \mathrm{HC}_m = \sum_{\sigma} \prod_{i=1}^m x_{i,\sigma(i)},`
“where $`S_m` is the symmetric group of size $`m!` and the second sum runs over the $`(m-1)!`
cyclic permutations in $`S_m`.”

# The five theorems

:::theorem "Solution.mainTheorem" (lean := "Solution.mainTheorem") (parent := "part-claim")
*Theorem 1.1 of the paper* (main theorem; page 2), quoted: “There is an absolute constant
$`c > 0` such that for every $`p`, zero or prime, there is $`m_0` with the following property.
Over every field of characteristic $`p` and for every $`m \geq m_0`, every circuit for
$`\mathrm{HC}_m`, and every circuit for $`\mathrm{PERM}_m` if $`p \neq 2`, has more than
$`m^{c(\log m)^{1/3}}` gates.”

The paper proves it as Theorem M.3 (Appendix M, page 61). The Lean statement is
`Statement.MainTheorem`.
:::

:::corollary "Solution.separation" (lean := "Solution.separation") (parent := "part-claim")
*Corollary 1.2 of the paper* (page 2), quoted: “Over every field, VP is a proper subset of VNP.”

The paper derives it from Theorem 1.1 (“As $`(\mathrm{PERM}_m)` and $`(\mathrm{HC}_m)` are in VNP,
Theorem 1.1 gives the following”) and proves it as Corollary M.4 (Appendix M, page 62). The Lean
statement is `Statement.Separation`.
:::

:::theorem "Solution.mainTheoremApprox" (lean := "Solution.mainTheoremApprox") (parent := "part-claim")
*Theorem 1.4 of the paper* (approximate computation; page 2), first sentence, quoted: “Theorem 1.1
holds for circuits that approximate $`\mathrm{HC}_m`, respectively $`\mathrm{PERM}_m`.”

Approximation is the paper's Definition 1.3 (page 2): “Let $`\Bbbk` be a field, and let
$`\Bbbk((\varepsilon))` be the field of formal Laurent series over $`\Bbbk`. A circuit over
$`\Bbbk((\varepsilon))` _approximates_ a polynomial $`f` over $`\Bbbk` if it computes a polynomial
of the form $`f + \varepsilon g`, where $`g` is a polynomial all of whose coefficients lie in
$`\Bbbk[[\varepsilon]]`.” The paper proves the theorem as the first assertion of Theorem N.5
(Appendix N, page 64). The Lean statement is `Statement.MainTheoremApprox`.
:::

:::theorem "Solution.separationClosure" (lean := "Solution.separationClosure") (parent := "part-claim")
*Theorem 1.4 of the paper*, second sentence, quoted: “In particular
$`\mathrm{VNP} \not\subseteq \overline{\mathrm{VP}}` over every field.” Here, by Definition 1.3,
“the class $`\overline{\mathrm{VP}}` is defined like VP, with approximating circuits in place of
circuits.”

The paper proves it as the second assertion of Theorem N.5 (Appendix N, page 64). The Lean
statement is `Statement.SeparationClosure`.
:::

:::theorem "Solution.permanent_over_real" (lean := "Solution.permanent_over_real") (parent := "part-claim")
*Theorem L.1 of the paper* (main theorem; Appendix L, page 59), quoted: “There are $`c > 0` and
$`m_0` such that for all $`m \geq m_0` every circuit over $`\mathbb{R}` that computes
$`\mathrm{PERM}_m` has more than $`m^{c(\log m)^{1/3}} = 2^{c(\log m)^{4/3}}` gates.”

This is the statement of the paper's abstract for the real numbers. Its Lean statement is written
in `Solution.lean` itself, with `Statement.Computes`, `Statement.perm` and `Statement.Beyond`.
:::

The theorems of `Solution.lean` are stated for a universe variable `u` and so hold for fields in
every universe. Section Q.3 of the paper says how the theorems with prefix `Paper.`, which state
the numbered statements of the appendix, are restricted to the lowest universe, and that “the
theorems of Solution hold for fields in every universe” (page 66).

# What is not claimed

The paper's abstract (page 1), quoted: “This is the algebraic analogue of the conjecture
P $`\neq` NP, but it does not settle that conjecture. Algebraic circuits must work for all inputs
in the field and its extensions – not just 0 and 1 – thus our superpolynomial bound does not apply
to Boolean circuits.”

From Section 1 (page 1): “In this paper, we resolve the latter problem, but not the former”, the
former being P vs NP and the latter VP vs VNP; and (page 2) “We do not claim that the exponent
$`1/3` is optimal. In characteristic two the permanent coincides with the determinant; since the
determinant has polynomial-size circuits, the theorem does not apply there.” On the size of the
bound (page 1): “We produce a lower bound of $`2^{\Omega((\log m)^{4/3})}`, which is
superpolynomial and thus separates VP from VNP. Our lower bound is quasipolynomial, whereas the
best upper bounds are exponential – i.e. of the form $`2^{O(m)}`.”

One numbered statement of the paper has no Lean counterpart. Section 3 (page 11), quoted: “Every
numbered statement of this paper, in Sections 1 and 2 and in the appendix, has a Lean equivalent
proved from Mathlib and the standard axioms, with one exception: Remark N.6, the consequence for
determinantal complexity that Section 1.2 draws from Theorem 1.4.”

# Who has checked what

Section 3 of the paper (page 11), quoted: “The proofs in this paper were found and written by AI.
No human mathematician has checked the proofs.” Section Q.1 (page 66), quoted: “Whether the
statements say what is meant was judged only by AI readers. No human mathematician has checked
the development, the statement file or the proofs.”

The paper says that some of its printed proofs are complete only in Lean (page 17), quoted: “The
proofs of Proposition I.1, Theorem H.2(d), (e), Theorem J.3 and Proposition N.4 describe machines
and programs and account for their sizes and running times. That these do exactly what is claimed
can be verified only in the Lean development, and each of these four statements is followed by a
formalization note that says so. Consequently the contracting case, and with it every main
result, rests on Lean at these points.”

A check of the Lean proofs, by Lean's kernel or by the other checkers that
{ref "chapter-checking"}[How to check this yourself] describes, establishes that each Lean
statement follows from Mathlib and Lean's axioms. It does not establish that the Lean statements
say what the paper's sentences say. The README of the folder, quoted: “Lean checks the proofs,
but no machine checks that this file says what is claimed.” That file is `Statement.lean`, and
{ref "chapter-statement"}[the next chapter] shows it, so that a reader can make that comparison.
