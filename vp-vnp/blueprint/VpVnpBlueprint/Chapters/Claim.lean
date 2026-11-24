/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import VpVnpBlueprint.Chapters.Statement
import VpVnpBlueprint.Chapters.Assembly
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

This chapter states the claim, exactly and once: the lower bound, its two consequences for
Valiant's classes, the five Lean theorems that express them, what the claim does not include, and
who or what has checked which part. The paper ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) states
the results in Section 1.1 (page 2) and proves them in its appendix; the Lean statements are
written with the definitions of `Statement.lean`, which
{ref "chapter-statement"}[The statement to trust] reads line by line.

# The claim in one screen

Arithmetic circuits are over a field $`\Bbbk`, with gates $`+` and $`\times` of fan-in two and
arbitrary constants from $`\Bbbk`; a circuit computes a polynomial as a formal expression, and its
size is the number of its gates, variables and constants included. Throughout, $`\log = \log_2`.
For an $`m \times m` matrix of variables,
$$`\mathrm{PERM}_m = \sum_{\sigma \in S_m} \prod_{i=1}^m x_{i,\sigma(i)}, \qquad \mathrm{HC}_m = \sum_{\sigma \text{ an } m\text{-cycle}} \; \prod_{i=1}^m x_{i,\sigma(i)}.`

*The lower bound.* There is $`c > 0` such that for every characteristic $`p` there is $`m_0`
such that, over every field of characteristic $`p` and for every $`m \ge m_0`,
$$`\text{every circuit for } \mathrm{HC}_m, \text{ and for } \mathrm{PERM}_m \text{ if } p \neq 2, \text{ has more than } m^{c(\log m)^{1/3}} = 2^{c(\log m)^{4/3}} \text{ gates.}`
The same holds for circuits over $`\Bbbk(\!(\varepsilon)\!)` that approximate these polynomials,
that is, compute $`f + \varepsilon g` with the coefficients of $`g` in $`\Bbbk[\![\varepsilon]\!]`.

*The consequences.* Over every field, $`\mathrm{VP} \subsetneq \mathrm{VNP}` and
$`\mathrm{VNP} \not\subseteq \overline{\mathrm{VP}}`.

*The quantifiers.* The constant $`c` is absolute: one value for all characteristics, fields and
$`m`. The threshold $`m_0` depends on the characteristic and on nothing else; it is the same for
all fields of one characteristic. The Lean proof takes $`c = 1/1600^2`; the statements only assert
that some $`c > 0` exists. No value of $`m_0` is known: the proof distinguishes two cases without
deciding between them, and in one of them the constants depend on an integer for which it gives
no value.

*The shape of the bound.* $`2^{c(\log m)^{4/3}}` exceeds every polynomial in $`m` and lies below
$`2^{(\log m)^{C}}` for every $`C > 4/3`. It separates VP from VNP. It does not show that the
permanent needs circuits of exponential size, nor that it has no circuits of quasi-polynomial
size. The paper (page 1): “Our lower bound is quasipolynomial, whereas the best upper bounds are
exponential – i.e. of the form $`2^{O(m)}`.”

*Not claimed.* Nothing about Boolean circuits, and nothing about P and NP.

*Status.* The paper's proof was found and written by AI models and formalized in Lean 4 by AI
models. In the build this site reports on, Lean's kernel accepted the five theorems below, and
by the README of the folder two further checkers each accepted them again. No human
mathematician has checked the proof, and no
tool or human has checked that the Lean statements say what the sentences above say.

Each of these points is made precise below.

# The five theorems

The five theorems of
{repoFile "vp-vnp/Comparator/VpVnp/Solution.lean"}[`Solution.lean`] are the ones a check of the
development judges: the challenge file states them without proof, importing only
`Statement.lean`, and the solution proves them. In each node below the left column is the
paper's statement, quoted, and the right column is the Lean theorem. A Lean statement that the
site marks as proved is proved; the quoted sentence is the paper's, and that the two say the same
is a reading, which the next chapter sets out.

:::theorem "Solution.mainTheorem" (lean := "Solution.mainTheorem") (parent := "part-claim")
*Theorem 1.1 of the paper* (main theorem; page 2), quoted: “There is an absolute constant
$`c > 0` such that for every $`p`, zero or prime, there is $`m_0` with the following property.
Over every field of characteristic $`p` and for every $`m \geq m_0`, every circuit for
$`\mathrm{HC}_m`, and every circuit for $`\mathrm{PERM}_m` if $`p \neq 2`, has more than
$`m^{c(\log m)^{1/3}}` gates.”

The paper proves it as Theorem M.3 (Appendix M, page 61). The type of the Lean theorem is
`Statement.MainTheorem`:
$`\exists c > 0\; \forall p\; \exists m_0\; \forall F\; \forall m \ge m_0\; \forall s`, with $`F`
a field of characteristic $`p`.
:::

:::proof "Solution.mainTheorem" (uses := "thm_allfields")
*The Lean proof* (read from `Solution.lean`). It takes the constant $`c` and, for $`p` zero or
prime, the threshold $`m_0` from `Paper.thm_allfields` ({bpref "thm_allfields"}[]), whose
statement is this one for such $`p`. For every other natural number $`p` it takes $`m_0 = 0`: no
field has characteristic $`p` (Mathlib's `CharP.char_is_prime_or_zero`), so nothing remains to
prove.
:::

The Lean statement quantifies over all natural numbers $`p`, where the paper has “zero or
prime”; for other $`p` no field has characteristic $`p`. It is stated for fields in an arbitrary
universe. It writes the permanent as $`\sum_\sigma \prod_i x_{\sigma(i),i}`, which is the same
polynomial. The paper's remarks on the theorem (page 2): “We do not claim that the exponent
$`1/3` is optimal. In characteristic two the permanent coincides with the determinant; since the
determinant has polynomial-size circuits, the theorem does not apply there.”

:::corollary "Solution.separation" (lean := "Solution.separation") (parent := "part-claim")
*Corollary 1.2 of the paper* (page 2), quoted: “Over every field, VP is a proper subset of VNP.”

The paper derives it from Theorem 1.1 (“As $`(\mathrm{PERM}_m)` and $`(\mathrm{HC}_m)` are in VNP,
Theorem 1.1 gives the following”) and proves it as Corollary M.4 (Appendix M, page 62). The type
of the Lean theorem is `Statement.Separation`.
:::

:::proof "Solution.separation" (uses := "cor_allclasses")
*The Lean proof* (read from `Solution.lean`). Both halves are those of `Paper.cor_allclasses`
({bpref "cor_allclasses"}[]), which is stated for the families `Nc.Family` of the development;
`Solution.toNc` and `Solution.ofNc` carry a family of `Statement.lean` to one of the development
and back, and Lean accepts membership in the one class for membership in the other.
:::

In the Lean proof the family that is in VNP and not in VP is $`(\mathrm{HC}_m)`, over every
field.

:::theorem "Solution.mainTheoremApprox" (lean := "Solution.mainTheoremApprox") (parent := "part-claim")
*Theorem 1.4 of the paper* (approximate computation; page 2), first sentence, quoted: “Theorem 1.1
holds for circuits that approximate $`\mathrm{HC}_m`, respectively $`\mathrm{PERM}_m`.”

Approximation is the paper's Definition 1.3 (page 2): “Let $`\Bbbk` be a field, and let
$`\Bbbk(\!(\varepsilon)\!)` be the field of formal Laurent series over $`\Bbbk`. A circuit over
$`\Bbbk(\!(\varepsilon)\!)` _approximates_ a polynomial $`f` over $`\Bbbk` if it computes a
polynomial of the form $`f + \varepsilon g`, where $`g` is a polynomial all of whose coefficients
lie in $`\Bbbk[\![\varepsilon]\!]`.” The paper proves the theorem as the first assertion of
Theorem N.5 (Appendix N, page 64). The type of the Lean theorem is `Statement.MainTheoremApprox`.
:::

:::proof "Solution.mainTheoremApprox" (uses := "thm_approx")
*The Lean proof* (read from `Solution.lean`). As for `Solution.mainTheorem`, from the first
conjunct of `Paper.thm_approx` ({bpref "thm_approx"}[]).
:::

The paper calls this approximation “in the sense of border complexity” (page 2).
{ref "chapter-statement"}[The statement to trust] compares the definition with the usual one,
which takes rational functions in $`\varepsilon` as constants, and gives the reason why the two
agree. The definition `Statement.Approximates` is the one declaration whose text in this build
differs from the printed file, in the spelling of a coefficient
({ref "statement-spelling"}[The one line this build spells differently]).

:::theorem "Solution.separationClosure" (lean := "Solution.separationClosure") (parent := "part-claim")
*Theorem 1.4 of the paper*, second sentence, quoted: “In particular
$`\mathrm{VNP} \not\subseteq \overline{\mathrm{VP}}` over every field.” Here, by Definition 1.3,
“the class $`\overline{\mathrm{VP}}` is defined like VP, with approximating circuits in place of
circuits.”

The paper proves it as the second assertion of Theorem N.5 (Appendix N, page 64). The type of the
Lean theorem is `Statement.SeparationClosure`.
:::

:::proof "Solution.separationClosure" (uses := "thm_approx")
*The Lean proof* (read from `Solution.lean`). The second conjunct of `Paper.thm_approx`
({bpref "thm_approx"}[]), with the conversion of families as for `Solution.separation`.
:::

:::theorem "Solution.permanent_over_real" (lean := "Solution.permanent_over_real") (parent := "part-claim")
*Theorem L.1 of the paper* (main theorem; Appendix L, page 59), quoted: “There are $`c > 0` and
$`m_0` such that for all $`m \geq m_0` every circuit over $`\mathbb{R}` that computes
$`\mathrm{PERM}_m` has more than $`m^{c(\log m)^{1/3}} = 2^{c(\log m)^{4/3}}` gates.”

This is the statement of the paper's abstract. The Lean statement is written in the challenge and
the solution themselves, with `Statement.Computes`, `Statement.perm` and `Statement.Beyond`; the
equality of the two forms of the bound is the separate theorem `Paper.thm_main_form`.
:::

:::proof "Solution.permanent_over_real" (uses := "thm_main")
*The Lean proof* (read from `Solution.lean`). The theorem is `Paper.thm_main`
({bpref "thm_main"}[]), whose statement Lean accepts for this one.
:::

The five are not independent as statements. The approximate bound contains the exact one, the
second separation contains the nontrivial half of the first, and the bound over $`\mathbb{R}` is
a case of Theorem 1.1. The development nevertheless proves each from the theorem of the appendix
that the paper names for it, and the Lean proofs differ in what they depend on: in this build,
`Solution.mainTheorem`, `Solution.separation` and `Solution.permanent_over_real` do not depend
on the three statements of Appendix N that carry the approximate case (Lemmas N.2 and N.3 and
Proposition N.4), and `Solution.mainTheoremApprox` and `Solution.separationClosure` do. (This
was read off, for this revision, from the constants on which each of the five theorems depends,
using the compiled dependency traversal in {repoFile "vp-vnp/scripts/InventoryKernel.lean"}[`InventoryKernel.lean`].)

# The quantifiers, the constant and the threshold

The order of quantifiers in `Statement.MainTheorem` and `Statement.MainTheoremApprox` is
$`\exists c\; \forall p\; \exists m_0\; \forall F`, as in the printed theorem.

- _The constant $`c`._ The statements assert that it exists. The Lean proofs of
  {InlineLean.name}`Paper.thm_allfields` and {InlineLean.name}`Paper.thm_approx` supply
  $`c = 1/1600^2`, the constant of the flat case (Theorem E.11, {bpref "thm_flat_rate"}[]). The
  other case gives a larger bound, $`2^{c'(\log m)^2/\log\log m}` (Theorem K.7,
  {bpref "thm_contracting"}[]), with a constant $`c' > 0` that depends on the field to which the
  dichotomy is applied, one algebraically closed field for each characteristic; the proof weakens
  it to the flat bound for large $`m` ({InlineLean.name}`Paper.thm_allfields_exceeds`). This is
  how one absolute constant serves all characteristics.
- _The threshold $`m_0`._ It depends on the characteristic $`p`. Within one characteristic it is
  uniform over all fields, because the proof transfers a circuit over any field of
  characteristic $`p` to one fixed algebraically closed field of that characteristic
  (Lemma M.1, {bpref "lem_transfer"}[]). It is not effective. The paper (page 8): “In the contracting case the constants,
  among them $`m_0`, depend on the integer $`\mu`, for which the proof gives no value, and this
  is why Theorem 1.1 comes with no value for $`m_0`.” And (page 6): “We do not know which of the
  two hypotheses holds, even over $`\mathbb{R}`, nor do we show that the two are mutually
  exclusive.”
- _The bound._ $`m^{c(\log m)^{1/3}} = 2^{c(\log m)^{4/3}}` for $`m \ge 2`. In the paper's words
  (page 1): “We produce a lower bound of $`2^{\Omega((\log m)^{4/3})}`, which is superpolynomial
  and thus separates VP from VNP.” With $`c = 1/1600^2` the exponent $`c(\log m)^{1/3}` of $`m`
  exceeds a given $`C` only when $`\log m > (1600^2 C)^3`; the statement is asymptotic in this
  sense as well as through $`m_0`.

# What is not claimed

*Boolean computation.* The paper's abstract (page 1): “This is the algebraic analogue of the
conjecture P $`\neq` NP, but it does not settle that conjecture. Algebraic circuits must work for
all inputs in the field and its extensions – not just 0 and 1 – thus our superpolynomial bound
does not apply to Boolean circuits.” And (page 4): “The results of this paper therefore say
nothing about whether NP-complete problems have fast algorithms.” On the relation between the two
questions the paper says (page 4): “it is not known whether Valiant's conjecture implies Boolean
separations such as P $`\neq` NP, while in the other direction a separation of Boolean circuit
classes is known to imply Valiant's conjecture over appropriate fields.”
{ref "chapter-overview"}[The shape of the proof] reports where, by the paper's account, the
argument stops for a circuit that is correct only on the inputs 0 and 1.

*Exponential bounds and quasi-polynomial size.* The bound is $`2^{\Theta((\log m)^{4/3})}` in
form. It is superpolynomial, which is what the separation of VP from VNP needs. It does not
exclude circuits of size $`2^{(\log m)^{C}}` for any $`C > 4/3`, so it does not separate VNP from
classes defined by quasi-polynomial circuit size. The paper (page 1): “Thus there is still plenty
of room to tighten the bounds.”

*The determinant, and characteristic two.* The bound for the permanent is claimed outside
characteristic two only; the bound for $`\mathrm{HC}_m` is claimed over every field.

*Determinantal complexity.* The paper draws a consequence for the determinantal complexity of the
permanent from Theorem 1.4 (Section 1.2 and Remark N.6). It is the one numbered statement with no
Lean counterpart. Section 3 (page 11): “Every numbered statement of this paper, in Sections 1 and
2 and in the appendix, has a Lean equivalent proved from Mathlib and the standard axioms, with one
exception: Remark N.6, the consequence for determinantal complexity that Section 1.2 draws from
Theorem 1.4.” Nothing on this site is evidence for it beyond the paper's prose.

*Barriers and derandomization.* The paper (page 3): “We have not analysed how it relates to
relativization and algebrization”, of the contracting case; and “Lower bounds for the permanent
have consequences for the derandomization of polynomial identity testing \[KI04\], but we have not
worked out what our bound gives there.”

*Constructive content.* The proof gives no value of $`m_0`, does not decide which of its two
cases holds, and uses functionals that exist by Zorn's lemma.
{ref "chapter-caveats"}[What a reader should keep in mind] collects these points.

# Provenance

The README of the folder {repoFile "vp-vnp"}[`vp-vnp`], quoted: “The result was discovered by an
internal research Claude model. This folder holds the paper and its Lean 4 formalization. Both
were written by AI models, and no human mathematician has checked the proof.” And: “Research
artifact. Not maintained and not accepting contributions.”

The paper, Section 3 (page 11), quoted: “The proofs in this paper were found and written by AI. No
human mathematician has checked the proofs.”

This blueprint is built from a branch of a fork of the repository, in which the development is
ported from Lean 4.33.1 to Lean 4.36.0 and the corresponding Mathlib. The port changed the
spelling of one coefficient in four statements, `Statement.Approximates` among them, and repaired
proofs; {repoFile "vp-vnp/PORTING.md"}[`PORTING.md`] lists every change. The blueprint's
exposition was written by AI models and has not been reviewed by a human mathematician either.

# Who or what has checked what

Four things could be checked, and they have been checked to different degrees.

*That the Lean proofs prove the Lean statements.* This is the part a machine checks.

- Lean's kernel, in the build of this branch: the development compiles, the only `sorry` are the
  five in the challenge file, which states the theorems without proof for the comparison, and
  `#print axioms` names `propext`, `Classical.choice` and `Quot.sound`, and no other axiom, for
  each of the five theorems.
- At the port baseline `9fd368ad`, the five theorems and their dependencies occupied
  61,815 declarations in a `leanexport` export. Both `con-leche --verified` and
  `con-ron --verified` accepted that export. The Project Stats page reports the replay
  performed for the site build a reader is viewing.
- The upstream development, on Lean 4.33.1, by the paper's account (Section Q.1, page 66):
  “Comparator accepted them against `Challenge.lean`, rechecking the proofs with Lean's kernel and
  with the independently written checker nanoda.” That run is the paper's; it was not repeated on
  this branch, whose README says of the corresponding script “not run on this branch”.

*That the Lean statements say what the paper claims.* No machine checks this, and no human has.
The README, quoted: “Lean checks the proofs, but no machine checks that this file says what is
claimed.” The paper (Section Q.1, page 66), quoted: “Whether the statements say what is meant was
judged only by AI readers. No human mathematician has checked the development, the statement file
or the proofs.” The file is `Statement.lean`, 98 lines, and
{ref "chapter-statement"}[The statement to trust] is this blueprint's reading of it, also by an
AI model. On this branch one more link belongs here: that the one respelled line means what the
printed line means, which is machine-checked in part and cited in part
({ref "statement-spelling"}[The one line this build spells differently]).

*That the printed proof is correct.* No human has checked it. The Lean proof does not check the
prose either: it proves Lean statements, by Lean proofs. For most of the paper the printed proof
and the Lean proof run in parallel; at four places the paper says that only the Lean proof is
complete (page 17), quoted: “The proofs of Proposition I.1, Theorem H.2(d), (e), Theorem J.3 and
Proposition N.4 describe machines and programs and account for their sizes and running times.
That these do exactly what is claimed can be verified only in the Lean development, and each of
these four statements is followed by a formalization note that says so. Consequently the
contracting case, and with it every main result, rests on Lean at these points.”

*That the intermediate Lean theorems are the paper's lemmas.* Appendix Q.3 of the paper (pages
66–70) lists where they differ. {ref "chapter-table3"}[The paper's statements and their Lean
names] gives a verdict for every numbered statement, and each chapter states the differences for
its own statements. These differences bear on how the paper can be used to read the Lean proof,
not on what the five theorems state.

{ref "chapter-checking"}[How to check this yourself] gives the commands for the first of the
four. For the second there are no commands; there is the file, and the next chapter.
