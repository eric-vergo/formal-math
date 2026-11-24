/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import VpVnpBlueprint.Chapters.Claim
import VpVnpBlueprint.Chapters.Accelerators
import Paper.Approximate

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "All fields and approximate computation" =>

%%%
tag := "chapter-assembly"
file := "assembly"
htmlSplit := .never
number := false
%%%

This chapter follows Appendices L (pages 59–60), M (pages 60–62) and N (pages 62–64) of the paper
({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]). It combines the lower bound of the flat case
({ref "chapter-flat"}[The flat case]) and that of the contracting case
({ref "chapter-accelerators"}[Accelerators and the diagonal argument]) through the dichotomy
({ref "chapter-dichotomy"}[The two cases]) into the theorems of
{ref "chapter-claim"}[What is claimed]: first over $`\mathbb{R}` (Appendix L), then over every field
with a constant that does not depend on the field (Appendix M), then for approximating circuits
(Appendix N). Nothing new about circuits happens here. What the chapter has to settle is
quantifiers: which constants depend on what, how a bound proved over one field in each
characteristic becomes a bound over all fields, and how the theorems with prefix `Paper.` become
the five judged theorems.

The deduction of Theorem L.1 is among the printed proofs that the paper calls “meant to be
complete, if terse” (page 17). For Appendices M and N the paper makes no such claim; their printed
proofs are short and the Lean statements beside the nodes are what is proved. Paragraphs marked
*Reading (gloss)* are this blueprint's readings of the Lean code, checked by no tool.

Two statements of these appendices are in other chapters: Proposition M.2 (sums over bits as
Hamiltonian cycle polynomials) in {ref "chapter-completeness"}[Completeness gadgets], and Lemma N.3
(sums with few terms, approximate version) in {ref "chapter-flat"}[The flat case]. Proposition N.4
is in {ref "chapter-accelerators"}[the previous chapter].

# L. Proofs of the main theorems over the real numbers

The paper (page 59): “Sections A to K work over the real numbers, and this section proves the
following three statements over $`\mathbb{R}`.” And (page 59): “The flat case was treated in Section
E and the contracting case in Sections F to K, and by Theorem D.2 at least one of them occurs.”

:::theorem "thm_main" (lean := "Paper.thm_main, Paper.thm_main_form, Paper.thm_main_calculation") (parent := "part-assembly")
*Theorem L.1 of the paper* (main theorem; page 59), quoted: “There are $`c > 0` and $`m_0` such that
for all $`m \geq m_0` every circuit over $`\mathbb{R}` that computes $`\mathrm{PERM}_m` has more than
$$`m^{c(\log m)^{1/3}} = 2^{c(\log m)^{4/3}}`
gates.”

`Paper.thm_main` states the bound in the first form for the polynomial
$`\sum_\sigma \prod_i x_{\sigma(i), i}` over `ℝ`; `Paper.thm_main_form` is the displayed equality,
for $`m \geq 2` and every real $`c`. The judged theorem
{bpref "Solution.permanent_over_real"}[] is `Paper.thm_main` itself.
:::

:::proof "thm_main"
*The paper's proof* (page 60), quoted: “By Theorem D.2 we are in the flat case or in the
contracting case. In the flat case Theorem E.11 gives the bound $`2^{c''(\log m)^{4/3}}` for all
large $`m`, with an explicit constant $`c'' > 0`. In the contracting case Theorem K.7 gives the
bound $`2^{c'(\log m)^2/\log\log m}` for some $`c' > 0` and all large $`m`, and
$`(\log m)^2/\log\log m \geq (\log m)^{4/3}` for large $`m`. Hence the smaller of $`c'` and $`c''`
serves as the constant $`c` of the theorem.”

*Reading (gloss).* The Lean proof splits on `thm_alt ℝ`. In the flat case it takes
$`c = 1/1600^2` from `thm_flat_rate`; in the contracting case it takes the constant of
{bpref "thm_contracting"}[] and `thm_main_calculation 1`. So the constant of `thm_main` is
$`1/1600^2` or the unspecified constant of the contracting case, according to which case holds for
$`\mathbb{R}`; this is the paper's “the smaller of $`c'` and $`c''`” in each branch.
`thm_main_calculation` is the inequality in a stronger form: for every real $`C`,
$`C(\log m)^{4/3} \leq (\log m)^2/\log\log m` for all large $`m`.
:::

:::theorem "thm_simple" (lean := "Paper.thm_simple") (parent := "part-assembly")
*Theorem L.2 of the paper* (no circuits of polynomial size; page 59), quoted: “For every integer
$`C \geq 0` there is $`m_0` such that for all $`m \geq m_0` no circuit over $`\mathbb{R}` with at
most $`m^C` gates computes $`\mathrm{PERM}_m`.”

Section Q.3 (page 66) lists Theorem L.2 and Corollary L.3 among the statements that are not on the
route of the theorems of `Solution`.
:::

:::proof "thm_simple"
*The paper's proofs* (page 60). First: “Theorem L.2 follows at once from Theorem L.1, since
$`m^{c(\log m)^{1/3}}` exceeds $`m^C` for large $`m`.” Then a direct proof that “uses of Section E
only the part that precedes Section E.4”: “In the flat case the claim is Theorem E.6. In the
contracting case it follows from Theorem K.7, whose bound exceeds $`m^C` for large $`m`.”

The Lean proof is the direct one: `thm_flat_simple` in the flat case, and `thm_contracting` with
`thm_main_calculation` in the contracting case. It does not use `thm_main`.
:::

:::corollary "cor_classes" (lean := "Paper.cor_classes, Paper.vp_subset_vnp") (parent := "part-assembly")
*Corollary L.3 of the paper* (page 59), quoted: “Over $`\mathbb{R}`, VP is a proper subset of VNP.”

`Paper.vp_subset_vnp` is the inclusion over every commutative semiring, in every universe.
:::

:::proof "cor_classes"
*The paper's proof* (page 60), quoted: “The inclusion $`\mathrm{VP} \subseteq \mathrm{VNP}` is the
case $`r(n) = 0` of the definition. By Ryser's formula” (the paper cites Rys63 and Gly10) “
$$`\mathrm{PERM}_m = (-1)^m \sum_{e \in \{0,1\}^m} \prod_{j=1}^m (1 - 2e_j) \prod_{i=1}^m \sum_{j=1}^m e_j x_{ij}.`
The summand is a polynomial in the $`x_{ij}` and the $`e_j` of degree at most $`3m` that has a
circuit of size polynomial in $`m`, so the family $`(\mathrm{PERM}_m)` is in VNP. By Theorem L.2 it
is not in VP.”

In Lean the membership is `Paper.perm_mem_VNP` (with the bound $`n^{700} + 700` in the definition
of VP), and the lower bound used is `thm_simple (C + 1)`.
:::

The paper's remarks after these proofs (page 60): “The constant $`m_0` in our theorems is not
effective, and we do not claim that the exponent $`1/3` is optimal. We do not know whether we are
in the flat case or in the contracting case, and we have not shown that the two cases exclude each
other (see the end of Section D). To make $`m_0` effective along the lines of this proof we would
have to decide which case holds, and in the contracting case we would also need values for the
numbers $`\mu` and $`s` of Definition D.1, which the proof of Theorem D.2 does not provide.” And:
“The exponent $`1/3` comes from the flat case alone, since the contracting case gives the stronger
bound of Theorem K.7.”

# M. All fields

The paper (page 60): “Sections A to L use nothing about $`\Bbbk` except that it is a field, apart
from the element $`\tfrac12` in Proposition E.1, and for uniform constants we apply them to a single
field in each characteristic. Since the permanent is the determinant in characteristic two, we also
treat the Hamiltonian cycle polynomial $`\mathrm{HC}_M`, for which Proposition M.2 replaces
Proposition E.1 and needs no $`\tfrac12`.”

:::lemma_ "lem_transfer" (lean := "Paper.lem_transfer, Paper.exists_closed") (parent := "part-assembly")
*Lemma M.1 of the paper* (circuits with constants in $`\mathbb{K}`; page 60), quoted, with its
preamble: “Let $`p` be zero or a prime, and let $`\mathbb{K}` be the algebraic closure of the prime
field of characteristic $`p`.” “Let $`f` be a polynomial with integer coefficients. If $`f` has a
circuit with $`L` gates over some field of characteristic $`p`, then it has a circuit with $`L` gates
over $`\mathbb{K}`.”

Section Q.3 (page 68): “Lemmas M.1 and N.2 are proved with any algebraically closed field of
characteristic $`p` in the place of $`\mathbb{K}`.” In the Lean statement `q` is a polynomial over
`ℤ`, in any type of variables, and “$`f` over a field” is its image `MvPolynomial.map
(Int.castRingHom F) q`. The given field `F` may lie in any universe (`F : Type*`), and the target
`KK` is in the lowest (`KK : Type`). `Paper.exists_closed` provides, for $`p` zero or prime, an
algebraically closed field of characteristic $`p` in the lowest universe: Mathlib's algebraic
closure of `ℚ` or of `ZMod p`.
:::

:::proof "lem_transfer"
*The paper's proof* (page 60), quoted: “We embed the given field into an algebraically closed
field, which contains a copy of $`\mathbb{K}`, and adjoin the constants of the circuit to this copy.
That the circuit computes $`f` is an identity in the resulting finitely generated
$`\mathbb{K}`-algebra, and we reduce it modulo a maximal ideal, whose residue field is $`\mathbb{K}`
by the Nullstellensatz.”

*Reading (gloss).* The Lean proof has these steps: a common extension `T` of `F` and `KK`
(`exists_common_ring`); the circuit mapped to `T`; a subalgebra `A` of `T` over `KK` that contains
the finitely many constants of the circuit and has a homomorphism `ψ` to `KK`
(`exists_specialisation`); the gates lifted to `A` (`exists_lift_steps`); and the circuit mapped
along `ψ`. The polynomial computed is unchanged because it has integer coefficients and there is
only one ring homomorphism from `ℤ` to a ring. The number of gates is the same at every step.
:::

:::theorem "thm_allfields" (lean := "Paper.thm_allfields, Paper.thm_allfields_exceeds, Paper.beyond_of_rate, Paper.flat_rate_hc, Paper.contracting_hc") (parent := "part-assembly")
*Theorem M.3 of the paper* (lower bound over all fields; page 61; the same text as Theorem 1.1,
page 2), quoted: “There is an absolute constant $`c > 0` such that for every $`p`, zero or prime,
there is $`m_0` with the following property. Over every field of characteristic $`p` and for every
$`m \geq m_0`, every circuit for $`\mathrm{HC}_m`, and every circuit for $`\mathrm{PERM}_m` if
$`p \neq 2`, has more than $`m^{c(\log m)^{1/3}}` gates.”

The Lean statement has this form, with “every circuit has more than $`b` gates” written as “for
every $`s`, if some circuit with at most $`s` gates computes the polynomial then $`b < s`”. The
field `F` is in an arbitrary universe `u`. The constant is explicit in the proof:
$`c = 1/1600^2`, the constant of Theorem E.11.
:::

:::proof "thm_allfields"
*The paper's proof* (pages 61–62), quoted: “By Lemma M.1 it suffices to consider circuits over
$`\mathbb{K}`, where Theorem D.2 gives the flat or the contracting case, depending on $`p`. The
constant of Theorem E.11 in the flat case is absolute, and the bound of Theorem K.7 in the
contracting case, although its constant depends on $`p`, exceeds that of the flat case for all
large $`m`, as in the proof of Theorem L.1. For $`\mathrm{HC}_m`, Proposition M.2 replaces
Proposition E.1, which enters through Corollary E.2 in Lemmas E.3 and K.3. There the factor 3
becomes 40, and the proofs only used that $`3k^3\ell\, 2^{k\ell} \leq 2^{2k\ell}` for large values of
the parameters.”

*Reading (gloss): the quantifiers in the Lean proof.*

1. The constant $`c = 1/1600^2` is fixed first, before $`p`.
2. For $`p` zero or prime, `exists_closed` gives one algebraically closed field `K` of
   characteristic $`p` in the lowest universe. Everything from Appendix A to Appendix K is applied
   to this one field.
3. For the Hamiltonian cycle polynomial over `K`: `thm_alt K` gives `Flat K` or `Contracting K`. In
   the flat case `flat_rate_hc` gives $`2^{(\log m)^{4/3}/1600^2} < s` for $`m \geq M_1`, from the
   flat bound for families complete for grid sums with factor 40. In the contracting case
   `contracting_hc` gives $`2^{c'(\log m)^2/\log\log m} < s` with some $`c' > 0`, and
   `thm_allfields_exceeds` converts this into the *same* bound $`2^{(\log m)^{4/3}/1600^2} < s` for
   all large $`m`: by `thm_main_calculation` with $`C = 1/(c' \cdot 1600^2)`,
   $`(\log m)^{4/3}/1600^2 \leq c'(\log m)^2/\log\log m` eventually. So in both cases the bound over
   `K` has the constant $`1/1600^2`, and only the threshold $`M_1` depends on the case and on $`c'`.
4. For the permanent, if $`p \neq 2`: the same with `thm_flat_rate` and `thm_contracting`, which
   need $`2 \neq 0` in `K`; threshold $`M_2`.
5. $`m_0 = M_1 + M_2 + 2`. For a field `F` of characteristic $`p` in any universe, a circuit for
   $`\mathrm{HC}_m` or $`\mathrm{PERM}_m` over `F` gives one with the same number of gates over `K`
   by `lem_transfer`, applied to the polynomial with integer coefficients (`genHC ℤ m`,
   `Paper.permInt m`). `beyond_of_rate` rewrites $`2^{(\log m)^{4/3}/1600^2}` as
   $`m^{(1/1600^2)(\log m)^{1/3}}` for $`m \geq 2`.

So the dependence is: $`c` on nothing; $`m_0` on $`p`, through which of the two cases holds for
`K`, through the threshold of that case, and in the contracting case through the constant $`c'`,
of which nothing is known. The step from the contracting bound to the flat bound costs nothing in
the constant because $`(\log m)^2/\log\log m` grows faster than every multiple of
$`(\log m)^{4/3}`; it is paid for in $`m_0`. The proof does not determine which case holds for any
`K`, and $`m_0` is not effective, as the paper says (page 60, quoted above).

*Universes.* Section Q.3 (page 66): “The theorems with prefix `Paper.` are stated for fields in the
lowest universe, and so are their rings, algebras, groups, spaces, point sets and index sets. The
exception is the given field in Theorems M.3 and N.5, Corollary M.4, Definition N.1 and Lemmas M.1
and N.2, which may lie in any universe.” The bridge is step 5: `lem_transfer` takes a field in any
universe to the field `K` in the lowest one, and nothing else of the proof ever sees `F`. The
reduction that makes the constant uniform over the fields of one characteristic is thus also what
makes the theorem hold in every universe.
:::

:::corollary "cor_allclasses" (lean := "Paper.cor_allclasses, Paper.exists_beyond_poly") (parent := "part-assembly")
*Corollary M.4 of the paper* (page 62; the same text as Corollary 1.2, page 2), quoted: “Over every
field, VP is a proper subset of VNP.”

In Lean, `VP F ⊂ VNP F` for the classes `Nc.VP`, `Nc.VNP` of the development and a field `F` in any
universe.
:::

:::proof "cor_allclasses"
*The paper's proof* (page 62), quoted: “The family $`(\mathrm{HC}_m)` is in VNP” (the paper cites
Val79), “as one sees by summing over one-hot codes of the places that the vertices take on the
cycle, with vertex 1 at place 1. By Theorem M.3 it is not in VP.”

*Reading (gloss).* The inclusion is `vp_subset_vnp`. For properness: `Paper.hc_mem_VNP` puts
$`(\mathrm{HC}_n)` in VNP, with $`r(n) = n^2` summation variables and the bound $`n^{700} + 700`. If
it were in VP with exponent $`C`, then for the characteristic $`p` of `F` and the $`m_0` of
`thm_allfields`, `exists_beyond_poly` gives some $`m \geq m_0` at which
$`m^{c(\log m)^{1/3}} < m^C + C` fails, against the lower bound applied to the circuit with
$`m^C + C` gates. The witness of the separation is thus the Hamiltonian cycle polynomial over
every field, also where the permanent would do.
:::

# N. Approximate computation

The paper (page 62): “In this appendix we extend Theorem M.3 to circuits that only approximate the
polynomial, in the sense of border complexity (Theorem N.5), so that VNP is not contained in the
closure $`\overline{\mathrm{VP}}` of VP. We first reduce to constants that are Laurent polynomials in
a formal variable $`\varepsilon` over $`\mathbb{K}`, and in the flat case we then only have to adapt
Lemma E.7.”

:::definition "def_approx" (lean := "Paper.def_approx, Paper.VPBar") (parent := "part-assembly")
*Definition N.1 of the paper* (page 62; Definition 1.3, page 2, without its third sentence),
quoted: “Let $`\Bbbk` be a field, and let $`\Bbbk((\varepsilon))` be the field of formal Laurent
series over $`\Bbbk`. A circuit over $`\Bbbk((\varepsilon))` *approximates* a polynomial $`f` over
$`\Bbbk` if it computes a polynomial of the form $`f + \varepsilon g`, where $`g` is a polynomial
all of whose coefficients lie in $`\Bbbk[[\varepsilon]]`. We then fix one such polynomial and call
it the *output* of the circuit. The class $`\overline{\mathrm{VP}}` is defined like VP, with
approximating circuits in place of circuits.”

Section Q.3 (page 69): “The theorem `def_approx` states when a circuit approximates a polynomial,
as in the second sentence of Definition N.1; the last sentence of the definition is the definition
of `Paper.VPBar`, and the match rests on reading it.” `Paper.def_approx` is an equivalence between
`Nc.Approximates f s` and the existence of a polynomial `p` over the Laurent series with a circuit
of at most `s` gates such that, for every monomial `d`, the coefficient of `p` at `d` has no term
$`\varepsilon^i` with $`i < 0` and has the coefficient of `f` at `d` as its term at
$`\varepsilon^0`. `Paper.VPBar` repeats the definition of VP with `Approximates` for `Computes`.

*The respelled line.* The coefficient of `p` at `d` is written `p.coeff d` in this build, where the
paper's file and upstream write `coeff d p`; `Paper.def_approx` is one of the three statements of
the development, besides `Statement.Approximates`, with this change. See
{ref "statement-spelling"}[The one line this build spells differently] and
{repoFile "vp-vnp/PORTING.md"}[`PORTING.md`].
:::

The paper adds (page 62): “Over an algebraically closed field, $`f` is approximated with $`L` gates
if and only if it lies in the Zariski closure of the polynomials that have circuits with $`L`
gates” (it cites Ald84 and Bür04), “but we do not use this fact.” The Lean development does not
state it.

:::lemma_ "lem_transfer_approx" (lean := "Paper.lem_transfer_approx") (parent := "part-assembly")
*Lemma N.2 of the paper* (constants that are Laurent polynomials; page 62), quoted: “Let $`f` be a
polynomial with integer coefficients, and let $`\Bbbk` be a field of characteristic $`p`. If a
circuit with $`L` gates over $`\Bbbk((\varepsilon))` approximates $`f`, then some circuit with $`L`
gates over the ring $`\mathbb{K}[\varepsilon, \varepsilon^{-1}]` computes a polynomial that lies in
$`f + \varepsilon\,\mathbb{K}[\varepsilon][x]`.”

As for Lemma M.1, the Lean statement has any algebraically closed field `KK` of characteristic
$`p` in the lowest universe for $`\mathbb{K}`, and a field `F` in any universe (Section Q.3, page
68, quoted under Lemma M.1). Its conclusion is a polynomial `P` over `LaurentPolynomial KK` with a
circuit of at most `s` gates whose coefficients have no negative powers of $`\varepsilon` and have
the coefficients of $`f` at $`\varepsilon^0`. This is one of the statements whose coefficient is
spelled `P.coeff d` in this build ({ref "statement-spelling"}[the section on that line]).
:::

:::proof "lem_transfer_approx"
*The paper's proof* (page 62), quoted: “We cut every constant off above $`\varepsilon^N` with
$`N = 2^L\Delta`, where no constant contains a power of $`\varepsilon` below
$`\varepsilon^{-\Delta}`. Since the output has degree at most $`2^L` in the constants, the cut
changes it only in the positive powers of $`\varepsilon`. We then apply the argument of Lemma M.1
to the coefficients of the constants, which are now Laurent polynomials.”

In Lean the cut is `Nc.Approximates.exists_laurentPolynomial`, and the rest repeats the steps of
`lem_transfer` on the finitely many coefficients of the constants. Section Q.3 (page 70): “Lemma
N.2 repeats the argument of Lemma M.1 on coefficients.”
:::

:::theorem "thm_approx" (lean := "Paper.thm_approx, Paper.approx_rate_closed, Paper.contracting_approx_rate") (parent := "part-assembly")
*Theorem N.5 of the paper* (approximate computation; page 64; the same text as Theorem 1.4, page
2), quoted: “Theorem M.3 holds for circuits that approximate $`\mathrm{HC}_m`, respectively
$`\mathrm{PERM}_m`. In particular $`\mathrm{VNP} \not\subseteq \overline{\mathrm{VP}}` over every
field.”

`Paper.thm_approx` is the conjunction of the two sentences: the statement of `thm_allfields` with
`Approximates` for `Computes`, and `¬ VNP F ⊆ VPBar F` for every field `F` in any universe. The
constant is again $`c = 1/1600^2`.
:::

:::proof "thm_approx"
*The paper's proof* (page 64), quoted: “By Lemma N.2 we may assume that the constants of the
circuit lie in $`\mathbb{K}[\varepsilon, \varepsilon^{-1}]`. The flat case was treated after Lemma
N.3. In the contracting case the proofs of Lemmas K.2 and K.3 work over this ring and give
approximate accelerators. Indeed, the output $`\Phi + \varepsilon g` of the circuit may have a large
degree, but the program of Lemma K.2 gives its part of degree at most $`d`, which is $`\Phi` plus
$`\varepsilon` times that part of $`g`. Proposition N.4 excludes them, with the calculation of
Theorems K.7 and M.3. For the last claim, $`(\mathrm{HC}_m)` is in VNP.”

*Reading (gloss).* The Lean proof has the skeleton of `thm_allfields`, with these replacements.
`approx_rate_closed` is the bound over one field `K` in the lowest universe, for a family complete
for grid sums and a circuit over `LaurentPolynomial K` whose output has the coefficient property:
it turns the circuit back into `Approximates (G m) s` over `K`
(`Nc.Approximates.of_laurentPolynomial`) and splits on `thm_alt K`, with
`flat_rate_approx_complete` in the flat case and, in the contracting case,
`contracting_approx_rate` followed by the same `thm_allfields_exceeds`. `lem_transfer_approx` takes
the place of `lem_transfer`. The second sentence is proved as Corollary M.4, with `hc_mem_VNP` and
`exists_beyond_poly`.

Section Q.3 (page 70) on the route: “Theorem N.5 does not cite Lemma K.3, Theorem K.7 and Theorem
M.3. Instead it uses the step `thm_allfields_exceeds` of the proof of the last of them and
approximate analogues of the first two, which share their steps with them; the analogues are
`lem_circuit_approx` and `contracting_approx_complete`. On the way the constants are cut off
twice.” And: “The form of the constants in Lemma N.2 is derived again in the proof of Theorem N.5.”
Section Q.3 (page 68) also notes: “The flat bound for approximating circuits has 14 where
Proposition E.10 has 16.”
:::

*Remark N.6 of the paper* (determinantal complexity; page 64), quoted in full: “This remark is the
one numbered statement of the paper that has not been formalized in Lean. Since the determinant has
circuits of polynomial size” (the paper cites Ber84), “Theorem N.5 has the following consequence.
Over fields of characteristic different from two there is $`c > 0` such that, for all large $`m`,
the polynomial $`\mathrm{PERM}_m` is not approximated, in the sense of Definition N.1, by
determinants of affine matrices of size $`m^{c(\log m)^{1/3}}`. Over $`\mathbb{C}`, and for matrices
of polynomial size, this was conjectured by Mulmuley and Sohoni” (the paper cites MS01) “in the
language of orbit closures.” This remark has no node: there is no Lean declaration for it, the
development contains no statement about determinants of affine matrices, and nothing on this site
checks it.

# From the theorems of the paper to the five judged theorems

The file {repoFile "vp-vnp/Comparator/VpVnp/Solution.lean"}[`Solution.lean`] proves the five
statements of {ref "chapter-statement"}[The statement to trust] from three theorems of this
chapter. Each proof is a few lines.

- {bpref "Solution.mainTheorem"}[] is `Paper.thm_allfields.{u}`, with one case added.
  `Statement.MainTheorem` quantifies over every natural number $`p`, and `Paper.thm_allfields` over
  $`p` zero or prime. For other $`p` the proof takes $`m_0 = 0`: no field has such a
  characteristic (`CharP.char_is_prime_or_zero`).
- {bpref "Solution.mainTheoremApprox"}[] is the first part of `Paper.thm_approx.{u}`, in the same
  way.
- {bpref "Solution.separation"}[] is `Paper.cor_allclasses F`, and
  {bpref "Solution.separationClosure"}[] is the second part of `Paper.thm_approx.{u}`, each
  transported between the two copies of the classes: `Statement.Family` has fields `vars`, `fin`,
  `poly` and `Nc.Family` has `X`, `fin`, `poly`, and `Solution.toNc`, `Solution.ofNc` convert.
- {bpref "Solution.permanent_over_real"}[] is `Paper.thm_main`.

*Reading (gloss).* Three things make these short proofs possible, and Lean's kernel checks each of
them when it checks the proofs.

- The definitions of `Statement.lean` and those of the development (`Statement.Computes` and
  `Nc.Computes`, `Statement.perm` and `Nc.genPerm`, `Statement.hc` and `Nc.genHC`,
  `Statement.Approximates` and `Nc.Approximates`, `Statement.Beyond` and the inequality written
  out, the classes) are separate declarations. The proofs pass a term whose type is stated with one
  set where the other is expected (`exact h p hp`, or a type ascription such as
  `(hf : toNc f ∈ Nc.VP F)`), which Lean accepts only if the two types are definitionally equal.
  No theorem states these equalities; they are checked where they are used.
- The universes. `Statement.lean` declares a universe `u` and states its propositions for fields
  `F : Type u`; `Challenge.lean` states and `Solution.lean` proves them as `MainTheorem.{u}` and so
  on, for every `u`. The three theorems `Paper.thm_allfields`, `Paper.cor_allclasses` and
  `Paper.thm_approx` are themselves stated for `F : Type u` and are instantiated at the same `u`.
  All the mathematics from Appendix A to Appendix K, and `Paper.thm_main`, is in the lowest
  universe; the passage from `Type` to `Type u` is made inside `thm_allfields` and `thm_approx` by
  `lem_transfer` and `lem_transfer_approx`, as described under Theorem M.3. For the second
  sentences (the classes) no transfer of classes is needed: membership of $`(\mathrm{HC}_n)` in VNP
  and the inclusion of VP in VNP are proved directly in every universe, and the lower bound is the
  first sentence.
- The form of the bound. `Statement.Beyond c m s` is $`m^{c(\log_2 m)^{1/3}} < s`, the form in
  which `Paper.thm_allfields` states it.

What this chapter does not settle is the one link that no machine checks: that the propositions of
`Statement.lean` say what the paper's sentences say. That comparison is the subject of
{ref "chapter-statement"}[The statement to trust].
