/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import Comparator.VpVnp.Solution
import Paper

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "What a reader should keep in mind" =>

%%%
tag := "chapter-caveats"
file := "caveats"
htmlSplit := .never
number := false
%%%

This chapter collects, in one place and in order of weight, the limits of what the paper
({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]), its Lean development and this site establish. Most
of them are stated by the paper itself, in Section 3 (page 11), on page 17 and in Appendix Q
(pages 66–70), and are quoted; the rest concern this branch and this site. None is new to a
reader of the earlier chapters. The order is by how much each item bears on what a reader may
conclude.

# 1. No machine and no human has checked that the statement file says what is claimed

The Lean check establishes five Lean theorems. That they are the paper's theorems, in the
standard model and for the standard classes, is a matter of reading the 98 lines of
`Statement.lean` against the paper and the literature. The README of the folder: “Lean checks the
proofs, but no machine checks that this file says what is claimed.” The paper (Section Q.1,
page 66): “Whether the statements say what is meant was judged only by AI readers. No human
mathematician has checked the development, the statement file or the proofs.”

{ref "chapter-statement"}[The statement to trust] is a further reading by an AI model, and has
the same standing. It finds the file faithful, and it records the conventions that a reader
could otherwise take for something stronger:

- gates are counted with variables and constants; the factor three to the count of operations is
  the paper's remark and is not formalized;
- $`m_0` depends on the characteristic, and only $`c` is absolute;
- the bound is quasi-polynomial, $`2^{c(\log m)^{4/3}}`;
- approximation is defined with Laurent series as constants; its agreement with the usual
  definition through rational functions rests on a truncation that the development proves, on
  two elementary inclusions that it does not state, and on this blueprint's recollection of the
  usual definition, which was not checked against the literature;
- the permanent is written for the transposed matrix.

On this branch there is a second link of the same kind, smaller: one line of the statement file
is spelled differently from the printed file, because the Mathlib function it used no longer
exists. That the new spelling denotes the same coefficient is machine-checked for this build's
side and cited from the older Mathlib for the other
({ref "statement-spelling"}[The one line this build spells differently]).

# 2. No human has checked the proof, and at four places only the Lean proof is complete

The paper, Section 3 (page 11): “The proofs in this paper were found and written by AI. No human
mathematician has checked the proofs.” The Lean development proves Lean statements by Lean
proofs; it does not check the printed argument. The two run in parallel, and the paper says how
far (page 17), quoted in full:

> The printed proofs differ in completeness. Those of Sections A to G and of Appendix O, and the deduction of Theorem L.1 in Section L, are meant to be complete, if terse. The proofs of Proposition I.1, Theorem H.2(d), (e), Theorem J.3 and Proposition N.4 describe machines and programs and account for their sizes and running times. That these do exactly what is claimed can be verified only in the Lean development, and each of these four statements is followed by a formalization note that says so. Consequently the contracting case, and with it every main result, rests on Lean at these points.

The four statements are {bpref "prop_universal"}[Proposition I.1],
{bpref "thm_tree"}[Theorem H.2], {bpref "thm_onecut"}[Theorem J.3] and
{bpref "prop_approx_acc"}[Proposition N.4]; their nodes quote the formalization notes. The
dependencies of the Lean theorems in this build refine the last sentence of the quotation: all
five theorems of `Solution` depend on the Lean theorems of the first three, and only the two
on approximation (`Solution.mainTheoremApprox`, `Solution.separationClosure`) depend on that of
Proposition N.4 ({ref "chapter-claim"}[What is claimed] says how this was read off).

Three things follow for a reader.

*The four items cannot be refereed from the paper.* What the universal automaton, the programs of
Theorem H.2, the evaluator and cutting program of Theorem J.3 and the programs of Proposition N.4
are, and that they do what is claimed, is in the Lean code, for the most part in the libraries `Nc/Uni`,
`Nc/Sort`, `Nc/Tow`, `Nc/Dl` and `Nc/Grp`, about 26,000 lines by a count of the files, and with
`Nc/Tape`, `Nc/Cut` and the program model `NS1` about 36,000 of the development's 73,000. The chapters
{ref "chapter-laws"}[Rerouting laws and tree networks],
{ref "chapter-programs"}[Programs, automata and cutting] and
{ref "chapter-accelerators"}[Accelerators and the diagonal argument] describe these programs from
the code and say what their authors did and did not understand from it. Those descriptions are
exposition by an AI model of code written by AI models; they make the Lean proof easier to enter
and do not replace reading it.

*There is a zone the paper is silent on.* The paper calls the printed proofs of Sections A to G,
of Appendix O and of the deduction of Theorem L.1 complete, and flags four statements as complete
only in Lean. It says neither of the other statements of Sections H to N: Proposition H.1 (whose
part (d) is printed with the exponent of the Lean theorem, the printed argument giving a smaller
one; formalization note, page 44), parts (a) to (c) of Theorem H.2, Lemma I.2, Proposition J.2
(whose formalization note, page 52, says that its last claim rests on Theorem H.2(d) and (e)),
Theorem J.4, all of Section K, Theorem L.2 and Corollary L.3, and Appendices M and N apart from
Proposition N.4. Their printed proofs should be read as accounts whose detail varies, with the
Lean proof as the authority.

*The diagonal argument rests on the bounds of these programs.* The contracting case ends in a
diagonal argument against programs that carry the coefficients of a small circuit as advice
({bpref "thm_noacc"}[Theorem K.6]). It needs the running times and the sizes of the advice to
fit at every scale. Those bounds come from the cutting theorem
({bpref "thm_cut"}[Theorem J.4]), which iterates the single cut of Theorem J.3, one of the four
items; and the printed proofs of Section K themselves lie in the zone just described. The paper
also says (page 3) that for this case “We have not analysed how it relates to relativization
and algebrization”.

# 3. Many intermediate Lean statements are variants of the printed ones

The theorems with prefix `Paper.` “state the numbered statements” (Section Q.3, page 66), and
Section Q.3 lists, over four pages, where they differ. None of the differences can affect the
five theorems, whose statements are fixed by `Statement.lean`; each limits what may be said when
a printed lemma is set beside a Lean name. {ref "chapter-table3"}[The paper's statements and
their Lean names] has a verdict for every numbered statement, with the counts. The differences
that the paper names are of four kinds.

- _More general in Lean._ Lemmas A.3, E.4, E.7, F.1, F.2, I.2, K.3, M.1, N.2, N.3 and
  Proposition B.2, by the paper's list (page 68).
- _Other constants._ “Lean states Lemma F.3 for explicit numbers …, which are not those of the
  printed proof, and $`C(n)` in (F.1) and in Lemmas F.4 and F.5 is formed with them” (page 68;
  {InlineLean.name}`Paper.kappa`). The flat bound for approximating circuits “has 14 where
  Proposition E.10 has 16” (page 68): {InlineLean.name}`Paper.flat_rate_approximating` concludes
  $`\ell k \sqrt{k}/14 \le \log s`, the intermediate inequality of the printed proof of
  Proposition E.10, and no Lean theorem states the form with 16 for approximating circuits
  ({bpref "flat_rate_approx_complete"}[the node]).
- _Hypotheses made explicit._ Theorem H.2, Proposition J.2 and Theorems J.3 and J.4 take the
  laws, and the last two the generators of $`A`, as standing hypotheses; Propositions K.5 and N.4
  and Theorem K.6 “do not assume the contracting case. They take the conclusion of Theorem J.4 as
  a hypothesis” (page 69; {InlineLean.name}`NS1.CutHyp`). The contracting case is assembled from
  instances of these.
- _Clauses in structures, and notions that rest on reading._ “Theorem H.2 and Proposition J.2
  state their clauses as the fields of structures” ({InlineLean.name}`Paper.ThinTrees`,
  {InlineLean.name}`Paper.PieceCut`), and for the value of a tree “no theorem restates this as the
  value of a network as defined in Section H” (page 69). The theorem `def_law` “lists only three
  of the fields of the structure, in one direction, so that it rests on reading the structure
  that it is the printed notion” (page 68; {InlineLean.name}`Nc.G.Law`). “In Lemma K.3,
  `lem_circuit_phi` states what is used of $`\Phi`, not that it equals the printed sum over
  words” (page 70): the polynomial $`\Phi` of the overview is not defined in Lean.

So for the statements of the last kind the node of this site shows the paper's statement beside
a Lean theorem that encodes it, and the match between the two is a reading, in the same sense as
for the statement file but with nothing resting on it beyond the exposition.

The chapters of this blueprint found a few further points that Section Q.3 does not list. None
bears on the five theorems.

- _The two forms of the contracting hypothesis._ Definition 2.1 states it for spectral points
  and Definition D.1 for prices. The paper says (page 5) that the two are the same “because the
  inequality survives scaling and limits”. No Lean theorem states this equivalence; the
  development uses the form for prices throughout ({bpref "def_cases"}[Definition D.1]). For the
  flat hypothesis the two forms are related by {InlineLean.name}`Paper.def_price`.
- _Which form of the flat bound Theorem M.3 uses._ Section Q.3 (page 70) says that “Lemma K.3,
  Theorem M.3 and Theorem N.5 use the general forms for families that are complete for grid
  sums”. In the Lean proof of Theorem M.3 this holds for $`\mathrm{HC}_m`; for
  $`\mathrm{PERM}_m` the flat half is {InlineLean.name}`Paper.thm_flat_rate`, Theorem E.11
  itself, and the contracting half is {InlineLean.name}`Paper.thm_contracting`, Theorem K.7
  itself (which is proved from the general form). So Theorem E.11 is on the route of
  `Solution.mainTheorem` ({bpref "flat_rate_complete"}[the node of the general form]).
- _Encodings that the paper does not remark on._ The random map of Proposition A.8 is a family
  of measurable maps with finite ranges on a probability space
  ({bpref "prop_random"}[Proposition A.8]); the Lean forms of Lemmas E.7 and E.8 do not ask
  that the set $`P`, respectively $`I`, be nonempty.

The paper adds a caution about the Lean files themselves (page 70): “Comments in the Lean files
are informal: some paraphrase the paper, say a little more than the step that they name proves,
or describe a bound or a definition loosely.” The docstrings appear on this site beside the code.
They are comments. This blueprint quotes Lean statements, not docstrings, as what is proved.

# 4. Some printed statements are not on the route, and some are not in Lean

Section Q.3 (page 66): “The theorems of `Solution` are proved through them, with these
exceptions, which are not on that route: Theorem L.2, Corollary L.3, the qualitative bound in the
flat case (Proposition E.5 and Theorem E.6) and the definitions.” These are proved in Lean, but
the five theorems do not depend on them. For this build that was confirmed from the constants on
which the five theorems depend: of the Lean theorems that Table 3 names first for a numbered
statement other than a definition, exactly those of the four statements just listed are not
among them. Several of the theorems that Table 3 names second are not among them either
({ref "chapter-table3"}[The paper's statements and their Lean names] lists them). The Lean route
also differs from the printed references at the places listed under “Routes of proof” (page 70);
for example Theorem N.5 “does not cite Lemma K.3, Theorem K.7 and Theorem M.3”.

Not formalized at all (page 70): “Remark N.6, the example of flattening ranks after Definition
A.1, the remarks that follow the proof of Theorem D.2, the fact that $`r` in the proof of
Proposition A.5 is also a limit, and the factor three between the two ways of counting gates in
Section 1”. Remark N.6 is the consequence for the determinantal complexity of the permanent. It
is argued in prose only, and the Lean development contains no statement about determinants of
affine matrices.

# 5. The intermediate theorems are stated in the lowest universe

Section Q.3 (page 66): “The theorems with prefix `Paper.` are stated for fields in the lowest
universe, and so are their rings, algebras, groups, spaces, point sets and index sets. The
exception is the given field in Theorems M.3 and N.5, Corollary M.4, Definition N.1 and Lemmas
M.1 and N.2, which may lie in any universe. This restricts the printed statements to the lowest
universe. The theorems of `Solution` hold for fields in every universe.”

The main results lose nothing: the proof moves every circuit to an algebraically closed field of
the same characteristic in the lowest universe (Lemmas M.1 and N.2) and argues there. But a
statement such as `Paper.thm_alt` is, as stated in Lean, about fields `K : Type`.

# 6. The proof is not constructive, and the threshold is not effective

- _The case is not decided._ Theorem D.2 is proved by excluded middle on the contracting
  hypothesis. The paper (page 6): “We do not know which of the two hypotheses holds, even over
  $`\mathbb{R}`, nor do we show that the two are mutually exclusive.” The bound proved is the
  weaker of the two that the cases give.
- _$`m_0` is not known._ The paper (page 8): “In the contracting case the constants, among them
  $`m_0`, depend on the integer $`\mu`, for which the proof gives no value, and this is why
  Theorem 1.1 comes with no value for $`m_0`.” The constant $`c = 1/1600^2` is explicit in the
  Lean proof; it should not be read as making the theorem effective.
- _The functionals are not explicit._ The paper (page 3): “The spectral points that we use are
  not explicit at all, since they are only known to exist by Zorn's lemma (`prop_gauge`).” The
  parallelogram law of Lemma C.2 is obtained with a limit along a free ultrafilter, in Lean a
  fixed one (page 69), and the flat case of the dichotomy with a compactness argument. The
  rerouting laws exist by duality and are not written down.

All of this is ordinary classical mathematics, and Lean's axiom `Classical.choice` covers it.
It does mean that the proof exhibits no explicit obstruction and no explicit hard instance size.

# 7. This site reports on a port, not on the paper's build

The paper's checks (Section Q.1) are of the development on Lean 4.33.1. This site is built from a
port to Lean 4.36.0 and the corresponding Mathlib, made on a branch of a fork; it is not part of
the upstream repository, and nothing on it has been reviewed there.
{repoFile "vp-vnp/PORTING.md"}[`PORTING.md`] lists the changes: one spelling in four statements,
and 28 repairs of proofs. Every verdict and mark of this site is about the port. The Comparator
run with the checker nanoda that the paper reports has not been repeated on this branch; the
site's own comparison and its kernel replay with two other checkers are described in
{ref "chapter-checking"}[How to check this yourself], with what they leave trusted.

# 8. Much of this site is generated from code, without exposition

The written chapters present the paper's numbered statements and the Lean theorems that state
them. The development is far larger: most of its declarations are steps of proofs that the paper
does not print. They are in the part
{ref "part-generated"}[The Lean development, declaration by declaration], which a program writes
from the compiled Lean code. A reader should know three things about it.

- _No informal statement._ A generated node shows a Lean declaration, its status and its
  dependencies, and the sentence that it was generated from the Lean code. The written chapters
  name 400 declarations in their nodes; when this text was last revised, 2,003 further
  declarations were shown as generated nodes. The Project Stats page gives the numbers for the
  build a reader is looking at, among them how many nodes have an informal statement.
- _Listed by name only._ Theorems of the library `Nc` whose names do not begin with `Paper.`
  (2,210 of them when this text was last revised) are listed by name with a link to the source,
  and have no node, because a node for each would make the site too large to publish. Lean's
  kernel checked them when the development was compiled; they do not appear in the graph.
- _The graph is not the full dependency relation._ An edge from a written node is drawn when the
  Lean code of the node uses a declaration of another node directly or through declarations that
  have no node, or when the chapter declares the dependency. A generated node has edges only to
  nodes of its own module. So a dependency of one written node on another that passes through
  generated nodes of several modules is drawn only where a chapter declares it, and the graph
  understates how the modules of the libraries depend on each other. Conversely, a node that
  shows several Lean declarations has an edge to it whenever any one of them is used. The Lean
  code, not this graph, is the full dependency relation; the statements about what the five
  theorems depend on, in this chapter and in
  {ref "chapter-table3"}[The paper's statements and their Lean names], were read off from the
  Lean constants and not from the graph.

The marks on generated nodes mean what they mean elsewhere: they are about the Lean code, and
the Project Stats page defines them.

# 9. What the paper does not claim to have done

- It does not settle P versus NP and says nothing about Boolean circuits (abstract; page 4).
- “We do not claim that the exponent $`1/3` is optimal” (page 2).
- It has not analysed the relation of the contracting case to relativization and algebrization,
  and has “not worked out” what the bound gives for the derandomization of polynomial identity
  testing (page 3).
- Its statements about earlier and concurrent work are in its Section 1.2. This blueprint
  repeats none of them as its own and has checked none of the works cited there.

# 10. This blueprint

The exposition on this site was written by AI models, from the paper and the Lean code. No human
mathematician has reviewed it. Where it quotes the paper, the quotation marks and the page number
let a reader check the quotation. Where it reads Lean code, it says so, and the code is beside
it. Where it summarizes a proof, the summary is an aid to reading and carries no authority: of
everything on a page, only the Lean statements have been checked by a machine, and only for
being proved.
