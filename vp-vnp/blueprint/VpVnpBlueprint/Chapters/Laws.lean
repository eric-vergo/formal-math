/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import VpVnpBlueprint.Chapters.Poincare
import Paper.Tree

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "Rerouting laws and tree networks" =>

%%%
tag := "chapter-laws"
file := "laws"
htmlSplit := .never
number := false
%%%

This chapter follows Appendices G (pages 41–43) and H (pages 43–48) of the paper
({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]). It establishes two things in the contracting case.
Theorem G.2 turns the Poincaré inequality of {ref "chapter-poincare"}[the previous chapter] into
finitely many identities between tensors, the _rerouting laws_: each writes a product of wires
between arbitrary pairs of elements of $`U_h` as a sum of tensor networks whose wires run along
edges of the Cayley graph, at a cost that a constant $`C_1` independent of $`h` controls. Theorem
H.2 applies these laws repeatedly, along a tower of finite groups (Proposition H.1), to an
arbitrary tensor network on $`M` nodes, and writes its value as a sum of values of networks whose
nodes form a tree of small depth in which a node holds fewer packets, by a factor $`M^{\gamma}`,
than the network holds in all. {ref "chapter-programs"}[Programs, automata and cutting] takes the
network to be a computation and cuts it along such a tree.

How to read the chapter. Appendix G is among the appendices whose printed proofs, the paper says,
“are meant to be complete, if terse” (page 17). Appendix H is not uniform. The paper, page 17,
quoted: “The proofs of Proposition I.1, Theorem H.2(d), (e), Theorem J.3 and Proposition N.4 describe machines and
programs and account for their sizes and running times. That these do exactly what is claimed can
be verified only in the Lean development, and each of these four statements is followed by a
formalization note that says so. Consequently the contracting case, and with it every main result,
rests on Lean at these points.” For Theorem H.2(d) and (e) this chapter therefore describes, from
the Lean code, what the construction is and how the Lean proof is organised (the section
{ref "laws-lean-construction"}[The Lean construction behind Theorem H.2]). About Proposition H.1
and parts (a) to (c) of Theorem H.2 the sentence quoted from page 17 says nothing: they are
neither among the proofs meant to be complete nor among those flagged. For them this chapter gives
what the printed proof gives and what the Lean statement gives, and makes no claim about the
completeness of the printed argument.

The Lean statements of this chapter differ from the printed ones in several ways, and all the
differences recorded here are listed by the paper in Section Q.3 (pages 68–70). Definition G.1 is
a Lean structure, `Nc.G.Law`; the clauses of Theorem H.2 are the fields of a Lean structure, `Paper.ThinTrees`; Proposition H.1(d) is stated with the exponent $`7` that
Lean proves, where the printed argument gives $`3`; and Theorem H.2 takes the laws as a hypothesis.
The Lean development says _unit_ for a packet, _table_ for a node tensor, _near pair_ for an edge
of the Cayley graph of $`U_h`, _chamber_ for an element of a set $`V_j` of the tower and _vertex_
of type $`i` for a coset of type $`i` (Section Q.3, pages 66 and 68, for the first three; the last
two are the words of the Lean files).

# G.1. Edges, loads and the choice of $`h`

The paper, page 41, quoted: “Let $`b = |U_h| = 2^{h(h-1)/2}`. By an _edge_ we always mean an edge
$`\{g, x_j g\}` of the Cayley graph of $`U_h` for the generators $`x_j = 1 + E_{j,j+1}`,
$`0 \le j < h-1`, and there are $`b/2` edges for each $`j`. A _load_ is a vector $`n = (n_e)` of
natural numbers, indexed by all pairs $`e` of distinct elements of $`U_h` or by the edges only,
and we measure loads by the norms
$$`\begin{aligned} \|n\| &= \Bigl(\tfrac{b(b-1)}{2} \sum_e n_e^2\Bigr)^{1/2}, \\ \|n\|_* &= \Bigl(\tfrac{b}{2} \sum_{\text{edges } e} n_e^2\Bigr)^{1/2}. \end{aligned}`”

In Lean $`b` is `2 ^ ee h` with `ee h = h * (h - 1) / 2`; the edges are the type `Nc.Tower.NN h`
of near pairs, with the ends `cNear ν` and `dNear ν`; a load on pairs is a function on
`Sym2 (U h)` of which only the values at pairs of distinct elements are used; and the norms are
written out where they occur.

:::lemma_ "thm_laws_poincare" (lean := "Paper.thm_laws_poincare") (parent := "part-contracting")
*The Poincaré inequality over pairs and edges* (page 42), quoted: “For a price on $`U_h` and a pair
$`e` we write $`|e|` for the distance between the two elements of $`e`. Let $`u` and $`C_0` be as
in Theorem F.6, let $`h` be a multiple of $`u` with $`h \ge 2u`, and fix an integer
$`C_0' \ge 2C_0 + 1`. Then Theorem F.6 implies that for every price on $`U_h`
$$`\frac{2}{b(b-1)} \sum_e |e|^2 \;\le\; C_0' \cdot \frac{2}{b} \sum_{\text{edges } e} |e|^2,`
because the left side of its inequality is at least half the mean of $`|e|^2` over all pairs, and
the right side is $`C_0 \cdot \frac{2}{b} \sum |e|^2` over the edges.”

In the Lean statement the real number `C` is the constant $`C_0` of Theorem F.6 and the natural
number `C₀` is the paper's integer $`C_0'`; this renaming holds throughout the Lean files of this
chapter. The sum on the left runs over ordered pairs and is divided by $`b(b-1)`, which is the
printed mean over pairs.
:::

The choice of $`h` (page 42), quoted: “Let $`C_1 = 4C_0'`. As $`C_1` does not depend on $`h`, we
can choose $`h` so large that
$$`h \ge 3, \qquad 1 + 8C_1 \le h/4.`
From now on $`h` and $`b` are fixed, and $`b \ge 8`.” The display is (G.1) of the paper. The
paper adds a formalization note (page
42), quoted: “Of the second condition in (G.1), the proof of Theorem H.2 uses only
$`1 + 4C_1 \le h/4`. The Lean proof is coarser at this point and uses (G.1) as it stands.” In Lean
(G.1) is the pair of hypotheses `3 ≤ h` and `1 + 8 * (4 * C₀) ≤ h / 4` of
{bpref "thm_laws"}[Theorem G.2], and `3 ≤ h` and `1 + 8 * VL.C₁ ≤ h / 4` of
{bpref "thm_tree"}[Theorem H.2].

# G.2. Laws

:::definition "def_law" (lean := "Nc.G.Law, Paper.def_law") (parent := "part-contracting")
*Definition G.1 of the paper* (law; page 42), quoted: “Let $`A` be a commutative ring. A _law_ on
$`U_h` over $`A` consists of the following data.

_Slots._ A finite family of pairs of distinct elements of $`U_h`, the _slots_. They are counted by
a load $`\sigma` on pairs: $`\sigma_e` is the number of slots equal to $`e`. Every slot carries one
bit, and each of its two ends has its own copy of this bit.

_Indices._ A finite nonempty set $`\mathcal{I}` of _indices_, with an injective _code_ that
assigns to every index a string of $`\lambda` bits, where $`\lambda \ge 1`.

_Channels._ For every $`i \in \mathcal{I}` a load $`\mathrm{len}_i` on edges. In this role an edge
$`e` is called a _channel_, and it carries $`\mathrm{len}_{i,e}` bits.

_Node tensors._ For every $`i \in \mathcal{I}` and every element $`g` of $`U_h` a function with
values in $`A`, the _node tensor_ of $`(i, g)`. Its arguments are the bits at $`g` of the slots
that contain $`g`, and the bits of the channels that contain $`g`.

These data are required to satisfy, for all values of the bits at the ends of the slots,
$$`\begin{aligned} &\prod_e \bigl[\text{the } \sigma_e \text{ bits agree at both ends of } e\bigr] \\ &\qquad = \sum_{i \in \mathcal{I}} \sum_y \prod_g (\text{node tensor of } (i, g)), \end{aligned}`
where $`e` runs over all pairs, $`y` over the assignments of $`\mathrm{len}_{i,e}` bits to every
channel $`e`, and $`g` over $`U_h`.” The display is (G.2) of the paper.

The Lean notion is the structure `Nc.G.Law`, and it is more general than the printed one. Section
Q.3 (page 68): “Laws may have any finite sets of elements, slots and channels. A law in Lean also
records that its channels connect its elements, in the form that indices which agree along all
channels agree everywhere; on $`U_h`, where the channels are all the edges, this holds by itself.
The conditions on $`\lambda`, on $`\mathcal{I}` and on $`U_h` come with Theorem G.2.” And: “The
theorem `def_law` lists only three of the fields of the structure, in one direction, so that it
rests on reading the structure that it is the printed notion.”

*Reading of the structure (gloss), field by field.*

* `Ro`, `Sl`, `Cn`, `I`: four finite types, the elements (“roles”), the slots, the channels and
  the indices. Nothing ties `Ro` to $`U_h` or `Cn` to the edges.
* `a`, `b : Sl → Ro` with `ab : ∀ e, a e ≠ b e`: the two ends of a slot, which are different. The
  load $`\sigma` is not a field; it is the number of slots with a given pair of ends.
* `c`, `d : Cn → Ro` with `cd : ∀ ν, c ν ≠ d ν`: the two ends of a channel.
* `lam : ℕ`, `lab : I → Fin lam → Bool`, `lab_inj`: the length $`\lambda` of the codes, the code,
  and its injectivity. Neither $`\lambda \ge 1` nor that `I` is nonempty is a field.
* `len : I → Cn → ℕ`: the loads $`\mathrm{len}_i`.
* `tab`: for a role `p` and an index `i`, a function with values in the ring of the bits at `p` of
  the slots with an end at `p` and of the `len i ν` bits of every channel `ν` with an end at `p`:
  the node tensor of $`(i, p)`.
* `law`: the identity (G.2). For every assignment `X` of a bit to every pair of a role and a slot,
  $`\bigl[\forall e,\ X(a_e, e) = X(b_e, e)\bigr] = \sum_i \sum_y \prod_p \mathrm{tab}_p(i, X(p, \cdot), y)`,
  where $`y` assigns `len i ν` bits to every channel `ν`. Only the values of `X` at the two ends
  of each slot enter either side.
* `conn`: if a function from the roles to the indices takes the same value at the two ends of
  every channel, then it is constant. This is the connectedness that Section Q.3 mentions.

The theorem `def_law` states `lab_inj`, `ab` and `law` for an arbitrary law, and nothing else. So
the correspondence between Definition G.1 and the Lean development is this reading of the
structure, not a theorem; and a law “on $`U_h`” in the printed sense is a Lean law together with
bijections of its roles with $`U_h` and of its channels with the edges, which
{bpref "thm_laws"}[Theorem G.2] supplies.
:::

The paper's convention (page 43), quoted: “When a law is applied, every element has to know the
index $`i`, so we let every channel begin with the $`\lambda` bits of the code of $`i`, and give
the node tensor $`0` to an element whose channels do not all begin with the same code, or begin
with a string that is no code. Since the edges connect $`U_h`, codes that agree along all channels
agree everywhere. The channel $`e` now carries $`\lambda + \mathrm{len}_{i,e}` bits, and this is
the load that Theorem G.2(b) bounds.” In Lean the convention is not part of a law. It is built into
the node tensors of a move ({bpref "law_move"}[the definition of a move] below): the string of a
channel is the concatenation, over the layers, of the code of the index and the bits of the law
(`Nc.G.chString`). The sentence on connectedness is `Paper.indices_agree` for $`U_h`, and the field
`conn` in general.

:::lemma_ "laws_over_algebras" (lean := "Paper.laws_over_algebras, Paper.lawMap") (parent := "part-contracting")
*The remark after Theorem G.2* (page 43), quoted: “The laws are finitely many polynomial
identities with coefficients in $`A`, so they hold over every commutative $`A`-algebra.”

The Lean theorem states the identity (G.2) of a law over `A` with its tables mapped to an
`A`-algebra `R`, and `lawMap` is the resulting law over `R`.
:::

# G.3. Existence of laws

:::theorem "thm_laws" (lean := "Paper.thm_laws") (parent := "part-contracting")
*Theorem G.2 of the paper* (existence of laws; page 43), quoted: “There are a finitely generated
subring $`A` of $`\Bbbk`, a positive integer $`a_1`, and finitely many laws on $`U_h` over $`A`
such that

(a) for every load $`n` on pairs and every $`t \in \mathbb{N}` with $`\|n\| \le a_1 t` some law
has $`n \le t\sigma`;

(b) for every law and every index $`i` of it,
$`\|\lambda + \mathrm{len}_i\|_* \le \sqrt{C_1}\, a_1`.”

“Here $`n \le t\sigma` is meant entry by entry, and $`\lambda + \mathrm{len}_i` is the load of the
convention above.”

The Lean statement contains the printed one and the choices that precede it. Section Q.3 (page
68): “Its Lean form also states the choices of Section G: $`u` and $`C_0` are as in Theorem F.6,
$`C_0' \ge 2C_0 + 1` is an integer and $`C_1 = 4C_0'`. It asserts that some multiple $`h \ge 2u` of
$`u` satisfies (G.1), and it asserts (a) and (b) for every such $`h`. That the channels there are
the edges, each once, on which the norm in Theorem G.2(b) depends, follows from the definitions
but is stated by no theorem of the development.”

*Reading of the Lean statement (gloss).* For a field `K` in the contracting case there are
$`u \ge 2`, a real $`C_0 \ge 0` (in Lean `C`) with `PoincareBound K u C`, and a natural number
$`C_0'` (in Lean `C₀`) with $`2C_0 + 1 \le C_0'`, such that some $`h` is a multiple of $`u` with
$`2u \le h`, $`3 \le h` and $`1 + 8 \cdot 4C_0' \le h/4`, and such that for every such $`h` there
are: a subring `A` of
`K` that is finitely generated as a ring (`Algebra.FiniteType ℤ A`); a natural number
$`a_1 > 0`; a finite type `Di` and a law `L d` over `A` for every `d : Di`; and bijections `ro d`
of the roles of `L d` with $`U_h` and `cn d` of its channels with the edges, with the following
five properties. The two ends of every channel are the two ends of its edge. Every `L d` has
$`\lambda \ge 1` and a nonempty set of indices. (a) is the printed clause, with $`\|n\|` written
out over the pairs of distinct elements and with $`\sigma_q` the number of slots of `L d` whose
ends are the pair $`q`. (b) is the printed clause in the form
$`\bigl(\tfrac{b}{2} \sum_\nu (\lambda + \mathrm{len}_{i,\nu})^2\bigr)^{1/2} \le \sqrt{4C_0'}\; a_1`,
the sum over the channels $`\nu` of the law.

On the sentence that no theorem states: (b) bounds a sum over the channels of the law, which is
the norm $`\|\cdot\|_*` over the edges because `cn d` is a bijection of the channels with the type
`NN h`. That `NN h` contains every edge $`\{g, x_j g\}` exactly once rests on its definition, a
subtype of the pairs $`(j, g)` cut out by a predicate that holds for exactly one of $`g` and
$`x_j g` (`Nc.Tower.FU_iff`). This blueprint read that definition and that lemma and did not
find a theorem that states the conclusion either.
:::

:::proof "thm_laws"
*The paper's proof* (page 43), summarised. “We apply the duality theorem to an inequality between
spectral points that follows from the Poincaré inequality, and read the resulting cover as a law.”

_The inequality._ Let $`a` be a large integer. The loads $`\sigma_x = \lceil a x \rceil`, for real
vectors $`x \ge 0` on pairs with $`\|x\| \le 1`, are finitely many, with
$`\|\sigma_x\| \le a + O(1)`. Let $`\mathcal{B}` be the finite set of loads $`\lceil y \rceil` on
edges for real $`y \ge 0` with $`\|y\|_* \le \sqrt{C_0'}\,(a + O(1))`. For every price on $`U_h`
and every $`x`, the Cauchy–Schwarz inequality, applied twice, and the Poincaré inequality in the
form above give
$$`\sum_e \sigma_{x,e}\, |e| \;\le\; \max_{\beta \in \mathcal{B}} \sum_{\text{edges } e} \beta_e\, |e|.`

_Duality._ For a load $`\sigma` let $`\mathsf{W}^\sigma = \prod_e \langle 2 \rangle_e^{\sigma_e}`,
a tensor on the set of parties $`U_h`. For a spectral point $`\varphi` on $`U_h`,
$`\varphi(\mathsf{W}^\sigma) = 2^{\sum_e \sigma_e d_\varphi(e)}` by Lemma A.2, and $`d_\varphi` is
a price. Hence $`\varphi(\mathsf{W}^{\sigma_x}) \le \max_{\beta} \varphi(\mathsf{W}^\beta)`, the
hypothesis of the duality theorem (Theorem A.6,
{ref "chapter-spectral"}[Tensors, spectral points and prices]). For every $`\varepsilon > 0` and
every large $`q` it covers $`\mathsf{W}^{q\sigma_x}` by at most $`2^{\varepsilon q}` tensors
$`\mathsf{W}^{\beta'}` in which $`\beta'` is a sum of $`q` elements of $`\mathcal{B}`; one $`q`
serves for the finitely many $`\sigma_x`.

_Reading the cover as a law._ The left side of (G.2) is $`\mathsf{W}^{q\sigma_x}`, so the slots
are counted by $`q\sigma_x`; the indices number the tensors of the cover; $`\mathrm{len}_i` is the
sum $`\beta'` of the $`i`th of them; the node tensor of $`(i, g)` is the matrix of the linear map
that the party $`g` applies; the code has $`1 \le \lambda \le \varepsilon q + 2` bits;
$`a_1 = aq`; and $`A` is the subring generated by $`-1` and the entries of the node tensors.
Clause (b) follows from the triangle inequality,
$`\|\lambda + \mathrm{len}_i\|_* \le q\bigl(\sqrt{C_0'}\, a + O(1)\bigr) + (\varepsilon q + 2)\|1\|_* \le 2\sqrt{C_0'}\, aq = \sqrt{C_1}\, a_1`,
“if we choose first $`a` large, then $`\varepsilon` small, and then $`q` large”; this is where the
factor $`4` in $`C_1 = 4C_0'` is spent. Clause (a): for $`\|n\| \le a_1 t` and $`t > 0`, the
vector $`x = n/(a_1 t)` has $`\|x\| \le 1` and $`n \le t\, q\sigma_x`.

_In Lean._ The steps are `Paper.thm_laws_loads` (the inequality between loads),
`Paper.thm_laws_cover` (duality, giving the cover “as an identity between functions of bits”),
`Paper.thm_laws_over_field` (the laws over `K` for one $`h`), and `Paper.thm_laws_ring` (the
subring). Section Q.3 (page 70): “The proof of Theorem G.2, for example, uses all loads of bounded
norm where the text uses the rounded ones”. The theorem depends on Theorem F.6 only through
{bpref "thm_laws_poincare"}[its form over pairs and edges].
:::

:::lemma_ "exists_laws" (lean := "Paper.exists_laws, Nc.Tow.VLaws") (parent := "part-contracting")
*What the later sections take from Theorem G.2* (page 43), quoted: “From now on $`A`, $`a_1` and
the laws, in some fixed order, are kept, and all constants below depend only on these choices.”

In Lean nothing is kept: the laws are an explicit hypothesis of every later theorem. Section Q.3
(page 69): “Theorem H.2, Proposition J.2 and Theorems J.3 and J.4 have the laws, and the last two
the generators of $`A`, as explicit standing hypotheses. The laws may be any finite family of
laws, over any commutative ring, that has the properties of Theorem G.2, with $`h \ge 3` and (G.1)
as hypotheses; property (b) of Theorem G.2 enters as
$`b \sum_e (\lambda + \mathrm{len}_{i,e})^2 \le G_1` for an integer $`G_1 \le 2C_1 a_1^2`. In the
contracting case `exists_laws` and `exists_generates` supply these hypotheses”.

That hypothesis is a term of the structure `VLaws A cNear dNear 1 (2 ^ ee h)`: a finite family of
laws over a commutative ring `A` with the bijections `ro` and `cn` and the clause on ends of
{bpref "thm_laws"}[Theorem G.2], with $`\lambda \ge 1` and nonempty index sets, numbers
$`a_1 > 0`, $`C_1 \ge 0` and $`G_1 \le 2C_1a_1^2`, clause (a) (the field `L1`) and clause (b) in
the integer form just quoted (the field `L2`). The theorem `exists_laws` states that in the
contracting case there are $`h \ge 3`, a finitely generated subring `A` of `K` and such a term with
$`1 + 8C_1 \le h/4`, for which moreover $`2C_1a_1^2` is a natural number. In its proof
$`C_1 = 4C_0'` and $`G_1 = 8C_0'a_1^2`.
:::

# H.1. A tower of finite groups

The paper, page 44, quoted: “To apply the laws repeatedly we use groups with $`h` types of edges,
arranged in a cycle, such that leaving out any one type leaves copies of the Cayley graph of
$`U_h`. Let
$$`R_n = \mathbb{F}_2[s]/(s^{n+1}), \qquad G_n = \mathrm{SL}_h(R_n),`
number the coordinates by $`\mathbb{Z}/h`, and put $`\varsigma = 1 + s`,
$`X_k = 1 + E_{k-1,k}` for $`k \ne 0` and $`X_0 = 1 + \varsigma E_{h-1,0}`, where $`E_{jk}` is a
matrix unit. … Let $`K_n` be the kernel of the reduction $`s \mapsto 0` from $`G_n` to
$`\mathrm{SL}_h(\mathbb{F}_2)`, a $`2`-group of order $`2^{(h^2-1)n}`.” In Lean $`G_n` is
`Nc.Tower.G h n`, the generator $`X_k` is `Nc.Tower.gen _ k`, and the statement on $`K_n` is
`Paper.prop_tower_kernel`.

:::proposition "prop_tower" (lean := "Paper.prop_tower, Paper.prop_tower_representatives") (parent := "part-contracting")
*Proposition H.1 of the paper* (tower; page 44), quoted: “Let $`n \ge 1` and $`M = |G_n|`. There
are $`G_n`-sets $`V_0 = G_n, V_1, \ldots, V_J`, with equivariant projections
$`\pi : V_j \to V_{j+1}` that are $`b` to one, such that

(a) for every $`i \in \mathbb{Z}/h` the $`X_k`, $`k \ne i`, generate a copy of $`U_h` (with
$`X_{i+1}, \ldots, X_{i-1}` as the generators in order), which acts freely on every $`V_j`; we
call its orbits _cosets of type_ $`i`;

(b) $`c` and $`X_i c` always lie in different cosets of type $`i`, and $`\pi` maps every coset of
type $`i` bijectively onto one, exactly $`b` of them onto each;

(c) $`|V_J| < b\,|\mathrm{SL}_h(\mathbb{F}_2)|` and $`|G_{n+1}| = 2^{h^2-1} |G_n|`; thus
$`|V_J| \le \mathrm{const}`, and $`M` runs through a sequence with bounded quotients as $`n`
varies;

(d) every element of $`G_n` is a word of at most $`\mathsf{L} = O((n+1)^7)` letters $`X_k` (the
proof gives the exponent $`3`; we state $`7` as in the formal development).”

*The exponent in (d).* The printed statement already carries the exponent of the Lean theorem.
The formalization note after the proof (page 44), quoted: “The exponent $`7` in part (d) is the
one that is proved in the Lean development; the argument above gives the exponent $`3`.” So for
(d) the statement that Lean proves is weaker than what the printed argument yields, and the
exponent $`3` rests on the printed argument alone. The last conjunct of `prop_tower` is: there is
a natural number $`C`, depending on $`h` only, such that for every $`n` every element of $`G_n` is
the product of a list of at most $`C (n+1)^7` generators. In the proof of Theorem H.2 the number
$`\mathsf{L}` enters the bound $`n_0 = 4\mathsf{L}(N + M^2)` and the term $`\Lambda N` of part
(e), and the proof uses of it that “$`\mathsf{L}` is at most a power of $`\lg M`” (page 47),
which holds with either exponent.

*The other differences.* Section Q.3 (page 68): “In Proposition H.1, the set $`V_0` is only stated
to have as many elements as $`G_n`, bijectivity on cosets is stated as equivariance and freeness,
and the cosets over a coset are given by representatives (`prop_tower_representatives`: there is
exactly one in each coset). Lean states the proposition for every $`h \ge 3` and every
$`n \ge 0`.”

*Reading of the Lean statement (gloss), conjunct by conjunct.* `XX h n j` is $`V_j`, defined as
the quotient of $`G_n` by the $`j`th subgroup of a chain in $`K_n`; `pr` is $`\pi`; `JJ h n` is
$`J`, the number $`\lfloor (h^2-1)n / \mathrm{ee}(h) \rfloor` with
$`\mathrm{ee}(h) = h(h-1)/2`; `th i` is a homomorphism $`U_h \to G_n`; `VV h n j i` is the set of
the elements of $`V_j` whose coordinate of type $`i`, an element of $`U_h`, is $`1`.

* $`|V_0| = |G_n|`.
* For $`j < J`: every fibre of $`\pi : V_j \to V_{j+1}` has $`2^{\mathrm{ee}(h)} = b` elements,
  and $`\pi` is equivariant.
* For every $`i`: `th i` is injective and sends the generator $`x_l` of $`U_h` to $`X_{i+1+l}`;
  on every $`V_j` its image acts freely; no element of the orbit of $`c` under this image equals
  $`X_i c`; and $`\pi` commutes with it. This is (a), and the first half of (b), with “bijectively
  onto one” in the form: equivariant, and both actions free.
* For every $`i`: every $`k \ne i` is of the form $`i + 1 + l`; every subgroup of $`G_n` that
  contains the $`X_k`, $`k \ne i`, contains the image of `th i`; and for $`j < J` every element of
  `VV h n (j+1) i` is the image of exactly $`b` elements of `VV h n j i`. By
  `prop_tower_representatives` every coset of type $`i` contains exactly one element of `VV`, so
  the last clause is “exactly $`b` of them onto each”.
* $`|V_J| < |\mathrm{SL}_h(\mathbb{F}_2)| \cdot b` and $`|G_{n+1}| = |G_n| \cdot 2^{h^2-1}`.
* The clause on words, described above.
:::

:::proof "prop_tower"
*The paper's proof* (page 44), summarised. The sets are $`V_j = G_n/\Gamma_j` for a chain of
subgroups $`\{1\} = \Gamma_0 \subset \cdots \subset \Gamma_J` of $`K_n`, each of index $`b` in the
next, with $`[K_n : \Gamma_J] < b`, “which is possible in a $`2`-group”. (a): conjugation by the
matrix $`P` with $`Pe_k = e_{k+1}` for $`k \ne h-1` and $`Pe_{h-1} = \varsigma^{-1} e_0` is an
automorphism of $`G_n` that maps $`K_n` to itself and $`X_k` to $`X_{k+1}`; so each of the $`h`
groups is the image of $`U_h` under a power of it, meets the normal subgroup $`K_n` trivially, and
acts freely because the stabilizers of the points of $`V_j` lie in $`K_n`. (b): modulo $`s` the
element $`X_i` is not in the group generated by the others, because of its entry $`(i-1, i)`; the
rest is counting. (c): $`|V_J| = |\mathrm{SL}_h(\mathbb{F}_2)|\,[K_n : \Gamma_J]`. (d): the
commutator rule for elementary matrices gives, from $`U_h` and $`X_0`, all $`e_{jk}(\varsigma)` by
words of bounded length and all $`e_{jk}(\varsigma^a)` by words of length $`O(a^2)`; the powers
$`\varsigma, \ldots, \varsigma^{n+1}` span $`R_n`; and Gaussian elimination over the local ring
$`R_n` writes every matrix of $`G_n` as a product of boundedly many elementary matrices. “This
gives words of length $`O((n+1)^3)`, which is stronger than (d).”

_In Lean._ The chain is `Nc.Tower.exists_chain`, by Sylow's theorem in the $`2`-group $`K_n`. The
bound on words is `Nc.Tower.exists_diam`, proved by induction on $`n`. This blueprint read its
statement and not its proof, and cannot say at which step the Lean argument is coarser than the
printed one. On the origin of the groups the paper says (page 44): “These groups, with the
subgroups generated by all but one of the $`X_k`, are close to those of the coset complexes of
Kaufman and Oppenheim”.
:::

The paper fixes one more piece of data (page 44), quoted: “An _edge of type_ $`i` of $`V_j` is a
pair $`\{c, X_i c\}`, and the edges inside a coset of type $`i` are those of the other types. For
each coset $`\omega` of type $`i` of $`V_{j+1}` we fix a bijection $`\chi \mapsto \hat\chi` from
the $`b` cosets of type $`i` of $`V_j` over $`\omega` to the $`b` elements of $`\omega`.” In Lean
these data, with those of the proposition, are assembled into a term `Nc.Tower.tower` of a
structure `Nc.Tow.Tower`, whose field `host` is $`\chi \mapsto \hat\chi`; the Lean proof of Theorem
H.2 is written for an arbitrary term of that structure, with routes on its bottom level, and uses
the groups of this section only through this term and through the words of part (d)
({bpref "tree_towers"}[the towers of the proof]). Section Q.3 (page 70): “Theorem H.2 uses parts (a) and (b) of Proposition H.1 through the
named theorems that also prove the proposition.”

# H.2. Packets, networks and the two moves

:::definition "network_value" (lean := "Paper.NetUnit, Paper.NodeTable, Paper.netValue") (parent := "part-contracting")
*Packets and networks* (page 45), quoted: “From now on wires are moved in _packets_, strings of
$`\ell` bits for a fixed $`\ell \ge 1`. A string $`w` is written on packets as $`w10 \cdots 0`, so
it takes $`\lfloor |w|/\ell \rfloor + 1` of them, and $`w` can be recovered from them. A _network_
on a finite set of nodes assigns a number of packets to every pair of nodes, and to each node a
_node tensor_, a function, with values in a ring, of the bits of the packets at this node. Its
_value_ is the sum, over all contents of all packets, of the product of the node tensors.”

In Lean a network on the nodes `Fin AA` is given by numbers `n a c` of packets and, for every
node `a`, a table `tab a` of the contents of the packets at `a`; `netValue tab` is its value.
Section Q.3 (page 69): “Packets have a direction in Lean, and packets from a node to itself are
allowed and stay at their node.” So `n a c` counts the packets from `a` to `c`, the packets at `a`
are those from `a` and those to `a`, and a packet from `a` to `a` is one packet. The writing of a
string on packets is `Nc.unitsOf`, with `Nc.ucount` for the number
$`\lfloor |w|/\ell \rfloor + 1`.
:::

:::definition "relay" (lean := "Nc.Tow.relay") (parent := "part-contracting")
*Definition of the paper* (relay; page 45), quoted: “A _relay_ through a node $`w` replaces a
packet between two other nodes $`x` and $`y` by a packet between $`x` and $`w` and one between
$`w` and $`y`, with a test at $`w` that these two are equal. It leaves no copy of the old packet,
as the node tensors of $`x` and $`y` read the new packets instead.”

In Lean a relay is not a separate kind of move. Section Q.3 (page 68): “A relay is a law with one
slot, two channels, one index and $`\lambda = 0`, applied to a batch of packets. Thus relays too
have outcomes and leave copies and dead packets at the ends of their strings, an outcome of a
relay is good if it equals the number of packets of the batch on both channels”. The term `relay`
is that law: three roles $`0, 1, 2`; one slot with the ends $`0` and $`2`; channels from $`0` to
$`1` and from $`1` to $`2`, of one bit each; and tables that test equality. So a Lean relay of a
batch of $`t` packets differs from $`t` printed relays in two respects: the old packets remain as
copies at their two ends, over which these nodes sum, and each of the two channels receives
$`t + 1` packets, the last of which holds only the end mark of the string.
:::

:::definition "law_move" (lean := "Nc.G.Sys, Nc.G.Uid, Nc.G.Plan, Nc.G.Plan.Ok, Nc.G.Plan.Poss, Nc.G.role, Nc.G.partyTab") (parent := "part-contracting")
*Definition of the paper* (law move; page 45), quoted: “Let $`\omega` be a coset of type $`i` in
some $`V_j` whose elements are nodes of a network, identified with $`U_h` by $`g \mapsto g z_0`
for one of its elements $`z_0`, so that the edges of $`U_h` become edges $`\{c, X_k c\}`. Let a
law and a number $`t \in \mathbb{N}` be given, and let $`t` packets of the network be given to
every slot of the law, where slots that are not full get packets of zeros. The _law move_ uses up
these packets and applies (G.2) to each of the $`t\ell` _layers_ of bits. By the convention of
Section G, every channel then holds a string of $`t\ell` blocks, each of which is the code of an
index followed by its bits. The string of every channel $`e` is written on $`o_e + 1` new packets,
where $`o_e = \lfloor (\text{length of the string})/\ell \rfloor`, and the vector $`o = (o_e)` is
called the _outcome_.

A packet that is used up leaves one copy at each of its two ends, and each of the two nodes sums
over its own copy. The node tensor of the law move at an element of $`\omega` is the sum, over one
index for each layer and over the bits of its channels in each layer, of the products of the node
tensors of the law, restricted to those choices whose strings are the contents of the new
packets.”

*Reading of the Lean definitions (gloss).* Moves are described once for all inputs, and what
happens in them is a function of the inputs.

* `Sys F (A + A') E` is a list of `E` moves on the nodes `Fin (A + A')`: every move `x` has a law
  `kind x` and an injective map `part x` from the roles of that law to the nodes. The first `A`
  nodes are those of the given network.
* `Uid` is the type of the names of packets: `init a b k` is packet number `k` from the given
  node `a` to the given node `b`, and `new ν k` is packet number `k` on the channel `ν` of a move.
  A content is an element of `UW ℓ`, that is, `none` (the packet is absent) or a string of
  $`\ell` bits.
* The inputs are the numbers `n a b` of given packets and an _outcome_ `o ν` for every channel
  `ν` of every move. The packets that exist are `init a b k` with `k < n a b` and `new ν k` with
  `k ≤ o ν` (`Plan.seenAt`); so a channel with the outcome $`o_e` has $`o_e + 1` packets.
* A `Plan` gives, as functions of `(n, o)`: the set `cons z` of packets given at each slot `z` of
  each move, the number `num x` of the move (the paper's $`t`), and a predicate `good x`.
  `Plan.Ok cap` holds the rules: `cons` and `num` of a move depend only on the outcomes of earlier
  moves, and `good` on those up to the move; the packets given at a slot are current, that is,
  exist and have not been given before (`Plan.cur`), and join the two nodes at the ends of the
  slot; different slots of a move get disjoint sets; a slot gets at most `num x` packets; and
  `num x ≤ cap`.
* `role` is the node tensor of the law move at a role `p`, as a function of the copies at the node
  of `p`: it is $`0` unless all the packets given at the slots of `p` are present, and then it is
  the sum, over an index for each of the `num x`·$`\ell` layers and over the bits of the channels
  at `p` in each layer, of the product over the layers of the tables of the law, restricted to the
  choices for which, on every channel at `p`, the string (`chString`) occupies exactly `o ν + 1`
  packets and these are the node's copies of the packets `new ν k`. Slots that are not full are
  filled with zeros (`slotBits`). This is the printed node tensor, with the outcome as a
  parameter.
* `partyTab` is the node tensor of a node after all moves: its initial table times the product of
  `role` over the roles that the moves give to this node.
* `Plan.Poss` says that an outcome can occur: for some choice of an index for every layer,
  `o ν` is $`\lfloor \sum_{\text{layers}} (\lambda + \mathrm{len}_{i,\nu}) / \ell \rfloor` on
  every channel `ν` of the move.
:::

:::lemma_ "thm_tree_moves" (lean := "Paper.thm_tree_moves, Paper.thm_tree_move") (parent := "part-contracting")
*The moves do not change the value* (page 45), quoted: “Thus a law move replaces a network by a
sum, over outcomes, of networks with $`o_e + 1` packets on the channel $`e`, whose node tensors
check the codes, and the value does not change because each choice of indices and bits belongs to
exactly one outcome.” And: “Every outcome that can occur is good, by Theorem G.2(b), the triangle
inequality over the $`t\ell` layers, and $`\lambda \ge 1`, so the sum may be restricted to good
outcomes.”

*Reading (gloss).* `thm_tree_moves` is stated for an arbitrary system of moves and an arbitrary
plan that obeys `Plan.Ok cap` and for which every possible outcome is good, with a bound `U1` for
outcomes that leaves room for the strings (`cap * (m x + lam) + 1 ≤ U1` for a bound `m x` on the
loads $`\mathrm{len}` of the law of the move `x`). For initial node tensors `init a` that depend
only on, and vanish unless they have, the node's copies of its given packets, it states
$$`\mathrm{val}_0 \;=\; \sum_{o \text{ good}} \mathrm{val}_{\mathrm{end}}(o),`
where the sum runs over the outcomes for which all moves are good, $`\mathrm{val}_0` is the value at the start (`posVal` with the given packets, all current)
and $`\mathrm{val}_{\mathrm{end}}(o)` is the sum, over the contents of the copies of all packets
that exist for `o`, with the two copies of every current packet equal, of the product of the
tables `partyTab`. `thm_tree_move` is the same for one move, and it rests on the identity
`Nc.G.move_identity` for one law. Nothing here refers to towers; the paper's two moves are the two
kinds of laws to which it is applied.
:::

:::lemma_ "thm_tree_good" (lean := "Paper.thm_tree_good, Paper.goodBound") (parent := "part-contracting")
*Good outcomes* (page 45), quoted: “We call an outcome of a law move with the number $`t` _good_
if $`\|o\|_* \le \sqrt{C_1}\, a_1 t` and $`o_e \ge t` for all channels $`e`.”

Section Q.3 (page 69): “Whether an outcome is good is tested with the integer
$`\lfloor 2C_1a_1^2 \rfloor` (`thm_tree_good`). This implies the printed notion and is equal to it
when $`2C_1a_1^2` is an integer, as the laws provide.” In the structure of
{bpref "thin_trees"}[the next section] an outcome of a law move is good if
$`b \sum_\nu o_\nu^2 \le G_1 t^2` and $`t \le o_\nu` for every channel, with
$`G_1 =` `goodBound C₁ a₁` $`= \lfloor 2C_1a_1^2 \rfloor`. The theorem states both directions of
the quotation; the integrality that the second needs is the last clause of
{bpref "exists_laws"}[`exists_laws`].
:::

The paper closes the section with a remark that carries the whole count (page 45), quoted: “The
numbers of packets in the new networks depend only on the outcomes, never on the contents of
packets, and all bounds below follow from such numbers.” In Lean this is the form of a `Plan`: its
three components are functions of `(n, o)` alone.

# H.3. The decomposition theorem

The idea, in the paper's words (page 45), quoted: “Of the $`h` types of edges of $`V_j`, only the
packets on the least loaded one travel on to $`V_{j+1}`, whereas all others end at a parent
(Figure 11). Rerouting the former multiplies their load by a factor that does not depend on $`h`,
so by (G.1) the load, in a quadratic norm, is halved at every stage, while the number of elements
falls by the constant factor $`b`, and this gives the factor $`M^{-\gamma}`. Different outcomes of
the law moves give different trees. Parts (c), (d) and (e) of the theorem are needed only in
Section J and can be skipped at first reading.”

:::theorem "thm_tree" (lean := "Paper.thm_tree") (parent := "part-contracting")
*Theorem H.2 of the paper* (decomposition into tree networks; pages 45–46), quoted: “There is a
constant $`C` with the following property. Let $`M \ge 2`, let $`\ell, N \ge 1`, and let a network
over a commutative $`A`-algebra, with packets of $`\ell` bits, have at most $`M` nodes, no packet
from a node to itself, and at most $`N` packets at each node. Its value is the sum, over a set of
choices $`\mathbf{o}`, each of which is a sequence of good outcomes, of the values of networks
with the following properties. Put $`\Lambda = (\lg M)^C`, where
$`\lg M = \lfloor \log M \rfloor + 1`, and $`\gamma = 1/\log b`.

(a) The nodes form a rooted tree of depth at most $`\Lambda`, by stages: the given nodes are of
stage $`0`, every node but the root has its parent in the next stage and at most $`b` children,
and the root has at most $`C` children.

(b) A set of at most $`M^C` named packets, the _dead_ ones, may join any two nodes, and not all of
them need be present. All other packets join a node and its parent. Their number is at most
$`\Lambda M^{1-\gamma}(N + M^2)` for one node, its children included, and at most
$`\Lambda M (N + M^2)` in all.

(c) The node tensor of a node is the given one (or $`1`) times the node tensors of the moves at
it, summed over the packets that they have used up. At stage $`0` these are tests only. Elsewhere
they are tests and entries of node tensors of laws, and the numbers of layers of the law moves at
a node add up to at most the number of bits of all packets that it ever holds.

(d) The parents, the packets of the new network, the packets and numbers of the moves, and which
outcomes are good are computed from $`\mathbf{o}` and the given numbers of packets by a
straight-line program with at most $`(MN)^C` steps on numbers below $`(MN)^C`. A step is an input,
a constant, or an arbitrary function of two earlier results, given by its table (a _binary
operation_). The program does not depend on the numbers of packets, the outcomes or the node
tensors. The numbers of nodes, of moves and of packets that can occur are at most $`(MN)^C` as
well.

(e) The program also computes for every node $`p` a number $`u_p` that bounds the number of
packets, other than dead ones, between $`p` and its parent. The bounds of (b) hold with these
numbers in place of those packets: $`u_p` and the numbers $`u_q` of the children $`q` of $`p` add
up to at most $`\Lambda M^{1-\gamma}(N + M^2)`, and all $`u_p` together to at most
$`\Lambda M (N + M^2)`. The number of all packets that a node $`p` ever holds is at most a
constant times the sum of $`u_p`, of the numbers $`u_q` of its children $`q`, and of the number of
dead packets at $`p`, present or not, and $`\Lambda N` more if $`p` is a given node. Here the
packets that are used up at $`p`, by relays as well as by law moves, and the zeros in slots are
counted too.”

*The formalization note* (page 46), quoted: “For part (d), and for the numbers $`u_p` of part (e),
the proof below only describes the straight-line program and accounts for its size. That the
program computes exactly what is claimed is proved in the Lean development (Appendix Q), and so
are the details of the count in part (e).”

*The Lean statement.* Section Q.3 (page 68): “Theorem H.2 and Proposition J.2 state their clauses
as the fields of structures.” The theorem `thm_tree` states: for a commutative ring `A`, a number
$`h \ge 3`, and laws `VL : VLaws A cNear dNear 1 (2 ^ ee h)` with $`1 + 8C_1 \le h/4`
({bpref "exists_laws"}[the standing hypothesis]), there is a natural number $`C` such that for
every commutative `A`-algebra `R` and all `M`, `AA`, `N`, `ℓ` with $`2 \le M`,
$`\mathtt{AA} \le M`, $`1 \le N`, $`1 \le \ell` the structure
`ThinTrees R laws AA N ℓ M b G₁ C γ` has a term, where `laws` is the list of the laws of `VL`
mapped to `R`, $`b = 2^{\mathrm{ee}(h)}`, $`G_1 = \lfloor 2C_1a_1^2 \rfloor` and
$`\gamma = 1/\log_2 b`. Here `AA` is the number of given nodes. Everything that the theorem says
about networks is in {bpref "thin_trees"}[the fields of that structure], which the next node
reads one by one.

What the Lean statement does not have of the printed hypotheses: the condition “no packet from a
node to itself” is dropped (such packets are allowed and stay), and “at most $`N` packets at each
node” is a hypothesis of the individual fields, in the form $`\sum_c (n_{a,c} + n_{c,a}) \le N`
for every given node $`a`. The constant $`C` depends on $`h` and on the laws, as in the paper,
where “all constants below depend only on these choices” (page 43).
:::

:::definition "thin_trees" (lean := "Paper.ThinTrees") (parent := "part-contracting")
*The structure that carries the clauses of Theorem H.2.* The paper has no counterpart of this
definition; it is the Lean form of the words “networks with the following properties” of the
theorem. Everything in this node is a reading (gloss) of the Lean source on the right, and no
machine has checked the reading.

*Data.* A term consists of: the number `A'` of further nodes (the nodes are `Fin (AA + A')`, the
given ones first); the number `E` of moves; a bound `U1 > 0` for outcomes; the moves `sys` and the
plan `plan` with a bound `cap` and the rules `ok : plan.Ok cap`
({bpref "law_move"}[the definition of a move]); a function `stage` on the nodes, a number `depth`
and a node `root`; and, as functions of the inputs, the parent `par n o p` of a node, a number
`up n o p`, and a set `dead o` of names of packets; and a flag `isLaw x` for every move. The
inputs are `n : Fin AA → Fin AA → Fin (N + 1)`, the numbers of given packets, and
`o : sys.N → Fin U1`, an outcome below `U1` for every channel of every move. A choice
$`\mathbf{o}` of the printed theorem is an `o` with `plan.good n o x` for every move `x`.

Three sets of packet names recur below. `Plan.seenAt n o E` is the set of all packets that exist
for `(n, o)`. `plan.cur n o E` is the set of those that are current after the last move. The
packets of the tree, written $`\mathcal{T}(n, o)` here, are the current packets that are not in
`dead o` and whose two holders are different nodes
(`cutUnits … id (plan.cur n o E \ dead o)`). “`p` holds `u`” is `Holds … p u`. The clauses that
bound numbers of packets assume that every given node has at most `N` packets and that all moves
are good (`dead_le` assumes neither, `layers_le` only the second); this is not repeated.

*Clause (a).* `depth_le`: `depth` $`\le (\lg M)^C`. `stage_le`, `stage_root`: every stage is at
most `depth`, with equality exactly at the root. `stage_given`: the given nodes have stage $`0`.
`stage_par`: for $`p \ne` `root` the stage of `par n o p` is that of `p` plus one, for all inputs.
`children_le`, `root_children_le`: a node other than the root is the parent of at most `b` nodes,
and the root of at most `C`. The tree structure consists of these statements; the parent depends
on the inputs, the stages do not.

*Clause (b).* `dead_le`: `dead o` has at most $`M^C` elements. `edge`: every packet of
$`\mathcal{T}(n, o)` joins some $`p \ne` `root` and `par n o p`. `node_le`: the number of packets
of $`\mathcal{T}(n, o)` that a node holds is at most $`(\lg M)^C M^{1-\gamma}(N + M^2)`; since a
packet of the tree at $`p` joins $`p` to its parent or to a child, this is the printed bound “for
one node, its children included”. `total_le`: $`\mathcal{T}(n, o)` has at most
$`(\lg M)^C M (N + M^2)` elements. On the dead packets, Section Q.3 (page 69): “As printed in (b)
and (e), the dead packets are a set of names that are not all stated to be present, so that the
bound on what a node ever holds may count absent ones. The end packets of relays count as dead,
and in networks without these packets they would count among the absent ones.”

*Clause (c).* `value`, for every network `tab` on the given nodes with the numbers `n`:
$$`\mathtt{netValue\ tab} \;=\; \sum_{o \text{ good}} \; \sum_{w} \; \prod_{p} \mathrm{val}_p(w).`
Here $`o` runs over the outcomes for which all moves are good, $`w` assigns a content, present or
absent, to every packet name and is absent outside the
current packets with two different holders, and $`\mathrm{val}_p(w)` (`groupVal`, with every node
a group of its own) is the sum, over the contents of the copies at $`p` of all packets that $`p`
has ever held, equal to $`w` on the current packets that $`p` shares with another node, of the
table `partyTab` of $`p`: the given table of $`p` (`startTab`: for a given node the table `tab`
applied to its given packets, and $`0` if one of them is absent; for a further node $`1`) times
the node tensors `role` of the moves at $`p`. This is the first sentence of (c), with the sum over
used-up packets inside $`\mathrm{val}_p`. Section Q.3 (page 69): “The value of a tree is written
as a sum, over the contents of named packets, present or absent, of products of the values of its
nodes, and no theorem restates this as the value of a network as defined in Section H.” To this
blueprint's reading of `role` and `startTab`, a term of the inner sum in which a current packet is
absent at a node that holds it vanishes, because both definitions test presence; this was not
checked beyond reading the two definitions. `kinds`: the law of a move `x` is in the list `laws`
if `isLaw x`, and is the law `relay` otherwise. `law_stage`: the nodes of a law move have positive
stage; with `stage_given` this is “At stage $`0` these are tests only”. `layers_le`: for every
node $`p`, the numbers `num` of the law moves in which $`p` has a role add up to at most the
number of packets in `Plan.seenAt n o E` that $`p` holds; multiplied by $`\ell` this is the last
sentence of (c). `good_iff`: a law move is good if $`b \sum_\nu o_\nu^2 \le G_1 t^2` and
$`t \le o_\nu` for all its channels, and a relay if $`o_\nu = t` on both channels, $`t` being
`plan.num n o x`. `poss_good`: every possible outcome (`Plan.Poss`) is good.

*Clause (d).* `computed`: there are numbers `D` and `steps`, input maps `inp`, and a set `H` of
functions from the inputs `(n, o)` to $`\mathbb{N}`, such that `D`, `steps`, the number `AA + A'`
of nodes, the number `E` of moves, `U1` and the number of packet names are all at most
$`(MN)^C`; `inp` gives each $`n_{a,c}` and each $`o_\nu` as an element of `Fin D`;
`SlpN inp steps H` holds; and `H` contains, for all nodes `p`, `q`, packet names `u`, slots `z` and moves `y`:
the indicator of `par n o p = q`; the indicator of `u ∈ plan.cur n o E`; the indicator of
`u ∈ plan.cons n o z`; the number `plan.num n o y`; the number `up n o p`; and the indicator of
`plan.good n o y`. `SlpN inp steps H` ({bpref "tree_computed"}[shown below]) says that there is a
sequence of functions from the inputs to `Fin D`, each of whose first `steps` members is an input,
a constant, or $`\varphi(f_i, f_j)` for two earlier members and an arbitrary
$`\varphi :` `Fin D → Fin D → Fin D`, such that every function in `H` is, at every input, the
value of one of them. The program is fixed before the inputs: this is “does not depend on the
numbers of packets, the outcomes”; node tensors do not occur in it. Section Q.3 (page 69): “The
programs may depend on $`M`, $`N`, $`\ell`, the ring of the network and the bound on the number of
given nodes”. The equalities hold for all inputs, good or not.

*Clause (e).* `between_le`: for $`p \ne` `root`, the number of packets of $`\mathcal{T}(n, o)`
that join $`p` and its parent is at most `up n o p`. `up_node`: `up n o p` and the numbers
`up n o q` of the children `q` of `p` add up to at most $`(\lg M)^C M^{1-\gamma}(N + M^2)`.
`up_total`: all `up n o p` add up to at most $`(\lg M)^C M (N + M^2)`. `copies_le`: for every node
$`p`,
$$`\begin{aligned} &\#\{u \in \mathtt{seenAt} : p \text{ holds } u\} + \sum_{r \text{ a role at } p} (1 + s_r)\, t_r \\ &\quad \le\; C \Bigl(u_p + \sum_{q \text{ child of } p} u_q\Bigr) + \bigl[p \text{ given}\bigr] (\lg M)^C N \\ &\qquad + C \cdot \#\{u \in \mathtt{dead}\ o : p \text{ holds } u\}, \end{aligned}`
where $`t_r` is the number `num` of the move of the role $`r` and $`s_r` the number of slots of
its law at $`r`. Section Q.3 (page 69): “In part (e) Lean has the constant $`C` of the theorem,
and it counts for every move at $`p`, with the number $`t`, also $`t` times one plus the number of
its slots at $`p`, which covers the zeros in slots.”
:::

:::proof "thm_tree"
*The paper's proof* (pages 46–48), summarised; the formalization note quoted above applies to its
last part.

_Reduction and start._ Take the least $`n \ge 1` with $`M \le |G_n|`, so that $`|G_n| = O(M)` by
Proposition H.1(c); adding nodes with node tensor $`1` and no packets, assume $`M = |G_n|` and
place the given nodes at the elements of $`V_0 = G_n`. The nodes of the new networks are the
elements of all $`V_j`, those of $`V_j` forming the stage $`j`, and a root. The packets of each
pair $`(\alpha, \beta)` of given nodes are divided into $`M` batches, of equal size up to one, one
for every $`g \in G_n`, and the batch of $`g` is led by relays from $`\alpha` to $`g` along the
word for $`g\alpha^{-1}` and on to $`\beta` along the word for $`\beta g^{-1}`, stopping at the
first visit of $`\beta`. Since for a fixed word all its translates use each edge at most twice for
each of its letters, every edge gets at most $`n_0 = 4\mathsf{L}(N + M^2)` packets.

_Loads._ For numbers $`n_e` of packets on the edges of $`V_j` let
$`N_i^2 = \frac{|V_j|}{2} \sum_{e \text{ of type } i} n_e^2` and $`Q_j^2 = \sum_i N_i^2`, so that
$`Q_0 \le \sqrt{h}\, M n_0`.

_One stage._ Let $`i` be the first type for which $`N_i` is least, so that
$`N_i^2 \le Q_j^2/h`. Every element $`c` of a coset $`\chi` of type $`i` gets the parent
$`\hat\chi`. A packet on an edge inside $`\chi` is relayed through $`\hat\chi`, which gives two
packets between nodes and their parent. A packet on an edge $`cc'` of type $`i`, with cosets
$`\chi, \chi'`, is relayed along $`c, \hat\chi, \pi c, \pi c', \hat\chi', c'`. The middle segments
$`\pi c\, \pi c'` lie on edges of type $`i` of $`V_{j+1}`, and the new $`N_i` is at most the old
one. The outer segments $`\hat\chi\, \pi c` lie inside the cosets $`\omega = \pi\chi` of type
$`i` of $`V_{j+1}` and give each $`\omega` a load $`n_\omega` on its pairs, with
$`\frac{|V_{j+1}|}{b} \sum_\omega \|n_\omega\|^2 \le 4N_i^2`. In each $`\omega` a law move is
applied to the outer segments, with the first law that has $`n_\omega \le t\sigma` for the least
possible $`t`, so that $`t \le \|n_\omega\|/a_1 + 1` by Theorem G.2(a). For a good outcome the new
load on the channels of $`\omega` has $`\|o_\omega\|_* \le \sqrt{C_1}(\|n_\omega\| + a_1)`; the
last of the $`o_e + 1` packets on a channel is not counted, “because it is never moved again, and
these end packets are the dead packets of (b)”. The channels of $`\omega` are its edges of the
types $`k \ne i`, and by Minkowski's inequality and (G.1), with $`C_2 = \sqrt{C_1}\, a_1/b`,
$$`\begin{aligned} Q_{j+1} &\le (1 + 4C_1)^{1/2} N_i + C_2 |V_{j+1}| \\ &\le \tfrac12 Q_j + C_2 |V_{j+1}|. \end{aligned}`
As $`b \ge 4`, this gives $`Q_j \le 2^{-j} \bar Q` with $`\bar Q = O(M n_0)`. After stage $`J`
every packet on an edge of $`V_J` that is not dead is relayed through the root.

_Bounds._ $`J = O(\log M)` gives (a). By the Cauchy–Schwarz inequality over its $`h` edges, an
element of stage $`j` has towards its parent at most
$`(2h/|V_j|)^{1/2} Q_j \le C (\sqrt{b}/2)^j M^{-1/2} \bar Q` packets, which is largest for
$`j = J`, and $`2^{-J} = O(M^{-\gamma})` since $`M = O(b^J)`; this gives (b) for one node and its
boundedly many children, “as $`\mathsf{L}` is at most a power of $`\lg M`”. All elements of stage
$`j` together have at most $`2\sqrt{h}\, Q_j` packets towards their parents, which gives the
total. There are at most $`hM` law moves, with boundedly many dead packets in each. For (c), the
elements of $`V_0` take part in relays only, and $`t \le o_e` for every channel at a node.

_Parts (d) and (e), as printed._ For (e), $`u_p` is the sum of the loads on the edges at $`p`, and
$`0` for the root; what a node ever holds in the stages is at most a constant times the loads at
it and at its children, and its dead packets; and in the start the end $`\beta` of a given packet
holds at most $`2\mathsf{L}` packets one after another, the term $`\Lambda N`. For (d), “the
groups, the words, the cosets and the maps $`\chi \mapsto \hat\chi` are constants of the program,
and all loads are $`(MN)^{O(1)}`. Finding the least $`N_i` and the least $`t`, and testing whether
an outcome is good, amounts to comparing integers of that size, because $`C_0'` is an integer.
Packets are assigned to batches, slots and channels by their number in a fixed order.” The rest
of the printed proof counts relays and packets, each $`(MN)^{O(1)}`.
:::

# The Lean construction behind Theorem H.2
%%%
tag := "laws-lean-construction"
%%%

The paper's note says that for parts (d) and (e) the printed proof “only describes the
straight-line program and accounts for its size”. This section says what the Lean development
has in the place of that description. It is this blueprint's account of the files
{repoFile "vp-vnp/Paper/Tree.lean"}[`Paper/Tree.lean`], `Nc/G/*.lean`, `Nc/Tow/*.lean` and
{repoFile "vp-vnp/Nc/SlpCalc.lean"}[`Nc/SlpCalc.lean`], and it is a gloss throughout: the Lean
statements shown beside the nodes are what is proved, and the prose is a reading of them.

*What was read and what was not.* Read in full: the definitions shown in this chapter, the
structure `ThinTrees`, the statements of the theorems named below, and the proofs of
`Paper.thm_tree` and `Paper.exists_thinTrees`, which assemble the fields. Read as statements only:
the theorems on loads (`Nc/Tow/Load*.lean`), on the packets at the end and on copies
(`Nc/Tow/End*.lean`, `Nc/Tow/Ever*.lean`), on the rules (`Nc/Tow/Ok.lean`), on one move
(`Nc/G/Move.lean`), and the stages of the program (`Nc/Tow/Slp*.lean`). Their proofs, about nine
thousand lines in `Nc/Tow` alone, were not read. Where the account below says how a proof goes, it
describes which statements are combined, as the statements and the assembling proofs show it.

*The architecture.* The Lean proof separates three things that the printed proof treats together.
First, a calculus of moves for arbitrary laws and arbitrary plans, in which the invariance of the
value is proved once ({bpref "thm_tree_moves"}[`thm_tree_moves`]). Second, one particular plan,
the _tower plan_, defined for an abstract tower (a term of `Nc.Tow.Tower`) with routes on its
bottom level (`Nc.Tow.Routes`) and laws at its vertices (`Nc.Tow.FlagLaws`), and analysed under
numerical hypotheses collected in `Nc.Tow.TCst`. Third, the towers of Proposition H.1. The
theorem `Paper.exists_thinTrees` builds a term of `ThinTrees` from the second, and
`Paper.tree_towers` supplies the third.

:::definition "tower_plan" (lean := "Nc.Tow.RM, Nc.Tow.tri, Nc.Tow.Tg, Nc.Tow.tgR, Nc.Tow.Mv, Nc.Tow.timeM, Nc.Tow.alvN, Nc.Tow.ld, Nc.Tow.IsMin, Nc.Tow.Fits, Nc.Tow.tmin, Nc.Tow.Pick, Nc.Tow.numF, Nc.Tow.numS, Nc.Tow.num, Nc.Tow.GoodMv, Nc.Tow.consM, Nc.Tow.plan") (parent := "part-contracting")
*The tower plan: the construction of Theorem H.2 as Lean defines it* (gloss). The paper describes
the construction in the proof of the theorem (pages 46–47); it has no numbered counterpart. In
Lean the list of moves is fixed, and only the numbers of packets in them depend on the inputs.

_Nodes._ The nodes are the elements (“chambers”) of all levels $`V_0, \ldots, V_J` and a root
(`Nc.Tow.Nd`). The given nodes are embedded in $`V_0`; the other elements of $`V_0` are further
nodes with the table $`1`.

_Moves._ `Mv` is the type of all moves: the relays `RM` that exist (`okR`), and one law move for
every stage $`j < J`, every type $`i`, every coset of type $`i` of $`V_{j+1}` and every law of the
family. Section Q.3 (page 68): “there is a law move for every stage, type, coset and law, with
$`t = 0` for those not chosen.” The relays are of four kinds, with the three nodes `tri`:

* `start a c γ s`: step $`s` of the path of the batch $`\gamma \in V_0` of the pair of given
  nodes $`(a, c)`, for $`s < 2m`, where $`m` bounds the length of the routes. The third node of
  the relay is $`c`.
* `inn j i e`, for an edge $`e` of stage $`j` whose type is not $`i`: through the parent
  $`\hat\chi` of the coset of type $`i` that contains $`e`.
* `mid j e s`, $`s < 4`, for an edge $`e = cc'` of stage $`j`: the four relays along
  $`c, \hat\chi, \pi c, \pi c', \hat\chi', c'`, each with $`c'` as its third node; a step is left
  out if its two first nodes coincide.
* `fin e`, for an edge of stage $`J`: through the root.

_Schedule._ `timeM` gives every move a time, and the moves are numbered in an order that is
monotone in time: `start … s` at time $`s`; at stage $`j`, with $`\tau_j = 2m + 6j`, the relays
`inn` at $`\tau_j`, the relays `mid … s` at $`\tau_j + s`, the law moves at $`\tau_j + 4`; and
`fin` at $`2m + 6J`.

_Targets._ Every channel of every move, and every given packet, has a fixed _target_ `Tg`, which
says what becomes of its packets: `done` (they stay, between a node and its parent, or at their
given nodes); `edge j e` (they are the load of the edge $`e` of stage $`j`); `nxt x` (they are
given in the relay `x`); `seg j i ω q` (they are outer segments on the pair `q` of the coset
`ω`, to be given in a law move there). The targets of the channels of relays are `tgR`; the
channels of a law move at a coset have the targets `edge (j+1) e` for the edges $`e` inside the
coset. A given packet number $`k` from $`a` to $`c` belongs to the batch number $`k \bmod |V_0|`.

_Numbers._ Everything that depends on the inputs is defined by one recursion over time, `numS`.
Given the numbers `N mv` of the moves before time $`\tau`, `alvN` is the number of _alive_ packets
of a channel: for a relay with the number $`t`, $`t` if the outcome is $`t` and $`0` otherwise;
for a law move, the outcome $`o_\nu` if the outcome is good for $`t` and $`\min(o_\nu, t)`
otherwise. (So of the $`o_\nu + 1` packets of a channel the last is never alive: it is the end
packet.) `ld N τ` is the number of alive packets with the target `τ`, the _load_. From the loads,
`numF` gives the number of a move at time $`\tau`: for a relay, the load of its input target if
the relay is active, and $`0` otherwise, where `inn j i e` is active if $`i` is the first type
with the least sum of squares of loads at stage $`j` (`IsMin`), and `mid j e 0` if the type of
$`e` is; for the law move of a coset and a law, the least $`t` for which some law of the family
has room for the loads of the outer segments (`tmin`, with `Fits`), if this law is the first that
has room for that $`t` (`Pick`), and $`0` otherwise. `num` is the result at the end of time.

_The plan._ `plan` has `num` as above; `good` is `GoodMv`, the two tests of
{bpref "thin_trees"}[`good_iff`]; and `consM` gives a relay all alive packets with its input
target, if it is active, and gives the slot number $`\sigma` among the slots on a pair $`q`, in
the law move that is picked, the alive packets with the target `seg … q` whose rank among these
lies in the interval $`[\sigma t, (\sigma + 1) t)`. This is the printed “Packets are assigned to
batches, slots and channels by their number in a fixed order”.

_The tree._ The parent of an element of stage $`j < J` is $`\hat\chi` for its coset $`\chi` of the
type chosen at stage $`j` (`Nc.Tow.hostj`), that of an element of stage $`J` is the root
(`Nc.Tow.parN`); the stage of the root is $`J + 1`, which is the depth. `up` at an element is the
sum of the loads `edge j e` over the edges $`e` at it (`Nc.Tow.fb`), and $`0` at the root
(`Paper.treeUp`). `dead o` is the set of the packets `new ν (o ν)`, the last packet of every
channel of every move (`Nc.Tow.deadU`).
:::

:::lemma_ "tree_value" (lean := "Paper.tree_value, Nc.Tow.plan_ok, Paper.thm_tree_poss_good, Paper.posVal_start") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem H.2: the value* (gloss). `tree_value` is the field
`value` for the tower plan. It combines four statements. `plan_ok`: the tower plan obeys the
rules `Plan.Ok` (causality holds because the numbers are defined by recursion over time and the
moves are ordered by time). `thm_tree_poss_good`: every possible outcome is good.
{bpref "thm_tree_moves"}[`thm_tree_moves`]: the moves keep the value, as a sum over good
outcomes. `posVal_start`: the starting position has the value `netValue tab`. The passage from
one sum over the contents of all copies to the product over the nodes of sums over their own
copies is `Nc.posVal_groups`.
:::

:::lemma_ "load_step" (lean := "Nc.Tow.Tower.load_step, Nc.Tow.kap_le, Paper.thm_tree_start_units") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem H.2: the recursion for the loads* (gloss). With
$`\kappa(n) = \bigl(\tfrac{r |V_j|}{2} \sum_e n_e^2\bigr)^{1/2}` for a load $`n` on the edges of
stage $`j` (the paper's $`Q_j`; in the towers of Proposition H.1 the parameter $`r` is $`1`),
`load_step` states the inequality of one stage,
$$`\kappa(n') \le \rho\, \kappa(n) + \frac{\sqrt{C_1}\, a_1}{b}\, |V_{j+1}|,`
under the hypothesis $`1 + 8C_1 \le \rho^2 h` and hypotheses that say that $`n'` arises from
$`n` by a stage with the type $`i` of least load. The theorem `thm_tree` takes $`\rho = 1/2`, so
that the hypothesis is (G.1) as it stands; this is the place of the paper's note that the printed
proof needs only $`1 + 4C_1 \le h/4`. `kap_le` is the induction over the stages for the loads of
the tower plan, and `thm_tree_start_units` is the bound $`4m(N + |V_0|^2)` for the load of an
edge after the start, the paper's $`n_0`. `kap_le` has no hypothesis on the outcomes: by the definition
of alive packets, a law move whose outcome is not good has at most $`t` of them on each channel.

The fields `node_le`, `total_le`, `up_node` and `up_total` follow from these through
`Nc.Tow.bet_le_bhat` and `Nc.Tow.sum_bet_le_kbar` (a node and a whole stage) and the arithmetic of
`Paper.exists_thinTrees`, where the factor $`M^{-\gamma}` appears as `Paper.gain_rpow`, from
$`\rho^{q} D \le 1` with $`\rho = 1/2`, $`D = b` and $`q = \log_2 b`.
:::

:::lemma_ "cur_tree" (lean := "Paper.cur_tree, Paper.tree_between, Paper.layers_le_seen") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem H.2: the packets at the end* (gloss). `cur_tree`:
under the tower plan, with at most `N` packets at every given node and all moves good, every
current packet that is not in `dead o` and has two different holders joins an element of some
stage and its parent, and is an alive packet of a channel at that element; this gives the field
`edge`. `tree_between` is the field `between_le`, and `layers_le_seen` the field `layers_le`.
:::

:::lemma_ "thm_tree_copies" (lean := "Paper.thm_tree_copies") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem H.2(e): the count of copies* (gloss). This is what the
note calls “the details of the count in part (e)”. The paper's sentences (page 48), quoted: “A
relay puts two packets at its middle node and replaces a packet by one packet at each of its
ends. In a stage a packet is relayed boundedly often, and the slots at an element take boundedly
many times $`t \le o_e` packets, zeros included. Hence what a node ever holds in the stages is at
most a constant times the loads at it and at its children, and its dead packets.”

The Lean statement, for the tower plan: for every node $`p`, the number of packets that $`p` ever
holds plus $`\sum_r (1 + s_r) t_r` over the roles $`r` at $`p` is at most
$$`\begin{aligned} &\bigl(4 + (2\,|\mathrm{Nr}|\, G_1 + 1 + S)\,|\mathrm{Di}|\bigr) \cdot 8 \cdot \Bigl(u_p + \sum_{q \text{ child of } p} u_q\Bigr) \\ &\quad + \bigl[p \text{ given}\bigr] (1 + 8m) N + 2\, \#\{\text{dead packets that } p \text{ holds}\}, \end{aligned}`
where $`|\mathrm{Nr}|` is the number of edges of $`U_h`, $`|\mathrm{Di}|` the number of laws,
$`S` a bound for the number of slots of a law, and $`m` the bound for the length of the routes.
The term $`(1 + 8m)N` is the paper's $`\Lambda N`: $`m \le c\,(J+1)^7` by Proposition H.1(d), and
$`J + 1 = O(\lg M)`. The field `copies_le` follows with the constant $`C`. Because Lean relays
leave copies, the count differs in its details from the printed one, in which a relay “leaves no
copy of the old packet”.
:::

:::lemma_ "tree_computed" (lean := "Paper.tree_computed, Paper.tree_slp, Unc.SlpN, Nc.Cut.IsSlpStep") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem H.2(d): the program* (gloss). `tree_computed` is the
field `computed` for the tower plan, with the explicit sizes `D` $`= (20 V^9)^4` and
`steps` $`\le 3\,(20 V^9)^{16}`, for a number $`V` that bounds the parameters of the tower, of the
laws and of the inputs; `Paper.exists_thinTrees` takes $`V = ((c+3)MN)^{30}` for a constant $`c`
of the tower and the laws.

_What is proved._ `SlpN inp steps H` asserts the existence of a program; the Lean development
does not write the program down as a list of instructions, and the proof never refers to one.
The set `H` consists of the functions `par`, `cur`, `cons`, `num`, `up`, `good` of the tower plan
themselves, which are defined mathematically in {bpref "tower_plan"}[the tower plan]. So “the
program computes exactly what is claimed” is, in Lean, the statement that these very functions
are among the values of the steps, for all inputs.

_How it is proved._ `Nc/SlpCalc.lean` and `Nc/Tow/Slp0.lean` set up a calculus of costs: a
function of the inputs is _computed in $`Y^a` steps from_ a set of functions already available
(`CY`, and `PY` for properties, through their indicators), and this notion is closed under binary
operations with values below `D`, under sums and under quantifiers over index sets of at most
$`Y` elements, under comparisons, and under the Boolean operations, the exponent $`a` growing by
a bounded amount each time. A _stage_ (`SY.add`) adds to a program all functions of a family,
each computed at such a cost. `tree_slp` chains the stages in the order of the definitions:

* from the inputs, the test that every given node has at most `N` packets, the numbers of given
  packets with each target, and the sums of squares of the outcomes of each law move
  (`stat_stage`);
* then, for each time $`\tau` in turn, the loads `ld` from the numbers of the earlier moves
  (`ld_stage`), from the loads the choices `IsMin`, `tmin`, `Pick` and the numbers `numF`
  (`pick_stage`), and from these the numbers of the moves up to time $`\tau + 1` (`num_stage`);
  after the last time, `num`, the numbers of alive packets and the loads are available
  (`after_stage`);
* then, for every packet name, whether it is alive, its rank among the alive packets with its
  target, whether it is given at each slot, whether it is current at the end, and for every move
  whether it is good (`units_stage`);
* then the indicators of the parents (`host_stage`) and the loads at the elements, which are the
  numbers `up` (`fb_stage`).

`tree_slp` bounds the cost of all stages together by $`Y^{16}` steps, for a number $`Y` with
$`Y^4 \le D`; `tree_computed` applies it with $`Y = 20V^9`. The loop over time is the Lean form of the printed “Finding the least $`N_i` and
the least $`t`, and testing whether an outcome is good, amounts to comparing integers”.
:::

:::lemma_ "tree_towers" (lean := "Paper.tree_towers, Paper.exists_thinTrees") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem H.2: the towers and the assembly* (gloss).
`tree_towers`: for laws as in the theorem there is a constant $`c` such that for every $`y \ge 1`
there are a tower with $`b = D = 2^{\mathrm{ee}(h)}` and $`r = 1`, routes on its bottom level of
length $`m \le c\,(J+1)^7` in which every edge is used at most $`2|V_0| m` times in all, and laws
at its vertices, such that the hypotheses `TCst` hold with $`\rho = 1/2` and
$`y \le |V_0| \le c\,y`. This is the paper's “Take the least $`n \ge 1` with $`M \le |G_n|`, so
that $`|G_n| = O(M)`”, with the words of Proposition H.1(d) as routes; this is where the exponent
$`7` of that proposition enters the proof. `exists_thinTrees` then gives a term of `ThinTrees` for every such
tower, with the exponent $`C =` `cTree c`, an explicit polynomial in $`c`, and with the fields
proved by the statements of the preceding nodes.
:::

# What the printed proof gives and what Lean gives

The following summary is this blueprint's, and it follows the items above.

*Appendix G.* The paper counts the printed proofs among those “meant to be complete, if terse”. The Lean statement of
Definition G.1 is a more general structure, matched to the printed notion by reading; that of
Theorem G.2 contains the printed statement and the choices of $`u`, $`C_0`, $`C_0'`, $`C_1` and
$`h`.

*Proposition H.1.* The printed proof is a sketch of one paragraph for each part. For (a) to (c)
the Lean statement expresses the printed one through representatives and freeness; for (d) Lean
proves the exponent $`7`, and the exponent $`3` rests on the printed sketch alone. The paper
neither counts this proof among those meant to be complete nor flags it.

*Theorem H.2(a) to (c).* The printed proof gives the construction and the recursion for the
loads, with constants absorbed in $`O(\cdot)` and in $`\Lambda`; the paper neither counts it among
those meant to be complete nor flags it. Lean gives the fields listed under clauses (a) to (c) of
{bpref "thin_trees"}[`ThinTrees`], for a construction that differs from the printed one in that
relays are laws applied to batches and leave copies and end packets, and that there is a move for
every law at every coset. The identity for the value is not restated as the value of a network in
the sense of Section H.2.

*Theorem H.2(d), (e).* The printed proof describes a program and counts its steps; the paper says
that the proof of these parts can be verified only in Lean. Lean gives the field `computed`,
which asserts that a program of the stated size exists whose steps take the values of the
functions that define the tower plan, and the fields `between_le`, `up_node`, `up_total` and
`copies_le`.

# What the next step takes from this chapter

{ref "chapter-programs"}[Programs, automata and cutting] keeps the ring $`A` and the laws as the
standing hypothesis {bpref "exists_laws"}[`VLaws`] and applies {bpref "thm_tree"}[Theorem H.2]
to the networks that Lemma I.2 attaches to a tape automaton. Proposition J.2 uses the tree to cut
a computation into pieces, and its last claim, the paper says (page 52), “rests on Theorem H.2(d)
and (e), whose printed proofs only describe the program in question”. The Lean file of that
proposition, {repoFile "vp-vnp/Paper/Pieces.lean"}[`Paper/Pieces.lean`], refers to the fields of
`ThinTrees` by name, among them `value`, the tree of clause (a), `edge`, `node_le`, `up_node`,
`up_total`, `copies_le` and `computed`. Section Q.3 (page 69) adds that “Proposition J.2 uses only
the total $`M^C`” of the dead packets.
