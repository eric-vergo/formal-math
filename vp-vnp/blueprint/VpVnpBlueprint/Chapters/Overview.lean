/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic), GPT (OpenAI)
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

#doc (Manual) "The shape of the proof" =>

%%%
tag := "chapter-overview"
file := "overview"
htmlSplit := .never
number := false
%%%

This chapter is the map of the proof. It follows Section 2 of the paper (pages 4–11 of
{repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]), its Figure 1 (page 5) and its Table 1 (page 17), and
adds, from the Lean code, how the two cases are assembled into the five theorems. It has no nodes
of its own: every statement it mentions is presented, beside its Lean declaration, in the chapter
it links to; a statement cited by its number in the paper links to its node, and a Lean name
shown here can be hovered for its statement. A reader should come
away knowing which statement does what, where the permanent and the circuit enter, which parts
are printed in full and which are complete only in Lean.

The summaries of proofs in this chapter are adapted from Section 2 of the paper, which “describes
the proof informally” (page 4); they are the paper's account, not statements this blueprint has
verified. What is proved is what the Lean theorems state.

# The argument in outline

The proof is a dichotomy. To a field $`\Bbbk` the paper attaches a family of metrics on finite
sets, the _prices_, which come from functionals on tensors over $`\Bbbk`. A common part shows
that prices have nonpositive curvature. Within nonpositive curvature either Euclidean metrics
occur among the prices (the _flat_ case) or the prices on a certain finite set are uniformly
shorter across diagonals than Euclidean rectangles (the _contracting_ case). Each case yields a
superpolynomial lower bound for the permanent and for the Hamiltonian cycle polynomial, by
unrelated arguments:

- in the flat case, a direct comparison of lengths in a Euclidean configuration, which gives
  $`2^{(\log m)^{4/3}/1600^2}`;
- in the contracting case, an indirect argument: contraction yields identities between tensors,
  the identities let every computation of a weighted nondeterministic program be cut into short
  pieces, a small circuit would then speed up all such computations, and a diagonal argument
  refutes the speed-up. This gives $`2^{c'(\log m)^2/\log\log m}`, with a constant $`c' > 0` for
  which the proof gives no value.

The theorem takes the weaker bound, which is the flat one for large $`m`. It is not known which
case holds, even over $`\mathbb{R}`.

# The two hypotheses

Definition 2.1 of the paper (pages 4–5) introduces the objects. A $`V`-tensor, for a finite set
$`V` of _parties_, is an array over $`\Bbbk` with one index for each party; tensors multiply
party by party; $`s` is a _restriction_ of $`t` if $`s = (\bigotimes_v A_v)\, t` for linear maps
$`A_v`. A _spectral point_ on $`V` is, quoted, “a function $`\phi` from the $`V`-tensors to
$`[0,\infty)` such that $`\phi(1) = 1` for the tensor 1 with all $`n_v = 1` and entry 1, such
that $`\phi(st) = \phi(s)\phi(t)`, and such that $`\phi(s) \le \sum_j \phi(t_j)` whenever
$`s = \sum_j s_j` with every $`s_j` a restriction of $`t_j`.” The _wire_
$`\langle q \rangle_{uv}` is the $`q \times q` identity matrix in the indices of $`u` and $`v`.
“For every spectral point $`\phi` there is a pseudometric $`d_\phi` on $`V` with values in
$`[0,1]` such that $`\phi(\langle q \rangle_{uv}) = q^{d_\phi(u,v)}` for all $`q \ge 1`.” The two
hypotheses on the field, quoted:

> *Contracting hypothesis:* There are an integer $`\mu \ge 2` and a real number $`s` with $`1 \le s` and $`s^2 < \mu` such that, for the set $`V = \mathrm{Mat}_\mu(\mathbb{F}_2)` of the $`\mu \times \mu` matrices over the field with two elements and for every spectral point $`\phi` on $`V`, $`\mathbb{E}_{a,\, W :\, \mathrm{rk}\, W = \mu}\; d_\phi(a, a+W)^2 \;\le\; s^2\; \mathbb{E}_{a,\, W :\, \mathrm{rk}\, W = 1}\; d_\phi(a, a+W)^2,` where the means are over all matrices $`a` and all matrices $`W` of the rank shown.

> *Flat hypothesis:* For every finite subset $`V` of a Euclidean space and every $`\varepsilon > 0` there are a spectral point $`\phi` on $`V` and a real number $`c \ge 0` such that $`|c\, d_\phi(u,v) - \|u - v\|| \le \varepsilon` for all $`u, v \in V`.

The paper adds (page 5): “The field enters only through the tensors, which have entries in
$`\Bbbk`, and the restrictions, which use $`\Bbbk`-linear maps. The set
$`\mathrm{Mat}_\mu(\mathbb{F}_2)` only supplies the parties and their addition; its
$`\mathbb{F}_2` is not the field $`\Bbbk`.”

A _price_ on $`V` is a pointwise limit of functions $`c\, d_\phi` with $`c \ge 0`; $`|uv|`
denotes a distance in a price, and for a price on $`\mathrm{Mat}_\mu(\mathbb{F}_2)` the paper
writes $`D(r)^2` for the mean of $`|a, a+W|^2` over all $`a` and all $`W` of rank $`r`. The Lean
definitions {InlineLean.name}`Paper.Flat` and {InlineLean.name}`Paper.Contracting` state the
hypotheses in this language, as the paper says (page 5): “The Lean definition states both
hypotheses for prices: the contracting one as $`D(\mu) \le s\, D(1)` for all prices on
$`\mathrm{Mat}_\mu(\mathbb{F}_2)`, which is the same because the inequality survives scaling and
limits, and the flat one as the statement that all finite subsets of Euclidean spaces, with their
metrics, are prices.” The form for prices is {bpref "def_cases"}[Definition D.1]
({InlineLean.name}`Paper.def_cases`). For the flat hypothesis the two forms are related by the
Lean characterization of prices ({bpref "def_price"}[Definition A.4],
{InlineLean.name}`Paper.def_price`). For the contracting hypothesis the agreement of the two
forms is the paper's remark just quoted; no Lean theorem states it, and the development uses
the form for prices throughout.

Theorem 2.2 of the paper (page 6), quoted: “Over every field $`\Bbbk` at least one of the two
hypotheses of Definition 2.1 holds, that is, one of the two cases occurs.” In Lean it is
{InlineLean.name}`Paper.thm_alt`, whose statement is `Flat K ∨ Contracting K` for a field `K`, in
the forms of Definition D.1; it is {bpref "thm_alt"}[Theorem D.2], presented in
{ref "chapter-dichotomy"}[The two cases]. The paper continues: “We
do not know which of the two hypotheses holds, even over $`\mathbb{R}`, nor do we show that the
two are mutually exclusive.” The Lean proof of the theorem is by cases on whether the contracting
hypothesis holds (excluded middle), so it gives no way to decide, and the proofs of the main
theorems need the lower bound in both cases.

What the hypotheses mean geometrically, adapted from page 5: every price on
$`\mathrm{Mat}_\mu(\mathbb{F}_2)` has $`D(\mu) \le \sqrt{\mu}\, D(1)`, because for $`W`, $`W'`
of ranks $`i`, $`j` with $`W + W'` of rank $`i + j` the points $`a`, $`a + W`, $`a + W + W'`,
$`a + W'` form a quadrilateral with two sides $`W`, two sides $`W'` and both diagonals
$`W + W'`, and in nonpositive curvature the squared diagonals of a quadrilateral add up to at
most its squared sides. “So the contracting hypothesis says that, for some $`\mu`, every price on
$`\mathrm{Mat}_\mu(\mathbb{F}_2)` falls short of a Euclidean rectangle by a fixed factor, and the
flat hypothesis says that prices can be Euclidean.”

# The common part

Three steps serve both cases; they are Appendices A to D of the paper.

*Ranks become distances.* A spectral point evaluates a product of wires exactly: the logarithm
of its value is the sum, over the wires, of the size $`\log q` of the wire times the distance
$`d_\phi` between its ends, the _length_ of the network. For other tensors there is only an upper
bound, through ranks ({InlineLean.name}`Paper.lem_hubs`, {bpref "lem_hubs"}[Lemma A.3]): a tensor
$`t` of rank at
most $`r` across a partition of the parties into $`I_1` and $`I_2` is a restriction of a product
of wires that join every party $`p` of $`I_i` to a further party $`o_i`, a _hub_, and the two
hubs to each other with dimension $`r`. Hence the paper's inequality (2.3), for every spectral
point on the parties and the hubs, with $`n_p` the dimension of the index of $`p`:
$$`\log \phi(t) \;\le\; \sum_{p \in I_1} d_\phi(p, o_1) \log n_p + \sum_{p \in I_2} d_\phi(p, o_2) \log n_p + d_\phi(o_1, o_2) \log r .`
The rank enters through the last term only. This is the bridge from circuits to geometry:
{ref "chapter-spectral"}[Tensors, spectral points and prices].

*Prices have nonpositive curvature.* The product of two crossing wires has full rank across both
partitions of its four ends into two pairs, so (2.3) says nothing about it. An identity between
integer tensors ({InlineLean.name}`Paper.prop_identity`, {bpref "prop_identity"}[Proposition B.2])
writes it as a sum of few terms, each of small rank across one partition when its rank across the
other is large; applying (2.3) to the largest term, once for each partition, gives an inequality
between the distances among the four ends and the four hubs
({InlineLean.name}`Paper.prop_crossing`, {bpref "prop_crossing"}[Proposition B.3]). Averaged over
fine chains of points it gives the inequality of Bruhat and Tits for prices
({InlineLean.name}`Paper.thm_cn`, {bpref "thm_cn"}[Theorem C.1]), and every price is induced by a
map into a complete CAT(0) space whose metric is again a price
({InlineLean.name}`Paper.prop_space`, {bpref "prop_space"}[Proposition C.3]):
{ref "chapter-curvature"}[Two crossing wires and nonpositive curvature].

*The dichotomy.* If the contracting hypothesis fails, a compactness argument gives prices on
$`\mathrm{Mat}_\mu(\mathbb{F}_2)` with $`D(\mu) = \sqrt{\mu}\, D(1)`, that is, with equality in
the quadrilateral inequality, and the flat rectangle property of CAT(0) spaces
({InlineLean.name}`Paper.lem_toolkit_f`, part (f) of {bpref "lem_toolkit"}[Lemma C.4]) then
“puts a solid cube of $`\mathbb{R}^\mu`, and so every finite subset of $`\mathbb{R}^\mu` up to
scale, into a price” (page 8): {ref "chapter-dichotomy"}[The two cases].

Neither a circuit nor the polynomial to be computed occurs in the common part.

# Two auxiliary polynomials, and where the permanent and the circuit enter

Neither case analyzes the permanent. The paper (page 6): “Rather than analyzing the permanent or
Hamiltonian cycle polynomial directly, in each case we work with another polynomial, which the
permanent, and likewise the Hamiltonian cycle polynomial, can express.”

- In the flat case the polynomial is that of a network of wires on the complete graph: for
  $`k \ge 2` and $`\ell \ge 1`,
  $`f_{k,\ell} = \sum_\sigma \prod_{a=1}^{k} x_{a,\sigma_a}`, where $`\sigma` assigns a string
  $`\sigma_{ab} = \sigma_{ba} \in \{0,1\}^\ell` to every edge $`ab` of the complete graph on
  $`k` nodes and $`\sigma_a = (\sigma_{ab})_{b \ne a}`. Its coefficient tensor is a product of
  wires, so its length in every price is known.
- In the contracting case it is $`\Phi = \sum_w U_t(w)\, y^w`, where $`w` runs over the words of
  fewer than $`n` symbols, $`U_t(w)` is the value of a fixed universal automaton on $`w` in $`t`
  steps, and $`y^w` is the monomial that encodes $`w`. Its values at the points that encode
  words are the sums over the weighted runs of all short nondeterministic programs.

Figure 1 of the paper (page 5) shows the structure of the two cases side by side; its caption,
quoted: “The two arrows marked *P* are the only steps that use the permanent; they use the
circuit too, but only by substituting into it. The two arrows marked *C* are the only steps that
look inside the circuit, both times at the polynomial at every gate. In the shaded boxes neither
the polynomial that is to be computed nor a circuit occurs; the dashed boxes are the assumptions.
For the determinant the arrows *P* are missing, and a Boolean circuit does not pass the arrows *C*
(Section 2.5).” The same structure as a table:

:::table +header
*
  * Step
  * Flat case
  * Contracting case
*
  * Without circuit or polynomial
  * Euclidean configurations are prices ({InlineLean.name}`Paper.def_cases`); the balanced sets cost about $`k^{3/2}` bits ({InlineLean.name}`Paper.lem_few`, {InlineLean.name}`Paper.prop_cube`)
  * Poincaré inequality ({InlineLean.name}`Paper.thm_poincare`), laws ({InlineLean.name}`Paper.thm_laws`), trees ({InlineLean.name}`Paper.thm_tree`), computations can be cut ({InlineLean.name}`Paper.thm_cut`)
*
  * Assumption
  * a circuit with $`L'` gates for $`\mathrm{PERM}_m`
  * a circuit with $`v^a` gates for $`\mathrm{PERM}_m`
*
  * *P*: the permanent, by substitution
  * a circuit with $`L = 5L'` gates for $`f_{k,\ell}` ({InlineLean.name}`Paper.cor_clauses`, {InlineLean.name}`Paper.lem_fkl_perm`)
  * a circuit with $`O(v^a)` gates for $`\Phi` ({InlineLean.name}`Paper.cor_clauses`)
*
  * *C*: inside the circuit
  * $`f_{k,\ell} = \sum_S f_S` over the balanced sets $`S`, the tensor of $`f_S` of rank at most $`L` across $`S` ({InlineLean.name}`Paper.lem_balanced`)
  * an approximate accelerator at the scale $`v`: sums over $`v^H` steps in $`v^{H-16}` steps ({InlineLean.name}`Paper.lem_lowdeg`, {InlineLean.name}`Paper.lem_circuit_approx`)
*
  * Conclusion
  * comparison of lengths: $`\log L \ge \ell k^{3/2}/16` ({InlineLean.name}`Paper.lem_hubs`, {InlineLean.name}`Paper.prop_flat_rate`); with $`k = r^2`, $`\ell = 100r`: {InlineLean.name}`Paper.thm_flat_rate`
  * approximate accelerators at arbitrarily large scales ({InlineLean.name}`Paper.lem_postpone`, {InlineLean.name}`Paper.prop_approx_acc_scales`); a diagonal argument shows there are none ({InlineLean.name}`Paper.thm_noacc`): {InlineLean.name}`Paper.thm_contracting`
:::

*The permanent* enters through an explicit form of Valiant's completeness theorem. Both
$`f_{k,\ell}` and $`\Phi` are _clause sums_, “sums over all bit vectors of products of local
weights” (page 6), and every clause sum is the permanent of a matrix whose entries are constants
or variables is the permanent of a matrix whose entries are affine in one variable each, of any
size at least three times its number of literals, over a field in which $`2 \ne 0`
({bpref "prop_grid"}[Proposition E.1], {bpref "cor_clauses"}[Corollary E.2];
{InlineLean.name}`Paper.prop_grid`, {InlineLean.name}`Paper.cor_clauses`), and the Hamiltonian
cycle polynomial of such a matrix with the factor 40 in the place of 3, over every field
({bpref "prop_hc_grid"}[Proposition M.2]; {InlineLean.name}`Paper.prop_hc_grid`,
{InlineLean.name}`Paper.cor_clauses_hc`; the underlying construction is over every commutative
ring and uses no division). So a circuit for the permanent or for the Hamiltonian cycle
polynomial gives, by substitution, a circuit with five times as many gates for $`f_{k,\ell}`,
and one with $`O(v^a)` gates for $`\Phi`: {ref "chapter-completeness"}[Completeness gadgets].
The Lean development states the later steps for any family that is _complete for grid sums_
({bpref "GridComplete"}[the definition]; {InlineLean.name}`Paper.gridComplete_perm`,
{InlineLean.name}`Paper.gridComplete_hc`), so that the two polynomials are treated at once.

*The circuit* is opened at two places, one in each case. In the flat case a decomposition lemma
“splits the polynomial at every gate, and so writes the tensor of the coefficients of the output
as a sum of terms of rank at most the number $`L` of gates” (page 6;
{bpref "lem_balanced"}[Lemma E.4]). In the
contracting case an evaluation lemma evaluates the part of degree at most $`d` of the output at
the points with coordinates 0 and 1 that encode words, in about $`d (\log L)^{O(1)}` steps, by a
nondeterministic program whose runs are the parse trees with at most $`d` leaves and which “does
not compute with the constants of the circuit but only records their names” (page 6;
{bpref "lem_lowdeg"}[Lemma K.2]).
Both use identities between the formal polynomials at the gates.

# The flat case

Adapted from Section 2.3 (pages 8–9). The tensor of $`f_{k,\ell}`, with the $`k(k-1)` _ends_
$`(a,b)` of the edges as parties, is the product over the edges of the wires of dimension
$`2^\ell` between $`(a,b)` and $`(b,a)`. A set $`S` of nodes is _balanced_ if
$`k/3 \le |S| \le 2k/3`, and every balanced set is crossed by at least $`2k^2/9` of the
$`k(k-1)/2` wires. A circuit with $`L` gates gives $`f = \sum_S f_S` over the balanced sets with
$`f_S` of rank at most $`L` across $`S`, so for every spectral point with hubs $`o_S`, $`o'_S`,
and for some balanced $`S`, the paper's inequality (2.4):
$$`\text{length of } f \;\le\; k + \text{length of the wires to the hubs of } S + d_\phi(o_S, o'_S) \log L .`
In the printed E.5 argument the flat hypothesis supplies one spectral point that realizes, up to any $`\delta`, a chosen
Euclidean configuration of all ends and all hubs in $`\mathbb{R}^k`: for $`a < b` the end
$`(a,b)` at $`\tfrac12 e_a` and the end $`(b,a)` at $`-\tfrac12 e_a`, and the hubs of $`S` at
distance of order $`k^{-1/2}` from the origin in the direction of the sum of the ends on the
side of $`S` and opposite to it. Routing through the hubs then saves a fixed fraction of $`k` in
length, while the two hubs are close; so $`\log L` must be large. In (2.4), multiplied by the
scale $`c` that the flat hypothesis supplies, the $`k` bits that name a balanced set appear as a
term $`ck`, which “is negligible for fixed $`k` and large $`\ell`, because $`\phi` and $`c` were
chosen for $`k` alone” (page 8; {bpref "prop_flat_lower"}[Proposition E.5]); for growing $`k` it
is replaced by about $`k^{3/2}` ({bpref "lem_few"}[Lemma E.7],
{bpref "prop_cube"}[Proposition E.9]), which gives $`\log L \ge \ell k^{3/2}/16` for
$`\ell \ge 100\sqrt{k}` ({bpref "prop_flat_rate"}[Proposition E.10]). With $`k = r^2`,
$`\ell = 100r` and $`\log m` of order $`k\ell = 100 r^3`, $`\log L` is of order
$`r^4 = (\log m)^{4/3}` up to constants: the bound of {bpref "thm_flat_rate"}[Theorem E.11],
{InlineLean.name}`Paper.thm_flat_rate`, which is $`2^{(\log m)^{4/3}/1600^2}` for all large
$`m`.

Lean retains the balanced hub decomposition. For fixed $`k` and sufficiently large
$`ℓ`, Proposition E.10 also gives the divisor-16 bound. The paper's divisor-six bound
uses the explicit configuration above.

Why the complete network: Figure 3 of the paper (page 9) contrasts it with a path, “the network
of an iterated matrix product”, which “has balanced sets that a single wire crosses”.

The printed proofs of this case are among those the paper calls “meant to be complete, if terse”
(page 17). {ref "chapter-flat"}[The flat case] presents it.

# The contracting case

Adapted from Section 2.4 (pages 9–10), which says: “Here the argument is indirect. Steps 1 to 4
prove, with no circuit and no permanent, that every computation of a nondeterministic program
with weighted runs can be cut into short pieces, which a fast program lists. In Step 5 a small
circuit for the permanent would speed up the sum over the runs of every short piece, hence all
such computations, and a diagonal argument refutes this.”

*Step 1: a Poincaré inequality.* The contracting hypothesis yields, for all prices on the groups
$`U_h` of upper unitriangular $`h \times h` matrices over $`\mathbb{F}_2`: “the mean square
distance of two random elements is at most a constant, the same for all multiples $`h` of a fixed
integer, times the sum over the $`h - 1` elementary generators of the mean square distances by
which they move a point” ({InlineLean.name}`Paper.thm_poincare`,
{bpref "thm_poincare"}[Theorem F.6]):
{ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups].

*Step 2: from inequalities to identities.* A form of Strassen's duality
({InlineLean.name}`Paper.thm_duality`, {bpref "thm_duality"}[Theorem A.6]) “turns an inequality
between lengths of products of wires that holds in every price into an identity that makes a
high tensor power of one product from few restrictions of the others”. From the Poincaré
inequality it makes the _rerouting laws_ ({InlineLean.name}`Paper.thm_laws`,
{bpref "thm_laws"}[Theorem G.2]), “whose coefficients generate a finitely generated ring $`A` and
which hold over every commutative $`A`-algebra”. The theorem asserts that such laws exist; of
the identities obtained from duality the paper says (page 20) that “none of them is written down
explicitly”.

*Step 3: trees.* The laws write the value of every network of tensors joined by wires as a sum
of values of tree networks, which can be cut into subtrees joined by wires of small total size
({InlineLean.name}`Paper.thm_tree`, {bpref "thm_tree"}[Theorem H.2]):
{ref "chapter-laws"}[Rerouting laws and tree networks].

*Step 4: computations can be cut.* An _instance_ $`z` is a nondeterministic program with an
argument, whose runs have weights in $`A`; $`\mathrm{sum}(z)` is the sum of the weights of its
accepting runs; $`z` is $`\tau`-_plain_ if all its runs halt and the accepting ones take at most
$`\tau` steps and name no constants. A fixed universal machine, a _tape automaton_, evaluates
$`\mathrm{sum}(z)` for plain $`z` ({InlineLean.name}`Paper.prop_universal`,
{bpref "prop_universal"}[Proposition I.1]), its runs form networks
({InlineLean.name}`Paper.lem_runnet`, {bpref "lem_runnet"}[Lemma I.2]), and Step 3 applies to
them. The result is the cutting theorem ({InlineLean.name}`Paper.thm_cut`,
{bpref "thm_cut"}[Theorem J.4]): for a large
integer $`v`, the _scale_, a suitable constant $`H` and $`\tau \ge v^H` below a fixed power of
$`v`, “for every $`\tau`-plain instance $`z` of size at most $`\tau/v^{48}`, the sum
$`\mathrm{sum}(z)` is the sum, over the runs of a program whose accepting runs take at most
$`\tau/v^{24}` steps, of the weight of the run times the product of $`\mathrm{sum}(y)` over the
pieces $`y` that the run lists. A run lists at most $`\tau v^2/v^H` pieces, and they are
$`v^H`-plain and short, that is, of size at most $`v^{H-32}`.”
{ref "chapter-programs"}[Programs, automata and cutting].

*Step 5: accelerators and the diagonal.* The printed exact argument converts a small circuit
into an exact accelerator at the initial scale and propagates it by Proposition K.5.
{bpref "lem_circuit"}[Lemma K.3] and {bpref "prop_next"}[Proposition K.5] mark those paper steps.
The checked construction uses a finite Laurent circuit and an approximate accelerator
({InlineLean.name}`Paper.lem_circuit_approx`). Postponing named constants and cutting the
remaining instances preserve the approximation invariant at arbitrarily large scales
({InlineLean.name}`Paper.prop_approx_acc_scales`). The proof extracts an exact accelerator at
a sufficiently large scale for the diagonal contradiction. Correctness of an
accelerator is a family of identities in its constants over $`A`, so it survives reduction to a
finite field, in which boundedly many names cover all powers of the constants. At a scale that is
large compared with that field a program $`\mathsf{P}` that on $`x` guesses a bit and either
accepts with weight 1 or applies the accelerator to “$`x` applied to $`x`” has, applied to
itself, a value $`V` with $`V = 1 + V`, “which is impossible in a nonzero ring”
({InlineLean.name}`Paper.thm_noacc`, {bpref "thm_noacc"}[Theorem K.6]). The condition
$`(\log v)^{O(a)} \le v` is what limits the bound to $`2^{c'(\log m)^2/\log\log m}`
({InlineLean.name}`Paper.thm_contracting`, {bpref "thm_contracting"}[Theorem K.7]):
{ref "chapter-accelerators"}[Accelerators and the diagonal argument].

*What is printed and what is not.* This case is where the printed proof and the Lean proof part
ways. The paper (page 17), quoted: “The proofs of Proposition I.1, Theorem H.2(d), (e), Theorem
J.3 and Proposition N.4 describe machines and programs and account for their sizes and running
times. That these do exactly what is claimed can be verified only in the Lean development, and
each of these four statements is followed by a formalization note that says so. Consequently the
contracting case, and with it every main result, rests on Lean at these points.” The four items
are: the universal tape automaton and its running time ({bpref "prop_universal"}[Proposition
I.1]); parts (d) and (e) of the theorem on tree networks ({bpref "thm_tree"}[Theorem H.2]), on
which the last claim of {bpref "prop_pieces"}[Proposition J.2] rests by its own formalization
note (page 52); the evaluator and the cutting program of a single cut
({bpref "thm_onecut"}[Theorem J.3]); and the exclusion of approximate accelerators
({bpref "prop_approx_acc"}[Proposition N.4]). For these the chapters of this blueprint describe
the machines and programs from the Lean code, and say what was and was not understood from it.
The compiled dependency closures of the five exports contain all four results. Proposition
N.4 excludes approximate accelerators in the contracting branch of the shared coefficientwise
bound. The exact lower bound uses it as well, through the constant-series embedding
({ref "chapter-claim"}[What is claimed]).

In the Lean development Steps 4 and 5 are also separated formally: Propositions K.5 and N.4 and
Theorem K.6 take the conclusion of the cutting theorem as a hypothesis, for a commutative ring
that has to be finitely generated only in Theorem K.6 and Proposition N.4, and the contracting
case supplies it (Section Q.3, page 69).

# Assembling the two cases

The paper proves the bound over $`\mathbb{R}` for the permanent first (Theorem L.1), then passes
to all fields and to the Hamiltonian cycle polynomial (Appendix M) and to approximation
(Appendix N). The following is read from the Lean proof of
{InlineLean.name}`Paper.thm_allfields` ({bpref "thm_allfields"}[Theorem M.3]), which the theorem
`Solution.mainTheorem` cites; {ref "chapter-assembly"}[All fields and approximate computation]
goes through it step by step.

1. The constant is fixed first: $`c = 1/1600^2`.
2. For a characteristic $`p`, zero or prime, take an algebraically closed field $`\mathbb{K}` of
   characteristic $`p` ({InlineLean.name}`Paper.exists_closed`: the algebraic closure of
   $`\mathbb{Q}` or of $`\mathbb{F}_p`).
3. Apply the dichotomy to $`\mathbb{K}` ({InlineLean.name}`Paper.approx_rate_closed`).
   The general flat and contracting bounds apply to any family complete for grid sums.
   The Hamiltonian cycle polynomial qualifies in every characteristic. The permanent qualifies
   for $`p\ne 2`. In the contracting case {InlineLean.name}`Paper.thm_allfields_exceeds` converts
   the stronger bound into the same eventual rate as in the flat case.
4. For each polynomial, its integer coefficients let {bpref "lem_transfer_approx"}[Lemma N.2]
   transfer an approximating circuit over any field of characteristic $`p` to a circuit over
   Laurent polynomials over $`\mathbb{K}`, preserving the gate budget and coefficient conditions.
   The bound over $`\mathbb{K}` therefore holds with one threshold for the entire characteristic.
5. The bound is rewritten as $`m^{c(\log m)^{1/3}}` ({InlineLean.name}`Paper.thm_main_form`).
   An exact circuit satisfies the same lower bound by mapping its constants to constant Laurent
   series ({InlineLean.name}`Paper.approximates_of_computes`).

The separation {InlineLean.name}`Paper.cor_allclasses` ({bpref "cor_allclasses"}[Corollary M.4])
follows: $`(\mathrm{HC}_n)` is in VNP ({InlineLean.name}`Paper.hc_mem_VNP`,
{bpref "hc_mem_VNP"}[its node]), and if it were in VP with exponent $`a` its circuits of
size $`n^a + a` would contradict the bound at a suitable $`n`
({InlineLean.name}`Paper.exists_beyond_poly`).

{InlineLean.name}`Paper.thm_approx` ({bpref "thm_approx"}[Theorem N.5]) applies the shared bound
directly. In that bound an approximating circuit over any field of characteristic $`p` is first
replaced by one of the same size whose constants are Laurent polynomials in $`\varepsilon` over
$`\mathbb{K}` ({InlineLean.name}`Paper.lem_transfer_approx`,
{bpref "lem_transfer_approx"}[Lemma N.2]); over $`\mathbb{K}` the dichotomy applies to
such circuits ({InlineLean.name}`Paper.approx_rate_closed`), here for both polynomials through
the forms for families that are complete for grid sums: the flat case with a version of Lemma
E.7 that allows an error in $`\varepsilon` ({InlineLean.name}`Paper.lem_few_approx`,
{bpref "lem_few_approx"}[Lemma N.3]; {bpref "flat_rate_approx_complete"}[the flat bound for
approximating circuits]), the contracting case with programs that are correct only up to
multiples of $`\varepsilon` ({InlineLean.name}`Paper.prop_approx_acc`,
{bpref "prop_approx_acc"}[Proposition N.4]). The constant is again $`1/1600^2`, and the second
separation again uses $`(\mathrm{HC}_n)`.

Two features of the assembly are worth isolating. The absolute constant is that of the flat
case, although the contracting case gives a stronger bound, because the constant of the
contracting bound depends on the field. And the threshold $`m_0` is not effective, for two
reasons that the paper names: the case is not decided, and in the contracting case “the
constants, among them $`m_0`, depend on the integer $`\mu`, for which the proof gives no value”
(page 8).

# The determinant and Boolean circuits

Section 2.5 of the paper (pages 10–11) says where the argument stops for two things it must not
prove. These are the paper's statements; the Lean development contains no theorem about the
determinant or about Boolean circuits.

*The determinant* (page 10): “The determinant is very similar to the permanent, but has circuits
of polynomial size \[Ber84\], so the proof must fail for it, and it fails at one point only: the
reduction of clause sums to the permanent (the arrows marked P in Figure 1). So our results imply
that $`f_{k,\ell}` in the flat case, and $`\Phi` in the contracting case, has no reduction of
comparable size to determinants.”

*Boolean circuits* (page 10): “A Boolean circuit for $`\mathrm{HC}_m` amounts to an arithmetic
circuit over $`\mathbb{F}_2` that only has to be correct on the inputs 0 and 1. So instead of
$`\mathrm{HC}_m` it may compute any polynomial $`g = \mathrm{HC}_m + \sum_i (x_i^2 - x_i) h_i`,
and our theorem says nothing about such $`g`. The proof breaks at the two steps that look inside
the circuit (marked C in Figure 1). The decomposition lemma (`lem_balanced`) uses the part of the
computed polynomial that is linear in each block of variables, and the evaluation lemma
(`lem_lowdeg`) uses its part of low degree; for $`g` these parts need have nothing to do with
those of $`\mathrm{HC}_m`.” And: “The substitutions (marked P) are not the obstacle: they send
inputs 0 and 1 to inputs 0 and 1”.

*The field* (pages 10–11): “Which of the two hypotheses holds may depend on the field. Otherwise
the field only supplies the scalars: the crossing identity is between integer tensors, the
geometry sees only the real numbers $`\phi(t)`, and the steps marked C use identities between
polynomials that hold over any commutative ring. Of the field we use only that $`2 \ne 0`, for
the matrix entries $`\pm\tfrac12` in the construction (`prop_grid`) behind the reduction to the
permanent (`cor_clauses`); in characteristic two, where the permanent is the determinant, the
construction stops there, whereas the one for $`\mathrm{HC}_m` needs no division (`prop_hc_grid`),
so the reduction to $`\mathrm{HC}_m` holds over every field (`cor_clauses_hc`).”

# The map of the proof

Table 1 of the paper (page 17), with the chapters of this blueprint. The paper's note to the
table: “Of Section G, Sections I and K use only the ring $`A`; of Section H, Section I uses only
the notion of a network.”

:::table +header
*
  * Section
  * What is proved
  * Uses
  * Case
  * Chapter
*
  * A
  * spectral points and prices; duality; random points
  * –
  * both
  * {ref "chapter-spectral"}[Tensors, spectral points and prices]
*
  * B
  * the inequality (B.2) for two crossing wires
  * A
  * both
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]
*
  * C
  * prices satisfy the inequality of Bruhat and Tits
  * A, B
  * both
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]
*
  * D
  * the flat case or the contracting case holds
  * C
  * both
  * {ref "chapter-dichotomy"}[The two cases]
*
  * E
  * lower bounds for $`f_{k,\ell}` and for the permanent
  * A, C, D
  * flat
  * {ref "chapter-completeness"}[Completeness gadgets] (E.1 to E.3), {ref "chapter-flat"}[The flat case] (E.4 to E.11)
*
  * F
  * a Poincaré inequality on unitriangular groups
  * C, D
  * contracting
  * {ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups]
*
  * G
  * rerouting laws
  * A, F
  * contracting
  * {ref "chapter-laws"}[Rerouting laws and tree networks]
*
  * H
  * every network is a sum of tree networks
  * G
  * contracting
  * {ref "chapter-laws"}[Rerouting laws and tree networks]
*
  * I
  * programs and tape automata; runs as networks
  * G, H
  * contracting
  * {ref "chapter-programs"}[Programs, automata and cutting]
*
  * J
  * computations can be cut into pieces
  * H, I
  * contracting
  * {ref "chapter-programs"}[Programs, automata and cutting]
*
  * K
  * small circuits give accelerators; there are none
  * E, G, I, J
  * contracting
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]
*
  * L
  * Theorems L.1, L.2, Corollary L.3
  * D, E, K
  * both
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * M
  * all fields; the Hamiltonian cycle polynomial
  * D, E, K
  * both
  * {ref "chapter-assembly"}[All fields and approximate computation]; Proposition M.2 in {ref "chapter-completeness"}[Completeness gadgets]
*
  * N
  * approximate computation
  * E, K, M
  * both
  * {ref "chapter-assembly"}[All fields and approximate computation]; Lemma N.3 in {ref "chapter-flat"}[The flat case], Proposition N.4 in {ref "chapter-accelerators"}[Accelerators and the diagonal argument]
*
  * O
  * proofs of the facts on CAT(0) spaces in Lemma C.4
  * C
  * both
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]
:::

On reading order the paper says (page 17): “Section E treats the flat case completely, and
nothing after it is needed for that case except Section L. The proof of the duality theorem in
Section A can be skipped at a first reading, since the theorem is used only in Section G.” And on
completeness: “The printed proofs differ in completeness. Those of Sections A to G and of
Appendix O, and the deduction of Theorem L.1 in Section L, are meant to be complete, if terse.”
For Sections H to K, M and N outside the four items named above, and for Theorem L.2 and
Corollary L.3, the paper makes no statement of either kind;
{ref "chapter-caveats"}[What a reader should keep in mind] returns to this.

The dependency graph of this site is drawn from the Lean code and from the dependencies that
the chapters declare, not from this table. The two differ where the Lean proof takes another
route than the printed one; Section Q.3 of the paper (page 70) lists those places, and
{ref "chapter-table3"}[The paper's statements and their Lean names] marks the statements that
are not on the route of the five theorems.

The next chapter, {ref "chapter-completeness"}[Completeness gadgets], takes from this one the two
auxiliary polynomials and the notion of a clause sum.
