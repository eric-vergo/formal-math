/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import Paper.Tensors
import Paper.Prices
import Paper.Gauges
import Paper.Extension

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "Tensors, spectral points and prices" =>

%%%
tag := "chapter-spectral"
file := "spectral-points"
htmlSplit := .never
number := false
%%%

This chapter defines the objects with which the whole proof measures a polynomial: tensors on a
finite set of _parties_, compared by restriction; _spectral points_, the functions on tensors
that are multiplicative and subadditive on sums of restrictions; the pseudometric $`d_\phi` that a
spectral point induces on the parties; and _prices_, the limits of multiples of these
pseudometrics. The complexity measure of the proof is not one function but the whole family of
spectral points, of which only existence statements are available (they come from Zorn's lemma),
and the lower bounds come from the geometry of the set of all prices. The chapter follows Appendix
A of the paper (pages 18–22) of {repoFile "vp-vnp/paper.pdf"}[`paper.pdf`].

The paper's own guide to the section (page 18): “Lemma A.3 is our link to circuits, Theorem A.6
is used only in Section G, and Propositions A.7 and A.8 add new points to a price. Section A.4 and
the proofs in Sections A.5 and A.6 rest on Zorn's lemma and may be skipped at a first reading.”
For a reader who wants the shortest path to the flat case: {bpref "def_spectral"}[],
{bpref "lem_exponents"}[], {bpref "lem_hubs"}[], {bpref "def_price"}[] and the statement of
{bpref "prop_random"}[] suffice for {ref "chapter-curvature"}[Two crossing wires and nonpositive
curvature] and {ref "chapter-flat"}[The flat case].

*Conventions.* The paper (pages 17–18): “In Sections A to L the field of coefficients is
$`\Bbbk = \mathbb{R}`, of which we use only that it is a field in which $`2 \neq 0` (Appendix M
treats all fields), and we write $`\Bbbk` so that Appendices M and N can quote the statements.
Tensors that are restrictions of each other are identified.” In Lean the field is a variable
`K : Type` with `[Field K]` in every theorem of this chapter; none of them assumes $`2 \neq 0`.
Appendix Q.3 (page 66): “Lean does not identify equivalent tensors (`def_spectral_congr` shows
that spectral points respect the identifications), and it writes the standing hypotheses out.”
The same passage restricts the universe: “The theorems with prefix `Paper.` are stated for fields
in the lowest universe, and so are their rings, algebras, groups, spaces, point sets and index
sets.”

_Background (not from the paper's proofs)._ Strassen's asymptotic spectrum of tensors (V.
Strassen, _The asymptotic spectrum of tensors_, J. reine angew. Math. 384 (1988); the paper's
reference Str88) consists of the functions on tensors that are monotone under restriction,
multiplicative under tensor product, additive under direct sum and normalized to $`q` on the unit
tensor of size $`q`. Spectral points in the sense of this paper drop additivity and
normalization; the paper says so after Definition A.1, quoted below.

# A.1. Tensors, restrictions and covers

:::definition "Ten" (lean := "Ov.Ten, Ov.Ten.Restr, Ov.Ten.SumRestr, Ov.Ten.Equi, Ov.Ten.push, Ov.Ten.unit, Ov.Ten.wire") (parent := "part-common")
*Definitions of Section A.1 of the paper* (page 18, unnumbered), quoted. “Let $`I` be a finite
nonempty set, whose elements we call _parties_, as in quantum information theory. A _tensor_ on
$`I` is an array with entries in $`\Bbbk` that has one index for each party, which runs through a
finite set, the _index set_ at this party. A tensor may be zero. Following Strassen, we say that
$`s` is a _restriction_ of $`t` if $`s = (\bigotimes_p A_p)\, t` for some linear maps $`A_p`, one
for each party. … We say that $`s` is _covered_ by $`t_1, \ldots, t_r`, and that these form a
_cover_ of $`s`, if $`s = s_1 + \cdots + s_r` with every $`s_j` a restriction of $`t_j`, and we
measure a cover by the number $`r` of its tensors.”

“In the _product_ $`st` each party holds its index of $`s` and its index of $`t`, and $`1` denotes
the tensor all of whose index sets have one element and whose entry is $`1`.”

“For a map $`\pi : I \to J` of finite sets the _push-forward_ $`\pi t` of a tensor $`t` on $`I` is
the tensor on $`J` in which the party $`\pi(p)` holds the index of $`p`, and a party outside the
image holds an index set with one element. When $`J` has two elements, $`\pi t` is a matrix, a
_flattening_ of $`t`.”

“For a nonempty $`P \subseteq I` and an integer $`q \geq 1` the _unit tensor_ of size $`q` on
$`P` is $`\langle q \rangle_P = \sum_{i=1}^{q} \bigotimes_{p \in P} e_i`, where
$`e_1, \ldots, e_q` is the standard basis of $`\Bbbk^q`. For parties $`u \neq v` we call
$`\langle q \rangle_{uv} = \langle q \rangle_{\{u,v\}}` the _wire_ of dimension $`q` between $`u`
and $`v`, and we put $`\langle q \rangle_{uu} = 1`. A product of wires is a _graph tensor_. …
Since $`\langle q \rangle_P \langle q' \rangle_P = \langle qq' \rangle_P`, a wire of dimension
$`2^n` is a product of $`n` wires of dimension two, and we say that it _carries $`n` bits_.”

The paper's example: “On two parties $`u, v` a tensor is a matrix, two matrices are restrictions
of each other if and only if they have the same rank, and the matrix of rank $`q \geq 1` is the
wire $`\langle q \rangle_{uv}`. On three parties the restrictions of $`\langle q \rangle_{uvw}`
are the tensors of tensor rank at most $`q`, and
$`\langle q \rangle_{uv} \langle q \rangle_{vw} \langle q \rangle_{uw}` is the tensor of the
multiplication of $`q \times q` matrices.”

In Lean a tensor `t : Ov.Ten K I` consists of a finite index type `t.ι p` for every party and an
array `t.val`. `Restr s t` asks for a family of matrices, one per party, that carries `t` to `s`;
`SumRestr s b` is a cover indexed by any finite type `κ` (one restriction of each `b k`, possibly
zero); `Equi s t` is restriction in both directions, the relation that the paper turns into an
identification. `Ten.push π t` gives the party $`q` the indices of all $`j` with $`\pi(j) = q`.
`Ten.unit K J r` is $`\langle r \rangle_J` on all of `J`; the unit tensor on a subset is its
push-forward, and `Ten.wire K n p q` is the push-forward of the unit tensor on two legs along
$`(p, q)`, also when $`p = q` (where the paper puts $`1`).
:::

:::lemma_ "tensor_laws" (lean := "Paper.tensor_mul_laws, Paper.tensor_one_restr, Paper.tensor_covered_by_ones, Paper.tensor_push_mul, Paper.tensor_push_comp, Paper.tensor_push_one, Paper.tensor_push_cover") (parent := "part-common")
*Remarks of Section A.1 of the paper* (page 18), quoted: “Tensors that are restrictions of each
other are identified, so that the product is commutative and associative, with unit $`1`. Every
nonzero tensor has $`1` as a restriction, and every tensor is covered by finitely many copies of
$`1`.” And: “Push-forward commutes with products and with the composition of maps, and it sends
$`1` to $`1`, restrictions to restrictions and covers to covers.”

Since Lean does not identify equivalent tensors, each law is an `Equi` between the two sides. The
two statements of the second sentence assume `[Nonempty I]`, the paper's standing assumption that
there is at least one party.
:::

# A.2. Spectral points, wires and hubs

:::definition "def_spectral" (lean := "Ov.Spec, Paper.def_spectral, Paper.def_spectral_congr") (parent := "part-common")
*Definition A.1 of the paper* (spectral point; page 19), quoted: “A _spectral point_ on $`I` is a
function $`\phi \geq 0` on the tensors on $`I` such that $`\phi(1) = 1`, such that
$`\phi(st) = \phi(s)\phi(t)` for all tensors $`s` and $`t`, and such that
$`\phi(s) \leq \sum_{j=1}^{r} \phi(t_j)` whenever $`s` is covered by $`t_1, \ldots, t_r`.”

The paper continues: “For $`r = 1` the last condition says that $`\phi` is monotone under
restriction, and for $`r = 0` it says that $`\phi(0) = 0`. Since $`1` is a restriction of every
nonzero tensor, $`\phi(t) \geq 1` for every $`t \neq 0`. Examples are the function that is $`1`
on all nonzero tensors and the rank of a flattening. This class is larger than Strassen's
asymptotic spectrum \[Str88\], whose points are in addition additive under direct sums and
normalized on unit tensors, and for example $`\phi^a` is again a spectral point for
$`0 < a \leq 1`.”

The Lean structure `Ov.Spec K I` has the function as its field `F` and the three conditions as
fields, the cover being indexed by an arbitrary finite type. `Paper.def_spectral` shows that a
function is the `F` of some `Spec` exactly if it satisfies the printed conditions with covers
indexed by $`\{1, \ldots, r\}` (`Fin r`). `Paper.def_spectral_congr` is the statement that Appendix
Q.3 cites for the identification of equivalent tensors: $`\phi` is monotone under `Restr` and
constant on `Equi`-classes. So a `Spec` is a function on tensors that descends to the paper's
identified tensors, and conversely.
:::

:::lemma_ "def_spectral_values" (lean := "Paper.def_spectral_values, Paper.trivialPoint, Paper.powerPoint") (parent := "part-common")
*Remarks after Definition A.1 of the paper* (page 19; quoted in the previous node). The first Lean
theorem is “$`\phi(t) \geq 1` for every $`t \neq 0`” together with $`\phi(0) = 0`; `trivialPoint`
is the spectral point that is $`1` on all nonzero tensors, and `powerPoint` is $`\phi^a` for
$`0 < a \leq 1`.

The third example of the paper has no Lean counterpart. Appendix Q.3 (page 70) lists “the example
of flattening ranks after Definition A.1” under “Not in Lean”.
:::

:::lemma_ "lem_exponents" (lean := "Paper.lem_exponents") (parent := "part-common")
*Lemma A.2 of the paper* (exponents of unit tensors; page 19), quoted: “Let $`\phi` be a spectral
point on $`I`. For every nonempty $`P \subseteq I` there is a real number $`g_\phi(P) \geq 0` such
that $`\phi(\langle q \rangle_P) = q^{g_\phi(P)}` for all $`q \geq 1`. The function defined by
$`d_\phi(u, v) = g_\phi(\{u, v\})` for $`u \neq v` and by $`d_\phi(u, u) = 0` is a pseudometric on
$`I` with values in $`[0, 1]`. Moreover $`g_\phi(P) \leq \sum_e d_\phi(e)`, where $`e` runs over
the edges of any tree with vertex set $`P`.” The paper calls $`g_\phi(P)` “the _exponent_ of $`P`
under $`\phi`”.

In Lean, $`d_\phi(u, v)` is `φ.e u v`, defined as $`\log \phi(\langle 2 \rangle_{uv})`
(`Ov.Spec.e`), and $`g_\phi` of the image of a map `π : A → I` is `Nc.Price.hexp φ π`, defined as
$`\log \phi(\pi \langle 2 \rangle_A)`. The theorem asserts the existence of a function `g` on the
finite subsets with the printed properties and with `φ.e u v = g {u, v}` for $`u \neq v`; the tree
is a `SimpleGraph` on `P` with `IsTree`. The paper records no difference.
:::

:::proof "lem_exponents"
*The paper's proof* (page 19), quoted: “Each claim follows from a restriction between products of
unit tensors. The function $`q \mapsto \phi(\langle q \rangle_P)` is at least $`1`,
multiplicative, because $`\langle q \rangle_P \langle q' \rangle_P = \langle qq' \rangle_P`, and
nondecreasing, because $`\langle q \rangle_P` is a restriction of $`\langle q' \rangle_P` for
$`q \leq q'`, and hence it is a power of $`q`. A wire of dimension $`q` is covered by $`q` copies
of $`1`, so $`d_\phi \leq 1`. Contracting the two indices at $`v` shows that
$`\langle q \rangle_{uw}` is a restriction of $`\langle q \rangle_{uv} \langle q \rangle_{vw}`,
which gives the triangle inequality. Identifying the indices at every vertex of a tree in the
same way shows that $`\langle q \rangle_P` is a restriction of the product of the wires on the
edges of the tree, which gives the last inequality.”
:::

:::lemma_ "lem_exponents_parts" (lean := "Paper.lem_exponents_power, Paper.lem_exponents_wire, Paper.lem_exponents_unit_interval, Paper.lem_exponents_self, Paper.lem_exponents_symm, Paper.lem_exponents_contract, Paper.lem_exponents_triangle") (parent := "part-common")
*The named parts of Lemma A.2* (page 19): the power law
$`\phi(\pi \langle q \rangle_A) = q^{g}` with $`g \geq 0` for the push-forward of a unit tensor
along any map; the power law $`\phi(\langle q \rangle_{uv}) = q^{d_\phi(u,v)}` for wires;
$`0 \leq d_\phi \leq 1`; $`d_\phi(u, u) = 0`; symmetry; the restriction
$`\langle q \rangle_{uw} \leq \langle q \rangle_{uv} \langle q \rangle_{vw}`; and the triangle
inequality.

Appendix Q.3 (page 70) on how the lemma is used: “Of Lemma A.2 only the clauses that say that
$`d_\phi` is a pseudometric are taken from the lemma: the power law and $`d_\phi \leq 1` come from
its named parts, and the bound by a tree is used nowhere.”
:::

:::lemma_ "lem_hubs" (lean := "Paper.lem_hubs, Paper.lem_hubs_further") (parent := "part-common")
*Lemma A.3 of the paper* (routing a tensor through two hubs; page 19), quoted: “Let
$`I = I_1 \sqcup I_2`, let a tensor $`t` on $`I` be a sum of $`r` products of a tensor on $`I_1`
and a tensor on $`I_2`, and let $`n_p` be the size of the index set of $`t` at the party $`p`. Let
$`o_1, o_2` be two further parties. Then $`t` is a restriction of
$$`\prod_{p \in I_1} \langle n_p \rangle_{p o_1} \cdot \langle r \rangle_{o_1 o_2} \cdot \prod_{p \in I_2} \langle n_p \rangle_{p o_2},`
and this remains true when $`o_1` and $`o_2` are identified with given parties.”

The Lean statement differs as the paper says. Appendix Q.3 (page 68) counts Lemma A.3 among those
“proved in stronger or more general forms. For example, `lem_hubs` pushes the tensor $`t` forward
along an arbitrary map from its parties to a finite set of parties, of which $`o_1, o_2` are any
two, and `lem_hubs_further` is the form with two further parties.” In `Paper.lem_hubs` the tensor
lives on a type `A` of parties split by a predicate `S`, the decomposition is
$`t(x) = \sum_{j < r} \alpha_j(x)\, \beta_j(x)` with $`\alpha_j` depending only on the indices in
$`S` and $`\beta_j` only on the others, `π : A → I` is any map, and `o₁ o₂ : I` are any two
parties. The conclusion is the restriction of $`\pi t` to the product of the wires
$`\langle n_a \rangle_{\pi(a),\, o}`, with $`o = o_1` for $`a \in S` and $`o = o_2` otherwise,
times $`\langle r \rangle_{o_1 o_2}`. This contains the printed statement and its last clause;
`Paper.lem_hubs_further` is the printed first sentence, with the two hubs as two new parties.
:::

:::proof "lem_hubs"
*The paper's proof* (page 19), quoted: “Only the two hubs apply linear maps, and these are built
from a decomposition $`t = \sum_{i=1}^{r} \alpha_i \otimes \beta_i` into tensors $`\alpha_i` on
$`I_1` and $`\beta_i` on $`I_2`. We read $`\alpha_i` and $`\beta_i` as functionals on the ends at
$`o_1` and at $`o_2` of the wires from the parties. When $`o_1` applies
$`\sum_i \alpha_i \otimes e_i^*` and $`o_2` applies $`\sum_i \beta_i \otimes e_i^*`, where
$`e_i^*` acts on the wire between the hubs, the result is $`t`. The last statement follows by
push-forward along the map that sends $`o_1` and $`o_2` to the given parties.”
:::

*From ranks to lengths.* The paper notes after the proof (page 19) that, together with Lemma A.2,
the lemma “gives the inequality (2.3) for every spectral point on $`I \cup \{o_1, o_2\}`”. Spelled
out from the three statements above (a derivation of this blueprint, immediate from monotonicity,
multiplicativity and the power law for wires): if $`t` has rank at most $`r` across
$`I_1 \mid I_2`, then for every spectral point $`\phi` on $`I \cup \{o_1, o_2\}`
$$`\log \phi(t) \;\leq\; \sum_{p \in I_1} \log n_p \cdot d_\phi(p, o_1) \;+\; \log r \cdot d_\phi(o_1, o_2) \;+\; \sum_{p \in I_2} \log n_p \cdot d_\phi(p, o_2).`
The rank $`r` enters multiplied by the distance of the two hubs. A circuit with $`L` gates will
supply such decompositions with $`r \leq L` (Lemma E.4 in {ref "chapter-flat"}[The flat case]),
and the freedom to place the hubs is what the proof exploits.

# A.3. Prices

The paper (page 20): “By Lemma A.2 a spectral point $`\phi` gives the value
$`2^{n\, d_\phi(u,v)}` to a wire that carries $`n` bits between $`u` and $`v`, so $`d_\phi(u, v)`
is what $`\phi` charges for one bit of such a wire, which explains the name in the next
definition.”

:::definition "def_price" (lean := "Nc.Price.IsPrice, Paper.def_price") (parent := "part-common")
*Definition A.4 of the paper* (price; page 20), quoted: “A _price_ on a finite set $`V` is a limit
of functions $`c\, d_\phi`, where $`c \geq 0` is a real number and $`\phi` is a spectral point on
$`V`. A function on the pairs of elements of an arbitrary set $`Y` is a price if all its
pull-backs to finite sets are prices. We write $`|xy|` for the distance of $`x` and $`y` in a
given price.” The paper adds: “Here limits are pointwise, and the pull-back of a function $`w` on
the pairs of $`Y` along a map $`g : V \to Y` is $`(x, y) \mapsto w(g(x), g(y))`.”

`Nc.Price.IsPrice K w` says that every pull-back of `w` to `Fin n` lies in the closure, in the
product topology, of the set of functions $`c\, d_\phi` on `Fin n`. `Paper.def_price` shows that
this is the printed definition: on a finite type `V`, `IsPrice K d` holds if and only if for every
$`\delta > 0` some $`\phi` and $`s \geq 0` have $`|d(u,v) - s\, d_\phi(u,v)| < \delta` for all
$`u, v`; and on any type `Y`, `IsPrice K w` holds if and only if all pull-backs along maps from
finite types are prices. The notion depends on the field `K` through the spectral points.
:::

:::lemma_ "def_price_facts" (lean := "Paper.def_price_pseudometric, Paper.def_price_pullback, Paper.def_price_multiple, Paper.def_price_limit, Paper.def_price_closed, Paper.def_price_compact") (parent := "part-common")
*Remarks after Definition A.4 of the paper* (page 20), quoted: “Prices are pseudometrics.
Pull-backs, nonnegative multiples and pointwise limits of prices are prices, where for a map
$`g : V \to W` of finite sets and a spectral point $`\phi` on $`W` one uses the spectral point
$`t \mapsto \phi(gt)` on $`V`. The prices that are bounded by a given function form a compact set,
by Tychonoff's theorem.”

The Lean theorems state these in order; the limit is along any nontrivial filter, and
compactness is in the product topology on functions `Y → Y → ℝ`.
:::

These closure properties are all that later chapters use of the definition, apart from the two
ways of making new prices: {bpref "prop_random"}[] below, and the inequality for two crossing
wires of the next chapter. Compactness is the source of the non-effective steps: it is used in
{bpref "prop_random"}[] and in the proof that one of the two cases holds
({ref "chapter-dichotomy"}[The two cases]).

# A.4. Upper functionals

The paper (page 20): “Spectral points are hard to construct directly, because they must be
exactly multiplicative, whereas submultiplicative functions arise easily as infima over covers.
The tensor rank is such a function, and for each of them we find a spectral point that is nowhere
larger (Proposition A.5).”

:::definition "def_gauge" (lean := "Ov.PreSpec, Paper.def_gauge") (parent := "part-common")
*Definition of the paper* (upper functional; page 20, unnumbered), quoted: “A function
$`p \geq 0` on the tensors on $`I` is an _upper functional_ if $`p(1) = 1`,
$`p(st) \leq p(s)p(t)` for all $`s, t`, and $`p(s) \leq \sum_j p(t_j)` whenever $`s` is covered by
$`t_1, \ldots, t_r`. One function is _below_ another if it is at most as large at every tensor.
For tensors $`x, y` and a real number $`c \geq 0` we say that $`p` _respects the triple_
$`(x, y, c)` if $`p(tx) \leq c\, p(ty)` for every tensor $`t`.”

The Lean development says _gauge_ for an upper functional (Appendix Q.3, page 66). `Ov.PreSpec`
is the structure, with the function as its field `p`, and `Paper.def_gauge` identifies it with the
printed conditions as `Paper.def_spectral` does for spectral points.
:::

:::proposition "prop_gauge" (lean := "Paper.prop_gauge") (parent := "part-common")
*Proposition A.5 of the paper* (spectral points below upper functionals; page 20), quoted: “Below
every upper functional there is a spectral point that respects every triple which the upper
functional respects.”

The Lean statement spells “respects” out for triples with $`c \geq 0`, as the printed definition
has it. The paper records no difference in the statement. On the proof, Appendix Q.3 (page 70):
“The proofs of Proposition A.5 and Theorem A.6 are carried out in a commutative monoid with a
covering relation, which is then taken to be the classes of tensors.”
:::

:::proof "prop_gauge"
*The paper's proof* (page 20), summarised. The upper functionals below the given one that respect
the triples it respects are closed under infima of chains, so by Zorn's lemma there is a minimal
one, $`p`. Two modifications of $`p` are again such upper functionals and lie below $`p`, hence
equal $`p`.

First, $`r(t) = \inf_{n \geq 1} p(t^n)^{1/n}`. Subadditivity of $`r` on a cover of $`s` by
$`t_1, \ldots, t_l` comes from covering $`s^n` by the words of length $`n` in the $`t_j` and
bounding, for $`\delta > 0`, the value of $`p` on a word with $`a_j` letters $`t_j` by
$`c_\delta^{\,l} \prod_j (r(t_j) + \delta)^{a_j}`. Minimality gives $`r = p`, that is,
$`p(t^n) = p(t)^n`.

Second, for $`f` with $`p(f) > 0`, $`p_f(t) = \inf_{n \geq 0} p(t f^n)/p(f)^n`. Minimality gives
$`p_f = p`, hence $`p(t) \leq p(tf)/p(f)`, and with submultiplicativity $`p(tf) = p(t)p(f)`. If
$`p(f) = 0` then $`p(tf) = 0`. So $`p` is multiplicative.

In Lean the steps are theorems about a function on a commutative monoid with a covering relation
(`Ov.Cover`, `Ov.IsPre` in {repoFile "vp-vnp/Ov/Duality/Abstract.lean"}[`Ov/Duality/Abstract.lean`]):
`Paper.prop_gauge_chain` and `Paper.prop_gauge_minimal` (the infimum of a chain and the minimal
element), `Paper.prop_gauge_radius` and `Paper.prop_gauge_radius_pow` (the function $`r` and
$`p(t^n) = p(t)^n`), `Paper.prop_gauge_localize` (the function $`p_f`), and
`Paper.prop_gauge_monoid` (the multiplicative function below). Appendix Q.3 (page 70) notes that
“the fact that $`r` in the proof of Proposition A.5 is also a limit” is not formalized; the Lean
proof uses the infimum.
:::

The spectral point of Proposition A.5 is obtained from Zorn's lemma, and the statements below
that produce spectral points or prices (Theorem A.6 in its proof, Propositions A.7 and A.8) all
rest on it. They assert existence and give no formula.

# A.5. Duality

:::theorem "thm_duality" (lean := "Paper.thm_duality") (parent := "part-common")
*Theorem A.6 of the paper* (duality; page 20), quoted: “Let $`C \neq 0` and
$`A_1, \ldots, A_r` be tensors on $`I`, not all $`A_\beta` zero, and suppose that every spectral
point $`\phi` on $`I` satisfies $`\phi(C) \leq \max_\beta \phi(A_\beta)`. Then for every
$`\varepsilon > 0` and all large $`N` the power $`C^N` is covered by at most
$`2^{\varepsilon N}` tensors, each of which is a product of $`N` factors from
$`A_1, \ldots, A_r`.”

The paper introduces it as “a form of Strassen's duality theorem \[Str88\], for the larger class
of spectral points of Definition A.1”, and comments (page 20): “Informally, if no spectral point
detects that $`C` is larger than all the $`A_\beta`, then $`C^N` can be made from products of
$`N` of the $`A_\beta` with only $`2^{\varepsilon N}` summands. All identities of Sections G to J
arise in this way, and none of them is written down explicitly.”

The Lean statement differs as the paper says (Appendix Q.3, page 68): “The families of tensors in
Theorem A.6 and of maps in Proposition A.7 are indexed by any finite set.” Here that set is the
type `B`. The cover is given by a number `m` with $`m \leq 2^{\varepsilon N}` and exponent
vectors $`v_i \in \mathbb{N}^B` with $`\sum_\beta v_i(\beta) = N`, the $`i`th tensor of the cover
being $`\prod_\beta A_\beta^{v_i(\beta)}`.
:::

:::proof "thm_duality"
*The paper's proof* (page 21), summarised. Let $`\eta = 2^{-\varepsilon/2}`. A _certificate_ of
level $`k` for a tensor $`t` is a cover of $`t C^k` by products $`C^{u_j} A^{v_j}` with
$`u_j + |v_j| = k`; its _weight_ is $`\sum_j \eta^{|v_j|}`. Let $`p(t)` be the infimum of the
weights of the certificates for $`t`. Certificates multiply, can be raised to a common level and
added along covers, so $`p` is an upper functional provided $`p(1) \geq 1`; and it respects the
triples $`(A_\beta, C, \eta)`. If $`p(1) \geq 1`, Proposition A.5 gives a spectral point with
$`\phi(A_\beta) \leq \eta\, \phi(C)` for all $`\beta`, contradicting the hypothesis because
$`\phi(C) \geq 1`. Hence $`1` has a certificate of some level $`k \geq 1` and weight less than
$`1`: a cover of $`C^k` by terms in each of which at least one $`C` has been exchanged for an
$`A_\beta`. Starting from $`C^N`, replace $`C^k` by this cover as long as a term contains it; the
total weight stays at most $`1` and every final term has weight at least $`\eta^N`, so there are
at most $`\eta^{-N}` terms. The fewer than $`k` remaining factors $`C` of each term are covered by
a fixed number $`c` of copies of a nonzero $`A_\beta`, giving at most
$`c^k \eta^{-N} \leq 2^{\varepsilon N}` terms for large $`N`.

The Lean steps are `Paper.thm_duality_gauge` (the function $`p` is an upper functional that
respects the triples, if no certificate of $`1` has weight below $`1`),
`Paper.thm_duality_exchange`, `Paper.thm_duality_replace`, `Paper.thm_duality_copies` and
`Paper.thm_duality_cover`. Appendix Q.3 (page 70) notes a difference of bookkeeping: “In the proof
of Theorem A.6 the certificate is first raised by one level, and the number of terms is bounded by
$`(c+1)^{k+1} \eta^{-N}`.”
:::

Duality turns an inequality that holds for all spectral points into an identity between tensors.
It is not used in the flat case. In the contracting case it is the step from the Poincaré
inequality to the rerouting laws ({ref "chapter-laws"}[Rerouting laws and tree networks]), and it
is the reason why those laws are not explicit.

# A.6. Extension and random points

The paper (page 21): “In Sections C and E we add new points to a price by placing each of them at
one of the old points, chosen at random, and Proposition A.8 below provides an enlarged price in
which distances are at most the expected distances of these positions.”

:::proposition "prop_extend" (lean := "Paper.prop_extend") (parent := "part-common")
*Proposition A.7 of the paper* (extension; page 21), quoted: “Let $`\iota : I \to I'` and
$`\pi_i : I' \to I`, for $`i = 1, \ldots, n`, be maps of finite sets with
$`\pi_i \iota = \mathrm{id}` for all $`i`, and let $`\theta_1, \ldots, \theta_n \geq 0` add up to
$`1`. Let $`\phi` be a spectral point on $`I` and let $`C` be a tensor on $`I`. Then there is a
spectral point $`\phi'` on $`I'` with
$$`\phi'(t) \leq \prod_i \phi(\pi_i t)^{\theta_i} \ \text{ for all tensors } t \text{ on } I', \qquad \phi'(\iota C) = \phi(C).`”

In the Lean statement the maps $`\pi_i` and the weights $`\theta_i` are indexed by a finite type
`L` (the quotation of Appendix Q.3 under {bpref "thm_duality"}[]).
:::

:::proof "prop_extend"
*The paper's proof* (page 21), summarised. Let $`f(t) = \prod_i \phi(\pi_i t)^{\theta_i}`, which
is multiplicative and monotone under restriction, and let $`p(t)` be the infimum of
$`\sum_j f(b_j)` over the covers $`(b_j)` of $`t`. If $`\iota A = \sum_j s_j` with $`s_j` a
restriction of $`b_j`, then each $`s_j` is $`\iota a_j` with $`\sum_j a_j = A`, and
$`a_j = \pi_i s_j` is a restriction of $`\pi_i b_j` for every $`i`; hence
$`\phi(A) \leq \sum_j \phi(a_j) \leq \sum_j f(b_j)`. So $`p(\iota A) = \phi(A)` for all $`A`, and
$`p` is an upper functional below $`f`. For $`C \neq 0`, with $`c = \phi(C)`, the function
$`q(t) = \inf_{m \geq 0} p(t\, \iota C^m)/c^m` is an upper functional below $`p` that respects the
triple $`(1, \iota C, 1/c)`; Proposition A.5 gives a spectral point $`\phi'` below $`q` that
respects it, so $`c \leq \phi'(\iota C) \leq f(\iota C) = c`.

The Lean steps: `Paper.prop_extend_product` (properties of $`f`), `Paper.prop_extend_cover` and
`Paper.prop_extend_lower` (the lower bound $`\phi(A) \leq \sum_j f(b_j)`),
`Paper.prop_extend_upper`, `Paper.prop_extend_gauge` (the upper functional $`p`), and
`Paper.prop_extend_localize` (the function $`q`).
:::

:::proposition "prop_random" (lean := "Paper.prop_random, Paper.prop_random_finite") (parent := "part-common")
*Proposition A.8 of the paper* (random points; page 21), quoted: “Let $`w` be a price on $`Y`, let
$`Q` be a set disjoint from $`Y`, and let $`\sigma` be a random map $`Y \cup Q \to Y` that is the
identity on $`Y`, such that each $`\sigma(o)` has only finitely many values. Then there is a price
on $`Y \cup Q` that extends $`w` and satisfies
$`|oo'| \leq \mathbb{E}\, |\sigma(o)\sigma(o')|` for all $`o, o' \in Y \cup Q`.”

In `Paper.prop_random` the random map is a family `σ : Q → Ω → Y` of functions on a probability
space `(Ω, μ)`, each with finite range and measurable fibres; the disjoint union is the sum type
`Y ⊕ Q`, the identity on `Y` is built in, and the expectation is the integral. The paper does not
remark on this encoding. `Paper.prop_random_finite` is the case of a finite probability space,
given by weights $`\theta_l \geq 0` with sum $`1` and maps `σ l : Q → Y`, in which the bound reads
$`w'(o, o') \leq \sum_l \theta_l\, w(\sigma_l o, \sigma_l o')`.
:::

:::proof "prop_random"
*The paper's proof* (page 22), summarised. By compactness of the prices bounded by a given
function it suffices to treat finite $`Y` and $`Q`; by a limit and homogeneity, $`w = d_\phi`. Let
$`\sigma` take the values $`\pi_i` with probabilities $`\theta_i`, and apply Proposition A.7 to
the inclusion of $`Y`, the maps $`\pi_i`, and $`C` the product of all wires
$`\langle 2 \rangle_{uv}` with $`u, v \in Y`. The first conclusion, applied to
$`\langle 2 \rangle_e`, gives $`d_{\phi'}(e) \leq \sum_i \theta_i\, d_\phi(\pi_i e)`, the expected
distance. On $`Y` this reads $`d_{\phi'} \leq d_\phi`, and by the second conclusion the sums over
all pairs in $`Y` are equal, so equality holds for each pair.

The Lean steps: `Paper.prop_random_spectral` (the statement for one spectral point),
`Paper.prop_random_limit` (finite sets, any price), `Paper.prop_random_compact` (the compactness
step) and `Paper.prop_random_values` (a random map with finitely many values on a finite set of
new points is a finite convex combination of maps).
:::

The role of the tensor $`C` in Proposition A.7 is visible here: the condition
$`\phi'(\iota C) = \phi(C)` for a product $`C` of wires, together with
$`\phi' \leq \phi` on each factor, pins every old distance. The same device, with one more factor
in $`C`, keeps an exponent $`g_\phi` fixed in Lemma E.8 ({ref "chapter-flat"}[The flat case]).

# What the rest of the proof takes from this chapter

- {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature] takes
  {bpref "lem_exponents"}[], {bpref "lem_hubs"}[] and the subadditivity of spectral points on
  covers for the crossing inequality, and {bpref "prop_random"}[] with the closure properties of
  prices for everything after it. The paper (page 25): “The only properties of prices that we use
  are Proposition A.8, the inequality (B.2), and the fact that pull-backs, nonnegative multiples
  and limits of prices are prices.”
- {ref "chapter-flat"}[The flat case] takes {bpref "lem_hubs"}[] for the tensors that a circuit
  produces, and {bpref "prop_extend"}[] for the exponent of a set of points.
- {ref "chapter-laws"}[Rerouting laws and tree networks] takes {bpref "thm_duality"}[].
