/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import VpVnpBlueprint.Chapters.SpectralPoints
import VpVnpBlueprint.Chapters.Curvature
import VpVnpBlueprint.Chapters.Dichotomy
import Paper.Groups

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "A Poincaré inequality on unitriangular groups" =>

%%%
tag := "chapter-poincare"
file := "poincare"
htmlSplit := .never
number := false
%%%

This chapter follows Appendix F of the paper (pages 37–41;
{repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and opens the contracting case. It leads to the one
statement that the rest of the proof uses, {bpref "thm_poincare"}[Theorem F.6]: in every price on the group $`U_h` of upper
unitriangular $`h \times h` matrices over $`\mathbb{F}_2`, the mean squared distance of two random
elements is at most $`C_0` times the sum, over the $`h-1` generators, of the mean squared distance
of two neighbours in the Cayley graph, with a constant $`C_0` that does not depend on $`h`. The
paper, page 37: “Only Theorem F.6 is used later.” In {ref "chapter-laws"}[the next chapter] the
independence of $`h` allows $`h` to be chosen large against $`C_0`, which is what makes rerouting
along edges of the Cayley graph gain a constant factor at every stage of a tower.

The hypothesis of the contracting case ({bpref "def_cases"}[Definition D.1],
{ref "chapter-dichotomy"}[The two cases]) enters only through the notion of a contracting length
function of Section F.1. From there on the argument is metric geometry in complete CAT(0) spaces,
for which {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature] provides
{bpref "prop_space"}[Proposition C.3] and {bpref "lem_toolkit"}[Lemma C.4]. The paper counts this appendix among those whose printed proofs “are meant to be
complete, if terse” (page 17). The Lean statements differ from the printed ones in three ways,
which Section Q.3 (page 68) lists and which are stated at each item below: Lemmas F.1 and F.2 are
proved under weaker hypotheses; Lemma F.3 is stated for explicit numbers $`\vartheta_n` that are
not those of the printed proof, so that the constant $`C(n)` of (F.1) and of Lemmas F.4 and F.5 is
formed with them; and the projection to the fixed points of a window is defined as a barycenter.

The paper, page 37: “In this section and in Sections G to K we are in the contracting case, and we
fix $`\mu` and $`s` as in Definition D.1.” In Lean nothing is fixed: the theorems of Sections F.1
and F.2 take $`\mu`, $`s` and the inequalities $`2 \le \mu`, $`1 \le s`, $`s^2 < \mu` as explicit
arguments, and Theorem F.6 takes the hypothesis `Paper.Contracting K` and unpacks it.

:::definition "unitriangular_group" (lean := "Nc.Tower.U, Nc.Tower.x") (parent := "part-contracting")
*The group and its generators* (page 37), quoted: “Let $`U_n` be the group of the upper
unitriangular $`n \times n` matrices over $`\mathbb{F}_2`. We number the coordinates by
$`0, \ldots, n-1` and use the generators $`x_j = 1 + E_{j,j+1}`, $`0 \le j < n-1`, where $`E_{jk}`
is the matrix whose only nonzero entry is a $`1` in row $`j` and column $`k`. The generators
$`x_i` and $`x_j` commute if $`|i-j| \ge 2`.”

In Lean `U h` is a subgroup of $`\mathrm{SL}_h(\mathbb{F}_2)`, and `x h j` is the transvection
with the entry $`1` at $`(j, j+1)`, for `j : Fin (h - 1)`.
:::

# F.1. Contracting length functions

:::definition "contracting_length" (lean := "Nc.Flag.Contr, Paper.rankMean, Paper.contracts_iff") (parent := "part-contracting")
*Length functions; contracting* (page 38), quoted: “A _length function_ on a group is a function
$`g \mapsto |g| \ge 0` with $`|1| = 0`, $`|g^{-1}| = |g|` and $`|gg'| \le |g| + |g'|`. We say that
it _contracts_ if for every homomorphism $`\theta` from the additive group
$`\mathrm{Mat}_\mu(\mathbb{F}_2)` into the group, the mean of $`|\theta W|^2` over the matrices
$`W` of rank $`\mu` is at most $`s^2` times the mean over the matrices of rank $`1`.”

In Lean a length function is the structure `Nc.Flag.Len`, with the three laws as fields; nonnegativity follows from them. The Lean
predicate `Contr l μ s` is written with the sums of $`|\theta(pMq)|^2` over
$`p, q \in \mathrm{GL}_\mu(\mathbb{F}_2)`, for $`M` the identity and for $`M` each diagonal matrix
unit, and `contracts_iff` proves, for $`\mu \ge 1`, that it is the printed condition, where
`rankMean f r` is the mean of $`f^2` over the matrices of rank $`r`. Neither form carries the
conditions $`\mu \ge 2`, $`1 \le s`, $`s^2 < \mu`.
:::

:::lemma_ "lengths_of_maps" (lean := "Paper.lengths_of_maps") (parent := "part-contracting")
*The remark after the definition* (length functions from maps into price spaces; page 38), quoted:
“Let $`f` be a map of a finite group $`G` into a price space. Then
$`|g| = \bigl(\mathbb{E}_a |f(a) f(ga)|^2\bigr)^{1/2}`, with $`a` uniformly distributed in $`G`, is
a length function on $`G` that contracts.”

This is where the hypothesis of the contracting case enters the chapter. The Lean statement takes
that hypothesis as its argument `hcase` (every price on $`\mathrm{Mat}_\mu(\mathbb{F}_2)` has
$`D(\mu) \le s D(1)`), a metric space $`Y` whose metric is a price, and any map $`f : G \to Y`, and
it produces a length function with the printed formula that contracts.
:::

:::proof "lengths_of_maps"
*The paper's argument* (page 38), quoted: “for a homomorphism
$`\theta : \mathrm{Mat}_\mu(\mathbb{F}_2) \to G` and $`a \in G`, the pull-back of the metric along
$`W \mapsto f(\theta(W)a)` is a price on $`\mathrm{Mat}_\mu(\mathbb{F}_2)`, so it has
$`D(\mu)^2 \le s^2 D(1)^2` by the contracting hypothesis, and the mean over $`a` is the claim.”
:::

:::lemma_ "lem_growth" (lean := "Paper.lem_growth") (parent := "part-contracting")
*Lemma F.1 of the paper* (growth of the mean length with the rank; page 38), quoted: “Let
$`1 \le r \le k`, let $`\theta` be a homomorphism from the additive group
$`\mathrm{Mat}_{k \times k}(\mathbb{F}_2)` into a group with a contracting length function, and let
$`D(r)` be the root mean square of $`|\theta W|` over the matrices $`W` of rank $`r`. Then
$`D(r) \le \mu (j+1) s^j D(1)`, where $`j = \lfloor \log_\mu r \rfloor`.”

The Lean statement is more general. Section Q.3 (page 68): “In Section F Lemma F.1 is proved
without the assumption $`s^2 < \mu` and also for $`r = 0`”. Its hypotheses are $`2 \le \mu`,
$`1 \le s`, `Contr l μ s` and $`r \le k`.
:::

:::proof "lem_growth"
*The paper's proof* (page 38), summarised. Two inequalities and an expansion in base $`\mu`. First,
$`D(\mu i) \le s\, D(i)` if $`\mu i \le k`: compose $`\theta` with
$`Z \mapsto \alpha (Z \otimes 1_i) \alpha'` for uniformly random $`k \times \mu i` and
$`\mu i \times k` matrices $`\alpha`, $`\alpha'` of full rank; this homomorphism from
$`\mathrm{Mat}_\mu(\mathbb{F}_2)` multiplies ranks by $`i` and sends a fixed $`Z` to a uniformly
distributed matrix of its rank, so the mean of the contraction inequality over $`\alpha, \alpha'`
is the claim. Second, $`D(i+i') \le D(i) + D(i')` if $`i + i' \le k`, by Minkowski's inequality
for a random transversal pair as in Step 1 of the proof of Theorem D.2. Writing
$`r = \sum_{t \le j} d_t \mu^t` with digits $`0 \le d_t < \mu` then gives
$`D(r) \le \sum_t d_t s^t D(1) \le \mu (j+1) s^j D(1)`, because $`s \ge 1`.

In Lean the two inequalities are `Paper.lem_growth_digit` and `Paper.lem_growth_minkowski`, and
the expansion is a strong induction on $`r` through
$`r = \mu \lfloor r/\mu \rfloor + (r \bmod \mu)`. Section Q.3 (page 70) names “the averaging in
Lemma F.1” among the steps that “exist only under names of the underlying library and not as
theorems with prefix `Paper.`”.
:::

:::lemma_ "lem_words" (lean := "Paper.lem_words") (parent := "part-contracting")
*Lemma F.2 of the paper* (length of the elements of rank one; page 38), quoted: “Let
$`1 \le k < n`, and let $`\xi \in \mathbb{F}_2^k` and $`\omega \in \mathbb{F}_2^{n-k}` be nonzero.
The element of $`U_n` with the upper right block $`\xi \omega^{\mathsf{T}}` and with unit diagonal
blocks has, in every length function on $`U_n`, length at most $`18 \sum_j |x_j|`.”

The Lean statement is more general. Section Q.3 (page 68): “Lemma F.2 without the conditions
$`1 \le k < n` and $`\xi, \omega \neq 0`”. It takes vectors $`u, \varphi \in \mathbb{F}_2^n` with
$`u` supported on the coordinates below $`k` and $`\varphi` on those from $`k` on, and an element
of $`U_n` with the matrix $`1 + u \varphi^{\mathsf{T}}`. No contraction is assumed: the bound holds
for every length function.
:::

:::proof "lem_words"
*The paper's proof* (page 38), summarised. The element is written as a word in which each generator
occurs at most $`16` times (the statement has $`18`). If the last entry of $`\xi` and the first
entry of $`\omega` are $`1`, then with $`e` the last unit vector of $`\mathbb{F}_2^k` and
$`i_1 < \cdots < i_l` the places where $`\xi` has a $`0`, the word
$`A = x_{i_l} \cdots x_{i_1} x_0 \cdots x_{k-2}` has $`A e = \xi` and uses each generator at most
twice; likewise a word $`B` in the $`x_j`, $`j \ge k`, has
$`e'^{\mathsf{T}} B = \omega^{\mathsf{T}}` for the first unit vector $`e'` of
$`\mathbb{F}_2^{n-k}`; and the element is $`A B^{-1} x_{k-1} B A^{-1}`, since $`x_{k-1}` has the
upper right block $`e e'^{\mathsf{T}}`. In general $`\xi` and $`\omega` are sums of at most two
such vectors each, which gives a product of at most four such elements.

Section Q.3 (page 70) names “the word in Lemma F.2” among the steps that exist only under names of
the underlying library.
:::

:::lemma_ "lem_first" (lean := "Paper.lem_first, Paper.kappa") (parent := "part-contracting")
*Lemma F.3 of the paper* (mean length on $`U_n`; page 38), quoted: “There are numbers
$`\vartheta_n` with $`\vartheta_n^2 n = o(n^2)` such that every contracting length function on
$`U_n` satisfies $`(\mathbb{E}_g |g|^2)^{1/2} \le \vartheta_n \sum_j |x_j|`.”

The Lean statement is for explicit numbers, and they are not the numbers of the printed proof.
Section Q.3 (page 68): “Lean states Lemma F.3 for explicit numbers,
$`\vartheta_n = 18 \lceil \log_2 n \rceil\, \mu (L+1) s^L` with
$`L = \lfloor \log_\mu 2^{\lceil \log_2 n \rceil} \rfloor` (`kappa`), which are not those of the
printed proof, and $`C(n)` in (F.1) and in Lemmas F.4 and F.5 is formed with them.” The printed
proof takes, along the powers of two, the numbers with
$`\vartheta_n = \vartheta_{n/2} + 18 \mu (d+1) s^d`, $`d = \lfloor \log_\mu n \rfloor`, and
$`\vartheta_1 = 0`. The Lean theorem has two conjuncts, for $`2 \le \mu`, $`1 \le s` and
$`s^2 < \mu`: that $`\vartheta_n^2 n / n^2 \to 0` for the numbers $`\vartheta_n =` `kappa μ s n`,
and the inequality for every $`n` and every contracting length function on $`U_n`. The printed
statement, which asserts only that such numbers exist, follows from it. Later statements that
mention $`C(n)` are, in Lean, statements about this particular sequence.
:::

:::proof "lem_first" (uses := "lem_growth, lem_words")
*The paper's proof* (pages 38–39), summarised. Induction along the powers of two, which suffices
because $`U_n` is a quotient of every larger $`U_{n'}` “in such a way that generators go to
generators or to $`1`”. For $`n = 2^{i+1}`, divide the matrices into four blocks of size $`n/2`. A
uniformly distributed element of $`U_n` is the product of a uniformly distributed element of the
abelian upper right block, a copy of $`\mathrm{Mat}_{n/2 \times n/2}(\mathbb{F}_2)`, and of
uniformly distributed elements of the two diagonal blocks, copies of $`U_{n/2}`. Lemmas F.1 and
F.2 bound the root mean square length of the first factor by a multiple of $`\sum_j |x_j|`; the
induction hypothesis applies to the other two, which use disjoint sets of generators; Minkowski's
inequality adds the three. This gives
$`\vartheta_n = O\bigl((\log n + 1)^2 s^{\log_\mu n}\bigr)`, and
$`\vartheta_n^2 n = o(n^2)` “because $`s^2 < \mu`”.

In Lean the step of the induction is `Paper.lem_first_double`: a bound with the constant
$`\kappa` for $`U_a` gives one with the constant $`18\, \mu (j+1) s^j + \kappa`,
$`j = \lfloor \log_\mu a \rfloor`, for $`U_{2a}`. The proof of `lem_first` adds these along the
powers of two up to $`2^{\lceil \log_2 n \rceil}`, bounding every term by the one for the last
power, and passes to $`n` through the quotient map; this is the closed form `kappa`. The rate is
`Paper.kappa_small`.
:::

# F.2. Windows and their fixed points

The setting of this section (page 39), quoted: “Let $`U_h` act by isometries on a CAT(0) space
$`Z`, and suppose that for every $`z \in Z` the length function $`g \mapsto |z, gz|` on $`U_h`
contracts.” In Lean the space is a metric space of the class {bpref "CN"}[`Cat.CN`] of
{ref "chapter-curvature"}[the chapter on curvature]: a complete metric space in which every two
points have a midpoint that satisfies the inequality of Bruhat and Tits.

:::definition "windows" (lean := "Nc.Flag.IsoAct.len, Nc.Flag.IsoAct.W, Nc.Flag.IsoAct.Fix, Nc.Flag.IsoAct.P, Paper.fixed_closed_convex, Paper.projection_nearest") (parent := "part-contracting")
*Windows and their projections* (page 39), quoted: “For $`p + n \le h` the _window_ $`[p, p+n)` is
the subgroup of the matrices that differ from the identity only in the rows and columns
$`p, \ldots, p+n-1`, a copy of $`U_n` generated by $`x_p, \ldots, x_{p+n-2}`. The points of $`Z`
that a window fixes form a closed convex set, which contains the barycenter of every orbit of the
window. We write $`P_{[p,p+n)}` for the nearest-point projection to this set (Lemma C.4(d)).”

In Lean an action by isometries is the structure `Nc.Flag.IsoAct`; `A.len z` is the length function
$`g \mapsto |z, gz|`; `A.W p n` is the action of $`U_n` through its embedding as the window
$`[p, p+n)`; and `A.Fix z` says that every element fixes $`z`. The projection differs in its
definition. Section Q.3 (page 68): “Lean defines the projection to the fixed points of a window
(Section F) as the barycenter of the orbit, and `projection_nearest` shows that this is the nearest
point.” So `(A.W p n).P z` is a barycenter of the orbit of $`z` under the window, and
`projection_nearest` states that it is fixed, that no fixed point is nearer to $`z`, and that it is
the only fixed point with this property. `fixed_closed_convex` states that the fixed points form a
closed set that contains the midpoint of any two of its points and the point `P z` of every $`z`.
:::

:::lemma_ "eq_window" (lean := "Paper.eq_window, Paper.windowConst") (parent := "part-contracting")
*Display (F.1) of the paper* (page 39). With $`\delta_j(z) = |z, x_j z|`, quoted:
$$`\begin{aligned} |z, P_{[p,p+n)} z|^2 &\le C(n) \sum_{p \le j < p+n-1} \delta_j(z)^2, \\ C(n) &= \vartheta_n^2 n = o(n^2). \end{aligned}`

Table 3 of the paper (Section Q.2, pages 66–67) lists this display, with the two Lean theorems
`eq_window` and `projection_nearest`; Section Q.2 (page 66): “it also lists the display (F.1), and
`eq_Q` is the display (B.2)”. The Lean constant is `windowConst μ s n`, which is
$`\vartheta_n^2 n` for the numbers `kappa` of the Lean form of Lemma F.3, not for those of the
printed proof.
:::

:::proof "eq_window"
*The paper's derivation* (page 39), quoted: “By Lemma C.4(c) for the orbit of a point $`z` we have
$`|z, Pz|^2 \le \mathbb{E}_g |z, gz|^2` for $`P = P_{[p,p+n)}`, with $`g` uniformly distributed in
the window”; then “Lemma F.3 for the window and the Cauchy–Schwarz inequality” give the display.
The factor $`n` in $`C(n)` comes from the Cauchy–Schwarz inequality over the $`n - 1` generators of
the window.
:::

The paper continues (page 39): “If two windows have no coordinate in common, then they commute,
and therefore the projection of one of them maps the fixed points of the other to fixed points of
the other” (in Lean `Paper.windows_commute`), and: “The windows $`[p, p+2u)` and $`[p+u, p+3u)`
generate $`[p, p+3u)`, which therefore fixes exactly their common fixed points”.

:::lemma_ "lem_tele" (lean := "Paper.lem_tele") (parent := "part-contracting")
*Lemma F.4 of the paper* (projections for overlapping windows; page 39), quoted: “Let $`u \ge 2`,
$`p + 3u \le h`, $`\zeta \ge 0` and $`4C(3u) \le \zeta^2 (u-1)^2`. If $`a` is fixed by
$`[p, p+2u)`, then $`|a, P_{[p+u,p+3u)} a| \ge (1 - \zeta) R`, where $`R = |a, P_{[p,p+3u)} a|`.”

The Lean statement has the printed form, with the standing hypotheses of Section F.2 written out
and with $`C(3u)` the number `windowConst μ s (3 * u)` (Section Q.3, page 68, quoted at Lemma
F.3).
:::

:::proof "lem_tele" (uses := "lem_first, eq_window")
*The paper's proof* (pages 39–40), summarised. Take $`p = 0` and pass from the window $`[u, 3u)`
to $`[0, 3u)` through the windows $`[k, 3u)`: let $`b_k = P_{[k,3u)} a` for $`u \le k < 2u`, so
that $`|a b_k| \le |a b_u| \le R`. For $`u < k < 2u` every generator of $`[0, 3u)` fixes $`b_k`
except possibly $`x_{k-1}`: the later ones by definition, the earlier ones because they fix $`a`
and commute with $`[k, 3u)`. As $`x_{k-1}` fixes $`b_{k-1}`, it moves $`b_k` by at most
$`2 |b_{k-1} b_k|`, and $`|b_{k-1} b_k|^2 \le |a b_{k-1}|^2 - |a b_k|^2` by Lemma C.4(d). For the
barycenter $`\bar b` of the $`u - 1` points $`b_k`, $`u < k < 2u`, Lemma C.4(c) and a telescoping
sum give
$$`\begin{aligned} \sum_j \delta_j(\bar b)^2 &\le \frac{4}{(u-1)^2} \sum_{u < k < 2u} \bigl(|a b_{k-1}|^2 - |a b_k|^2\bigr) \\ &\le \frac{4R^2}{(u-1)^2}. \end{aligned}`
By (F.1) for $`[0, 3u)` and the hypothesis on $`\zeta`, the point $`\bar b` is within $`\zeta R` of
a point fixed by $`[0, 3u)`, and $`|a \bar b| \le |a b_u|`; hence
$`R \le |a \bar b| + \zeta R \le |a b_u| + \zeta R`. The gain is the factor $`1/(u-1)`: each
generator moves only one of the $`u - 1` averaged points, and this is set against
$`C(3u) = o(u^2)`.
:::

:::lemma_ "lem_angle" (lean := "Paper.lem_angle") (parent := "part-contracting")
*Lemma F.5 of the paper* (almost right angles; page 40), quoted: “Let $`u, p, \zeta` be as in Lemma
F.4, and let $`0 \le \zeta \le 1`, $`c > 0` and $`1 - c^2 \le (1 - \zeta)^2`. If $`a` and $`a'` are
the projections of a point $`z` for the windows $`[p, p+2u)` and $`[p+u, p+3u)`, then
$`|aa'|^2 \le |za|^2 + |za'|^2 + 2c\,|za|\,|za'|`.”

The Lean statement has the printed form, with $`C(3u)` formed with `kappa` as in Lemma F.4.
:::

:::proof "lem_angle" (uses := "lem_tele, lem_toolkit")
*The paper's proof* (page 40), summarised. Let $`v = P_{[p,p+3u)} a`, $`r = |za|`, $`r' = |za'|`,
$`\alpha = |av|`, $`\beta = |va'|`, all positive without loss. First step, the angle at the common
fixed point $`v`: the inequality (F.2), $`\alpha^2 + \beta^2 - 2c\alpha\beta \le |aa'|^2`. For
this take $`q` and $`q'` at the distances $`\sigma\alpha` and $`\sigma'\beta` from $`v` on the
segments to $`a` and $`a'`, with $`\sigma'\beta = c\,\sigma\alpha`. The point $`q` is fixed by
$`[p, p+2u)` and projects to $`v` for $`[p, p+3u)`, so Lemma F.4 and the hypothesis on $`c` give
$`|qq'|^2 \ge (1 - c^2) \sigma^2 \alpha^2`, while Lemma C.4(a), applied twice, gives
$`|qq'|^2 \le \sigma^2\alpha^2 + \sigma'^2\beta^2 - \sigma\sigma'(\alpha^2 + \beta^2 - |aa'|^2)`.
Second step, the quadrilateral $`z, a, v, a'`: $`r^2 + \alpha^2` and $`r'^2 + \beta^2` are at most
$`|zv|^2` by Lemma C.4(d), and Lemma C.4(a), applied to a point on the segment from $`a` to $`a'`
and to one on the segment from $`z` to $`v` with suitable parameters, gives
$`(rr' + \alpha\beta)\,|aa'|^2 \le \alpha\beta\,(r^2 + r'^2) + rr'\,(\alpha^2 + \beta^2)`; inserting
(F.2) on the right gives the claim.

In Lean the argument is carried by `Paper.lem_angle_projections`, stated for two arbitrary
isometric actions of finite groups with a common fixed point $`v` and with the lower bound for
$`|qq'|` as a hypothesis; `Paper.lem_angle` supplies that hypothesis from Lemma F.4.
:::

# F.3. Proof of the Poincaré inequality

:::theorem "thm_poincare" (lean := "Paper.thm_poincare, Paper.PoincareBound") (parent := "part-contracting")
*Theorem F.6 of the paper* (Poincaré inequality; page 40), quoted: “There are an integer
$`u \ge 2` and a real number $`C_0 \ge 0` such that for every $`l \ge 2`, $`h = lu`, and every
price on $`U_h`
$$`\mathbb{E}_{g,a} |a, ga|^2 \le C_0 \sum_{j < h-1} \mathbb{E}_a |a, x_j a|^2.`”
Here “$`g` and $`a` are independent and uniformly distributed in $`U_h`”.

The Lean statement is the printed one, for a field `K` in the contracting case
(`Paper.Contracting K`) and prices over `K` (`Nc.Price.IsPrice K w`), with the two means written
as sums divided by $`|U_h|^2` and by $`|U_h|`. `PoincareBound K u C₀` is the name of the
inequality for given $`u` and $`C_0`, under which {ref "chapter-laws"}[the next chapter] carries
it. Section Q.3 (page 68) remarks on the proof only: “In the proof of Theorem F.6 the space of
functions carries the sum where the text has the mean, which is one scaling factor.” The Lean
proof takes $`C_0 = 32\,C(2u)/(1 - 2c)` with $`c = 1/4`, as printed, with $`C(n)` formed with
`kappa`.
:::

:::proof "thm_poincare" (uses := "lem_first, thm_poincare_action")
*The paper's proof* (pages 40–41), summarised. Since $`C(n) = o(n^2)`, there is $`u \ge 2` with
$`4C(3u) \le (u-1)^2/32^2`; fix it and put $`\zeta = 1/32`, $`c = 1/4`. By Proposition C.3 the
price is pulled back from the metric of a price space $`Y` along a map $`f : U_h \to Y`. Let $`Z`
be the set of all maps $`z : U_h \to Y` with the metric
$`|zz'| = (\mathbb{E}_a |z(a) z'(a)|^2)^{1/2}`, which is CAT(0) by Lemma C.4(e), and let $`U_h` act
by $`(gz)(a) = z(g^{-1}a)`. The length functions $`g \mapsto |z, gz|` contract by the remark of
Section F.1, so Section F.2 applies to $`Z`.

_Distances between projections._ Let $`k = l - 1`, let $`Q_i` be the projection for the window
$`[iu, iu+2u)`, $`0 \le i < k`, and put $`r_i = |z, Q_i z|` and $`\Phi(z) = \sum_i r_i^2`. The
claim (F.3) is that $`|Q_i z, Q_{i'} z|^2 \le r_i^2 + r_{i'}^2` if $`|i - i'| \ge 2`, because the
two windows commute and the proof of Lemma F.5 applies with $`\zeta = 0` and every $`c > 0`, and
that $`|Q_i z, Q_{i+1} z|^2 \le (1 + c)(r_i^2 + r_{i+1}^2)`, by Lemma F.5.

_One step of averaging._ For the barycenter $`b` of the $`k` points $`Q_i z`, Lemma C.4(c) and
(F.3) give
$$`\begin{aligned} \Phi(b) &\le \Bigl(1 - \frac{1 - 2c}{k}\Bigr) \Phi(z), \\ k\,|zb|^2 &\le \Phi(z) - \Phi(b), \end{aligned}`
and hence $`|zb| \le \frac{2}{\sqrt{1-2c}} \bigl(\sqrt{\Phi(z)} - \sqrt{\Phi(b)}\bigr)` if
$`\Phi(z) > 0`. In this last bound $`k` has cancelled: the decrease of $`\Phi` by the factor
$`1 - (1-2c)/k` is set against the factor $`k` in the bound for the step, and this is how the
constant becomes independent of $`l`.

_Iteration._ Iterating $`z \mapsto b`, the values of $`\Phi` decrease geometrically and the steps
add up to at most $`2\sqrt{\Phi(z)/(1-2c)}`, so the points converge to a point fixed by every
window and hence by $`U_h`, and $`|z, P_{[0,h)} z|^2 \le \frac{4}{1-2c} \Phi(z)`. Each generator
lies in at most two of the windows, so (F.1) for $`n = 2u` gives
$`\Phi(z) \le 2C(2u) \sum_j \delta_j(z)^2`, and $`|z, gz| \le 2\,|z, P_{[0,h)} z|`. For $`z = f`
this is the theorem with $`C_0 = 32\,C(2u)/(1-2c)`.

In Lean the steps are the theorems `Paper.thm_poincare_size` (the choice of $`u`),
`Paper.thm_poincare_far` and `Paper.thm_poincare_pairs` (the claim (F.3) and its sum over pairs),
`Paper.thm_poincare_step`, `Paper.thm_poincare_limit`, `Paper.thm_poincare_windows`, and the
statement for an arbitrary action that follows.
Inside the window argument an isometry preserves distance to a point it fixes: apply the
isometry to both endpoints and use the fixed-point equality. This identity holds for any
isometric action and is used both in the initial window estimate and at the limit.
:::

:::theorem "thm_poincare_action" (lean := "Paper.thm_poincare_action") (uses := "lem_angle, lem_first, lem_toolkit") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem F.6* (page 41): the inequality for an arbitrary action.
*Reading (gloss).* For every action of $`U_h`, $`h = lu`, $`l \ge 2`, by isometries on a complete
CAT(0) space $`Z` all of whose length functions $`g \mapsto |z, gz|` contract, for every
$`u \ge 2` with $`4C(3u) \le (u-1)^2/32^2`, and for every $`z \in Z`,
$$`\mathbb{E}_g |z, gz|^2 \le \frac{32\,C(2u)}{1 - 2 \cdot \frac14} \sum_{j < h-1} |z, x_j z|^2.`
The paper proves this inside the proof of Theorem F.6, for the space $`Z` of maps into a price
space. Prices enter Theorem F.6 only through the choice of $`Z` and through the remark of
Section F.1.
:::

# What the next step takes from this chapter

Only Theorem F.6, as the predicate `Paper.PoincareBound K u C₀`: the pair $`(u, C_0)` is fixed
once, and the inequality is then available on $`U_h` for every multiple $`h \ge 2u` of $`u`.
{ref "chapter-laws"}[Rerouting laws and tree networks] rewrites it as an inequality between a sum
over all pairs of elements of $`U_h` and a sum over the edges of the Cayley graph, with an integer
constant $`C_0' \ge 2C_0 + 1` ({bpref "thm_laws_poincare"}[the form over pairs and edges]),
chooses $`h` in terms of $`C_0'`, and turns the inequality, by the duality theorem
({bpref "thm_duality"}[Theorem A.6], {ref "chapter-spectral"}[Tensors, spectral points and prices]),
into identities between tensors ({bpref "thm_laws"}[Theorem G.2]). Section F.4 of the paper (page 41) relates the theorem to spectral
gaps of walks on unitriangular matrices, to proofs of property (T) and to Poincaré constants for
nonlinear targets.
