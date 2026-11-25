/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic), Codex (OpenAI)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import VpVnpBlueprint.Chapters.Programs
import VpVnpBlueprint.Chapters.Completeness
import Paper.Scales
import Paper.ApproxScales
import Paper.BorderRate

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "Accelerators and the diagonal argument" =>

%%%
tag := "chapter-accelerators"
file := "accelerators"
htmlSplit := .never
number := false
%%%

This chapter follows Appendix K (pages 55–59) and Section N.3 (pages 63–64) of the paper
({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]). Its subject is the contracting lower bound ({bpref "thm_contracting"}[Theorem K.7]).
The printed argument converts a small circuit to an accelerator by {bpref "lem_circuit"}[Lemma K.3]
and rules it out by {bpref "thm_noacc"}[Theorem K.6]. The checked proof starts with a finite
Laurent circuit. It constructs an approximate accelerator, carries it to larger scales using
{bpref "thm_cut"}[Theorem J.4], extracts an exact accelerator and applies K.6. Constant Laurent
coefficients give the exact circuit conclusion as a special case.

Claude (Anthropic) authored the original paper and formalization. Eric Vergo and Claude ported
the proof and wrote the original fork blueprint. Eric Vergo and GPT-6.2 (OpenAI) adapted the
proof and revised the blueprint. Claude Fable 5.2 directed a proof-cleanup round, with edits by
Claude Opus 5.5 (Anthropic).

The paper lists Proposition N.4 among the four statements whose printed proofs “describe machines
and programs and account for their sizes and running times” and can be verified “only in the Lean
development” (page 17). Of the other statements of this chapter it claims neither that the printed
proofs are complete nor that they are not: its list of proofs “meant to be complete, if terse”
(page 17) is Sections A to G, Appendix O and the deduction of Theorem L.1. The Lean statements
beside the nodes are what is proved. Paragraphs marked
*Reading (gloss)* describe the Lean objects and proofs; *they are this blueprint's readings, and no
tool has checked them against the Lean code.*

Throughout, $`A` is a commutative ring with a table `θ` of named elements, $`H = 16h` with
$`h \geq 17` (the paper's $`h_0 = H/16`), and `CutHyp θ (16 * h) C₀ v₀` is assumed; in the
contracting case these are supplied by `Paper.exists_setting`. The paper (page 55): “We are still in
the contracting case, and we keep the ring $`A` of Theorem G.2 and the constant $`H` of Theorem J.4,
and put $`h_0 = H/16`.”

# The shape of the argument

*Reading (gloss).* This section is this blueprint's outline of the diagonalization, written for a
reader who knows indirect diagonalization and wants to see who diagonalizes against whom, with
what resources, and why the accounting closes. The Lean arguments are `Paper.thm_noacc` and `Paper.thm_noacc_diagonal`.

*In brief.* The object diagonalized against is not a circuit but an accelerator: one program
$`D` with a table of constants that, at one scale $`v`, has the sums of all short instances of
$`v^H` steps as its values within $`v^{H-16}` steps. The diagonalizing machine is a program
$`\mathsf{P}` of the same model that contains $`D` and is run on its own code; its value $`V` is
$`1` plus what $`D` reports about $`\mathsf{P}` on $`\mathsf{P}`, so that $`V = 1 + V` in a nonzero
ring. The resources are the four exponents of Table 2: time $`v^H` for the computations that are
summed, time $`v^{H-16}` for $`D`, inputs of size $`v^{H-32}`, and one more factor $`v` for
$`\mathsf{P}`. Three things stand in the way, and each has its own lemma: $`\mathsf{P}` names
constants, and $`D` is correct only on instances that name none (Lemma K.4); naming the constants
of Lemma K.4 needs powers that $`D` may not name (reduction to a finite field); and the $`D` that
a circuit gives is larger than its own inputs (Proposition K.5, which rests on the cutting
theorem). The steps:

- *The quantity* (`NS1.pv`, `NS1.Plain`; {bpref "def_plain"}[the definition in Section I.1]). For a
  tree $`z`, read as (program, argument), $`\mathrm{sum}(z) \in A` is the sum of the weights of the
  accepting runs: a weighted count of accepting computations, with weights that are products of
  finitely many named elements of $`A`. The instance is $`\tau`-plain if all runs halt, and the
  accepting ones within $`\tau` steps and without naming constants.
- *The adversary* (`NS1.IsAccT`, `NS1.HasAcc`; {bpref "def_acc"}[Definition K.1]). An accelerator at
  scale $`v` is a program $`D` with a trie of constants $`\xi_1, \xi_2, \ldots` from an arbitrary
  commutative $`A`-algebra $`R`. On every short instance ($`|z| \leq v^{H-32}`) all its runs halt,
  the accepting ones within $`v^{H-16}` steps; on short instances that are $`v^H`-plain its value
  is $`\mathrm{sum}(z)`. The constants are non-uniform advice with which the program never
  computes. A run only records, in its tally, which powers $`\xi_l^{2^i}` it wants as factors, and
  the value of $`D` is defined from outside as the sum over accepting runs of the weight times
  these factors (`NS1.val`). So the advice may consist of arbitrary ring elements, and its size is
  the number of nodes of the trie, not a bit length.
- *The diagonal program* (`NS1.diagF`, `NS1.diagF_ev`). $`\mathsf{P}`, on an argument $`x`, guesses
  a bit. On one branch it accepts with weight 1. On the other it guesses an exponent vector $`e`,
  names the product $`\lambda^e` of constants, and applies $`D` to the instance $`z_e` of the next
  step for “$`x` on $`x`”. `diagF_ev` states: if $`D` halts on all these instances, then
  all runs of $`\mathsf{P}` on $`x` halt and the value of $`\mathsf{P}` on $`x` is
  $`1 + \sum_e \lambda^e \cdot (\text{value of } D \text{ on } z_e)`. The diagonal is
  $`x = \mathsf{P}`.
- *First obstacle: the instance “$`\mathsf{P}` on $`\mathsf{P}`” is not plain,* because
  $`\mathsf{P}` contains $`D`, whose runs name constants, and $`D` is only correct on plain
  instances. {bpref "lem_postpone"}[Lemma K.4] (`Paper.lem_postpone`) removes the names: the value
  of any program $`p` on an argument is $`\sum_e \lambda^e \,\mathrm{sum}(z_e)`, a sum over exponent
  vectors $`e` with one entry below $`2^J` for each named power, where $`z_e` is a plain instance
  that runs $`p` under an interpreter with counters and accepts exactly the runs whose tally is
  $`e`. The sum over $`e` has exponentially many terms, but a nondeterministic program produces it
  by guessing $`e` and naming $`\lambda^e`, at the cost of writing $`e` down.
- *Second obstacle: naming $`\lambda^e` needs higher powers.* If the tally of $`p` uses the powers
  $`\xi_l^{2^i}`, $`i < B`, then $`\lambda^e` is a product of powers $`\xi_l^{2^{i+j}}` with
  $`j < J`: the exponent bound grows from $`B` to $`B + J`. For a program that is to be fed to
  itself the set of names must be closed under this. Over a finite ring it is
  (`Paper.thm_noacc_periodic`): $`c^{2^j} = c^{2^{r(j)}}` for some $`r(j)` below a bound $`m_E`
  that depends only on the ring. Hence the reduction of the constants modulo a maximal ideal of
  the ring they generate over $`A`, which gives a finite field because $`A` is finitely generated
  as a ring (`Paper.thm_noacc_finite_field`). This is the only place where the proof of
  Theorem K.6 uses that hypothesis.
- *Third obstacle: sizes.* A circuit can give a program longer than its own admissible inputs.
  The paper uses {bpref "prop_next"}[Proposition K.5]. Lean first maps the finitely many constants
  to a finite field, reads them as constant Laurent polynomials, and obtains arbitrarily large
  scales from {bpref "prop_approx_acc_scales"}[the scale invariant]. Substituting a power of the
  Laurent variable preserves constant polynomials. Taking their degree-zero values therefore
  gives an exact accelerator at a scale large enough for the diagonal.
- *The accounting at the diagonal* (`Paper.thm_noacc_diagonal`). At a scale $`v` with
  $`|D| \leq v^{4h}`, at most $`v` nodes in the trie, and all logarithmic quantities (height of the
  trie, exponent bound, $`m_E`, $`J` with $`2^J > v^{H-15}`) bounded by $`X` with
  $`1000X^3 \leq v`: the program $`\mathsf{P}` has size at most $`v^{4h+1}`; every instance $`z_e`
  for $`\mathsf{P}` on $`\mathsf{P}` has size at most $`v^{H-32}`, so all runs of $`D` on it halt,
  the accepting ones within $`v^{H-16}` steps, whether or not it is plain; hence all runs of
  $`\mathsf{P}` on $`\mathsf{P}` halt, the accepting ones within $`v^{H-15}` steps; hence, by
  Lemma K.4 with $`T = v^{H-15}`, every $`z_e` is plain within $`v \cdot v^{H-15} \leq v^H` steps;
  hence $`D` is correct on every $`z_e`. So the value $`V` of $`\mathsf{P}` on $`\mathsf{P}` is
  $`\sum_e \lambda^e\,\mathrm{sum}(z_e)` by Lemma K.4 and
  $`1 + \sum_e \lambda^e\,\mathrm{sum}(z_e)` by `diagF_ev` and the correctness of $`D`. The four
  exponents $`H - 32 < H - 16 < H - 15 < H` are the whole budget.
- *Why the construction is not circular.* That $`z_e` is plain presupposes that $`\mathsf{P}`
  halts on $`\mathsf{P}`, which presupposes that $`D` halts on $`z_e`. The definition of an
  accelerator therefore demands halting, with the time bound for accepting runs, on *every* short
  instance (the field `run` of `IsAccT`), and correctness only on plain ones (the field `val`);
  the cutting programs of {bpref "def_cut"}[Definition J.1] are total for the same reason.
- *From the diagonal to circuits* (`Paper.exists_scale`, `Paper.contracting_complete`,
  `Paper.quasi_of_exponents`). With $`v \approx m^{1/B_0}` and a circuit of size $`v^a`, the
  argument needs $`(\lg v)^{C(a+1)} \leq v`, that is $`a = O(\log m/\log\log m)`, which gives the
  bound $`2^{c(\log m)^2/\log\log m}` ({bpref "thm_contracting"}[Theorem K.7]). The circuit is
  opened once, in {bpref "lem_lowdeg"}[Lemma K.2], which evaluates the part of degree at most $`d`
  of the polynomial of a circuit with $`L` gates at the indicator assignment of the word of $`z`
  in about $`(d + |z|)\,\mathrm{polylog}(L)` steps by guessing a parse tree and naming one
  constant for each of its nodes.

The paper's own remark on the argument (page 59): “This is an indirect diagonalization in the
sense of” its references FLMV05, vM07, SW14, MW17. “Compare the lower bounds for the permanent
against uniform threshold circuits of Allender” and “of Koiran and Perifel”. “The assumed speed-up
is used at one scale only.” And in Section 1.2 (page 3): “In the contracting case no property of
polynomials other than low degree is used, and the argument ends in a diagonalization. We have not
analysed how it relates to relativization and algebrization”.

# K.1. Accelerators

The paper (page 55): “A run of a program never multiplies by the constants of a circuit but only
*names* them in its tally (Section I). The powers $`\xi^{2^i}` of a constant $`\xi` also get names,
so that a program can multiply by $`\xi^e` by naming $`\xi^{2^i}` for the binary digits of $`e`
that are 1.”

:::definition "def_acc" (lean := "NS1.HasAcc, NS1.IsAccT, NS1.KT, NS1.KT.lk, NS1.KT.InB, NS1.wt, NS1.val") (parent := "part-contracting")
*Definition K.1 of the paper* (accelerator; page 55), quoted: “Let $`R` be a commutative
$`A`-algebra. An *accelerator* at scale $`v` with constants $`\xi_1, \xi_2, \ldots` from $`R` and
exponent bound $`B` is a program $`D` with the following two properties.

1. On every instance $`z` with $`|z| \leq v^{H-32}` all runs of $`D` halt, the accepting runs halt
   within $`v^{H-16}` steps, and every name in the tally of an accepting run stands for a power
   $`\xi_l^{2^i}` with $`i < B`.
2. If moreover $`z` is $`v^H`-plain, then the *value* of $`D` on $`z` is $`\mathrm{sum}(z)`, where
   the value is the sum, over the accepting runs, of the weight of the run times the powers that
   its tally names, each taken as often as it is named.

The constants sit at the leaves of a binary trie with $`Q` nodes, and names are paths: the name of
$`\xi_l^{2^i}` is the path from the root to the leaf of $`\xi_l`, followed by $`1^i0`. The
accelerator is *of size* $`s` if $`Q` and the size of $`D` are at most $`s` and, with
$`\beta = \lg(\max(v^H, s))`, the height of the trie is at most $`\beta^2` and
$`B \leq \beta^3`.” (The paper numbers the two properties (i) and (ii).) After it: “An instance of
size at most $`v^{H-32}` is called *short*”.

*Reading (gloss).* `KT R` is the trie; `K.lk p` is the element of $`R` that the name `p` stands
for (the power $`c^{2^b}` for the path of a leaf $`c` followed by $`1^b0`, and $`0` for every other
list of bits); `K.InB B p` says that `p` is such a name with $`b < B`. `wt κ r` is the weight of a
run times the product of `κ` over its tally, and `val κ l` the sum over a list of runs. `IsAccT θ H
v t K B D` holds the two properties with a time bound `t`; `HasAcc θ R H v s` adds the four bounds
of “size $`s`” with `t = v ^ (H - 16)`. The program `D` is applied to the instance $`z` as its argument.
:::

# K.2. Accelerators from small circuits

The paper (page 56): “The polynomials have one variable for every pair (place, symbol), where an
end mark counts as a symbol. The *indicator assignment* of a word of fewer than $`n` symbols sets to
1 the variable (place, symbol) for each of its symbols and the variable of the end mark at the
place after the last symbol, and it sets all other variables to 0.”

:::lemma_ "lem_lowdeg" (lean := "Paper.lem_lowdeg, Paper.lem_lowdeg_chains") (parent := "part-contracting")
*Lemma K.2 of the paper* (evaluation of the part of low degree; page 56), quoted: “Let $`R` be a
commutative $`A`-algebra, let $`d \geq 0`, and let a polynomial over $`R` in the variables (place,
symbol), with $`n` places, have a circuit with $`L` gates. There is a program of size
$`O(\log L + \log n + d)`, with $`O((L + n)^3)` constants, which on every instance $`z` with
$`|z| < n` has as value, in $`(d + |z| + 1)(\log(L + n + d))^{O(1)}` steps, the sum of the
homogeneous parts of degree at most $`d` of the polynomial, evaluated at the indicator assignment
of the word of $`z`. All its runs halt, it names only constants, not powers, and the trie that
holds the constants has height $`O(\log L + \log n)`.”

Section Q.3 (pages 69–70): “Lemma K.2 is stated for the alphabet of these two symbols and the end
mark and with explicit constants, in which the time is
$`O((d + 1)\log(L + n) + (|z| + 1)\log n)`; its bound on the number of steps is for accepting runs,
and halting is stated for the $`z` with $`|z| < n`.”

*Reading (gloss).* In the Lean statement the polynomial `p` is over any commutative ring `R`, in
the variables `Fin N × Option Bool` ($`N` places, the two symbols of the word of a tree and the end
mark `none`), with `Nc.Computes p S`, $`S \leq 2^M` and $`N \leq 2^m`. The trie `K` and the program
`D` are produced before the ring $`A`, the table `θ` and the instance are chosen, so they do not
depend on them. The bounds are: at most $`2^{3M+1} + 2^{M+m+3} + 3` nodes and height at most
$`3M + m + 4` for the trie, size at most $`c(M + m + 1) + 2(d + 1)` for the program, and cost at
most $`(d + 1)(800(M + m) + 4000) + (|z| + 2)(40m + 60) + 10m + 100` for an accepting run; every
name in a tally satisfies `K.InB 1` (constants, not powers). The value is
$`\sum_{i \leq d}` of the evaluation of `MvPolynomial.homogeneousComponent i p` at `codeB R N
(tbits z)`, the indicator assignment of the preorder word of `z`. The time bound is linear in
$`d` and in $`|z|` with logarithmic factors, stronger than the printed one.
:::

:::proof "lem_lowdeg"
*The paper's proof* (page 56), summarised. With $`g^{(i)}` the homogeneous part of degree $`i` at
the gate $`g`, for $`i \geq 1`
$$`(g' + g'')^{(i)} = g'^{(i)} + g''^{(i)}, \qquad (g'g'')^{(i)} = g'^{(0)}g''^{(i)} + g''^{(0)}g'^{(i)} + \sum_{0<j<i} g'^{(j)}g''^{(i-j)}.`
A *chain* goes from a gate to one of the two gates below it, and so on; a step has the factor 1 at
a sum gate and, at a product gate, the part of degree zero of the other gate below. With
$`c_{g,\gamma} \in R` the sum over chains from $`g` to $`\gamma` of the products of their factors,
$`a_{g,l}` the sum of $`c_{g,\gamma}` over input gates $`\gamma` with the variable $`x_l`, and
$`b_{g,g',g''}` that over product gates $`\gamma = g'g''`, induction gives
$$`g^{(1)} = \sum_l a_{g,l}x_l, \qquad g^{(i)} = \sum_{g',g''} b_{g,g',g''} \sum_{0<j<i} g'^{(j)}g''^{(i-j)} \quad (i \geq 2).`
“These constants do not depend on $`i`”. The program keeps a stack of gates and a counter; in each
round it takes a gate $`g` and guesses either a variable $`x_l` (naming $`a_{g,l}`, rejecting if
$`x_l = 0` at the indicator assignment) or, if the counter is not 0, two gates (naming
$`b_{g,g',g''}`, pushing both, decreasing the counter). “The accepting runs are, in preorder, the
parse trees with at most $`d` leaves” (the paper cites JS82 and MP08), “and the products of the
constants that they name sum to $`\sum_{1 \leq i \leq d} g^{(i)}` at the indicator assignment”.

`Paper.lem_lowdeg_chains` is the displayed identity with its constants, for the coefficients of
the restriction of the gates to the line through a point `u`: there are `κ`, `lam`, `left`,
`right`, independent of the degree, with the recursion for every gate, point and degree. The
program and its runs are in `Nc/Acc` (not read beyond the statement of `lem_lowdeg`).
:::

The paper (page 56): “We apply Lemma K.2 to a polynomial $`\Phi` whose values at indicator
assignments are the sums $`\mathrm{sum}(z)` of the short plain instances, and which is a clause
sum, so that by Corollary E.2 it has a small circuit if the permanent has one.”

:::lemma_ "lem_circuit" (parent := "part-contracting")
*Lemma K.3 of the paper* (accelerators from circuits for the permanent; page 56), quoted: “There
are constants $`B_0, C, v_0` such that the following holds for all integers $`a \geq 0` and
$`v \geq v_0` with $`(\lg v)^{Ca} \leq v`. Let $`R` be a field that is an $`A`-algebra and in which
$`2 \neq 0`. If, for some $`m \geq v^{B_0}`, the polynomial $`\mathrm{PERM}_m` has a circuit over
$`R` with at most $`v^a` gates, then $`R` has an accelerator of size $`v^{C(a+1)}` at scale $`v`.”

The printed exact accelerator at this scale is a paper-only claim here. Lean proves the
finite Laurent circuit version for a family complete for grid sums in
{bpref "lem_circuit_approx"}[the approximate circuit lemma]. An exact circuit gives that
hypothesis at identical gate count. Its conclusion concerns an approximate accelerator.
:::

:::proof "lem_circuit" (uses := "lem_circuit_universal, lem_circuit_program")
The paper applies the grid projection for the permanent to the universal instance polynomial,
then evaluates its low-degree part. The checked projection and evaluator are also used by the
approximate circuit lemma. Its Laurent output agrees with the universal sum through degree zero.
:::

:::lemma_ "lem_circuit_phi" (lean := "Paper.lem_circuit_phi, Paper.lem_circuit_assignment, Paper.lem_circuit_value") (parent := "part-contracting")
*An unnumbered step of the proof of Lemma K.3* (the polynomial $`\Phi`; page 57).

Section Q.3 (page 70): “In Lemma K.3, `lem_circuit_phi` states what is used of $`\Phi`, not that it
equals the printed sum over words.” The Lean statement: for every tape automaton with one input
over a field `F`, states `i`, `e` and numbers `t`, `N`, there is a clause sum (finite types of bits
`V` and of clauses `K`, the literals of each clause, and a weight for each clause that is a
variable $`X_i` or a constant) such that every clause has a literal, every bit occurs, the number
of literals is at most
$`1600\,(t + N + |Q| + |S| + |\Gamma| + 2)^9`, the total degree of the clause sum is at most $`N`,
and for every word $`u` with $`|u| + 1 \leq N` its value at the indicator assignment of $`u`
(`code1 N u`) is `runVal mu i e t` on $`u`. So the Lean development does not define a polynomial
called $`\Phi` and does not prove the displayed formula for it; it proves the existence of a clause
sum with the three properties that the proof of Lemma K.3 uses. `lem_circuit_assignment` is the
paper's sentence “there is exactly one assignment for each matched sequence and each sequence of
states”, and `lem_circuit_value` the resulting value at a code.
:::

:::lemma_ "lem_circuit_universal" (lean := "Paper.lem_circuit_universal") (parent := "part-contracting")
*An unnumbered step of the proof of Lemma K.3* ($`\Phi` for the universal automaton as a
projection; page 57).

The Lean statement: for `θ` with finite support, $`H \geq 32` and a factor `κ` there are $`B_0 > 0`
and $`v_0` such that for every field `F` that is an $`A`-algebra, every family `G` complete for
grid sums with factor `κ`, and all $`v \geq v_0`, $`m \geq v^{B_0}`, there is a matrix `Mat` of
polynomials in the variables (place, symbol), $`v^{H-32} + 1` places, each entry affine in one
variable, such that the substitution `aeval Mat (G m)` has total degree at most $`v^{H-32} + 1` and
takes the value `pv θ z` at the indicator assignment of the word of every $`z` with
$`|z| \leq v^{H-32}` that is $`v^H`-plain.
:::

:::lemma_ "lem_circuit_program" (lean := "Paper.lem_circuit_program") (parent := "part-contracting")
*An unnumbered step of the proof of Lemma K.3* (the program; page 57), quoted: “Lemma K.2 with
$`d = n` turns the circuit into a program with $`v^{O(a+1)}` constants that has these values and
takes $`v^{H-32}((a+1)\lg v)^{O(1)} \leq v^{H-16}` steps. All its runs halt, its names have
$`O((a+1)\lg v)` bits, and $`B = 1`”.

The Lean statement, for a polynomial with a circuit of at most $`v^a` gates over any commutative
ring: a trie and a program with at most $`v^{3a+H+20}` nodes and size, height at most
$`(3a + H + 20)\lg v`, halting on every $`z` with $`|z| \leq v^{H-32}`, accepting runs within
$`v^{H-16}` steps with names satisfying `InB 1`, and value the sum of the homogeneous parts of
degree at most $`v^{H-32} + 1` at the indicator assignment of the word of $`z`.
:::

# K.3. Transferring accelerators between scales

The paper (page 57): “The tool for passing to larger scales is Theorem J.4, but it applies only to
plain instances, whose accepting runs name no constants, whereas the programs to be sped up contain
the accelerator. The following lemma therefore collects the constants in front of the sum over the
runs.”

:::lemma_ "lem_postpone" (lean := "Paper.lem_postpone, Paper.postponed, NS1.zq, NS1.WF, NS1.Bt, NS1.KT.budg, NS1.ok") (parent := "part-contracting")
*Lemma K.4 of the paper* (postponing the constants; page 57), quoted: “Let $`p` be a program and
let an argument be given on which all runs of $`p` halt, the accepting ones within $`T < 2^J` steps
and with names among the leaves of a binary trie with $`Q'` nodes and height $`\eta`. Let the leaves
of the trie stand for powers $`\lambda_1, \lambda_2, \ldots` Then the value of $`p` on the argument
is
$$`\sum_e \lambda^e \,\mathrm{sum}(z_e), \qquad \lambda^e = \prod_j \lambda_j^{e_j},`
where $`e` runs over the vectors with one entry in $`\{0, \ldots, 2^J - 1\}` for every leaf, and the
instance $`z_e` accepts exactly the runs of $`p` whose tally uses each name the prescribed number
of times. The instance $`z_e` is plain within $`O(T(J + \eta + 1) + Q'(J + 1))` steps, and its size
is that of $`p` and the argument plus $`O(Q'(J + 1))`.”

*Reading (gloss).* The Lean statement has explicit constants in place of $`O(\cdot)`. An exponent
vector is a *budget* `Bt`, a trie with a number of $`J` binary digits at each leaf; `L.budg J`
lists all budgets for the trie `L` together with $`\lambda^e`. The instance is
`postponed p z e = zq p z e`, the tree (code of `WF`, (`p`, (`z`, code of `e`))), where `WF` is one
fixed program: it runs the interpreter `NS1.IF` on `p` and `z` with the budget, and then checks
that every counter is zero. The four conclusions for every budget `e` are: `Plain` within
$`(1000 + 100(\eta + J + 1))T + 40\,Q'(J + 1) + 40`; size at most
$`|\mathtt{WF}| + |p| + |z| + 4Q'(J + 1) + 3`; `pv` of the instance equal to the sum of the weights
of the accepting runs `r` of `p` with `ok e r.bill`; and the list of weights of the accepting runs
of the instance equal to the list of weights of those runs of `p`, in order. `ok e b` says that
subtracting one at every name of the list `b` never fails and leaves all counters zero. The
hypothesis `hκ` says that the meaning `κ` of names agrees with the lookup in the trie `L` on all
names that occur.

Section Q.3 (page 70): “The clause of Lemma K.4 on the size is never cited and is proved again
where it is needed.”
:::

:::proof "lem_postpone"
*The paper's proof* (page 57), quoted in part: “We take $`z_e = (I, (p, \text{argument}, e))`, where
$`I` is a fixed program, the *interpreter*. It evaluates $`p` construct by construct, also inside
`run`, with constant overhead, and it carries $`e` as a binary trie of counters indexed by the
names. At a `use` it follows the name and decreases that counter, and it fails if there is none or
if it is 0, which takes $`O(J + \eta + 1)` steps. The interpreter accepts if $`p` accepts and all
counters are 0 at the end. Hence it halts on every run and has empty tallies. An accepting run of
$`p` is accepted for exactly one $`e`, because the numbers of times that it uses the names are at
most $`T < 2^J`.”

In Lean the interpreter and its correctness are `NS1/Eval.lean` and `NS1/EvalThm.lean`
(`NS1.WF_ev`), the counting identity $`\prod_{n \in \text{tally}} \lambda_n = \sum_e [\,\text{tally
uses up } e\,]\,\lambda^e` is `NS1.sum_budg`, and `NS1.bill_le` gives that a run names at most one
constant a step. The statements were read; the interpreter was not.
:::

:::proposition "prop_next" (parent := "part-contracting")
*Proposition K.5 of the paper* (transfer to the next scale; pages 57–58), quoted: “Let $`v` be
large, let $`\alpha \geq 5` be an integer, and suppose that $`(\lg v)^{C\alpha} \leq v`, where $`C`
is a suitable constant that depends on the fixed power below. Let $`D` be a program with the two
properties of an accelerator at scale $`v` (Definition K.1), whose trie has $`Q \leq v^{h_0\alpha}`
nodes and whose size is at most $`v^{h_0\alpha}`. Suppose that its exponent bound $`B` and the
height of its trie are at most a fixed power of $`\alpha \lg v`. Then there is a program with the
two properties of an accelerator at scale $`v' = v^\alpha`, with the same constants, with exponent
bound $`B + 51h_0\alpha^2 \lg v` and with program size at most $`v'^{4h_0}`. Its accepting runs
take at most $`v'^{H-17}` steps. For the new program we claim only this, and not that it is an
accelerator of a given size in the sense of Definition K.1, which would require the bounds of that
definition on the height of the trie and on the exponent bound.”

The prescribed-scale conclusion with the original trie is paper-only. The checked substitute
gives arbitrarily large scales and preserves rescaling-stable properties of the constants.
It constructs a new trie. These differences matter when using K.6.
:::

:::proof "prop_next" (uses := "lem_postpone")
The printed construction repeatedly postpones constant uses and cuts plain computations.
For the checked scale argument see {bpref "prop_approx_acc_scales"}[the Laurent scale invariant].
:::

:::lemma_ "prop_next_round" (parent := "part-contracting")
The paper's exact single round is part of its proof of K.5. The checked round uses Laurent
constants, a bounded support interval and short lists of terms for their powers. Its estimates
are given under {bpref "prop_approx_acc_round"}[the approximate round].
:::

# K.4. Nonexistence of accelerators

:::theorem "thm_noacc" (lean := "Paper.thm_noacc") (parent := "part-contracting")
*Theorem K.6 of the paper* (nonexistence of small accelerators; page 58), quoted: “There are $`C`
and $`v_1` such that for all integers $`a \geq 0` and $`v \geq v_1` with $`(\lg v)^{Ca} \leq v` no
nonzero commutative $`A`-algebra has an accelerator of size $`v^a` at scale $`v`.”

The Lean statement is for any commutative ring `A` that is finitely generated as a ring
(`Algebra.FiniteType ℤ A`), a table `θ`, $`h \geq 17` and the hypothesis `CutHyp θ (16 * h) C₀ v₀`;
“nonzero” is `Nontrivial R`, and the algebras `R` are in the lowest universe. K.6 supplies the final contradiction for N.4 after coefficient extraction.
:::

:::proof "thm_noacc" (uses := "thm_noacc_finite_field, thm_noacc_periodic, prop_approx_acc_scales, thm_noacc_diagonal")
Map the finitely generated algebra of advice to a finite field $`E`. Choose its power-period
bound before the target scale. Reading the surviving constants as constant Laurent polynomials
gives an approximate accelerator. The scale theorem preserves constancy and gives arbitrarily
large scales, so the choice can absorb the field-dependent period. Evaluation at degree zero
then gives an exact accelerator over $`E`. The diagonal program contradicts its correctness
on plain inputs by the equation $`V = 1 + V`.
:::

:::lemma_ "thm_noacc_finite_field" (lean := "Paper.thm_noacc_finite_field, NS1.finite_of_finiteType_int") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem K.6* (the finite field; page 58).

The Lean statement: if `A` is finitely generated as a ring, `R` is nonzero and `D` with the trie
`K` has the two properties (`IsAccT`) over `R`, then there are a finite field `E` that is an
$`A`-algebra and a trie `K'` over `E` with the same numbers of nodes and height such that the same
`D` has the two properties over `E` with `K'`, with the same scale, time and exponent bound. The
proof lifts the trie to the subalgebra generated by its constants, which is where the accelerator
property is transported along an injective map (`IsAccT.of_map`), and maps it to the quotient by a
maximal ideal (`IsAccT.map`: the two properties are preserved by every homomorphism of
$`A`-algebras, because the value is a polynomial expression in the constants with coefficients
from $`A`). That a field which is finitely generated as a ring is finite is
`NS1.finite_of_finiteType_int`, proved from Mathlib's Jacobson rings.
:::

:::lemma_ "thm_noacc_periodic" (lean := "Paper.thm_noacc_periodic") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem K.6* (the number $`m_E`; page 59).

The Lean statement, for every finite commutative ring `R`: there are `M` and `red : ℕ → ℕ` with
`red i < M` and $`c^{2^{\mathtt{red}\, i}} = c^{2^i}` for all `c` and `i`.
For each function in the finite image of $`i \mapsto (c \mapsto c^{2^i})`, choose one index
that realizes it. The chosen indices form a finite set, so a single bound works for all of them.
:::

:::lemma_ "thm_noacc_all_scales" (lean := "Paper.prop_approx_acc_scales") (parent := "part-contracting")
The arbitrarily large scales used in K.6 come from `Paper.prop_approx_acc_scales`.
Its extra hypothesis describes a property of each Laurent constant preserved by rescaling.
For K.6 that property is membership in the constant polynomials over the finite field.
:::

:::lemma_ "thm_noacc_diagonal" (lean := "Paper.thm_noacc_diagonal, NS1.diagF, NS1.diagF_ev") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem K.6* (the diagonal; page 59).

*Reading (gloss).* The Lean statement derives `False` from: `D` with the trie `K` and exponent
bound `B` has the two properties at scale $`v` in $`v^{H-16}` steps over a nonzero ring `R`;
$`\mathtt{cst} \leq v` (a constant bounding the fixed programs); `K` has at most $`v` nodes;
$`|D| \leq v^{4h}`; `red` and `M` as in `thm_noacc_periodic`; $`v^{H-15} < 2^J`; and
$`X \geq \mathrm{ht}(K) + \max(B, M) + J + 1`, $`X \geq 10`, $`1000X^3 \leq v`.

The diagonal program is the code `p` of `diagF D g`, where `diagF D g` is “if `guess` then the
fixed tree nil else `D` applied to `ZE id g`”, `ZE id g` builds the instance `zq x x e` from the
argument `x` and a budget `e` guessed by `g`, and `g` guesses a budget for the trie
`K.expand B'`, $`B' = \max(B, M)`, naming each power $`(\xi^{2^i})^{2^j}` by the name of
$`\xi^{2^{\mathtt{red}(i+j)}}`. `NS1.diagF_ev` gives the list `l` of accepting runs of `diagF D g`
on any `z` on which `D` halts at all `zq z z e`, with cost at most that of `g` plus that of `D`
plus 30, and
$$`\mathrm{val}(l) = 1 + \sum_e \lambda^e \cdot \mathrm{val}\bigl(\text{runs of } D \text{ on } \mathtt{zq}\ z\ z\ e\bigr).`
The proof of `thm_noacc_diagonal` then has four steps, in the order of the outline at the head of
this chapter: the sizes ($`|p| \leq v^{4h+1}` and $`|\mathtt{zq}\ p\ p\ e| \leq v^{H-32}`); the
runs of `p` on `p` and their time $`\leq v^{H-15}`; Lemma K.4 for `p` on `p`, which gives
$`\mathrm{val}(l) = \sum_e \lambda^e\,\mathrm{sum}(\mathtt{zq}\ p\ p\ e)` and the plainness of every
`zq p p e` within $`v^H` steps; and the equation `val K.lk l = 1 + val K.lk l` from property (ii)
of `D`, whence $`1 = 0` in `R`.

Two details differ from the printed sketch. The printed bound “the size of $`\mathsf{P}` is at most
$`v^{H/4}` plus lower-order terms” is $`v^{4h+1}` in Lean. And the paper's “$`v` large compared
with the size of $`E` and with the number of constants” is the pair of hypotheses that the trie
has at most $`v` nodes and that $`m_E` is among the quantities bounded by $`X`; the cardinality of
$`E` does not occur otherwise.
:::

# K.4a. The setting of the contracting case

:::lemma_ "scales_setting" (lean := "Paper.exists_setting, Paper.prop_approx_acc_setting") (parent := "part-contracting")
For the contracting field, `Paper.exists_setting` supplies the ring, table and cut
hypothesis. Proposition N.4 is available in that setting as `Paper.prop_approx_acc_setting`.
The exact contradiction K.6 itself accepts the cut hypothesis directly.
:::

# K.5. The lower bound in the contracting case

:::theorem "thm_contracting" (lean := "Paper.thm_contracting, Paper.contracting_complete") (parent := "part-contracting")
*Theorem K.7 of the paper* (lower bound in the contracting case; page 59), quoted: “In the
contracting case there are $`c > 0` and $`m_0` such that for $`m \geq m_0` every circuit over
$`\Bbbk` for $`\mathrm{PERM}_m` has more than $`2^{c(\log m)^2/\log\log m}` gates.”

The Lean statement is this for a field `K` in the lowest universe with `Contracting K` and
$`2 \neq 0`, the hypothesis that the printed statement leaves to the context (Lemma K.3).
`Paper.contracting_complete` is the form for any family that is complete for grid sums, in terms
of exponents: there are $`C`, $`M_1` such that for $`M \geq M_1` and every $`a` with
$`(\lg M)^{Ca} \leq M` no circuit with $`M^a` gates computes $`G_M`.
{bpref "quasi_of_exponents"}[`Paper.quasi_of_exponents`] converts a statement of that form into
the bound $`2^{c(\log m)^2/\log\log m}` with $`c = 1/(4(C + 1))`.
:::

:::proof "thm_contracting" (uses := "lem_circuit_approx, prop_approx_acc, quasi_of_exponents")
View the exact circuit as a constant Laurent circuit at the same size. The contracting
bound for finite Laurent circuits applies with the same exponents and threshold; the permanent
is the grid-complete family with parameter three. The asymptotic estimate is shared with N.5.
:::

:::lemma_ "quasi_of_exponents" (lean := "Paper.quasi_of_exponents, Paper.exists_scale") (parent := "part-contracting")
*Two calculations of the proof of Theorem K.7* (page 59): the choice “$`v = \lfloor m^{1/B_0}
\rfloor`” of the scale, and the passage from exponents $`a` to the bound
$`2^{c(\log m)^2/\log\log m}`.

Neither theorem mentions circuits or accelerators. `Paper.quasi_of_exponents` is stated for an
arbitrary predicate $`P(M, s)` that is monotone in $`s`: if $`P(M, M^a)` fails whenever
$`M \geq M_1` and $`(\lg M)^{Ca} \leq M`, then $`P(m, s)` implies
$`2^{c(\log m)^2/\log\log m} < s` for all large $`m`, with $`c = 1/(4(C+1))`.
`Paper.exists_scale` is described in the proof above. Both are used again, with `Approximates` for
`Computes`, by {bpref "lem_circuit_approx"}[the approximate forms].
:::

# N.3. Approximate accelerators in the contracting case

The paper (page 62): “In the contracting case an approximating circuit gives a program that is
correct only up to multiples of $`\varepsilon`, and Proposition N.4, whose long proof may be skipped
at first reading, excludes such programs.”

:::definition "def_approx_acc" (lean := "NS1.HasAccA, NS1.IsAccA, NS1.OrdGE") (parent := "part-contracting")
*Definition of Section N.3 of the paper* (approximate accelerator; page 63; unnumbered), quoted:
“An *approximate accelerator* over $`R` is defined as in Definition K.1, except that its constants
lie in $`R[\varepsilon, \varepsilon^{-1}]` and that in property (ii) its value on a $`v^H`-plain
instance $`z` is only required to lie in $`\mathrm{sum}(z) + \varepsilon R[\varepsilon]`.”

*Reading (gloss).* The trie has its constants in Mathlib's Laurent polynomials `R[T;T⁻¹]`, and
property (ii) is `OrdGE 1 (value − sum)`: every coefficient of the difference at an exponent
$`i < 1` vanishes. `HasAccA` packages this condition with the same four
bounds of “size $`s`” as in Definition K.1.
:::

:::proposition "prop_approx_acc" (lean := "Paper.prop_approx_acc, Paper.prop_approx_acc_setting") (parent := "part-contracting")
*Proposition N.4 of the paper* (no approximate accelerators; page 63), quoted: “Theorem K.6 holds
for approximate accelerators.”

The paper's formalization note (page 63): “The proof below describes the programs and accounts for
their sizes and running times to the level of exponents. That the programs do what is claimed is
proved only in the Lean development.”

The Lean statement is that of `Paper.thm_noacc` with `HasAccA` in place of `HasAcc`: for `A`
finitely generated as a ring, $`h \geq 17` and `CutHyp θ (16 * h) C₀ v₀` there are $`C`, $`v_1` such
that for $`v \geq v_1` and $`(\lg v)^{Ca} \leq v` no nonzero commutative $`A`-algebra `R` has
`HasAccA θ R (16 * h) v (v ^ a)`. `Paper.prop_approx_acc_setting` is its instance in the
contracting case using the cut setting of {bpref "thm_cut"}[Theorem J.4].
:::

:::proof "prop_approx_acc" (uses := "prop_approx_acc_scales, prop_approx_acc_exact, thm_noacc")
*The paper's proof* (pages 63–64), summarised. “We carry the given program to larger scales by the
rounds of Proposition K.5, keeping the error a multiple of $`\varepsilon`, and at a large scale we
extract the coefficient of $`\varepsilon^0`.” Let $`\Delta` bound the absolute values of the
exponents of $`\varepsilon` in the constants, and let $`\sigma_r` be the substitution
$`\varepsilon \mapsto \varepsilon^r`. *One round*: for a program $`p` whose values on plain
instances lie in $`\mathrm{sum}(z) + \varepsilon E[\varepsilon]`, Lemma K.4 gives its value
*exactly* as $`\sum_e \lambda^e\,\mathrm{sum}(z_e)` with $`\mathrm{sum}(z_e) \in A`. Let $`r` exceed
the absolute values of the exponents of $`\varepsilon` in all $`\lambda^e`. The new program guesses
$`e`, multiplies by $`\lambda^e`, cuts $`z_e` into pieces, and runs $`D` on all pieces with the
constants $`\sigma_r(\xi')` in place of its constants $`\xi'`; the result on a list of plain pieces
lies in $`\prod_y \mathrm{sum}(y) + \varepsilon^r E[\varepsilon]`, so the new value lies in
$$`\sum_e \lambda^e\bigl(\mathrm{sum}(z_e) + \varepsilon^r E[\varepsilon]\bigr) \subseteq (\text{value of } p) + \varepsilon E[\varepsilon] \subseteq \mathrm{sum}(z) + \varepsilon E[\varepsilon].`
The error of the inner calls is thus pushed, by the substitution, beyond the negative exponents of
the outer factors. A round adds one to the height of the trie, at most the number of constants of
$`D` to the number of constants, and $`J` to the exponent bound; the logarithm of the largest
exponent of $`\varepsilon` stays $`(\lg u)^{O(1)}`. *Back to exact values*: at a scale $`u` large
compared with $`v`, $`\Delta` and $`b_0`, a new program guesses for every named power
$`c = \xi_l^{2^i}` the number $`n < 2^J` of times it is to be used and the number $`k` of one term
of $`c^n`, names the coefficient of that term, an element of $`E`, and adds its exponent to a
counter modulo $`2^W`; it then runs the interpreter on $`D`, counting each name against its number,
and accepts if the interpreter does and the counter is 0. Its value is the coefficient of
$`\varepsilon^0` in the value of $`D`, which is $`\mathrm{sum}(z)` on plain instances. “This is an
accelerator over $`E` of size $`u^{O(1)}` with a fixed exponent, which contradicts Theorem K.6.”

*Reading (gloss): the Lean proof.* `Paper.prop_approx_acc` uses `Paper.thm_noacc` as it stands: it
produces, from an approximate accelerator over a nonzero $`A`-algebra `R`, an exact accelerator
over the same `R` at a larger scale, of size $`u^{4400h+6}`, and applies the exact theorem. Its
steps are the three nodes below. The scale and extraction estimates are assembled in
{repoFile "vp-vnp/Paper/ApproxScales.lean"}[`Paper/ApproxScales.lean`].
:::

:::lemma_ "prop_approx_acc_round" (lean := "Paper.prop_approx_acc_round, Paper.prop_approx_acc_round_num, Paper.prop_approx_acc_next") (parent := "part-contracting")
A round postpones the constants, cuts the resulting plain instance and evaluates its pieces.
At a transition from $`u` to $`u^α`, Lean takes $`3α` cuts. Each saves eight
powers of $`u`. The new trie uses at most $`6α+1` times the original node bound;
bounds on height, named powers and Laurent support account for the extra cuts. This gives the
stronger time estimate $`(u^α)^{16h-17}` already at the first transition.
:::

:::lemma_ "prop_approx_acc_scales" (lean := "Paper.prop_approx_acc_scales, Paper.prop_approx_acc_first, Paper.prop_approx_acc_step, Paper.prop_approx_acc_all_scales, NS1.InvA") (parent := "part-contracting")
`NS1.InvA` records the program and trie sizes, height, bound on named powers, support span,
thinness of powers and one spare power of the current scale in the running time. The first
transition establishes the whole invariant. The step takes the fifth power of the scale and
preserves it. Iteration gives arbitrarily large scales with common coefficients and preserves
each rescaling-stable property of the input constants. This is where K.6 obtains a scale large
enough for the chosen finite field's power period.
:::

:::lemma_ "prop_approx_acc_exact" (lean := "Paper.prop_approx_acc_exact, Paper.prop_approx_acc_hasAcc") (parent := "part-contracting")
*An unnumbered step of the proof of Proposition N.4* (back to exact values; pages 63–64), quoted:
“Expanding the powers $`c^n` into their terms shows, as the true sum of the exponents is below
$`2^W` in absolute value, that the value of the new program is the coefficient of
$`\varepsilon^0` in the value of $`D`, which is $`\mathrm{sum}(z)` on plain instances.”

`prop_approx_acc_exact`: from `IsAccA θ H v t K B D` with $`t < 2^J`, constants of span `M` and
thinness `Δ`, and numbers `m`, `W` with $`2 \cdot 2^{B+J}\Delta + 1 \leq 2^m` and
$`Q_B\, 2^J \cdot 2^B M < 2^W`, it gives a trie `K'` over `E` and a program `D'` with
`IsAccT θ H v t' K' 1 D'`: an exact program with exponent bound 1, whose constants are the
coefficients of the terms of the powers. `prop_approx_acc_hasAcc` puts the sizes together: under
the invariant, at a scale large against `b₀`, `Δ` and `cΔ`, there is `HasAcc θ E (16 * h) u
(u ^ (4400 * h + 6))`.
:::

:::lemma_ "lem_circuit_approx" (lean := "Paper.lem_circuit_approx, Paper.contracting_approx_complete") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem N.5* (approximate accelerators from approximating
circuits; page 64), quoted: “In the contracting case the proofs of Lemmas K.2 and K.3 work over
this ring and give approximate accelerators. Indeed, the output $`\Phi + \varepsilon g` of the
circuit may have a large degree, but the program of Lemma K.2 gives its part of degree at most
$`d`, which is $`\Phi` plus $`\varepsilon` times that part of $`g`.”

The checked input is a finite Laurent circuit for the grid-complete family. The affine grid
projection preserves its coefficient identities and costs at most five gates per gate.
The low-degree evaluator uses that projected witness directly. Approximation by series enters
through the gate-count-preserving equivalence `Nc.laurentApproximates_iff`.
:::

# What the next chapter takes from this one

{ref "chapter-assembly"}[All fields and approximate computation] takes
`Paper.contracting_approx_complete` for both families over a field `K` in the lowest universe
with `Contracting K`. An exact circuit enters that bound as a constant-series circuit.
`Paper.thm_contracting` and `Paper.contracting_complete` specialize the approximate bound to exact circuits
for the permanent and for arbitrary families complete for grid sums, respectively. These
statements give no value for the constant $`c` of these bounds; it comes out of the laws and the
cutting theorem for the field `K`. In {bpref "thm_allfields"}[Theorem M.3] the bound is weakened,
for large $`m`, to that of the flat case, so that this constant does not enter the constant of
the main theorems.
