/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import Paper.Universal
import Paper.UniversalSteps
import Paper.Runnet
import Paper.Pieces
import Paper.Cuts

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "Programs, automata and cutting" =>

%%%
tag := "chapter-programs"
file := "programs"
htmlSplit := .never
number := false
%%%

This chapter follows Appendices I (pages 48–51) and J (pages 51–55) of the paper
({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]). It fixes the model of computation of the contracting
case, a weighted nondeterministic program on binary trees whose *sum* over accepting runs is an
element of the ring $`A` of {ref "chapter-laws"}[Rerouting laws and tree networks], and it proves the
one statement that the diagonal argument of
{ref "chapter-accelerators"}[Accelerators and the diagonal argument] takes from the geometry:
a sum over runs of $`\tau` steps is a sum, over the runs of a fast program, of products of sums over
runs of $`v^H` steps on short inputs (Theorem J.4). The route is: a program is simulated by a
tape automaton with quasi-linear loss (Proposition I.1); a run of a tape automaton cut into time
blocks is a tensor network (Lemma I.2); the tree decomposition of the previous chapter cuts the
network into pieces (Proposition J.2); a program writes the pieces down as instances again
(Theorem J.3); and the cut is repeated (Theorem J.4).

The paper says (page 17): “The proofs of Proposition I.1, Theorem H.2(d), (e), Theorem J.3 and
Proposition N.4 describe machines and programs and account for their sizes and running times. That
these do exactly what is claimed can be verified only in the Lean development, and each of these
four statements is followed by a formalization note that says so. Consequently the contracting
case, and with it every main result, rests on Lean at these points.” Two of the four are in this
chapter. For them the sections below describe, from the Lean sources, the objects and the chain of
Lean theorems, in paragraphs marked *Reading (gloss)*. *These readings are this blueprint's, not the
paper's, and no tool has checked them against the Lean code.* Each says which declarations were
opened and which were not. Of the other statements of this chapter the paper claims neither that
the printed proof is complete nor that it is not: its list of proofs that “are meant to be
complete, if terse” (page 17) is Sections A to G, Appendix O and the deduction of Theorem L.1.
For those statements the Lean statement beside each node is what is proved, and the printed proof
is summarised as the paper's.

Notation as in the paper: $`\lg n = \lfloor \log n \rfloor + 1` (`NS1.lg`), $`|x|` for the size of a
tree, $`\mathrm{sum}(z)` for the sum of an instance. The Lean development writes *bill* for the
paper's tally, *unit* for a packet and *table* for a node tensor (Section Q.3, page 66).

# I.1. Programs and sums over runs

The paper (page 48): “All data are binary trees, where a tree is either nil or a pair of two trees,
and the size $`|x|` of a tree $`x` is its number of nodes. A program is an expression in the
constructs of the following table, in which $`p_1, p_2, p_3` stand for subprograms and $`x` for the
argument. Programs are nondeterministic, and a run carries a weight in $`A`, which is 1 at the
start, and a tally, which is a list of names.” The table lists: a fixed tree; the argument; the
first and the second part of $`p_1`; the pair of $`p_1, p_2`; if $`p_1` then $`p_2` else $`p_3`;
`run` $`p_1` $`p_2` (“the output of the program coded by the output of $`p_1` at the output of
$`p_2`”); `guess` (“two runs, with outputs nil and (nil, nil)”); `fail` (“no accepting run”);
`weight` $`p_1` (“nil; multiplies the weight by the generator of $`A` named by the output of
$`p_1`”); `use` $`p_1` (“nil; appends the output of $`p_1`, a name, to the tally”). And: “Subprograms
are evaluated from left to right, their weights multiply and their tallies are concatenated. Every
construct costs one step, and the cost of a run is its number of steps. Finitely many generators of
$`A`, one of which is $`-1`, have names, and every other name has the weight 0.”

:::definition "def_program" (lean := "NS1.Tree, NS1.Tree.size, NS1.Fm, NS1.Fm.code, NS1.Fm.ofTree") (parent := "part-contracting")
*The program model of Section I.1 of the paper* (page 48; unnumbered). Trees, their size, the
eleven constructs, the code of a program as a tree, and the reading of an arbitrary tree as a
program: “A program is coded as the pair of the number of its outermost construct, in unary, and
the codes of its parts. Conversely every tree is read as a program, with nil read as the fixed tree
nil and a pair whose first component is not the number of a construct as `fail`” (pages 48–49).

*Reading (gloss).* `Fm` has one constructor for each row of the paper's table: `quote` (a fixed
tree), `id` (the argument), `hd`, `tl`, `cons`, `ite`, `run`, `guess`, `fail`, `theta` (the paper's
`weight`) and `mul` (the paper's `use`). `Fm.code` writes the constructs as the numbers 0 to 10 in
unary. `Fm.ofTree` is total and satisfies `ofTree (code F) = F` (`NS1.Fm.ofTree_code`).

Section Q.3 (page 69) on the reading of a tree: “In Section I.1, Lean reads the construct of a pair
from the length of its first component as a list, so that this component need not be the number of
a construct, and such a pair is read as `fail` only if the length is above 10.” So the two readings
differ on trees that are not codes; on codes they agree.
:::

:::definition "def_runs" (lean := "NS1.Run, NS1.Ev, NS1.Hl, NS1.evl") (parent := "part-contracting")
*Runs, halting and the accepting runs* (page 49; unnumbered): “That all runs of an instance halt is
defined inductively along the evaluation: in a pair and in `run` both subprograms must halt, also
when the first has no accepting run, and a chosen branch, and the program that is run, must halt
for every accepting run of what precedes them.”

*Reading (gloss).* The semantics is one inductive relation, in big-step form. An accepting run is a
record `Run` of its cost, its weight in $`A` (`th`), its tally (`bill`, a list of names, each a
list of bits) and its output tree. `Ev θ F x l` says that all runs of the program `F` on the
argument `x` halt and that `l` is the list of the accepting runs, with multiplicity and in a fixed
order. Its eleven rules are the eleven constructs. Three points of the rules matter later.

- Cost. A fixed tree, the argument and `guess` cost 1; every other construct costs 1 more than the
  sum of the costs of the runs of its parts that were taken, and `run` adds the cost of the run of
  the called program. This is the paper's “every construct costs one step”.
- Halting. The rules for `cons` and `run` require `Ev` of both subprograms whatever the first
  yields; the rule for `ite` requires `Ev` of the branch chosen by each accepting run of the
  condition; the rule for `run` requires `Ev` of the program `Fm.ofTree r.out` on `s.out` for every
  pair of accepting runs `r`, `s` of its two parts. A program with a run that does not halt has no
  list at all. This is the paper's inductive definition, and it is why a statement such as
  “all runs halt on every short instance, plain or not” (Definitions J.1 and K.1) has content.
- Weights and names. `theta a` multiplies the weight by `θ w`, where `w` is the output of `a` read
  as a list of bits (`Tree.path`) and `θ : List Bool → A` is the table of named generators;
  `mul a` appends that list of bits to the tally and changes no weight. Nothing in the semantics
  refers to a ring of constants beyond $`A`: what a name in the tally stands for is decided by
  whoever evaluates the run (Definition K.1).

`Hl θ F x` is “some list exists”, and `evl θ F x` is that list (the empty list if there is none);
the list is unique (`NS1.Ev.unique`).
:::

:::definition "def_plain" (lean := "NS1.Plain, NS1.pv, NS1.pval, NS1.lg") (parent := "part-contracting")
*Definition of Section I.1 of the paper* (plain instances and their sums; page 49; unnumbered),
quoted: “An instance $`z` is $`\tau`-plain if all its runs halt and every accepting run has an
empty tally and costs at most $`\tau`. The sum $`\mathrm{sum}(z) \in A` of an instance is the sum of
the weights of its accepting runs.” Before it: “An instance $`z` is a pair of a program and an
argument, and the tree nil, of size 1, also counts as one, with program and argument nil.”

*Reading (gloss).* In Lean every tree `z` is an instance: its program is `Fm.ofTree z.hd` and its
argument is `z.tl`, where `hd` and `tl` of nil are nil. `Plain θ τ z` and `pv θ z` are the two
notions of the definition; `pv θ z` is defined for every `z` and is $`0` when not all runs halt.
:::

The paper adds (page 49): “Any machine model with a self-interpreter of constant overhead should
do, and polylogarithmic factors are always absorbed by powers of the parameter $`v` of Sections J
and K. The construct `use` and the tally are needed only in Section K, where a program that
simulates a circuit over $`\mathbb{R}` cannot contain the real constants of the circuit and names
them in the tally instead (Definition K.1). Finally, the code of an instance as a word, or briefly
its word, lists one symbol for each node of the tree, in preorder.” In Lean the word of `z` over two
symbols `b0`, `b1` is `Nc.Dl.wordG b0 b1 z`: `b0` for nil, and `b1` followed by the words of the
two parts for a pair; its length is `z.size` (`Nc.Dl.length_wordG`).

# I.2. Tape automata

:::definition "def_tape_automaton" (lean := "Nc.Ch, Nc.Letter, Nc.emit, Nc.Matched, Nc.runVal") (parent := "part-contracting")
*Definition of Section I.2 of the paper* (tape automaton; page 49; unnumbered), quoted: “A tape
automaton over $`A` has finite sets of states, of tapes and of symbols, two fixed states $`q^-` and
$`q^+`, and for each letter a matrix over $`A` whose rows and columns are indexed by the states.
Each tape has two sides. A letter is either idle, or it writes one symbol on one of the two sides
of a tape, or it writes one symbol on the input. A sequence of $`t` letters is matched on an input
word if on every tape the two sides receive the same word and the input receives the given word.
The value of the automaton on an input word in $`t` steps is the sum, over all sequences of $`t`
letters that are matched on this word, of the entry $`(q^-, q^+)` of the product of their
matrices.”

*Reading (gloss).* With tapes `S`, inputs `J` and symbols `Γ`, a channel (`Ch S J`) is a side of a
tape or an input, and a letter is `none` (idle) or a pair of a channel and a symbol. An automaton
is a map `mu` from letters to $`Q \times Q` matrices with two states `i`, `e`; `runVal mu i e t u`
is the displayed sum over all functions from $`\{0, \ldots, t-1\}` to letters. The Lean definition
allows several inputs; the paper's automata have one (`J = Unit`).
:::

The paper's comment (page 49): “One side of a tape is for writing and the other for reading: a
letter on the reading side guesses the symbol that is read, and being matched forces the guesses to
agree with what is written. So a tape is like a queue, except that a symbol may be read before it
is written.” The model has no head positions and no transition relation beyond the matrices: all
of the control is in the matched condition, which is what makes the value a contraction of tensors
in Lemma I.2.

:::proposition "prop_universal" (lean := "Paper.prop_universal, Paper.universal_symbols_ne") (parent := "part-contracting")
*Proposition I.1 of the paper* (a universal tape automaton; page 49), quoted: “There are a tape
automaton and a constant $`C_{\mathrm{univ}}` such that the value of the automaton on the code of an
instance $`z` as a word, in $`t` steps, is $`\mathrm{sum}(z)` whenever $`z` is $`\tau`-plain and
$`t \geq C_{\mathrm{univ}}(|z| + \tau)\bigl(\lg(|z| + \tau)\bigr)^2`.”

The paper's formalization note (page 49): “The proof describes the automaton and counts its steps,
and that the automaton is exact is proved only in the Lean development (Appendix Q).”

The Lean statement makes the dependence on the named generators explicit: for every table
`θ : List Bool → A` with finite support, over any commutative ring `A`, there are finite types of
tapes, symbols and states, matrices, two states, two symbols `b0`, `b1` and a constant `C` with the
stated property for all `τ`, `z`, `t`. Section Q.3 (page 69): “In Proposition I.1, that the two
symbols of the word of an instance are different is a separate theorem (`universal_symbols_ne`).”
That theorem needs $`A` to be nonzero.
:::

:::proof "prop_universal"
*The paper's proof* (pages 49–50), summarised. “A pointer machine evaluates the program, and a tape
automaton simulates it by guessing what every load returns and checking the guesses at the end.”
The pointer machine has a finite control and a fixed number of registers holding addresses; in one
step it loads the pair at an address, allocates a pair at the next free address, tests for 0,
guesses a bit or multiplies by a weight. It builds the tree of $`z` from its word and evaluates the
program with a stack of frames in the heap; an accepting run of $`z` of cost $`n` gives exactly one
accepting run of the machine, with the same weight and $`O(|z| + n)` steps. The automaton guesses
the number $`\beta` of bits of an address, lets registers circulate on a tape, writes a record
(address, load, pair) for every load with a guessed pair and a record (address, allocation, pair)
for every allocation, and at the end sorts the records by address with allocations first, by
$`\beta + 1` passes of a radix sort on two tapes; “a last pass checks that each address begins with
an allocation and that all loads of it repeat its pair”. The count is $`O(\beta)` letters for each
of $`O(|z| + \tau)` steps and records in each of $`\beta + 1` passes, with
$`\beta = O(\lg(|z| + \tau))`. The paper attributes the ideas to its references Sch78, Sch80,
BEGKN94, Rob91 and GS89.

*Reading (gloss): the Lean proof.* The proof of `Paper.prop_universal` is short: it combines
`Paper.prop_universal_series` (below) with `Nc.exists_run_val` and adjusts the constant to
$`27(2C + 2)`. The content is in four layers, each with its own Lean objects.

1. *Pointer machines* (`Nc.Uni.Mach`, file `Nc/Uni/PM.lean`). A machine has finite sets of modes
   and of kinds of records, five registers holding natural numbers, and a heap, a list of records
   (kind, address, three fields). A step is a rule together with the values of nine variables (the
   five registers, the three fields of the record that is loaded, the new address); every step
   loads one record at the address in a register named by the rule, allocates one record at the
   next address, may read one bit of the input, and has a weight. `Mach.Seq` defines the accepting
   runs from a state. `Mach.GV` is the weaker, global condition that a sequence of steps threads
   modes, registers, fresh addresses and the input correctly and that every loaded record occurs
   *somewhere* in the initial heap or among the records allocated by the sequence, earlier or
   later. `Nc.Uni.Mach.gv_iff` proves that for a heap that is closed (all addresses at most the
   last one, every address present, registers in range) the two conditions agree. This is the
   paper's sentence “By induction on time all addresses in registers are below the free one, so a
   load refers to the only allocation at its address, which is earlier.”
2. *The universal machine* (`Nc.Uni.UM`, files `Nc/Uni/Rules.lean`, `EvalU.lean`, `EvThm*.lean`,
   `TopU.lean`). Its theorem is `Nc.Uni.sum_machine`, restated as the node
   `prop_universal_machine` below: for a $`\tau`-plain $`z` the accepting runs of the machine from
   its initial state on the word of $`z` form a finite set, their weights sum to
   $`\mathrm{sum}(z)`, and each has at most $`3|z| + C\tau + 10` steps. It is proved by induction
   over the relation `Ev` (`Nc.Uni.evOK`, one case per construct), after a parsing phase that
   builds the tree in the heap (`Nc.Uni.parse`). The table `θ` enters through its finite support:
   the modes of the machine include the prefixes of the names in the support.
3. *Tape programs as rational series* (`Nc/Tape`, `Nc/Sort`, `Nc/Uni/Prog.lean`). A tape program
   is a function from words over (channel, symbol) to $`A` that has a linear representation of
   bounded dimension (`Nc.RatLe`); sums, products and stars keep this property. `Nc.Uni.runs_X`
   writes the simulating program as a product of such pieces (input, counter, a star over the
   steps, end, and the sorting loop) and proves that its sum over all words with given projections
   to the channels is the sum of the weights of *structured runs* with these projections
   (`Nc.IsRuns`). `Nc.Uni.mt_X` characterises the structured runs whose two sides agree on every
   tape, and `Paper.prop_universal_automaton` (below) concludes that the value of the program is
   the sum of the weights of the sequences satisfying `Mach.GV`, with a bound on the total length
   of what is written. The sorting argument is `Nc/Sort/Radix.lean`: after one stable pass for
   every letter of the key, records with equal keys are neighbours in their original order, so
   “every lookup has the key of an earlier entry of the table” is equivalent to a test of
   neighbours.
4. *From a series to an automaton* (`Nc.exists_run_val`, file `Nc/Tape/ProgRun.lean`). A series of
   dimension at most $`n` is the value of a tape automaton with at most $`n + 3` states that emits
   the letters of the program and then idles: if all contributing tape contents have total length
   at most $`t_0` and $`2 t_0 + |u| + 1 \leq t`, the value in $`t` steps on the input $`u` is the
   value of the series.

*What was read.* The statements named above, the definitions of `Mach`, `State`, `Fire`, `Seq`,
`GV`, `Closed`, `RatLe`, `IsRuns`, `Nc.val`, `Nc.Bdd`, and the proofs of `Paper.prop_universal` and
`Paper.prop_universal_series`. Not read: the rules of the universal machine one by one, the proofs
of `evOK` and `gv_iff`, the specification of the sorting loop (`Nc/Uni/SortU.lean`, `SpecU.lean`,
`SpecU2.lean`, `CmpU.lean`), and the proof of `mt_X`. Section Q.3 (page 70) lists “the sorting pass,
the tape encoding and the time count of Proposition I.1” among the steps that “exist only under
names of the underlying library and not as theorems with prefix `Paper.`”.
:::

:::lemma_ "prop_universal_machine" (lean := "Paper.prop_universal_machine, Nc.Uni.sum_machine") (parent := "part-contracting")
*An unnumbered step of the proof of Proposition I.1* (the pointer machine is exact; page 50),
quoted: “Hence an accepting run of $`z` of cost $`n` gives exactly one accepting run of the
machine, with the same weight and $`O(|z| + n)` steps, and there are no others.”

The Lean statement is the form that is used: for a table `θ` that vanishes outside a finite set
`supp` and a $`\tau`-plain `z`, a finite set `R` is exactly the set of step sequences satisfying
the global condition `Mach.GV` from the initial state, the weights of its elements sum to `pv θ z`,
and each has at most $`3|z| + C\tau + 10` steps, with a constant $`C` that depends on `supp`. It
does not state a bijection between runs of the program and runs of the machine.
:::

:::lemma_ "prop_universal_automaton" (lean := "Paper.prop_universal_automaton") (parent := "part-contracting")
*An unnumbered step of the proof of Proposition I.1* (the automaton is exact; page 50), quoted:
“Thus accepting runs correspond to matched sequences of length $`t`, provided that $`t` is large
enough.”

The Lean statement is for any pointer machine `P` of the kind above and any series `S₀` with the
structured runs of the simulation: if the heap of the initial state is closed and a finite set `R`
is the set of sequences satisfying `Mach.GV`, all of length at most `Tm`, then every contributing
tape content has total length at most an explicit bound in `Tm` and the number of bits of
`Tm + 1`, and the value of `S₀` on the input is the sum of the weights over `R`.
:::

:::lemma_ "prop_universal_series" (lean := "Paper.prop_universal_series") (parent := "part-contracting")
*An unnumbered step of the proof of Proposition I.1* (exactness and number of steps; page 50),
summarised: the letters needed are $`O(\beta)` for each of $`O(|z| + \tau)` steps and records in
each of $`\beta + 1` passes.

The Lean statement: there are a series of bounded dimension and a constant $`C` such that for
every $`\tau`-plain `z` the series, on the word of `z`, has all contributing contents of total
length at most $`C (|z| + \tau + 2) \lg(|z| + \tau + 2)^2` and has the value `pv θ z`.
:::

# I.3. The runs of a tape automaton as a network

The paper (page 50): “Cutting a computation into time blocks and recording which block reads what
another has written goes back to Hopcroft, Paul and Valiant” (its reference HPV77). “For a tape
automaton the result is a network in the sense of Section H.2, whose nodes are the time blocks and
the parts of the input word (Figure 12). As a tape is a queue, the readers of what a node writes
follow each other in order, and the data $`\rho` below record the first and the last.”

:::lemma_ "lem_runnet" (lean := "Paper.lem_runnet, Nc.Cut.RowData, Nc.Cut.ValidRows, Nc.Cut.parts") (parent := "part-contracting")
*Lemma I.2 of the paper* (the runs of a tape automaton as networks; pages 50–51), quoted: “Let
$`K, T, \ell \geq 1` and $`T' \leq T`. Let an input word of at most $`KT'` symbols be cut into $`K`
consecutive parts of $`T'` symbols, the last parts possibly shorter or empty, and let the $`KT`
steps be cut into $`K` consecutive time blocks of $`T` steps. Order the $`2K` nodes as follows:
first the $`K` time blocks, then the $`K` parts. Regard the input as one more tape, which is
written by the parts and read by the blocks. Let $`S` be the set of tapes and $`Q` the set of
states, and let the symbols and an end mark be coded by $`c` bits each.

- Data $`\rho` say, for every tape and every node, whether the node writes nothing on the tape, and
  otherwise which is the first and which is the last node that reads its symbols.
- The data $`\rho` are valid if on every tape the first reader of a node is not before the last
  reader of the node before it, and not after the last reader of the node itself. Here a node that
  writes nothing repeats the last reader of the node before it, so that $`\rho` is determined by the
  sequence of letters, and for the first node, the first node itself takes the place of that last
  reader.

Then the value of the automaton in $`KT` steps is the sum of the values of networks on these $`2K`
nodes, one network for every choice of

- boundary states $`q \in Q^{K+1}` with $`q_0 = q^-` and $`q_K = q^+`,
- valid data $`\rho`, and
- numbers of packets of $`\ell` bits between any two nodes, each number at most
  $`(T + |S| + 1)c/\ell + 1`.

In each of these networks a node whose node tensor is not 0 has at most
$`2\bigl((T + 2K(|S| + 1))c/\ell + 2K\bigr)` packets.”

Section Q.3 (page 68) lists Lemma I.2 among the statements “proved in stronger or more general
forms”.

*Reading (gloss).* The Lean statement is a conjunction of the sum formula and the bound on packets.
Its letters differ from the paper's: `ub` is the paper's $`\ell` (bits of a packet), `ℓ` is the
paper's $`T'` (symbols of a part, with `ℓ ≤ T`), `cb` is an injective code of the symbols and the
end mark (`none`) by `c` bits. The three sums are over `q : Fin (K + 1) → Q` with the two boundary
conditions, over `ρ` with `ValidRows ρ` (one triple of a flag and two nodes for every tape, the
input counted as the tape `none`, and every node), and over numbers `n a b` of packets from `a` to
`b` below `U0 + 1`. The summand is `Nc.posVal … fun y => ∏ p, Nc.G.tabInit …`: a sum over the
contents `y` of the copies of named packets, restricted to contents in which the two copies of
every packet agree, of the product over the $`2K` nodes of their node tensors. The node tensor
`Nc.G.tabInit` of a node is itself a sum over what the node writes and reads on every tape, with the
weight of the block (or the test of a part), restricted to choices that have the partners
prescribed by $`\rho` and whose coded strings fill the prescribed numbers of packets with the given
contents. The second conjunct is the printed bound, as $`\sum_b (n_{p,b} + n_{b,p})` for a node $`p`
whose node tensor is not zero at some contents.

The statement is more general than the printed one in three ways: the bound on the numbers of
packets is any `U0` with $`(T + |S| + 1)c/\mathtt{ub} + 1 \leq \mathtt{U0}`; packets have a
direction, and packets from a node to itself are allowed; and the network is set in a larger frame
with `A'` further nodes and further packet names (`N`, `U1`, `np`), which are the nodes and packets
that the moves of Theorem H.2 will add. Only consecutive parts of `ℓ` symbols (`Nc.Cut.parts`) are
stated. The definitions of `posVal` and `tabInit` were opened; the proof (`Nc.G.start`, files
`Nc/Cut/StartA.lean`, `StartB.lean`, `Rows.lean`, `Refine.lean`) was not.
:::

:::proof "lem_runnet"
*The paper's proof* (page 51), summarised. For an ordered pair $`(p, p')` of nodes the symbols that
$`p` writes and $`p'` reads on all $`|S| + 1` tapes, those of each tape closed by the end mark, form
one string, written on the packets from $`p` to $`p'`. The node tensor of the $`i`th block is the
sum over all sequences of $`T` letters with the partners prescribed by $`\rho` and the given
contents of the entry $`(q_{i-1}, q_i)` of the product of their matrices. In a matched sequence the
$`j`th symbol of one side of a tape meets the $`j`th symbol of the other, so the partners of a node
follow each other in order and every matched sequence belongs to one choice. Conversely, validity
of $`\rho` forces the words $`w_{pp'}` to be the same word in the order of the writers and in the
order of the readers.
:::

# J.1. Programs that cut

Appendix J measures everything in powers of a large integer $`v`, the *scale*. The paper's Table 2
(page 52) lists the exponents used from here to the end of Appendix K; “the exponents are not
optimized, and apart from the few inequalities noted in the table only their order matters” (page
51). Its rows, for a computation of $`\tau` steps, adapted from page 52:

- $`v^{300}`: the cut packets of a piece have at most $`KT\Lambda/v^{300}` bits (Proposition J.2);
  more than 256, so the next line absorbs these bits.
- $`v^{256}`: one cut adds $`\tau/v^{256}` to the inputs and $`\tau k/v^{256}` to the time of cutting
  (Theorem J.3); $`48 + 64 \leq 256`, so inputs stay shorter than times by $`v^{48}`.
- $`v^{64}`: the largest number $`k` for one cut; less than 300, so a single node of the tree is
  small enough for a piece.
- $`v^{63}`: $`k` for every cut but the last; the time stays at least $`v^{H+1}`.
- $`\tau/v^{48}`: inputs of a cut; exponent vectors and programs of a round fit (Proposition K.5).
- $`\tau/v^{24}`: time of listing the pieces; less than what a round saves.
- $`v^{H}`: time of the sums to be evaluated; a multiple of 16 with $`H \geq 272` and
  $`H \geq a_0 + 16`.
- $`v^{H-32}`: their inputs; programs of size $`v^{H/4}` fit.
- $`v^{H-16}`: time of an accelerator (Definition K.1); a round saves $`v^{8}`, with room for
  logarithms.

:::definition "def_cut" (lean := "Paper.def_cut, NS1.CutD") (parent := "part-contracting")
*Definition J.1 of the paper* (page 52), quoted: “A program $`G` *cuts* $`(\tau, s)` into
$`(\tau', s')` with $`P` pieces in $`t` steps if the following holds for every instance $`z` with
$`|z| \leq s`.

- All runs of $`G` on $`z` halt. The accepting ones take at most $`t` steps, have empty tallies,
  and output lists of at most $`P` instances of size at most $`s'`.
- If $`z` is $`\tau`-plain, then all these instances are $`\tau'`-plain, and
  $`\mathrm{sum}(z) = \sum_{\text{runs}} \mathrm{weight} \cdot \prod_{y \text{ in the list}} \mathrm{sum}(y)`,
  where the sum is over the accepting runs of $`G` on $`z`.”

`NS1.CutD` is the definition used in the proofs, through a list of pairs (weight, output); the
theorem `Paper.def_cut` proves that it is equivalent to the printed form, with `evl` for the
accepting runs, `bill` for the tally, `th` for the weight, `Tree.toList` for the list that an
output tree codes and `pv` for $`\mathrm{sum}`. The program is given as a tree `G` and run as
`Fm.ofTree G`; its argument is the instance `z` itself.
:::

The paper remarks (page 52): “The first condition is required of every instance of size at most
$`s`, plain or not, which Proposition K.5 uses.” A cutting program is thus a *total* reduction: it
halts within its time bound on every short input and its outputs are short, and only the meaning of
its outputs is conditional on the input being plain. The cutting program is itself a program of the
model, with weights in $`A` and guesses, so the identity is a weighted sum over its accepting runs.

# J.2. The pieces of a tree network

The paper (page 52): “By Lemma I.2 and Theorem H.2 the value of a tape automaton in $`KT` steps is a
sum of values of tree networks. The next proposition cuts each tree into subtrees, the pieces, each
with about the fraction $`1/k` of the nodes and of the packets, for a prescribed $`k`. Once the
packets between different pieces are fixed, the sum over all others is a product of one factor for
each piece, its value.” Throughout Appendix J, “$`\Lambda` denotes a power of $`\lg v` whose
exponent may grow a bounded number of times” (page 51).

:::proposition "prop_pieces" (lean := "Paper.prop_pieces, Paper.PieceCut, Paper.prop_pieces_identity") (parent := "part-contracting")
*Proposition J.2 of the paper* (the pieces of a computation; page 52), quoted: “For every tape
automaton over $`A` there are constants $`a`, $`a_K` and $`C`, where $`a_K \geq 300` and where $`a`
and $`a_K` do not depend on the automaton, with the following property. For all large $`v` there is
$`K` with $`v^{a_K} \leq K \leq C v^{a_K}` such that the statements below hold for all $`T \geq v^a`
with $`\lg T \leq (\lg v)^2` and all $`2 \leq k \leq v^{64}`. Cut an input word of at most $`KT'`
symbols, where $`T' \leq T`, into $`K` consecutive parts of $`T'` symbols, the last parts possibly
shorter or empty.

- The value of the automaton in $`KT` steps is the sum, over boundary states, valid data $`\rho` as
  in Lemma I.2, numbers of packets, good outcomes, and the contents of *cut* packets, of products of
  the values of at most $`k\Lambda` pieces.
- A piece has at most $`CK/k` blocks and parts, at most $`KT\Lambda/v^{300}` bits in cut packets,
  and at most $`KT\Lambda/k` bits in all.
- The packets, the pieces and what each node tensor consists of are computed from the numbers of
  packets and the outcomes by $`v^C` binary operations on numbers below $`v^C`.”

The paper's formalization note (page 52): “The last claim rests on Theorem H.2(d) and (e), whose
printed proofs only describe the program in question.”

*The clauses are fields of a structure.* The Lean theorem states the quantifiers of the proposition
and concludes `Nonempty (PieceCut …)`; the three clauses are fields of the structure `PieceCut`,
shown beside this node. Section Q.3 (page 68): “Theorem H.2 and Proposition J.2 state their clauses
as the fields of structures.” The standing hypotheses are explicit: a finite family of laws `VL`
with $`h \geq 3` and the condition (G.1), $`1 + 8C_1 \leq h/4`, over any commutative ring `A`.

*Reading (gloss): the fields against the clauses.*

- First clause: the field `value`. For all states `i`, `e`, every input `u` and every `ℓ ≤ T` with
  $`|u| \leq K\ell`, the value `Nc.runVal mu i e (K * T) u` is the sum over `q`, valid `ρ`, numbers
  `n` of packets with at most `load` packets at every node, outcomes `o` with `plan.good n o x` for
  every move `x`, and common contents `b` of the cut packets, of the product over the pieces
  `g : Fin num` of their values `grpVal … g b`. The number of pieces is bounded by the field
  `num_le`: $`\mathtt{num} \leq k (\lg v)^C`.
- Second clause: the fields `blocks_le` (the number of blocks and parts in a piece, times $`k`, is
  at most $`CK`), `cut_le` (the number of cut packets at a piece, times `ub`, times $`v^{300}`, is
  at most $`KT(\lg v)^C`) and `all_le` (a count `evG + pdG` of all packets of a piece, times `ub`,
  times $`k`, is at most $`KT(\lg v)^C`). All three are stated for numbers within `load` and good
  outcomes.
- Third clause: the fields `tab`, `tab_valid`, `digits` and `steps_le`. The field `tab` is a
  straight-line program with `steps` steps on numbers below `D` that computes the plan and the
  pieces; `steps_le` bounds `D`, `steps`, the number of nodes, of moves and the bounds `U0`, `U1`
  by $`v^C`.
- What good means: the field `good_iff`. For a law move, an outcome `o` is good when
  $`b \sum_\nu o_\nu^2 \leq G_1 t^2` and $`t \leq o_\nu` for every channel $`\nu`, where $`t` is the
  number of the move, $`b = 2^{h(h-1)/2}` and $`G_1 = \lfloor 2C_1a_1^2 \rfloor`; for a relay, when
  the outcome equals the number of packets of the batch on both channels. The field `poss_good`
  says that every outcome that can occur is good.
- Further fields that the printed statement does not have: the code `cb` of symbols by `c ≤ C`
  bits; the size `ub` of a packet with `ub ≤ T` and `load * ub ≤ T * lg v ^ C`; `kinds_mem`, that
  every role of a move is from a fixed finite list. Section Q.3 (page 69): “It also states what the
  program needs besides: the packets have at most $`T` bits, at most $`T\Lambda` bits start at a
  node, and the numbers of the program have room for packets, outcomes and pieces.”

*Differences that the paper states* (Section Q.3, page 69): “In Proposition J.2 the outcomes range
over tuples of numbers below a bound that is part of the data (the field `U1`); no clause says that
every good outcome lies below it, and the identity sums over those that do.” “Proposition J.2 is
proved without the bound on $`\lg T`, and its number of bits in all counts every copy ever held and
the zeros in slots. Its sum runs over the numbers of packets with at most $`N` packets at each node,
as in the printed proof, where Lean takes for $`N` the last bound of Lemma I.2, it is stated for
every pair of a first and a last state, and the exponent of $`\Lambda` is the constant $`C` of the
statement.” And, from the entry on Theorem H.2 (page 69): “The value of a tree is written as a sum,
over the contents of named packets, present or absent, of products of the values of its nodes, and
no theorem restates this as the value of a network as defined in Section H.” The same holds for the
value `grpVal` of a piece.

The fields were read as listed. The definitions behind them (`G.Plan`, `Sys`, `SlpTab`, `grpVal`,
`evG`, `pdG`) were not opened beyond their statements, so the glosses “number of cut packets” and
“all packets of a piece” for the left sides of `cut_le` and `all_le` follow the names and the
paper's sentence, not a reading of those definitions.

`Paper.prop_pieces_identity` is the step that regroups one network of Lemma I.2, through the tree
decomposition `ThinTrees` of Theorem H.2, into the sum over good outcomes and contents of cut
packets of products of values of pieces, for an arbitrary assignment `grp` of nodes to pieces.
:::

:::proof "prop_pieces"
*The paper's proof* (page 53), summarised. Take $`K = v^{a_K}` with $`a_K \geq 300` so large that
$`M^{-\gamma} \leq v^{-300}` for $`M = 2K`, packets of $`\ell = \lfloor T/v^{a'} \rfloor` bits, and
$`N = v^{a'}\Lambda` as the bound for the packets at a node, exceeding $`M^2`. Apply Lemma I.2, keep
the numbers that give every node at most $`N` packets, and apply Theorem H.2. With $`Y` the bound
for the total in Theorem H.2(b), a node of the tree is *heavy* if it is the root or if
$$`\frac{\#(\text{given nodes below})}{4M} + \frac{\#(\text{packets below})}{2Y} > \frac{1}{k},`
and light otherwise; each stage has fewer than $`k` heavy nodes, parents of heavy nodes are heavy,
and “a piece is a heavy node, or the subtree of a light node with a heavy parent, so there are at
most $`k\Lambda` pieces”. The packets between different pieces are the cut packets. By Theorem
H.2(b) a piece has at most $`\Lambda M^{1-\gamma} N \ell \leq KT\Lambda/v^{300}` bits in cut packets
besides the dead ones; a subtree that is a piece has at most $`4M/k` given nodes and $`2Y/k`
packets because its root is light. Parts (d) and (e) of Theorem H.2 give the last claim.

In Lean the heavy nodes and pieces of a staged tree are in `Paper/Heavy.lean`, and their
computation by binary operations in `Paper/HeavyProg.lean`; the number of pieces is
`Paper.pieceNum`, at most $`1 + C + b \cdot \mathrm{depth} \cdot k`.
:::

# J.3. One cut

The paper (page 53): “The next theorem turns Proposition J.2 into a program. Each piece becomes an
instance again, whose program is a fixed *evaluator* and whose argument is a *script* that describes
the piece.”

:::theorem "thm_onecut" (lean := "Paper.thm_onecut, Paper.Generates") (parent := "part-contracting")
*Theorem J.3 of the paper* (one cut; page 53), quoted: “There are constants $`a_0, C, v_0` such that
the following holds with $`\Lambda = (\lg v)^C`, for all $`v \geq v_0`, all $`\tau \geq v^{a_0}` with
$`4 \lg \tau \leq (\lg v)^2`, all $`s \leq \tau` and all $`2 \leq k \leq v^{64}`. Some program of size
at most $`v^{a_0}` cuts $`(\tau, s)` into
$`\bigl(\tau\Lambda/k,\ (s/k + \tau/v^{256})\Lambda\bigr)`
with at most $`k\Lambda` pieces, in $`(s + \tau k/v^{256})\Lambda` steps.”

The paper's formalization note (page 53): “The proof describes the evaluator and the cutting
program $`G` but does not print them, and that they are exact and keep the stated bounds is proved
only in the Lean development (Appendix Q).”

The Lean statement has the same quantifiers, and its conclusion is `CutD` with the four bounds
$`\tau (\lg v)^C / k`, $`(s/k + \tau/v^{256})(\lg v)^C`, $`k (\lg v)^C` and
$`(s + \tau k/v^{256})(\lg v)^C`, for a tree `G` of size at most $`v^{a_0}`. Its differences from
the printed statement are those that Section Q.3 (page 69) states: “Theorem H.2, Proposition J.2
and Theorems J.3 and J.4 have the laws, and the last two the generators of $`A`, as explicit
standing hypotheses. The laws may be any finite family of laws, over any commutative ring, that has
the properties of Theorem G.2, with $`h \geq 3` and (G.1) as hypotheses” and “The quotients in the
bounds of Theorems J.3 and J.4 are rounded down in Lean.” The hypothesis on the generators is
`Generates θ`: the table `θ` has finite support and every element of `A` is the value of a fixed
sum of products of named generators.
:::

:::proof "thm_onecut"
*The paper's proof* (pages 53–54), summarised. Let $`K, a` be as in Proposition J.2 for the
universal automaton and $`T = \lceil \tau\Lambda/K \rceil`. For a $`\tau`-plain $`z` with
$`|z| \leq s \leq \tau`, $`KT` exceeds the bound of Proposition I.1, so $`\mathrm{sum}(z)` is the
value of the universal automaton on the word of $`z` in $`KT` steps, and Proposition J.2 gives a
formula for it. The tree, the packets and the pieces of one choice are its *plan*. A *script* of a
piece contains $`T` and $`\ell` in binary, the contents of its cut packets, the names of its inner
packets, and instructions of three kinds: `Block` (the boundary states of a block, its entries of
$`\rho`, the numbers of packets and the names of the packets that carry them), `Role` (“the part of
one node in one law move: the law, the number $`t`, the outcome, and for every slot and channel at
this node the names of the packets that supply or receive its bits”) and `Test` (two packets are
equal, or one is zero). The *evaluator* guesses the contents of all inner packets; for `Block` it
guesses $`T` letters and the states between them and multiplies by the matrix entries; for `Role`
it guesses the index of each of the $`t\ell` layers and the bits of its channels and multiplies by
the entries of the node tensors of the law. “An entry of a matrix or of a node tensor is an element
of $`A`, hence a fixed sum of products of the generators, so multiplying by it is guessing a
summand and multiplying by its factors.” Hence the sum of the instance (evaluator, script) is the
value of the piece, and it is plain within
$`(\#\text{blocks} \cdot T + \#\text{bits of packets} + \#\text{instructions} \cdot v^{O(1)})(\lg v)^{O(1)} \leq \tau\Lambda/k`
steps. The program $`G` contains the tables of the tower; on $`z` it writes the word of $`z`, cuts
it into $`K` parts, guesses $`q`, $`\rho`, the numbers of packets and the outcomes, rejects unless
$`\rho` is valid, the numbers are within $`N` and the outcomes are good, computes the plan by the
binary operations, guesses the contents of the cut packets, and outputs the list of the instances
(evaluator, script). “All of this is deterministic except for the guesses, and every choice in the
formula is guessed exactly once, so the sum formula is the one obtained above.”

*Reading (gloss): the Lean proof.* `Paper.thm_onecut` obtains the universal automaton from
`Paper.prop_universal` and, for this automaton, a `PieceCut` from `Paper.prop_pieces`; it then
puts two programs on them, each with its own theorem (the two nodes below), and the rest of its
proof, about 350 lines, is arithmetic between the numbers of the two theorems and the bounds of the
statement. The two programs live in two libraries.

- *The evaluator* is the program `GROUP` of `Nc/Grp` (28 files; the Lean word for a piece is
  *group*). `Nc.Grp.exists_group` gives, for a fixed automaton, a fixed code of symbols and a fixed
  finite list of roles of laws, one program `GROUP` and a step cost `κ`. Its specification is the
  predicate `Nc.Dl.GroupOK`: for every plan, every choice `q`, `ρ`, `n`, `o`, every assignment `grp`
  of nodes to pieces, every piece `g`, every injective naming of packets by bit strings and every
  content `b` of packets, the instance (code of `GROUP`, script of `g`) is plain within `κ` times an
  explicit cost `grpT` of the script, and its sum is `grpVal … g b`, the value of the piece that
  occurs in `PieceCut.value`. A third clause says that if `GROUP` has an accepting run at all, then
  the numbers of packets at the nodes of the piece obey the bound of Lemma I.2 and the outcomes at
  its roles are the outcomes of some choice of indices; this is how the bounds on packets needed for
  the time are obtained from one contributing choice. `Nc.Dl.GrpTimeOK` bounds `grpT` by the numbers
  of blocks, packets and names of the piece. The script is a tree built by `Nc.Grp.script` and
  `Nc.Grp.scriptT` (`Nc/Grp/Script.lean`). Inside, `GROUP` is assembled from the program of a base
  node (a block or a part: simulate the automaton or take the part of the input, cut what is
  written on each tape into segments for the partners, cut the strings into packets;
  `Nc/Grp/Base*.lean`, `Seg*.lean`, `Pack.lean`, `Put*.lean`) and the program of a role, a finite
  transducer run for $`t \cdot \mathtt{ub}` steps (`Nc/Grp/Role*.lean`, `Trans.lean`); the value of a
  piece is first rewritten as a sum over executions of these steps in a fixed order
  (`Nc/Grp/GrpSteps.lean`, `GrpVal.lean`, `Steps.lean`).
- *The cutting program* is the *dealing program* of `Nc/Dl` (22 files) on the general machinery
  of `NS1` for programs that proceed by steps writing named values into a trie (`NS1/Deal.lean`,
  `DSteps.lean`, `Picks.lean`, `Parts.lean`). Its theorem `Paper.thm_onecut_program` (below) takes
  as hypotheses the specification `GroupOK` of the evaluator, the statement of the universal
  automaton, the straight-line program `tab` of the plan and the sum formula of `PieceCut.value`,
  and concludes that a program `G` cuts, with explicit numbers for its size, its time and the sizes
  of the scripts.

*What was read.* The statement and the first part of the proof of `Paper.thm_onecut`, the
statements of the two nodes below, the definition of `GroupOK`, and the module headers of `Nc/Grp`,
`Nc/Dl` and `Nc/Cut`. Not read: the programs themselves and the proofs about them (about 11,700
lines in `Nc/Grp` and `Nc/Dl`). The description of the internal structure of `GROUP` and of the
dealing program above is taken from the organisation of the files and their names, and is the
least checked passage of this chapter. Section Q.3 (page 70) names “the semantics of scripts inside
the evaluator” among the steps that exist only under names of the underlying library.
:::

:::lemma_ "thm_onecut_evaluator" (lean := "Paper.thm_onecut_evaluator, Nc.Dl.GroupOK, Nc.Dl.GrpTimeOK") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem J.3* (the evaluator; page 54), quoted: “Hence the sum
of the instance (evaluator, script) is the value of the piece. All its loops have lengths that
stand in the script, so all its runs halt”.

Section Q.3 (page 69): “The programs of Theorem J.3 are written out in full, where we describe them
(`thm_onecut_evaluator`, `thm_onecut_program`).” The Lean statement: for generators `θ`, an
automaton `mu`, a code `cb` and a list `kinds` of roles there are a program `GROUP` and a number
`κ` with `GroupOK` and `GrpTimeOK`. The content is in those two predicates, shown beside this node.
:::

:::lemma_ "thm_onecut_program" (lean := "Paper.thm_onecut_program") (parent := "part-contracting")
*An unnumbered step of the proof of Theorem J.3* (the program $`G`; page 54), quoted: “All of this
is deterministic except for the guesses, and every choice in the formula is guessed exactly once,
so the sum formula is the one obtained above.”

The Lean statement is long, because every number of the construction is a parameter with its own
hypothesis; its conclusion is a program that cuts, in the sense of `CutD`, with explicit bounds.
:::

# J.4. Cuts at all scales

The paper (page 54): “We now repeat the cut of Theorem J.3 until the pieces take $`v^H` steps, and
the point to watch is that the inputs remain shorter than the times by the factor $`v^{48}`, up to a
factor 4 for each cut.”

:::theorem "thm_cut" (lean := "Paper.thm_cut, Paper.cutHyp_of_laws, Paper.exists_setting, NS1.CutProg, NS1.CutHyp") (parent := "part-contracting")
*Theorem J.4 of the paper* (cuts at all scales; pages 54–55), quoted: “There are a multiple
$`H \geq 272` of 16 and constants $`C_{\mathrm{cut}}, v_0` such that the following holds whenever
$`v \geq v_0` and $`\alpha` satisfy $`(\lg v)^{C_{\mathrm{cut}}\alpha} \leq v`. For all $`\tau` and
$`s` with $`v^H \leq \tau \leq v^{H\alpha}` and $`s v^{48} \leq \tau`, some program of size at most
$`v^H` cuts $`(\tau, s)` into $`(v^H, v^{H-32})` with at most $`\tau v^2/v^H` pieces in at most
$`\tau/v^{24}` steps.”

`Paper.thm_cut` is this statement with the laws and the generators as standing hypotheses and the
two quotients rounded down (Section Q.3, page 69, as quoted under Theorem J.3). Two further
declarations give the forms that the next chapter uses.

- `NS1.CutHyp θ H C₀ v₀` is the conclusion of the theorem as a property of a ring `A` with a table
  `θ`, with the quotients multiplied out (`NS1.CutProg`: a run costs $`c` steps with
  $`c\, v^{24} \leq \tau` and outputs $`P` pieces with $`P\, v^H \leq \tau v^2`).
  `Paper.cutHyp_of_laws` derives it from `thm_cut` with $`H = 16h`, $`h \geq 17`.
- `Paper.exists_setting` is the instance in the contracting case: for a field `K` (in the lowest
  universe) with `Contracting K` there are a subring `A` of `K` that is finitely generated as a
  ring, a table `θ` with `Generates θ`, and `h ≥ 17`, `C₀`, `v₀` with `CutHyp θ (16 * h) C₀ v₀`.
  Section Q.3 (page 69): “In the contracting case `exists_laws` and `exists_generates` supply these
  hypotheses, and `exists_setting` states the conclusion of Theorem J.4 without them.”
:::

:::proof "thm_cut"
*The paper's proof* (page 55), summarised. Let $`H` be a multiple of 16 with $`H \geq 272` and
$`H \geq a_0 + 16`. Cut by $`k = v^{63}` as long as $`\tau\Lambda \geq v^{H+64}` and at last once by
$`k = \lfloor \tau\Lambda/v^H \rfloor + 1`, composing the programs so that the next one is run on
every piece in the list; there are $`r = O(\alpha)` cuts, and the condition on $`v` gives
$`4\lg\tau \leq (\lg v)^2`. With $`(\tau_i, s_i)` the parameters after $`i` cuts and $`P_i` the
number of pieces, three bounds hold by induction: $`s_i v^{48} \leq 4^i \tau_i` (because
$`k \leq v^{64}` and $`48 + 64 \leq 256`), $`P_i \tau_i \leq \tau (4\Lambda^2)^i`, and the next cut
takes at most $`2 \cdot 4^i \tau_i \Lambda / v^{48}` steps on each piece; “moreover, the sum formulas
compose”. All the powers of $`\Lambda` that arise are below $`v` if $`C_{\mathrm{cut}}` is large.

*Reading (gloss): the Lean proof.* The composition of two cutting programs is the program
`NS1.compC` (`NS1/Compose.lean`): run `G`, then fold over the list of pieces, running `G'` on each
and appending the results; that the sum formulas compose is `NS1.wsum_foldW_pvs` and the theorems
after it. The induction on the numbers of steps, sizes and pieces is `NS1/OneCut.lean`, which takes
“one cut by any factor $`k \leq v^{64}`” as a hypothesis. `Paper.thm_cut` takes $`H = 16h` with
$`h = a_0 + 217`. The statements of `compC` and of `thm_cut` were read; the induction of
`NS1/OneCut.lean` was not.
:::

The paper's remark after the proof (page 55): “For a fixed $`\alpha` the condition
$`(\lg v)^{C_{\mathrm{cut}}\alpha} \leq v` holds for all large $`v`, and this is all that Theorem L.2
needs.”

# What the next chapter takes from this one

{ref "chapter-accelerators"}[Accelerators and the diagonal argument] uses of Appendices F to J
exactly the property `NS1.CutHyp θ (16 * h) C₀ v₀` with $`h \geq 17`, for a commutative ring $`A`
with a table `θ` of named elements, together with the program model of Section I.1 and, in
Lemma K.3, the universal automaton of Proposition I.1. Section Q.3 (page 69): “Proposition K.5,
Theorem K.6 and Proposition N.4 do not assume the contracting case. They take the conclusion of
Theorem J.4 as a hypothesis (`CutHyp`), for a commutative ring $`A`, which has to be finitely
generated only in Theorem K.6 and Proposition N.4, and $`H = 16h` with $`h \geq 17`”. The geometry
of the first chapters, the laws and the trees do not appear again.
