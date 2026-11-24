# Common and flat proof review

Baseline 9fd368ad. The section below distinguishes full reads from targeted proof-body inspection and the declaration/dependency index. Kernel checking alone does not count as a mathematical read.

## Checked changes

- Assembly commit 320ae2d. Reviewed both specialization arguments in Transfer, the field dichotomy, threshold combination, flat and contracting conversions, Laurent witness conversion, exact and approximate class separation. Kept specialization separate because the Laurent proof specializes all coefficients in a finite support. The exact bound does not require closure/approximation. Characteristic two still excludes only the permanent.
- Flat commit 1a59bf0. Replaced E.6's direct cardinal/logarithm calibration with the E.11 quantitative rate and the same growing-exponent proof used for L.2. E.5 and its denominator 6 remain as their own proof. E.3 and E.11 are the completeness-factor-three instances of their general statements. Read the original proofs of all four results. Checked Algebraic Flat, Rate, Fields, Identity, States, Alternative, Core.Basic directly. The exact and approximate outputs were checked together with Solution after the assembly commit.
- Meixner B and C use the same triangular recurrence with their two slopes exchanged. Kept them to verify the series in the paper. The root-infimum equality in Gauges likewise compares two genuinely different descriptions of the radius. Removed the immediate aliases mem_states, mem_stateClass, distAtRank_sq (definitions, mem_pairs and meanSq_nonneg suffice), and withVal_val. Deleting the candidate one_val actually broke simp in Restr.one_le; kept that simp rule.
- NS1.Comp and Nc.Acc.CompK independent source review of edited support/conditional arguments. Singleton output is determined for every run in the support. Nil selects the third formula. The new proof preserves cost, bill and weight identities, with the same public true/false rule types.

## Full file reads

- Nc.Cat.Space (midpoint term depth and placement); Nc.Cat.Prod (square of the product metric); Nc.Plus.Interface (exclusive membership); Nc.Plus.UnitBits (word/empty encoding); Nc.Vp.Main (tower law reindexing); Nc.CaseI.Cube (opposite corners); Nc.Price.Network (product of wires); Nc.Price.LawF (variable-width wires to single-bit slots); Ov.Duality.PreSpec (monotonicity by singleton cover).
- Nc.Cross.Inv (site permutation and products of row/column multipliers); Nc.Cross.One (strictly increasing row/column tuples, missing row forces zero determinant); Nc.Cross.Psi (four blocks, coefficient maps, determinant congruence via quotient); Nc.Cross.Ident (state to word embedding via ranges, energy conservation); Nc.Cross.Meix (two triangular recurrences and map compatibility); Nc.WidePerm (definitions only).

## Partial mathematical reads

All assigned modules have a declaration and proof-length inventory, plus a sample from the body of the largest proof where present. Those samples are not full module reads.

- Paper.Flat: E.3, E.5 geometry and largest-term argument, E.6 original calibration, E.10 auxiliary hub-cover, projection/unused variables; Paper.Rate: flat-family specialization, E.10 geometry and E.11 asymptotics, exponent-conversion, original real results; Paper.Identity: Meixner coefficient series, selected orthogonality, low-degree blocks; Paper.Alternative: squared rank mean and telescoping rank-one bound. Paper.Gauges: radius definition, submultiplicativity via positive approximants and concrete root characterization. Paper.States: membership and interleaving.
- Nc.Cat.Mean: full coordinate-translation proof including telescoping two rectangular boundary sums and integrable boundedness. Nc.Cat.Len: full homogenization via Fekete limit, preservation of quadratic inequality. Nc.CaseI.Lower and Geo: ordered pairs, diagonal subtraction, and sign-vector sum. Nc.PermValiant: full affine substitution proof, including the addition, multiplication and five-gate affine input blocks. Ov.Core.Unit: multiplicative monotonicity calculation using adjacent binary powers; Ov.Core.Basic: unit tensor, local map and singleton restriction. Ov.Duality.Cert: product infimum, certificate cover and preservation of Keeps.
- Paper.Fan: full random subdivision construction in thm_cn_segments and outlines of thm_cn_fan, Lipschitz and telescope; Paper.Prices: hub and random limit; Paper.Tensors: zero tensor case and tree exponent; Paper.Extension: extension by cover/product/gauge; Paper.Crossing: crossing tensor size indices and spectral inequality transfer; Paper.Curvature: Cauchy midpoint estimate and depth-inducted midpoint creation; Paper.Means: length estimate/telescoping; Paper.Toolkit: minimizer by metric strong convexity and distance estimate; Paper.Convex: spectrum point extension and opposite cube endpoints; Paper.Grids: clause encoding and affine entry choices; Paper.Ryser: sum over functions and surjectivity, explicit witness circuit size.

## Further complete proof-body reads

Read the full original files in Nc.Cross.{Count,Data,Split,Near}, Nc.Cat.{Core,Len}, Nc.CaseI.{Fkl,Geo,Hub,Lower}, Nc.{PermCoeff,PermPad,PermSum,PermValiant}, Nc.Vp.Gen, Ov.Core.{Tensor,Equi,Wire,Spec}, Ov.Duality.{Abstract,Minimal,Cert}, and Nc.Price.{Cover,Law,Basic,Hyper,Cross,Norm}. Count's energy addition, Core's midpoint construction, Len's closed quadratic bound, the sign function in Hub, and the permutation fiber bijection led to checked changes. Kept the truncated split in Near and the zero and nonzero cases in Lower. Hyper required the wire, tensor, and restriction primitives only. In Abstract the directedness condition supplies a common lower index after distributing the product over both infima.

Reviewed Ov.Core.Network and Nc.Price.BorderSum in full. The former explicitly handles empty index assignments before extending local maps and uses a diagonal wire constraint to collapse edge labels. The latter uses X-divisibility below the leading degree and assigns the total-degree test at one party in the coefficient restriction.

Read Paper.Ryser and Paper.Grids in full. Ryser's function sum cancels a missing column and finite surjectivity is equivalent to bijectivity. The explicit signed summand has a bounded circuit even in characteristic two. Grids' nonempty clause hypothesis selects a distinguished literal that contributes the weight minus one. Surjectivity of the incidence maps and the matrix padding are both used.

Read Paper.Extension in full. The cover comparison uses a retraction for each factor, the gauge is the infimum of cover weights, and its value at the distinguished tensor is preserved separately for zero and positive spectral price. Focused Fkl, Lower, Hub, Flat, and Rate passed after moving the circuit-renaming import to Flat.

Read Paper.Fan in full, including both random subdivisions and the shared end, clamped windows, the horizontal/diagonal/vertical step estimates, the squared potential telescope and arithmetic error in claim (iv), the discrete concavity bound, and both parameter limits. Claims (i) and (iv) telescope different potentials. The radial length bound already works for arbitrary increments by nonexpansiveness of clamping. This subsumes an induction in the estimate for the change of the square.

Read Nc.Cat.Window, Nc.Cat.Length and Nc.CaseI.Multi in full. Window retains the exact limiting mean of the clamped coordinate, the discrete second-difference estimate and sq_core. Length now reduces a single pointwise crossing inequality under the mean using linearity and the square identity; its eight Cauchy–Schwarz comparisons remain explicit. Multi's multiplication proof partitions squarefree monomials by subsets of blocks, and the circuit decomposition follows the larger side of each split or selects a balanced gate directly.

Read Paper.Alternative and Nc.Cat.Mean in full. Alternative's compactness argument normalizes D(1), equality propagates from the maximum rank to all ranks, exchange of independent row and column vectors makes orthogonality propagate, and the rank metric first gives cube vertices, then an isometric solid cube by interpolation. The preliminary uniform bound admits a shorter proof: any squared distance is one nonnegative term in its rank class, whose mean is bounded by the rank times the rank-one mean. Mean's normalization at n = 0, compact interval ultrafilter, two distinct rectangular boundary sums, square-root seminorm, and Cauchy–Schwarz with a positive balancing parameter were reviewed.

Read Paper.Identity in full, including the three induction branches of orthogonality, all sixteen matrix-entry reflection cases, sign at X=1, Schur expansion and the rank bounds for both ends of the coefficient range. The two boundary cases share the same telescoping sum. The invertible-variable reflection uses the fraction field only to prove a polynomial identity over the integers and handles zero polynomials when transferring degree and coefficient constraints.

Read Paper.States, Paper.Curvature, Paper.Tensors and Ov.Core.Basic in full. The asymptotic count picks an almost-maximizing energy and uses its square-spaced multiples to fill the gaps. Midpoint completion extends the inequality by density before proving convergence of the midpoint sequence. The tensor calculus handles the empty cover, identity, composition and dependent reindexing of restrictions. The proof of wire-tree restriction can contract directly over the given vertex type.

Read Ov.Core.Unit and Nc.Price.BorderFew in full. Unit uses adjacent powers of two to identify all monotone multiplicative functions, and distinguishes grouping several legs at one party from moving a leg through a wire. BorderFew reorders each word type by permutations, selects the order via the shared unit tensor, counts only polynomially many types, and removes the polynomial prefactor by the power bound. The empty support and empty type-class cases are handled explicitly.

Read Paper.Crossing and Paper.Means in full. Crossing passes from the two different hub decompositions to logarithmic bounds, compactness of the quarter disk, and Young's inequality. Projection from a compact factor proves that feasibility of both inequalities is closed. Means homogenizes the RMS length, uses a discrete convexity estimate for translated differences, and sends the averaging parameter to infinity before recovering the reverse parallelogram inequality.

Completed Paper.Prices and Paper.Toolkit. Prices derives the compactness reduction by simultaneously controlling finite restrictions, and uses specified wire values to preserve distances on old parties. Toolkit's quadrilateral inequality clears the positive denominator after applying the comparison inequality. The more general midpoint and limit arguments retain their assumptions.

Completed the full pinned texts of Paper.Gauges, Flat, Convex and Rate. Gauges' word-growth proof increments one exponent, then takes a common constant over the finite set of generators. Minimality identifies the radius, localization at positive elements forces multiplicativity, and the certificate proof exchanges at least one factor per step before eliminating the bounded residue. Kept the radius formula that identifies the printed Fekete quantity. Flat encodes assignments as clauses, expands balanced products on complementary variable blocks, then evaluates the resulting tensor cover with hubs for a maximizing balanced set. Its original final argument for E.6 picks a largest admissible string length at fixed k, subsumed by the explicit uniform rate. Convex controls an approximate midpoint by the CAT inequality and induces over sign-cube levels, budgeting the accumulated error. Rate uses the signed cut vector to bound the hub direction, retains separate price errors on ends, hubs and the hyperedge, and optimizes the projection using k=r² and ℓ=100r. The direct geometric argument in E.5 earns its place through its stronger exponent for sufficiently large ℓ. The real-only specializations and eventual polynomial comparison are shared.

Read Nc.PermGrid in full. Its three slots force the two orbit-invariance conditions and uniquely determine the auxiliary bit. Reindexing the false-branch contributions by the second permutation yields the desired weights, including fixed points. Keep the characteristic-dependent gadget equation separate from this incidence calculation.

## Complete baseline coverage
The following pinned source files have had their proof bodies reviewed. Files carrying only definitions were reviewed as definitions. Earlier partial entries record checkpoints during this work.
Nc/CaseI/Cube.lean
Nc/CaseI/Fkl.lean
Nc/CaseI/Geo.lean
Nc/CaseI/Hub.lean
Nc/CaseI/Lower.lean
Nc/CaseI/Multi.lean
Nc/Cat/Core.lean
Nc/Cat/Len.lean
Nc/Cat/Length.lean
Nc/Cat/Mean.lean
Nc/Cat/Prod.lean
Nc/Cat/Space.lean
Nc/Cat/Window.lean
Nc/Cross/Count.lean
Nc/Cross/Data.lean
Nc/Cross/Ident.lean
Nc/Cross/Inv.lean
Nc/Cross/Meix.lean
Nc/Cross/Near.lean
Nc/Cross/One.lean
Nc/Cross/Psi.lean
Nc/Cross/Split.lean
Nc/PermCoeff.lean
Nc/PermGrid.lean
Nc/PermPad.lean
Nc/PermSum.lean
Nc/PermValiant.lean
Nc/Plus/Interface.lean
Nc/Plus/UnitBits.lean
Nc/Price/Basic.lean
Nc/Price/BorderFew.lean
Nc/Price/BorderSum.lean
Nc/Price/Cover.lean
Nc/Price/Cross.lean
Nc/Price/Hyper.lean
Nc/Price/Law.lean
Nc/Price/LawF.lean
Nc/Price/Network.lean
Nc/Price/Norm.lean
Nc/Vp/Gen.lean
Nc/Vp/Main.lean
Nc/WidePerm.lean
Ov/Core/Basic.lean
Ov/Core/Equi.lean
Ov/Core/Network.lean
Ov/Core/Spec.lean
Ov/Core/Tensor.lean
Ov/Core/Unit.lean
Ov/Core/Wire.lean
Ov/Duality/Abstract.lean
Ov/Duality/Cert.lean
Ov/Duality/Minimal.lean
Ov/Duality/PreSpec.lean
Paper/Alternative.lean
Paper/Convex.lean
Paper/Crossing.lean
Paper/Curvature.lean
Paper/Extension.lean
Paper/Fan.lean
Paper/Flat.lean
Paper/Gauges.lean
Paper/Grids.lean
Paper/Identity.lean
Paper/Means.lean
Paper/Prices.lean
Paper/Rate.lean
Paper/Ryser.lean
Paper/States.lean
Paper/Tensors.lean
Paper/Toolkit.lean
