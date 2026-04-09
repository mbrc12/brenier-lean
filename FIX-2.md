# Remaining Plan to Reach the Classical Brenier Theorem

This note records the remaining steps after the proper-convex migration.

At this point, the repository already has:

- the measure-theoretic existence layer;
- the proper-convex API `Φ : E → WithTop ℝ`;
- the proper Brenier bridge:
  if `support π ⊆ ProperSubgradientGraph Φ`, `Φ` is measurable and proper convex, and
  `μ ≪ volume`, then `π` is a graph plan induced by
  `gradient (fun x => (Φ x).untopD 0)`.

What is still missing is the automatic production of such a `Φ` from optimality alone, with no
extra Rockafellar boundedness hypothesis.

## Main remaining gap

The repository does **not** yet prove the classical chain

- optimal quadratic coupling
- `=>` cyclical monotonicity of the support
- `=>` proper Rockafellar potential with support contained in its proper subgradient graph
- `=>` graph concentration by the Brenier bridge

without extra assumptions.

The missing work is concentrated in the Rockafellar and cyclical-monotonicity layers.

## Step 1. Measurability of the proper Rockafellar potential

File:

- `OptimalTransport/Rockafellar.lean`

Needed theorem:

- `Measurable (properRockafellarPotential base Γ)`

Reason:

- the new proper-convex Brenier bridge in `Brenier.lean` now assumes `Measurable Φ`;
- for the final theorem we want to apply it with `Φ = properRockafellarPotential base Γ`.

Likely route:

- prove measurability of each chain functional `x ↦ rockafellarChainValue l x`;
- express sublevel/superlevel information for the `sSup` over rooted chain values;
- use countable generation from finite chains if needed.

## Step 2. Pointwise finiteness on a cyclically monotone set

File:

- `OptimalTransport/Rockafellar.lean`

Key theorem to prove:

- if `Γ` is pairing-cyclically monotone, `base ∈ Γ`, and `(x, y) ∈ Γ`,
  then `properRockafellarPotential base Γ x < ⊤`.

Reason:

- this removes the old global boundedness assumption from the Rockafellar construction;
- it is the precise replacement for `HasRockafellarBound`.

Core estimate:

- for any rooted finite chain ending at `x`, pairing-cyclical monotonicity should give an upper
  bound by `⟪y, x - base.1⟫`;
- therefore the rooted value set at `x` is bounded above;
- hence the proper Rockafellar potential is finite at `x`.

## Step 3. Full proper Rockafellar containment from cyclical monotonicity

File:

- `OptimalTransport/Rockafellar.lean`

Needed theorem:

- if `Γ` is pairing-cyclically monotone and `base ∈ Γ`, then
  `Γ ⊆ ProperSubgradientGraph (properRockafellarPotential base Γ)`.

Reason:

- the file currently has only the local containment theorem
  `properSubgradient_properRockafellarPotential_of_mem_of_lt_top`;
- Step 2 should provide the finiteness hypothesis needed to apply it at every point of `Γ`.

This is the theorem that should replace the old bounded-above real-valued containment theorem as the
main Rockafellar result.

## Step 4. Finish optimality => cyclical monotonicity

File:

- `OptimalTransport/CyclicMonotone.lean`

Needed theorem:

- if `π` is optimal for the continuous quadratic cost and has finite transport cost, then
  `support π` is `c`-cyclically monotone.

Then specialize:

- for quadratic/Brenier-friendly costs, rewrite this as pairing-cyclical monotonicity.

Reason:

- this is the missing link from optimal transport to the Rockafellar construction.

The local rectangle and local cost-control lemmas are already in place; this step is the global
perturbation argument using those local pieces.

### Detailed plan for Step 4

The proof should now be organized as a finite-measure replacement argument around a fixed
strict cycle-gap witness.

#### 4A. Fix the contradiction data

Assume:

- `c : X → Y → ℝ` is continuous;
- `π : Coupling μ ν` is optimal for `c`;
- `Integrable (fun z => c z.1 z.2) (π.toTransportPlan : Measure (X × Y))`;
- `p : Fin (n + 1) → X × Y` is injective, each `p i` lies in `support π`,
  and `0 < cycleGap c p`.

Apply

- `exists_pairwiseDisjoint_open_rectangles_of_cycleGap_pos_with_costControl`

to obtain open rectangles `U i × V i` and a bound `B` such that:

- each `p i ∈ U i × V i`;
- the rectangles are pairwise disjoint;
- every `q i ∈ U i × V i` still satisfies `0 < cycleGap c q`;
- `|c| < B` on every diagonal rectangle `U i × V i`;
- `|c| < B` on every cyclic rectangle `U i × V (i + 1)`.

#### 4B. Extract positive-mass local pieces

For each `i`, define the finite measure

- `κ i := π.toTransportPlan.toFiniteMeasure.restrict (U i ×ˢ V i)`.

Use:

- support membership of `p i`,
- openness of `U i × V i`,
- `FiniteMeasure.restrict_nonzero_of_mem_support_of_isOpen`

to prove `κ i ≠ 0`.

Then define the normalized probability pieces

- `ξ i := (κ i).normalize : ProbabilityMeasure (X × Y)`.

Use the new helper lemmas to record:

- `ξ i` is a.e. contained in `U i × V i`,
- `TransportPlan.fst (ξ i)` is a.e. contained in `U i`,
- `TransportPlan.snd (ξ i)` is a.e. contained in `V i`.

#### 4C. Choose a common removable mass

Define

- `m i := κ i.mass : ℝ≥0`,
- `t := Finset.univ.inf' Finset.univ_nonempty m`.

Prove:

- `0 < t`,
- `t ≤ κ i.mass` for every `i`.

The point of `t` is that one can remove `t` units of mass from every diagonal piece `κ i`
simultaneously.

#### 4D. Build the old and new finite pieces

Define the diagonal removable part:

- `old i := t • (ξ i).toFiniteMeasure`,
- `old := ∑ i, old i`.

Define the shifted replacement part:

- `new i :=
    t • (((TransportPlan.fst (ξ i)).prod (TransportPlan.snd (ξ (i + 1)))).toFiniteMeasure)`,
- `new := ∑ i, new i`.

At this stage prove:

- `old i ≤ κ i` for each `i`, by combining
  `κ i = κ i.mass • (ξ i).toFiniteMeasure`
  with `t ≤ κ i.mass`;
- `old ≤ π.toTransportPlan.toFiniteMeasure`, using pairwise disjointness of the rectangles and
  `FiniteMeasure.sum_restrict_eq_restrict_biUnion_finset`;
- both `old` and `new` are finite;
- the support of `old i` is inside `U i × V i`;
- the support of `new i` is inside `U i × V (i + 1)`.

#### 4E. Define the competitor

Pass to measures and define

- `ρ := (π : Measure (X × Y)) - old + new`.

Then package `ρ` as a `Coupling μ ν`.

The key identities are:

- subtraction commutes with `fst` and `snd` under domination,
  using `Measure.fst_sub_of_le` and `Measure.snd_sub_of_le`;
- `fst new = fst old`,
- `snd new = snd old`.

The last two are proved termwise:

- `fst (new i) = t • TransportPlan.fst (ξ i)`,
- `snd (new i) = t • TransportPlan.snd (ξ (i + 1))`,
- summing over `i` and using cyclic reindexing gives equality with the marginals of `old`.

Hence:

- `ρ.fst = μ`,
- `ρ.snd = ν`.

#### 4F. Prove integrability of the competitor pieces

The original plan already has finite cost by hypothesis. The only issue is the inserted part `new`.

Use the local bound `|c| < B` on `U i × V (i + 1)` and the a.e. concentration of `new i` on that
rectangle to prove:

- each `new i` has finite `c`-integral,
- hence `new` has finite `c`-integral.

Similarly, `old` is finite because it is dominated by `π`.

So the cost of `ρ` is a well-defined real number and one can expand:

- `∫ c dρ = ∫ c dπ - ∫ c dold + ∫ c dnew`.

#### 4G. Compute the strict cost drop

The goal is:

- `∫ c dnew < ∫ c dold`.

For each `i`:

- `∫ c dold_i = t * ∫ c(x,y) dξ_i(x,y)`,
- `∫ c dnew_i =
    t * ∫ c(x,y) d((TransportPlan.fst ξ_i).prod (TransportPlan.snd ξ_{i+1}))(x,y)`.

To compute the shifted term, use:

- the product-law identity already proved for finite products,
  `map_pair_eval_eq_prod_map_eval`,

so that the sum of all shifted costs can be written as the expectation of the cyclic cross terms
under the product probability measure `ProbabilityMeasure.pi ξ`.

Likewise, the diagonal sum is the expectation of the diagonal terms under the same product measure.

Therefore:

- `∫ c dold - ∫ c dnew
    = t * ∫ cycleGap c q d(ProbabilityMeasure.pi ξ)`.

Now use:

- every sampled `q` lies in the rectangles `U i × V i` almost surely,
- on those rectangles the cycle gap is strictly positive,

to deduce that the right-hand side is strictly positive.

Hence:

- `transportCost c ρ < transportCost c π.toTransportPlan`.

#### 4H. Conclude cyclical monotonicity

The strict inequality contradicts optimality of `π`.

Therefore no strict cycle-gap witness can exist, so:

- `support π` is `c`-cyclically monotone.

#### 4I. Final theorem packaging

The file should end this step with:

- a theorem in the continuous real-valued branch saying optimality plus finite cost implies
  `CCyclicallyMonotone c ((π.toTransportPlan : Measure (X × Y)).support)`;
- then the Brenier-friendly specialization converting quadratic-type costs to pairing
  cyclical monotonicity.

## Step 5A. Convert cycle inequalities to Rockafellar closed chains

Files:

- `OptimalTransport/CyclicMonotone.lean`
- `OptimalTransport/Rockafellar.lean`

Needed theorem:

- `CCyclicallyMonotone (fun x y => -⟪x, y⟫) Γ`
  `=>`
  `PairingClosedChainMonotone Γ`

or equivalently a direct theorem from the quadratic specialization already proved in
`CyclicMonotone.lean` to the list-based rooted closed-chain condition used by `Rockafellar.lean`.

Reason:

- `CyclicMonotone.lean` now produces finite-cycle inequalities on `Γ`, indexed by `Fin (n + 1)`;
- `Rockafellar.lean` currently consumes the list-based predicate
  `PairingClosedChainMonotone Γ`;
- this is the only remaining interface gap between the optimality layer and the proper Rockafellar
  containment theorem.

Likely route:

- start from a nonempty list `l = [p₀, …, pₙ]` with all points in `Γ` and root `base = p₀`;
- remove immediate repetitions if necessary, or prove directly that duplicates can be discarded
  without increasing the closed-chain Rockafellar value;
- convert the resulting closed chain into a `Fin (n + 1)`-indexed cycle;
- apply pairing cyclical monotonicity to obtain
  `rockafellarChainValue l base.1 ≤ 0`.

The output of this step should be the theorem that lets

- `pairing_support_of_optimal_quadratic`

feed directly into

- `subset_ProperSubgradientGraph_properRockafellarPotential_of_pairingClosedChainMonotone`.

## Step 5. Final assembly in Brenier.lean

File:

- `OptimalTransport/Brenier.lean`

Combine:

- Step 4: optimality gives pairing cyclical monotonicity of the support for quadratic cost;
- Step 5A: convert that cycle inequality into `PairingClosedChainMonotone` for the support;
- Step 3: closed-chain monotonicity gives support inclusion in the proper subgradient graph of the
  proper Rockafellar potential;
- Step 1: that potential is measurable;
- existing proper-convex Brenier bridge: support inclusion implies graph concentration.

Target theorem:

- the actual classical Brenier statement for quadratic cost and absolutely continuous source
  measure, with no `HasRockafellarBound` assumption.

## Step 6. Remove compatibility scaffolding

Once the final theorem is in place:

- delete or deprecate `Coupling.HasRockafellarBound`;
- keep the old bounded real-valued theorems only as compatibility corollaries, or remove them if
  they no longer add value;
- update `GUIDE.tex`, `guide.tex`, and `FIX.md`.

## Recommended execution order

1. Prove pointwise finiteness on a pairing-cyclically monotone set.
2. Upgrade this to full proper Rockafellar containment.
3. Prove measurability of `properRockafellarPotential`.
4. Finish optimality implies cyclical monotonicity in `CyclicMonotone.lean`.
5. Prove `CCyclicallyMonotone -> PairingClosedChainMonotone`.
6. Assemble the classical Brenier theorem in `Brenier.lean`.

## Immediate next theorem

The highest-leverage next result is:

- `CCyclicallyMonotone (fun x y => -⟪x, y⟫) Γ -> PairingClosedChainMonotone Γ`.

Once that is proved, Step 5 should be mostly assembly.
