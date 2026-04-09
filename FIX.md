# Plan to Refactor Potentials to `ℝ ∪ {+∞}`

## Completion status (April 2026)

This migration is now completed in the repository.

Completed outcomes:

- The proper-convex layer is implemented in
  [ProperConvex.lean](/Users/subwave/dev/lean/OptimalTransport/OptimalTransport/ProperConvex.lean),
  with `ProperSubgradient`, `ProperSubgradientGraph`, and `EffectiveDomain`.
- Rockafellar has been migrated to the extended-real potential
  `properRockafellarPotential : E → WithTop ℝ` in
  [Rockafellar.lean](/Users/subwave/dev/lean/OptimalTransport/OptimalTransport/Rockafellar.lean),
  and the core containment theorem is proved in this setting.
- The finite-on-support replacement for the old boundedness bottleneck is implemented:
  cyclical monotonicity gives pointwise finiteness on the relevant source set, then global proper
  subgradient containment.
- The Brenier bridge is now proper-convex and no longer depends on
  `HasRockafellarBound`; the final quadratic endpoint is assembled in
  [Brenier.lean](/Users/subwave/dev/lean/OptimalTransport/OptimalTransport/Brenier.lean).
- The old `HasRockafellarBound` assumption is removed from active code paths.

Residual compatibility lemmas with stronger finite-everywhere assumptions are intentionally kept as
auxiliary corollaries, but they are no longer required for the main theorem pipeline.

This note describes how to remove the current `HasRockafellarBound` bottleneck by moving the
Rockafellar/Brenier potential layer from real-valued convex functions
`φ : E → ℝ` to proper extended-real-valued convex functions
`φ : E → ℝ ∪ {+∞}`.

In Lean, the most practical target is likely `WithTop ℝ` rather than a bespoke type. Mathematically,
the intended codomain is `ℝ ∪ {+∞}`.

## Goal

Replace the current route

- build `φ : E → ℝ` directly by a pointwise `sSup`,
- assume `HasRockafellarBound` to guarantee finiteness,
- use the real-valued convex/differentiability API,

by the proper-convex route

- build `Φ : E → ℝ ∪ {+∞}` without any global boundedness hypothesis,
- prove Rockafellar containment for `Φ`,
- prove `Φ(x) < +∞` on the part of the domain relevant to Brenier,
- extract a real-valued convex representative there,
- then reuse the existing a.e.-differentiability and graph-plan machinery.

## High-level strategy

There are really two layers to separate:

1. `Proper convex analysis`:
   work with `Φ : E → ℝ ∪ {+∞}` and prove the Rockafellar theorem in that setting.

2. `Brenier extraction`:
   show that in the quadratic optimal-transport setting, the proper convex potential is finite
   `μ`-a.e., hence yields a genuine real-valued convex function on the source side.

This is the clean mathematical split. The current code mixes those two layers by forcing finiteness
 too early.

## File-by-file refactor plan

### 1. Add a new proper-convex layer

Create a new file, likely

- `OptimalTransport/ProperConvex.lean`

This file should introduce the basic API for functions

- `Φ : E → WithTop ℝ`

with the intended mathematical meaning `E → ℝ ∪ {+∞}`.

Definitions to add:

- `IsProperConvex Φ`
- `ProperSubgradient Φ x y`
- `ProperSubgradientGraph Φ`
- `EffectiveDomain Φ := {x | Φ x < ⊤}`

Basic lemmas to add:

- affine perturbation rules for `ProperSubgradient`
- scaling rules by positive real scalars
- restriction from `WithTop ℝ` to `ℝ` on `EffectiveDomain`
- if `Φ x`, `Φ z` are finite and `y ∈ ∂Φ(x)`, then the subgradient inequality can be rewritten in
  real form

This layer should be intentionally small. It only needs the operations used later in Rockafellar and
 Brenier.

### 2. Refactor Rockafellar to an extended-real potential

Refactor

- [Rockafellar.lean](/Users/subwave/dev/lean/OptimalTransport/OptimalTransport/Rockafellar.lean)

so that the main construction is no longer

- `rockafellarPotential : E → ℝ`

but rather something like

- `properRockafellarPotential : E → WithTop ℝ`

Construction plan:

- keep `rockafellarChainValue` real-valued
- define the proper potential as the supremum of those real chain values, viewed inside `WithTop ℝ`
- remove the global boundedness hypothesis from the definition

Needed theorems:

- `Γ ⊆ ProperSubgradientGraph Φ_Γ`
- proper convexity of `Φ_Γ`

Recommended proof of convexity:

- use the epigraph characterization
- show
  `epi Φ_Γ = ⋂_{l} epi(A_l)`
  where each `A_l` is the affine chain functional
- each `epi(A_l)` is convex
- arbitrary intersections of convex sets are convex

This is the mathematically natural route and avoids any direct `sSup` manipulation in the codomain.

### 3. Keep a temporary real-valued wrapper as a compatibility layer

Once the proper potential exists, add a compatibility wrapper in `Rockafellar.lean` or
`ProperConvex.lean`:

- if `Φ` is finite everywhere, define `toRealPotential : E → ℝ`
- prove that its ordinary subgradient graph agrees with the proper one

This lets the current real-valued API continue working while the rest of the repository is migrated.

## Brenier-side extraction plan

### 4. Prove finiteness on the relevant source set

The Brenier argument does not need `Φ < ⊤` everywhere. It only needs finiteness where the first
 marginal `μ` lives.

So after the proper Rockafellar theorem is in place, add a theorem in

- `OptimalTransport/Brenier.lean`

of the form:

- if `π` is an optimal quadratic coupling and
  `support π ⊆ ProperSubgradientGraph Φ`,
  then `Φ(x) < ⊤` for `μ`-a.e. `x`

or slightly more concretely:

- `Φ` is finite on the projection of `support π` to the source space

This is the theorem that should replace the current `HasRockafellarBound`.

There are two plausible routes:

1. derive local finiteness from the support/subgradient inequality directly;
2. normalize `Φ` at one source point and use quadratic-cost structure to show the values along the
   relevant support remain finite.

The first route is preferable if it can be made clean.

### 5. Extract an honest real-valued convex function on the source side

Once finiteness `μ`-a.e. is known, define a real-valued representative on the effective domain:

- `φ x := (Φ x).untopD 0` or a more careful restricted-domain construction

Then prove:

- `φ` is convex on the set where `Φ` is finite
- on that set, proper subgradients for `Φ` become ordinary subgradients for `φ`

At this stage there are two implementation options:

1. prove a localized a.e.-differentiability theorem directly on the effective domain;
2. show that in the Brenier setting the effective domain contains the relevant convex region, then
   use the existing global real-valued theorem.

Option 2 is likely shorter if the effective domain geometry is manageable.

## Downstream migration plan

### 6. Generalize the current Milestone 6 bridge

Refactor

- [Brenier.lean](/Users/subwave/dev/lean/OptimalTransport/OptimalTransport/Brenier.lean)

so that the current theorem

- support in `SubgradientGraph φ`
- `μ ≪ volume`
- conclude graph concentration on `gradient φ`

is replaced by:

- support in `ProperSubgradientGraph Φ`
- `Φ` finite `μ`-a.e.
- the real representative `φ` agrees with `Φ` on that set
- conclude graph concentration on `gradient φ`

The measure-theoretic graph-plan lemmas already in `Brenier.lean` should remain unchanged.

### 7. Delete `HasRockafellarBound`

Once the new proper-convex path is complete:

- remove `Coupling.HasRockafellarBound`
- replace the current final theorem by the actual Brenier theorem statement
- update `guide.tex`, `issue.tex`, and `PLAN.md`

## Suggested theorem sequence

The shortest safe implementation order is:

1. `ProperSubgradient`, `ProperSubgradientGraph`, `EffectiveDomain`
2. proper affine/subgradient algebra
3. proper Rockafellar potential definition
4. convexity of the proper Rockafellar potential via epigraphs
5. proper Rockafellar containment theorem
6. finiteness-on-support theorem in the quadratic OT setting
7. bridge from proper subgradients to ordinary subgradients on the finite locus
8. reuse `ConvexAE` to get gradients a.e.
9. replace the current final theorem in `Brenier.lean`

## Risks and design choices

### Codomain choice

Most likely Lean choice:

- `WithTop ℝ`

Mathematical meaning:

- `ℝ ∪ {+∞}`

Avoid introducing `-∞`. The Brenier/Rockafellar potential should be proper convex, not an arbitrary
 extended-real function.

### Convexity API

The existing `ConvexOn` API is written for ordered additive codomains with scalar action. It may or
 may not fit `WithTop ℝ` comfortably for every theorem we want.

So the plan should not assume the entire existing convex-function API ports unchanged.
If needed:

- define convexity of `Φ` via epigraphs directly
- only translate back to `ConvexOn` after restricting to the finite locus

That is safer than fighting typeclass issues across the whole file.

### Differentiability API

The existing Rademacher-based theorems are for `φ : E → ℝ`.
They should remain so.

The proper-convex layer should therefore stop before differentiability, and the Brenier layer should
 convert back to a real-valued convex function before invoking `ConvexAE`.

## Deliverable

After this refactor, the intended final theorem should be:

- if `μ`, `ν` are probability measures on `EuclideanSpace ℝ (Fin n)`,
- `μ` has finite second moment,
- `ν` has finite second moment,
- `μ ≪ volume`,
- `π` is an optimal coupling for `κ * ‖x - y‖^2`,

then there exists a convex real-valued `φ` such that

- `π = (id, gradient φ)#μ`
- `(gradient φ)#μ = ν`
- the graph plan of `gradient φ` is optimal

with no extra `HasRockafellarBound` hypothesis.
