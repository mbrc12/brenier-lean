# Plan for Formalizing Optimal Transport up to Brenier's Theorem

This plan is for the repository as currently pinned to `lean4 v4.29.0` and `mathlib4 v4.29.0`
(`mathlib` rev `8a178386ffc0f5fef0b77738bb5449d50efeea95`).

## Current mathlib situation

Useful infrastructure already exists:

- `MeasureTheory.ProbabilityMeasure`, weak convergence, Portmanteau, and the Lévy-Prokhorov metric.
- `MeasureTheory.Measure.Prokhorov`: compactness of probability measures on compact spaces and
  Prokhorov compactness for tight families.
- `PolishSpace`, `StandardBorelSpace`, kernels, and disintegration.
- Finite-dimensional Euclidean spaces, convexity, strong convexity, differentiability, and
  measurable derivative APIs.

What does not seem to exist yet in a form directly usable for optimal transport:

- No OT API: couplings, transport plans, transport costs, Wasserstein distances, Monge/Kantorovich
  problems.
- No ready-made convex-analysis stack for subgradients, convex conjugates, or cyclic monotonicity.
- No ready-made theorem of the form "convex functions on `R^n` are differentiable almost
  everywhere", which is the main analytic input for Brenier.

So the project should split into two coordinated tracks:

1. A measure-theoretic track up to existence of optimal plans.
2. A convex-analysis track up to "optimal plans are induced by gradients of convex functions".

## Overall strategy

The repository should not hardwire a single cost too early. The better split is:

1. Develop a generic cost layer for existence theory in Polish spaces.
2. Develop a generic `c`-cyclical monotonicity layer.
3. Specialize only at the map-representation stage to a Brenier-friendly subclass of costs.

Following Villani, the generic existence theory should be built for:

- `X`, `Y` Polish spaces, equipped with their Borel sigma-algebras;
- `μ : ProbabilityMeasure X`, `ν : ProbabilityMeasure Y`;
- costs `c : X → Y → ℝ≥0∞`;
- `c` lower semicontinuous.

This is the right level of generality for the first real OT existence theorem:

- weak compactness comes from tightness plus Prokhorov, not from ambient compactness;
- the cost is always defined via `lintegral`, so no extra integrability side-condition is needed
  just to state the minimization problem;
- this includes the standard Villani setup for generic Kantorovich existence.

Only after this generic `ℝ≥0∞` layer is in place should we add a refined real-valued cost layer,
for example:

- `c : X → Y → ℝ` lower semicontinuous and bounded below by separable integrable terms;
- moment-controlled costs such as `‖x - y‖^2`.

For the Brenier branch, the key useful subclasses are:

- `c_κ(x,y) = κ * ‖x - y‖^2` with `κ > 0`;
- more generally, costs of the form `a x + b y - κ * ⟪x, y⟫`, since these have the same minimizers
  as `κ * ‖x - y‖^2` once the marginals are fixed.

Indeed,

`κ * ‖x - y‖^2 = κ * ‖x‖^2 + κ * ‖y‖^2 - 2κ * ⟪x, y⟫`,

so after fixing marginals the optimization problem is equivalent to maximizing the pairing
`⟪x,y⟫`. This is the structure needed for Rockafellar and convex potentials.

The standing topological assumption for the measure-theoretic track should therefore be:

- `X`, `Y` Polish spaces.

The first serious Brenier target should be:

- `X = EuclideanSpace ℝ (Fin n)` with `0 < n`.
- `μ ν : ProbabilityMeasure X`.
- finite second moments for `μ` and `ν`.
- `μ ≪ volume`.

Only after this version is in place should the project generalize to arbitrary finite-dimensional
real inner product spaces.

## Proposed file structure

- `OptimalTransport/Coupling.lean`
- `OptimalTransport/Cost.lean`
- `OptimalTransport/Existence.lean`
- `OptimalTransport/CyclicMonotone.lean`
- `OptimalTransport/CostSpecialized.lean`
- `OptimalTransport/Subgradient.lean`
- `OptimalTransport/Rockafellar.lean`
- `OptimalTransport/ConvexAE.lean`
- `OptimalTransport/Brenier.lean`

## Milestone 1: Basic OT objects

Define:

- `Coupling μ ν : Type` for `μ : ProbabilityMeasure X`, `ν : ProbabilityMeasure Y`.
- `TransportPlan X Y := ProbabilityMeasure (X × Y)`.
- `TransportPlan.fst`, `TransportPlan.snd`, and the fixed-marginal set/predicate.
- `GraphPlan μ T` for a measurable map `T : X → Y`.
- a generic Villani-style cost functional
  `TransportCost∞ c (π : TransportPlan X Y) := ∫⁻ z, c z.1 z.2 dπ`
  for `c : X → Y → ℝ≥0∞`.
- measurability and lower-semicontinuity hypotheses on costs in a reusable form.
- later, a real-valued refinement `TransportCost c π := ∫ z, c z.1 z.2 dπ`
  under explicit integrability hypotheses.
- `HasFiniteSecondMoment μ := ∫ x, ‖x‖^2 dμ < ∞`.
- specialized costs such as `QuadraticCost κ`.

Prove:

- `Coupling.nonempty` via `μ.prod ν`.
- marginal lemmas for product plans and graph plans.
- continuity/measurability of the marginal maps in the weak topology on probability measures,
  needed later for closedness of the coupling set.
- basic measurability lemmas for `TransportCost∞`, at least for lower semicontinuous and
  continuous costs.
- second-moment formulas for couplings:
  `∫ ‖x‖^2 dπ = ∫ ‖x‖^2 dμ` and similarly for `y`.
- integrability criteria turning moment bounds on marginals into finiteness of
  the real-valued `TransportCost c π` for important subclasses of `c`.

Deliverable:

- a clean base API in which later files can talk about couplings, supports, weak convergence, and
  both `ℝ≥0∞`-valued and real-valued costs without redefining the basic objects.

## Milestone 2: Existence of optimal couplings

Show that the set of couplings with fixed marginals is compact in the weak topology and that the
generic Villani cost functional attains its minimum.

Assume throughout:

- `X`, `Y` are Polish;
- `c : X → Y → ℝ≥0∞` is lower semicontinuous.

Needed theorems:

- the set `{π : ProbabilityMeasure (X × Y) | π.fst = μ ∧ π.snd = ν}` is closed.
- this set is tight, hence compact, using Prokhorov.
- lower semicontinuity of the cost functional under weak convergence for lower semicontinuous
  `ℝ≥0∞`-valued costs.

For compactness, the key lemma should be:

- if `π` is a coupling of `μ` and `ν`, and `K ⊆ X`, `L ⊆ Y` are compact, then
  `π ((K × L)ᶜ) ≤ μ (Kᶜ) + ν (Lᶜ)`;
- since probability measures on Polish spaces are tight, the family of all couplings of `μ` and
  `ν` is tight.

For the lower semicontinuity step, the preferred route is:

- define the generic cost as
  `TransportCost∞ c (π : TransportPlan X Y) := ∫⁻ z, c z.1 z.2 dπ`;
- prove lower semicontinuity for lower semicontinuous `ℝ≥0∞` costs using Portmanteau;
- only afterwards add bounded-continuous and real-valued corollaries as refinements.

Main theorem:

- `exists_optimalCoupling :
    ∃ π : Coupling μ ν, ∀ ρ : Coupling μ ν,
      TransportCost∞ c π.toTransportPlan ≤ TransportCost∞ c ρ.toTransportPlan`
  for lower semicontinuous `c : X → Y → ℝ≥0∞` on Polish spaces.

Refinements after the main theorem:

- bounded-continuous and real-valued corollaries;
- existence for real-valued lower semicontinuous costs bounded below by separable integrable terms;
- existence for quadratic costs under finite-moment assumptions.

## Milestone 3: Optimality implies cyclical monotonicity

Define:

- `CCyclicallyMonotone c (Γ : Set (X × Y))`.

First prove the direct perturbation theorem in the continuous real-valued branch:

- assume `c : X → Y → ℝ` is continuous;
- assume `π : Coupling μ ν` is optimal for `c` among couplings of `μ` and `ν`;
- assume `∫ z, c z.1 z.2 dπ < ∞`.

Then prove:

- `support π` is `c`-cyclically monotone.

This should be done directly from the optimality of `π`, by comparing `π` with finitely supported
competitors obtained from cyclic permutations. This avoids needing full Kantorovich duality on the
critical path.

The key local ingredient is now explicit:

- from a strict cycle gap and continuity of `c`, shrink to pairwise disjoint rectangles on which
  the cycle gap stays positive;
- simultaneously obtain a uniform local bound for `|c|` on the diagonal rectangles
  `Uᵢ × Vᵢ` and cyclic rectangles `Uᵢ × Vᵢ₊₁`;
- use these local bounds, together with the global hypothesis `∫ c dπ < ∞`, to show the perturbed
  competitor still has finite cost.

Only afterwards should this milestone be generalized, if needed, to broader real-valued cost
classes such as lower-semicontinuous costs bounded below by separable integrable terms.

Then add specialization lemmas for Brenier-friendly costs:

- for `c(x,y) = a x + b y - κ * ⟪x,y⟫`, `c`-cyclical monotonicity is equivalent to ordinary
  cyclical monotonicity for the pairing `⟪x,y⟫`;
- in particular this applies to `c_κ(x,y) = κ * ‖x - y‖^2` with `κ > 0`.

## Milestone 4: Subgradients and Rockafellar

Define:

- `Subgradient φ x y`.
- the graph `SubgradientGraph φ := {(x,y) | y ∈ ∂φ(x)}`.
- optionally `ConvexConjugate` if it simplifies later proofs.

This milestone should be split into smaller pieces.

### Milestone 4A: Basic subgradient API

Define and prove:

- `Subgradient φ x y` in a form adapted to finite-dimensional real vector spaces;
- `SubgradientGraph φ`;
- elementary closure properties of subgradients under addition of affine functions;
- the specialization for costs `a x + b y - κ * ⟪x, y⟫`.

Deliverable:

- a usable local API for statements of the form `y ∈ ∂φ(x)`.

### Milestone 4B: Subgradient graphs are cyclically monotone

Prove:

- if `φ` is convex, then `SubgradientGraph φ` is cyclically monotone;
- equivalently, for Brenier-friendly costs, the graph is `c`-cyclically monotone after the usual
  algebraic rewriting.

This is the easy direction and should come before any attempt at Rockafellar.

### Milestone 4C: Finite-cycle Rockafellar construction

Construct the Rockafellar potential attached to a cyclically monotone set `Γ ⊆ R^n × R^n`:

- define the candidate potential as a supremum over finite chains;
- prove each finite-chain functional is convex;
- prove the supremum is convex;
- prove the construction is normalized and monotone along the prescribed graph.

Deliverable:

- a concrete candidate `φ_Γ` together with its basic convexity properties.

### Milestone 4D: Global Rockafellar theorem

Prove:

- every cyclically monotone set in `R^n × R^n` is contained in `SubgradientGraph φ_Γ` for the
  potential built in Milestone 4C.

This is the first major gap relative to current `mathlib`. It will likely require a local library
for finite-dimensional convex analysis, and parts of it may be worth upstreaming.

## Milestone 5: Almost-everywhere differentiability of convex functions

Needed theorem:

- if `φ : X → ℝ` is convex on `X = EuclideanSpace ℝ (Fin n)`, then `φ` is differentiable
  `volume`-almost everywhere.

Then prove:

- at differentiability points, the subgradient is a singleton, equal to `fderiv`/gradient.
- the resulting gradient map is measurable.

This is probably the hardest missing analytic ingredient in the whole plan. Without it, one can
reach optimal plans and convex potentials, but not Brenier's map theorem.

## Milestone 6: From optimal plans to optimal maps

Assume:

- `μ ≪ volume`.
- `π` is an optimal coupling.
- `support π` is `c`-cyclically monotone for a Brenier-friendly cost `c`.

First specialize `c` so that `c`-cyclical monotonicity gives ordinary cyclical monotonicity for
the pairing and hence

- `support π ⊆ SubgradientGraph φ`

for some convex `φ`.

Prove:

- since convex `φ` is differentiable `volume`-a.e., it is differentiable `μ`-a.e.
- therefore `support π` is contained in the graph of `∇φ` for `μ`-a.e. `x`.
- any coupling with first marginal `μ` concentrated on the graph of a measurable map `T`
  is equal to `GraphPlan μ T`.

Main consequences:

- every optimal coupling is induced by a measurable map `T`.
- `T` is `μ`-a.e. equal to the gradient of a convex function.
- the optimal map is unique `μ`-a.e.

## Milestone 7: Brenier's theorem

Final target theorem, first in Euclidean finite dimension:

- if `μ` and `ν` are probability measures on `EuclideanSpace ℝ (Fin n)` with finite second moments
  and `μ ≪ volume`, then for every `κ > 0` there exists a convex function `φ` such that `∇φ`
  pushes `μ` to `ν`, and the graph plan of `∇φ` is the unique optimal coupling for the cost
  `κ * ‖x - y‖^2`, up to `μ`-a.e. equality of the map.

It is also natural to formulate the final theorem for the wider equivalent class of costs

- `c(x,y) = a x + b y - κ * ⟪x,y⟫`, `κ > 0`,

since these differ from the quadratic cost only by marginal terms and therefore have the same
optimal plans.

## Optional work not on the critical path

These are natural extensions, but they should come after Brenier:

- Kantorovich duality for lower semicontinuous costs.
- `Wasserstein` and especially `W₂` as an actual space/metric.
- stability of optimal plans under weak convergence plus moment bounds.
- displacement interpolation and McCann's theorem.
- uniqueness of convex potentials up to constants.
- extension from `EuclideanSpace ℝ (Fin n)` to arbitrary finite-dimensional real inner product
  spaces.

## Recommended implementation order

The shortest path to Brenier is:

1. couplings and generic transport costs;
2. existence of optimal couplings for a useful abstract class of costs;
3. continuous-cost cyclical monotonicity of optimal supports under a finite-cost hypothesis;
4. subgradient basics;
5. cyclic monotonicity of subgradient graphs;
6. Rockafellar construction and graph-containment theorem;
7. a.e. differentiability of convex functions;
8. specialization lemmas for the Brenier-friendly class `a x + b y - κ * ⟪x,y⟫`;
9. graph-concentration lemmas;
10. Brenier for `κ * ‖x - y‖^2`.

In other words, the project should not start with a full Wasserstein-space development. The
critical bottleneck is the finite-dimensional convex-analysis layer, not the abstract OT API.
