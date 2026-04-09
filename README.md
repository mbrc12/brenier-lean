# OptimalTransport

A formalization of **Brenier's theorem** for quadratic optimal transport in Lean 4.

## Main result

Let $E$ be a finite-dimensional real inner product space with Borel σ-algebra and additive Haar measure $m$, let $\kappa > 0$, and let $\mu, \nu$ be probability measures on $E$ with $\mu \ll m$. If $\pi$ is a coupling of $\mu$ and $\nu$ that minimizes the quadratic transport cost $\kappa\|x - y\|^2$, then there exists a proper convex potential $\Phi : E \to [-\infty, +\infty]$ such that:

1. $\Phi$ is proper convex and measurable,
2. $\pi = \mathrm{graph}_\mu(\nabla \varphi)$, where $\varphi$ is the real-valued representative of $\Phi$ on its effective domain,
3. $\nu = (\nabla\varphi)_\sharp\,\mu$,
4. $\mathrm{supp}(\pi) \subseteq \partial\Phi$ (the subdifferential graph of $\Phi$).

In words: an optimal coupling for the quadratic cost with absolutely continuous source measure is uniquely determined by the gradient of a proper convex function, simultaneously giving the Monge map $\nabla\varphi$ and the pushforward identity $\nu = (\nabla\varphi)_\sharp\mu$.

The Lean 4 signature of the main theorem is as follows. `WithTop` and `untopD` are used to handle the extended real-valued nature of the convex potential, and `IsProperConvex` encodes the proper convexity condition. The `graph` construction encodes the transport plan concentrated on the graph of the gradient map, and the support inclusion ensures the plan is concentrated on the subgradient graph of the potential.

We include short comments (lines starting with `--`) for a guide on how to read this statement. Here
`quadraticCost κ` denotes the cost function $\kappa\|x - y\|^2$.

```lean4
theorem exists_properConvex_potential_of_optimal_quadratic
    -- π is a coupling of μ and ν, and κ > 0 (hκ is a proof of that)
    (π : Coupling μ ν) {κ : ℝ} (hκ : 0 < κ)
    -- hopt is the proof that π is optimal among all couplings of μ and ν for the quadratic cost
    -- which is written by saying that transportCost of any other coupling ρ is at least as large as that of π
    (hopt : ∀ ρ : Coupling μ ν,
      transportCost (quadraticCost κ) π.toTransportPlan ≤
        transportCost (quadraticCost κ) ρ.toTransportPlan)
    -- hπ is the integrability condition that the quadratic cost is integrable with respect to π
    (hπ : Integrable (fun z : E × E ↦ quadraticCost κ z.1 z.2)
      (π.toTransportPlan : Measure (E × E)))
    -- hμ_ac is the absolute continuity condition that μ is absolutely continuous with respect to the Haar measure m on E
    (hμ_ac : (μ : Measure E) ≪ m) :
    -- If all of the above is provided, then this theorem outputs the following
    -- There is a Φ : E -> ℝ + {+∞} (encoded as WithTop ℝ) such that
    ∃ Φ : E → WithTop ℝ,
    -- Φ is proper convex
      IsProperConvex Φ ∧
    -- Φ is measurable
      Measurable Φ ∧
    -- Such that the transport plan π is the graph of the gradient of Φ, and the gradient is measurable
      π.toTransportPlan =
        TransportPlan.graph μ (gradient fun x => (Φ x).untopD 0)
          (measurable_gradient fun x => (Φ x).untopD 0) ∧
    -- And the pushforward of μ by the gradient map is ν
      ν = μ.map (measurable_gradient fun x => (Φ x).untopD 0).aemeasurable ∧
    -- And the support of π is contained in the proper subgradient graph of Φ
      ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
        ProperSubgradientGraph Φ
```

## Proof outline

The proof chains together several ingredients:

- **Optimality → cyclical monotonicity:** A finite-cycle perturbation argument shows the support of an optimal plan is $c$-cyclically monotone (via local rectangles, a competitor coupling, and a cost-drop estimate).
- **Cyclical monotonicity → Rockafellar potential:** A pairing-cyclically-monotone set is contained in the proper subgradient graph of a proper convex potential constructed as a supremum of affine chain functionals.
- **Subgradient inclusion → gradient map:** Absolute continuity ensures almost every source point lies in the interior of the effective domain, where the convex potential is differentiable and subgradients coincide with the gradient.

## File structure

| File | Content |
|------|---------|
| `Coupling.lean` | Transport plans, marginals, graph plans, couplings |
| `Cost.lean` | Transport costs, quadratic cost, finite second moments |
| `Existence.lean` | Prokhorov compactness, existence of optimal couplings |
| `CyclicMonotone.lean` | Cyclical monotonicity, perturbation competitor, optimality → $c$-cyclical monotonicity |
| `Subgradient.lean` | Subgradient algebra, pairing inequality, subgradient graphs are $c$-cyclically monotone |
| `ProperConvex.lean` | Proper convex potentials, effective domains, localized subgradients, affine perturbations |
| `Rockafellar.lean` | Rockafellar chain potentials, proper convex potential from cyclical monotonicity |
| `ConvexAE.lean` | Convex functions are differentiable a.e.; subgradients equal gradients at differentiability points |
| `Brenier.lean` | Graph concentration, proper-subgradient collapse, Brenier's theorem |
