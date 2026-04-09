# Optimal Transport: Brenier's Theorem in Lean 4

A formalization of **Brenier's theorem** for quadratic optimal transport in Lean 4.

## Main result

Let $E$ be a finite-dimensional real inner product space with Borel σ-algebra and additive Haar measure $m$, let $\kappa > 0$, and let $\mu, \nu$ be probability measures on $E$ with $\mu \ll m$. If $\pi$ is a coupling of $\mu$ and $\nu$ that minimizes the quadratic transport cost $\kappa\|x - y\|^2$, then there exists a proper convex potential $\Phi : E \to \WithTop{\mathbb{R}}$ such that:

1. $\Phi$ is proper convex and measurable,
2. $\pi = \mathrm{graph}_\mu(\nabla \Phi^\star)$, where $\Phi^\star(x) = (\Phi(x)).\mathrm{untopD}\;0$ is the real-valued representative,
3. $\nu = (\nabla \Phi^\star)_\sharp\,\mu$,
4. $\mathrm{supp}(\pi) \subseteq \partial\Phi$ (the subdifferential graph of $\Phi$).

In words: an optimal coupling for the quadratic cost with absolutely continuous source measure is uniquely determined by the gradient of a proper convex function, simultaneously giving the Monge map $\nabla\Phi^\star$ and the pushforward identity $\nu = (\nabla\Phi^\star)_\sharp\mu$.

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
