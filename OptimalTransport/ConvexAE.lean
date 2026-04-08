import OptimalTransport.Subgradient
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

namespace OptimalTransport

open MeasureTheory Set
open scoped Gradient Topology

/-!
This file packages the analytic ingredient from Milestone 5 that is already available in
`mathlib`: convex real-valued functions on finite-dimensional real normed spaces are locally
Lipschitz, hence differentiable almost everywhere by Rademacher's theorem.

For the OT roadmap, the main output is the Euclidean statement needed later for Brenier:

* a convex function on `EuclideanSpace ℝ (Fin n)` is differentiable `volume`-almost everywhere;
* its gradient map is measurable.

This file also contains the uniqueness bridge needed later in the map-representation argument:
once a convex potential is differentiable at `x`, any subgradient at `x` must coincide with the
actual gradient there.
-/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [MeasureTheory.Measure.IsAddHaarMeasure μ]

/-- A convex real-valued function on a finite-dimensional real normed space is differentiable
`volume`-almost everywhere.

The proof is standard:

1. convexity on `univ` gives local Lipschitz continuity;
2. on each compact closed ball, local Lipschitz continuity upgrades to a global Lipschitz bound;
3. Rademacher gives almost-everywhere differentiability on each such ball;
4. the countable cover by balls yields the global almost-everywhere statement. -/
theorem ConvexOn.ae_differentiableAt {f : E → ℝ} (hf : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  have hloc : LocallyLipschitz f := hf.locallyLipschitz
  have hball :
      ∀ n : ℕ, ∀ᵐ x ∂μ, x ∈ Metric.ball (0 : E) (n + 1) → DifferentiableAt ℝ f x := by
    intro n
    let K : Set E := Metric.closedBall (0 : E) (n + 1)
    have hK_compact : IsCompact K := isCompact_closedBall _ _
    obtain ⟨C, hC⟩ :=
      (hloc.locallyLipschitzOn (s := K)).exists_lipschitzOnWith_of_compact hK_compact
    have hrad :
        ∀ᵐ x ∂(μ.restrict K), DifferentiableWithinAt ℝ f K x :=
      hC.ae_differentiableWithinAt (μ := μ) measurableSet_closedBall
    rw [ae_restrict_iff' measurableSet_closedBall] at hrad
    filter_upwards [hrad] with x hx hxball
    have hxK : x ∈ K := Metric.mem_closedBall.2 (le_of_lt hxball)
    exact (hx hxK).differentiableAt (Metric.closedBall_mem_nhds_of_mem hxball)
  have hall :
      ∀ᵐ x ∂μ, ∀ n : ℕ, x ∈ Metric.ball (0 : E) (n + 1) → DifferentiableAt ℝ f x := by
    rw [ae_all_iff]
    intro n
    exact hball n
  filter_upwards [hall] with x hx
  have hxcover : x ∈ ⋃ n : ℕ, Metric.ball (0 : E) (n + 1) := by
    simp [Metric.iUnion_ball_nat_succ]
  rcases mem_iUnion.1 hxcover with ⟨n, hxn⟩
  exact hx n hxn

end FiniteDimensional

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [MeasureTheory.Measure.IsAddHaarMeasure μ]

omit [MeasurableSpace E] [BorelSpace E] in
/-- At a differentiability point, a subgradient must coincide with the gradient.

The proof reduces the multidimensional statement to a one-dimensional local-minimum argument.
For a fixed direction `u`, the subgradient inequality says that the function

`t ↦ φ (x + t • u) - (φ x + t * ⟪y, u⟫)`

is globally nonnegative, hence has a local minimum at `0`. Differentiability of `φ` at `x`
identifies the derivative of this function at `0` as `⟪∇φ x - y, u⟫`, so Fermat's theorem gives
`⟪∇φ x - y, u⟫ = 0`. Since this holds for every `u`, the two vectors are equal. -/
theorem Subgradient.eq_gradient_of_hasGradientAt {φ : E → ℝ} {x y g : E}
    (hy : Subgradient φ x y) (hg : HasGradientAt φ g x) :
    y = g := by
  apply ext_inner_right ℝ
  intro u
  let ψ : ℝ → ℝ := fun t ↦ φ (x + t • u) - (φ x + t * inner ℝ y u)
  have hψ_min : IsLocalMin ψ 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), ψ 0 ≤ ψ t
    filter_upwards with t
    have hsub := hy (x + t • u)
    have hsub' : φ x + t * inner ℝ y u ≤ φ (x + t • u) := by
      simpa [sub_eq_add_neg, real_inner_smul_right, add_assoc, add_left_comm, add_comm] using hsub
    have hnonneg : 0 ≤ ψ t := by
      dsimp [ψ]
      linarith
    simpa [ψ]
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
  have hcomp : HasDerivAt (fun t : ℝ ↦ φ (x + t • u)) (inner ℝ g u) 0 := by
    have hcomp' :
        HasDerivAt ((fun z : E ↦ φ z) ∘ fun t : ℝ ↦ x + t • u)
          (((InnerProductSpace.toDual ℝ E) g) u) 0 := by
      exact HasFDerivAt.comp_hasDerivAt_of_eq (x := 0) (y := x)
        (hl := hg.hasFDerivAt) (hf := hline) (by simp)
    simpa using hcomp'
  have haff : HasDerivAt (fun t : ℝ ↦ φ x + t * inner ℝ y u) (inner ℝ y u) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (inner ℝ y u)).const_add (φ x)
  have hψ_deriv : HasDerivAt ψ (inner ℝ g u - inner ℝ y u) 0 := by
    exact hcomp.sub haff
  have hzero : inner ℝ g u - inner ℝ y u = 0 := hψ_min.hasDerivAt_eq_zero hψ_deriv
  linarith

/-- The gradient map of a real-valued function on a finite-dimensional real inner product space is
measurable. This is a direct corollary of the measurability of `fderiv` in `mathlib` and the
continuous Riesz identification between vectors and continuous linear functionals. -/
theorem measurable_gradient (f : E → ℝ) : Measurable (gradient f) := by
  simpa [gradient] using
    ((InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv (𝕜 := ℝ) (f := f)))

/-- A convex real-valued function on a finite-dimensional real inner product space admits a
gradient `μ`-almost everywhere for any additive Haar measure `μ`. -/
theorem ConvexOn.ae_hasGradientAt {f : E → ℝ} (hf : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂μ, HasGradientAt f (gradient f x) x := by
  filter_upwards [OptimalTransport.ConvexOn.ae_differentiableAt (μ := μ) hf] with x hx
  exact hx.hasGradientAt

end InnerProduct

section Euclidean

variable {n : ℕ}

/-- Euclidean specialization of `ConvexOn.ae_differentiableAt`, stated in the form needed for the
later Brenier development. -/
theorem ConvexOn.ae_differentiableAt_euclidean
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ f x :=
  OptimalTransport.ConvexOn.ae_differentiableAt
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hf

end Euclidean

end OptimalTransport
