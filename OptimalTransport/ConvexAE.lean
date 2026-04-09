import OptimalTransport.ProperConvex
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

namespace OptimalTransport

open MeasureTheory Set
open scoped Gradient Topology

/-!
This file provides the analytic ingredients for the Brenier argument from Mathlib:

1. A convex real-valued function on a finite-dimensional real normed space is differentiable almost
   everywhere with respect to any additive Haar measure. The proof combines local Lipschitz
   continuity, compact exhaustion, and Rademacher's theorem.

2. A localized version for convex functions on open convex subsets, since the proper-convex
   Brenier bridge works on the interior of the effective domain.

3. At a differentiability point, any subgradient must coincide with the gradient — this is the
   uniqueness bridge from subgradient inclusion to gradient-map representation.

4. The gradient map of a real-valued function on a finite-dimensional inner product space is
   measurable.
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

/-- A convex real-valued function on an open convex set is differentiable almost everywhere on that
open set.

The proof is a localized version of `ConvexOn.ae_differentiableAt`. We exhaust the open set by the
compact sets

`Kₙ = closedBall 0 n ∩ {x | 1 / (n + 1) ≤ infDist x sᶜ}`.

Each `Kₙ` is compact and contained in `s`, so local Lipschitz continuity on `s` upgrades to a
global Lipschitz bound on `Kₙ`; Rademacher then gives differentiability almost everywhere on `Kₙ`.
The interiors of these compact sets cover `s`, thanks to the positive distance to the complement of
an open set. -/
theorem ConvexOn.ae_differentiableAt_of_isOpen {s : Set E} {f : E → ℝ}
    (hs : IsOpen s) (hf : ConvexOn ℝ s f) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableAt ℝ f x := by
  by_cases hsu : s = Set.univ
  · subst hsu
    filter_upwards [OptimalTransport.ConvexOn.ae_differentiableAt (μ := μ) hf] with x hx _
    exact hx
  have hscomp_nonempty : (sᶜ : Set E).Nonempty := by
    by_contra hsempty
    apply hsu
    ext x
    by_cases hx : x ∈ s
    · simp [hx]
    · exfalso
      exact hsempty ⟨x, hx⟩
  let K : ℕ → Set E := fun n =>
    Metric.closedBall (0 : E) n ∩ {x | (1 : ℝ) / (n + 1 : ℝ) ≤ Metric.infDist x sᶜ}
  have hK_compact : ∀ n : ℕ, IsCompact (K n) := by
    intro n
    have hclosed_inf :
        IsClosed {x : E | (1 : ℝ) / (n + 1 : ℝ) ≤ Metric.infDist x sᶜ} :=
      isClosed_le continuous_const (Metric.continuous_infDist_pt (sᶜ : Set E))
    exact (isCompact_closedBall (0 : E) n).inter_right hclosed_inf
  have hK_subset : ∀ n : ℕ, K n ⊆ s := by
    intro n x hx
    have hpos : 0 < Metric.infDist x sᶜ := by
      have hfrac_pos : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
      exact lt_of_lt_of_le hfrac_pos hx.2
    rw [← hs.isClosed_compl.notMem_iff_infDist_pos hscomp_nonempty] at hpos
    simpa using hpos
  have hloc : LocallyLipschitzOn s f := hf.locallyLipschitzOn hs
  have hpiece :
      ∀ n : ℕ, ∀ᵐ x ∂μ, x ∈ interior (K n) → DifferentiableAt ℝ f x := by
    intro n
    have hlocK : LocallyLipschitzOn (K n) f := hloc.mono (hK_subset n)
    obtain ⟨C, hC⟩ := hlocK.exists_lipschitzOnWith_of_compact (hK_compact n)
    have hrad :
        ∀ᵐ x ∂μ, x ∈ K n → DifferentiableWithinAt ℝ f (K n) x :=
      hC.ae_differentiableWithinAt_of_mem (μ := μ)
    filter_upwards [hrad] with x hx hxint
    have hK_nhds : K n ∈ 𝓝 x := by
      exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hxint) interior_subset
    exact (hx (interior_subset hxint)).differentiableAt
      hK_nhds
  have hall :
      ∀ᵐ x ∂μ, ∀ n : ℕ, x ∈ interior (K n) → DifferentiableAt ℝ f x := by
    rw [ae_all_iff]
    intro n
    exact hpiece n
  filter_upwards [hall] with x hx hxs
  have hdist_pos : 0 < Metric.infDist x sᶜ := by
    rw [← hs.isClosed_compl.notMem_iff_infDist_pos hscomp_nonempty]
    simpa using hxs
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt ‖x‖
  obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt hdist_pos
  let n : ℕ := max N₁ N₂ + 1
  have hn_norm : ‖x‖ < n := by
    have hmax_lt : (max N₁ N₂ : ℝ) < n := by
      exact_mod_cast Nat.lt_succ_self (max N₁ N₂)
    calc
      ‖x‖ < N₁ := hN₁
      _ ≤ max N₁ N₂ := by exact_mod_cast Nat.le_max_left N₁ N₂
      _ < n := by simpa using hmax_lt
  have hn_inf : (1 : ℝ) / (n + 1 : ℝ) < Metric.infDist x sᶜ := by
    have hlt_nat : N₂ + 1 < n + 1 := by
      dsimp [n]
      omega
    have hlt_cast : (N₂ + 1 : ℝ) < n + 1 := by exact_mod_cast hlt_nat
    have hone_div :
        (1 : ℝ) / (n + 1 : ℝ) < (1 : ℝ) / (N₂ + 1 : ℝ) :=
      one_div_lt_one_div_of_lt (by positivity) hlt_cast
    exact hone_div.trans hN₂
  have hxcover : x ∈ interior (K n) := by
    have hball : x ∈ Metric.ball (0 : E) n := by
      simpa [Metric.mem_ball, dist_eq_norm] using hn_norm
    have hdist_open : x ∈ {z : E | (1 : ℝ) / (n + 1 : ℝ) < Metric.infDist z sᶜ} := hn_inf
    have hopen :
        IsOpen (Metric.ball (0 : E) n ∩
          {z : E | (1 : ℝ) / (n + 1 : ℝ) < Metric.infDist z sᶜ}) :=
      IsOpen.inter Metric.isOpen_ball
        (isOpen_lt continuous_const (Metric.continuous_infDist_pt (sᶜ : Set E)))
    have hsubset :
        Metric.ball (0 : E) n ∩
          {z : E | (1 : ℝ) / (n + 1 : ℝ) < Metric.infDist z sᶜ} ⊆ K n := by
      intro z hz
      constructor
      · exact Metric.mem_closedBall.2 (le_of_lt hz.1)
      · have hzinf : (1 : ℝ) / (n + 1 : ℝ) < Metric.infDist z sᶜ := by
          simpa using hz.2
        exact le_of_lt hzinf
    exact mem_interior_iff_mem_nhds.2 <|
      Filter.mem_of_superset (hopen.mem_nhds ⟨hball, hdist_open⟩) hsubset
  exact hx n hxcover

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

omit [MeasurableSpace E] [BorelSpace E] in
/-- Localized version of `Subgradient.eq_gradient_of_hasGradientAt`.

If `x` lies in the interior of a set `s`, then a localized supporting-hyperplane inequality on `s`
already determines the ambient gradient at `x`. The proof is the same one-dimensional local-minimum
argument as in the global case, using interior membership to ensure that the line
`t ↦ x + t • u` stays inside `s` for small `t`. -/
theorem SubgradientOn.eq_gradient_of_hasGradientAt_of_mem_interior
    {s : Set E} {φ : E → ℝ} {x y g : E}
    (hy : SubgradientOn s φ x y) (hx : x ∈ interior s) (hg : HasGradientAt φ g x) :
    y = g := by
  apply ext_inner_right ℝ
  intro u
  let ψ : ℝ → ℝ := fun t ↦ φ (x + t • u) - (φ x + t * inner ℝ y u)
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
  have hs_near : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • u ∈ s := by
    exact hline.continuousAt.tendsto.eventually (by simpa using mem_interior_iff_mem_nhds.mp hx)
  have hψ_min : IsLocalMin ψ 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), ψ 0 ≤ ψ t
    filter_upwards [hs_near] with t hts
    have hsub' : φ x + t * inner ℝ y u ≤ φ (x + t • u) := by
      simpa [sub_eq_add_neg, real_inner_smul_right, add_assoc, add_left_comm, add_comm] using
        hy.2 hts
    have hnonneg : 0 ≤ ψ t := by
      dsimp [ψ]
      linarith
    simpa [ψ]
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

/-- On an open convex set, a convex function admits a gradient almost everywhere on that set. -/
theorem ConvexOn.ae_hasGradientAt_of_isOpen {s : Set E} {f : E → ℝ}
    (hs : IsOpen s) (hf : ConvexOn ℝ s f) :
    ∀ᵐ x ∂μ, x ∈ s → HasGradientAt f (gradient f x) x := by
  filter_upwards [OptimalTransport.ConvexOn.ae_differentiableAt_of_isOpen
      (μ := μ) hs hf] with x hx hxs
  exact (hx hxs).hasGradientAt

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
