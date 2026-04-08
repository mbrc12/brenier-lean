import OptimalTransport.Coupling
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

namespace OptimalTransport

open MeasureTheory
open scoped ENNReal NNReal

/-!
This file adds the first layer of analytic structure on top of transport plans.

The main definitions are:

* `transportCostENNReal c π`: the generic Villani-style cost, valued in `ℝ≥0∞`;
* `transportCost c π`: the integral of a cost function `c` against a transport plan `π`;
* `HasFiniteSecondMoment μ`: integrability of `x ↦ ‖x‖^2` against a probability measure `μ`.

The main lemmas show that:

* lower semicontinuous and continuous costs on `X × Y` can be packaged as reusable hypotheses;
* square norms pulled back from the first or second factor are measurable and integrable;
* integrating `‖x‖^2` against a coupling gives the same value as integrating against the
  corresponding marginal;
* finite second moments on the marginals imply integrability of the quadratic cost.
-/

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The generic Villani-style transport cost of a plan against an `ℝ≥0∞`-valued cost. -/
noncomputable def transportCostENNReal (c : X → Y → ℝ≥0∞) (π : TransportPlan X Y) : ℝ≥0∞ :=
  -- We integrate the nonnegative cost over the product space with respect to the plan `π`.
  ∫⁻ z, c z.1 z.2 ∂(π : Measure (X × Y))

/-- The transport cost of a plan against a real-valued cost function. -/
noncomputable def transportCost (c : X → Y → ℝ) (π : TransportPlan X Y) : ℝ :=
  -- We integrate the cost over the product space with respect to the plan `π`.
  ∫ z, c z.1 z.2 ∂(π : Measure (X × Y))

section CostAssumptions

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- A cost is lower semicontinuous when viewed as a function on the product space. -/
def IsLowerSemicontinuousCost (c : X → Y → ℝ≥0∞) : Prop :=
  LowerSemicontinuous fun z : X × Y ↦ c z.1 z.2

/-- A cost is continuous when viewed as a function on the product space. -/
def IsContinuousCost (c : X → Y → ℝ≥0∞) : Prop :=
  Continuous fun z : X × Y ↦ c z.1 z.2

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- A continuous cost on the product space is automatically lower semicontinuous. This lets later
results assume only lower semicontinuity. -/
lemma isLowerSemicontinuousCost_of_isContinuousCost {c : X → Y → ℝ≥0∞}
    (hc : IsContinuousCost c) :
    IsLowerSemicontinuousCost c :=
  hc.lowerSemicontinuous

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- For a lower semicontinuous cost, every strict superlevel set is open. This is the topological
formulation used in Portmanteau-style arguments. -/
lemma isOpen_preimage_of_isLowerSemicontinuousCost {c : X → Y → ℝ≥0∞}
    (hc : IsLowerSemicontinuousCost c) (r : ℝ≥0∞) :
    IsOpen {z : X × Y | r < c z.1 z.2} := by
  -- Lower semicontinuity is equivalent to openness of all strict superlevel sets.
  simpa using hc.isOpen_preimage r

/-- A lower semicontinuous `ℝ≥0∞`-valued cost is measurable on the product space. -/
lemma measurable_of_isLowerSemicontinuousCost {c : X → Y → ℝ≥0∞}
    [OpensMeasurableSpace (X × Y)] (hc : IsLowerSemicontinuousCost c) :
    Measurable fun z : X × Y ↦ c z.1 z.2 := by
  -- Lower semicontinuous maps to `ℝ≥0∞` are measurable.
  exact hc.measurable

/-- The integrand of a lower semicontinuous `ℝ≥0∞`-valued cost is automatically a.e. measurable
with respect to any transport plan. -/
lemma aemeasurable_of_isLowerSemicontinuousCost {c : X → Y → ℝ≥0∞}
    [OpensMeasurableSpace (X × Y)] (hc : IsLowerSemicontinuousCost c)
    (π : TransportPlan X Y) :
    AEMeasurable (fun z : X × Y ↦ c z.1 z.2) (π : Measure (X × Y)) :=
  hc.measurable.aemeasurable

end CostAssumptions

section SecondMoment

/-- Finite second moment, expressed as integrability of `x ↦ ‖x‖^2`. -/
def HasFiniteSecondMoment [NormedAddCommGroup X] (μ : ProbabilityMeasure X) : Prop :=
  Integrable (fun x : X ↦ ‖x‖ ^ (2 : ℕ)) (μ : Measure X)

/-- The quadratic cost `κ * ‖x - y‖^2` on a normed additive group. -/
def quadraticCost [NormedAddCommGroup X] (κ : ℝ) (x y : X) : ℝ :=
  κ * ‖x - y‖ ^ (2 : ℕ)

/-- The square-norm integrand is a.e. strongly measurable with respect to any measure. This is the
basic measurability input for second-moment estimates. -/
lemma aestronglyMeasurable_norm_sq
    [NormedAddCommGroup X] [BorelSpace X] [OpensMeasurableSpace X] (μ : Measure X) :
    AEStronglyMeasurable (fun x : X ↦ ‖x‖ ^ (2 : ℕ)) μ := by
  -- The map `x ↦ ‖x‖^2` is continuous, hence strongly measurable, hence a.e. strongly measurable.
  exact (continuous_norm.pow 2).aestronglyMeasurable

/-- Pulling back the square norm along the first projection gives an a.e. strongly measurable
function on the product space. -/
lemma aestronglyMeasurable_norm_sq_left
    [NormedAddCommGroup X] [OpensMeasurableSpace X] (π : TransportPlan X Y) :
    AEStronglyMeasurable (fun z : X × Y ↦ ‖z.1‖ ^ (2 : ℕ)) (π : Measure (X × Y)) := by
  -- Compose the first projection with norm and squaring.
  exact ((measurable_fst.aemeasurable.norm.pow_const 2)).aestronglyMeasurable

/-- Pulling back the square norm along the second projection gives an a.e. strongly measurable
function on the product space. -/
lemma aestronglyMeasurable_norm_sq_right
    [NormedAddCommGroup Y] [OpensMeasurableSpace Y] (π : TransportPlan X Y) :
    AEStronglyMeasurable (fun z : X × Y ↦ ‖z.2‖ ^ (2 : ℕ)) (π : Measure (X × Y)) := by
  -- Compose the second projection with norm and squaring.
  exact ((measurable_snd.aemeasurable.norm.pow_const 2)).aestronglyMeasurable

/-- If the source marginal has finite second moment, then the square norm of the first coordinate
is integrable with respect to the whole coupling. -/
lemma integrable_norm_sq_fst_of_hasFiniteSecondMoment
    [NormedAddCommGroup X] [BorelSpace X] [OpensMeasurableSpace X]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (π : Coupling μ ν)
    (hμ : HasFiniteSecondMoment μ) :
    Integrable (fun z : X × Y ↦ ‖z.1‖ ^ (2 : ℕ)) (π.toTransportPlan : Measure (X × Y)) := by
  -- First rewrite the assumption using the fact that the first marginal of `π` is exactly `μ`.
  have hmap : Integrable (fun x : X ↦ ‖x‖ ^ (2 : ℕ))
      ((π.toTransportPlan.fst : ProbabilityMeasure X) : Measure X) := by
    simpa [Coupling.fst] using hμ
  -- Then use the standard integrability criterion for pullbacks along a measurable map.
  exact
    (integrable_map_measure
      (aestronglyMeasurable_norm_sq ((π.toTransportPlan.fst : ProbabilityMeasure X) : Measure X))
      measurable_fst.aemeasurable).mp hmap

/-- If the target marginal has finite second moment, then the square norm of the second coordinate
is integrable with respect to the whole coupling. -/
lemma integrable_norm_sq_snd_of_hasFiniteSecondMoment
    [NormedAddCommGroup Y] [BorelSpace Y] [OpensMeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (π : Coupling μ ν)
    (hν : HasFiniteSecondMoment ν) :
    Integrable (fun z : X × Y ↦ ‖z.2‖ ^ (2 : ℕ)) (π.toTransportPlan : Measure (X × Y)) := by
  -- Rewrite the target assumption using the second marginal of the coupling.
  have hmap : Integrable (fun y : Y ↦ ‖y‖ ^ (2 : ℕ))
      ((π.toTransportPlan.snd : ProbabilityMeasure Y) : Measure Y) := by
    simpa [Coupling.snd] using hν
  -- Pull integrability back through the second projection.
  exact
    (integrable_map_measure
      (aestronglyMeasurable_norm_sq ((π.toTransportPlan.snd : ProbabilityMeasure Y) : Measure Y))
      measurable_snd.aemeasurable).mp hmap

/-- Integrating `‖x‖^2` against a coupling equals integrating it against the first marginal. -/
lemma integral_norm_sq_fst
    [NormedAddCommGroup X] [BorelSpace X] [OpensMeasurableSpace X]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (π : Coupling μ ν) :
    ∫ z : X × Y, ‖z.1‖ ^ (2 : ℕ) ∂(π.toTransportPlan : Measure (X × Y)) =
      ∫ x : X, ‖x‖ ^ (2 : ℕ) ∂(μ : Measure X) := by
  calc
    -- Move the integral from the product space to the first marginal using `integral_map`.
    ∫ z : X × Y, ‖z.1‖ ^ (2 : ℕ) ∂(π.toTransportPlan : Measure (X × Y)) =
        ∫ x : X, ‖x‖ ^ (2 : ℕ) ∂((π.toTransportPlan.fst : ProbabilityMeasure X) : Measure X) := by
          symm
          exact
            integral_map measurable_fst.aemeasurable
              (aestronglyMeasurable_norm_sq
                ((π.toTransportPlan.fst : ProbabilityMeasure X) : Measure X))
    -- Then replace the first marginal by `μ`.
    _ = ∫ x : X, ‖x‖ ^ (2 : ℕ) ∂(μ : Measure X) := by
      exact congrArg
        (fun ρ : ProbabilityMeasure X => ∫ x : X, ‖x‖ ^ (2 : ℕ) ∂(ρ : Measure X))
        π.fst_eq

/-- Integrating `‖y‖^2` against a coupling equals integrating it against the second marginal. -/
lemma integral_norm_sq_snd
    [NormedAddCommGroup Y] [BorelSpace Y] [OpensMeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (π : Coupling μ ν) :
    ∫ z : X × Y, ‖z.2‖ ^ (2 : ℕ) ∂(π.toTransportPlan : Measure (X × Y)) =
      ∫ y : Y, ‖y‖ ^ (2 : ℕ) ∂(ν : Measure Y) := by
  calc
    -- Move the integral from the product space to the second marginal.
    ∫ z : X × Y, ‖z.2‖ ^ (2 : ℕ) ∂(π.toTransportPlan : Measure (X × Y)) =
        ∫ y : Y, ‖y‖ ^ (2 : ℕ) ∂((π.toTransportPlan.snd : ProbabilityMeasure Y) : Measure Y) := by
          symm
          exact
            integral_map measurable_snd.aemeasurable
              (aestronglyMeasurable_norm_sq
                ((π.toTransportPlan.snd : ProbabilityMeasure Y) : Measure Y))
    -- Then replace the second marginal by `ν`.
    _ = ∫ y : Y, ‖y‖ ^ (2 : ℕ) ∂(ν : Measure Y) := by
      exact congrArg
        (fun ρ : ProbabilityMeasure Y => ∫ y : Y, ‖y‖ ^ (2 : ℕ) ∂(ρ : Measure Y))
        π.snd_eq

omit [MeasurableSpace X] in
/-- Elementary quadratic-growth bound for the squared distance. This is the key pointwise estimate
used to control the quadratic cost by second moments of the marginals. -/
lemma norm_sub_sq_le_two_mul_add [NormedAddCommGroup X] (x y : X) :
    ‖x - y‖ ^ (2 : ℕ) ≤ 2 * ‖x‖ ^ (2 : ℕ) + 2 * ‖y‖ ^ (2 : ℕ) := by
  -- Start from the triangle inequality `‖x - y‖ ≤ ‖x‖ + ‖y‖`.
  have h : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := by
    simpa [sub_eq_add_neg, norm_neg] using norm_add_le x (-y)
  -- Square both sides. Since all quantities are nonnegative, `nlinarith` can handle this.
  have hsq : ‖x - y‖ ^ (2 : ℕ) ≤ (‖x‖ + ‖y‖) ^ (2 : ℕ) := by
    nlinarith [h, norm_nonneg (x - y), add_nonneg (norm_nonneg x) (norm_nonneg y)]
  -- Finally bound `(‖x‖ + ‖y‖)^2` by `2‖x‖^2 + 2‖y‖^2`.
  refine hsq.trans ?_
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Finite second moments of both marginals imply integrability of the quadratic cost integrand.
This is the bridge from the generic coupling API to quadratic-cost optimal transport. -/
lemma integrable_quadraticCostIntegrand_of_hasFiniteSecondMoment
    [NormedAddCommGroup X] [BorelSpace X] [OpensMeasurableSpace X]
    [OpensMeasurableSpace (X × X)] {μ ν : ProbabilityMeasure X} (π : Coupling μ ν)
    (hμ : HasFiniteSecondMoment μ) (hν : HasFiniteSecondMoment ν) {κ : ℝ} (hκ : 0 ≤ κ) :
    Integrable (fun z : X × X ↦ κ * ‖z.1 - z.2‖ ^ (2 : ℕ))
      (π.toTransportPlan : Measure (X × X)) := by
  -- The first and second coordinate square norms are integrable by the moment assumptions.
  have hfst := integrable_norm_sq_fst_of_hasFiniteSecondMoment π hμ
  have hsnd := integrable_norm_sq_snd_of_hasFiniteSecondMoment π hν
  -- Therefore their weighted sum is integrable.
  have hsum0 : Integrable (fun z : X × X ↦ 2 * ‖z.1‖ ^ (2 : ℕ) + 2 * ‖z.2‖ ^ (2 : ℕ))
      (π.toTransportPlan : Measure (X × X)) := by
    exact (hfst.const_mul 2).add (hsnd.const_mul 2)
  -- Multiplying by `κ` preserves integrability.
  have hsum : Integrable
      (fun z : X × X ↦ κ * (2 * ‖z.1‖ ^ (2 : ℕ) + 2 * ‖z.2‖ ^ (2 : ℕ)))
      (π.toTransportPlan : Measure (X × X)) := hsum0.const_mul κ
  -- The quadratic cost integrand is measurable because subtraction, norm, squaring, and scalar
  -- multiplication are continuous operations.
  have hmeas :
      AEStronglyMeasurable (fun z : X × X ↦ κ * ‖z.1 - z.2‖ ^ (2 : ℕ))
        (π.toTransportPlan : Measure (X × X)) := by
    simpa using
      (((continuous_fst.sub continuous_snd).norm.pow 2).aestronglyMeasurable.const_mul κ)
  -- Compare pointwise with the integrable upper bound coming from `norm_sub_sq_le_two_mul_add`.
  refine Integrable.mono' hsum hmeas ?_
  filter_upwards with z
  have hbase := norm_sub_sq_le_two_mul_add z.1 z.2
  have hnonneg : 0 ≤ ‖z.1 - z.2‖ ^ (2 : ℕ) := sq_nonneg _
  -- Remove the absolute value on the left-hand side, using nonnegativity.
  rw [Real.norm_of_nonneg (mul_nonneg hκ hnonneg)]
  -- Now multiply the pointwise bound by the nonnegative scalar `κ`.
  exact mul_le_mul_of_nonneg_left hbase hκ

end SecondMoment

end OptimalTransport
