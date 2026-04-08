import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prod

namespace OptimalTransport

open MeasureTheory

/-!
This file introduces the most basic objects for optimal transport:

* `TransportPlan X Y`: a probability measure on the product space `X × Y`;
* the two marginals `fst` and `snd` of such a plan;
* plans coming from measurable maps, called `graph`;
* `Coupling μ ν`: a transport plan whose marginals are exactly `μ` and `ν`.

The definitions are intentionally lightweight. The point of this file is to set up the
foundational API that later files use for transport costs, compactness, and optimality.
-/

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A transport plan from `X` to `Y` is a probability measure on `X × Y`. -/
abbrev TransportPlan (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] :=
  ProbabilityMeasure (X × Y)

namespace TransportPlan

/-- The first marginal of a transport plan. -/
noncomputable def fst (π : TransportPlan X Y) : ProbabilityMeasure X :=
  -- Push the plan `π` forward along the projection `(x, y) ↦ x`.
  π.map measurable_fst.aemeasurable

/-- The second marginal of a transport plan. -/
noncomputable def snd (π : TransportPlan X Y) : ProbabilityMeasure Y :=
  -- Push the plan `π` forward along the projection `(x, y) ↦ y`.
  π.map measurable_snd.aemeasurable

/-- Coercing the first marginal to a measure gives the usual first marginal of the underlying
product-space measure. -/
@[simp]
lemma toMeasure_fst (π : TransportPlan X Y) :
    (π.fst : Measure X) = (π : Measure (X × Y)).fst := rfl

/-- Coercing the second marginal to a measure gives the usual second marginal of the underlying
product-space measure. -/
@[simp]
lemma toMeasure_snd (π : TransportPlan X Y) :
    (π.snd : Measure Y) = (π : Measure (X × Y)).snd := rfl

/-- Evaluating the first marginal on a measurable set is the same as evaluating the plan on the
preimage of that set under the first projection. -/
@[simp]
lemma fst_apply (π : TransportPlan X Y) {s : Set X} (hs : MeasurableSet s) :
    π.fst s = π (Prod.fst ⁻¹' s) := by
  -- This is just the defining formula for the pushforward measure.
  simpa [fst] using ProbabilityMeasure.map_apply π measurable_fst.aemeasurable hs

/-- Evaluating the second marginal on a measurable set is the same as evaluating the plan on the
preimage of that set under the second projection. -/
@[simp]
lemma snd_apply (π : TransportPlan X Y) {s : Set Y} (hs : MeasurableSet s) :
    π.snd s = π (Prod.snd ⁻¹' s) := by
  -- Again, unfold the pushforward along the second projection.
  simpa [snd] using ProbabilityMeasure.map_apply π measurable_snd.aemeasurable hs

/-- The first marginal of the independent product plan `μ.prod ν` is `μ`. -/
@[simp]
lemma fst_prod (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    (TransportPlan.fst (μ.prod ν)) = μ := by
  -- The first marginal of a product measure is the first factor.
  simp [TransportPlan.fst]

/-- The second marginal of the independent product plan `μ.prod ν` is `ν`. -/
@[simp]
lemma snd_prod (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    (TransportPlan.snd (μ.prod ν)) = ν := by
  -- The second marginal of a product measure is the second factor.
  simp [TransportPlan.snd]

/-- The graph plan of a measurable map `T : X → Y` with source marginal `μ`. -/
noncomputable def graph (μ : ProbabilityMeasure X) (T : X → Y) (hT : Measurable T) :
    TransportPlan X Y :=
  -- This is the pushforward of `μ` by the graph map `x ↦ (x, T x)`.
  μ.map (measurable_id.prodMk hT).aemeasurable

/-- The first marginal of a graph plan is the source measure. -/
@[simp]
lemma fst_graph (μ : ProbabilityMeasure X) (T : X → Y) (hT : Measurable T) :
    (graph μ T hT).fst = μ := by
  -- Equality of probability measures is reduced to equality of the underlying measures.
  apply Subtype.ext
  -- After unfolding definitions, this is exactly the standard statement that the first marginal
  -- of the graph measure of `x ↦ (x, T x)` is the original measure.
  change Measure.map Prod.fst (Measure.map (fun x ↦ (x, T x)) (μ : Measure X)) = (μ : Measure X)
  simpa [Measure.fst] using
    Measure.fst_map_prodMk (μ := (μ : Measure X)) (X := fun x : X ↦ x) hT

/-- The second marginal of a graph plan is the pushforward of the source measure by the map. -/
@[simp]
lemma snd_graph (μ : ProbabilityMeasure X) (T : X → Y) (hT : Measurable T) :
    (graph μ T hT).snd = μ.map hT.aemeasurable := by
  -- As above, work with the underlying measures.
  apply Subtype.ext
  -- The second marginal of the graph measure is the pushforward of `μ` by `T`.
  change Measure.map Prod.snd (Measure.map (fun x ↦ (x, T x)) (μ : Measure X)) =
    Measure.map T (μ : Measure X)
  simpa [Measure.snd] using
    Measure.snd_map_prodMk (μ := (μ : Measure X)) (X := fun x : X ↦ x) measurable_id

end TransportPlan

/-- A coupling of `μ` and `ν` is a transport plan on `X × Y` with marginals `μ` and `ν`. -/
structure Coupling (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) where
  /-- The underlying transport plan on the product space. -/
  toTransportPlan : TransportPlan X Y
  /-- The first marginal is the prescribed source measure `μ`. -/
  fst_eq : toTransportPlan.fst = μ
  /-- The second marginal is the prescribed target measure `ν`. -/
  snd_eq : toTransportPlan.snd = ν

namespace Coupling

variable {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}

/-- Restates the first-marginal field of a coupling as a simp lemma. -/
@[simp]
lemma fst (π : Coupling μ ν) : π.toTransportPlan.fst = μ := π.fst_eq

/-- Restates the second-marginal field of a coupling as a simp lemma. -/
@[simp]
lemma snd (π : Coupling μ ν) : π.toTransportPlan.snd = ν := π.snd_eq

/-- Coercing the first marginal of a coupling to a measure recovers the prescribed source
measure. -/
@[simp]
lemma toMeasure_fst (π : Coupling μ ν) :
    ((π.toTransportPlan.fst : ProbabilityMeasure X) : Measure X) = (μ : Measure X) := by
  -- Apply the coercion from probability measures to measures to `π.fst_eq`.
  exact congrArg (fun ρ : ProbabilityMeasure X => (ρ : Measure X)) π.fst_eq

/-- Coercing the second marginal of a coupling to a measure recovers the prescribed target
measure. -/
@[simp]
lemma toMeasure_snd (π : Coupling μ ν) :
    ((π.toTransportPlan.snd : ProbabilityMeasure Y) : Measure Y) = (ν : Measure Y) := by
  -- Same argument for the second marginal.
  exact congrArg (fun ρ : ProbabilityMeasure Y => (ρ : Measure Y)) π.snd_eq

/-- The independent product plan is a coupling. -/
noncomputable def prod (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : Coupling μ ν where
  -- Take the ordinary product probability measure.
  toTransportPlan := μ.prod ν
  fst_eq := by
    -- Its first marginal is `μ`.
    exact TransportPlan.fst_prod μ ν
  snd_eq := by
    -- Its second marginal is `ν`.
    exact TransportPlan.snd_prod μ ν

/-- Any pair of probability measures admits at least one coupling. -/
instance (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : Nonempty (Coupling μ ν) :=
  -- A coupling always exists: the independent product plan.
  ⟨prod μ ν⟩

/-- The graph plan of a measurable map is a coupling with its pushforward target. -/
noncomputable def ofMap (μ : ProbabilityMeasure X) (T : X → Y) (hT : Measurable T) :
    Coupling μ (μ.map hT.aemeasurable) where
  -- Use the graph measure associated to `T`.
  toTransportPlan := TransportPlan.graph μ T hT
  fst_eq := by
    -- The first marginal is still `μ`.
    exact TransportPlan.fst_graph μ T hT
  snd_eq := by
    -- The second marginal is the pushforward of `μ` by `T`.
    exact TransportPlan.snd_graph μ T hT

end Coupling

end OptimalTransport
