import OptimalTransport.Rockafellar
import OptimalTransport.ConvexAE
import Mathlib.MeasureTheory.Measure.Support

namespace OptimalTransport

open MeasureTheory

/-!
This file collects the measure-theoretic lemmas on the map side of the Brenier program that fit
cleanly into the current repository API.

The two main reusable facts proved here are:

* support inclusion in the graph of a map implies almost-sure graph membership;
* a transport plan whose first marginal is `μ` and which is almost surely concentrated on the graph
  of a measurable map `T` is exactly the graph plan `graph μ T`.

The final section adds the actual Milestone 6 bridge used later in Brenier's theorem:

* if a transport plan is supported in the subgradient graph of a convex potential `φ`;
* and if its first marginal is absolutely continuous with respect to an additive Haar measure;

then the plan is the graph plan of the measurable map `gradient φ`.

The second statement is the key measure-theoretic uniqueness lemma needed later in Brenier's
argument: once one has proved that an optimal plan is a.e. supported on a graph, no further
transport structure remains to be checked.
-/

section GraphAE

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [TopologicalSpace Y] [PolishSpace X] [PolishSpace Y]

/-- If the support of a measure on `X × Y` is contained in the graph of a map `T`, then the
measure is almost surely contained in that graph as well. -/
lemma ae_mem_graphOn_of_support_subset {μ : Measure (X × Y)} {T : X → Y}
    (hsupp : μ.support ⊆ Set.univ.graphOn T) :
    ∀ᵐ z ∂μ, z ∈ Set.univ.graphOn T := by
  filter_upwards [μ.support_mem_ae] with z hz
  exact hsupp hz

namespace TransportPlan

/-- If a transport plan is almost surely concentrated on the graph of a measurable map `T`, then
the plan is exactly the graph plan of its first marginal.

The proof proceeds setwise. For a measurable set `s ⊆ X × Y`, almost-sure graph membership lets us
replace membership of a point `z = (x, y)` in `s` by membership of `(x, T x)` in `s`. This turns
the value of the plan on `s` into the value of the first marginal on the pullback of `s` by the
graph map `x ↦ (x, T x)`, which is exactly the defining formula for the graph plan. -/
lemma eq_graph_of_ae_mem_graphOn
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {π : TransportPlan X Y} {T : X → Y} (hT : Measurable T)
    (hgraph : ∀ᵐ z ∂(π : Measure (X × Y)), z ∈ Set.univ.graphOn T) :
    π = TransportPlan.graph π.fst T hT := by
  apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  have hs_eq :
      s =ᵐ[(π : Measure (X × Y))]
        Prod.fst ⁻¹' ((fun x : X ↦ (x, T x)) ⁻¹' s) := by
    filter_upwards [hgraph] with z hz
    rcases z with ⟨x, y⟩
    have hzT : T x = y := by
      have hz' : x ∈ Set.univ ∧ T x = y := by
        simpa using hz
      exact hz'.2
    apply propext
    constructor
    · intro hsxy
      change s (x, T x)
      simpa [hzT] using hsxy
    · intro hsxy
      change s (x, T x) at hsxy
      simpa [hzT] using hsxy
  calc
    (π : Measure (X × Y)) s
      = (π : Measure (X × Y)) (Prod.fst ⁻¹' ((fun x : X ↦ (x, T x)) ⁻¹' s)) := by
          exact measure_congr hs_eq
    _ = (π.fst : Measure X) ((fun x : X ↦ (x, T x)) ⁻¹' s) := by
          exact TransportPlan.measure_preimage_fst_eq (π := π)
            (hs := hs.preimage (measurable_id.prodMk hT))
    _ = ((TransportPlan.graph π.fst T hT : TransportPlan X Y) : Measure (X × Y)) s := by
          symm
          simpa [TransportPlan.graph] using
            (Measure.map_apply (μ := ((π.fst : ProbabilityMeasure X) : Measure X))
              (f := fun x : X ↦ (x, T x)) (hf := measurable_id.prodMk hT) hs)

/-- Support inclusion in a graph upgrades immediately to equality with the corresponding graph
plan. This packages the previous two lemmas in the form that later optimal-transport arguments
actually use. -/
lemma eq_graph_of_support_subset
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y] [PolishSpace X] [PolishSpace Y]
    {π : TransportPlan X Y} {T : X → Y} (hT : Measurable T)
    (hsupp : (π : Measure (X × Y)).support ⊆ Set.univ.graphOn T) :
    π = TransportPlan.graph π.fst T hT :=
  eq_graph_of_ae_mem_graphOn hT (ae_mem_graphOn_of_support_subset hsupp)

end TransportPlan

namespace Coupling

/-- A coupling whose underlying plan is almost surely concentrated on the graph of a measurable map
is exactly the coupling induced by that map. The codomain marginal is forced automatically by the
graph-plan identity. -/
lemma toTransportPlan_eq_graph_of_ae_mem_graphOn
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {T : X → Y} (hT : Measurable T)
    (hgraph : ∀ᵐ z ∂(π.toTransportPlan : Measure (X × Y)), z ∈ Set.univ.graphOn T) :
    π.toTransportPlan = TransportPlan.graph μ T hT := by
  simpa [π.fst_eq] using
    TransportPlan.eq_graph_of_ae_mem_graphOn (π := π.toTransportPlan) hT hgraph

/-- Support inclusion in a graph also identifies the underlying transport plan of a coupling with
the graph plan induced by that map. -/
lemma toTransportPlan_eq_graph_of_support_subset
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y] [PolishSpace X] [PolishSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {T : X → Y} (hT : Measurable T)
    (hsupp : ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support ⊆
      Set.univ.graphOn T) :
    π.toTransportPlan = TransportPlan.graph μ T hT := by
  simpa [π.fst_eq] using
    TransportPlan.eq_graph_of_support_subset (π := π.toTransportPlan) hT hsupp

end Coupling

end GraphAE

section GradientGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [PolishSpace E]
  {m : Measure E} [MeasureTheory.Measure.IsAddHaarMeasure m]

namespace TransportPlan

/-- If a transport plan is supported in the subgradient graph of a convex function `φ`, and its
first marginal is absolutely continuous with respect to an additive Haar measure `m`, then the plan
is almost surely supported on the graph of the gradient of `φ`.

The proof has two inputs:

1. convexity gives `HasGradientAt φ (gradient φ x) x` for `m`-almost every `x`, hence also for the
   first marginal by absolute continuity;
2. on points of the support lying in the subgradient graph, the subgradient must equal the gradient
   at differentiability points.

This is the precise analytic bridge from Rockafellar's convex potential to a Monge map. -/
lemma ae_mem_graphOn_gradient_of_support_subset_subgradientGraph
    {π : TransportPlan E E} {φ : E → ℝ} (hconv : ConvexOn ℝ Set.univ φ)
    (hfst_ac : (π.fst : Measure E) ≪ m)
    (hsupp : (π : Measure (E × E)).support ⊆ SubgradientGraph φ) :
    ∀ᵐ z ∂(π : Measure (E × E)), z ∈ Set.univ.graphOn (gradient φ) := by
  have hsub :
      ∀ᵐ z ∂(π : Measure (E × E)), z ∈ SubgradientGraph φ := by
    filter_upwards [(π : Measure (E × E)).support_mem_ae] with z hz
    exact hsupp hz
  have hgrad_fst :
      ∀ᵐ x ∂(π.fst : Measure E), HasGradientAt φ (gradient φ x) x :=
    hfst_ac.ae_le (ConvexOn.ae_hasGradientAt (μ := m) hconv)
  have hgrad :
      ∀ᵐ z ∂(π : Measure (E × E)), HasGradientAt φ (gradient φ z.1) z.1 := by
    have hgrad_map :
        ∀ᵐ x ∂((π : Measure (E × E)).map Prod.fst), HasGradientAt φ (gradient φ x) x := by
      simpa [TransportPlan.toMeasure_fst] using hgrad_fst
    exact ae_of_ae_map measurable_fst.aemeasurable hgrad_map
  filter_upwards [hsub, hgrad] with z hzsub hzgrad
  have hz_eq : gradient φ z.1 = z.2 := by
    simpa using (Subgradient.eq_gradient_of_hasGradientAt (by simpa using hzsub) hzgrad).symm
  simp [hz_eq]

/-- A transport plan supported in the subgradient graph of a convex potential is the graph plan of
the gradient of that potential, provided the first marginal is absolutely continuous with respect to
an additive Haar measure.

This packages the previous almost-sure graph-membership statement with the general
`eq_graph_of_ae_mem_graphOn` lemma. It is the exact Milestone 6 statement needed later when an
optimal plan has already been identified with a convex subgradient graph via Rockafellar. -/
lemma eq_graph_gradient_of_support_subset_subgradientGraph
    {π : TransportPlan E E} {φ : E → ℝ} (hconv : ConvexOn ℝ Set.univ φ)
    (hfst_ac : (π.fst : Measure E) ≪ m)
    (hsupp : (π : Measure (E × E)).support ⊆ SubgradientGraph φ) :
    π = TransportPlan.graph π.fst (gradient φ) (measurable_gradient φ) := by
  exact eq_graph_of_ae_mem_graphOn (π := π) (T := gradient φ) (measurable_gradient φ)
    (ae_mem_graphOn_gradient_of_support_subset_subgradientGraph
      (π := π) (φ := φ) hconv hfst_ac hsupp)

end TransportPlan

namespace Coupling

/-- Coupling version of `TransportPlan.eq_graph_gradient_of_support_subset_subgradientGraph`.

If the source marginal `μ` is absolutely continuous with respect to an additive Haar measure and the
support of the coupling sits inside the subgradient graph of a convex potential `φ`, then the
underlying transport plan is exactly the graph plan of `gradient φ`. -/
lemma toTransportPlan_eq_graph_gradient_of_support_subset_subgradientGraph
    {μ ν : ProbabilityMeasure E} (π : Coupling μ ν) {φ : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ φ) (hμ_ac : (μ : Measure E) ≪ m)
    (hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      SubgradientGraph φ) :
    π.toTransportPlan = TransportPlan.graph μ (gradient φ) (measurable_gradient φ) := by
  have hfst_ac : (π.toTransportPlan.fst : Measure E) ≪ m := by
    simpa [π.fst_eq] using hμ_ac
  simpa [π.fst_eq] using
    TransportPlan.eq_graph_gradient_of_support_subset_subgradientGraph
      (π := π.toTransportPlan) (φ := φ) hconv hfst_ac hsupp

/-- Under the same hypotheses, the target marginal is the pushforward of the source marginal by the
gradient map. This is the pushforward identity needed for the Monge-side conclusion of Brenier's
theorem. -/
lemma snd_eq_map_gradient_of_support_subset_subgradientGraph
    {μ ν : ProbabilityMeasure E} (π : Coupling μ ν) {φ : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ φ) (hμ_ac : (μ : Measure E) ≪ m)
    (hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      SubgradientGraph φ) :
    ν = μ.map (measurable_gradient φ).aemeasurable := by
  have hgraph :
      π.toTransportPlan = TransportPlan.graph μ (gradient φ) (measurable_gradient φ) :=
    toTransportPlan_eq_graph_gradient_of_support_subset_subgradientGraph
      (π := π) (φ := φ) hconv hμ_ac hsupp
  have hsnd := congrArg TransportPlan.snd hgraph
  simpa [π.snd_eq, TransportPlan.snd_graph] using hsnd

end Coupling

end GradientGraph

section FinalTheorems

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [PolishSpace E]
  {m : Measure E} [MeasureTheory.Measure.IsAddHaarMeasure m]

namespace Coupling

variable {μ ν : ProbabilityMeasure E}

/-- The Rockafellar boundedness hypothesis for a coupling.

This records exactly the extra assumption still needed by the present real-valued Rockafellar file:
some base point of the support should root value sets that are bounded above at every target point.
Under this hypothesis the finite-chain supremum defines a genuine real-valued convex potential. -/
def HasRockafellarBound (π : Coupling μ ν) : Prop :=
  ∃ base ∈ ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support,
    ∀ x : E,
      BddAbove
        (rockafellarValueSet base
          (((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support) x)

/-- If a coupling satisfies the Rockafellar boundedness hypothesis and its source marginal is
absolutely continuous with respect to an additive Haar measure, then the coupling is induced by the
gradient of a convex potential.

The potential is the rooted Rockafellar supremum attached to the support of the coupling.
The proof combines the completed Rockafellar containment theorem with the Milestone 6
graph-collapse result. -/
theorem exists_convex_potential_eq_graph_of_hasRockafellarBound
    (π : Coupling μ ν) (hμ_ac : (μ : Measure E) ≪ m) (hrock : π.HasRockafellarBound) :
    ∃ φ : E → ℝ,
      ConvexOn ℝ Set.univ φ ∧
      π.toTransportPlan = TransportPlan.graph μ (gradient φ) (measurable_gradient φ) ∧
      ν = μ.map (measurable_gradient φ).aemeasurable := by
  rcases hrock with ⟨base, hbase, h_bdd⟩
  let Γ : Set (E × E) := ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support
  let φ : E → ℝ := rockafellarPotential base Γ h_bdd
  have hconv : ConvexOn ℝ Set.univ φ := by
    simpa [φ, Γ] using
      convexOn_rockafellarPotential (base := base) (Γ := Γ) (h_bdd := h_bdd) hbase
  have hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      SubgradientGraph φ := by
    simpa [φ, Γ] using
      subset_SubgradientGraph_rockafellarPotential
        (base := base) (Γ := Γ) (h_bdd := h_bdd) hbase
  refine ⟨φ, hconv, ?_, ?_⟩
  · exact toTransportPlan_eq_graph_gradient_of_support_subset_subgradientGraph
      (π := π) (φ := φ) hconv hμ_ac hsupp
  · exact snd_eq_map_gradient_of_support_subset_subgradientGraph
      (π := π) (φ := φ) hconv hμ_ac hsupp

/-- Final quadratic-cost packaging under the hypotheses currently available in the repository.

If `π` is already known to be optimal for the quadratic cost and also satisfies the Rockafellar
boundedness hypothesis on its support, then there exists a convex potential `φ` whose gradient
induces `π`. Since the graph plan is literally the same transport plan, it inherits optimality
immediately.

Relative to the classical Brenier theorem, the only missing input here is the derivation of the
Rockafellar support hypothesis from optimality itself. -/
theorem exists_convex_potential_of_optimal_quadratic_of_hasRockafellarBound
    (π : Coupling μ ν) {κ : ℝ}
    (hopt : ∀ ρ : Coupling μ ν,
      transportCost (quadraticCost κ) π.toTransportPlan ≤
        transportCost (quadraticCost κ) ρ.toTransportPlan)
    (hμ_ac : (μ : Measure E) ≪ m) (hrock : π.HasRockafellarBound) :
    ∃ φ : E → ℝ,
      ConvexOn ℝ Set.univ φ ∧
      π.toTransportPlan = TransportPlan.graph μ (gradient φ) (measurable_gradient φ) ∧
      ν = μ.map (measurable_gradient φ).aemeasurable ∧
      ∀ ρ : Coupling μ ν,
        transportCost (quadraticCost κ)
            (TransportPlan.graph μ (gradient φ) (measurable_gradient φ)) ≤
          transportCost (quadraticCost κ) ρ.toTransportPlan := by
  rcases exists_convex_potential_eq_graph_of_hasRockafellarBound
      (π := π) hμ_ac hrock with ⟨φ, hconv, hgraph, hsnd⟩
  refine ⟨φ, hconv, hgraph, hsnd, ?_⟩
  intro ρ
  simpa [hgraph] using hopt ρ

end Coupling

end FinalTheorems

section EuclideanFinalTheorems

namespace Coupling

variable {n : ℕ}
variable {μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}

/-- Euclidean specialization of the quadratic Brenier endpoint currently formalized in the
repository.

This is the version closest to the planned grand theorem: on `EuclideanSpace ℝ (Fin n)`, an
optimal quadratic coupling with absolutely continuous source measure and with the Rockafellar
boundedness hypothesis on its support is induced by the gradient of a convex potential, and the
resulting graph plan is optimal. -/
theorem exists_convex_potential_of_optimal_quadratic_of_hasRockafellarBound_euclidean
    (π : Coupling μ ν) {κ : ℝ}
    (hopt : ∀ ρ : Coupling μ ν,
      transportCost (quadraticCost κ) π.toTransportPlan ≤
        transportCost (quadraticCost κ) ρ.toTransportPlan)
    (hμ_ac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume)
    (hrock : π.HasRockafellarBound) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ConvexOn ℝ Set.univ φ ∧
      π.toTransportPlan =
        TransportPlan.graph μ (gradient φ) (measurable_gradient φ) ∧
      ν = μ.map (measurable_gradient φ).aemeasurable ∧
      ∀ ρ : Coupling μ ν,
        transportCost (quadraticCost κ)
            (TransportPlan.graph μ (gradient φ) (measurable_gradient φ)) ≤
          transportCost (quadraticCost κ) ρ.toTransportPlan := by
  exact exists_convex_potential_of_optimal_quadratic_of_hasRockafellarBound
    (m := volume) (π := π) hopt hμ_ac hrock

end Coupling

end EuclideanFinalTheorems

end OptimalTransport
