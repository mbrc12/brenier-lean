import OptimalTransport.Rockafellar
import OptimalTransport.ConvexAE
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Measure.Map
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

section ProperFiniteness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [TopologicalSpace E]

namespace TransportPlan

/-- If the support of a transport plan is contained in a proper subgradient graph, then the
projection of that support to the source space lies in the effective domain of the potential.

This is the basic finiteness statement behind the proper-convex Brenier refactor: proper
subgradients already include finiteness at the contact point, so source-side finiteness on the
support is immediate once support inclusion is known. -/
lemma fst_image_support_subset_effectiveDomain_of_support_subset_properSubgradientGraph
    {π : TransportPlan E E} {Φ : E → WithTop ℝ}
    (hsupp : (π : Measure (E × E)).support ⊆ ProperSubgradientGraph Φ) :
    Prod.fst '' (π : Measure (E × E)).support ⊆ EffectiveDomain Φ := by
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  exact (hsupp hz).1

/-- Under the same support hypothesis, the transport plan is almost surely finite on the source
coordinate. -/
lemma ae_mem_effectiveDomain_fst_of_support_subset_properSubgradientGraph
    [PolishSpace E]
    {π : TransportPlan E E} {Φ : E → WithTop ℝ}
    (hsupp : (π : Measure (E × E)).support ⊆ ProperSubgradientGraph Φ) :
    ∀ᵐ z ∂(π : Measure (E × E)), z.1 ∈ EffectiveDomain Φ := by
  filter_upwards [(π : Measure (E × E)).support_mem_ae] with z hz
  exact (hsupp hz).1

/-- If `Φ` is measurable, the previous statement pushes forward to the first marginal.

This is the Brenier-side replacement for the old global `HasRockafellarBound` hypothesis: what is
really needed is finiteness on the source measure, not finiteness everywhere. -/
lemma fst_ae_mem_effectiveDomain_of_support_subset_properSubgradientGraph
    [PolishSpace E]
    {π : TransportPlan E E} {Φ : E → WithTop ℝ} (hΦ : Measurable Φ)
    (hsupp : (π : Measure (E × E)).support ⊆ ProperSubgradientGraph Φ) :
    ∀ᵐ x ∂(π.fst : Measure E), x ∈ EffectiveDomain Φ := by
  have hplan :
      ∀ᵐ z ∂(π : Measure (E × E)), z.1 ∈ EffectiveDomain Φ :=
    ae_mem_effectiveDomain_fst_of_support_subset_properSubgradientGraph
      (π := π) (Φ := Φ) hsupp
  have hmeas : MeasurableSet (EffectiveDomain Φ) := by
    change MeasurableSet (Φ ⁻¹' Set.Iio (⊤ : WithTop ℝ))
    simpa [EffectiveDomain] using
      measurableSet_preimage hΦ (measurableSet_Iio : MeasurableSet (Set.Iio (⊤ : WithTop ℝ)))
  have hmap :
      ∀ᵐ x ∂((π : Measure (E × E)).map Prod.fst), x ∈ EffectiveDomain Φ := by
    exact (MeasureTheory.ae_map_iff measurable_fst.aemeasurable hmeas).2 hplan
  simpa [TransportPlan.toMeasure_fst] using hmap

end TransportPlan

namespace Coupling

/-- Coupling version of source-side almost-everywhere finiteness for proper convex potentials. -/
lemma ae_mem_effectiveDomain_of_support_subset_properSubgradientGraph
    [PolishSpace E]
    {μ ν : ProbabilityMeasure E} (π : Coupling μ ν) {Φ : E → WithTop ℝ} (hΦ : Measurable Φ)
    (hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      ProperSubgradientGraph Φ) :
    ∀ᵐ x ∂(μ : Measure E), x ∈ EffectiveDomain Φ := by
  simpa [π.fst_eq] using
    TransportPlan.fst_ae_mem_effectiveDomain_of_support_subset_properSubgradientGraph
      (π := π.toTransportPlan) (Φ := Φ) hΦ hsupp

end Coupling

end ProperFiniteness

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

section ProperGradientGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [PolishSpace E]
  {m : Measure E} [MeasureTheory.Measure.IsAddHaarMeasure m]

namespace TransportPlan

/-- Proper-convex graph collapse without any global finiteness assumption.

The point is that only source-side finiteness matters. Support inclusion in a proper subgradient
graph gives finiteness on the first coordinate almost everywhere; since the effective domain of a
proper convex function is convex, its frontier has Haar measure zero, so almost every such source
point actually lies in the interior of the effective domain. On that open convex region the
real-valued representative `x ↦ (Φ x).untopD 0` is convex and differentiable almost everywhere, and
the localized supporting-hyperplane inequality forces the support point to lie on the gradient
graph. -/
lemma ae_mem_graphOn_gradient_of_support_subset_properSubgradientGraph
    {π : TransportPlan E E} {Φ : E → WithTop ℝ} (hproper : IsProperConvex Φ)
    (hΦ : Measurable Φ) (hfst_ac : (π.fst : Measure E) ≪ m)
    (hsupp : (π : Measure (E × E)).support ⊆ ProperSubgradientGraph Φ) :
    ∀ᵐ z ∂(π : Measure (E × E)),
      z ∈ Set.univ.graphOn (gradient fun x => (Φ x).untopD 0) := by
  let φ : E → ℝ := fun x => (Φ x).untopD 0
  let s : Set E := EffectiveDomain Φ
  have hconv_s : ConvexOn ℝ s φ := hproper.convexOn_effectiveDomain
  have hconv_int : ConvexOn ℝ (interior s) φ := by
    exact hconv_s.subset interior_subset hconv_s.1.interior
  have hsub :
      ∀ᵐ z ∂(π : Measure (E × E)), ProperSubgradient Φ z.1 z.2 := by
    filter_upwards [(π : Measure (E × E)).support_mem_ae] with z hz
    exact hsupp hz
  have hs_fst :
      ∀ᵐ x ∂(π.fst : Measure E), x ∈ s :=
    fst_ae_mem_effectiveDomain_of_support_subset_properSubgradientGraph
      (π := π) (Φ := Φ) hΦ hsupp
  have hfrontier_null_m : m (frontier s) = 0 := by
    exact Convex.addHaar_frontier (μ := m) hconv_s.1
  have hfrontier_null_fst : (π.fst : Measure E) (frontier s) = 0 := hfst_ac hfrontier_null_m
  have hs_int_fst :
      ∀ᵐ x ∂(π.fst : Measure E), x ∈ interior s := by
    have hs_ae_eq : interior s =ᵐ[(π.fst : Measure E)] s :=
      interior_ae_eq_of_null_frontier hfrontier_null_fst
    filter_upwards [hs_fst, hs_ae_eq] with x hxs hxeq
    have hxiff : x ∈ interior s ↔ x ∈ s := by simpa using hxeq
    exact hxiff.mpr hxs
  have hgrad_fst :
      ∀ᵐ x ∂(π.fst : Measure E), HasGradientAt φ (gradient φ x) x := by
    have hgrad_m :
        ∀ᵐ x ∂m, x ∈ interior s → HasGradientAt φ (gradient φ x) x :=
      ConvexOn.ae_hasGradientAt_of_isOpen (μ := m) isOpen_interior hconv_int
    have hgrad_fst' :
        ∀ᵐ x ∂(π.fst : Measure E), x ∈ interior s → HasGradientAt φ (gradient φ x) x :=
      hfst_ac.ae_le hgrad_m
    filter_upwards [hs_int_fst, hgrad_fst'] with x hxint hxgrad
    exact hxgrad hxint
  have hgrad :
      ∀ᵐ z ∂(π : Measure (E × E)), HasGradientAt φ (gradient φ z.1) z.1 := by
    have hgrad_map :
        ∀ᵐ x ∂((π : Measure (E × E)).map Prod.fst), HasGradientAt φ (gradient φ x) x := by
      simpa [TransportPlan.toMeasure_fst] using hgrad_fst
    exact ae_of_ae_map measurable_fst.aemeasurable hgrad_map
  have hs_int :
      ∀ᵐ z ∂(π : Measure (E × E)), z.1 ∈ interior s := by
    have hs_int_map : ∀ᵐ x ∂((π : Measure (E × E)).map Prod.fst), x ∈ interior s := by
      simpa [TransportPlan.toMeasure_fst] using hs_int_fst
    exact ae_of_ae_map measurable_fst.aemeasurable hs_int_map
  filter_upwards [hsub, hgrad, hs_int] with z hzsub hzgrad hzint
  have hsubOn : SubgradientOn s φ z.1 z.2 :=
    ProperSubgradient.subgradientOn_effectiveDomain hzsub
  have hz_eq : gradient φ z.1 = z.2 := by
    simpa [φ] using
      (SubgradientOn.eq_gradient_of_hasGradientAt_of_mem_interior hsubOn hzint hzgrad).symm
  simp [φ, hz_eq]

/-- Proper-convex version of the gradient-graph bridge, under the temporary compatibility
assumption that the proper potential is finite everywhere.

This theorem is the migrated endpoint for the Milestone 6 bridge: once a proper convex potential
`Φ : E → WithTop ℝ` is known to be finite everywhere, we pass to the real-valued wrapper
`toRealPotential Φ hfin` and reuse the existing real-valued graph-collapse theorem. -/
lemma eq_graph_gradient_of_support_subset_properSubgradientGraph_of_finite
    {π : TransportPlan E E} {Φ : E → WithTop ℝ} (hproper : IsProperConvex Φ)
    (hfin : ∀ x : E, Φ x < ⊤) (hfst_ac : (π.fst : Measure E) ≪ m)
    (hsupp : (π : Measure (E × E)).support ⊆ ProperSubgradientGraph Φ) :
    π = TransportPlan.graph π.fst (gradient (toRealPotential Φ hfin))
      (measurable_gradient (toRealPotential Φ hfin)) := by
  have hconv : ConvexOn ℝ Set.univ (toRealPotential Φ hfin) :=
    IsProperConvex.convexOn_toRealPotential (Φ := Φ) hproper hfin
  have hsupp' : (π : Measure (E × E)).support ⊆
      SubgradientGraph (toRealPotential Φ hfin) := by
    rw [← properSubgradientGraph_eq_subgradientGraph_toRealPotential (Φ := Φ) hfin]
    exact hsupp
  exact eq_graph_gradient_of_support_subset_subgradientGraph
    (π := π) (φ := toRealPotential Φ hfin) hconv hfst_ac hsupp'

/-- Proper-convex graph collapse to an actual transport map, without a global finiteness
assumption. -/
lemma eq_graph_gradient_of_support_subset_properSubgradientGraph
    {π : TransportPlan E E} {Φ : E → WithTop ℝ} (hproper : IsProperConvex Φ)
    (hΦ : Measurable Φ) (hfst_ac : (π.fst : Measure E) ≪ m)
    (hsupp : (π : Measure (E × E)).support ⊆ ProperSubgradientGraph Φ) :
    π = TransportPlan.graph π.fst (gradient fun x => (Φ x).untopD 0)
      (measurable_gradient fun x => (Φ x).untopD 0) := by
  exact eq_graph_of_ae_mem_graphOn
    (π := π) (T := gradient fun x => (Φ x).untopD 0)
    (measurable_gradient fun x => (Φ x).untopD 0)
    (ae_mem_graphOn_gradient_of_support_subset_properSubgradientGraph
      (π := π) (Φ := Φ) hproper hΦ hfst_ac hsupp)

end TransportPlan

namespace Coupling

/-- Coupling version of the proper-convex graph-collapse theorem under the temporary
finite-everywhere compatibility assumption. -/
lemma toTransportPlan_eq_graph_gradient_of_support_subset_properSubgradientGraph_of_finite
    {μ ν : ProbabilityMeasure E} (π : Coupling μ ν) {Φ : E → WithTop ℝ}
    (hproper : IsProperConvex Φ) (hfin : ∀ x : E, Φ x < ⊤)
    (hμ_ac : (μ : Measure E) ≪ m)
    (hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      ProperSubgradientGraph Φ) :
    π.toTransportPlan = TransportPlan.graph μ (gradient (toRealPotential Φ hfin))
      (measurable_gradient (toRealPotential Φ hfin)) := by
  have hfst_ac : (π.toTransportPlan.fst : Measure E) ≪ m := by
    simpa [π.fst_eq] using hμ_ac
  simpa [π.fst_eq] using
    TransportPlan.eq_graph_gradient_of_support_subset_properSubgradientGraph_of_finite
      (π := π.toTransportPlan) (Φ := Φ) hproper hfin hfst_ac hsupp

/-- Coupling version of the proper-convex graph-collapse theorem without a global finiteness
assumption. -/
lemma toTransportPlan_eq_graph_gradient_of_support_subset_properSubgradientGraph
    {μ ν : ProbabilityMeasure E} (π : Coupling μ ν) {Φ : E → WithTop ℝ}
    (hproper : IsProperConvex Φ) (hΦ : Measurable Φ)
    (hμ_ac : (μ : Measure E) ≪ m)
    (hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      ProperSubgradientGraph Φ) :
    π.toTransportPlan = TransportPlan.graph μ (gradient fun x => (Φ x).untopD 0)
      (measurable_gradient fun x => (Φ x).untopD 0) := by
  have hfst_ac : (π.toTransportPlan.fst : Measure E) ≪ m := by
    simpa [π.fst_eq] using hμ_ac
  simpa [π.fst_eq] using
    TransportPlan.eq_graph_gradient_of_support_subset_properSubgradientGraph
      (π := π.toTransportPlan) (Φ := Φ) hproper hΦ hfst_ac hsupp

/-- Pushforward identity corresponding to the proper-convex graph-collapse theorem. -/
lemma snd_eq_map_gradient_of_support_subset_properSubgradientGraph_of_finite
    {μ ν : ProbabilityMeasure E} (π : Coupling μ ν) {Φ : E → WithTop ℝ}
    (hproper : IsProperConvex Φ) (hfin : ∀ x : E, Φ x < ⊤)
    (hμ_ac : (μ : Measure E) ≪ m)
    (hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      ProperSubgradientGraph Φ) :
    ν = μ.map (measurable_gradient (toRealPotential Φ hfin)).aemeasurable := by
  have hgraph :
      π.toTransportPlan = TransportPlan.graph μ (gradient (toRealPotential Φ hfin))
        (measurable_gradient (toRealPotential Φ hfin)) :=
    toTransportPlan_eq_graph_gradient_of_support_subset_properSubgradientGraph_of_finite
      (π := π) (Φ := Φ) hproper hfin hμ_ac hsupp
  have hsnd := congrArg TransportPlan.snd hgraph
  simpa [π.snd_eq, TransportPlan.snd_graph] using hsnd

/-- Pushforward identity corresponding to the localized proper-convex graph-collapse theorem. -/
lemma snd_eq_map_gradient_of_support_subset_properSubgradientGraph
    {μ ν : ProbabilityMeasure E} (π : Coupling μ ν) {Φ : E → WithTop ℝ}
    (hproper : IsProperConvex Φ) (hΦ : Measurable Φ)
    (hμ_ac : (μ : Measure E) ≪ m)
    (hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      ProperSubgradientGraph Φ) :
    ν = μ.map (measurable_gradient fun x => (Φ x).untopD 0).aemeasurable := by
  have hgraph :
      π.toTransportPlan = TransportPlan.graph μ (gradient fun x => (Φ x).untopD 0)
        (measurable_gradient fun x => (Φ x).untopD 0) :=
    toTransportPlan_eq_graph_gradient_of_support_subset_properSubgradientGraph
      (π := π) (Φ := Φ) hproper hΦ hμ_ac hsupp
  have hsnd := congrArg TransportPlan.snd hgraph
  simpa [π.snd_eq, TransportPlan.snd_graph] using hsnd

/-- Migrated proper-convex Brenier endpoint under the current compatibility assumption that the
proper potential is finite everywhere. -/
theorem exists_convex_potential_eq_graph_of_support_subset_properSubgradientGraph_of_finite
    {μ ν : ProbabilityMeasure E} (π : Coupling μ ν) {Φ : E → WithTop ℝ}
    (hproper : IsProperConvex Φ) (hfin : ∀ x : E, Φ x < ⊤)
    (hμ_ac : (μ : Measure E) ≪ m)
    (hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      ProperSubgradientGraph Φ) :
    ∃ φ : E → ℝ,
      ConvexOn ℝ Set.univ φ ∧
      π.toTransportPlan = TransportPlan.graph μ (gradient φ) (measurable_gradient φ) ∧
      ν = μ.map (measurable_gradient φ).aemeasurable := by
  refine ⟨toRealPotential Φ hfin, ?_, ?_, ?_⟩
  · exact IsProperConvex.convexOn_toRealPotential (Φ := Φ) hproper hfin
  · exact toTransportPlan_eq_graph_gradient_of_support_subset_properSubgradientGraph_of_finite
      (π := π) (Φ := Φ) hproper hfin hμ_ac hsupp
  · exact snd_eq_map_gradient_of_support_subset_properSubgradientGraph_of_finite
      (π := π) (Φ := Φ) hproper hfin hμ_ac hsupp

/-- Migrated proper-convex endpoint without any global finiteness assumption.

The output is phrased directly in terms of the proper potential `Φ`; the induced Monge map is the
gradient of the real-valued representative `x ↦ (Φ x).untopD 0`, which is only used on the
effective domain, a set of full source measure under the hypotheses. -/
theorem exists_properConvex_potential_eq_graph_of_support_subset_properSubgradientGraph
    {μ ν : ProbabilityMeasure E} (π : Coupling μ ν) {Φ : E → WithTop ℝ}
    (hproper : IsProperConvex Φ) (hΦ : Measurable Φ)
    (hμ_ac : (μ : Measure E) ≪ m)
    (hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      ProperSubgradientGraph Φ) :
    π.toTransportPlan = TransportPlan.graph μ (gradient fun x => (Φ x).untopD 0)
        (measurable_gradient fun x => (Φ x).untopD 0) ∧
      ν = μ.map (measurable_gradient fun x => (Φ x).untopD 0).aemeasurable := by
  refine ⟨?_, ?_⟩
  · exact toTransportPlan_eq_graph_gradient_of_support_subset_properSubgradientGraph
      (π := π) (Φ := Φ) hproper hΦ hμ_ac hsupp
  · exact snd_eq_map_gradient_of_support_subset_properSubgradientGraph
      (π := π) (Φ := Φ) hproper hΦ hμ_ac hsupp

/-- Quadratic-cost packaging of the migrated proper-convex endpoint. -/
theorem
    exists_convex_potential_of_optimal_quadratic_of_support_subset_properSubgradientGraph_of_finite
    {μ ν : ProbabilityMeasure E} (π : Coupling μ ν) {Φ : E → WithTop ℝ} {κ : ℝ}
    (hopt : ∀ ρ : Coupling μ ν,
      transportCost (quadraticCost κ) π.toTransportPlan ≤
        transportCost (quadraticCost κ) ρ.toTransportPlan)
    (hproper : IsProperConvex Φ) (hfin : ∀ x : E, Φ x < ⊤)
    (hμ_ac : (μ : Measure E) ≪ m)
    (hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      ProperSubgradientGraph Φ) :
    ∃ φ : E → ℝ,
      ConvexOn ℝ Set.univ φ ∧
      π.toTransportPlan = TransportPlan.graph μ (gradient φ) (measurable_gradient φ) ∧
      ν = μ.map (measurable_gradient φ).aemeasurable ∧
      ∀ ρ : Coupling μ ν,
        transportCost (quadraticCost κ)
            (TransportPlan.graph μ (gradient φ) (measurable_gradient φ)) ≤
          transportCost (quadraticCost κ) ρ.toTransportPlan := by
  rcases exists_convex_potential_eq_graph_of_support_subset_properSubgradientGraph_of_finite
      (π := π) (Φ := Φ) hproper hfin hμ_ac hsupp with ⟨φ, hconv, hgraph, hsnd⟩
  refine ⟨φ, hconv, hgraph, hsnd, ?_⟩
  intro ρ
  simpa [hgraph] using hopt ρ

end Coupling

end ProperGradientGraph

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
  let Φ : E → WithTop ℝ := properRockafellarPotential base Γ
  have hfin : ∀ x : E, Φ x < ⊤ := by
    intro x
    simpa [Φ, Γ] using
      properRockafellarPotential_lt_top_of_bddAbove
        (base := base) (Γ := Γ) (h_bdd := h_bdd) hbase x
  have hproper : IsProperConvex Φ := by
    exact isProperConvex_properRockafellarPotential
      (base := base) (Γ := Γ) (hbase := hbase) (x := base.1) (hfin base.1)
  have hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      ProperSubgradientGraph Φ := by
    have hsupp_real : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
        SubgradientGraph (rockafellarPotential base Γ h_bdd) := by
      simpa [Γ] using
        subset_SubgradientGraph_rockafellarPotential
          (base := base) (Γ := Γ) (h_bdd := h_bdd) hbase
    have hgraph_eq :
        ProperSubgradientGraph Φ =
          SubgradientGraph (rockafellarPotential base Γ h_bdd) := by
      rw [properSubgradientGraph_eq_subgradientGraph_toRealPotential (Φ := Φ) hfin,
        toRealPotential_properRockafellarPotential_eq_rockafellarPotential
          (base := base) (Γ := Γ) (h_bdd := h_bdd) hbase]
    intro z hz
    rw [hgraph_eq]
    exact hsupp_real hz
  exact exists_convex_potential_eq_graph_of_support_subset_properSubgradientGraph_of_finite
    (π := π) (Φ := Φ) hproper hfin hμ_ac hsupp

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
  rcases hrock with ⟨base, hbase, h_bdd⟩
  let Γ : Set (E × E) := ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support
  let Φ : E → WithTop ℝ := properRockafellarPotential base Γ
  have hfin : ∀ x : E, Φ x < ⊤ := by
    intro x
    simpa [Φ, Γ] using
      properRockafellarPotential_lt_top_of_bddAbove
        (base := base) (Γ := Γ) (h_bdd := h_bdd) hbase x
  have hproper : IsProperConvex Φ := by
    exact isProperConvex_properRockafellarPotential
      (base := base) (Γ := Γ) (hbase := hbase) (x := base.1) (hfin base.1)
  have hsupp : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
      ProperSubgradientGraph Φ := by
    have hsupp_real : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
        SubgradientGraph (rockafellarPotential base Γ h_bdd) := by
      simpa [Γ] using
        subset_SubgradientGraph_rockafellarPotential
          (base := base) (Γ := Γ) (h_bdd := h_bdd) hbase
    have hgraph_eq :
        ProperSubgradientGraph Φ =
          SubgradientGraph (rockafellarPotential base Γ h_bdd) := by
      rw [properSubgradientGraph_eq_subgradientGraph_toRealPotential (Φ := Φ) hfin,
        toRealPotential_properRockafellarPotential_eq_rockafellarPotential
          (base := base) (Γ := Γ) (h_bdd := h_bdd) hbase]
    intro z hz
    rw [hgraph_eq]
    exact hsupp_real hz
  exact
    exists_convex_potential_of_optimal_quadratic_of_support_subset_properSubgradientGraph_of_finite
      (π := π) (Φ := Φ) hopt hproper hfin hμ_ac hsupp

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
