import OptimalTransport.Rockafellar
import OptimalTransport.ConvexAE
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Support

namespace OptimalTransport

open MeasureTheory

/-!
This file develops the measure-theoretic bridge from subgradient inclusion to Monge-map
representation, culminating in Brenier's theorem for quadratic cost.

The key ingredients are:

1. **Graph concentration.** If the support of a transport plan is contained in the graph of a
   measurable map, then the plan is almost surely concentrated on that graph, and hence equals the
   graph plan of that map. This is the abstract uniqueness lemma: once a plan is known to be
   supported on a graph, its first marginal uniquely determines it.

2. **Proper-subgradient graph collapse.** If a transport plan is supported in the proper
   subgradient graph of a convex potential `Φ : E → WithTop ℝ`, and its first marginal is
   absolutely continuous with respect to an additive Haar measure, then the plan is the graph
   plan of the gradient of the real-valued representative `x ↦ (Φ x).untopD 0`. The proof
   restricts to the interior of the effective domain (a convex set whose frontier has Haar
   measure zero), where the real-valued representative is differentiable a.e., so subgradients
   coincide with gradients.

3. **Brenier's theorem.** Combining the above with the Rockafellar construction (optimal plans
   sit inside proper subgradient graphs) yields the final result: an optimal quadratic-cost
   coupling with absolutely continuous source measure is the graph plan of the gradient of a
   proper convex potential, and the target measure is the pushforward by that gradient map.
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

Since proper subgradients include finiteness at the contact point, source-side finiteness on the
support follows immediately from support inclusion. -/
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

/-- If `Φ` is measurable, the effective-domain a.e. membership pushes forward to the first
marginal. The absolute-continuity hypothesis ensures that Haar-null sets for `m` are null for
the first marginal. -/
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

/-- If a transport plan is supported in the subgradient graph of a convex function `φ` and its
first marginal is absolutely continuous with respect to an additive Haar measure `m`, then the plan
is almost surely supported on the graph of `gradient φ`.

The proof has two steps:
1. Convexity gives `HasGradientAt φ (gradient φ x) x` for `m`-almost every `x`, hence for the
   first marginal by absolute continuity.
2. At a support point in the subgradient graph where `φ` is differentiable, the subgradient
   must coincide with the gradient. -/
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

/-- A transport plan supported in the subgradient graph of a convex potential equals the graph plan
of the gradient of that potential, provided the first marginal is absolutely continuous with respect
to an additive Haar measure. -/
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
gradient map. -/
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

/-- Proper-convex graph collapse: if a transport plan is supported in the proper subgradient
graph of a measurable proper convex potential, and the first marginal is absolutely continuous
with respect to an additive Haar measure, then the plan is almost surely supported on the graph
of the gradient of the real-valued representative `x ↦ (Φ x).untopD 0`.

The proof restricts to the interior of the effective domain. The frontier of a convex set has Haar
measure zero, so almost every source point lies in the interior. There the real-valued
representative is differentiable a.e. by convexity, and the local subgradient inequality forces
the support point to lie on the gradient graph. -/
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

/-- Transport plan supported in a proper subgradient graph equals the graph plan of the gradient of
the real-valued representative, under absolute continuity of the first marginal.

This combines the a.e. graph-membership statement with the general `eq_graph_of_ae_mem_graphOn`. -/
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

/-- Transport plan supported in a proper subgradient graph equals the graph plan of the gradient of
the real-valued representative, without any global finiteness assumption.

The induced Monge map is the gradient of `x ↦ (Φ x).untopD 0`, which is only used on the
effective domain — a set of full source measure under the given hypotheses. -/
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

/-- Coupling version of the proper-convex graph-collapse theorem for potentials that are finite
everywhere. -/
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

/-- Coupling version of the proper-convex graph-collapse theorem, without global finiteness. -/
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

/-- Pushforward identity: under the same hypotheses, the target marginal equals the pushforward of
the source marginal by the gradient of the real-valued representative. -/
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

/-- Pushforward identity for the localized proper-convex graph collapse. -/
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

/-- Proper-convex Brenier endpoint: if a coupling is supported in the proper subgradient graph of a
finite-everywhere proper convex potential, then the plan is the graph plan of the gradient and the
target marginal is the corresponding pushforward. -/
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

/-- Proper-convex Brenier endpoint without any global finiteness assumption.

The plan is the graph plan of `gradient (fun x => (Φ x).untopD 0)`, and the target marginal is the
pushforward of the source marginal by this gradient map. The real-valued representative is only used
on the effective domain, a set of full source measure. -/
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

/-- Quadratic-cost Brenier theorem with proper convex potential and optimality. -/
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

/-- The classical Brenier theorem for quadratic cost on a finite-dimensional inner product space,
without the Rockafellar boundedness assumption.

Given an optimal transport plan for the quadratic cost with absolutely continuous source measure,
the plan is determined by the gradient of a proper convex potential `Φ`:
1. `Φ` is proper convex and measurable;
2. The plan equals the graph plan of `gradient (fun x => (Φ x).untopD 0)`;
3. The target measure equals the pushforward of the source measure by this gradient;
4. The plan's support is contained in the proper subgradient graph of `Φ`.

The proof chains together: optimality implies pairing cyclical monotonicity of the support,
which implies the closed-chain condition, which by Rockafellar gives inclusion in the proper
subgradient graph, and the proper-convex graph collapse then produces the Monge map. -/
theorem exists_properConvex_potential_of_optimal_quadratic
    (π : Coupling μ ν) {κ : ℝ} (hκ : 0 < κ)
    (hopt : ∀ ρ : Coupling μ ν,
      transportCost (quadraticCost κ) π.toTransportPlan ≤
        transportCost (quadraticCost κ) ρ.toTransportPlan)
    (hπ : Integrable (fun z : E × E ↦ quadraticCost κ z.1 z.2)
      (π.toTransportPlan : Measure (E × E)))
    (hμ_ac : (μ : Measure E) ≪ m) :
    ∃ Φ : E → WithTop ℝ,
      IsProperConvex Φ ∧
      Measurable Φ ∧
      π.toTransportPlan =
        TransportPlan.graph μ (gradient fun x => (Φ x).untopD 0)
          (measurable_gradient fun x => (Φ x).untopD 0) ∧
      ν = μ.map (measurable_gradient fun x => (Φ x).untopD 0).aemeasurable ∧
      ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
        ProperSubgradientGraph Φ := by
  let Γ := ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support
  have hpairing : PairingClosedChainMonotone Γ := by
    have hΓ : CCyclicallyMonotone (fun x y ↦ -inner ℝ x y) Γ := by
      intro n p hp hmem
      have h := pairing_support_of_optimal_quadratic hκ π hopt hπ n p hp hmem
      have h1 : (∑ i, -inner ℝ (p i).1 (p i).2) = -(∑ i, inner ℝ (p i).1 (p i).2) := by simp
      have h2 :
          (∑ i, -inner ℝ (p i).1 (p (i + 1)).2) =
            -(∑ i, inner ℝ (p i).1 (p (i + 1)).2) := by
        simp
      rw [h1, h2]
      exact neg_le_neg h
    exact pairingClosedChainMonotone_of_cCyclicallyMonotone_negInner hΓ
  have hplan_ne_zero : ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)) ≠ 0 := by
    intro hzero
    have huniv :
        (((π.toTransportPlan : TransportPlan E E) : Measure (E × E)) Set.univ) =
          (1 : ENNReal) := by simp
    have : (0 : ENNReal) = 1 := by
      simp [hzero] at huniv
    exact zero_ne_one this
  have hΓ_nonempty : Γ.Nonempty := by
    simpa [Γ] using
      (Measure.nonempty_support
        (μ := ((π.toTransportPlan : TransportPlan E E) : Measure (E × E))) hplan_ne_zero)
  rcases hΓ_nonempty with ⟨base, hbase⟩
  let Φ := properRockafellarPotential base Γ
  have hΦ : Measurable Φ := measurable_properRockafellarPotential hbase
  have hfin_base : Φ base.1 < ⊤ := by
    refine properRockafellarPotential_lt_top_of_pairingClosedChainMonotone hpairing hbase
      (x := base.1) (y := base.2) hbase
  have hbase_in_domain : base.1 ∈ EffectiveDomain Φ := by
    simp [EffectiveDomain, hfin_base]
  have hproper : IsProperConvex Φ := by
    simpa [Φ] using isProperConvex_properRockafellarPotential hbase hbase_in_domain
  have hsupp : Γ ⊆ ProperSubgradientGraph Φ := by
    exact subset_ProperSubgradientGraph_properRockafellarPotential_of_pairingClosedChainMonotone
      hpairing hbase
  refine ⟨Φ, hproper, hΦ, ?_⟩
  have hplan :=
    Coupling.exists_properConvex_potential_eq_graph_of_support_subset_properSubgradientGraph
      (π := π) (Φ := Φ) hproper hΦ hμ_ac hsupp
  exact ⟨hplan.1, hplan.2, hsupp⟩

/-- Packaged Brenier endpoint from measure data only: finite second moments and absolute
continuity of the source produce an optimal quadratic coupling and a proper convex potential whose
gradient induces that optimal coupling. -/
theorem exists_optimalCoupling_and_properConvex_potential_of_quadratic_data
    (μ ν : ProbabilityMeasure E) {κ : ℝ} (hκ : 0 < κ)
    (hμ2 : HasFiniteSecondMoment μ) (hν2 : HasFiniteSecondMoment ν)
    (hμ_ac : (μ : Measure E) ≪ m) :
    ∃ π : Coupling μ ν, ∃ Φ : E → WithTop ℝ,
      IsProperConvex Φ ∧
      Measurable Φ ∧
      π.toTransportPlan =
        TransportPlan.graph μ (gradient fun x => (Φ x).untopD 0)
          (measurable_gradient fun x => (Φ x).untopD 0) ∧
      ν = μ.map (measurable_gradient fun x => (Φ x).untopD 0).aemeasurable ∧
      ((π.toTransportPlan : TransportPlan E E) : Measure (E × E)).support ⊆
        ProperSubgradientGraph Φ ∧
      (∀ ρ : Coupling μ ν,
        transportCost (quadraticCost κ) π.toTransportPlan ≤
          transportCost (quadraticCost κ) ρ.toTransportPlan) := by
  let cENN : E → E → ENNReal := fun x y ↦ ENNReal.ofReal (quadraticCost κ x y)
  have hc_cont : IsContinuousCost cENN := by
    dsimp [IsContinuousCost, cENN, quadraticCost]
    exact ENNReal.continuous_ofReal.comp
      (continuous_const.mul ((continuous_fst.sub continuous_snd).norm.pow 2))
  have hc_lsc : IsLowerSemicontinuousCost cENN :=
    isLowerSemicontinuousCost_of_isContinuousCost hc_cont
  obtain ⟨π, hoptENN⟩ :=
    exists_optimalCoupling_of_isLowerSemicontinuousCost (X := E) (Y := E) μ ν hc_lsc
  have hπ_int :
      Integrable (fun z : E × E ↦ quadraticCost κ z.1 z.2)
        (π.toTransportPlan : Measure (E × E)) :=
    integrable_quadraticCostIntegrand_of_hasFiniteSecondMoment
      (π := π) hμ2 hν2 (le_of_lt hκ)
  have hπ_nonneg :
      0 ≤ᵐ[(π.toTransportPlan : Measure (E × E))] (fun z : E × E ↦ quadraticCost κ z.1 z.2) :=
    Filter.Eventually.of_forall (fun z ↦ mul_nonneg (le_of_lt hκ) (sq_nonneg ‖z.1 - z.2‖))
  have hopt : ∀ ρ : Coupling μ ν,
      transportCost (quadraticCost κ) π.toTransportPlan ≤
        transportCost (quadraticCost κ) ρ.toTransportPlan := by
    intro ρ
    have hρ_int :
        Integrable (fun z : E × E ↦ quadraticCost κ z.1 z.2)
          (ρ.toTransportPlan : Measure (E × E)) :=
      integrable_quadraticCostIntegrand_of_hasFiniteSecondMoment
        (π := ρ) hμ2 hν2 (le_of_lt hκ)
    have hρ_nonneg :
        0 ≤ᵐ[(ρ.toTransportPlan : Measure (E × E))] (fun z : E × E ↦ quadraticCost κ z.1 z.2) :=
      Filter.Eventually.of_forall (fun z ↦ mul_nonneg (le_of_lt hκ) (sq_nonneg ‖z.1 - z.2‖))
    have hπ_cost :
        ENNReal.ofReal (transportCost (quadraticCost κ) π.toTransportPlan) =
          transportCostENNReal cENN π.toTransportPlan := by
      rw [transportCost, transportCostENNReal]
      simp [cENN, ofReal_integral_eq_lintegral_ofReal hπ_int hπ_nonneg]
    have hρ_cost :
        ENNReal.ofReal (transportCost (quadraticCost κ) ρ.toTransportPlan) =
          transportCostENNReal cENN ρ.toTransportPlan := by
      rw [transportCost, transportCostENNReal]
      simp [cENN, ofReal_integral_eq_lintegral_ofReal hρ_int hρ_nonneg]
    have hleENN :
        ENNReal.ofReal (transportCost (quadraticCost κ) π.toTransportPlan) ≤
          ENNReal.ofReal (transportCost (quadraticCost κ) ρ.toTransportPlan) := by
      simpa [hπ_cost, hρ_cost] using hoptENN ρ
    have hρ_cost_nonneg : 0 ≤ transportCost (quadraticCost κ) ρ.toTransportPlan := by
      exact integral_nonneg_of_ae hρ_nonneg
    exact (ENNReal.ofReal_le_ofReal_iff hρ_cost_nonneg).1 hleENN
  rcases exists_properConvex_potential_of_optimal_quadratic
      (m := m) (π := π) hκ hopt hπ_int hμ_ac with
    ⟨Φ, hproper, hΦ, hgraph, hpush, hsupp⟩
  exact ⟨π, Φ, hproper, hΦ, hgraph, hpush, hsupp, hopt⟩

end Coupling

end FinalTheorems

section EuclideanFinalTheorems

namespace Coupling

variable {n : ℕ}
variable {μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}

/-- Euclidean specialization of Brenier's theorem on `EuclideanSpace ℝ (Fin n)`. -/
theorem exists_properConvex_potential_of_optimal_quadratic_euclidean
    (π : Coupling μ ν) {κ : ℝ}
    (hopt : ∀ ρ : Coupling μ ν,
      transportCost (quadraticCost κ) π.toTransportPlan ≤
        transportCost (quadraticCost κ) ρ.toTransportPlan)
    (hκ : 0 < κ)
    (hπ : Integrable (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
      quadraticCost κ z.1 z.2) (π.toTransportPlan : Measure (EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n))))
    (hμ_ac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume)
    :
    ∃ Φ : EuclideanSpace ℝ (Fin n) → WithTop ℝ,
      IsProperConvex Φ ∧
      Measurable Φ ∧
      π.toTransportPlan =
        TransportPlan.graph μ (gradient fun x => (Φ x).untopD 0)
          (measurable_gradient fun x => (Φ x).untopD 0) ∧
      ν = μ.map (measurable_gradient fun x => (Φ x).untopD 0).aemeasurable ∧
      ((π.toTransportPlan : TransportPlan (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin n))) : Measure ((EuclideanSpace ℝ (Fin n)) ×
          (EuclideanSpace ℝ (Fin n)))).support ⊆ ProperSubgradientGraph Φ := by
  exact exists_properConvex_potential_of_optimal_quadratic
    (m := volume) (π := π) hκ hopt hπ hμ_ac

end Coupling

end EuclideanFinalTheorems

end OptimalTransport
