import OptimalTransport.Cost
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.MetricSpace.Polish

namespace OptimalTransport

open MeasureTheory
open Filter
open scoped ENNReal NNReal

/-!
This file proves the basic compactness and existence statements for couplings in the weak topology.

Unlike the earlier compact-space warm-up, the intended setting here is already the one used in the
generic Villani-style existence theorem:

* `X` and `Y` are Polish spaces with their Borel sigma-algebras;
* the set of couplings of fixed marginals is shown to be closed and tight, hence compact by
  Prokhorov;
* as an immediately usable corollary, bounded continuous nonnegative costs admit minimizers.

The final lower-semicontinuous `ℝ≥0∞` existence theorem sits one step beyond this file: it only
is proved here by combining Portmanteau with truncated costs and a minimizing-sequence argument.
-/

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The set of transport plans whose marginals are exactly `μ` and `ν`. -/
def couplingSet (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : Set (TransportPlan X Y) :=
  -- This is the fixed-marginal subset of the ambient space `ProbabilityMeasure (X × Y)`.
  {π | π.fst = μ ∧ π.snd = ν}

/-- Membership in `couplingSet μ ν` just means having first marginal `μ` and second marginal `ν`.
This lemma keeps that predicate transparent for rewriting. -/
@[simp]
lemma mem_couplingSet {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {π : TransportPlan X Y} :
    π ∈ couplingSet μ ν ↔ π.fst = μ ∧ π.snd = ν :=
  Iff.rfl

namespace TransportPlan

/-- The first marginal map is continuous for the weak topology on probability measures. This is
used to prove that the fixed-marginal coupling set is closed. -/
lemma continuous_fstMarginal [TopologicalSpace X] [BorelSpace X] [TopologicalSpace Y]
    [BorelSpace Y] [OpensMeasurableSpace (X × Y)] :
    Continuous (fun π : TransportPlan X Y ↦ π.fst) := by
  -- The first marginal is pushforward along the continuous projection `Prod.fst`.
  simpa [TransportPlan.fst] using
    (ProbabilityMeasure.continuous_map (Ω := X × Y) (Ω' := X) continuous_fst)

/-- The second marginal map is continuous for the weak topology on probability measures. -/
lemma continuous_sndMarginal [TopologicalSpace X] [BorelSpace X] [TopologicalSpace Y]
    [BorelSpace Y] [OpensMeasurableSpace (X × Y)] :
    Continuous (fun π : TransportPlan X Y ↦ π.snd) := by
  -- Likewise for the second projection.
  simpa [TransportPlan.snd] using
    (ProbabilityMeasure.continuous_map (Ω := X × Y) (Ω' := Y) continuous_snd)

/-- The measure of a cylinder set pulled back by the first projection is the value of the first
marginal on the underlying set. -/
lemma measure_preimage_fst_eq (π : TransportPlan X Y)
    {s : Set X} (hs : MeasurableSet s) :
    (π : Measure (X × Y)) (Prod.fst ⁻¹' s) = (π.fst : Measure X) s := by
  -- This is the usual marginal formula, rewritten on the level of underlying measures.
  simpa [TransportPlan.toMeasure_fst] using
    (Measure.fst_apply (ρ := (π : Measure (X × Y))) (s := s) hs).symm

/-- The measure of a cylinder set pulled back by the second projection is the value of the second
marginal on the underlying set. -/
lemma measure_preimage_snd_eq (π : TransportPlan X Y)
    {s : Set Y} (hs : MeasurableSet s) :
    (π : Measure (X × Y)) (Prod.snd ⁻¹' s) = (π.snd : Measure Y) s := by
  -- And similarly for the second marginal.
  simpa [TransportPlan.toMeasure_snd] using
    (Measure.snd_apply (ρ := (π : Measure (X × Y))) (s := s) hs).symm

/-- A coupling cannot put much mass outside `K × L` unless one of its marginals puts mass outside
`K` or `L`. This is the basic estimate used to prove tightness of the whole coupling set from
tightness of the marginals. -/
lemma measure_compl_prod_le {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : TransportPlan X Y) (hfst : π.fst = μ) (hsnd : π.snd = ν)
    {K : Set X} {L : Set Y} (hK : MeasurableSet K) (hL : MeasurableSet L) :
    (π : Measure (X × Y)) ((K ×ˢ L)ᶜ) ≤ (μ : Measure X) Kᶜ + (ν : Measure Y) Lᶜ := by
  have hsubset :
      (K ×ˢ L)ᶜ ⊆ Prod.fst ⁻¹' Kᶜ ∪ Prod.snd ⁻¹' Lᶜ := by
    intro z hz
    by_cases hx : z.1 ∈ K
    · right
      simp only [Set.mem_preimage, Set.mem_compl_iff]
      intro hzL
      exact hz ⟨hx, hzL⟩
    · left
      simp [hx]
  calc
    (π : Measure (X × Y)) ((K ×ˢ L)ᶜ)
      ≤ (π : Measure (X × Y)) (Prod.fst ⁻¹' Kᶜ ∪ Prod.snd ⁻¹' Lᶜ) := by
          exact measure_mono hsubset
    _ ≤ (π : Measure (X × Y)) (Prod.fst ⁻¹' Kᶜ) + (π : Measure (X × Y)) (Prod.snd ⁻¹' Lᶜ) := by
          exact measure_union_le _ _
    _ = (π.fst : Measure X) Kᶜ + (π.snd : Measure Y) Lᶜ := by
          rw [TransportPlan.measure_preimage_fst_eq (π := π) (s := Kᶜ) (hs := hK.compl)]
          rw [TransportPlan.measure_preimage_snd_eq (π := π) (s := Lᶜ) (hs := hL.compl)]
    _ = (μ : Measure X) Kᶜ + (ν : Measure Y) Lᶜ := by
          rw [hfst, hsnd]

end TransportPlan

namespace Coupling

/-- The transport plan underlying a coupling belongs to the corresponding fixed-marginal set. -/
@[simp]
lemma toTransportPlan_mem_couplingSet {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) :
    π.toTransportPlan ∈ couplingSet μ ν := by
  -- This is exactly the data stored in the structure `Coupling`.
  exact ⟨π.fst_eq, π.snd_eq⟩

/-- The product-complement estimate specialized to an actual coupling. -/
lemma measure_compl_prod_le {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {K : Set X} {L : Set Y} (hK : MeasurableSet K) (hL : MeasurableSet L) :
    (π.toTransportPlan : Measure (X × Y)) ((K ×ˢ L)ᶜ) ≤
      (μ : Measure X) Kᶜ + (ν : Measure Y) Lᶜ :=
  TransportPlan.measure_compl_prod_le π.toTransportPlan π.fst_eq π.snd_eq hK hL

end Coupling

/-- The set of couplings is nonempty: the independent product plan always belongs to it. -/
lemma couplingSet_nonempty (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    (couplingSet μ ν).Nonempty := by
  -- Use the independent product coupling constructed in `Coupling.lean`.
  exact ⟨(Coupling.prod μ ν).toTransportPlan, Coupling.toTransportPlan_mem_couplingSet _⟩

/-- In the Polish setting, the fixed-marginal set of couplings is closed in the weak topology. -/
lemma isClosed_couplingSet [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y] (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsClosed (couplingSet μ ν) := by
  -- Each marginal map is continuous in the weak topology, so the fixed-point conditions are closed.
  simpa [couplingSet] using
    (isClosed_eq (TransportPlan.continuous_fstMarginal (X := X) (Y := Y)) continuous_const).inter
      (isClosed_eq (TransportPlan.continuous_sndMarginal (X := X) (Y := Y)) continuous_const)

/-- The family of all couplings of fixed marginals is tight. The proof combines tightness of the
two singleton marginal families with the product-complement estimate. -/
lemma isTightMeasureSet_couplingSet [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y] (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsTightMeasureSet {((π : TransportPlan X Y) : Measure (X × Y)) | π ∈ couplingSet μ ν} := by
  rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hεhalf : 0 < ε / 2 := by
    simpa using ENNReal.half_pos hε.ne'
  have hμtight : IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X)} :=
    MeasureTheory.isTightMeasureSet_singleton
  have hνtight : IsTightMeasureSet {((ν : ProbabilityMeasure Y) : Measure Y)} :=
    MeasureTheory.isTightMeasureSet_singleton
  rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hμtight hνtight
  obtain ⟨K, hKc, hKbound⟩ := hμtight (ε / 2) hεhalf
  obtain ⟨L, hLc, hLbound⟩ := hνtight (ε / 2) hεhalf
  refine ⟨K ×ˢ L, hKc.prod hLc, ?_⟩
  intro ρ hρ
  rcases hρ with ⟨π, hπ, rfl⟩
  calc
    (π : Measure (X × Y)) ((K ×ˢ L)ᶜ)
      ≤ (μ : Measure X) Kᶜ + (ν : Measure Y) Lᶜ := by
          exact TransportPlan.measure_compl_prod_le π hπ.1 hπ.2 hKc.measurableSet hLc.measurableSet
    _ ≤ ε / 2 + ε / 2 := by
          exact add_le_add (hKbound _ (by simp)) (hLbound _ (by simp))
    _ = ε := by
          simp

/-- Prokhorov compactness for the set of couplings with fixed marginals. Since the set is tight
and already closed, its closure compactness gives compactness of the set itself. -/
lemma isCompact_couplingSet [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y] (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsCompact (couplingSet μ ν) := by
  have hcompact :
      IsCompact (closure (couplingSet μ ν : Set (TransportPlan X Y))) := by
    exact isCompact_closure_of_isTightMeasureSet (isTightMeasureSet_couplingSet μ ν)
  simpa [(isClosed_couplingSet (X := X) (Y := Y) μ ν).closure_eq] using hcompact

/-- A bounded continuous nonnegative cost gives a continuous `ℝ≥0∞`-valued functional on the
space of transport plans. This is the immediate existence-ready corollary of the weak topology API
already present in `mathlib`. -/
lemma continuous_transportCostENNReal_of_boundedContinuous [TopologicalSpace X] [BorelSpace X]
    [TopologicalSpace Y] [BorelSpace Y] [OpensMeasurableSpace (X × Y)]
    (c : BoundedContinuousFunction (X × Y) ℝ≥0) :
    Continuous fun π : TransportPlan X Y ↦ transportCostENNReal (fun x y ↦ c (x, y)) π := by
  -- For bounded continuous nonnegative functions, integration against probability measures is
  -- continuous in the weak topology.
  simpa [transportCostENNReal] using
    (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction (X := X × Y) c)

/-- Portmanteau plus the layer-cake formula give a liminf inequality for nonnegative lower
semicontinuous real-valued functions, not just continuous ones. This is the analytic step used
below for lower-semicontinuous transport costs after truncation. -/
lemma lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure_of_lsc
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ} (hf : LowerSemicontinuous f)
    (h_nonneg : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ Filter.liminf (fun i ↦ μs i G) atTop) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      Filter.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i)) atTop := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall h_nonneg)
    hf.measurable.aemeasurable]
  calc
    ∫⁻ t in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ t in Set.Ioi 0, Filter.liminf (fun i ↦ (μs i) {a | t < f a}) atTop := by
          exact
            (lintegral_mono fun t ↦ h_opens _ (hf.isOpen_preimage t)).trans (le_refl _)
    _ ≤ Filter.liminf (fun i ↦ ∫⁻ t in Set.Ioi 0, (μs i) {a | t < f a}) atTop := by
          exact lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
            measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))

/-- Weak convergence of transport plans implies a liminf inequality for lower-semicontinuous
`ℝ≥0∞`-valued transport costs. The proof follows Villani's standard truncation argument:
truncate the cost to a finite lower-semicontinuous real-valued function, apply Portmanteau to
each truncation, and then let the truncation level go to infinity. -/
lemma transportCostENNReal_le_liminf_of_tendsto [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y] {c : X → Y → ℝ≥0∞}
    (hc : IsLowerSemicontinuousCost c) {πs : ℕ → TransportPlan X Y} {π : TransportPlan X Y}
    (hπs : Tendsto πs atTop (nhds π)) :
    transportCostENNReal c π ≤ Filter.liminf (fun n ↦ transportCostENNReal c (πs n)) atTop := by
  let f : X × Y → ℝ≥0∞ := fun z ↦ c z.1 z.2
  have h_opens :
      ∀ G, IsOpen G → (π : Measure (X × Y)) G ≤
        Filter.liminf (fun i ↦ (πs i : Measure (X × Y)) G) atTop :=
    fun G hG ↦ ProbabilityMeasure.le_liminf_measure_open_of_tendsto hπs hG
  have hf_meas : Measurable f := measurable_of_isLowerSemicontinuousCost hc
  have htrunc :
      ∀ N : ℕ,
        ∫⁻ z, min (N : ℝ≥0∞) (f z) ∂(π : Measure (X × Y)) ≤
          Filter.liminf (fun n ↦ transportCostENNReal c (πs n)) atTop := by
    intro N
    let g : X × Y → ℝ := fun z ↦ ENNReal.truncateToReal N (f z)
    have hg_lsc : LowerSemicontinuous g := by
      exact
        (ENNReal.continuous_truncateToReal (t := (N : ℝ≥0∞)) (by simp)).comp_lowerSemicontinuous
          hc (ENNReal.monotone_truncateToReal (t := (N : ℝ≥0∞)) (by simp))
    have hg_nonneg : 0 ≤ g := fun z ↦ ENNReal.truncateToReal_nonneg
    have hmain :=
      lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure_of_lsc hg_lsc
        hg_nonneg h_opens
    have hrewrite :
        (∫⁻ z, ENNReal.ofReal (g z) ∂(π : Measure (X × Y))) =
          ∫⁻ z, min (N : ℝ≥0∞) (f z) ∂(π : Measure (X × Y)) := by
      refine lintegral_congr_ae ?_
      filter_upwards with z
      have hmin_ne_top : min (N : ℝ≥0∞) (f z) ≠ ∞ := by
        simp
      change ENNReal.ofReal ((min (N : ℝ≥0∞) (f z)).toReal) = min (N : ℝ≥0∞) (f z)
      rw [ENNReal.ofReal_toReal hmin_ne_top]
    have hmono :
        Filter.liminf (fun n ↦ ∫⁻ z, ENNReal.ofReal (g z) ∂(πs n : Measure (X × Y))) atTop ≤
          Filter.liminf (fun n ↦ transportCostENNReal c (πs n)) atTop := by
      exact liminf_le_liminf (.of_forall fun n ↦ by
        refine (lintegral_mono fun z ↦ ?_)
        change ENNReal.ofReal ((min (N : ℝ≥0∞) (f z)).toReal) ≤ c z.1 z.2
        rw [ENNReal.ofReal_toReal (by simp : min (N : ℝ≥0∞) (f z) ≠ ∞)]
        exact min_le_right (N : ℝ≥0∞) (f z))
    rw [hrewrite] at hmain
    exact hmain.trans hmono
  have hcost_eq :
      transportCostENNReal c π = ⨆ N : ℕ, ∫⁻ z, min (N : ℝ≥0∞) (f z) ∂(π : Measure (X × Y)) := by
    rw [transportCostENNReal]
    have hsup : (fun z ↦ ⨆ N : ℕ, min (N : ℝ≥0∞) (f z)) = f := by
      funext z
      apply le_antisymm
      · exact iSup_le fun N ↦ min_le_right _ _
      · by_cases hz : f z = ∞
        · simp [f, hz, ENNReal.iSup_natCast]
        · obtain ⟨N, hN⟩ := exists_nat_gt (f z).toReal
          have hfz_le : f z ≤ (N : ℝ≥0∞) := by
            exact (ENNReal.toReal_le_toReal hz (by simp)).1 (le_of_lt hN)
          exact le_iSup_of_le N (by simp [min_eq_right hfz_le])
    rw [← lintegral_iSup (fun N ↦ (measurable_const.min hf_meas))
      (fun m n hmn z ↦ min_le_min (by exact_mod_cast hmn) le_rfl), hsup]
  calc
    transportCostENNReal c π
      = ⨆ N : ℕ, ∫⁻ z, min (N : ℝ≥0∞) (f z) ∂(π : Measure (X × Y)) := hcost_eq
    _ ≤ Filter.liminf (fun n ↦ transportCostENNReal c (πs n)) atTop := by
      exact iSup_le htrunc

/-- On Polish spaces, a lower-semicontinuous `ℝ≥0∞`-valued cost admits an optimal coupling.
This is the Villani-style existence theorem: compactness of the coupling set comes from
Prokhorov, and lower semicontinuity of the objective comes from Portmanteau after truncation. -/
theorem exists_optimalCoupling_of_isLowerSemicontinuousCost [TopologicalSpace X] [PolishSpace X]
    [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) {c : X → Y → ℝ≥0∞}
    (hc : IsLowerSemicontinuousCost c) :
    ∃ π : Coupling μ ν, ∀ ρ : Coupling μ ν,
      transportCostENNReal c π.toTransportPlan ≤ transportCostENNReal c ρ.toTransportPlan := by
  let S : Set (TransportPlan X Y) := couplingSet μ ν
  have hS_nonempty : S.Nonempty := couplingSet_nonempty μ ν
  have hS_compact : IsCompact S := isCompact_couplingSet (X := X) (Y := Y) μ ν
  let A : Set ℝ≥0∞ := (fun π : TransportPlan X Y ↦ transportCostENNReal c π) '' S
  have hA_nonempty : A.Nonempty := by
    rcases hS_nonempty with ⟨π, hπS⟩
    exact ⟨transportCostENNReal c π, ⟨π, hπS, rfl⟩⟩
  let m : ℝ≥0∞ := sInf A
  by_cases hm_top : m = ∞
  · rcases hS_nonempty with ⟨π, hπS⟩
    refine ⟨⟨π, hπS.1, hπS.2⟩, ?_⟩
    intro ρ
    have hπ_mem : transportCostENNReal c π ∈ A := ⟨π, hπS, rfl⟩
    have hρ_mem : transportCostENNReal c ρ.toTransportPlan ∈ A := ⟨ρ.toTransportPlan,
      ρ.toTransportPlan_mem_couplingSet, rfl⟩
    have hπ_cost_eq_top : transportCostENNReal c π = ∞ := by
      simpa [m, hm_top] using (sInf_le hπ_mem)
    have hρ_cost_eq_top : transportCostENNReal c ρ.toTransportPlan = ∞ := by
      simpa [m, hm_top] using (sInf_le hρ_mem)
    simp [hπ_cost_eq_top, hρ_cost_eq_top]
  · have hm_finite : m < ∞ := lt_top_iff_ne_top.mpr hm_top
    have h_lower_plan : ∀ ⦃ρ : TransportPlan X Y⦄, ρ ∈ S → m ≤ transportCostENNReal c ρ := by
      intro ρ hρS
      exact sInf_le ⟨ρ, hρS, rfl⟩
    have hchoose :
        ∀ n : ℕ, ∃ πn : TransportPlan X Y,
          πn ∈ S ∧ transportCostENNReal c πn < m + (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
      intro n
      have hε_ne_zero : (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) ≠ 0 := by
        simp
      obtain ⟨a, haA, ha_lt⟩ :=
        exists_lt_of_csInf_lt hA_nonempty (by
          simpa [m] using ENNReal.lt_add_right hm_top hε_ne_zero)
      rcases haA with ⟨πn, hπnS, rfl⟩
      exact ⟨πn, hπnS, by simpa [m] using ha_lt⟩
    choose πseq hπseq_mem hπseq_lt using hchoose
    obtain ⟨πmin, hπminS, φ, hφmono, hφtendsto⟩ :=
      hS_compact.tendsto_subseq (fun n ↦ hπseq_mem n)
    have hsubseq_tendsto :
        Tendsto (fun n ↦ transportCostENNReal c (πseq (φ n))) atTop (nhds m) := by
      have h_lower_subseq : Tendsto (fun _ : ℕ ↦ m) atTop (nhds m) := tendsto_const_nhds
      have h_upper_subseq :
          Tendsto (fun n ↦ (((φ n + 1 : ℕ) : ℝ≥0∞)⁻¹) + m) atTop (nhds m) := by
        have h_inv :
            Tendsto (fun n ↦ (((φ n + 1 : ℕ) : ℝ≥0∞)⁻¹)) atTop (nhds 0) := by
          have hφ : Tendsto φ atTop atTop := hφmono.tendsto_atTop
          exact ENNReal.tendsto_inv_nat_nhds_zero.comp ((tendsto_add_atTop_nat 1).comp hφ)
        simpa [zero_add] using h_inv.add_const m
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le h_lower_subseq h_upper_subseq ?_ ?_
      · intro n
        exact h_lower_plan (hπseq_mem (φ n))
      · intro n
        simpa [add_comm] using (hπseq_lt (φ n)).le
    have hcost_min :
        transportCostENNReal c πmin ≤ m := by
      have hliminf :=
        transportCostENNReal_le_liminf_of_tendsto (X := X) (Y := Y) hc
          (πs := fun n ↦ πseq (φ n)) hφtendsto
      rw [hsubseq_tendsto.liminf_eq] at hliminf
      exact hliminf
    refine ⟨⟨πmin, hπminS.1, hπminS.2⟩, ?_⟩
    intro ρ
    exact hcost_min.trans (h_lower_plan ρ.toTransportPlan_mem_couplingSet)

/-- On Polish spaces, a bounded continuous nonnegative cost admits an optimal coupling. -/
theorem exists_optimalCoupling_of_boundedContinuous [TopologicalSpace X] [PolishSpace X]
    [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : BoundedContinuousFunction (X × Y) ℝ≥0) :
    ∃ π : Coupling μ ν, ∀ ρ : Coupling μ ν,
      transportCostENNReal (fun x y ↦ c (x, y)) π.toTransportPlan ≤
        transportCostENNReal (fun x y ↦ c (x, y)) ρ.toTransportPlan := by
  let S : Set (TransportPlan X Y) := couplingSet μ ν
  have hS_nonempty : S.Nonempty := couplingSet_nonempty μ ν
  have hS_compact : IsCompact S := isCompact_couplingSet (X := X) (Y := Y) μ ν
  have hcont :
      Continuous fun π : TransportPlan X Y ↦ transportCostENNReal (fun x y ↦ c (x, y)) π :=
    continuous_transportCostENNReal_of_boundedContinuous (X := X) (Y := Y) c
  obtain ⟨π, hπS, hπmin⟩ := hS_compact.exists_isMinOn hS_nonempty hcont.continuousOn
  refine ⟨⟨π, hπS.1, hπS.2⟩, ?_⟩
  intro ρ
  exact hπmin ρ.toTransportPlan_mem_couplingSet

end OptimalTransport
