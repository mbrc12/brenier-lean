import OptimalTransport.Existence
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Logic.Equiv.Fin.Rotate

namespace OptimalTransport

open MeasureTheory
open Filter
open scoped BigOperators

/-!
This file introduces cyclical monotonicity and the first optimality-to-geometry theorem.

For the direct perturbation argument, the real point is continuity, not global boundedness.
Indeed, once one has a strict cycle gap at finitely many support points, continuity lets one shrink
to small product neighborhoods on which the same strict inequality still holds uniformly. This is
the local step that later lets finite-cost assumptions replace any global boundedness hypothesis.

The main definition is:

* `CCyclicallyMonotone c Γ`: the usual finite-cycle inequality for a set `Γ ⊆ X × Y`.

The main local theorem proved in this file is:

* if a continuous cost has a strict cycle gap at a finite family of pairwise distinct points,
  then there are pairwise disjoint open rectangles around those points on which the same strict
  cycle gap persists pointwise.
-/

variable {X Y : Type*}

/-- The cycle-gap functional associated to a finite family of points in `X × Y`. Positive values
detect failure of `c`-cyclical monotonicity. -/
def cycleGap (c : X → Y → ℝ) {n : ℕ} (p : Fin (n + 1) → X × Y) : ℝ :=
  (∑ i, c (p i).1 (p i).2) - ∑ i, c (p i).1 (p (i + 1)).2

/-- A set `Γ ⊆ X × Y` is `c`-cyclically monotone if every finite cycle of pairwise distinct points
in `Γ` satisfies the standard transport inequality. We index cycles by `Fin (n + 1)` so the family
is never empty and the successor `i + 1` is automatically taken modulo the cycle length. -/
def CCyclicallyMonotone (c : X → Y → ℝ) (Γ : Set (X × Y)) : Prop :=
  ∀ n (p : Fin (n + 1) → X × Y), Function.Injective p →
    (∀ i, p i ∈ Γ) →
      (∑ i, c (p i).1 (p i).2) ≤ ∑ i, c (p i).1 (p (i + 1)).2

/-- Cyclical monotonicity is monotone with respect to enlarging the ambient set. -/
lemma CCyclicallyMonotone.mono {c : X → Y → ℝ} {Γ₁ Γ₂ : Set (X × Y)}
    (hΓ : Γ₁ ⊆ Γ₂) (h : CCyclicallyMonotone c Γ₂) :
    CCyclicallyMonotone c Γ₁ := by
  intro n p hp hmem
  exact h n p hp fun i ↦ hΓ (hmem i)

/-- The empty set is `c`-cyclically monotone for every cost. -/
lemma cCyclicallyMonotone_empty (c : X → Y → ℝ) :
    CCyclicallyMonotone c (∅ : Set (X × Y)) := by
  intro n p hp hmem
  simpa using hmem 0

/-- Rewriting a Brenier-type cost by separating the `x`-only and `y`-only terms reduces
`c`-cyclical monotonicity to the pairing inequality. This is the algebraic specialization used
later for quadratic costs. -/
lemma cCyclicallyMonotone_of_pairing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b : E → ℝ} {κ : ℝ} {Γ : Set (E × E)}
    (hΓ : CCyclicallyMonotone (fun x y ↦ a x + b y - κ * inner ℝ x y) Γ) :
    ∀ n (p : Fin (n + 1) → E × E), Function.Injective p → (∀ i, p i ∈ Γ) →
      κ * (∑ i, inner ℝ (p i).1 (p i).2) ≥
        κ * (∑ i, inner ℝ (p i).1 (p (i + 1)).2) := by
  intro n p hp hmem
  have h := hΓ n p hp hmem
  have hb :
      (∑ i, b (p (i + 1)).2) = ∑ i, b (p i).2 := by
    simpa [Function.comp] using
      (Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) (fun i : Fin (n + 1) ↦ b (p i).2))
  have h' :
      (∑ i, a (p i).1) + (∑ i, b (p i).2) - κ * (∑ i, inner ℝ (p i).1 (p i).2) ≤
        (∑ i, a (p i).1) + (∑ i, b (p (i + 1)).2) - κ * (∑ i, inner ℝ (p i).1 (p (i + 1)).2) := by
    simpa [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, add_assoc,
      add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using h
  rw [hb] at h'
  linarith

section LocalGap

variable [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]

omit [T2Space X] [T2Space Y] in
/-- The cycle-gap functional is continuous when the cost is continuous. -/
lemma continuous_cycleGap {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {n : ℕ} :
    Continuous fun p : Fin (n + 1) → X × Y ↦ cycleGap c p := by
  unfold cycleGap
  refine (continuous_finset_sum _ fun i _ ↦ hc.comp (continuous_apply i)).sub ?_
  refine continuous_finset_sum _ fun i _ ↦ ?_
  have hpair : Continuous fun z : (X × Y) × (X × Y) ↦ (z.1.1, z.2.2) := by
    fun_prop
  have hcoords : Continuous fun p : Fin (n + 1) → X × Y ↦ (p i, p (i + 1)) :=
    (continuous_apply i).prodMk (continuous_apply (i + 1))
  exact hc.comp (hpair.comp hcoords)

/-- A strict violation of cyclical monotonicity at finitely many distinct points persists on small
pairwise disjoint open rectangles around those points. This is the continuity-based local step in
the direct perturbation proof, and it is precisely where global boundedness is unnecessary. -/
lemma exists_pairwiseDisjoint_open_rectangles_of_cycleGap_pos
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2) {n : ℕ}
    {p : Fin (n + 1) → X × Y} (hp : Function.Injective p) (hgap : 0 < cycleGap c p) :
    ∃ U : Fin (n + 1) → Set X, ∃ V : Fin (n + 1) → Set Y,
      (∀ i, IsOpen (U i) ∧ (p i).1 ∈ U i) ∧
      (∀ i, IsOpen (V i) ∧ (p i).2 ∈ V i) ∧
      (Set.Pairwise (Set.univ : Set (Fin (n + 1)))
        (Function.onFun Disjoint fun i => U i ×ˢ V i)) ∧
      ∀ q : Fin (n + 1) → X × Y, (∀ i, q i ∈ U i ×ˢ V i) → 0 < cycleGap c q := by
  let F : (Fin (n + 1) → X × Y) → ℝ := cycleGap c
  have hF : Continuous F := continuous_cycleGap hc
  let S : Set (Fin (n + 1) → X × Y) := {q | 0 < F q}
  have hSopen : IsOpen S := isOpen_lt continuous_const hF
  have hpS : p ∈ S := hgap
  obtain ⟨C, hC, hCS⟩ := (isOpen_pi_iff' (s := S)).mp hSopen p hpS
  let R : Set (X × Y) := Set.range p
  have hRfin : R.Finite := Set.finite_range p
  obtain ⟨W, hWmem, hWdisj⟩ := hRfin.t2_separation
  have hCW_mem : ∀ i, C i ∩ W (p i) ∈ nhds (p i) := by
    intro i
    exact inter_mem
      (IsOpen.mem_nhds (hC i).1 (hC i).2)
      (IsOpen.mem_nhds (hWmem (p i)).2 (hWmem (p i)).1)
  choose U V hUopen hpU hVopen hpV hUVsub using
    fun i ↦ mem_nhds_prod_iff'.mp (hCW_mem i)
  refine ⟨U, V, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hUopen i, hpU i⟩
  · intro i
    exact ⟨hVopen i, hpV i⟩
  · intro i _ j _ hij
    refine (hWdisj ?_ ?_ ?_).mono
      ((hUVsub i).trans Set.inter_subset_right)
      ((hUVsub j).trans Set.inter_subset_right)
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩
    · exact hp.ne hij
  · intro q hq
    have hqC : q ∈ Set.univ.pi C := by
      intro i hi
      exact (hUVsub i (hq i)).1
    exact hCS hqC

/-- The auxiliary control functional used in the perturbation argument: it records the total size
of the diagonal costs `c (xᵢ, yᵢ)` and the cyclic cross costs `c (xᵢ, yᵢ₊₁)` for a tuple
`q : Fin (n + 1) → X × Y`. Bounding this quantity bounds every individual diagonal and cyclic term,
which is the local substitute for a global boundedness assumption on `c`. -/
def localCostControl (c : X → Y → ℝ) {n : ℕ} (q : Fin (n + 1) → X × Y) : ℝ :=
  (∑ i, |c (q i).1 (q i).2|) + ∑ i, |c (q i).1 (q (i + 1)).2|

omit [T2Space X] [T2Space Y] in
/-- The local cost-control functional is continuous for continuous costs. -/
lemma continuous_localCostControl {c : X → Y → ℝ}
    (hc : Continuous fun z : X × Y ↦ c z.1 z.2) {n : ℕ} :
    Continuous fun q : Fin (n + 1) → X × Y ↦ localCostControl c q := by
  unfold localCostControl
  refine (continuous_finset_sum _ fun i _ ↦ ?_).add ?_
  · exact (hc.comp (continuous_apply i)).abs
  · refine continuous_finset_sum _ fun i _ ↦ ?_
    have hpair : Continuous fun z : (X × Y) × (X × Y) ↦ (z.1.1, z.2.2) := by
      fun_prop
    have hcoords : Continuous fun q : Fin (n + 1) → X × Y ↦ (q i, q (i + 1)) :=
      (continuous_apply i).prodMk (continuous_apply (i + 1))
    exact (hc.comp (hpair.comp hcoords)).abs

/-- The local rectangles witnessing a strict cycle gap can be chosen so that the cost is also
uniformly bounded on every diagonal rectangle `Uᵢ × Vᵢ` and on every cyclic rectangle
`Uᵢ × Vᵢ₊₁`. This is the exact place where continuity replaces a global boundedness assumption:
later, once `∫ c dπ < ∞` is known for the original plan, these local bounds are enough to show the
newly inserted competitor pieces still have finite cost. -/
lemma exists_pairwiseDisjoint_open_rectangles_of_cycleGap_pos_with_costControl
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2) {n : ℕ}
    {p : Fin (n + 1) → X × Y} (hp : Function.Injective p) (hgap : 0 < cycleGap c p) :
    ∃ U : Fin (n + 1) → Set X, ∃ V : Fin (n + 1) → Set Y, ∃ B : ℝ,
      0 ≤ B ∧
      (∀ i, IsOpen (U i) ∧ (p i).1 ∈ U i) ∧
      (∀ i, IsOpen (V i) ∧ (p i).2 ∈ V i) ∧
      (Set.Pairwise (Set.univ : Set (Fin (n + 1)))
        (Function.onFun Disjoint fun i => U i ×ˢ V i)) ∧
      (∀ q : Fin (n + 1) → X × Y, (∀ i, q i ∈ U i ×ˢ V i) → 0 < cycleGap c q) ∧
      (∀ i {x y}, x ∈ U i → y ∈ V i → |c x y| < B) ∧
      (∀ i {x y}, x ∈ U i → y ∈ V (i + 1) → |c x y| < B) := by
  let F : (Fin (n + 1) → X × Y) → ℝ := cycleGap c
  let G : (Fin (n + 1) → X × Y) → ℝ := localCostControl c
  have hF : Continuous F := continuous_cycleGap hc
  have hG : Continuous G := continuous_localCostControl hc
  let B : ℝ := G p + 1
  have hBpos : 0 ≤ B := by
    have hGp_nonneg : 0 ≤ G p := by
      dsimp [G, localCostControl]
      exact add_nonneg
        (Finset.sum_nonneg fun i _ ↦ abs_nonneg (c (p i).1 (p i).2))
        (Finset.sum_nonneg fun i _ ↦ abs_nonneg (c (p i).1 (p (i + 1)).2))
    linarith
  let S : Set (Fin (n + 1) → X × Y) := {q | 0 < F q ∧ G q < B}
  have hSopen : IsOpen S := (isOpen_lt continuous_const hF).inter
    (isOpen_lt hG continuous_const)
  have hpS : p ∈ S := by
    refine ⟨hgap, ?_⟩
    dsimp [B]
    linarith
  obtain ⟨C, hC, hCS⟩ := (isOpen_pi_iff' (s := S)).mp hSopen p hpS
  let R : Set (X × Y) := Set.range p
  have hRfin : R.Finite := Set.finite_range p
  obtain ⟨W, hWmem, hWdisj⟩ := hRfin.t2_separation
  have hCW_mem : ∀ i, C i ∩ W (p i) ∈ nhds (p i) := by
    intro i
    exact inter_mem
      (IsOpen.mem_nhds (hC i).1 (hC i).2)
      (IsOpen.mem_nhds (hWmem (p i)).2 (hWmem (p i)).1)
  choose U V hUopen hpU hVopen hpV hUVsub using
    fun i ↦ mem_nhds_prod_iff'.mp (hCW_mem i)
  have hgapRect :
      ∀ q : Fin (n + 1) → X × Y, (∀ i, q i ∈ U i ×ˢ V i) → 0 < cycleGap c q := by
    intro q hq
    have hqC : q ∈ Set.univ.pi C := by
      intro i hi
      exact (hUVsub i (hq i)).1
    exact (hCS hqC).1
  have hdiagBound :
      ∀ i {x y}, x ∈ U i → y ∈ V i → |c x y| < B := by
    intro i x y hx hy
    let q : Fin (n + 1) → X × Y := Function.update p i (x, y)
    have hq_mem : ∀ j, q j ∈ U j ×ˢ V j := by
      intro j
      by_cases hij : j = i
      · subst hij
        simpa [q] using And.intro hx hy
      · simp [q, hij, hpU, hpV]
    have hqC : q ∈ Set.univ.pi C := by
      intro j hj
      exact (hUVsub j (hq_mem j)).1
    have hq_bound : G q < B := (hCS hqC).2
    have hdiag :
        |c (q i).1 (q i).2| ≤ ∑ j, |c (q j).1 (q j).2| := by
      exact Finset.single_le_sum
        (fun j _ ↦ abs_nonneg (c (q j).1 (q j).2))
        (by simp)
    have hsum :
        ∑ j, |c (q j).1 (q j).2| ≤ G q := by
      dsimp [G, localCostControl]
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg fun j _ ↦ abs_nonneg (c (q j).1 (q (j + 1)).2))
    have hterm : |c x y| ≤ G q := by
      simpa [q] using hdiag.trans hsum
    exact lt_of_le_of_lt hterm hq_bound
  have hcrossBound :
      ∀ i {x y}, x ∈ U i → y ∈ V (i + 1) → |c x y| < B := by
    intro i x y hx hy
    by_cases hii : i + 1 = i
    · have hy' : y ∈ V i := by simpa [hii] using hy
      exact hdiagBound i hx hy'
    · let q : Fin (n + 1) → X × Y :=
        Function.update (Function.update p i (x, (p i).2)) (i + 1) ((p (i + 1)).1, y)
      have hne : i ≠ i + 1 := by
        intro h
        exact hii h.symm
      have hq_mem : ∀ j, q j ∈ U j ×ˢ V j := by
        intro j
        by_cases hji : j = i
        · subst j
          constructor
          · simpa [q, hne] using hx
          · have hpi : (p i).2 ∈ V i := hpV i
            simpa [q, hne] using hpi
        · by_cases hjnext : j = i + 1
          · subst j
            simp [q, hy, hpU]
          · simp [q, hji, hjnext, hpU, hpV]
      have hqC : q ∈ Set.univ.pi C := by
        intro j hj
        exact (hUVsub j (hq_mem j)).1
      have hq_bound : G q < B := (hCS hqC).2
      have hcross :
          |c (q i).1 (q (i + 1)).2| ≤ ∑ j, |c (q j).1 (q (j + 1)).2| := by
        exact Finset.single_le_sum
          (fun j _ ↦ abs_nonneg (c (q j).1 (q (j + 1)).2))
          (by simp)
      have hsum :
          ∑ j, |c (q j).1 (q (j + 1)).2| ≤ G q := by
        dsimp [G, localCostControl]
        exact le_add_of_nonneg_left
          (Finset.sum_nonneg fun j _ ↦ abs_nonneg (c (q j).1 (q j).2))
      have hterm : |c x y| ≤ G q := by
        simpa [q, hne] using hcross.trans hsum
      exact lt_of_le_of_lt hterm hq_bound
  refine ⟨U, V, B, hBpos, ?_, ?_, ?_, hgapRect, hdiagBound, hcrossBound⟩
  · intro i
    exact ⟨hUopen i, hpU i⟩
  · intro i
    exact ⟨hVopen i, hpV i⟩
  · intro i _ j _ hij
    refine (hWdisj ?_ ?_ ?_).mono
      ((hUVsub i).trans Set.inter_subset_right)
      ((hUVsub j).trans Set.inter_subset_right)
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩
    · exact hp.ne hij

/-- The full local data extracted from a strict cycle-gap witness.

This packages exactly the information needed later in the perturbation proof:

* pairwise disjoint open rectangles around the witness points;
* persistence of the strict cycle gap on those rectangles;
* a single uniform bound for the diagonal and cyclic cross costs on those rectangles.

The point of introducing this structure is to keep the later global competitor construction from
repeating the same long tuple of hypotheses. -/
structure CycleGapNeighborhoodData {n : ℕ} (c : X → Y → ℝ) (p : Fin (n + 1) → X × Y) where
  /-- The source-side neighborhoods. -/
  U : Fin (n + 1) → Set X
  /-- The target-side neighborhoods. -/
  V : Fin (n + 1) → Set Y
  /-- A uniform local bound for the cost on the relevant rectangles. -/
  B : ℝ
  /-- The local bound is nonnegative. -/
  B_nonneg : 0 ≤ B
  /-- Each witness point lies in its source neighborhood, and that neighborhood is open. -/
  isOpen_mem_U : ∀ i, IsOpen (U i) ∧ (p i).1 ∈ U i
  /-- Each witness point lies in its target neighborhood, and that neighborhood is open. -/
  isOpen_mem_V : ∀ i, IsOpen (V i) ∧ (p i).2 ∈ V i
  /-- The rectangles are pairwise disjoint, so later restricted pieces do not overlap. -/
  pairwiseDisjoint :
    Set.Pairwise (Set.univ : Set (Fin (n + 1)))
      (Function.onFun Disjoint fun i => U i ×ˢ V i)
  /-- Every tuple sampled from the local rectangles still has positive cycle gap. -/
  gap_pos :
    ∀ q : Fin (n + 1) → X × Y, (∀ i, q i ∈ U i ×ˢ V i) → 0 < cycleGap c q
  /-- The cost is uniformly bounded on every diagonal rectangle `Uᵢ × Vᵢ`. -/
  diag_bound :
    ∀ i {x y}, x ∈ U i → y ∈ V i → |c x y| < B
  /-- The cost is uniformly bounded on every cyclic rectangle `Uᵢ × Vᵢ₊₁`. -/
  cross_bound :
    ∀ i {x y}, x ∈ U i → y ∈ V (i + 1) → |c x y| < B

/-- Package the output of
`exists_pairwiseDisjoint_open_rectangles_of_cycleGap_pos_with_costControl`
as a single reusable object.

This is the clean endpoint of Step 4A: once a strict cycle-gap witness is fixed, all later parts of
the perturbation proof can refer to one object `hdata` instead of repeatedly unpacking a long
nested tuple of neighborhoods, openness, disjointness, and local bounds. -/
lemma exists_cycleGapNeighborhoodData_of_cycleGap_pos
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2) {n : ℕ}
    {p : Fin (n + 1) → X × Y} (hp : Function.Injective p) (hgap : 0 < cycleGap c p) :
    Nonempty (CycleGapNeighborhoodData c p) := by
  rcases exists_pairwiseDisjoint_open_rectangles_of_cycleGap_pos_with_costControl hc hp hgap with
    ⟨U, V, B, hB, hU, hV, hdisj, hgapRect, hdiag, hcross⟩
  refine ⟨
    { U := U
      V := V
      B := B
      B_nonneg := hB
      isOpen_mem_U := hU
      isOpen_mem_V := hV
      pairwiseDisjoint := hdisj
      gap_pos := hgapRect
      diag_bound := hdiag
      cross_bound := hcross }⟩

end LocalGap

section ProductMeasureHelpers

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
variable {μ : ∀ i, ProbabilityMeasure (Ω i)}
variable {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]

/-- Under a finite product probability measure, two functions depending on distinct coordinates are
independent. After pushing forward those coordinates by measurable maps, the resulting pair law is
the product of the individual pushed-forward laws. This is the exact independence calculation used
for the shifted competitor pieces in the cyclical-monotonicity proof. -/
  lemma map_pair_eval_eq_prod_map_eval
    {i j : ι} (hij : i ≠ j) {f : Ω i → β} {g : Ω j → γ}
    (hf : AEMeasurable f (μ i)) (hg : AEMeasurable g (μ j)) :
    (Measure.pi fun k ↦ ((μ k : ProbabilityMeasure (Ω k)) : Measure (Ω k))).map
        (fun ω ↦ (f (ω i), g (ω j))) =
      (((μ i : ProbabilityMeasure (Ω i)) : Measure (Ω i)).map f).prod
      (((μ j : ProbabilityMeasure (Ω j)) : Measure (Ω j)).map g) := by
  let piMeasure : Measure (∀ k, Ω k) :=
    Measure.pi fun k ↦ ((μ k : ProbabilityMeasure (Ω k)) : Measure (Ω k))
  have hindep_coords :
      (fun ω : ∀ k, Ω k ↦ ω i) ⟂ᵢ[piMeasure] (fun ω : ∀ k, Ω k ↦ ω j) := by
    let hInd :
        iIndepFun (fun k ω ↦ ω k) piMeasure :=
      iIndepFun_pi (μ := fun k ↦ ((μ k : ProbabilityMeasure (Ω k)) : Measure (Ω k)))
        (fun k ↦ aemeasurable_id)
    exact hInd.indepFun hij
  have hf_map : AEMeasurable f (piMeasure.map (fun ω : ∀ k, Ω k ↦ ω i)) := by
    rw [show piMeasure.map (fun ω : ∀ k, Ω k ↦ ω i) =
        ((μ i : ProbabilityMeasure (Ω i)) : Measure (Ω i)) by
          simpa [piMeasure] using
            (measurePreserving_eval
              (fun k ↦ ((μ k : ProbabilityMeasure (Ω k)) : Measure (Ω k))) i).map_eq]
    exact hf
  have hg_map : AEMeasurable g (piMeasure.map (fun ω : ∀ k, Ω k ↦ ω j)) := by
    rw [show piMeasure.map (fun ω : ∀ k, Ω k ↦ ω j) =
        ((μ j : ProbabilityMeasure (Ω j)) : Measure (Ω j)) by
          simpa [piMeasure] using
            (measurePreserving_eval
              (fun k ↦ ((μ k : ProbabilityMeasure (Ω k)) : Measure (Ω k))) j).map_eq]
    exact hg
  have hf_comp : AEMeasurable (fun ω : ∀ k, Ω k ↦ f (ω i)) piMeasure := by
    exact hf.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval
        (fun k ↦ ((μ k : ProbabilityMeasure (Ω k)) : Measure (Ω k))) i)
  have hg_comp : AEMeasurable (fun ω : ∀ k, Ω k ↦ g (ω j)) piMeasure := by
    exact hg.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval
        (fun k ↦ ((μ k : ProbabilityMeasure (Ω k)) : Measure (Ω k))) j)
  have hindep_maps :
      (fun ω : ∀ k, Ω k ↦ f (ω i)) ⟂ᵢ[piMeasure] (fun ω : ∀ k, Ω k ↦ g (ω j)) := by
    exact hindep_coords.comp₀
      ((measurable_pi_apply i).aemeasurable)
      ((measurable_pi_apply j).aemeasurable)
      hf_map
      hg_map
  change piMeasure.map (fun ω ↦ (f (ω i), g (ω j))) =
    (((μ i : ProbabilityMeasure (Ω i)) : Measure (Ω i)).map f).prod
      (((μ j : ProbabilityMeasure (Ω j)) : Measure (Ω j)).map g)
  have hmap_left :
      piMeasure.map (fun ω : ∀ k, Ω k ↦ f (ω i)) =
        (((μ i : ProbabilityMeasure (Ω i)) : Measure (Ω i)).map f) := by
    calc
      piMeasure.map (fun ω : ∀ k, Ω k ↦ f (ω i))
        = (piMeasure.map (fun ω : ∀ k, Ω k ↦ ω i)).map f := by
            symm
            exact AEMeasurable.map_map_of_aemeasurable hf_map
              ((measurable_pi_apply i).aemeasurable)
      _ = (((μ i : ProbabilityMeasure (Ω i)) : Measure (Ω i)).map f) := by
            rw [show piMeasure.map (fun ω : ∀ k, Ω k ↦ ω i) =
                ((μ i : ProbabilityMeasure (Ω i)) : Measure (Ω i)) by
                  simpa [piMeasure] using
                    (measurePreserving_eval
                      (fun k ↦ ((μ k : ProbabilityMeasure (Ω k)) : Measure (Ω k))) i).map_eq]
  have hmap_right :
      piMeasure.map (fun ω : ∀ k, Ω k ↦ g (ω j)) =
        (((μ j : ProbabilityMeasure (Ω j)) : Measure (Ω j)).map g) := by
    calc
      piMeasure.map (fun ω : ∀ k, Ω k ↦ g (ω j))
        = (piMeasure.map (fun ω : ∀ k, Ω k ↦ ω j)).map g := by
            symm
            exact AEMeasurable.map_map_of_aemeasurable hg_map
              ((measurable_pi_apply j).aemeasurable)
      _ = (((μ j : ProbabilityMeasure (Ω j)) : Measure (Ω j)).map g) := by
            rw [show piMeasure.map (fun ω : ∀ k, Ω k ↦ ω j) =
                ((μ j : ProbabilityMeasure (Ω j)) : Measure (Ω j)) by
                  simpa [piMeasure] using
                    (measurePreserving_eval
                      (fun k ↦ ((μ k : ProbabilityMeasure (Ω k)) : Measure (Ω k))) j).map_eq]
  calc
    piMeasure.map (fun ω ↦ (f (ω i), g (ω j)))
      = (piMeasure.map (fun ω : ∀ k, Ω k ↦ f (ω i))).prod
          (piMeasure.map (fun ω : ∀ k, Ω k ↦ g (ω j))) := by
            exact (indepFun_iff_map_prod_eq_prod_map_map hf_comp hg_comp).1 hindep_maps
    _ = (((μ i : ProbabilityMeasure (Ω i)) : Measure (Ω i)).map f).prod
          (((μ j : ProbabilityMeasure (Ω j)) : Measure (Ω j)).map g) := by
            rw [hmap_left, hmap_right]

end ProductMeasureHelpers

section MeasureReplacementHelpers

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace Measure

/-- Pushforward commutes with subtraction of finite measures when the subtrahend is dominated by
the minuend. This is the marginal-calculus lemma used for the replacement competitor in the proof
of cyclical monotonicity. -/
lemma map_sub_of_le {μ ν : Measure α} [IsFiniteMeasure ν] (hνμ : ν ≤ μ)
    {f : α → β} (hf : Measurable f) :
    Measure.map f (μ - ν) = Measure.map f μ - Measure.map f ν := by
  ext s hs
  calc
    Measure.map f (μ - ν) s = (μ - ν) (f ⁻¹' s) := Measure.map_apply hf hs
    _ = μ (f ⁻¹' s) - ν (f ⁻¹' s) := Measure.sub_apply (hf hs) hνμ
    _ = (Measure.map f μ - Measure.map f ν) s := by
          symm
          simpa [Measure.map_apply hf hs, Measure.map_apply hf hs] using
            (Measure.sub_apply hs (Measure.map_mono hνμ hf))

/-- The first marginal commutes with subtraction of finite measures under domination. -/
lemma fst_sub_of_le {μ ν : Measure (α × β)} [IsFiniteMeasure ν] (hνμ : ν ≤ μ) :
    (μ - ν).fst = μ.fst - ν.fst := by
  simpa [Measure.fst] using Measure.map_sub_of_le (μ := μ) (ν := ν) hνμ measurable_fst

/-- The second marginal commutes with subtraction of finite measures under domination. -/
lemma snd_sub_of_le {μ ν : Measure (α × β)} [IsFiniteMeasure ν] (hνμ : ν ≤ μ) :
    (μ - ν).snd = μ.snd - ν.snd := by
  simpa [Measure.snd] using Measure.map_sub_of_le (μ := μ) (ν := ν) hνμ measurable_snd

end Measure

namespace FiniteMeasure

/-- A nonzero normalized restriction is almost surely contained in the restricting set. -/
lemma ae_mem_of_normalize_restrict [Nonempty α] {μ : FiniteMeasure α} {s : Set α}
    (hs : MeasurableSet s)
    (hμs : μ.restrict s ≠ 0) :
    ∀ᵐ x ∂((μ.restrict s).normalize : Measure α), x ∈ s := by
  let m : NNReal := (μ.restrict s).mass
  have hself :
      ((μ.restrict s).normalize : Measure α) = m⁻¹ • (μ.restrict s : Measure α) := by
    simpa only [m] using (μ.restrict s).toMeasure_normalize_eq_of_nonzero hμs
  have h_ac :
      ((μ.restrict s).normalize : Measure α) ≪ (μ.restrict s : Measure α) := by
    rw [hself]
    exact Measure.smul_absolutelyContinuous
  have hs_restrict : ∀ᵐ x ∂(μ.restrict s : Measure α), x ∈ s := by
    rw [FiniteMeasure.restrict_measure_eq]
    exact self_mem_ae_restrict (μ := (μ : Measure α)) hs
  exact h_ac.ae_le hs_restrict

end FiniteMeasure

end MeasureReplacementHelpers

section SupportRectangleHelpers

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace FiniteMeasure

/-- If a point lies in the support of a finite measure, then restricting to any open neighborhood of
that point produces a nonzero finite measure. This is the positivity input for the normalized local
pieces in the perturbation argument. -/
lemma restrict_nonzero_of_mem_support_of_isOpen [TopologicalSpace α]
    {μ : FiniteMeasure α} {s : Set α} {x : α}
    (hx : x ∈ (μ : Measure α).support) (hs : IsOpen s) (hxs : x ∈ s) :
    μ.restrict s ≠ 0 := by
  have hpos : 0 < ((μ : Measure α) s) := by
    exact (Measure.mem_support_iff_forall x).1 hx s (hs.mem_nhds hxs)
  have hpos' : 0 < μ s := by
    exact ENNReal.coe_pos.1 (by simpa using hpos)
  rw [← FiniteMeasure.mass_nonzero_iff, FiniteMeasure.restrict_mass]
  exact hpos'.ne'

end FiniteMeasure

namespace Measure

/-- Almost-sure membership in a product set implies almost-sure first-coordinate membership in the
corresponding first marginal. -/
lemma ae_fst_mem_of_ae_mem_prod {μ : Measure (α × β)} {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (h : ∀ᵐ z ∂μ, z ∈ s ×ˢ t) :
    ∀ᵐ x ∂μ.fst, x ∈ s := by
  have h' : ∀ᵐ z ∂μ, z.1 ∈ s := h.mono fun z hz ↦ hz.1
  exact (ae_map_iff measurable_fst.aemeasurable hs).2 h'

/-- Almost-sure membership in a product set implies almost-sure second-coordinate membership in the
corresponding second marginal. -/
lemma ae_snd_mem_of_ae_mem_prod {μ : Measure (α × β)} {s : Set α} {t : Set β}
    (ht : MeasurableSet t) (h : ∀ᵐ z ∂μ, z ∈ s ×ˢ t) :
    ∀ᵐ y ∂μ.snd, y ∈ t := by
  have h' : ∀ᵐ z ∂μ, z.2 ∈ t := h.mono fun z hz ↦ hz.2
  exact (ae_map_iff measurable_snd.aemeasurable ht).2 h'

end Measure

end SupportRectangleHelpers

section NormalizedRectangleHelpers

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

namespace FiniteMeasure

/-- A nonzero normalized restriction to a measurable rectangle is almost surely contained in that
rectangle. -/
lemma ae_mem_prod_of_normalize_restrict {μ : FiniteMeasure (X × Y)} {U : Set X} {V : Set Y}
    [Nonempty (X × Y)]
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hμUV : μ.restrict (U ×ˢ V) ≠ 0) :
    ∀ᵐ z ∂((μ.restrict (U ×ˢ V)).normalize : Measure (X × Y)), z ∈ U ×ˢ V := by
  exact ae_mem_of_normalize_restrict (hs := hU.prod hV) hμUV

/-- The first marginal of a normalized rectangular restriction is concentrated on the first factor
of the rectangle. -/
lemma fst_ae_mem_of_normalize_restrict_prod {μ : FiniteMeasure (X × Y)} {U : Set X} {V : Set Y}
    [Nonempty (X × Y)]
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hμUV : μ.restrict (U ×ˢ V) ≠ 0) :
    ∀ᵐ x ∂((TransportPlan.fst
      ((μ.restrict (U ×ˢ V)).normalize : ProbabilityMeasure (X × Y)) : ProbabilityMeasure X) :
      Measure X), x ∈ U := by
  exact Measure.ae_fst_mem_of_ae_mem_prod hU (ae_mem_prod_of_normalize_restrict hU hV hμUV)

/-- The second marginal of a normalized rectangular restriction is concentrated on the second
factor of the rectangle. -/
lemma snd_ae_mem_of_normalize_restrict_prod {μ : FiniteMeasure (X × Y)} {U : Set X} {V : Set Y}
    [Nonempty (X × Y)]
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hμUV : μ.restrict (U ×ˢ V) ≠ 0) :
    ∀ᵐ y ∂((TransportPlan.snd
      ((μ.restrict (U ×ˢ V)).normalize : ProbabilityMeasure (X × Y)) : ProbabilityMeasure Y) :
      Measure Y), y ∈ V := by
  exact Measure.ae_snd_mem_of_ae_mem_prod hV (ae_mem_prod_of_normalize_restrict hU hV hμUV)

end FiniteMeasure

namespace TransportPlan

/-- If the marginals of a product plan are almost surely contained in `U` and `V`, then the whole
product plan is almost surely contained in `U × V`. -/
lemma ae_mem_prod_of_prod {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {U : Set X} {V : Set Y} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hμ : ∀ᵐ x ∂(μ : Measure X), x ∈ U) (hν : ∀ᵐ y ∂(ν : Measure Y), y ∈ V) :
    ∀ᵐ z ∂((μ.prod ν : TransportPlan X Y) : Measure (X × Y)), z ∈ U ×ˢ V := by
  have hU0 : (μ : Measure X) Uᶜ = 0 := by
    rw [ae_iff] at hμ
    simpa using hμ
  have hV0 : (ν : Measure Y) Vᶜ = 0 := by
    rw [ae_iff] at hν
    simpa using hν
  have hcompl :
      ((μ.prod ν : TransportPlan X Y) : Measure (X × Y)) ((U ×ˢ V)ᶜ) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      ((μ.prod ν : TransportPlan X Y) : Measure (X × Y)) ((U ×ˢ V)ᶜ)
        ≤ (μ : Measure X) Uᶜ + (ν : Measure Y) Vᶜ := by
            exact Coupling.measure_compl_prod_le (π := Coupling.prod μ ν) hU hV
      _ = 0 := by rw [hU0, hV0, zero_add]
  rw [ae_iff]
  convert hcompl using 1

end TransportPlan

end NormalizedRectangleHelpers

section LocalPieces

variable [MeasurableSpace X] [MeasurableSpace Y] [Nonempty (X × Y)]
  [TopologicalSpace X] [TopologicalSpace Y]

open scoped NNReal

/-- The finite local piece cut from the transport plan by restricting to the rectangle
`Uᵢ × Vᵢ` coming from the local cycle-gap data. These are the diagonal pieces that will later be
partially removed from the original plan. -/
noncomputable def localRestrictedPiece {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) :
    FiniteMeasure (X × Y) :=
  π.toTransportPlan.toFiniteMeasure.restrict (hdata.U i ×ˢ hdata.V i)

/-- The normalized probability version of `localRestrictedPiece`. These are the local laws that
feed the finite product construction in the perturbation argument. -/
noncomputable def localNormalizedPiece {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) :
    ProbabilityMeasure (X × Y) :=
  (localRestrictedPiece π hdata i).normalize

/-- If the witness point `p i` lies in the support of the original plan, then the corresponding
local restricted piece is nonzero. This is where support membership gets converted into positive
local mass. -/
lemma localRestrictedPiece_nonzero_of_mem_support
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    localRestrictedPiece π hdata i ≠ 0 := by
  have hrect_open : IsOpen (hdata.U i ×ˢ hdata.V i) :=
    (hdata.isOpen_mem_U i).1.prod (hdata.isOpen_mem_V i).1
  have hrect_mem : p i ∈ hdata.U i ×ˢ hdata.V i := by
    exact ⟨(hdata.isOpen_mem_U i).2, (hdata.isOpen_mem_V i).2⟩
  simpa [localRestrictedPiece] using
    (FiniteMeasure.restrict_nonzero_of_mem_support_of_isOpen
      (μ := π.toTransportPlan.toFiniteMeasure) (x := p i) (hmem i) hrect_open hrect_mem)

/-- The normalized local piece is almost surely contained in its defining rectangle. -/
lemma ae_mem_localNormalizedPiece_rect
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    ∀ᵐ z ∂((localNormalizedPiece π hdata i : ProbabilityMeasure (X × Y)) : Measure (X × Y)),
      z ∈ hdata.U i ×ˢ hdata.V i := by
  have hU : MeasurableSet (hdata.U i) := (hdata.isOpen_mem_U i).1.measurableSet
  have hV : MeasurableSet (hdata.V i) := (hdata.isOpen_mem_V i).1.measurableSet
  simpa [localNormalizedPiece, localRestrictedPiece] using
    (FiniteMeasure.ae_mem_prod_of_normalize_restrict
      (μ := π.toTransportPlan.toFiniteMeasure) (U := hdata.U i) (V := hdata.V i) hU hV
      (localRestrictedPiece_nonzero_of_mem_support π hdata hmem i))

/-- The first marginal of the normalized local piece is almost surely contained in `Uᵢ`. -/
lemma ae_fst_mem_localNormalizedPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    ∀ᵐ x ∂((TransportPlan.fst (localNormalizedPiece π hdata i) : ProbabilityMeasure X) :
      Measure X), x ∈ hdata.U i := by
  have hU : MeasurableSet (hdata.U i) := (hdata.isOpen_mem_U i).1.measurableSet
  have hV : MeasurableSet (hdata.V i) := (hdata.isOpen_mem_V i).1.measurableSet
  simpa [localNormalizedPiece, localRestrictedPiece] using
    (FiniteMeasure.fst_ae_mem_of_normalize_restrict_prod
      (μ := π.toTransportPlan.toFiniteMeasure) (U := hdata.U i) (V := hdata.V i) hU hV
      (localRestrictedPiece_nonzero_of_mem_support π hdata hmem i))

/-- The second marginal of the normalized local piece is almost surely contained in `Vᵢ`. -/
lemma ae_snd_mem_localNormalizedPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    ∀ᵐ y ∂((TransportPlan.snd (localNormalizedPiece π hdata i) : ProbabilityMeasure Y) :
      Measure Y), y ∈ hdata.V i := by
  have hU : MeasurableSet (hdata.U i) := (hdata.isOpen_mem_U i).1.measurableSet
  have hV : MeasurableSet (hdata.V i) := (hdata.isOpen_mem_V i).1.measurableSet
  simpa [localNormalizedPiece, localRestrictedPiece] using
    (FiniteMeasure.snd_ae_mem_of_normalize_restrict_prod
      (μ := π.toTransportPlan.toFiniteMeasure) (U := hdata.U i) (V := hdata.V i) hU hV
      (localRestrictedPiece_nonzero_of_mem_support π hdata hmem i))

end LocalPieces

section CommonRemovableMass

variable [MeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace X] [TopologicalSpace Y]

open scoped NNReal

/-- The total mass of the local restricted piece cut out by the `i`-th rectangle. These are the
individual masses from which we will later choose a common removable amount. -/
noncomputable def localRestrictedMass {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) : ℝ≥0 :=
  (localRestrictedPiece π hdata i).mass

/-- The common removable mass is the minimum of the finitely many local masses. This guarantees
that one can remove exactly this much mass from every diagonal local piece simultaneously. -/
noncomputable def commonRemovableMass {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) : ℝ≥0 :=
  Finset.univ.inf' Finset.univ_nonempty (localRestrictedMass π hdata)

/-- Each local restricted mass is positive when the corresponding witness point lies in the support
of the original plan. This is the scalar form of `localRestrictedPiece_nonzero_of_mem_support`. -/
lemma localRestrictedMass_pos_of_mem_support
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [Nonempty (X × Y)]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    0 < localRestrictedMass π hdata i := by
  rw [localRestrictedMass, pos_iff_ne_zero, FiniteMeasure.mass_nonzero_iff]
  exact localRestrictedPiece_nonzero_of_mem_support π hdata hmem i

/-- The common removable mass is positive because every local restricted mass is positive. -/
lemma commonRemovableMass_pos_of_mem_support
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [Nonempty (X × Y)]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support) :
    0 < commonRemovableMass π hdata := by
  rw [commonRemovableMass]
  exact (Finset.lt_inf'_iff (s := Finset.univ) (H := Finset.univ_nonempty)
    (f := localRestrictedMass π hdata)).2 fun i _ ↦
      localRestrictedMass_pos_of_mem_support π hdata hmem i

/-- By construction, the common removable mass is bounded above by every local restricted mass. -/
lemma commonRemovableMass_le_localRestrictedMass
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) :
    commonRemovableMass π hdata ≤ localRestrictedMass π hdata i := by
  simpa [commonRemovableMass] using
    (Finset.inf'_le (s := Finset.univ) (f := localRestrictedMass π hdata) (h := Finset.mem_univ i))

end CommonRemovableMass

section FiniteMassBookkeeping

variable {α : Type*} [MeasurableSpace α]

namespace FiniteMeasure

/-- The sum of disjoint finite restrictions is the restriction to the finite union. This is just a
named re-export of the `mathlib` lemma in the form used later in the competitor construction. -/
lemma sum_restrict_eq_restrict_biUnion_finset {ι : Type*} {μ : FiniteMeasure α} {T : Finset ι}
    {s : ι → Set α} (hd : (T : Set ι).Pairwise (Function.onFun Disjoint s))
    (hm : ∀ i, MeasurableSet (s i)) :
    ∑ i ∈ T, μ.restrict (s i) = μ.restrict (⋃ i ∈ T, s i) := by
  symm
  exact μ.restrict_biUnion_finset hd hm

end FiniteMeasure

end FiniteMassBookkeeping

section ReplacementPieces

variable [MeasurableSpace X] [MeasurableSpace Y] [Nonempty (X × Y)]
  [TopologicalSpace X] [TopologicalSpace Y]

open scoped NNReal

/-- The diagonal piece removed from the `i`-th local rectangle. It is obtained by taking the
normalized local law `ξᵢ` and scaling it by the common removable mass `t`. -/
noncomputable def localOldPiece {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) :
    FiniteMeasure (X × Y) :=
  commonRemovableMass π hdata • (localNormalizedPiece π hdata i).toFiniteMeasure

/-- The total diagonal mass removed from the original plan. -/
noncomputable def oldPiece {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    FiniteMeasure (X × Y) :=
  ∑ i, localOldPiece π hdata i

/-- The shifted replacement piece corresponding to the `i`-th local rectangle. Its first marginal
comes from the `i`-th diagonal piece, while its second marginal comes from the next rectangle in
the cycle. -/
noncomputable def localNewPiece {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) :
    FiniteMeasure (X × Y) :=
  commonRemovableMass π hdata •
    (((TransportPlan.fst (localNormalizedPiece π hdata i)).prod
      (TransportPlan.snd (localNormalizedPiece π hdata (i + 1)))).toFiniteMeasure)

/-- The total shifted replacement mass inserted into the competitor. -/
noncomputable def newPiece {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    FiniteMeasure (X × Y) :=
  ∑ i, localNewPiece π hdata i

/-- Each diagonal removable piece is dominated by the corresponding restricted piece cut out of the
original plan. This is the basic scalar comparison `t ≤ κᵢ.mass` transported to measures. -/
lemma localOldPiece_le_localRestrictedPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) :
    (localOldPiece π hdata i : Measure (X × Y)) ≤
      (localRestrictedPiece π hdata i : Measure (X × Y)) := by
  have hself :
      (localRestrictedPiece π hdata i : Measure (X × Y)) =
        localRestrictedMass π hdata i •
          ((localNormalizedPiece π hdata i).toFiniteMeasure : Measure (X × Y)) := by
    simpa [localRestrictedMass, localNormalizedPiece] using
      congrArg (fun ν : FiniteMeasure (X × Y) => (ν : Measure (X × Y)))
        (localRestrictedPiece π hdata i).self_eq_mass_smul_normalize
  intro s
  rw [localOldPiece, FiniteMeasure.toMeasure_smul, hself, Measure.coe_nnreal_smul_apply,
    Measure.coe_nnreal_smul_apply]
  gcongr
  exact commonRemovableMass_le_localRestrictedMass π hdata i

/-- Summing the diagonal removable pieces still gives a finite measure dominated by the original
transport plan. This is the domination needed before subtracting `oldPiece` from `π`. -/
lemma oldPiece_le_toFiniteMeasure
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    (oldPiece π hdata : Measure (X × Y)) ≤
      (π.toTransportPlan.toFiniteMeasure : Measure (X × Y)) := by
  have hsum :
      ∑ i, localRestrictedPiece π hdata i =
        π.toTransportPlan.toFiniteMeasure.restrict
          (⋃ i ∈ (Finset.univ : Finset (Fin (n + 1))), hdata.U i ×ˢ hdata.V i) := by
    simpa [localRestrictedPiece] using
        (FiniteMeasure.sum_restrict_eq_restrict_biUnion_finset
        (μ := π.toTransportPlan.toFiniteMeasure) (T := Finset.univ)
        (hd := by
          intro i _ j _ hij
          exact hdata.pairwiseDisjoint (by simp) (by simp) hij)
        (hm := fun i ↦
          ((hdata.isOpen_mem_U i).1.measurableSet).prod ((hdata.isOpen_mem_V i).1.measurableSet)))
  calc
    (oldPiece π hdata : Measure (X × Y))
      = ∑ i, (localOldPiece π hdata i : Measure (X × Y)) := by
          simp [oldPiece, FiniteMeasure.toMeasure_sum]
    _ ≤ ∑ i, (localRestrictedPiece π hdata i : Measure (X × Y)) := by
      exact Finset.sum_le_sum fun i _ ↦ localOldPiece_le_localRestrictedPiece π hdata i
    _ = ((∑ i, localRestrictedPiece π hdata i : FiniteMeasure (X × Y)) : Measure (X × Y)) := by
      simp [FiniteMeasure.toMeasure_sum]
    _ = ((π.toTransportPlan.toFiniteMeasure.restrict
          (⋃ i ∈ (Finset.univ : Finset (Fin (n + 1))), hdata.U i ×ˢ hdata.V i) :
            FiniteMeasure (X × Y)) : Measure (X × Y)) := by
      exact congrArg (fun ν : FiniteMeasure (X × Y) => (ν : Measure (X × Y))) hsum
    _ ≤ π.toTransportPlan.toFiniteMeasure := by
      simpa using
        (Measure.restrict_le_self
          (μ := (π.toTransportPlan.toFiniteMeasure : Measure (X × Y)))
          (s := ⋃ i ∈ (Finset.univ : Finset (Fin (n + 1))), hdata.U i ×ˢ hdata.V i))

/-- The `i`-th removable diagonal piece is almost surely contained in the rectangle
`Uᵢ × Vᵢ`. This is the localization statement later used for the diagonal cost term. -/
lemma ae_mem_localOldPiece_rect
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    ∀ᵐ z ∂(localOldPiece π hdata i : Measure (X × Y)), z ∈ hdata.U i ×ˢ hdata.V i := by
  exact Measure.ae_smul_measure
    (ae_mem_localNormalizedPiece_rect π hdata hmem i) (commonRemovableMass π hdata)

/-- The `i`-th shifted replacement piece is almost surely contained in the cyclic rectangle
`Uᵢ × Vᵢ₊₁`. This is the localization statement later used for the cross-cost term. -/
lemma ae_mem_localNewPiece_rect
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    ∀ᵐ z ∂(localNewPiece π hdata i : Measure (X × Y)), z ∈ hdata.U i ×ˢ hdata.V (i + 1) := by
  have hU : MeasurableSet (hdata.U i) := (hdata.isOpen_mem_U i).1.measurableSet
  have hV : MeasurableSet (hdata.V (i + 1)) := (hdata.isOpen_mem_V (i + 1)).1.measurableSet
  have hprod :
      ∀ᵐ z ∂((((TransportPlan.fst (localNormalizedPiece π hdata i)).prod
        (TransportPlan.snd (localNormalizedPiece π hdata (i + 1))) : TransportPlan X Y) :
        Measure (X × Y))), z ∈ hdata.U i ×ˢ hdata.V (i + 1) := by
    exact TransportPlan.ae_mem_prod_of_prod hU hV
      (ae_fst_mem_localNormalizedPiece π hdata hmem i)
      (ae_snd_mem_localNormalizedPiece π hdata hmem (i + 1))
  simpa [localNewPiece] using
    Measure.ae_smul_measure hprod (commonRemovableMass π hdata)

end ReplacementPieces

section ReplacementCompetitor

variable [MeasurableSpace X] [MeasurableSpace Y] [Nonempty (X × Y)]
  [TopologicalSpace X] [TopologicalSpace Y]

open scoped NNReal

/-- The first marginal of a diagonal removable piece is the corresponding first marginal of the
normalized local law, scaled by the common removable mass. -/
lemma fst_localOldPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) :
    (localOldPiece π hdata i : Measure (X × Y)).fst =
      commonRemovableMass π hdata •
        (((TransportPlan.fst (localNormalizedPiece π hdata i) : ProbabilityMeasure X) :
          Measure X)) := by
  simp [localOldPiece, Measure.fst, TransportPlan.fst, FiniteMeasure.toMeasure_smul]

/-- The second marginal of a diagonal removable piece is the corresponding second marginal of the
normalized local law, scaled by the common removable mass. -/
lemma snd_localOldPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) :
    (localOldPiece π hdata i : Measure (X × Y)).snd =
      commonRemovableMass π hdata •
        (((TransportPlan.snd (localNormalizedPiece π hdata i) : ProbabilityMeasure Y) :
          Measure Y)) := by
  simp [localOldPiece, Measure.snd, TransportPlan.snd, FiniteMeasure.toMeasure_smul]

/-- The first marginal of a shifted replacement piece is the first marginal of the `i`-th
normalized local law, scaled by the common removable mass. -/
lemma fst_localNewPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) :
    (localNewPiece π hdata i : Measure (X × Y)).fst =
      commonRemovableMass π hdata •
        (((TransportPlan.fst (localNormalizedPiece π hdata i) : ProbabilityMeasure X) :
          Measure X)) := by
  simp [localNewPiece, Measure.fst, TransportPlan.fst, FiniteMeasure.toMeasure_smul]

/-- The second marginal of a shifted replacement piece is the second marginal of the next
normalized local law in the cycle, scaled by the common removable mass. -/
lemma snd_localNewPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) (i : Fin (n + 1)) :
    (localNewPiece π hdata i : Measure (X × Y)).snd =
      commonRemovableMass π hdata •
        (((TransportPlan.snd (localNormalizedPiece π hdata (i + 1)) : ProbabilityMeasure Y) :
          Measure Y)) := by
  simp [localNewPiece, Measure.snd, TransportPlan.snd, FiniteMeasure.toMeasure_smul]

/-- The first marginal of the total removed mass is the sum of the first marginals of the
individual diagonal pieces. -/
lemma fst_oldPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    (oldPiece π hdata : Measure (X × Y)).fst =
      ∑ i, commonRemovableMass π hdata •
        (((TransportPlan.fst (localNormalizedPiece π hdata i) : ProbabilityMeasure X) :
          Measure X)) := by
  calc
    (oldPiece π hdata : Measure (X × Y)).fst
      = (Measure.sum fun i : Fin (n + 1) => (localOldPiece π hdata i : Measure (X × Y))).fst := by
          simp [oldPiece, FiniteMeasure.toMeasure_sum, Measure.sum_fintype]
    _ = Measure.sum (fun i : Fin (n + 1) => (localOldPiece π hdata i : Measure (X × Y)).fst) := by
          rw [Measure.fst_sum]
    _ = ∑ i, commonRemovableMass π hdata •
          (((TransportPlan.fst (localNormalizedPiece π hdata i) : ProbabilityMeasure X) :
            Measure X)) := by
          rw [Measure.sum_fintype]
          simp [fst_localOldPiece]

/-- The second marginal of the total removed mass is the sum of the second marginals of the
individual diagonal pieces. -/
lemma snd_oldPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    (oldPiece π hdata : Measure (X × Y)).snd =
      ∑ i, commonRemovableMass π hdata •
        (((TransportPlan.snd (localNormalizedPiece π hdata i) : ProbabilityMeasure Y) :
          Measure Y)) := by
  calc
    (oldPiece π hdata : Measure (X × Y)).snd
      = (Measure.sum fun i : Fin (n + 1) => (localOldPiece π hdata i : Measure (X × Y))).snd := by
          simp [oldPiece, FiniteMeasure.toMeasure_sum, Measure.sum_fintype]
    _ = Measure.sum (fun i : Fin (n + 1) => (localOldPiece π hdata i : Measure (X × Y)).snd) := by
          rw [Measure.snd_sum]
    _ = ∑ i, commonRemovableMass π hdata •
          (((TransportPlan.snd (localNormalizedPiece π hdata i) : ProbabilityMeasure Y) :
            Measure Y)) := by
          rw [Measure.sum_fintype]
          simp [snd_localOldPiece]

/-- The first marginal of the total inserted mass agrees termwise with the first marginal of the
total removed mass. -/
lemma fst_newPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    (newPiece π hdata : Measure (X × Y)).fst =
      ∑ i, commonRemovableMass π hdata •
        (((TransportPlan.fst (localNormalizedPiece π hdata i) : ProbabilityMeasure X) :
          Measure X)) := by
  calc
    (newPiece π hdata : Measure (X × Y)).fst
      = (Measure.sum fun i : Fin (n + 1) => (localNewPiece π hdata i : Measure (X × Y))).fst := by
          simp [newPiece, FiniteMeasure.toMeasure_sum, Measure.sum_fintype]
    _ = Measure.sum (fun i : Fin (n + 1) => (localNewPiece π hdata i : Measure (X × Y)).fst) := by
          rw [Measure.fst_sum]
    _ = ∑ i, commonRemovableMass π hdata •
          (((TransportPlan.fst (localNormalizedPiece π hdata i) : ProbabilityMeasure X) :
            Measure X)) := by
          rw [Measure.sum_fintype]
          simp [fst_localNewPiece]

/-- The second marginal of the total inserted mass is the cyclic reindexing of the second
marginals of the diagonal pieces. -/
lemma snd_newPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    (newPiece π hdata : Measure (X × Y)).snd =
      ∑ i, commonRemovableMass π hdata •
        (((TransportPlan.snd (localNormalizedPiece π hdata i) : ProbabilityMeasure Y) :
          Measure Y)) := by
  calc
    (newPiece π hdata : Measure (X × Y)).snd
      = (Measure.sum fun i : Fin (n + 1) => (localNewPiece π hdata i : Measure (X × Y))).snd := by
          simp [newPiece, FiniteMeasure.toMeasure_sum, Measure.sum_fintype]
    _ = Measure.sum (fun i : Fin (n + 1) => (localNewPiece π hdata i : Measure (X × Y)).snd) := by
          rw [Measure.snd_sum]
    _ = Measure.sum (fun i : Fin (n + 1) =>
          commonRemovableMass π hdata •
            (((TransportPlan.snd (localNormalizedPiece π hdata (i + 1)) : ProbabilityMeasure Y) :
              Measure Y))) := by
          congr 1
          funext i
          exact snd_localNewPiece π hdata i
    _ = Measure.sum (fun i : Fin (n + 1) =>
          commonRemovableMass π hdata •
            (((TransportPlan.snd (localNormalizedPiece π hdata i) : ProbabilityMeasure Y) :
              Measure Y))) := by
          simpa [finRotate_succ_apply] using
            (Measure.sum_comp_equiv (e := finRotate (n + 1))
              (m := fun i : Fin (n + 1) =>
                commonRemovableMass π hdata •
                  (((TransportPlan.snd (localNormalizedPiece π hdata i) :
                    ProbabilityMeasure Y) : Measure Y))))
    _ = ∑ i, commonRemovableMass π hdata •
          (((TransportPlan.snd (localNormalizedPiece π hdata i) : ProbabilityMeasure Y) :
            Measure Y)) := by
          rw [Measure.sum_fintype]

/-- The total inserted and removed masses have the same first marginal. -/
lemma fst_newPiece_eq_fst_oldPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    (newPiece π hdata : Measure (X × Y)).fst =
      (oldPiece π hdata : Measure (X × Y)).fst := by
  rw [fst_newPiece, fst_oldPiece]

/-- The total inserted and removed masses have the same second marginal. -/
lemma snd_newPiece_eq_snd_oldPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    (newPiece π hdata : Measure (X × Y)).snd =
      (oldPiece π hdata : Measure (X × Y)).snd := by
  rw [snd_newPiece, snd_oldPiece]

/-- The measure obtained by subtracting the diagonal old piece from `π` and adding the shifted new
piece. This is the competitor used in the perturbation argument. -/
noncomputable def competitorMeasure
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    Measure (X × Y) :=
  (π.toTransportPlan : Measure (X × Y)) - (oldPiece π hdata : Measure (X × Y)) +
    (newPiece π hdata : Measure (X × Y))

/-- The competitor measure has the same first marginal as the original coupling. -/
lemma fst_competitorMeasure
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    (competitorMeasure π hdata).fst = (μ : Measure X) := by
  have h_old_le :
      (oldPiece π hdata : Measure (X × Y)) ≤ (π.toTransportPlan : Measure (X × Y)) :=
    oldPiece_le_toFiniteMeasure π hdata
  have hπfst : ((π.toTransportPlan : Measure (X × Y)).fst) = (μ : Measure X) := by
    exact (TransportPlan.toMeasure_fst π.toTransportPlan).symm.trans π.toMeasure_fst
  have hfst_old_le :
      (oldPiece π hdata : Measure (X × Y)).fst ≤ (μ : Measure X) := by
    have htmp :
        (oldPiece π hdata : Measure (X × Y)).fst ≤
          ((π.toTransportPlan : Measure (X × Y)).fst) :=
      Measure.fst_mono (ρ := (oldPiece π hdata : Measure (X × Y)))
        (μ := (π.toTransportPlan : Measure (X × Y))) h_old_le
    exact htmp.trans_eq hπfst
  have hcancel :
      ((π.toTransportPlan : Measure (X × Y)).fst) -
          (oldPiece π hdata : Measure (X × Y)).fst +
          (oldPiece π hdata : Measure (X × Y)).fst =
        (μ : Measure X) := by
    calc
      ((π.toTransportPlan : Measure (X × Y)).fst) -
            (oldPiece π hdata : Measure (X × Y)).fst +
            (oldPiece π hdata : Measure (X × Y)).fst
        = ((π.toTransportPlan : Measure (X × Y)).fst) := by
            exact Measure.sub_add_cancel_of_le
              (Measure.fst_mono (ρ := (oldPiece π hdata : Measure (X × Y)))
                (μ := (π.toTransportPlan : Measure (X × Y))) h_old_le)
      _ = (μ : Measure X) := hπfst
  simpa [competitorMeasure, Measure.fst_add, Measure.fst_sub_of_le h_old_le,
    fst_newPiece_eq_fst_oldPiece] using hcancel

/-- The competitor measure has the same second marginal as the original coupling. -/
lemma snd_competitorMeasure
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    (competitorMeasure π hdata).snd = (ν : Measure Y) := by
  have h_old_le :
      (oldPiece π hdata : Measure (X × Y)) ≤ (π.toTransportPlan : Measure (X × Y)) :=
    oldPiece_le_toFiniteMeasure π hdata
  have hπsnd : ((π.toTransportPlan : Measure (X × Y)).snd) = (ν : Measure Y) := by
    exact (TransportPlan.toMeasure_snd π.toTransportPlan).symm.trans π.toMeasure_snd
  have hsnd_old_le :
      (oldPiece π hdata : Measure (X × Y)).snd ≤ (ν : Measure Y) := by
    have htmp :
        (oldPiece π hdata : Measure (X × Y)).snd ≤
          ((π.toTransportPlan : Measure (X × Y)).snd) :=
      Measure.snd_mono (ρ := (oldPiece π hdata : Measure (X × Y)))
        (μ := (π.toTransportPlan : Measure (X × Y))) h_old_le
    exact htmp.trans_eq hπsnd
  have hcancel :
      ((π.toTransportPlan : Measure (X × Y)).snd) -
          (oldPiece π hdata : Measure (X × Y)).snd +
          (oldPiece π hdata : Measure (X × Y)).snd =
        (ν : Measure Y) := by
    calc
      ((π.toTransportPlan : Measure (X × Y)).snd) -
            (oldPiece π hdata : Measure (X × Y)).snd +
            (oldPiece π hdata : Measure (X × Y)).snd
        = ((π.toTransportPlan : Measure (X × Y)).snd) := by
            exact Measure.sub_add_cancel_of_le
              (Measure.snd_mono (ρ := (oldPiece π hdata : Measure (X × Y)))
                (μ := (π.toTransportPlan : Measure (X × Y))) h_old_le)
      _ = (ν : Measure Y) := hπsnd
  simpa [competitorMeasure, Measure.snd_add, Measure.snd_sub_of_le h_old_le,
    snd_newPiece_eq_snd_oldPiece] using hcancel

/-- The competitor measure is again a transport plan with the same marginals, hence a coupling of
`μ` and `ν`. -/
noncomputable def competitorCoupling
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    Coupling μ ν where
  toTransportPlan :=
    ⟨competitorMeasure π hdata, by
      refine ⟨?_⟩
      calc
        competitorMeasure π hdata Set.univ =
            (competitorMeasure π hdata).fst Set.univ := by
          symm
          exact Measure.fst_univ
        _ = (μ : Measure X) Set.univ := by rw [fst_competitorMeasure π hdata]
        _ = 1 := measure_univ⟩
  fst_eq := by
    apply Subtype.ext
    exact fst_competitorMeasure π hdata
  snd_eq := by
    apply Subtype.ext
    exact snd_competitorMeasure π hdata

end ReplacementCompetitor

section ReplacementCostIntegrability

variable [MeasurableSpace X] [MeasurableSpace Y] [Nonempty (X × Y)]
  [TopologicalSpace X] [TopologicalSpace Y]
  [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
  [OpensMeasurableSpace (X × Y)]

/-- The cost is integrable on each diagonal removable piece because that piece is supported in a
rectangle on which `c` is uniformly bounded. This is the local diagonal integrability statement
used later when expanding the cost of the competitor. -/
lemma integrable_cost_localOldPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    Integrable (fun z : X × Y ↦ c z.1 z.2) (localOldPiece π hdata i : Measure (X × Y)) := by
  refine Integrable.of_bound (μ := (localOldPiece π hdata i : Measure (X × Y))) ?_ hdata.B ?_
  · exact hc.measurable.aestronglyMeasurable
  · filter_upwards [ae_mem_localOldPiece_rect π hdata hmem i] with z hz
    simpa [Real.norm_eq_abs] using le_of_lt (hdata.diag_bound i hz.1 hz.2)

/-- The cost is integrable on each shifted replacement piece because that piece is supported in a
rectangle on which `c` is uniformly bounded. This is the local cross-term integrability statement
needed before comparing old and new costs. -/
lemma integrable_cost_localNewPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    Integrable (fun z : X × Y ↦ c z.1 z.2) (localNewPiece π hdata i : Measure (X × Y)) := by
  refine Integrable.of_bound (μ := (localNewPiece π hdata i : Measure (X × Y))) ?_ hdata.B ?_
  · exact hc.measurable.aestronglyMeasurable
  · filter_upwards [ae_mem_localNewPiece_rect π hdata hmem i] with z hz
    simpa [Real.norm_eq_abs] using le_of_lt (hdata.cross_bound i hz.1 hz.2)

/-- Summing the finitely many diagonal removable pieces preserves integrability of the cost. -/
lemma integrable_cost_oldPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support) :
    Integrable (fun z : X × Y ↦ c z.1 z.2) (oldPiece π hdata : Measure (X × Y)) := by
  simpa [oldPiece, FiniteMeasure.toMeasure_sum] using
    (integrable_finset_sum_measure
      (f := fun z : X × Y ↦ c z.1 z.2)
      (μ := fun i : Fin (n + 1) ↦ (localOldPiece π hdata i : Measure (X × Y)))
      (s := Finset.univ)).2
      (fun i _ ↦ integrable_cost_localOldPiece hc hdata π hmem i)

/-- Summing the finitely many shifted replacement pieces preserves integrability of the cost. -/
lemma integrable_cost_newPiece
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support) :
    Integrable (fun z : X × Y ↦ c z.1 z.2) (newPiece π hdata : Measure (X × Y)) := by
  simpa [newPiece, FiniteMeasure.toMeasure_sum] using
    (integrable_finset_sum_measure
      (f := fun z : X × Y ↦ c z.1 z.2)
      (μ := fun i : Fin (n + 1) ↦ (localNewPiece π hdata i : Measure (X × Y)))
      (s := Finset.univ)).2
      (fun i _ ↦ integrable_cost_localNewPiece hc hdata π hmem i)

/-- The competitor has finite transport cost for a continuous real-valued cost once the original
plan has finite cost. The diagonal part is dominated by the original plan, and the inserted part is
integrable by the local rectangle bounds proved above. -/
lemma integrable_cost_competitorMeasure
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (hπ :
      Integrable (fun z : X × Y ↦ c z.1 z.2) (π.toTransportPlan : Measure (X × Y)))
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support) :
    Integrable (fun z : X × Y ↦ c z.1 z.2) (competitorMeasure π hdata) := by
  have hsub :
      Integrable (fun z : X × Y ↦ c z.1 z.2)
        (((π.toTransportPlan : Measure (X × Y)) - (oldPiece π hdata : Measure (X × Y)))) := by
    exact hπ.mono_measure Measure.sub_le
  simpa [competitorMeasure] using hsub.add_measure (integrable_cost_newPiece hc hdata π hmem)

end ReplacementCostIntegrability

section ReplacementCostDrop

variable [MeasurableSpace X] [MeasurableSpace Y] [Nonempty (X × Y)]
  [TopologicalSpace X] [TopologicalSpace Y]

/-- The product law of the normalized local pieces. Sampling from this measure chooses one point
from each local rectangle independently. It is the ambient probability measure under which the
diagonal and cyclic cross costs combine into `cycleGap`. -/
noncomputable def replacementPiMeasure
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    ProbabilityMeasure (Fin (n + 1) → X × Y) :=
  ProbabilityMeasure.pi fun i ↦ localNormalizedPiece π hdata i

/-- The measure underlying the replacement product probability measure. This alias is only here to
keep later integral expressions readable. -/
noncomputable abbrev replacementPiMeasureMeasure
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p) :
    Measure (Fin (n + 1) → X × Y) :=
  (replacementPiMeasure π hdata : Measure (Fin (n + 1) → X × Y))

/-- Each coordinate of the replacement product law lies almost surely in its corresponding local
rectangle. -/
lemma ae_mem_replacementPiMeasure_rect
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (π : Coupling μ ν) {c : X → Y → ℝ} {p : Fin (n + 1) → X × Y}
    (hdata : CycleGapNeighborhoodData c p)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    ∀ᵐ ω ∂replacementPiMeasureMeasure π hdata, ω i ∈ hdata.U i ×ˢ hdata.V i := by
  have hrect :
      ∀ᵐ z ∂(((localNormalizedPiece π hdata i : ProbabilityMeasure (X × Y)) :
        Measure (X × Y))), z ∈ hdata.U i ×ˢ hdata.V i :=
    ae_mem_localNormalizedPiece_rect π hdata hmem i
  have hmap :
      (replacementPiMeasureMeasure π hdata).map (fun ω : Fin (n + 1) → X × Y ↦ ω i) =
        (((localNormalizedPiece π hdata i : ProbabilityMeasure (X × Y)) :
          Measure (X × Y))) := by
    simpa [replacementPiMeasure] using
      (measurePreserving_eval
        (fun k ↦
          ((localNormalizedPiece π hdata k : ProbabilityMeasure (X × Y)) :
            Measure (X × Y))) i).map_eq
  rw [← hmap] at hrect
  exact (mem_ae_map_iff (μ := replacementPiMeasureMeasure π hdata)
    ((measurable_pi_apply i).aemeasurable)
    (((hdata.isOpen_mem_U i).1.measurableSet).prod
      ((hdata.isOpen_mem_V i).1.measurableSet))).1 hrect

/-- The diagonal term for coordinate `i` is integrable under the replacement product law. -/
lemma integrable_replacementPiMeasure_diag
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    [OpensMeasurableSpace (X × Y)]
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    Integrable (fun ω : Fin (n + 1) → X × Y ↦ c (ω i).1 (ω i).2)
      (replacementPiMeasureMeasure π hdata) := by
  refine Integrable.of_bound (μ := replacementPiMeasureMeasure π hdata) ?_ hdata.B ?_
  · exact (hc.measurable.comp (measurable_pi_apply i)).aestronglyMeasurable
  · filter_upwards [ae_mem_replacementPiMeasure_rect π hdata hmem i] with ω hω
    simpa [Real.norm_eq_abs] using le_of_lt (hdata.diag_bound i hω.1 hω.2)

/-- The cyclic cross term for coordinate `i` is integrable under the replacement product law. -/
lemma integrable_replacementPiMeasure_cross
    {n : ℕ} [NeZero n] {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    [OpensMeasurableSpace (X × Y)]
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support)
    (i : Fin (n + 1)) :
    Integrable (fun ω : Fin (n + 1) → X × Y ↦ c (ω i).1 (ω (i + 1)).2)
      (replacementPiMeasureMeasure π hdata) := by
  refine Integrable.of_bound (μ := replacementPiMeasureMeasure π hdata) ?_ hdata.B ?_
  · have hφ : Measurable fun ω : Fin (n + 1) → X × Y ↦ ((ω i).1, (ω (i + 1)).2) := by
      fun_prop
    exact (hc.measurable.comp hφ).aestronglyMeasurable
  · filter_upwards [ae_mem_replacementPiMeasure_rect π hdata hmem i,
      ae_mem_replacementPiMeasure_rect π hdata hmem (i + 1)] with ω hi hi1
    simpa [Real.norm_eq_abs] using le_of_lt (hdata.cross_bound i hi.1 hi1.2)

/-- The cost of a diagonal removable piece is the common removable mass times the diagonal expected
cost of the corresponding coordinate under the replacement product law. -/
lemma integral_cost_localOldPiece_eq_commonRemovableMass_mul
    {n : ℕ} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace (X × Y)]
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (i : Fin (n + 1)) :
    ∫ z, c z.1 z.2 ∂(localOldPiece π hdata i : Measure (X × Y)) =
      (commonRemovableMass π hdata : ℝ) *
        ∫ ω, c (ω i).1 (ω i).2 ∂replacementPiMeasureMeasure π hdata := by
  have hmap :
      (replacementPiMeasureMeasure π hdata).map (fun ω : Fin (n + 1) → X × Y ↦ ω i) =
        (((localNormalizedPiece π hdata i : ProbabilityMeasure (X × Y)) :
          Measure (X × Y))) := by
    simpa [replacementPiMeasure] using
      (measurePreserving_eval
        (fun k ↦
          ((localNormalizedPiece π hdata k : ProbabilityMeasure (X × Y)) :
            Measure (X × Y))) i).map_eq
  unfold localOldPiece
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  simp only [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  congr 1
  calc
    ∫ z, c z.1 z.2 ∂(((localNormalizedPiece π hdata i : ProbabilityMeasure (X × Y)) :
      Measure (X × Y)))
      = ∫ z, c z.1 z.2 ∂((replacementPiMeasureMeasure π hdata).map
            (fun ω : Fin (n + 1) → X × Y ↦ ω i)) := by
              rw [hmap]
    _ = ∫ ω, c (ω i).1 (ω i).2 ∂replacementPiMeasureMeasure π hdata := by
          simpa using
            (integral_map ((measurable_pi_apply i).aemeasurable)
              (hc.measurable.aestronglyMeasurable))

/-- The cost of a shifted replacement piece is the common removable mass times the expected cyclic
cross cost of the corresponding coordinate pair under the replacement product law. -/
lemma integral_cost_localNewPiece_eq_commonRemovableMass_mul
    {n : ℕ} [NeZero n] {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace (X × Y)]
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (i : Fin (n + 1)) :
    ∫ z, c z.1 z.2 ∂(localNewPiece π hdata i : Measure (X × Y)) =
      (commonRemovableMass π hdata : ℝ) *
        ∫ ω, c (ω i).1 (ω (i + 1)).2 ∂replacementPiMeasureMeasure π hdata := by
  have hij : i ≠ i + 1 := by
    intro h
    have : (1 : Fin (n + 1)) = 0 := by
      simpa using congrArg (fun j : Fin (n + 1) ↦ j - i) h
    exact one_ne_zero this
  let φ : (Fin (n + 1) → X × Y) → X × Y := fun ω ↦ ((ω i).1, (ω (i + 1)).2)
  have hmap :
      (replacementPiMeasureMeasure π hdata).map φ =
        ((((TransportPlan.fst (localNormalizedPiece π hdata i)).prod
          (TransportPlan.snd (localNormalizedPiece π hdata (i + 1))) : TransportPlan X Y) :
          Measure (X × Y))) := by
    simpa [replacementPiMeasure] using
      (map_pair_eval_eq_prod_map_eval
        (μ := fun k ↦ localNormalizedPiece π hdata k)
        (i := i) (j := i + 1) hij
        measurable_fst.aemeasurable measurable_snd.aemeasurable)
  unfold localNewPiece
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  simp only [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ProbabilityMeasure.toMeasure_prod, TransportPlan.toMeasure_fst, TransportPlan.toMeasure_snd]
  congr 1
  calc
    ∫ z, c z.1 z.2 ∂((((TransportPlan.fst (localNormalizedPiece π hdata i)).prod
      (TransportPlan.snd (localNormalizedPiece π hdata (i + 1))) : TransportPlan X Y) :
      Measure (X × Y)))
      = ∫ z, c z.1 z.2 ∂((replacementPiMeasureMeasure π hdata).map φ) := by
              rw [hmap]
    _ = ∫ ω, c (ω i).1 (ω (i + 1)).2 ∂replacementPiMeasureMeasure π hdata := by
          have hφ : Measurable φ := by
            fun_prop
          simpa using
            (integral_map hφ.aemeasurable (hc.measurable.aestronglyMeasurable))

/-- The old-minus-new cost difference is the common removable mass times the expectation of
`cycleGap c` under the replacement product law. -/
lemma integral_cost_oldPiece_sub_integral_cost_newPiece_eq_commonRemovableMass_mul_integral_cycleGap
    {n : ℕ} [NeZero n] {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    [OpensMeasurableSpace (X × Y)]
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support) :
    (∫ z, c z.1 z.2 ∂(oldPiece π hdata : Measure (X × Y))) -
        (∫ z, c z.1 z.2 ∂(newPiece π hdata : Measure (X × Y))) =
      (commonRemovableMass π hdata : ℝ) *
        ∫ ω, cycleGap c ω ∂replacementPiMeasureMeasure π hdata := by
  have hold_sum :
      ∫ z, c z.1 z.2 ∂(oldPiece π hdata : Measure (X × Y)) =
        ∑ i, ∫ z, c z.1 z.2 ∂(localOldPiece π hdata i : Measure (X × Y)) := by
    simpa [oldPiece, FiniteMeasure.toMeasure_sum] using
      (integral_finset_sum_measure
        (f := fun z : X × Y ↦ c z.1 z.2)
        (μ := fun i : Fin (n + 1) ↦ (localOldPiece π hdata i : Measure (X × Y)))
        (s := Finset.univ))
        (fun i _ ↦ integrable_cost_localOldPiece hc hdata π hmem i)
  have hnew_sum :
      ∫ z, c z.1 z.2 ∂(newPiece π hdata : Measure (X × Y)) =
        ∑ i, ∫ z, c z.1 z.2 ∂(localNewPiece π hdata i : Measure (X × Y)) := by
    simpa [newPiece, FiniteMeasure.toMeasure_sum] using
      (integral_finset_sum_measure
        (f := fun z : X × Y ↦ c z.1 z.2)
        (μ := fun i : Fin (n + 1) ↦ (localNewPiece π hdata i : Measure (X × Y)))
        (s := Finset.univ))
        (fun i _ ↦ integrable_cost_localNewPiece hc hdata π hmem i)
  have hdiag_sum :
      ∑ i, ∫ z, c z.1 z.2 ∂(localOldPiece π hdata i : Measure (X × Y)) =
        (commonRemovableMass π hdata : ℝ) *
          ∑ i, ∫ ω, c (ω i).1 (ω i).2 ∂replacementPiMeasureMeasure π hdata := by
    simp_rw [integral_cost_localOldPiece_eq_commonRemovableMass_mul hc hdata π]
    rw [Finset.mul_sum]
  have hcross_sum :
      ∑ i, ∫ z, c z.1 z.2 ∂(localNewPiece π hdata i : Measure (X × Y)) =
        (commonRemovableMass π hdata : ℝ) *
          ∑ i, ∫ ω, c (ω i).1 (ω (i + 1)).2 ∂replacementPiMeasureMeasure π hdata := by
    simp_rw [integral_cost_localNewPiece_eq_commonRemovableMass_mul hc hdata π]
    rw [Finset.mul_sum]
  have hdiag_int :
      ∫ ω, ∑ i, c (ω i).1 (ω i).2 ∂replacementPiMeasureMeasure π hdata =
        ∑ i, ∫ ω, c (ω i).1 (ω i).2 ∂replacementPiMeasureMeasure π hdata := by
    exact integral_finset_sum (s := Finset.univ)
      (fun i _ ↦ integrable_replacementPiMeasure_diag hc hdata π hmem i)
  have hcross_int :
      ∫ ω, ∑ i, c (ω i).1 (ω (i + 1)).2 ∂replacementPiMeasureMeasure π hdata =
        ∑ i, ∫ ω, c (ω i).1 (ω (i + 1)).2 ∂replacementPiMeasureMeasure π hdata := by
    exact integral_finset_sum (s := Finset.univ)
      (fun i _ ↦ integrable_replacementPiMeasure_cross hc hdata π hmem i)
  have hdiag_whole :
      Integrable (fun ω : Fin (n + 1) → X × Y ↦ ∑ i, c (ω i).1 (ω i).2)
        (replacementPiMeasureMeasure π hdata) := by
    simpa only [Finset.sum_apply] using
      integrable_finset_sum (s := Finset.univ)
        (fun i _ ↦ integrable_replacementPiMeasure_diag hc hdata π hmem i)
  have hcross_whole :
      Integrable (fun ω : Fin (n + 1) → X × Y ↦ ∑ i, c (ω i).1 (ω (i + 1)).2)
        (replacementPiMeasureMeasure π hdata) := by
    simpa only [Finset.sum_apply] using
      integrable_finset_sum (s := Finset.univ)
        (fun i _ ↦ integrable_replacementPiMeasure_cross hc hdata π hmem i)
  calc
    (∫ z, c z.1 z.2 ∂(oldPiece π hdata : Measure (X × Y))) -
        (∫ z, c z.1 z.2 ∂(newPiece π hdata : Measure (X × Y)))
      = (commonRemovableMass π hdata : ℝ) *
          (∑ i, ∫ ω, c (ω i).1 (ω i).2 ∂replacementPiMeasureMeasure π hdata) -
            (commonRemovableMass π hdata : ℝ) *
              (∑ i, ∫ ω, c (ω i).1 (ω (i + 1)).2 ∂replacementPiMeasureMeasure π hdata) := by
              rw [hold_sum, hnew_sum, hdiag_sum, hcross_sum]
    _ = (commonRemovableMass π hdata : ℝ) *
          ((∑ i, ∫ ω, c (ω i).1 (ω i).2 ∂replacementPiMeasureMeasure π hdata) -
            (∑ i, ∫ ω, c (ω i).1 (ω (i + 1)).2 ∂replacementPiMeasureMeasure π hdata)) := by
            ring
    _ = (commonRemovableMass π hdata : ℝ) *
          ((∫ ω, ∑ i, c (ω i).1 (ω i).2 ∂replacementPiMeasureMeasure π hdata) -
            (∫ ω, ∑ i, c (ω i).1 (ω (i + 1)).2 ∂replacementPiMeasureMeasure π hdata)) := by
            rw [hdiag_int, hcross_int]
    _ = (commonRemovableMass π hdata : ℝ) *
          ∫ ω, cycleGap c ω ∂replacementPiMeasureMeasure π hdata := by
            rw [← integral_sub hdiag_whole hcross_whole]
            simp [cycleGap]

/-- Under the replacement product law, the cycle gap is almost surely positive. This turns the
local pointwise gap on the rectangles into the strict positivity needed for the global cost-drop
argument. -/
lemma integral_cycleGap_replacementPiMeasure_pos
    {n : ℕ} [NeZero n] {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    [OpensMeasurableSpace (X × Y)]
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support) :
    0 < ∫ ω, cycleGap c ω ∂replacementPiMeasureMeasure π hdata := by
  have hall_rect :
      ∀ᵐ ω ∂replacementPiMeasureMeasure π hdata, ∀ i, ω i ∈ hdata.U i ×ˢ hdata.V i := by
    rw [ae_all_iff]
    intro i
    exact ae_mem_replacementPiMeasure_rect π hdata hmem i
  have hgap_ae :
      ∀ᵐ ω ∂replacementPiMeasureMeasure π hdata, 0 < cycleGap c ω := by
    filter_upwards [hall_rect] with ω hω
    exact hdata.gap_pos ω hω
  have hnonneg_ae :
      0 ≤ᵐ[replacementPiMeasureMeasure π hdata] fun ω : Fin (n + 1) → X × Y ↦ cycleGap c ω :=
    hgap_ae.mono fun _ hω ↦ le_of_lt hω
  have hint :
      Integrable
        (fun ω : Fin (n + 1) → X × Y ↦ cycleGap c ω)
        (replacementPiMeasureMeasure π hdata) := by
    have hdiag :
        Integrable (fun ω : Fin (n + 1) → X × Y ↦ ∑ i, c (ω i).1 (ω i).2)
          (replacementPiMeasureMeasure π hdata) := by
      simpa only [Finset.sum_apply] using integrable_finset_sum (s := Finset.univ)
        (fun i _ ↦ integrable_replacementPiMeasure_diag hc hdata π hmem i)
    have hcross :
        Integrable (fun ω : Fin (n + 1) → X × Y ↦ ∑ i, c (ω i).1 (ω (i + 1)).2)
          (replacementPiMeasureMeasure π hdata) := by
      simpa only [Finset.sum_apply] using integrable_finset_sum (s := Finset.univ)
        (fun i _ ↦ integrable_replacementPiMeasure_cross hc hdata π hmem i)
    simpa [cycleGap] using hdiag.sub hcross
  have hnot_ae_zero :
      ¬ ((fun ω : Fin (n + 1) → X × Y ↦ cycleGap c ω) =ᵐ[replacementPiMeasureMeasure π hdata] 0) :=
      by
    intro hzero
    have hfalse : ∀ᵐ ω ∂replacementPiMeasureMeasure π hdata, False := by
      filter_upwards [hgap_ae, hzero] with ω hω hz
      simp [hz] at hω
    have huniv_zero :
        replacementPiMeasureMeasure π hdata Set.univ = 0 := by
      simp [ae_iff] at hfalse
    have huniv_one : replacementPiMeasureMeasure π hdata Set.univ = 1 := by
      simp [replacementPiMeasureMeasure, replacementPiMeasure]
    have hone_zero := huniv_one.symm.trans huniv_zero
    exact one_ne_zero hone_zero
  have hne :
      ∫ ω, cycleGap c ω ∂replacementPiMeasureMeasure π hdata ≠ 0 := by
    intro hzero
    exact hnot_ae_zero ((integral_eq_zero_iff_of_nonneg_ae hnonneg_ae hint).1 hzero)
  exact lt_of_le_of_ne (integral_nonneg_of_ae hnonneg_ae) (by simpa using hne.symm)

/-- The total inserted cost is strictly smaller than the total removed cost. This is the numerical
heart of the perturbation argument. -/
lemma integral_cost_newPiece_lt_integral_cost_oldPiece
    {n : ℕ} [NeZero n] {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    [OpensMeasurableSpace (X × Y)]
    {c : X → Y → ℝ} (hc : Continuous fun z : X × Y ↦ c z.1 z.2)
    {p : Fin (n + 1) → X × Y} (hdata : CycleGapNeighborhoodData c p)
    (π : Coupling μ ν)
    (hmem : ∀ i, p i ∈ ((π.toTransportPlan : TransportPlan X Y) : Measure (X × Y)).support) :
    ∫ z, c z.1 z.2 ∂(newPiece π hdata : Measure (X × Y)) <
      ∫ z, c z.1 z.2 ∂(oldPiece π hdata : Measure (X × Y)) := by
  have hmass_pos : 0 < commonRemovableMass π hdata :=
    commonRemovableMass_pos_of_mem_support π hdata hmem
  have hgap_pos :
      0 < ∫ ω, cycleGap c ω ∂replacementPiMeasureMeasure π hdata :=
    integral_cycleGap_replacementPiMeasure_pos (n := n) hc hdata π hmem
  have hdiff :
      (∫ z, c z.1 z.2 ∂(oldPiece π hdata : Measure (X × Y))) -
          (∫ z, c z.1 z.2 ∂(newPiece π hdata : Measure (X × Y))) =
        (commonRemovableMass π hdata : ℝ) *
          ∫ ω, cycleGap c ω ∂replacementPiMeasureMeasure π hdata :=
    integral_cost_oldPiece_sub_integral_cost_newPiece_eq_commonRemovableMass_mul_integral_cycleGap
      (n := n) hc hdata π hmem
  have hpos_rhs :
      0 < (commonRemovableMass π hdata : ℝ) *
        ∫ ω, cycleGap c ω ∂replacementPiMeasureMeasure π hdata := by
    exact mul_pos (show 0 < (commonRemovableMass π hdata : ℝ) by exact_mod_cast hmass_pos) hgap_pos
  linarith [hdiff, hpos_rhs]

end ReplacementCostDrop

end OptimalTransport
