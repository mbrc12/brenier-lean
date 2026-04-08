import OptimalTransport.Existence
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Constructions.SumProd

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

end LocalGap

end OptimalTransport
