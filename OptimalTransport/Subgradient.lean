import OptimalTransport.CyclicMonotone

namespace OptimalTransport

open scoped BigOperators

/-!
This file introduces the local subgradient API needed for the convex-analysis side of the OT
development.

At this stage we only formalize the elementary algebraic layer:

* `Subgradient φ x y`: the first-order supporting-hyperplane inequality for a real-valued
  function `φ` on an inner product space;
* `SubgradientGraph φ`: the graph of the subgradient relation;
* basic algebraic transport lemmas for subgradients under
  `z ↦ φ z + ⟪v, z⟫ + b` and under positive rescaling.

These are exactly the manipulations that later appear when passing between convex potentials and
the Brenier-friendly cost class `a x + b y - κ * ⟪x, y⟫`.
-/

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `y` is a subgradient of the real-valued function `φ` at `x` if the affine function
`z ↦ φ x + ⟪y, z - x⟫` is a global lower support for `φ`.

The definition is phrased using the inner product so that, in finite-dimensional real inner
product spaces, subgradients are represented by vectors rather than by continuous linear
functionals. -/
def Subgradient (φ : E → ℝ) (x y : E) : Prop :=
  ∀ z : E, φ x + inner ℝ y (z - x) ≤ φ z

/-- The graph of the subgradient relation. This is the set that later gets compared with supports
of optimal plans and with cyclically monotone sets. -/
def SubgradientGraph (φ : E → ℝ) : Set (E × E) :=
  {p | Subgradient φ p.1 p.2}

/-- Membership in the subgradient graph is just the corresponding pointwise subgradient statement.
This lemma keeps the definition transparent for rewriting. -/
@[simp]
lemma mem_SubgradientGraph {φ : E → ℝ} {p : E × E} :
    p ∈ SubgradientGraph φ ↔ Subgradient φ p.1 p.2 :=
  Iff.rfl

/-- The zero vector is a subgradient of a constant function at every point. -/
lemma subgradient_const (b : ℝ) (x : E) :
    Subgradient (fun _ : E ↦ b) x 0 := by
  intro z
  simp

/-- For the affine function `z ↦ ⟪v, z⟫ + b`, the vector `v` is a subgradient at every point.
This is the model calculation behind all affine-perturbation lemmas below. -/
lemma subgradient_inner_const (v : E) (b : ℝ) (x : E) :
    Subgradient (fun z : E ↦ inner ℝ v z + b) x v := by
  intro z
  have hinner : inner ℝ v x + inner ℝ v (z - x) = inner ℝ v z := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (inner_add_right (𝕜 := ℝ) v x (z - x)).symm
  calc
    (inner ℝ v x + b) + inner ℝ v (z - x)
      = inner ℝ v x + inner ℝ v (z - x) + b := by
          ac_rfl
    _ = inner ℝ v z + b := by
          rw [hinner]
    _ ≤ (fun z : E ↦ inner ℝ v z + b) z := by
          rfl

namespace Subgradient

variable {φ : E → ℝ} {x y v : E} {b κ : ℝ}

/-- Adding the affine term `z ↦ ⟪v, z⟫ + b` shifts a subgradient by the vector `v`.

This is the basic algebraic move used later to absorb the `x`-only affine part of a
pairing-type cost into the convex potential. -/
lemma add_inner_const (h : Subgradient φ x y) (v : E) (b : ℝ) :
    Subgradient (fun z : E ↦ φ z + inner ℝ v z + b) x (y + v) := by
  intro z
  have hz : φ x + inner ℝ y (z - x) ≤ φ z := h z
  have hinner : inner ℝ v x + inner ℝ v (z - x) = inner ℝ v z := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (inner_add_right (𝕜 := ℝ) v x (z - x)).symm
  calc
    (φ x + inner ℝ v x + b) + inner ℝ (y + v) (z - x)
      = φ x + inner ℝ y (z - x) + (inner ℝ v x + inner ℝ v (z - x) + b) := by
          simp [inner_add_left, add_assoc, add_left_comm, add_comm]
    _ = φ x + inner ℝ y (z - x) + (inner ℝ v z + b) := by
          rw [hinner]
    _ ≤ φ z + (inner ℝ v z + b) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_right hz (inner ℝ v z + b)
    _ = (fun z : E ↦ φ z + inner ℝ v z + b) z := by
          simp [add_left_comm, add_comm]

/-- Affine perturbation by `z ↦ ⟪v, z⟫ + b` is reversible: it shifts the subgradient by exactly
the same vector `v`. -/
lemma add_inner_const_iff :
    Subgradient (fun z : E ↦ φ z + inner ℝ v z + b) x y ↔
      Subgradient φ x (y - v) := by
  constructor
  · intro h
    have h' := h.add_inner_const (-v) (-b)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  · intro h
    have h' := h.add_inner_const v b
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'

/-- Multiplying a function by a nonnegative scalar multiplies every subgradient by the same
scalar. This is the algebraic move responsible for the coefficient `κ` in
`a x + b y - κ * ⟪x, y⟫`. -/
lemma smul (h : Subgradient φ x y) (hκ : 0 ≤ κ) :
    Subgradient (fun z : E ↦ κ * φ z) x (κ • y) := by
  intro z
  have hz : κ * (φ x + inner ℝ y (z - x)) ≤ κ * φ z :=
    mul_le_mul_of_nonneg_left (h z) hκ
  have hinner : inner ℝ (κ • y) (z - x) = κ * inner ℝ y (z - x) := by
    simpa using (real_inner_smul_left y (z - x) κ)
  calc
    (κ * φ x) + inner ℝ (κ • y) (z - x)
      = κ * (φ x + inner ℝ y (z - x)) := by
          rw [hinner]
          ring_nf
    _ ≤ κ * φ z := hz
    _ = (fun z : E ↦ κ * φ z) z := by
          rfl

/-- Positive rescaling is reversible on the subgradient relation. -/
lemma smul_iff_of_pos (hκ : 0 < κ) :
    Subgradient (fun z : E ↦ κ * φ z) x (κ • y) ↔ Subgradient φ x y := by
  constructor
  · intro h
    have h' := h.smul (κ := κ⁻¹) (show 0 ≤ κ⁻¹ by positivity)
    simpa [smul_eq_mul, mul_assoc, hκ.ne', sub_eq_add_neg] using h'
  · intro h
    exact h.smul (le_of_lt hκ)

/-- Combined affine-shift and positive-rescaling rule for subgradients.

This is the exact subgradient-side normalization used later when rewriting Brenier-friendly costs:
first absorb the `x`-affine term into the potential, then absorb the coefficient `κ` into the
subgradient variable. -/
lemma smul_add_inner_const_iff_of_pos (hκ : 0 < κ) :
    Subgradient (fun z : E ↦ κ * φ z + inner ℝ v z + b) x (κ • y + v) ↔
      Subgradient φ x y := by
  constructor
  · intro h
    have h₁ :
        Subgradient (fun z : E ↦ κ * φ z) x (κ • y) := by
      have h₂ := (Subgradient.add_inner_const_iff
        (φ := fun z : E ↦ κ * φ z) (x := x) (y := κ • y + v) (v := v) (b := b)).1 h
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h₂
    exact (Subgradient.smul_iff_of_pos (φ := φ) (x := x) (y := y) hκ).1 h₁
  · intro h
    have h₁ :
        Subgradient (fun z : E ↦ κ * φ z) x (κ • y) :=
      (Subgradient.smul_iff_of_pos (φ := φ) (x := x) (y := y) hκ).2 h
    have h₂ := (Subgradient.add_inner_const_iff
      (φ := fun z : E ↦ κ * φ z) (x := x) (y := κ • y + v) (v := v) (b := b)).2
        (by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h₁)
    exact h₂

end Subgradient

/-- A finite family of points in a subgradient graph satisfies the pairing inequality. This is the
core telescoping estimate behind cyclical monotonicity of subgradient graphs. -/
lemma subgradientGraph_pairing
    {φ : E → ℝ} :
    ∀ n (p : Fin (n + 1) → E × E), (∀ i, p i ∈ SubgradientGraph φ) →
      ∑ i, inner ℝ (p i).1 (p (i + 1)).2 ≤ ∑ i, inner ℝ (p i).1 (p i).2 := by
  intro n p hmem
  have hsum :
      ∑ i, (φ (p (i + 1)).1 + inner ℝ (p (i + 1)).2 ((p i).1 - (p (i + 1)).1)) ≤
        ∑ i, φ (p i).1 := by
    exact Finset.sum_le_sum fun i _ ↦ hmem (i + 1) (p i).1
  have hphi :
      (∑ i, φ (p (i + 1)).1) = ∑ i, φ (p i).1 := by
    simpa [Function.comp] using
      (Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) (fun i : Fin (n + 1) ↦ φ (p i).1))
  have hdiag :
      (∑ i, inner ℝ (p (i + 1)).1 (p (i + 1)).2) = ∑ i, inner ℝ (p i).1 (p i).2 := by
    simpa [Function.comp] using
      (Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1)))
        (fun i : Fin (n + 1) ↦ inner ℝ (p i).1 (p i).2))
  have hinnerSum :
      (∑ i, inner ℝ (p (i + 1)).2 ((p i).1 - (p (i + 1)).1)) =
        (∑ i, inner ℝ (p i).1 (p (i + 1)).2) -
          (∑ i, inner ℝ (p (i + 1)).1 (p (i + 1)).2) := by
    calc
      (∑ i, inner ℝ (p (i + 1)).2 ((p i).1 - (p (i + 1)).1))
        = ∑ i,
            (inner ℝ (p (i + 1)).2 (p i).1 -
              inner ℝ (p (i + 1)).2 (p (i + 1)).1) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [inner_sub_right]
      _ = (∑ i, inner ℝ (p i).1 (p (i + 1)).2) -
            (∑ i, inner ℝ (p (i + 1)).1 (p (i + 1)).2) := by
              simp_rw [real_inner_comm]
              rw [Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib] at hsum
  have hrewrite :
      (∑ i, φ (p (i + 1)).1) + (∑ i, inner ℝ (p i).1 (p (i + 1)).2) -
          (∑ i, inner ℝ (p (i + 1)).1 (p (i + 1)).2) ≤
        ∑ i, φ (p i).1 := by
    rw [hinnerSum] at hsum
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  rw [hphi, hdiag] at hrewrite
  linarith

/-- The graph of a subgradient relation is cyclically monotone for the cost `-(x · y)`. This is
the standard easy direction of Rockafellar's theorem, proved by telescoping the
supporting-hyperplane inequalities around the cycle. -/
lemma cCyclicallyMonotone_subgradientGraph_negInner
    {φ : E → ℝ} :
    CCyclicallyMonotone (fun x y ↦ -inner ℝ x y) (SubgradientGraph φ) := by
  intro n p _hp hmem
  have hpair := subgradientGraph_pairing (φ := φ) n p hmem
  simpa [Finset.sum_neg_distrib] using neg_le_neg hpair

/-- Subgradient graphs are cyclically monotone for every Brenier-friendly cost
`a x + b y - κ * ⟪x, y⟫` with `κ ≥ 0`. The `x`-only and `y`-only terms cancel along cycles, so
the proof reduces to the pairing inequality from `subgradientGraph_pairing`. -/
lemma cCyclicallyMonotone_subgradientGraph_of_pairing
    {φ : E → ℝ} {a b : E → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) :
    CCyclicallyMonotone (fun x y ↦ a x + b y - κ * inner ℝ x y) (SubgradientGraph φ) := by
  intro n p _hp hmem
  have hpair := subgradientGraph_pairing (φ := φ) n p hmem
  have hb :
      (∑ i, b (p (i + 1)).2) = ∑ i, b (p i).2 := by
    simpa [Function.comp] using
      (Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) (fun i : Fin (n + 1) ↦ b (p i).2))
  have hscaled :
      κ * (∑ i, inner ℝ (p i).1 (p (i + 1)).2) ≤
        κ * (∑ i, inner ℝ (p i).1 (p i).2) :=
    mul_le_mul_of_nonneg_left hpair hκ
  have hmain :
      (∑ i, a (p i).1) + (∑ i, b (p i).2) - κ * (∑ i, inner ℝ (p i).1 (p i).2) ≤
        (∑ i, a (p i).1) + (∑ i, b (p (i + 1)).2) -
          κ * (∑ i, inner ℝ (p i).1 (p (i + 1)).2) := by
    rw [hb]
    linarith
  simpa [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, add_assoc,
    add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using hmain

end Basic

end OptimalTransport
