import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace OptimalTransport

/-!
This file starts the refactor from real-valued convex potentials to proper extended-real-valued
potentials.

For now the layer is intentionally small. We only introduce the objects that later sit between the
Rockafellar construction and the Brenier extraction step:

* `EffectiveDomain Φ`: the finite locus `{x | Φ x < ⊤}` of a function `Φ : E → WithTop ℝ`;
* `ProperSubgradient Φ x y`: the supporting-hyperplane inequality for an extended-real-valued
  function, together with the finiteness of `Φ x`;
* `ProperSubgradientGraph Φ`: the graph of that relation;
* `IsProperConvex Φ`: a practical proper-convex predicate, phrased as convexity of the effective
  domain together with convexity of the real-valued restriction `x ↦ (Φ x).untopD 0` on that
  domain.

We also record the two algebraic manipulations that will be reused later:

* affine perturbation by `z ↦ ⟪v, z⟫ + b`;
* positive rescaling of finite values, keeping `⊤` fixed.

The file deliberately stops before any Rockafellar-specific construction. The point is to put the
extended-real API in place first, while staying compatible with the existing real-valued
convex-analysis layer.
-/

open scoped BigOperators

section ProperConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The effective domain of an extended-real-valued function is the set where the value is finite.

Since we work with `WithTop ℝ`, this means exactly the strict upper inequality `Φ x < ⊤`. -/
def EffectiveDomain (Φ : E → WithTop ℝ) : Set E :=
  {x | Φ x < ⊤}

/-- `y` is a proper subgradient of `Φ` at `x` if `Φ x` is finite and the affine function
`z ↦ Φ x + ⟪y, z - x⟫` is a global lower support for `Φ`.

The codomain is `WithTop ℝ`, so the inequality is stated directly there. Rewriting it into an
ordinary real inequality is handled by lemmas below once the relevant values are known to be
finite. -/
def ProperSubgradient (Φ : E → WithTop ℝ) (x y : E) : Prop :=
  Φ x < ⊤ ∧ ∀ z : E, Φ x + ((inner ℝ y (z - x) : ℝ) : WithTop ℝ) ≤ Φ z

/-- The graph of the proper subgradient relation. This is the extended-real analogue of the
real-valued `SubgradientGraph`. -/
def ProperSubgradientGraph (Φ : E → WithTop ℝ) : Set (E × E) :=
  {p | ProperSubgradient Φ p.1 p.2}

/-- A practical proper-convex predicate for `WithTop ℝ`-valued functions.

The predicate says two things:

* the effective domain is nonempty, so the function is not identically `⊤`;
* on that effective domain, the real-valued restriction obtained from `untopD 0` is convex.

This is the right amount of structure for the present refactor stage. It avoids committing yet to a
global epigraph-based API on `WithTop ℝ`, while still recording the exact finite-locus convexity
that Brenier will later use. -/
def IsProperConvex (Φ : E → WithTop ℝ) : Prop :=
  (EffectiveDomain Φ).Nonempty ∧
    ConvexOn ℝ (EffectiveDomain Φ) (fun x => (Φ x).untopD 0)

/-- The real-valued restriction of an extended-real-valued function to its effective domain. -/
noncomputable def toRealOnEffectiveDomain (Φ : E → WithTop ℝ) :
    EffectiveDomain Φ → ℝ :=
  fun x => (Φ x).untop (WithTop.lt_top_iff_ne_top.mp x.2)

/-- Adding a finite real-valued perturbation to an extended-real-valued potential. -/
def addReal (Φ : E → WithTop ℝ) (ψ : E → ℝ) : E → WithTop ℝ :=
  fun x => Φ x + ((ψ x : ℝ) : WithTop ℝ)

/-- Affine perturbation by `z ↦ ⟪v, z⟫ + b`. This is the proper-convex analogue of the affine
shift used for ordinary subgradients. -/
def addInnerConst (Φ : E → WithTop ℝ) (v : E) (b : ℝ) : E → WithTop ℝ :=
  addReal Φ fun z => inner ℝ v z + b

/-- Positive rescaling of finite values, leaving `⊤` fixed.

`WithTop ℝ` does not carry the linear scalar action one would want for this API, so we define the
pointwise action directly: finite values are multiplied by `κ`, and `⊤` stays `⊤`. -/
def scale (κ : ℝ) (Φ : E → WithTop ℝ) : E → WithTop ℝ :=
  fun x => Option.map (fun r : ℝ => κ * r) (Φ x)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp]
lemma mem_EffectiveDomain {Φ : E → WithTop ℝ} {x : E} :
    x ∈ EffectiveDomain Φ ↔ Φ x < ⊤ :=
  Iff.rfl

@[simp]
lemma mem_ProperSubgradientGraph {Φ : E → WithTop ℝ} {p : E × E} :
    p ∈ ProperSubgradientGraph Φ ↔ ProperSubgradient Φ p.1 p.2 :=
  Iff.rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp]
lemma scale_top (κ : ℝ) :
    scale κ (fun _ : E => (⊤ : WithTop ℝ)) = fun _ => (⊤ : WithTop ℝ) := by
  funext x
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp]
lemma scale_coe (κ r : ℝ) :
    scale κ (fun _ : E => ((r : ℝ) : WithTop ℝ)) = fun _ => (((κ * r : ℝ) : ℝ) : WithTop ℝ) := by
  funext x
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp]
lemma addReal_apply (Φ : E → WithTop ℝ) (ψ : E → ℝ) (x : E) :
    addReal Φ ψ x = Φ x + ((ψ x : ℝ) : WithTop ℝ) :=
  rfl

@[simp]
lemma addInnerConst_apply (Φ : E → WithTop ℝ) (v : E) (b : ℝ) (x : E) :
    addInnerConst Φ v b x = Φ x + ((inner ℝ v x + b : ℝ) : WithTop ℝ) :=
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp]
lemma scale_apply_top {κ : ℝ} {Φ : E → WithTop ℝ} {x : E} (hx : Φ x = ⊤) :
    scale κ Φ x = ⊤ := by
  rw [scale, hx]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp]
lemma scale_apply_coe {κ r : ℝ} {Φ : E → WithTop ℝ} {x : E} (hx : Φ x = ((r : ℝ) : WithTop ℝ)) :
    scale κ Φ x = (((κ * r : ℝ) : ℝ) : WithTop ℝ) := by
  rw [scale, hx]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp]
lemma coe_toRealOnEffectiveDomain {Φ : E → WithTop ℝ} (x : EffectiveDomain Φ) :
    ((toRealOnEffectiveDomain Φ x : ℝ) : WithTop ℝ) = Φ x := by
  exact WithTop.coe_untop _ (WithTop.lt_top_iff_ne_top.mp x.2)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp]
lemma toRealOnEffectiveDomain_eq_untopD {Φ : E → WithTop ℝ} (x : EffectiveDomain Φ) :
    toRealOnEffectiveDomain Φ x = (Φ x).untopD 0 := by
  have hcoe : ((toRealOnEffectiveDomain Φ x : ℝ) : WithTop ℝ) = Φ x :=
    coe_toRealOnEffectiveDomain (Φ := Φ) x
  exact congrArg (WithTop.untopD 0) hcoe

namespace ProperSubgradient

variable {Φ : E → WithTop ℝ} {x y v z : E} {b κ : ℝ}

/-- A proper subgradient point always lies in the effective domain. -/
lemma mem_effectiveDomain (h : ProperSubgradient Φ x y) : x ∈ EffectiveDomain Φ :=
  h.1

/-- A proper subgradient point has finite value. This packaged form is more convenient than
repeatedly rewriting `lt_top_iff_ne_top`. -/
lemma ne_top (h : ProperSubgradient Φ x y) : Φ x ≠ ⊤ :=
  WithTop.lt_top_iff_ne_top.mp h.1

/-- The supporting-hyperplane inequality, rewritten as an ordinary real inequality when both
endpoint values are finite. -/
lemma real_inequality (h : ProperSubgradient Φ x y) (hz : z ∈ EffectiveDomain Φ) :
    (Φ x).untop h.ne_top + inner ℝ y (z - x) ≤
      (Φ z).untop (WithTop.lt_top_iff_ne_top.mp hz) := by
  have hxeq : (((Φ x).untop h.ne_top : ℝ) : WithTop ℝ) = Φ x :=
    WithTop.coe_untop _ h.ne_top
  have hzeq :
      (((Φ z).untop (WithTop.lt_top_iff_ne_top.mp hz) : ℝ) : WithTop ℝ) = Φ z :=
    WithTop.coe_untop _ (WithTop.lt_top_iff_ne_top.mp hz)
  have hle := h.2 z
  rw [← hxeq, ← hzeq, ← WithTop.coe_add] at hle
  exact WithTop.coe_le_coe.mp hle

/-- Adding a finite affine functional shifts a proper subgradient by the corresponding vector.

The proof is the same algebra as in the real-valued case. The only extra work is to split off the
case `Φ z = ⊤`, where the target inequality is automatic. -/
lemma add_inner_const (h : ProperSubgradient Φ x y) (v : E) (b : ℝ) :
    ProperSubgradient (addInnerConst Φ v b) x (y + v) := by
  constructor
  · have hxeq : (((Φ x).untop h.ne_top : ℝ) : WithTop ℝ) = Φ x :=
      WithTop.coe_untop _ h.ne_top
    rw [addInnerConst_apply, ← hxeq, ← WithTop.coe_add]
    exact WithTop.coe_lt_top _
  · intro z
    by_cases hz : Φ z = ⊤
    · simp [addInnerConst_apply, hz]
    · have hz_mem : z ∈ EffectiveDomain Φ := by
        simpa [EffectiveDomain] using WithTop.lt_top_iff_ne_top.mpr hz
      have hreal := h.real_inequality hz_mem
      have hinner : inner ℝ v x + inner ℝ v (z - x) = inner ℝ v z := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (inner_add_right (𝕜 := ℝ) v x (z - x)).symm
      have hreal' :
          ((Φ x).untop h.ne_top + (inner ℝ v x + b)) + inner ℝ (y + v) (z - x) ≤
            (Φ z).untop hz + (inner ℝ v z + b) := by
        calc
          ((Φ x).untop h.ne_top + (inner ℝ v x + b)) + inner ℝ (y + v) (z - x)
            = ((Φ x).untop h.ne_top + inner ℝ y (z - x)) +
                (inner ℝ v x + inner ℝ v (z - x) + b) := by
                  simp [inner_add_left, add_assoc, add_left_comm, add_comm]
          _ = ((Φ x).untop h.ne_top + inner ℝ y (z - x)) + (inner ℝ v z + b) := by
                rw [hinner]
          _ ≤ (Φ z).untop hz + (inner ℝ v z + b) := by
                gcongr
      have hxeq : (((Φ x).untop h.ne_top : ℝ) : WithTop ℝ) = Φ x :=
        WithTop.coe_untop _ h.ne_top
      have hzeq : (((Φ z).untop hz : ℝ) : WithTop ℝ) = Φ z :=
        WithTop.coe_untop _ hz
      rw [addInnerConst_apply, addInnerConst_apply, ← hxeq, ← hzeq]
      change
        ((((Φ x).untop h.ne_top + (inner ℝ v x + b)) + inner ℝ (y + v) (z - x) : ℝ) :
          WithTop ℝ) ≤
          (((Φ z).untop hz + (inner ℝ v z + b) : ℝ) : WithTop ℝ)
      exact WithTop.coe_le_coe.mpr hreal'

/-- Positive rescaling of a proper subgradient. Finite values are multiplied by `κ`, and `⊤`
remains `⊤`. -/
lemma scale (h : ProperSubgradient Φ x y) (hκ : 0 ≤ κ) :
    ProperSubgradient (scale κ Φ) x (κ • y) := by
  constructor
  · rw [scale_apply_coe (x := x) (r := (Φ x).untop h.ne_top)
        (by exact (WithTop.coe_untop _ h.ne_top).symm)]
    exact WithTop.coe_lt_top _
  · intro z
    by_cases hz : Φ z = ⊤
    · rw [scale_apply_top (x := z) hz]
      exact le_top
    · have hz_mem : z ∈ EffectiveDomain Φ := by
        simpa [EffectiveDomain] using WithTop.lt_top_iff_ne_top.mpr hz
      have hreal := h.real_inequality hz_mem
      have hscaled :
          κ * ((Φ x).untop h.ne_top + inner ℝ y (z - x)) ≤ κ * (Φ z).untop hz :=
        mul_le_mul_of_nonneg_left hreal hκ
      have hreal' :
          κ * (Φ x).untop h.ne_top + inner ℝ (κ • y) (z - x) ≤ κ * (Φ z).untop hz := by
        simpa [real_inner_smul_left, mul_add, add_comm, add_left_comm, add_assoc] using hscaled
      rw [scale_apply_coe (x := x) (r := (Φ x).untop h.ne_top)
            (by exact (WithTop.coe_untop _ h.ne_top).symm)]
      rw [scale_apply_coe (x := z) (r := (Φ z).untop hz)
            (by exact (WithTop.coe_untop _ hz).symm)]
      change
        (((κ * (Φ x).untop h.ne_top + inner ℝ (κ • y) (z - x) : ℝ) : WithTop ℝ) ≤
          (((κ * (Φ z).untop hz : ℝ) : ℝ) : WithTop ℝ))
      exact WithTop.coe_le_coe.mpr hreal'

end ProperSubgradient

namespace IsProperConvex

variable {Φ : E → WithTop ℝ}

/-- A proper convex function has a nonempty effective domain. -/
lemma nonempty_effectiveDomain (h : IsProperConvex Φ) :
    (EffectiveDomain Φ).Nonempty :=
  h.1

/-- The real-valued restriction to the effective domain is convex. -/
lemma convexOn_effectiveDomain (h : IsProperConvex Φ) :
    ConvexOn ℝ (EffectiveDomain Φ) (fun x => (Φ x).untopD 0) :=
  h.2

/-- In particular, the effective domain itself is convex. -/
lemma convex_effectiveDomain (h : IsProperConvex Φ) :
    Convex ℝ (EffectiveDomain Φ) :=
  h.2.1

end IsProperConvex

end ProperConvex

end OptimalTransport
