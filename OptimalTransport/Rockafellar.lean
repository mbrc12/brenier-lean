import OptimalTransport.Subgradient
import Mathlib.Data.List.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace OptimalTransport

open scoped BigOperators

/-!
This file implements the finite-chain Rockafellar candidate in the real-valued setting used by the
current repository.

The key objects are:

* `rockafellarChainValue`: the affine functional attached to one finite chain of pairs;
* `rockafellarValueSet base Γ x`: the set of all chain values at `x`, rooted at `base` and using
  points of `Γ`;
* `rockafellarPotential base Γ h_bdd`: the supremum of those values, assuming they are bounded
  above for every target point `x`.

The current file only sets up the candidate and the basic order-theoretic lemmas that are already
stable in the present API:

* singleton chains rooted at `base` give the initial nonemptiness statements;
* appending one point to a chain has the expected algebraic effect on the chain value;
* from this append lemma one gets the Rockafellar containment theorem
  `Γ ⊆ SubgradientGraph φ_Γ` under the explicit bounded-above hypothesis already built into the
  real-valued potential;
* the resulting potential is convex.

In the fully general OT story, cyclic monotonicity is used to justify the finiteness of the rooted
value sets. In the present real-valued file we keep that finiteness as an explicit assumption
`h_bdd`, and then prove the graph-containment theorem from the rooted supremum construction itself.
-/

section Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine functional associated to a finite chain of points in `E × E`.

If the chain is `[(x₀,y₀), …, (xₙ,yₙ)]`, then this is the standard Rockafellar expression

`∑_{i < n} ⟪yᵢ, xᵢ₊₁ - xᵢ⟫ + ⟪yₙ, x - xₙ⟫`.

The empty chain contributes `0`, which gives a canonical lower support for the eventual supremum.
-/
def rockafellarChainValue : List (E × E) → E → ℝ
  | [], _ => 0
  | [p], x => inner ℝ p.2 (x - p.1)
  | p :: q :: l, x => inner ℝ p.2 (q.1 - p.1) + rockafellarChainValue (q :: l) x

/-- The set of all rooted finite-chain values at the point `x`.

The root condition `l.head? = some base` records the normalization point for the construction.
Unlike the earlier placeholder version of this file, this is the standard Rockafellar value set:
only genuine nonempty rooted chains are allowed. In particular, nonemptiness of the value set now
comes from the singleton chain `[base]`, and therefore requires the hypothesis `base ∈ Γ`. -/
def rockafellarValueSet (base : E × E) (Γ : Set (E × E)) (x : E) : Set ℝ :=
  {r | ∃ l : List (E × E),
      l ≠ [] ∧ l.head? = some base ∧ List.Forall (fun p ↦ p ∈ Γ) l ∧
        r = rockafellarChainValue l x}

/-- The real-valued Rockafellar potential attached to `base` and `Γ`, defined as the supremum of
the rooted finite-chain values.

Since the codomain is `ℝ`, we keep the finiteness requirement explicit as the hypothesis that each
value set is bounded above. -/
noncomputable def rockafellarPotential (base : E × E) (Γ : Set (E × E))
    (_h_bdd : ∀ x : E, BddAbove (rockafellarValueSet base Γ x)) (x : E) : ℝ :=
  sSup (rockafellarValueSet base Γ x)

/-- The singleton rooted chain `[base]` contributes the affine functional
`x ↦ ⟪base.2, x - base.1⟫`. This is the basic witness used both for nonemptiness of the value sets
and for the normalization statements at the root. -/
lemma singleton_mem_rockafellarValueSet {base : E × E} {Γ : Set (E × E)}
    (hbase : base ∈ Γ) (x : E) :
    inner ℝ base.2 (x - base.1) ∈ rockafellarValueSet base Γ x := by
  refine ⟨[base], by simp, by simp, ?_, by simp [rockafellarChainValue]⟩
  simp [hbase]

/-- If the root point belongs to `Γ`, then every value set is nonempty by using the singleton
rooted chain `[base]`. -/
lemma rockafellarValueSet_nonempty {base : E × E} {Γ : Set (E × E)} (hbase : base ∈ Γ) (x : E) :
    (rockafellarValueSet base Γ x).Nonempty :=
  ⟨_, singleton_mem_rockafellarValueSet hbase x⟩

/-- Any explicit chain value is bounded above by the Rockafellar potential. -/
lemma le_rockafellarPotential_of_mem_valueSet
    {base : E × E} {Γ : Set (E × E)} {h_bdd : ∀ x : E, BddAbove (rockafellarValueSet base Γ x)}
    {x : E} {r : ℝ} (hr : r ∈ rockafellarValueSet base Γ x) :
    r ≤ rockafellarPotential base Γ h_bdd x := by
  simpa [rockafellarPotential] using (le_csSup (h_bdd x) hr)

/-- The affine chain functional for a singleton list is exactly the supporting hyperplane
`x ↦ ⟪y, x - x₀⟫`. -/
@[simp]
lemma rockafellarChainValue_singleton (p : E × E) (x : E) :
    rockafellarChainValue [p] x = inner ℝ p.2 (x - p.1) :=
  rfl

/-- Appending one more point to the chain adds exactly one more affine step.

This is the algebraic identity behind the Rockafellar subgradient theorem: if a chain contributes
the value `r` at `x`, then appending `(x, y)` produces the value `r + ⟪y, z - x⟫` at `z`. -/
lemma rockafellarChainValue_concat_singleton :
    ∀ (l : List (E × E)) (p : E × E) (z : E),
      rockafellarChainValue (l ++ [p]) z =
        rockafellarChainValue l p.1 + inner ℝ p.2 (z - p.1)
  | [], p, z => by
      simp [rockafellarChainValue]
  | [q], p, z => by
      simp [rockafellarChainValue]
  | q :: r :: l, p, z => by
      simp [rockafellarChainValue]
      have h :=
        congrArg (fun t => inner ℝ q.2 (r.1 - q.1) + t)
          (rockafellarChainValue_concat_singleton (r :: l) p z)
      simpa [add_assoc] using h

/-- Affine behavior of the chain functional in the target variable.

This is the key calculation behind convexity of the Rockafellar potential: every fixed finite
chain contributes an affine function of the endpoint `x`. -/
lemma rockafellarChainValue_convexCombination :
    ∀ (l : List (E × E)) (x y : E) (a b : ℝ), a + b = 1 →
      rockafellarChainValue l (a • x + b • y) =
        a * rockafellarChainValue l x + b * rockafellarChainValue l y
  | [], x, y, a, b, hab => by
      simp [rockafellarChainValue]
  | [p], x, y, a, b, hab => by
      have hsub :
          a • x + b • y - p.1 = a • (x - p.1) + b • (y - p.1) := by
        have hp1 : p.1 = (a + b) • p.1 := by
          simp [hab]
        have hp : p.1 = a • p.1 + b • p.1 := by
          simpa [add_smul] using hp1
        calc
          a • x + b • y - p.1
            = a • x + b • y - (a • p.1 + b • p.1) := by
                simpa using congrArg (fun t : E => a • x + b • y - t) hp
          _ = a • (x - p.1) + b • (y - p.1) := by
                simp [sub_eq_add_neg, smul_add, add_assoc, add_left_comm, add_comm]
      calc
        rockafellarChainValue [p] (a • x + b • y)
          = inner ℝ p.2 (a • (x - p.1) + b • (y - p.1)) := by
              simp [rockafellarChainValue, hsub]
        _ = a * inner ℝ p.2 (x - p.1) + b * inner ℝ p.2 (y - p.1) := by
              rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        _ = a * rockafellarChainValue [p] x + b * rockafellarChainValue [p] y := by
              simp [rockafellarChainValue]
  | p :: q :: l, x, y, a, b, hab => by
      let I : ℝ := inner ℝ p.2 (q.1 - p.1)
      let tx : ℝ := rockafellarChainValue (q :: l) x
      let ty : ℝ := rockafellarChainValue (q :: l) y
      calc
        rockafellarChainValue (p :: q :: l) (a • x + b • y)
          = I + (a * tx + b * ty) := by
                simp [I, rockafellarChainValue, rockafellarChainValue_convexCombination
                  (q :: l) x y a b hab, tx, ty]
        _ = (a * I + b * I) + (a * tx + b * ty) := by
                calc
                  I + (a * tx + b * ty) = (1 : ℝ) * I + (a * tx + b * ty) := by ring
                  _ = (a + b) * I + (a * tx + b * ty) := by rw [hab]
                  _ = (a * I + b * I) + (a * tx + b * ty) := by ring
        _ = a * (I + tx) + b * (I + ty) := by
                ring
        _ = a * rockafellarChainValue (p :: q :: l) x +
              b * rockafellarChainValue (p :: q :: l) y := by
                simp [I, rockafellarChainValue, mul_add, tx, ty]

/-- If a value `r` at `x` comes from a rooted chain and `(x, y) ∈ Γ`, then appending `(x, y)` to
that chain produces the value `r + ⟪y, z - x⟫` at `z`. This is the dynamic-programming step that
drives the Rockafellar containment theorem. -/
lemma add_inner_mem_rockafellarValueSet
    {base : E × E} {Γ : Set (E × E)} {x y z : E} {r : ℝ}
    (hxy : (x, y) ∈ Γ) (hr : r ∈ rockafellarValueSet base Γ x) :
    r + inner ℝ y (z - x) ∈ rockafellarValueSet base Γ z := by
  rcases hr with ⟨l, hlne, hhead, hforall, rfl⟩
  refine ⟨l ++ [(x, y)], by simp [hlne], ?_, ?_, ?_⟩
  · rw [List.head?_append_of_ne_nil l hlne]
    exact hhead
  · rw [List.forall_iff_forall_mem] at hforall ⊢
    intro q hq
    rw [List.mem_append] at hq
    rcases hq with hq | hq
    · exact hforall q hq
    · simp at hq
      simpa [hq] using hxy
  · simp [rockafellarChainValue_concat_singleton, add_comm]

/-- Every point of `Γ` is a subgradient of the rooted Rockafellar potential.

The point is simple: every rooted chain value at `x` can be extended by appending `(x, y)`, so its
value increases by exactly `⟪y, z - x⟫` when evaluated at `z`. Taking the supremum over all rooted
chains at `x` yields the global subgradient inequality. -/
lemma subgradient_rockafellarPotential_of_mem
    {base : E × E} {Γ : Set (E × E)}
    {h_bdd : ∀ x : E, BddAbove (rockafellarValueSet base Γ x)}
    (hbase : base ∈ Γ) {x y : E} (hxy : (x, y) ∈ Γ) :
    Subgradient (rockafellarPotential base Γ h_bdd) x y := by
  intro z
  have hupper :
      rockafellarPotential base Γ h_bdd x ≤
        rockafellarPotential base Γ h_bdd z - inner ℝ y (z - x) := by
    rw [rockafellarPotential]
    refine csSup_le (rockafellarValueSet_nonempty hbase x) ?_
    intro r hr
    have hmem :
        r + inner ℝ y (z - x) ∈ rockafellarValueSet base Γ z :=
      add_inner_mem_rockafellarValueSet hxy hr
    have hle :
        r + inner ℝ y (z - x) ≤ rockafellarPotential base Γ h_bdd z :=
      le_rockafellarPotential_of_mem_valueSet (h_bdd := h_bdd) hmem
    linarith
  linarith

/-- The rooted Rockafellar potential contains `Γ` in its subgradient graph. This is the
real-valued Rockafellar containment theorem in the present file: once the rooted value sets are
known to be bounded above, the supremum construction produces a genuine real-valued convex
potential whose subgradient graph contains the original set. -/
lemma subset_SubgradientGraph_rockafellarPotential
    {base : E × E} {Γ : Set (E × E)}
    {h_bdd : ∀ x : E, BddAbove (rockafellarValueSet base Γ x)}
    (hbase : base ∈ Γ) :
    Γ ⊆ SubgradientGraph (rockafellarPotential base Γ h_bdd) := by
  intro p hp
  exact subgradient_rockafellarPotential_of_mem (h_bdd := h_bdd) hbase hp

/-- The Rockafellar potential is convex on the whole space.

Each rooted chain contributes an affine function of the endpoint. The potential is the supremum of
these affine functions, and convexity follows by checking the convexity inequality against each
chain separately and then taking the supremum. -/
lemma convexOn_rockafellarPotential
    {base : E × E} {Γ : Set (E × E)}
    {h_bdd : ∀ x : E, BddAbove (rockafellarValueSet base Γ x)}
    (hbase : base ∈ Γ) :
    ConvexOn ℝ Set.univ (rockafellarPotential base Γ h_bdd) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  rw [rockafellarPotential]
  refine csSup_le (rockafellarValueSet_nonempty hbase (a • x + b • y)) ?_
  intro r hr
  rcases hr with ⟨l, hlne, hhead, hforall, rfl⟩
  have hlx :
      rockafellarChainValue l x ≤ rockafellarPotential base Γ h_bdd x :=
    le_rockafellarPotential_of_mem_valueSet (h_bdd := h_bdd)
      ⟨l, hlne, hhead, hforall, rfl⟩
  have hly :
      rockafellarChainValue l y ≤ rockafellarPotential base Γ h_bdd y :=
    le_rockafellarPotential_of_mem_valueSet (h_bdd := h_bdd)
      ⟨l, hlne, hhead, hforall, rfl⟩
  rw [rockafellarChainValue_convexCombination l x y a b hab, smul_eq_mul, smul_eq_mul]
  have hax :
      a * rockafellarChainValue l x ≤ a * rockafellarPotential base Γ h_bdd x :=
    mul_le_mul_of_nonneg_left hlx ha
  have hby :
      b * rockafellarChainValue l y ≤ b * rockafellarPotential base Γ h_bdd y :=
    mul_le_mul_of_nonneg_left hly hb
  linarith

end Rockafellar

end OptimalTransport
