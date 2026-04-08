import OptimalTransport.Subgradient
import OptimalTransport.ProperConvex
import Mathlib.Data.List.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.WithTop

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

/-- The same rooted value set, now viewed in `WithTop ℝ`.

This is the right codomain for the next Rockafellar refactor: every finite chain value is still a
real number, but taking the supremum in `WithTop ℝ` no longer requires a global boundedness
hypothesis. -/
def properRockafellarValueSet (base : E × E) (Γ : Set (E × E)) (x : E) : Set (WithTop ℝ) :=
  ((↑) : ℝ → WithTop ℝ) '' rockafellarValueSet base Γ x

/-- The extended-real Rockafellar potential attached to `base` and `Γ`.

Unlike `rockafellarPotential`, this version is defined with no boundedness hypothesis: the supremum
is taken in `WithTop ℝ`, so `⊤` records precisely the points where the chain values are unbounded
above. -/
noncomputable def properRockafellarPotential (base : E × E) (Γ : Set (E × E)) (x : E) : WithTop ℝ :=
  sSup (properRockafellarValueSet base Γ x)

/-- Predicate selecting the rooted chains used by the Rockafellar construction. -/
def IsRockafellarRootedChain (base : E × E) (Γ : Set (E × E)) (l : List (E × E)) : Prop :=
  l ≠ [] ∧ l.head? = some base ∧ List.Forall (fun p ↦ p ∈ Γ) l

/-- A rooted chain defines an affine `WithTop ℝ`-valued function of the endpoint variable. -/
def properRockafellarChainFun (l : List (E × E)) : E → WithTop ℝ :=
  fun x => ((rockafellarChainValue l x : ℝ) : WithTop ℝ)

/-- The family of affine chain functionals attached to rooted chains in `Γ`. -/
def properRockafellarFamily (base : E × E) (Γ : Set (E × E)) : Set (E → WithTop ℝ) :=
  {f | ∃ l : List (E × E), IsRockafellarRootedChain base Γ l ∧ f = properRockafellarChainFun l}

/-- The Rockafellar chain functional is continuous in the endpoint variable. -/
lemma continuous_rockafellarChainValue : ∀ l : List (E × E), Continuous (rockafellarChainValue l)
  | [] => by
      simpa [rockafellarChainValue] using
        (continuous_const : Continuous fun _x : E => (0 : ℝ))
  | [p] => by
      have hpair : Continuous fun x : E => (p.2, x - p.1) := by
        exact continuous_const.prodMk (continuous_id.sub continuous_const)
      simpa [rockafellarChainValue] using (continuous_inner.comp hpair)
  | p :: q :: l => by
      have hconst : Continuous fun _x : E => inner ℝ p.2 (q.1 - p.1) := continuous_const
      simpa [rockafellarChainValue] using hconst.add (continuous_rockafellarChainValue (q :: l))

/-- Each affine chain functional is continuous as a `WithTop ℝ`-valued function. -/
lemma continuous_properRockafellarChainFun (l : List (E × E)) :
    Continuous (properRockafellarChainFun l) := by
  exact WithTop.continuous_coe.comp (continuous_rockafellarChainValue l)

/-- Evaluating the family of chain functions at a point recovers exactly the rooted value set at
that point. -/
lemma image_apply_properRockafellarFamily (base : E × E) (Γ : Set (E × E)) (x : E) :
    (fun f : E → WithTop ℝ => f x) '' properRockafellarFamily base Γ =
      properRockafellarValueSet base Γ x := by
  ext r
  constructor
  · rintro ⟨f, ⟨l, hl, rfl⟩, rfl⟩
    rcases hl with ⟨hlne, hhead, hforall⟩
    exact ⟨rockafellarChainValue l x, ⟨l, hlne, hhead, hforall, rfl⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    rcases hs with ⟨l, hlne, hhead, hforall, hs⟩
    refine ⟨properRockafellarChainFun l, ?_, ?_⟩
    · exact ⟨l, ⟨hlne, hhead, hforall⟩, rfl⟩
    · simp [properRockafellarChainFun, hs]

/-- The family of affine chain functionals has the proper Rockafellar potential as its least upper
bound in the function order, provided the rooted singleton chain `[base]` is admissible. -/
lemma isLUB_properRockafellarFamily {base : E × E} {Γ : Set (E × E)} (hbase : base ∈ Γ) :
    IsLUB (properRockafellarFamily base Γ) (properRockafellarPotential base Γ) := by
  rw [isLUB_pi]
  intro x
  rw [image_apply_properRockafellarFamily]
  refine isLUB_csSup ?_ ?_
  · refine ⟨(inner ℝ base.2 (x - base.1) : WithTop ℝ), ?_⟩
    refine Set.mem_image_of_mem ((↑) : ℝ → WithTop ℝ) ?_
    refine ⟨[base], by simp, by simp, ?_, by simp [rockafellarChainValue]⟩
    simp [hbase]
  · exact ⟨⊤, fun _ _ => le_top⟩

/-- Any member of the Rockafellar family is continuous. -/
lemma continuous_of_mem_properRockafellarFamily {base : E × E} {Γ : Set (E × E)}
    {f : E → WithTop ℝ} (hf : f ∈ properRockafellarFamily base Γ) :
    Continuous f := by
  rcases hf with ⟨l, _hl, rfl⟩
  exact continuous_properRockafellarChainFun l

/-- The proper Rockafellar potential is lower semicontinuous.

The proof uses the defining characterization of lower semicontinuity by strict superlevel sets.
Since `properRockafellarPotential` is the pointwise supremum of the affine chain functionals,
the set `{x | a < properRockafellarPotential base Γ x}` is exactly the union of the open sets
`{x | a < f x}` over `f` in the Rockafellar family. -/
theorem lowerSemicontinuous_properRockafellarPotential
    {base : E × E} {Γ : Set (E × E)} (hbase : base ∈ Γ) :
    LowerSemicontinuous (properRockafellarPotential base Γ) := by
  have h𝓕_lub : IsLUB (properRockafellarFamily base Γ) (properRockafellarPotential base Γ) :=
    isLUB_properRockafellarFamily hbase
  have hLub_eval :
      ∀ x : E,
        IsLUB ((fun f : E → WithTop ℝ => f x) '' properRockafellarFamily base Γ)
          (properRockafellarPotential base Γ x) := by
    simpa [isLUB_pi] using h𝓕_lub
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro a
  have hEq :
      (properRockafellarPotential base Γ) ⁻¹' Set.Ioi a =
        ⋃ f ∈ properRockafellarFamily base Γ, f ⁻¹' Set.Ioi a := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, haz⟩ := (lt_isLUB_iff (hLub_eval x)).1 hx
      rcases hz with ⟨f, hf, rfl⟩
      exact Set.mem_iUnion.2 ⟨f, Set.mem_iUnion.2 ⟨hf, haz⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨f, hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨hf, hfx⟩
      exact lt_of_lt_of_le hfx ((hLub_eval x).1 (Set.mem_image_of_mem _ hf))
  rw [hEq]
  exact isOpen_biUnion fun f hf =>
    isOpen_Ioi.preimage (continuous_of_mem_properRockafellarFamily hf)

/-- The proper Rockafellar potential is measurable.

This is an immediate consequence of lower semicontinuity in the ordered codomain `WithTop ℝ`. -/
theorem measurable_properRockafellarPotential
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {base : E × E} {Γ : Set (E × E)} (hbase : base ∈ Γ) :
    Measurable (properRockafellarPotential base Γ) := by
  exact (lowerSemicontinuous_properRockafellarPotential hbase).measurable

/-- Membership in the extended-real value set is just membership in the real value set after
coercion. -/
@[simp]
lemma mem_properRockafellarValueSet {base : E × E} {Γ : Set (E × E)} {x : E} {r : WithTop ℝ} :
    r ∈ properRockafellarValueSet base Γ x ↔
      ∃ s : ℝ, s ∈ rockafellarValueSet base Γ x ∧ ((s : ℝ) : WithTop ℝ) = r := by
  constructor
  · intro hr
    rcases hr with ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact Set.mem_image_of_mem ((↑) : ℝ → WithTop ℝ) hs

/-- If the root belongs to `Γ`, then the extended-real value set is nonempty as well. -/
lemma properRockafellarValueSet_nonempty {base : E × E} {Γ : Set (E × E)} (hbase : base ∈ Γ)
    (x : E) :
    (properRockafellarValueSet base Γ x).Nonempty := by
  refine ⟨(inner ℝ base.2 (x - base.1) : WithTop ℝ), ?_⟩
  refine Set.mem_image_of_mem ((↑) : ℝ → WithTop ℝ) ?_
  refine ⟨[base], by simp, by simp, ?_, by simp [rockafellarChainValue]⟩
  simp [hbase]

/-- The extended-real value set is always bounded above by `⊤`. -/
lemma bddAbove_properRockafellarValueSet {base : E × E} {Γ : Set (E × E)} (x : E) :
    BddAbove (properRockafellarValueSet base Γ x) := by
  refine ⟨⊤, ?_⟩
  intro r hr
  exact le_top

/-- Any explicit chain value is bounded above by the extended-real Rockafellar potential. -/
lemma le_properRockafellarPotential_of_mem_valueSet
    {base : E × E} {Γ : Set (E × E)} {x : E} {r : ℝ}
    (hr : r ∈ rockafellarValueSet base Γ x) :
    ((r : ℝ) : WithTop ℝ) ≤ properRockafellarPotential base Γ x := by
  exact le_csSup (bddAbove_properRockafellarValueSet (base := base) (Γ := Γ) x)
    (Set.mem_image_of_mem ((↑) : ℝ → WithTop ℝ) hr)

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

/-- Closed rooted chains in `Γ` have nonpositive Rockafellar value at their root.

This is the exact list-level consequence of pairing cyclical monotonicity needed by the
proper-Rockafellar construction. It is deliberately phrased on lists rather than `Fin`-indexed
cycles: later, once a theorem supplies this property for supports of optimal plans, the finiteness
and containment arguments below become completely formal. -/
def PairingClosedChainMonotone (Γ : Set (E × E)) : Prop :=
  ∀ ⦃l : List (E × E)⦄ ⦃base : E × E⦄,
    l ≠ [] → l.head? = some base → List.Forall (fun p ↦ p ∈ Γ) l →
      rockafellarChainValue l base.1 ≤ 0

/-- Under the closed-chain nonpositivity hypothesis, every rooted value set is bounded above by the
affine functional `x ↦ ⟪y, x - base.1⟫` for each `(x, y) ∈ Γ`. -/
lemma rockafellarValueSet_le_inner_of_pairingClosedChainMonotone
    {base : E × E} {Γ : Set (E × E)}
    (hΓ : PairingClosedChainMonotone Γ)
    {x y : E} (hxy : (x, y) ∈ Γ)
    {r : ℝ} (hr : r ∈ rockafellarValueSet base Γ x) :
    r ≤ inner ℝ y (x - base.1) := by
  rcases hr with ⟨l, hlne, hhead, hforall, rfl⟩
  have hforall_append :
      List.Forall (fun p ↦ p ∈ Γ) (l ++ [(x, y)]) := by
    rw [List.forall_iff_forall_mem] at hforall ⊢
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hforall p hp
    · simp at hp
      simpa [hp] using hxy
  have hclosed :
      rockafellarChainValue (l ++ [(x, y)]) base.1 ≤ 0 :=
    hΓ (l := l ++ [(x, y)]) (base := base) (by simp [hlne])
      (by
        rw [List.head?_append_of_ne_nil l hlne]
        exact hhead)
      hforall_append
  rw [rockafellarChainValue_concat_singleton] at hclosed
  have hrewrite : inner ℝ y (base.1 - x) = - inner ℝ y (x - base.1) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, inner_add_right, inner_add_right, inner_neg_right,
      inner_neg_right]
    ring
  rw [hrewrite] at hclosed
  linarith

/-- Under the closed-chain nonpositivity hypothesis, every rooted value set is bounded above by the
affine functional `x ↦ ⟪y, x - base.1⟫` for each `(x, y) ∈ Γ`. -/
lemma bddAbove_rockafellarValueSet_of_pairingClosedChainMonotone
    {base : E × E} {Γ : Set (E × E)}
    (hΓ : PairingClosedChainMonotone Γ)
    {x y : E} (hxy : (x, y) ∈ Γ) :
    BddAbove (rockafellarValueSet base Γ x) := by
  refine ⟨inner ℝ y (x - base.1), ?_⟩
  intro r hr
  exact rockafellarValueSet_le_inner_of_pairingClosedChainMonotone hΓ hxy hr

/-- Pairing closed-chain nonpositivity makes the proper Rockafellar potential finite at every point
of `Γ`.

The proof is the standard Rockafellar estimate: append the point `(x, y)` to a rooted chain,
close the chain back at the root, and use the closed-chain hypothesis to bound the original chain
value by `⟪y, x - base.1⟫`. -/
lemma properRockafellarPotential_lt_top_of_pairingClosedChainMonotone
    {base : E × E} {Γ : Set (E × E)}
    (hΓ : PairingClosedChainMonotone Γ) (hbase : base ∈ Γ)
    {x y : E} (hxy : (x, y) ∈ Γ) :
    properRockafellarPotential base Γ x < ⊤ := by
  have h_bound :
      ∀ r ∈ rockafellarValueSet base Γ x, r ≤ inner ℝ y (x - base.1) := by
    intro r hr
    exact rockafellarValueSet_le_inner_of_pairingClosedChainMonotone hΓ hxy hr
  have h_bdd : BddAbove (rockafellarValueSet base Γ x) :=
    bddAbove_rockafellarValueSet_of_pairingClosedChainMonotone hΓ hxy
  rw [properRockafellarPotential, properRockafellarValueSet]
  have hupper :
      sSup (((↑) : ℝ → WithTop ℝ) '' rockafellarValueSet base Γ x) ≤
        ((inner ℝ y (x - base.1) : ℝ) : WithTop ℝ) := by
    refine csSup_le ?_ ?_
    · rcases rockafellarValueSet_nonempty hbase x with ⟨r, hr⟩
      exact ⟨(r : WithTop ℝ), Set.mem_image_of_mem ((↑) : ℝ → WithTop ℝ) hr⟩
    · intro u hu
      rcases hu with ⟨r, hr, rfl⟩
      exact WithTop.coe_le_coe.mpr (h_bound r hr)
  exact lt_of_le_of_lt hupper (WithTop.coe_lt_top _)

/-- If the extended-real Rockafellar potential is finite at `x`, then the real value set at `x`
is automatically bounded above by that finite value. This is the local replacement for the old
global `h_bdd` hypothesis. -/
lemma bddAbove_rockafellarValueSet_of_properRockafellarPotential_lt_top
    {base : E × E} {Γ : Set (E × E)} {x : E}
    (hfin : properRockafellarPotential base Γ x < ⊤) :
    BddAbove (rockafellarValueSet base Γ x) := by
  refine ⟨(properRockafellarPotential base Γ x).untop (WithTop.lt_top_iff_ne_top.mp hfin), ?_⟩
  intro r hr
  have hrle : ((r : ℝ) : WithTop ℝ) ≤ properRockafellarPotential base Γ x :=
    le_properRockafellarPotential_of_mem_valueSet hr
  rw [← WithTop.coe_untop _ (WithTop.lt_top_iff_ne_top.mp hfin)] at hrle
  exact WithTop.coe_le_coe.mp hrle

/-- Passing to `WithTop ℝ` commutes with taking the supremum of a nonempty bounded set of real
numbers. This is the bridge between the real `csSup` lemmas and the extended-real Rockafellar
potential. -/
lemma coe_csSup_eq_sSup_image_withTop {s : Set ℝ} (hs : s.Nonempty) (hb : BddAbove s) :
    (((sSup s : ℝ) : ℝ) : WithTop ℝ) = sSup (((↑) : ℝ → WithTop ℝ) '' s) := by
  have himage_bdd : BddAbove (((↑) : ℝ → WithTop ℝ) '' s) := by
    rcases hb with ⟨B, hB⟩
    refine ⟨(B : WithTop ℝ), ?_⟩
    intro u hu
    rcases hu with ⟨r, hr, rfl⟩
    exact WithTop.coe_le_coe.mpr (hB hr)
  have hupper :
      sSup (((↑) : ℝ → WithTop ℝ) '' s) ≤ (((sSup s : ℝ) : ℝ) : WithTop ℝ) := by
    refine csSup_le ?_ ?_
    · rcases hs with ⟨r, hr⟩
      exact ⟨(r : WithTop ℝ), Set.mem_image_of_mem ((↑) : ℝ → WithTop ℝ) hr⟩
    · intro u hu
      rcases hu with ⟨r, hr, rfl⟩
      exact WithTop.coe_le_coe.mpr (le_csSup hb hr)
  have hfin : sSup (((↑) : ℝ → WithTop ℝ) '' s) < ⊤ := by
    exact lt_of_le_of_lt hupper (WithTop.coe_lt_top _)
  have hcoe_le :
      (((sSup s : ℝ) : ℝ) : WithTop ℝ) ≤ sSup (((↑) : ℝ → WithTop ℝ) '' s) := by
    have hcsSup_le :
        sSup s ≤ (sSup (((↑) : ℝ → WithTop ℝ) '' s)).untop
          (WithTop.lt_top_iff_ne_top.mp hfin) := by
      refine csSup_le hs ?_
      intro r hr
      have hrle :
          ((r : ℝ) : WithTop ℝ) ≤ sSup (((↑) : ℝ → WithTop ℝ) '' s) := by
        exact le_csSup himage_bdd (Set.mem_image_of_mem ((↑) : ℝ → WithTop ℝ) hr)
      rw [← WithTop.coe_untop _ (WithTop.lt_top_iff_ne_top.mp hfin)] at hrle
      exact WithTop.coe_le_coe.mp hrle
    have hthis :
        (((sSup s : ℝ) : ℝ) : WithTop ℝ) ≤
          (((sSup (((↑) : ℝ → WithTop ℝ) '' s)).untop
            (WithTop.lt_top_iff_ne_top.mp hfin) : ℝ) : WithTop ℝ) :=
      WithTop.coe_le_coe.mpr hcsSup_le
    simpa [WithTop.coe_untop _ (WithTop.lt_top_iff_ne_top.mp hfin)] using hthis
  exact le_antisymm hcoe_le hupper

/-- Under the old bounded-above hypothesis, the proper Rockafellar potential is finite everywhere.

This is the point where the new `WithTop ℝ` construction reconnects with the old real-valued one:
if the rooted value set at each point is bounded above, then the extended supremum never reaches
`⊤`. -/
lemma properRockafellarPotential_lt_top_of_bddAbove
    {base : E × E} {Γ : Set (E × E)}
    {h_bdd : ∀ x : E, BddAbove (rockafellarValueSet base Γ x)}
    (hbase : base ∈ Γ) (x : E) :
    properRockafellarPotential base Γ x < ⊤ := by
  rw [properRockafellarPotential, properRockafellarValueSet]
  rw [← coe_csSup_eq_sSup_image_withTop
    (rockafellarValueSet_nonempty hbase x) (h_bdd x)]
  exact WithTop.coe_lt_top _

/-- In the bounded-above regime, the proper Rockafellar potential is just the old real-valued
Rockafellar potential viewed inside `WithTop ℝ`. -/
lemma properRockafellarPotential_eq_coe_rockafellarPotential
    {base : E × E} {Γ : Set (E × E)}
    {h_bdd : ∀ x : E, BddAbove (rockafellarValueSet base Γ x)}
    (hbase : base ∈ Γ) (x : E) :
    properRockafellarPotential base Γ x =
      (((rockafellarPotential base Γ h_bdd x : ℝ) : ℝ) : WithTop ℝ) := by
  rw [properRockafellarPotential, properRockafellarValueSet, rockafellarPotential]
  exact (coe_csSup_eq_sSup_image_withTop
    (rockafellarValueSet_nonempty hbase x) (h_bdd x)).symm

/-- Therefore the old real-valued Rockafellar potential is exactly the real wrapper of the new
proper potential, provided the rooted value sets are bounded above. -/
lemma toRealPotential_properRockafellarPotential_eq_rockafellarPotential
    {base : E × E} {Γ : Set (E × E)}
    {h_bdd : ∀ x : E, BddAbove (rockafellarValueSet base Γ x)}
    (hbase : base ∈ Γ) :
    toRealPotential (properRockafellarPotential base Γ)
      (properRockafellarPotential_lt_top_of_bddAbove
        (base := base) (Γ := Γ) (h_bdd := h_bdd) hbase) =
      rockafellarPotential base Γ h_bdd := by
  funext x
  have h_eq :
      properRockafellarPotential base Γ x =
        (((rockafellarPotential base Γ h_bdd x : ℝ) : ℝ) : WithTop ℝ) :=
    properRockafellarPotential_eq_coe_rockafellarPotential
      (base := base) (Γ := Γ) (h_bdd := h_bdd) hbase x
  simp [toRealPotential, h_eq]

/-- The extended-real Rockafellar potential is convex on its effective domain.

This is the `WithTop ℝ` version of the usual statement that a supremum of affine functions is
convex. The proof only uses finiteness at the two endpoints of the convex combination; the
potential may still take the value `⊤` elsewhere. -/
lemma convexOn_properRockafellarPotential
    {base : E × E} {Γ : Set (E × E)} (hbase : base ∈ Γ) :
    ConvexOn ℝ (EffectiveDomain (properRockafellarPotential base Γ))
      (fun x => (properRockafellarPotential base Γ x).untopD 0) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    let Mx : ℝ :=
      (properRockafellarPotential base Γ x).untop (WithTop.lt_top_iff_ne_top.mp hx)
    let My : ℝ :=
      (properRockafellarPotential base Γ y).untop (WithTop.lt_top_iff_ne_top.mp hy)
    have hbound :
        ∀ r ∈ rockafellarValueSet base Γ (a • x + b • y), r ≤ a * Mx + b * My := by
      intro r hr
      rcases hr with ⟨l, hlne, hhead, hforall, rfl⟩
      have hlx :
          rockafellarChainValue l x ≤ Mx := by
        have hle :
            ((rockafellarChainValue l x : ℝ) : WithTop ℝ) ≤ properRockafellarPotential base Γ x :=
          le_properRockafellarPotential_of_mem_valueSet
            ⟨l, hlne, hhead, hforall, rfl⟩
        rw [show properRockafellarPotential base Γ x = ((Mx : ℝ) : WithTop ℝ) by
          exact (WithTop.coe_untop _ (WithTop.lt_top_iff_ne_top.mp hx)).symm] at hle
        exact WithTop.coe_le_coe.mp hle
      have hly :
          rockafellarChainValue l y ≤ My := by
        have hle :
            ((rockafellarChainValue l y : ℝ) : WithTop ℝ) ≤ properRockafellarPotential base Γ y :=
          le_properRockafellarPotential_of_mem_valueSet
            ⟨l, hlne, hhead, hforall, rfl⟩
        rw [show properRockafellarPotential base Γ y = ((My : ℝ) : WithTop ℝ) by
          exact (WithTop.coe_untop _ (WithTop.lt_top_iff_ne_top.mp hy)).symm] at hle
        exact WithTop.coe_le_coe.mp hle
      rw [rockafellarChainValue_convexCombination l x y a b hab]
      nlinarith
    have hcombo_le :
        properRockafellarPotential base Γ (a • x + b • y) ≤
          (((a * Mx + b * My : ℝ) : ℝ) : WithTop ℝ) := by
      refine csSup_le (properRockafellarValueSet_nonempty hbase (a • x + b • y)) ?_
      intro u hu
      rcases hu with ⟨r, hr, rfl⟩
      exact WithTop.coe_le_coe.mpr (hbound r hr)
    have hcombo_fin :
        properRockafellarPotential base Γ (a • x + b • y) < ⊤ :=
      lt_of_le_of_lt hcombo_le (WithTop.coe_lt_top _)
    exact hcombo_fin
  · intro x hx y hy a b ha hb hab
    let Mx : ℝ :=
      (properRockafellarPotential base Γ x).untop (WithTop.lt_top_iff_ne_top.mp hx)
    let My : ℝ :=
      (properRockafellarPotential base Γ y).untop (WithTop.lt_top_iff_ne_top.mp hy)
    have hbound :
        ∀ r ∈ rockafellarValueSet base Γ (a • x + b • y), r ≤ a * Mx + b * My := by
      intro r hr
      rcases hr with ⟨l, hlne, hhead, hforall, rfl⟩
      have hlx :
          rockafellarChainValue l x ≤ Mx := by
        have hle :
            ((rockafellarChainValue l x : ℝ) : WithTop ℝ) ≤ properRockafellarPotential base Γ x :=
          le_properRockafellarPotential_of_mem_valueSet
            ⟨l, hlne, hhead, hforall, rfl⟩
        rw [show properRockafellarPotential base Γ x = ((Mx : ℝ) : WithTop ℝ) by
          exact (WithTop.coe_untop _ (WithTop.lt_top_iff_ne_top.mp hx)).symm] at hle
        exact WithTop.coe_le_coe.mp hle
      have hly :
          rockafellarChainValue l y ≤ My := by
        have hle :
            ((rockafellarChainValue l y : ℝ) : WithTop ℝ) ≤ properRockafellarPotential base Γ y :=
          le_properRockafellarPotential_of_mem_valueSet
            ⟨l, hlne, hhead, hforall, rfl⟩
        rw [show properRockafellarPotential base Γ y = ((My : ℝ) : WithTop ℝ) by
          exact (WithTop.coe_untop _ (WithTop.lt_top_iff_ne_top.mp hy)).symm] at hle
        exact WithTop.coe_le_coe.mp hle
      rw [rockafellarChainValue_convexCombination l x y a b hab]
      nlinarith
    have hcombo_le :
        properRockafellarPotential base Γ (a • x + b • y) ≤
          (((a * Mx + b * My : ℝ) : ℝ) : WithTop ℝ) := by
      refine csSup_le (properRockafellarValueSet_nonempty hbase (a • x + b • y)) ?_
      intro u hu
      rcases hu with ⟨r, hr, rfl⟩
      exact WithTop.coe_le_coe.mpr (hbound r hr)
    have hcombo_fin :
        properRockafellarPotential base Γ (a • x + b • y) < ⊤ :=
      lt_of_le_of_lt hcombo_le (WithTop.coe_lt_top _)
    have hreal :
        (properRockafellarPotential base Γ (a • x + b • y)).untop
            (WithTop.lt_top_iff_ne_top.mp hcombo_fin) ≤
          a * Mx + b * My := by
      rw [← WithTop.coe_untop _ (WithTop.lt_top_iff_ne_top.mp hcombo_fin)] at hcombo_le
      exact WithTop.coe_le_coe.mp hcombo_le
    have hxreal :
        (properRockafellarPotential base Γ x).untopD 0 = Mx := by
      exact (toRealOnEffectiveDomain_eq_untopD
        (Φ := properRockafellarPotential base Γ) ⟨x, hx⟩).symm
    have hyreal :
        (properRockafellarPotential base Γ y).untopD 0 = My := by
      exact (toRealOnEffectiveDomain_eq_untopD
        (Φ := properRockafellarPotential base Γ) ⟨y, hy⟩).symm
    have hcomboreal :
        (properRockafellarPotential base Γ (a • x + b • y)).untop
            (WithTop.lt_top_iff_ne_top.mp hcombo_fin) =
          (properRockafellarPotential base Γ (a • x + b • y)).untopD 0 := by
      exact toRealOnEffectiveDomain_eq_untopD
        (Φ := properRockafellarPotential base Γ) ⟨a • x + b • y, hcombo_fin⟩
    simpa [hxreal, hyreal, hcomboreal, smul_eq_mul] using hreal

/-- Once one knows that the proper Rockafellar potential is finite at some point, it becomes a
proper convex function in the sense introduced in `ProperConvex.lean`. -/
lemma isProperConvex_properRockafellarPotential
    {base : E × E} {Γ : Set (E × E)} {x : E}
    (hbase : base ∈ Γ)
    (hx : x ∈ EffectiveDomain (properRockafellarPotential base Γ)) :
    IsProperConvex (properRockafellarPotential base Γ) := by
  exact ⟨⟨x, hx⟩, convexOn_properRockafellarPotential (base := base) (Γ := Γ) hbase⟩

/-- If the proper Rockafellar potential is finite at `x`, then every `(x, y) ∈ Γ` is a proper
subgradient point of that potential.

The affine lower-support inequality holds for purely formal reasons, exactly as in the real-valued
construction. The only extra input needed in the extended-real setting is the local finiteness
assumption at the contact point `x`. -/
lemma properSubgradient_properRockafellarPotential_of_mem_of_lt_top
    {base : E × E} {Γ : Set (E × E)}
    (hbase : base ∈ Γ) {x y : E} (hxy : (x, y) ∈ Γ)
    (hfin : properRockafellarPotential base Γ x < ⊤) :
    ProperSubgradient (properRockafellarPotential base Γ) x y := by
  constructor
  · exact hfin
  · intro z
    let S : Set ℝ := rockafellarValueSet base Γ x
    let c : ℝ := inner ℝ y (z - x)
    have hS_nonempty : S.Nonempty := rockafellarValueSet_nonempty hbase x
    have hS_bdd : BddAbove S :=
      bddAbove_rockafellarValueSet_of_properRockafellarPotential_lt_top hfin
    have hTc_nonempty : ((fun r : ℝ => r + c) '' S).Nonempty := by
      rcases hS_nonempty with ⟨r, hr⟩
      exact ⟨r + c, ⟨r, hr, rfl⟩⟩
    have hTc_bdd : BddAbove ((fun r : ℝ => r + c) '' S) := by
      rcases hS_bdd with ⟨B, hB⟩
      refine ⟨B + c, ?_⟩
      intro t ht
      rcases ht with ⟨r, hr, rfl⟩
      linarith [hB hr]
    have hsup_translate :
        sSup (((↑) : ℝ → WithTop ℝ) '' ((fun r : ℝ => r + c) '' S)) ≤
          properRockafellarPotential base Γ z := by
      refine csSup_le ?_ ?_
      · rcases hTc_nonempty with ⟨t, ht⟩
        exact ⟨(t : WithTop ℝ), Set.mem_image_of_mem ((↑) : ℝ → WithTop ℝ) ht⟩
      · intro u hu
        rcases hu with ⟨t, ht, rfl⟩
        rcases ht with ⟨r, hr, htrfl⟩
        subst htrfl
        exact le_properRockafellarPotential_of_mem_valueSet (base := base) (Γ := Γ)
          (add_inner_mem_rockafellarValueSet hxy hr)
    have hmap_real :
        sSup ((fun r : ℝ => r + c) '' S) = sSup S + c := by
      simpa using ((OrderIso.addRight c).map_csSup' (s := S) hS_nonempty hS_bdd).symm
    have hmap :
        (((sSup S + c : ℝ) : ℝ) : WithTop ℝ) =
          sSup (((↑) : ℝ → WithTop ℝ) '' ((fun r : ℝ => r + c) '' S)) := by
      calc
        (((sSup S + c : ℝ) : ℝ) : WithTop ℝ)
          = (((sSup ((fun r : ℝ => r + c) '' S) : ℝ) : ℝ) : WithTop ℝ) := by
              congr 1
              exact hmap_real.symm
        _ = sSup (((↑) : ℝ → WithTop ℝ) '' ((fun r : ℝ => r + c) '' S)) := by
              exact coe_csSup_eq_sSup_image_withTop hTc_nonempty hTc_bdd
    have hxeq :
        properRockafellarPotential base Γ x = (((sSup S : ℝ) : ℝ) : WithTop ℝ) := by
      symm
      exact coe_csSup_eq_sSup_image_withTop hS_nonempty hS_bdd
    rw [hxeq]
    rw [← WithTop.coe_add]
    rw [hmap]
    exact hsup_translate

/-- Under the closed-chain nonpositivity hypothesis, the support set `Γ` is contained in the
proper subgradient graph of the proper Rockafellar potential.

This is the proper extended-real Rockafellar containment theorem in the migrated API. The only
nonformal input is the pointwise finiteness result from
`properRockafellarPotential_lt_top_of_pairingClosedChainMonotone`; once that is available, the
subgradient inequality itself is exactly the same append-a-point argument as in the bounded
real-valued construction. -/
lemma subset_ProperSubgradientGraph_properRockafellarPotential_of_pairingClosedChainMonotone
    {base : E × E} {Γ : Set (E × E)}
    (hΓ : PairingClosedChainMonotone Γ) (hbase : base ∈ Γ) :
    Γ ⊆ ProperSubgradientGraph (properRockafellarPotential base Γ) := by
  intro p hp
  exact properSubgradient_properRockafellarPotential_of_mem_of_lt_top hbase hp
    (properRockafellarPotential_lt_top_of_pairingClosedChainMonotone hΓ hbase hp)

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
