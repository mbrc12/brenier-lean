import OptimalTransport.Subgradient
import OptimalTransport.ProperConvex
import Mathlib.Data.List.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.WithTop

namespace OptimalTransport

open scoped BigOperators

section AlgebraicHelpers

variable {R : Type*} [AddSemigroup R]

/-- Generic prefix-congruence for addition: replacing the final summand under a fixed
three-term additive prefix preserves equality. This is purely algebraic and independent of any
optimal-transport structure. -/
lemma add_prefix3_congr (a b c t u : R) (h : t = u) :
    a + b + c + t = a + b + c + u := by
  simp [h]

end AlgebraicHelpers

section AlgebraicCycleSums

variable {X Y : Type*}

/-- Standalone cyclic finite-sum identity.

This is the algebraic core used in the `rockafellarChainValue_ofFn_rev` induction: for a kernel
`K : Y → X → ℝ` and sequences `xᵢ`, `yᵢ`, one can rewrite the cyclic successor-difference sum as a
difference of two signed sums. No optimal-transport definitions are involved. -/
lemma sum_succ_kernel_sub_eq_sub_sum_neg_diag_sub_sum_neg_shift
    {n : ℕ} (K : Y → X → ℝ) (x : Fin (n + 1) → X) (y : Fin (n + 1) → Y) :
    (∑ i, (K (y (i + 1)) (x i) - K (y (i + 1)) (x (i + 1)))) =
      (∑ i, -K (y i) (x i)) - ∑ i, -K (y (i + 1)) (x i) := by
  calc
    (∑ i, (K (y (i + 1)) (x i) - K (y (i + 1)) (x (i + 1)))) =
        (∑ i, K (y (i + 1)) (x i)) - ∑ i, K (y (i + 1)) (x (i + 1)) := by
          simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = (∑ i, K (y (i + 1)) (x i)) - ∑ i, K (y i) (x i) := by
          congr 1
          simpa [Function.comp] using
            (Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1)))
              (fun i : Fin (n + 1) ↦ K (y i) (x i)))
    _ = (∑ i, -K (y i) (x i)) - ∑ i, -K (y (i + 1)) (x i) := by
          rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
          ring

end AlgebraicCycleSums

/-!
This file implements the Rockafellar construction of a convex potential from a cyclically monotone
set, in both the classical real-valued and the proper extended-real-valued settings.

The key objects are:

* `rockafellarChainValue`: the affine functional attached to one finite chain of pairs;
* `rockafellarValueSet base Γ x`: the set of all chain values at `x`, rooted at `base` and using
  points of `Γ`;
* `rockafellarPotential base Γ h_bdd`: the supremum of those values, assuming they are bounded
  above for every target point `x`;
* `properRockafellarPotential base Γ`: the supremum in `WithTop ℝ`, removing the boundedness
  hypothesis;
* `IsProperConvex`: the resulting potential is proper convex;
* `PairingClosedChainMonotone Γ`: the list-based closed-chain condition derived from pairing
  cyclical monotonicity.

The main results are:

* Singleton chains give initial nonemptiness and finiteness at the root;
* Appending one point to a chain has the expected algebraic effect on the chain value;
* The Rockafellar containment theorem: under the closed-chain nonpositivity hypothesis,
  `Γ ⊆ ProperSubgradientGraph Φ`, where `Φ` is the proper Rockafellar potential;
* The resulting potential is convex on its effective domain.

Cyclical monotonicity is used to justify the finiteness of the rooted value sets; the
proper-extended construction makes the boundedness assumption unnecessary by working in
`WithTop ℝ`.
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

/-- The rooted value set viewed in `WithTop ℝ`.

Every finite chain value is still a real number, but taking the supremum in `WithTop ℝ` removes
the need for a global boundedness hypothesis; `⊤` records precisely the points where the chain
values are unbounded above. -/
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

/-- A membership witness in a list yields a decomposition around that entry. -/
lemma list_mem_split {α : Type*} {a : α} :
    ∀ {l : List α}, a ∈ l → ∃ s t : List α, l = s ++ a :: t
  | [], h => by simp at h
  | b :: l, h => by
      rw [List.mem_cons] at h
      rcases h with h | h
      · subst h
        exact ⟨[], l, rfl⟩
      · rcases list_mem_split h with ⟨s, t, rfl⟩
        exact ⟨b :: s, t, by simp⟩

/-- A duplicate entry in a list yields a decomposition with two occurrences of that entry. -/
lemma list_duplicate_split {α : Type*} {a : α} :
    ∀ {l : List α}, List.Duplicate a l → ∃ s t u : List α, l = s ++ a :: t ++ a :: u
  | _, List.Duplicate.cons_mem h => by
      rcases list_mem_split h with ⟨t, u, rfl⟩
      exact ⟨[], t, u, by simp⟩
  | _, @List.Duplicate.cons_duplicate _ a y l h => by
      rcases list_duplicate_split h with ⟨s, t, u, rfl⟩
      exact ⟨y :: s, t, u, by simp [List.append_assoc]⟩

/-- Concatenating a second chain of the form `q :: l₂` splits the Rockafellar value into the value
of the first part evaluated at `q.1`, plus the value of the second chain at the final endpoint. -/
lemma rockafellarChainValue_append_cons :
    ∀ (l₁ : List (E × E)) (q : E × E) (l₂ : List (E × E)) (z : E),
      rockafellarChainValue (l₁ ++ q :: l₂) z =
        rockafellarChainValue l₁ q.1 + rockafellarChainValue (q :: l₂) z
  | [], q, l₂, z => by
      simp [rockafellarChainValue]
  | [p], q, l₂, z => by
      simp [rockafellarChainValue]
  | p :: r :: l₁, q, l₂, z => by
      have h :=
        congrArg
          (fun t => inner ℝ p.2 (r.1 - p.1) + t)
          (rockafellarChainValue_append_cons (r :: l₁) q l₂ z)
      simpa [rockafellarChainValue, add_assoc] using h

/-- For a chain ending at `p`, changing the endpoint only changes the final affine term. -/
lemma rockafellarChainValue_concat_singleton_endpoint
    (l : List (E × E)) (p : E × E) (z w : E) :
    rockafellarChainValue (l ++ [p]) z =
      rockafellarChainValue (l ++ [p]) w + inner ℝ p.2 (z - w) := by
  rw [rockafellarChainValue_concat_singleton, rockafellarChainValue_concat_singleton]
  have hsub :
      inner ℝ p.2 (z - p.1) = inner ℝ p.2 (w - p.1) + inner ℝ p.2 (z - w) := by
    rw [← inner_add_right]
    congr 1
    abel
  linarith

/-- Reversing a finite cycle turns the pairing cycle-gap functional into the Rockafellar chain
value, up to the obvious final affine correction term. -/
lemma rockafellarChainValue_ofFn_rev
    : ∀ {n : ℕ} (p : Fin (n + 1) → E × E) (z : E),
        rockafellarChainValue (List.ofFn (p ∘ Fin.rev)) z =
          cycleGap (fun x y ↦ - inner ℝ y x) p +
            inner ℝ (p 0).2 (z - (p (Fin.last n)).1)
  | 0, p, z => by
      simp [cycleGap]
  | n + 1, p, z => by
      let q : Fin (n + 1) → E × E := fun i ↦ p (Fin.castSucc i)
      have hp : p = Fin.snoc q (p (Fin.last (n + 1))) := by
        funext i
        obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
        · simp [q]
        · simp [q]
      rw [hp]
      rw [Fin.snoc_comp_rev]
      rw [List.ofFn_cons]
      have htail :
          rockafellarChainValue (q (Fin.last n) :: List.ofFn (fun i : Fin n ↦ q i.succ.rev)) z =
            cycleGap (fun x y ↦ - inner ℝ y x) q +
              inner ℝ (q 0).2 (z - (q (Fin.last n)).1) :=
        by simpa [Function.comp, List.ofFn_cons] using rockafellarChainValue_ofFn_rev q z
      have hstart :
          rockafellarChainValue (p (Fin.last (n + 1)) :: List.ofFn (q ∘ Fin.rev)) z =
            inner ℝ (p (Fin.last (n + 1))).2 ((q (Fin.last n)).1 - (p (Fin.last (n + 1))).1) +
              rockafellarChainValue (List.ofFn (q ∘ Fin.rev)) z := by
        simp [rockafellarChainValue]
      rw [hstart]
      have htail' :
          rockafellarChainValue (List.ofFn (q ∘ Fin.rev)) z =
            cycleGap (fun x y ↦ -inner ℝ y x) q +
              inner ℝ (q 0).2 (z - (q (Fin.last n)).1) := by
        simpa [Function.comp, List.ofFn_cons] using htail
      rw [htail']
      have hcycle :
          cycleGap (fun x y ↦ - inner ℝ y x) (Fin.snoc q (p (Fin.last (n + 1)))) =
            cycleGap (fun x y ↦ - inner ℝ y x) q +
              inner ℝ (p (Fin.last (n + 1))).2 ((q (Fin.last n)).1 - (p (Fin.last (n + 1))).1) +
              inner ℝ (q 0).2 ((p (Fin.last (n + 1))).1 - (q (Fin.last n)).1) := by
        have hsucc :
            ∀ x : Fin n,
              (Fin.snoc q (p (Fin.last (n + 1))) : Fin (n + 2) → E × E)
                (x.castSucc.castSucc + 1) = q x.succ := by
          intro x
          have hidx : x.castSucc.castSucc + 1 = x.succ.castSucc := by
            ext
            simp
          rw [hidx]
          have hsnoc :
              (Fin.snoc (α := fun _ : Fin (n + 2) ↦ E × E) q (p (Fin.last (n + 1))))
                x.succ.castSucc = q x.succ :=
            Fin.snoc_castSucc (α := fun _ : Fin (n + 2) ↦ E × E)
              (x := p (Fin.last (n + 1))) (p := q) (i := x.succ)
          simpa using hsnoc
        have hlast :
            (Fin.snoc q (p (Fin.last (n + 1))) : Fin (n + 2) → E × E) ((Fin.last n).castSucc + 1) =
              p (Fin.last (n + 1)) := by
          simp
        have hzero :
            (Fin.snoc q (p (Fin.last (n + 1))) : Fin (n + 2) → E × E) (Fin.last (n + 1) + 1) =
              q 0 := by
          simp
        have hqsucc : ∀ x : Fin n, q (x.castSucc + 1) = q x.succ := by
          intro x
          have hidx : x.castSucc + 1 = x.succ := by
            ext
            simp
          rw [hidx]
        have hqzero : q (Fin.last n + 1) = q 0 := by
          simp
        rw [cycleGap, cycleGap]
        simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
        simp_rw [hsucc, hqsucc]
        rw [hlast, hzero, hqzero]
        rw [inner_sub_right, inner_sub_right]
        ring
      rw [hcycle]
      have hcorr :
          inner ℝ (q 0).2 (z - (q (Fin.last n)).1) =
            inner ℝ (q 0).2 ((p (Fin.last (n + 1))).1 - (q (Fin.last n)).1) +
              inner ℝ (q 0).2 (z - (p (Fin.last (n + 1))).1) := by
        rw [← inner_add_right]
        congr 1
        abel
      have hsimpTail :
          inner ℝ (q 0).2 (z - (p (Fin.last (n + 1))).1) =
            inner ℝ (((Fin.snoc q (p (Fin.last (n + 1))) : Fin (n + 2) → E × E) 0).2)
              (z - (((Fin.snoc q (p (Fin.last (n + 1))) : Fin (n + 2) → E × E)
                (Fin.last (n + 1))).1)) := by
        simp
      rw [hcorr]
      rw [hsimpTail]
      abel_nf

/-- If the endpoint is the first `x`-coordinate of the reversed cycle, then the correction term in
`rockafellarChainValue_ofFn_rev` vanishes and one recovers exactly the pairing cycle-gap. -/
lemma rockafellarChainValue_ofFn_rev_eq_cycleGap
    {n : ℕ} (p : Fin (n + 1) → E × E) :
    rockafellarChainValue (List.ofFn (p ∘ Fin.rev)) (p (Fin.last n)).1 =
      cycleGap (fun x y ↦ - inner ℝ y x) p := by
  rw [rockafellarChainValue_ofFn_rev]
  simp

/-- Removing the segment between two equal points splits the chain value into the sum of the
shortened outer chain and the inner rooted chain. -/
lemma rockafellarChainValue_duplicate_split
    (s t u : List (E × E)) (a : E × E) (z : E) :
    rockafellarChainValue (s ++ a :: t ++ a :: u) z =
      rockafellarChainValue (s ++ a :: u) z + rockafellarChainValue (a :: t) a.1 := by
  rw [show s ++ a :: t ++ a :: u = s ++ a :: (t ++ a :: u) by simp [List.append_assoc]]
  rw [rockafellarChainValue_append_cons s a (t ++ a :: u) z]
  change rockafellarChainValue s a.1 + rockafellarChainValue ((a :: t) ++ a :: u) z =
    rockafellarChainValue (s ++ a :: u) z + rockafellarChainValue (a :: t) a.1
  rw [rockafellarChainValue_append_cons (a :: t) a u z]
  rw [rockafellarChainValue_append_cons s a u z]
  ring

/-- The closed-chain list-based monotonicity condition used by the Rockafellar construction.

A rooted chain `l` with head `base` and all entries in `Γ` must satisfy
`rockafellarChainValue l base.1 ≤ 0`. This is the list-level consequence of pairing cyclical
monotonicity; it is deliberately phrased on lists rather than `Fin`-indexed cycles, so that the
finiteness and containment arguments in the Rockafellar construction become completely formal
once this property is established for supports of optimal plans. -/
def PairingClosedChainMonotone (Γ : Set (E × E)) : Prop :=
  ∀ ⦃l : List (E × E)⦄ ⦃base : E × E⦄,
    l ≠ [] → l.head? = some base → List.Forall (fun p ↦ p ∈ Γ) l →
      rockafellarChainValue l base.1 ≤ 0

/-- A nodup rooted chain in `Γ` satisfies the closed-chain Rockafellar inequality as soon as `Γ`
is pairing-cyclically monotone in the usual finite-cycle sense. -/
lemma pairingClosedChainMonotone_of_nodup
    {Γ : Set (E × E)}
    (hΓ : CCyclicallyMonotone (fun x y ↦ -inner ℝ x y) Γ)
    {l : List (E × E)} {base : E × E}
    (hlne : l ≠ []) (hhead : l.head? = some base)
    (hforall : List.Forall (fun p ↦ p ∈ Γ) l)
    (hnodup : l.Nodup) :
    rockafellarChainValue l base.1 ≤ 0 := by
  obtain ⟨n, hlen⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (List.length_pos_iff_ne_nil.mpr hlne))
  let p : Fin (n + 1) → E × E := fun i ↦ l.get (Fin.cast hlen.symm i)
  have hp_inj : Function.Injective p := by
    intro i j hij
    exact (Fin.cast_injective hlen.symm) (hnodup.injective_get hij)
  have hp_mem : ∀ i, p i ∈ Γ := by
    rw [List.forall_iff_forall_mem] at hforall
    intro i
    exact hforall _ (List.get_mem _ _)
  have hcycle :
      cycleGap (fun x y ↦ - inner ℝ y x) (p ∘ Fin.rev) ≤ 0 := by
    have h :=
      hΓ n (p ∘ Fin.rev) (hp_inj.comp Fin.rev_injective) fun i ↦ hp_mem (Fin.rev i)
    simpa [cycleGap, real_inner_comm] using sub_nonpos.mpr h
  have hlist : List.ofFn p = l := by
    simpa [p, hlen] using (List.ofFn_get l)
  have hbase_head : base = l.head hlne := by
    apply Option.some.inj
    rw [← hhead, List.head?_eq_some_head hlne]
  have hbase_get : base = l.get ⟨0, by simp [hlen]⟩ := by
    simpa [List.head_eq_getElem_zero hlne] using hbase_head
  have hchain :
      rockafellarChainValue l base.1 =
        cycleGap (fun x y ↦ - inner ℝ y x) (p ∘ Fin.rev) := by
    rw [← hlist, ← rockafellarChainValue_ofFn_rev_eq_cycleGap (p := p ∘ Fin.rev)]
    simp [Function.comp, p, hbase_get]
  rw [hchain]
  exact hcycle

/-- Length-induction helper for `pairingClosedChainMonotone_of_cCyclicallyMonotone_negInner`. -/
private lemma pairingClosedChainMonotone_of_cCyclicallyMonotone_negInner_aux
    {Γ : Set (E × E)}
    (hΓ : CCyclicallyMonotone (fun x y ↦ -inner ℝ x y) Γ) :
    ∀ m : ℕ, ∀ {l : List (E × E)} {base : E × E},
      l.length = m → l ≠ [] → l.head? = some base →
        List.Forall (fun p ↦ p ∈ Γ) l → rockafellarChainValue l base.1 ≤ 0 := by
  let P : ℕ → Prop := fun m =>
    ∀ {l : List (E × E)} {base : E × E},
      l.length = m → l ≠ [] → l.head? = some base →
        List.Forall (fun p ↦ p ∈ Γ) l → rockafellarChainValue l base.1 ≤ 0
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro l base hlen hlne hhead hforall
    by_cases hnodup : l.Nodup
    · exact pairingClosedChainMonotone_of_nodup hΓ hlne hhead hforall hnodup
    · rcases (List.exists_duplicate_iff_not_nodup.mpr hnodup) with ⟨a, ha⟩
      rcases list_duplicate_split ha with ⟨s, t, u, rfl⟩
      have hforall_outer :
          List.Forall (fun p ↦ p ∈ Γ) (s ++ a :: u) := by
        rw [List.forall_iff_forall_mem] at hforall ⊢
        intro p hp
        exact hforall p (by simp [List.mem_append] at hp ⊢; aesop)
      have hforall_inner :
          List.Forall (fun p ↦ p ∈ Γ) (a :: t) := by
        rw [List.forall_iff_forall_mem] at hforall ⊢
        intro p hp
        exact hforall p (by simp [List.mem_append] at hp ⊢; aesop)
      have houter_len : (s ++ a :: u).length < m := by
        rw [← hlen]
        simp
      have hinner_len : (a :: t).length < m := by
        rw [← hlen]
        simp
        omega
      have houter_ne : s ++ a :: u ≠ [] := by simp
      have hinner_ne : a :: t ≠ [] := by simp
      have houter_head : (s ++ a :: u).head? = some base := by
        cases s <;> simpa using hhead
      have hinner_head : (a :: t).head? = some a := by simp
      have houter :
          rockafellarChainValue (s ++ a :: u) base.1 ≤ 0 :=
        ih (s ++ a :: u).length houter_len rfl houter_ne houter_head hforall_outer
      have hinner :
          rockafellarChainValue (a :: t) a.1 ≤ 0 :=
        ih (a :: t).length hinner_len rfl hinner_ne hinner_head hforall_inner
      rw [rockafellarChainValue_duplicate_split]
      linarith

/-- Pairing cyclical monotonicity on finite injective cycles implies the list-based closed-chain
property used by the Rockafellar construction. -/
lemma pairingClosedChainMonotone_of_cCyclicallyMonotone_negInner
    {Γ : Set (E × E)}
    (hΓ : CCyclicallyMonotone (fun x y ↦ -inner ℝ x y) Γ) :
    PairingClosedChainMonotone Γ := by
  intro l base hlne hhead hforall
  exact pairingClosedChainMonotone_of_cCyclicallyMonotone_negInner_aux hΓ l.length rfl hlne hhead
    hforall

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

/-- If the proper Rockafellar potential is finite at `x`, then the real value set at `x` is
bounded above by that finite value. This replaces the global boundedness hypothesis with a local
one. -/
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

/-- If the rooted value sets are bounded above, then the proper Rockafellar potential is finite
everywhere. This connects the `WithTop ℝ` construction back to the classical real-valued one. -/
lemma properRockafellarPotential_lt_top_of_bddAbove
    {base : E × E} {Γ : Set (E × E)}
    {h_bdd : ∀ x : E, BddAbove (rockafellarValueSet base Γ x)}
    (hbase : base ∈ Γ) (x : E) :
    properRockafellarPotential base Γ x < ⊤ := by
  rw [properRockafellarPotential, properRockafellarValueSet]
  rw [← coe_csSup_eq_sSup_image_withTop
    (rockafellarValueSet_nonempty hbase x) (h_bdd x)]
  exact WithTop.coe_lt_top _

/-- In the bounded-above regime, the proper Rockafellar potential equals the classical real-valued
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

/-- The real-valued Rockafellar potential equals the real wrapper of the proper potential when
the rooted value sets are bounded above. -/
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

/-- Under the closed-chain hypothesis, the support set `Γ` is contained in the proper subgradient
graph of the proper Rockafellar potential.

The subgradient inequality itself is the standard append-a-point argument: every rooted chain
value at `x` can be extended by `(x, y)`, giving a larger chain value at `z`. The only additional
input in the extended-real setting is local finiteness at the contact point, which follows from
the pairing closed-chain condition. -/
lemma subset_ProperSubgradientGraph_properRockafellarPotential_of_pairingClosedChainMonotone
    {base : E × E} {Γ : Set (E × E)}
    (hΓ : PairingClosedChainMonotone Γ) (hbase : base ∈ Γ) :
    Γ ⊆ ProperSubgradientGraph (properRockafellarPotential base Γ) := by
  intro p hp
  exact properSubgradient_properRockafellarPotential_of_mem_of_lt_top hbase hp
    (properRockafellarPotential_lt_top_of_pairingClosedChainMonotone hΓ hbase hp)

/-- Every point of `Γ` is a subgradient of the real-valued Rockafellar potential rooted at `base`.

Each rooted chain value at `x` can be extended by appending `(x, y)`, which adds exactly
`⟪y, z - x⟫` when evaluated at `z`. Taking the supremum over all rooted chains yields the global
subgradient inequality. -/
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

/-- The rooted Rockafellar potential contains `Γ` in its subgradient graph. This is the classical
Rockafellar containment theorem: once the rooted value sets are bounded above, the supremum
construction produces a real-valued convex potential whose subgradient graph contains `Γ`. -/
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
