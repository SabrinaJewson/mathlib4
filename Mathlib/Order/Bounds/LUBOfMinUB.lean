/-
Copyright (c) 2026 Sabrina Jewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sabrina Jewson
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Defs

import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Minimal upper bounds are least upper bounds

This file provides a `Prop`-valued mixin for orders in which all minimal upper bounds of nonempty
sets are also least upper bounds, and respectively for lower bounds. Notably, this property is
satisfied by `ConditionallyCompleteLattice`s and `LinearOrder`s.

A counterexample is the partial ordering on the set `ℝ ⊕ Bool` that makes the booleans greater than
the reals, but not related to each other. In this case, `true` and `false` are both minimal upper
bounds of `ℝ`, but neither is a least upper bound.
-/

@[expose] public section

variable {α : Type*}

/-- Every minimal upper bound is a least upper bound. -/
class LUBOfMinUB (α) [LE α] : Prop where
  lub_of_min_ub {s : Set α} (hs : s.Nonempty) {ub : α} (hub : Minimal (· ∈ upperBounds s) ub) :
    ub ∈ lowerBounds (upperBounds s)

/-- Every maximal lower bound is a greatest lower bound. -/
@[to_dual existing LUBOfMinUB]
class GLBOfMaxLB (α) [LE α] : Prop where
  glb_of_max_lb {s : Set α} (hs : s.Nonempty) {lb : α} (hlb : Maximal (· ∈ lowerBounds s) lb) :
    lb ∈ upperBounds (lowerBounds s)

/-- Every conditionally complete lattice has all minimal upper bounds be least upper bounds. -/
@[to_dual
/-- Every conditionally complete lattice has all maximal lower bounds be greatest lower bounds. -/
]
instance ConditionallyCompleteLattice.instLUBOfMinUB [ConditionallyCompleteLattice α] :
    LUBOfMinUB α where
  lub_of_min_ub := fun {_s} hs ub ⟨hub, h⟩ _w hw ↦
    (h (fun _x hx ↦ le_csSup ⟨ub, hub⟩ hx) (csSup_le hs hub)).trans (csSup_le hs hw)

/-- Every linear order has all minimal upper bounds be least upper bounds. -/
@[to_dual instGLBOfMaxLB
/-- Every linear order has all maximal lower bounds be greatest lower bounds. -/
]
instance LinearOrder.instLUBOfMinUB [LinearOrder α] : LUBOfMinUB α where
  lub_of_min_ub := fun _ _ ⟨_, h⟩ _w hw ↦ not_lt.mp fun w_lt ↦ (h hw w_lt.le).not_gt w_lt

@[to_dual IsGLB.of_maximal_lb]
theorem IsLUB.of_minimal_ub [LE α] [LUBOfMinUB α] {s : Set α} (hs : s.Nonempty) {x : α}
    (ub : ∀ a ∈ s, a ≤ x) (min_ub : ∀ ub ∈ upperBounds s, ub ≤ x → x ≤ ub) : IsLUB s x :=
  ⟨ub, LUBOfMinUB.lub_of_min_ub hs ⟨ub, min_ub⟩⟩

section PartialOrder
variable [PartialOrder α] [LUBOfMinUB α]

@[to_dual IsGLB.of_gt_notMem_lowerBounds]
theorem IsLUB.of_lt_notMem_upperBounds {s : Set α} (hs : s.Nonempty) {x : α}
    (ub : ∀ a ∈ s, a ≤ x) (min_ub : ∀ w < x, w ∉ upperBounds s) : IsLUB s x :=
  .of_minimal_ub hs ub fun _ub hub le ↦
    le.lt_or_eq.elim (fun h ↦ (min_ub _ h hub).elim) (fun | rfl => le_rfl)

end PartialOrder
