/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Sabrina Jewson
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Order.OrdContinuous

/-!
# Distributivity of group operations over supremum/infimum
-/

public section

open Set

variable {G : Type*}

section OrdContinuousRight
variable [Preorder G] [Group G] [MulRightMono G]

@[to_additive (attr := to_dual)]
lemma LeftOrdContinuous.mul_right (a : G) : LeftOrdContinuous (· * a) :=
  (OrderIso.mulRight a).leftOrdContinuous

@[to_additive]
lemma IsLUB.mul_right {a b : G} {s : Set G} (hs : IsLUB s b) :
    IsLUB ((· * a) '' s) (b * a) :=
  (OrderIso.mulRight a).to_galoisConnection.isLUB_l_image hs

@[to_dual existing, to_additive]
lemma IsGLB.mul_right {a b : G} {s : Set G} (hs : IsGLB s b) :
    IsGLB ((· * a) '' s) (b * a) :=
  (OrderIso.mulRight a).symm.to_galoisConnection.isGLB_u_image hs

end OrdContinuousRight

section OrdContinuousLeftGroup
variable [Preorder G] [Group G] [MulLeftMono G]

@[to_additive]
lemma IsLUB.mul_left {a b : G} {s : Set G} (hs : IsLUB s b) :
    IsLUB ((a * ·) '' s) (a * b) :=
  (OrderIso.mulLeft a).to_galoisConnection.isLUB_l_image hs

@[to_dual existing, to_additive]
lemma IsGLB.mul_left {a b : G} {s : Set G} (hs : IsGLB s b) :
    IsGLB ((a * ·) '' s) (a * b) :=
  (OrderIso.mulLeft a).symm.to_galoisConnection.isGLB_u_image hs

end OrdContinuousLeftGroup

/- The additive versions of the left-multiplication lemmas work with types like `ℝ≥0`, `Ordinal`,
and `ℕ`. Since `ExistsMulOfLE` concerns left division and not right division, the right-
multiplication lemmas cannot be generalized similarly (indeed
`LeftOrdContinuous (· + a)` is false for ordinals). -/
section OrdContinuousLeft
variable [Preorder G] [Semigroup G] [ExistsMulOfLE G] [MulLeftMono G] [MulLeftReflectLE G]

@[to_additive]
lemma LeftOrdContinuous.mul_left (a : G) : LeftOrdContinuous (a * ·) :=
  .of_forall_exists fun c ⟨b, hb⟩ ↦
    have ⟨d, hd⟩ := exists_mul_of_le hb
    ⟨b * d, fun x ↦ by rw [hd, mul_assoc, mul_le_mul_iff_left a]⟩

@[to_additive]
lemma RightOrdContinuous.mul_left [GLBOfMaxLB G] (a : G) : RightOrdContinuous (a * ·) :=
  .of_forall_bounded_exists fun c _ ⟨b, hb⟩ ↦
    have ⟨d, hd⟩ := exists_mul_of_le hb
    ⟨b * d, fun x ↦ by rw [hd, mul_assoc, mul_le_mul_iff_left a]⟩

end OrdContinuousLeft

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice G] {ι : Type*} [Nonempty ι] {f : ι → G} {s : Set G}

section Right
variable [Group G] [MulRightMono G]

@[to_additive (attr := to_dual)]
lemma csSup_mul (ne : s.Nonempty) (bdd : BddAbove s) (a : G) : sSup s * a = sSup ((· * a) '' s) :=
  (LeftOrdContinuous.mul_right a).map_csSup ne bdd

@[to_additive (attr := to_dual)]
lemma csSup_div (ne : s.Nonempty) (bdd : BddAbove s) (a : G) :
    sSup s / a = sSup ((· / a) '' s) := by
  simp only [div_eq_mul_inv, csSup_mul ne bdd]

@[to_additive (attr := to_dual)]
lemma ciSup_mul (hf : BddAbove (range f)) (a : G) : (⨆ i, f i) * a = ⨆ i, f i * a :=
  (LeftOrdContinuous.mul_right a).map_ciSup hf

@[to_additive (attr := to_dual)]
lemma ciSup_div (hf : BddAbove (range f)) (a : G) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, ciSup_mul hf]

end Right

section Left
variable [Semigroup G] [ExistsMulOfLE G] [MulLeftMono G] [MulLeftReflectLE G]

@[to_additive]
lemma mul_csSup (ne : s.Nonempty) (bdd : BddAbove s) (a : G) : a * sSup s = sSup ((a * ·) '' s) :=
  (LeftOrdContinuous.mul_left a).map_csSup ne bdd

@[to_additive]
lemma mul_ciSup (hf : BddAbove (range f)) (a : G) : a * ⨆ i, f i = ⨆ i, a * f i :=
  (LeftOrdContinuous.mul_left a).map_ciSup hf

@[to_additive (attr := to_dual existing)]
lemma mul_csInf (ne : s.Nonempty) (bdd : BddBelow s) (a : G) : a * sInf s = sInf ((a * ·) '' s) :=
  (RightOrdContinuous.mul_left a).map_csInf ne bdd

@[to_additive (attr := to_dual existing)]
lemma mul_ciInf (hf : BddBelow (range f)) (a : G) : a * ⨅ i, f i = ⨅ i, a * f i :=
  (RightOrdContinuous.mul_left a).map_ciInf hf

end Left

end ConditionallyCompleteLattice
