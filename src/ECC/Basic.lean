import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.UniqueProds
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.FiniteAbelian

def ECPoints {k : Type} [Field k] [Fintype k] (E : EllipticCurve k) : Type := E.toAffine.Point

noncomputable instance ECPointsCommGroup {k : Type} [Field k] [Fintype k] (E : EllipticCurve k) : AddCommGroup (ECPoints E) :=
WeierstrassCurve.Affine.Point.instAddCommGroupPoint

noncomputable instance ECPointsGroup {k : Type} [Field k] [Fintype k] (E : EllipticCurve k) : Group (ECPoints E) :=
  {
    one := AddCommGroup.toAddGroup.zero,
    mul := AddCommGroup.toAddGroup.add,
    inv := AddCommGroup.toAddGroup.neg,
    one_mul := AddCommGroup.toAddGroup.zero_add,
    mul_assoc := AddCommGroup.toAddGroup.add_assoc,
    mul_one := AddCommGroup.toAddGroup.add_zero,
    mul_left_inv := AddCommGroup.toAddGroup.add_left_neg,
  }

def IsProductOfTwoCyclicGroups (G : Type*) [Group G] : Prop :=
  ∃ (H K : Subgroup G), IsCyclic H ∧ IsCyclic K ∧ Nontrivial H ∧ Nontrivial K ∧ Nonempty (G ≃* H.prod K)

--- This would be easy to do by contradiction as the most amount of points on an elliptic curve is |k|²
theorem point_group_is_finite_with_finite_field {k : Type} [Field k] [Fintype k] (E : EllipticCurve k) [Group (ECPoints E)] :
  Finite (ECPoints E) := by
  have h1 : ∃ f : ECPoints E ↪ Fin (Fintype.card k) × Fin (Fintype.card k), true := sorry
  choose f hf using h1
  haveI : Fintype (ECPoints E) := Fintype.ofInjective f (by apply f.injective)
  exact Finite.of_fintype (ECPoints E)


theorem point_group_is_cyclic_or_product_of_cyclic {k : Type} [Field k] [Fintype k] (E : EllipticCurve k) [Group (ECPoints E)] :
  IsCyclic (ECPoints E) ∨ IsProductOfTwoCyclicGroups (ECPoints E) := by
  have h1: AddCommGroup (ECPoints E) := ECPointsCommGroup (E)
  have h2 : Finite (ECPoints E) := point_group_is_finite_with_finite_field E
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (ECPoints E)
  have h3 : n ≤ 2 := sorry
  sorry




-- We also need that ∀ E.Δ ≠ 0 so we know it is not singular

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/GroupTheory/FiniteAbelian.lean this is useful
-- ^^^ yes, this has the proof of: `AddCommGroup.equiv_directSum_zmod_of_finite` : Any finite abelian group is a direct sum of some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i`.`
