import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian

namespace EllipticCurve


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

end EllipticCurve

theorem point_group_is_cyclic {k : Type} [Field k] [Fintype k] (E : EllipticCurve k) [Group (ECPoints)]: IsCyclic (ECPoints) := by
  sorry

-- We also need that ∀ E.Δ ≠ 0 so we know it is not singular
