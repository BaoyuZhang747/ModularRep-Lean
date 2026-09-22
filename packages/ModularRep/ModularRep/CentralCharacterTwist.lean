import ModularRep.CentralAction
import ModularRep.Twist

/-!
# Automorphism transport of central characters

For the convention `rho.twist alpha = rho.comp alpha`, the central character of the twisted
representation is the pullback of the original central character along the automorphism induced
by `alpha` on the centre.
-/

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The automorphism of the centre induced by a group automorphism. -/
def centerAutomorphism (alpha : MulAut G) : MulAut (Subgroup.center G) :=
  Subgroup.centerCongr alpha

@[simp]
theorem centerAutomorphism_coe (alpha : MulAut G) (z : Subgroup.center G) :
    ((centerAutomorphism alpha z : Subgroup.center G) : G) = alpha (z : G) :=
  rfl

variable [FiniteDimensional k V] [IsAlgClosed k]

section

variable (rho : Representation k G V) [rho.IsIrreducible] (alpha : MulAut G)

local instance twistIsIrreducible : (rho.twist alpha).IsIrreducible :=
  IsIrreducible.twist (rho := rho) inferInstance alpha

/-- Twisting by `alpha` pulls the central character back along the induced automorphism of the
centre. -/
theorem centralCharacter_twist :
    centralCharacter (rho.twist alpha) (Subgroup.center G) le_rfl =
      (centralCharacter rho (Subgroup.center G) le_rfl).comp
        (centerAutomorphism alpha).toMonoidHom := by
  apply (existsUnique_centralCharacter (rho.twist alpha) (Subgroup.center G) le_rfl).unique
  · exact centralCharacter_spec (rho.twist alpha) (Subgroup.center G) le_rfl
  · intro z
    change rho (alpha (z : G)) =
      (centralCharacter rho (Subgroup.center G) le_rfl (centerAutomorphism alpha z) : k) •
        LinearMap.id
    simpa only [centerAutomorphism_coe] using
      centralCharacter_spec rho (Subgroup.center G) le_rfl (centerAutomorphism alpha z)

@[simp]
theorem centralCharacter_twist_apply (z : Subgroup.center G) :
    centralCharacter (rho.twist alpha) (Subgroup.center G) le_rfl z =
      centralCharacter rho (Subgroup.center G) le_rfl (centerAutomorphism alpha z) := by
  exact DFunLike.congr_fun (centralCharacter_twist rho alpha) z

end

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
