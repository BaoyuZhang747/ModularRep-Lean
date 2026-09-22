import ModularRep.PaperProofs.EvenFieldSourceShaped
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# The selected Levi subgroup and torus in Lemma 3.6

The rational-Levi witness is connected here to the selected subgroup.  If
`M = g L g⁻¹`, `sigma` stabilises `L`, and
`tau = Int(g sigma(g)⁻¹) sigma`, then Lean proves that `tau` stabilises `M`.
Naturality of the characteristic-torus construction then gives fixation of
the selected torus.  Neither selected fixedness statement is an input.
-/

namespace ModularRep.PaperProofs.EvenFieldLeviTorus

open ModularRep.PaperProofs.EvenFieldSourceShaped

universe u

variable {G : Type u} [Group G]

/-- The inner-twisted automorphism used in the manuscript. -/
def innerTwistedAut (sigma : MulAut G) (g : G) : MulAut G :=
  MulAut.conj (innerTwistElement sigma.toMonoidHom g) * sigma

/-- The calculation expressing that the inner-twisted action on a conjugate
of `x` is the conjugate of the original field action on `x`. -/
theorem innerTwistedAut_conjugate
    (sigma : MulAut G) (g x : G) :
    innerTwistedAut sigma g (g * x * g⁻¹) =
      g * sigma x * g⁻¹ := by
  simp [innerTwistedAut, innerTwistElement, MulAut.mul_apply, mul_assoc]

/-- The conjugate subgroup `g L g⁻¹`. -/
def conjugateSubgroup (L : Subgroup G) (g : G) : Subgroup G :=
  L.map (MulAut.conj g).toMonoidHom

/-- The inner-twisted automorphism stabilises the selected rational Levi
subgroup. -/
theorem innerTwistedAut_stabilises_conjugateSubgroup
    (sigma : MulAut G) (g : G) (L : Subgroup G)
    (L_stable : L.map sigma.toMonoidHom = L) :
    (conjugateSubgroup L g).map
        (innerTwistedAut sigma g).toMonoidHom =
      conjugateSubgroup L g := by
  rw [conjugateSubgroup, Subgroup.map_map]
  have hcomp :
      (innerTwistedAut sigma g).toMonoidHom.comp
          (MulAut.conj g).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp sigma.toMonoidHom := by
    ext x
    exact innerTwistedAut_conjugate sigma g x
  rw [hcomp, ← Subgroup.map_map, L_stable]

/-- A characteristic-torus construction is natural under automorphisms. -/
def CharacteristicTorusNatural
    (centralSylow : Subgroup G → Subgroup G) : Prop :=
  ∀ (alpha : MulAut G) (M : Subgroup G),
    (centralSylow M).map alpha.toMonoidHom =
      centralSylow (M.map alpha.toMonoidHom)

/-- The selected torus is fixed as a subgroup, derived from the preceding
Levi equality and naturality. -/
theorem characteristicTorus_stable
    (sigma : MulAut G) (g : G) (L : Subgroup G)
    (L_stable : L.map sigma.toMonoidHom = L)
    (centralSylow : Subgroup G → Subgroup G)
    (natural : CharacteristicTorusNatural centralSylow) :
    (centralSylow (conjugateSubgroup L g)).map
        (innerTwistedAut sigma g).toMonoidHom =
      centralSylow (conjugateSubgroup L g) := by
  rw [natural]
  rw [innerTwistedAut_stabilises_conjugateSubgroup sigma g L L_stable]

end ModularRep.PaperProofs.EvenFieldLeviTorus


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
