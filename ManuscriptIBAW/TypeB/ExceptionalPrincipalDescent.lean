import ManuscriptIBAW.TypeB.ExceptionalApplication
import ModularRep.CurrentSpathFiniteSplittingDescent
import ModularRep.PaperProofs.TypeBCurrentPrincipalBijection

/-!
# The principal block of Omega7(3) from the exceptional covering family

The record proving Proposition 4.11 also supplies the family used here.
Its full family witness is constructed by `Inputs.familyComplete`. The
principal block bijection is transported through the stated central
quotient correspondences. The general descent source applies to the actual
pairs of that family, with explicit coefficient requirements for their
extension groups. No second copy of the nine-block inputs and no separate
assumption of a principal block witness is used.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.Exceptional

open ModularRep ModularRep.PaperProofs
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldFLZBAWGoodFamily TypeBFullBlockCondition
open TypeBQ3TripleCoverCarrier TypeBCurrentPrincipalBijection

/-- The full family is obtained from the same record as Proposition 4.11. -/
def Inputs.provedFamily (D : Inputs G3) : FamilyWitness D.family D.cover :=
  Classical.choice D.familyComplete

/-- Use the cover appearing in the stated central quotient comparison. -/
def Inputs.familyOnCover (D : Inputs G3)
    {family : Definition35Family 2}
    (matchCover : EllPrimeCoverCentralExtensionFamilyMatch D.family family)
    (cover_eq : matchCover.cover = D.cover) :
    FamilyWitness D.family matchCover.cover := by
  rw [cover_eq]
  exact D.provedFamily

/-- Structural and coefficient identifications for the principal quotient
application. The exceptional family itself is proved from `prop411`. -/
structure PrincipalSources (family : Definition35Family 2) (block : family.Block) where
  prop411 : Inputs G3
  presentation : Q3PrincipalPresentation family block
  matchCover : EllPrimeCoverCentralExtensionFamilyMatch prop411.family family
  cover_eq : matchCover.cover = prop411.cover
  centerless : Subgroup.center family.H = ⊥
  upPhysical : CurrentSpathDescent.PhysicalFamilySource prop411.family
  downPhysical : CurrentSpathDescent.PhysicalFamilySource family
  downField : SpathCoefficientField 2 family.k family.ellPrime
  upBlock : prop411.family.Block
  transport : CurrentSpathFiniteSplittingDescent.BlockTransport
    prop411.family family matchCover upBlock block
  adequate : CurrentSpathFiniteSplittingDescent.CoefficientAdequacy family
    (prop411.familyOnCover matchCover cover_eq)
  descent : CurrentSpathFiniteSplittingDescent.Source.{0}

/-- The map and its equivariance are transported from the established
covering family. The general descent source supplies its pair conditions. -/
theorem PrincipalSources.coherent {family : Definition35Family 2} {block : family.Block}
    (D : PrincipalSources family block) :
    Nonempty (TypeBCurrentPrincipalBijection.CoherentBlockWitness (family.problem block)) := by
  let : Finite X := finite_X D.prop411.matrixSource
  obtain ⟨good⟩ := CurrentSpathFiniteSplittingDescent.current_corollary_2_5_block
    D.descent D.centerless D.upPhysical D.downPhysical
    D.prop411.raw.before.fieldSource D.downField D.transport
    (D.prop411.familyOnCover D.matchCover D.cover_eq) D.adequate
  exact ⟨{ omega := good.omega
           equivariant := good.equivariant
           matched := fun psi => ⟨good.matched psi⟩ }⟩

end ManuscriptIBAW.TypeB.Exceptional

/-
This file belongs to the Lean formalisation accompanying Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under explicit external assumptions.
-/
