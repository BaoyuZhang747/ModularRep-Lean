import ModularRep.PaperProofs.TypeBQ3PrincipalExtensionCentralQuotient

/-! The common central sector of the actual principal block is trivial.
Its kernel is the kernel of the fixed projection to G3. This identifies the
central quotient in the manuscript's fixed-block definition, independently
of any block-goodness or character-weight conclusion. -/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalCriterionDominatedBlock

open ModularRep
open TypeBQ3TripleCoverCarrier TypeBCentralKernelBlockSource
open SporadicFi24P3Definition44NamedCarrierCentralBlockKernel

variable (source : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
variable [Finite X]
variable {k : Type} [Field k] [CharP k 2] [IsAlgClosed k]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

@[instance_reducible] def centralOrderInvertible :
    Invertible (Fintype.card (Subgroup.center X) : k) :=
  invertibleOfNonzero (by
    intro hzero
    have hdiv : 2 ∣ Nat.card (Subgroup.center X) := by
      simpa only [Nat.card_eq_fintype_card] using
        (CharP.cast_eq_zero_iff k 2 (Fintype.card (Subgroup.center X))).mp hzero
    rw [← q_kernel_eq_center source freeSource] at hdiv
    exact q_kernel_primeToTwo source freeSource hdiv)

def centralSector (bX : LiteralPrimitiveBlock k X) : Subgroup.center X →* kˣ := by
  letI := centralOrderInvertible source freeSource (k := k)
  exact bX.property.centralCharacterSector (Subgroup.center X) le_rfl

theorem principal_centralSector_eq_one
    (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX) :
    centralSector source freeSource bX = 1 := by
  letI := centralOrderInvertible source freeSource (k := k)
  letI : Representation.IsIrreducible (1 : Representation k X k) :=
    TypeBRankThreePrincipalReferenceBinding.trivialRepresentation_irreducible
  have support : ∀ v : (1 : Representation k X k).asModule, bX.val • v = v := by
    intro v
    apply (1 : Representation k X k).asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, hbX]
    rfl
  exact (Representation.primitiveCentralIdempotentSector_eq_centralCharacter
    (1 : Representation k X k) (Subgroup.center X) le_rfl bX.property support).trans
      (centralCharacter_eq_one_of_le_ker (Subgroup.center X) le_rfl
        (1 : Representation k X k) (by intro x hx; rfl))

theorem principal_isTrivialSector
    (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX) :
    letI := centralOrderInvertible source freeSource (k := k)
    IsCentralCharacterSector (Subgroup.center X) bX.val 1 := by
  letI := centralOrderInvertible source freeSource (k := k)
  have sector := bX.property.centralCharacterSector_isSector (Subgroup.center X) le_rfl
  change IsCentralCharacterSector (Subgroup.center X) bX.val
    (centralSector source freeSource bX) at sector
  rw [principal_centralSector_eq_one source freeSource bX hbX] at sector
  exact sector

/-- The kernel of the common sector, embedded in X, is exactly the old q kernel. -/
theorem principal_sectorKernel_eq_qker
    (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX) :
    (centralSector source freeSource bX).ker.map (Subgroup.center X).subtype =
      (q source freeSource).ker := by
  rw [principal_centralSector_eq_one source freeSource bX hbX,
    q_kernel_eq_center source freeSource]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact z.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl, rfl⟩

include source freeSource in
/-- Every representation of this block has the same trivial central character. -/
theorem supported_centralCharacter_eq_one
    (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX)
    (V : FDRep k X) (hV : Representation.IsIrreducible V.ρ)
    (hsupport : Representation.asAlgebraHom V.ρ bX.val = 1) :
    letI : Representation.IsIrreducible V.ρ := hV
    Representation.centralCharacter V.ρ (Subgroup.center X) le_rfl = 1 := by
  letI : Representation.IsIrreducible V.ρ := hV
  apply centralCharacter_eq_one_of_le_ker
  rw [← q_kernel_eq_center source freeSource]
  exact TypeBQ3PrincipalBrauerInflation.principalRepresentation_kernel
    (q source freeSource) (q_kernel_le_center source freeSource)
    (q_kernel_primeToTwo source freeSource) bX hbX V hV hsupport

end ModularRep.PaperProofs.TypeBQ3PrincipalCriterionDominatedBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
