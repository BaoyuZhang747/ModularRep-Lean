import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionDominatedBlock

/-!
# The trivial central sector and its literal quotient block

This construction retains the exceptional triple cover and its fixed map to
G3. The specified block's trivial sector determines the common central kernel.
Actual representation descent then determines the nonzero primitive image
and the complete Brauer fibre. The only block-image input is the existing
one-way guarded primitivity statement. A supported reference character is
specified block data; its choice does not supply a block map or a matching.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B2CentralQuotient

open ModularRep FDRepSimpleClassKZero
open TypeBQ3TripleCoverCarrier TypeBCentralKernelBlockSource
open TypeBCentralKernelBrauerBlocks TypeBQ3PrincipalCriterionDominatedBlock
open IrreducibleBrauerCharacterSurjectiveDescent
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport

variable (source : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
variable [Finite X]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

variable {k : Type} [Field k] [CharP k 2] [IsAlgClosed k]

/-- The common sector kernel is embedded in the original carrier. -/
theorem sectorKernel_eq_qker (bX : LiteralPrimitiveBlock k X)
    (sectorOne : centralSector source freeSource bX = 1) :
    (centralSector source freeSource bX).ker.map (Subgroup.center X).subtype =
      (q source freeSource).ker := by
  rw [sectorOne, q_kernel_eq_center source freeSource]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact z.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl, rfl⟩

/-- Every supported representation is trivial on the same full centre. -/
theorem supportedRepresentation_center_le_kernel
    (bX : LiteralPrimitiveBlock k X)
    (sectorOne : centralSector source freeSource bX = 1)
    (V : FDRep k X) (hV : Representation.IsIrreducible V.ρ)
    (support : Representation.asAlgebraHom V.ρ bX.val = 1) :
    Subgroup.center X ≤ V.ρ.ker := by
  letI : Representation.IsIrreducible V.ρ := hV
  letI := centralOrderInvertible source freeSource (k := k)
  have same : centralSector source freeSource bX =
      Representation.centralCharacter V.ρ (Subgroup.center X) le_rfl := by
    apply Representation.primitiveCentralIdempotentSector_eq_centralCharacter
      V.ρ (Subgroup.center X) le_rfl bX.property
    intro v
    apply (Representation.asModuleEquiv V.ρ).injective
    rw [Representation.asModuleEquiv_map_smul, support]
    rfl
  exact SporadicFi24P3Definition44NamedCarrierCentralBlockKernel.le_ker_of_centralCharacter_eq_one
    (Subgroup.center X) le_rfl V.ρ (same.symm.trans sectorOne)

variable {K : Type} [Field K] [CharZero K]
  (rootX : PrimeRegularRootEmbedding 2 k K X)

/-- The lower convention is restricted along the fixed projection. -/
abbrev downRoot : PrimeRegularRootEmbedding 2 k K G3 :=
  TypeBQ3PrincipalBrauerInflation.downRoot
    (q source freeSource) (q_surjective source freeSource) rootX

/-- Literal support supplies the representation needed by checked descent. -/
def kernelTrivial (bX : LiteralPrimitiveBlock k X)
    (sectorOne : centralSector source freeSource bX = 1)
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    KernelTrivialIBrAlong (q source freeSource) rootX := by
  refine ⟨phi.val, ?_⟩
  obtain ⟨V, hV, hchar, hsupp⟩ := phi.property
  refine ⟨V, hV, hchar, ?_⟩
  rw [q_kernel_eq_center source freeSource]
  exact supportedRepresentation_center_le_kernel source freeSource bX sectorOne V hV hsupp

variable [Fintype (LiteralPrimitiveBlock k X)]
  [Fintype (LiteralPrimitiveBlock k G3)]
  (DX : BlockIdempotentDecomposition (fun c : LiteralPrimitiveBlock k X => c.val))
  (bX : LiteralPrimitiveBlock k X)
  (sectorOne : centralSector source freeSource bX = 1)

include DX sectorOne in
/-- This is the central kernel of the same chosen affording representation. -/
theorem centralKernel_eq_center
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val = Subgroup.center X := by
  have hk := supportedRepresentation_center_le_kernel source freeSource bX sectorOne
    (EvenFieldFLZBAWGoodFamily.chosenIBrRepresentation rootX phi.val)
    (Classical.choose_spec phi.val.property).1
    (TypeBQ3PrincipalBrauerInflation.chosenRepresentation_support rootX DX bX phi)
  exact inf_eq_left.mpr hk

include DX sectorOne in
theorem centralKernel_eq_qker
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val =
      (q source freeSource).ker :=
  (centralKernel_eq_center source freeSource rootX DX bX sectorOne phi).trans
    (q_kernel_eq_center source freeSource).symm

/-- The character's own quotient identifies with the fixed matrix G3. -/
def centralQuotientEquiv
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    TypeBQ3PrincipalExtensionCentralQuotient.CentralQuotient rootX bX phi ≃* G3 :=
  (QuotientGroup.quotientMulEquivOfEq
    (centralKernel_eq_qker source freeSource rootX DX bX sectorOne phi)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (q source freeSource) (q_surjective source freeSource))

@[simp] theorem centralQuotientEquiv_mk
    (phi : {phi : IBr rootX // Supported rootX bX phi}) (x : X) :
    centralQuotientEquiv source freeSource rootX DX bX sectorOne phi
      (QuotientGroup.mk' (TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val) x) =
        q source freeSource x := rfl

variable (DB : BlockIdempotentDecomposition (fun c : LiteralPrimitiveBlock k G3 => c.val))
  (reference : {phi : IBr rootX // Supported rootX bX phi})
  (primitive : CentralPrimeToPrimitiveImageSource (k := k)
    (q source freeSource) (q_surjective source freeSource) rootX.prime
    (q_kernel_le_center source freeSource) (q_kernel_primeToTwo source freeSource))

/-- Descend the supplied reference through the checked equivalence. -/
def referenceDown : IBr (downRoot source freeSource rootX) :=
  (TypeBQ3PrincipalBrauerInflation.kernelEquiv
    (q source freeSource) (q_surjective source freeSource)
    (q_kernel_primeToTwo source freeSource) rootX).symm
      (kernelTrivial source freeSource rootX bX sectorOne reference)

theorem referenceDown_pullback :
    PrimeRegularClassFunction.pullback (q source freeSource)
      (referenceDown source freeSource rootX bX sectorOne reference).val = reference.val.val := by
  let E := TypeBQ3PrincipalBrauerInflation.kernelEquiv
    (q source freeSource) (q_surjective source freeSource)
    (q_kernel_primeToTwo source freeSource) rootX
  exact congrArg (fun z : KernelTrivialIBrAlong (q source freeSource) rootX => z.val.val)
    (E.apply_symm_apply (kernelTrivial source freeSource rootX bX sectorOne reference))

include DX DB primitive in
/-- The selected image equality follows from the actual descended character. -/
theorem reference_image :
    algebraMapOf (q source freeSource) bX.val =
      (block (downRoot source freeSource rootX) DB
        (referenceDown source freeSource rootX bX sectorOne reference)).val := by
  have image := actualBrauerBlock_image
    (q source freeSource) (q_surjective source freeSource) rootX.prime
    (q_kernel_le_center source freeSource) (q_kernel_primeToTwo source freeSource)
    primitive rootX (downRoot source freeSource rootX)
    (TypeBQ3PrincipalBrauerInflation.root_compatible
      (q source freeSource) (q_surjective source freeSource) rootX)
    (injective rootX) (injective (downRoot source freeSource rootX)) DX DB
    reference.val (referenceDown source freeSource rootX bX sectorOne reference)
    (referenceDown_pullback source freeSource rootX bX sectorOne reference).symm
  change algebraMapOf (q source freeSource) (block rootX DX reference.val).val = _ at image
  rw [(supported_iff_block rootX DX bX reference.val).mp reference.property] at image
  exact image

/-- The actual primitive image, with its underlying idempotent fixed by q. -/
def downBlock : LiteralPrimitiveBlock k G3 :=
  ⟨algebraMapOf (q source freeSource) bX.val,
    primitive.primitive_image_of_ne_zero _ bX.property (by
      rw [reference_image source freeSource rootX DX bX sectorOne DB reference primitive]
      exact (block (downRoot source freeSource rootX) DB
        (referenceDown source freeSource rootX bX sectorOne reference)).property.ne_zero)⟩

@[simp] theorem downBlock_val :
    (downBlock source freeSource rootX DX bX sectorOne DB reference primitive).val =
      algebraMapOf (q source freeSource) bX.val := rfl

include DX DB sectorOne reference primitive in
theorem inflate_supported_iff (chi : IBr (downRoot source freeSource rootX)) :
    Supported rootX bX
      (TypeBQ3PrincipalBrauerInflation.kernelEquiv
        (q source freeSource) (q_surjective source freeSource)
        (q_kernel_primeToTwo source freeSource) rootX chi).val ↔
      Supported (downRoot source freeSource rootX)
        (downBlock source freeSource rootX DX bX sectorOne DB reference primitive) chi := by
  rw [supported_iff_block rootX DX, supported_iff_block _ DB]
  have image := actualBrauerBlock_image
    (q source freeSource) (q_surjective source freeSource) rootX.prime
    (q_kernel_le_center source freeSource) (q_kernel_primeToTwo source freeSource)
    primitive rootX (downRoot source freeSource rootX)
    (TypeBQ3PrincipalBrauerInflation.root_compatible
      (q source freeSource) (q_surjective source freeSource) rootX)
    (injective rootX) (injective (downRoot source freeSource rootX)) DX DB
    (TypeBQ3PrincipalBrauerInflation.kernelEquiv
      (q source freeSource) (q_surjective source freeSource)
      (q_kernel_primeToTwo source freeSource) rootX chi).val chi rfl
  change algebraMapOf (q source freeSource)
    (block rootX DX (TypeBQ3PrincipalBrauerInflation.kernelEquiv
      (q source freeSource) (q_surjective source freeSource)
      (q_kernel_primeToTwo source freeSource) rootX chi).val).val =
      (block (downRoot source freeSource rootX) DB chi).val at image
  constructor
  · intro h
    apply Subtype.ext
    rw [h] at image
    exact image.symm
  · intro h
    apply blockIndex_eq_of_map_eq_of_ne_zero DX (algebraMapOf (q source freeSource)).toRingHom
    · exact image.trans (congrArg Subtype.val h)
    · change algebraMapOf (q source freeSource)
        (block rootX DX (TypeBQ3PrincipalBrauerInflation.kernelEquiv
          (q source freeSource) (q_surjective source freeSource)
          (q_kernel_primeToTwo source freeSource) rootX chi).val).val ≠ 0
      rw [image]
      exact (block (downRoot source freeSource rootX) DB chi).property.ne_zero

/-- Deflation identifies exactly these two specified supported Brauer fibres. -/
def brauerDeflation :
    {phi : IBr rootX // Supported rootX bX phi} ≃
      {chi : IBr (downRoot source freeSource rootX) //
        Supported (downRoot source freeSource rootX)
          (downBlock source freeSource rootX DX bX sectorOne DB reference primitive) chi} := by
  let E := TypeBQ3PrincipalBrauerInflation.kernelEquiv
    (q source freeSource) (q_surjective source freeSource)
    (q_kernel_primeToTwo source freeSource) rootX
  have supportedKernel {phi : IBr rootX} (hphi : Supported rootX bX phi) :
      ∃ V : FDRep k X, Representation.IsIrreducible V.ρ ∧
        phi.val = Representation.brauerCharacterOfRootEmbedding V.ρ rootX ∧
          (q source freeSource).ker ≤ V.ρ.ker :=
    (kernelTrivial source freeSource rootX bX sectorOne ⟨phi, hphi⟩).property
  let flatten :
      {phi : KernelTrivialIBrAlong (q source freeSource) rootX // Supported rootX bX phi.val} ≃
        {phi : IBr rootX // Supported rootX bX phi} :=
    Equiv.subtypeSubtypeEquivSubtype supportedKernel
  let restricted :
      {chi : IBr (downRoot source freeSource rootX) //
        Supported (downRoot source freeSource rootX)
          (downBlock source freeSource rootX DX bX sectorOne DB reference primitive) chi} ≃
      {phi : KernelTrivialIBrAlong (q source freeSource) rootX // Supported rootX bX phi.val} :=
    E.subtypeEquiv (fun chi =>
      (inflate_supported_iff source freeSource rootX DX bX sectorOne DB reference primitive chi).symm)
  exact flatten.symm.trans restricted.symm

@[simp] theorem brauerDeflation_symm_val
    (chi : {chi : IBr (downRoot source freeSource rootX) //
      Supported (downRoot source freeSource rootX)
        (downBlock source freeSource rootX DX bX sectorOne DB reference primitive) chi}) :
    ((brauerDeflation source freeSource rootX DX bX sectorOne DB reference primitive).symm chi).val.val =
      PrimeRegularClassFunction.pullback (q source freeSource) chi.val.val := rfl

theorem brauerDeflation_pullback
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    PrimeRegularClassFunction.pullback (q source freeSource)
      (brauerDeflation source freeSource rootX DX bX sectorOne DB reference primitive phi).val.val =
        phi.val.val := by
  let E := brauerDeflation source freeSource rootX DX bX sectorOne DB reference primitive
  exact congrArg (fun z => z.val.val) (E.symm_apply_apply phi)

/-- The original chosen representation on its own central quotient has the same values. -/
theorem quotientBrauer_eq_pullback_deflation
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    (TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer rootX bX phi).val =
      PrimeRegularClassFunction.pullback
        (centralQuotientEquiv source freeSource rootX DX bX sectorOne phi).toMonoidHom
        (brauerDeflation source freeSource rootX DX bX sectorOne DB reference primitive phi).val.val := by
  let pi := QuotientGroup.mk' (TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val)
  have hprime : (Nat.card pi.ker).Coprime 2 := by
    rw [QuotientGroup.ker_mk', centralKernel_eq_qker source freeSource rootX DX bX sectorOne phi]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr
      (q_kernel_primeToTwo source freeSource)).symm
  apply primeRegularClassFunction_pullback_injective_of_ker_card_coprime
    pi (QuotientGroup.mk'_surjective _) hprime
  calc
    (PrimeRegularClassFunction.pullback pi
      (TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer rootX bX phi).val :
        PrimeRegularClassFunction K X 2) = phi.val.val :=
      TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer_inflation rootX bX phi
    _ = _ := by
      have inflated := brauerDeflation_pullback
        source freeSource rootX DX bX sectorOne DB reference primitive phi
      apply PrimeRegularClassFunction.ext
      intro x
      have values := congrArg (fun eta : PrimeRegularClassFunction K X 2 => eta x) inflated
      exact values.symm

end ModularRep.PaperProofs.TypeBQ3B2CentralQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
