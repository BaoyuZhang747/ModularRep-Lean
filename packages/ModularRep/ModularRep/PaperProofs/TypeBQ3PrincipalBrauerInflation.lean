import ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSurjectiveRoot
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralBlockKernel
import ModularRep.PaperProofs.CentralEllPrimeIBrFibreEquivariance
import ModularRep.PaperProofs.TypeBRankThreePrincipalReferenceBinding

/-!
# Literal principal Brauer inflation for the exceptional triple cover

The map is the actual finite central prime-to-two surjection supplied by
`TypeBQ3TripleCoverCarrier`. Its target root is the restriction of the given
upstairs convention along that same map. The only block-theoretic literature
input is the existing one-way `CentralPrimeToPrimitiveImageSource`: a nonzero
image of a primitive central idempotent is primitive (Navarro, pp. 198--199,
Theorem 9.9(c)). The principal image equality is proved from the action on the
trivial representation. No character equivalence, chosen block image,
character-weight matching, or source injectivity is an input.

The source-neutral deductions below apply directly to that literal map. They
retain both displayed specified block decompositions; their authentication is
the same inherited catalogue obligation as in the downstairs application.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3PrincipalBrauerInflation

open ModularRep FDRepSimpleClassKZero
open IrreducibleBrauerCharacterSurjectiveDescent
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelPrincipalStability
open TypeBRankThreePrincipalReferenceBinding
open SporadicFi24P3Definition44NamedCarrierSurjectiveRoot
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport

variable {k K A B : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K] [Group A] [Finite A] [Group B] [Finite B]

local instance groupFintype (T : Type) [Group T] [Finite T] : Fintype T :=
  Fintype.ofFinite T

variable (q : A →* B) (surjective : Function.Surjective q)
  (central : q.ker ≤ Subgroup.center A) (primeTo : ¬ 2 ∣ Nat.card q.ker)
  (rootX : PrimeRegularRootEmbedding 2 k K A)

/-- One root convention, restricted along the same specified surjection. -/
abbrev downRoot : PrimeRegularRootEmbedding 2 k K B :=
  surjectiveRoot rootX q surjective

theorem root_compatible (V : FDRep k B) :
    Representation.BrauerRootLiftCompatibleAlong V.ρ
      (downRoot q surjective rootX) rootX q :=
  surjectiveRoot_compatible rootX q surjective V.ρ

private theorem support_asModule
    {T V : Type} [Group T] [AddCommGroup V] [Module k V]
    (rho : Representation k T V) (e : k[T])
    (he : rho.asAlgebraHom e = 1) : ∀ v : rho.asModule, e • v = v := by
  intro v
  apply rho.asModuleEquiv.injective
  rw [Representation.asModuleEquiv_map_smul, he]
  rfl

include central primeTo in
/-- Every irreducible representation supported by this principal idempotent
is trivial on the actual central prime-to-two kernel. -/
theorem principalRepresentation_kernel
    (bX : LiteralPrimitiveBlock k A) (hbX : IsPrincipal bX)
    (V : FDRep k A) (hV : Representation.IsIrreducible V.ρ)
    (hsupport : Representation.asAlgebraHom V.ρ bX.val = 1) : q.ker ≤ V.ρ.ker := by
  letI : Representation.IsIrreducible V.ρ := hV
  letI : Representation.IsIrreducible (1 : Representation k A k) :=
    trivialRepresentation_irreducible
  letI : Invertible (Fintype.card q.ker : k) := invertibleOfNonzero (by
    intro hzero
    apply primeTo
    simpa only [Nat.card_eq_fintype_card] using
      (CharP.cast_eq_zero_iff k 2 (Fintype.card q.ker)).mp hzero)
  have same : Representation.centralCharacter V.ρ q.ker central =
      Representation.centralCharacter (1 : Representation k A k) q.ker central :=
    (Representation.primitiveCentralIdempotentSector_eq_centralCharacter V.ρ q.ker central
      bX.property (support_asModule V.ρ bX.val hsupport)).symm.trans
      (Representation.primitiveCentralIdempotentSector_eq_centralCharacter (1 : Representation k A k)
        q.ker central bX.property (support_asModule _ bX.val hbX))
  have trivial : Representation.centralCharacter (1 : Representation k A k) q.ker central = 1 :=
    SporadicFi24P3Definition44NamedCarrierCentralBlockKernel.centralCharacter_eq_one_of_le_ker
      q.ker central (1 : Representation k A k) (by intro x hx; rfl)
  exact SporadicFi24P3Definition44NamedCarrierCentralBlockKernel.le_ker_of_centralCharacter_eq_one
    q.ker central V.ρ (same.trans trivial)

/-- The kernel-triviality witness is derived from literal principal support. -/
def principalKernelTrivial (bX : LiteralPrimitiveBlock k A) (hbX : IsPrincipal bX)
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    KernelTrivialIBrAlong q rootX := by
  refine ⟨phi.val, ?_⟩
  obtain ⟨V, hV, hchar, hsupp⟩ := phi.property
  exact ⟨V, hV, hchar, principalRepresentation_kernel q central primeTo bX hbX V hV hsupp⟩

variable [Fintype (LiteralPrimitiveBlock k A)] [Fintype (LiteralPrimitiveBlock k B)]
  (DX : BlockIdempotentDecomposition (fun c : LiteralPrimitiveBlock k A => c.val))
  (DB : BlockIdempotentDecomposition (fun c : LiteralPrimitiveBlock k B => c.val))
  (bX : LiteralPrimitiveBlock k A) (hbX : IsPrincipal bX)
  (b : LiteralPrimitiveBlock k B) (hb : IsPrincipal b)
  (primitive : CentralPrimeToPrimitiveImageSource (k := k)
    q surjective rootX.prime central primeTo)

include surjective central primeTo rootX DB hbX hb primitive in
/-- Principalness forces the specified image, without a supplied block map. -/
theorem principal_image : algebraMapOf q bX.val = b.val := by
  have support : (1 : Representation k B k).asAlgebraHom (algebraMapOf q bX.val) = 1 := by
    rw [← algebra_action_map]
    exact hbX
  have nonzero : algebraMapOf q bX.val ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at support
    exact zero_ne_one support
  let image : LiteralPrimitiveBlock k B :=
    ⟨algebraMapOf q bX.val,
      primitive.primitive_image_of_ne_zero _ bX.property nonzero⟩
  exact congrArg Subtype.val (principal_unique DB image b support hb)

/-- The checked full inflation/representation-descent equivalence, restricted
later to the same specified principal blocks. -/
def kernelEquiv : IBr (downRoot q surjective rootX) ≃ KernelTrivialIBrAlong q rootX :=
  quotientIBrEquivKernelTrivialIBrAlong q surjective
    (rootX.prime.coprime_iff_not_dvd.mpr primeTo).symm rootX
    (downRoot q surjective rootX) (root_compatible q surjective rootX)

include central DX DB hbX hb primitive in
theorem inflate_supported_iff (chi : IBr (downRoot q surjective rootX)) :
    Supported rootX bX (kernelEquiv q surjective primeTo rootX chi).val ↔
      Supported (downRoot q surjective rootX) b chi := by
  rw [supported_iff_block rootX DX, supported_iff_block _ DB]
  have image := actualBrauerBlock_image q surjective rootX.prime central primeTo primitive
    rootX (downRoot q surjective rootX) (root_compatible q surjective rootX)
    (injective rootX) (injective (downRoot q surjective rootX)) DX DB
    (kernelEquiv q surjective primeTo rootX chi).val chi rfl
  have imagePrincipal := principal_image q surjective central primeTo rootX DB bX hbX b hb primitive
  change algebraMapOf q (block rootX DX (kernelEquiv q surjective primeTo rootX chi).val).val =
    (block (downRoot q surjective rootX) DB chi).val at image
  constructor
  · intro h
    apply Subtype.ext
    rw [h] at image
    exact image.symm.trans imagePrincipal
  · intro h
    apply blockIndex_eq_of_map_eq_of_ne_zero DX (algebraMapOf q).toRingHom
    · exact image.trans ((congrArg Subtype.val h).trans imagePrincipal.symm)
    · change algebraMapOf q
        (block rootX DX (kernelEquiv q surjective primeTo rootX chi).val).val ≠ 0
      rw [image]
      exact (block (downRoot q surjective rootX) DB chi).property.ne_zero

/-- Deflate exactly the principal fibre; the inverse is literal inflation. -/
def principalBrauerDeflation :
    {phi : IBr rootX // Supported rootX bX phi} ≃
      {chi : IBr (downRoot q surjective rootX) // Supported (downRoot q surjective rootX) b chi} := by
  let E := kernelEquiv q surjective primeTo rootX
  have supportedKernel {phi : IBr rootX} (hphi : Supported rootX bX phi) :
      ∃ V : FDRep k A, Representation.IsIrreducible V.ρ ∧
        phi.val = Representation.brauerCharacterOfRootEmbedding V.ρ rootX ∧ q.ker ≤ V.ρ.ker :=
    (principalKernelTrivial q central primeTo rootX bX hbX ⟨phi, hphi⟩).property
  let flatten : {phi : KernelTrivialIBrAlong q rootX // Supported rootX bX phi.val} ≃
      {phi : IBr rootX // Supported rootX bX phi} :=
    Equiv.subtypeSubtypeEquivSubtype supportedKernel
  let restricted :
      {chi : IBr (downRoot q surjective rootX) // Supported (downRoot q surjective rootX) b chi} ≃
      {phi : KernelTrivialIBrAlong q rootX // Supported rootX bX phi.val} :=
    E.subtypeEquiv (fun chi =>
      (inflate_supported_iff q surjective central primeTo rootX DX DB bX hbX b hb primitive chi).symm)
  exact flatten.symm.trans restricted.symm

@[simp] theorem principalBrauerDeflation_symm_val
    (chi : {chi : IBr (downRoot q surjective rootX) //
      Supported (downRoot q surjective rootX) b chi}) :
    ((principalBrauerDeflation q surjective central primeTo rootX DX DB bX hbX b hb primitive).symm
      chi).val.val = PrimeRegularClassFunction.pullback q chi.val.val := rfl

/-- The original function is recovered on every actual prime regular element. -/
theorem principalBrauerDeflation_pullback
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    PrimeRegularClassFunction.pullback q
      (principalBrauerDeflation q surjective central primeTo rootX DX DB bX hbX b hb primitive
        phi).val.val = phi.val.val := by
  let E := principalBrauerDeflation q surjective central primeTo rootX DX DB bX hbX b hb primitive
  exact congrArg (fun z => z.val.val) (E.symm_apply_apply phi)

/-- Restrict the actual opposite automorphism twist to this principal fibre. -/
def principalStep (alpha : (MulAut A)ᵐᵒᵖ)
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    {phi : IBr rootX // Supported rootX bX phi} :=
  ⟨alpha • phi.val, supported_principal_op_smul DX rootX bX hbX alpha phi.val phi.property⟩

theorem principalBrauerDeflation_twist
    (alpha : (MulAut A)ᵐᵒᵖ) (beta : (MulAut B)ᵐᵒᵖ)
    (square : ∀ x, q (alpha.unop x) = beta.unop (q x))
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    (principalBrauerDeflation q surjective central primeTo rootX DX DB bX hbX b hb primitive
      (principalStep rootX DX bX hbX alpha phi)).val =
      beta • (principalBrauerDeflation q surjective central primeTo rootX DX DB bX hbX b hb primitive
        phi).val := by
  apply Subtype.ext
  apply primeRegularClassFunction_pullback_injective_of_ker_card_coprime q surjective
    (rootX.prime.coprime_iff_not_dvd.mpr primeTo).symm
  let E := principalBrauerDeflation q surjective central primeTo rootX DX DB bX hbX b hb primitive
  have stepValues : PrimeRegularClassFunction.pullback q
      (E (principalStep rootX DX bX hbX alpha phi)).val.val = phi.val.val.twist alpha.unop :=
    principalBrauerDeflation_pullback q surjective central primeTo rootX DX DB bX hbX b hb primitive
      (principalStep rootX DX bX hbX alpha phi)
  have baseValues : PrimeRegularClassFunction.pullback q (E phi).val.val = phi.val.val :=
    principalBrauerDeflation_pullback q surjective central primeTo rootX DX DB bX hbX b hb primitive phi
  have twistValues := CentralEllPrimeIBrFibreEquivariance.pullback_twist_of_commuting
    q alpha.unop beta.unop square (E phi).val.val
  exact stepValues.trans
    ((congrArg (fun eta : PrimeRegularClassFunction K A 2 => eta.twist alpha.unop)
      baseValues.symm).trans twistValues.symm)

include DX in
/-- Support holds for the same representation already chosen by the central
kernel definition, independently of the existential support witness. -/
theorem chosenRepresentation_support
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    Representation.asAlgebraHom
      (EvenFieldFLZBAWGoodFamily.chosenIBrRepresentation rootX phi.val).ρ bX.val = 1 := by
  let V := EvenFieldFLZBAWGoodFamily.chosenIBrRepresentation rootX phi.val
  have hV : Representation.IsIrreducible V.ρ := (Classical.choose_spec phi.val.property).1
  have hchar : phi.val.val = Representation.brauerCharacterOfRootEmbedding V.ρ rootX :=
    (Classical.choose_spec phi.val.property).2
  have hblock := (supported_iff_block rootX DX bX phi.val).mp phi.property
  apply LinearMap.ext
  intro v
  change Representation.asAlgebraHom V.ρ bX.val v = v
  have support := SporadicFi24P3Definition44NamedCarrierBrauerBlockAction.block_smul_of_affording
    rootX (injective rootX) DX phi.val V hV hchar
    ((Representation.asModuleEquiv V.ρ).symm v)
  change (block rootX DX phi.val).val • (Representation.asModuleEquiv V.ρ).symm v =
    (Representation.asModuleEquiv V.ρ).symm v at support
  rw [hblock] at support
  have values := congrArg (Representation.asModuleEquiv V.ρ) support
  simpa only [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] using values

include central primeTo DX hbX in
/-- If the actual quotient kernel is the full centre, the character's own
computed central kernel is that same subgroup, for every principal character. -/
theorem centralKernel_eq (kernelCenter : q.ker = Subgroup.center A)
    (phi : {phi : IBr rootX // Supported rootX bX phi}) :
    TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val = q.ker := by
  have hk := principalRepresentation_kernel q central primeTo bX hbX
    (EvenFieldFLZBAWGoodFamily.chosenIBrRepresentation rootX phi.val)
    (Classical.choose_spec phi.val.property).1
    (chosenRepresentation_support rootX DX bX phi)
  unfold TypeBBSCentralCharacterQuotient.centralKernel
  rw [← kernelCenter]
  exact inf_eq_left.mpr hk

end ModularRep.PaperProofs.TypeBQ3PrincipalBrauerInflation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
