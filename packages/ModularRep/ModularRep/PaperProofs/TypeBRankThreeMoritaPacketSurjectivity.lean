import ModularRep.PaperProofs.TypeBRankThreeMoritaSimpleTransport
import ModularRep.PaperProofs.TypeBRankThreeMoritaPhysicalSource

/-!
# Surjectivity of the same modular Jordan packet map

An irreducible representation supported by a central idempotent belongs
to its literal character packet. The base supported tensor equivalence
then supplies a preimage representation for each ambient packet character.
The existing uniform calibration identifies its character with the image
under the already specified Jordan map.

There is no additional map, equivalence or surjectivity source. These are
supporting deductions for the later all-orbit application.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaPacketSurjectivity

open ModularRep
open TypeBRankThreeJordanPacketCarriers
open TypeBRankThreeMoritaTensor TypeBRankThreeMoritaFiniteTensor
open TypeBRankThreeMoritaSources TypeBRankThreeMoritaSimpleTransport

section SupportConverse

variable {k K G I : Type}
  [Field k] [Field K] [Group G] [Finite G] [Fintype I]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  {d : I → k[G]}

/-- Support of the SAME irreducible affording module implies membership in
the packet of the displayed central idempotent. -/
theorem irreducible_supported_in_packet
    (root : PrimeRegularRootEmbedding 2 k K G)
    (blocks : BlockIdempotentDecomposition d) (e : k[G])
    (idempotent : IsIdempotentElem e) (central : IsMulCentral e)
    (phi : IBr root) (W : FDRep k G)
    (irreducible : Representation.IsIrreducible W.ρ)
    (support : supported e W)
    (affords : phi.val = Representation.brauerCharacterOfRootEmbedding W.ρ root) :
    InPacket root blocks e phi := by
  let c := supportingBlock root blocks phi
  have blockSupport : supported c.val W :=
    packet_affording_supported root blocks c.val
      (⟨phi, c.property.idempotent.eq⟩ : Packet root blocks c.val)
      W irreducible affords
  letI : IsSimpleModule k[G] (Representation.asModule W.ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule W.ρ).mp irreducible
  letI : Nontrivial (Representation.asModule W.ρ) :=
    IsSimpleModule.nontrivial k[G] (Representation.asModule W.ρ)
  letI : Nontrivial W := (Representation.asModuleEquiv W.ρ).symm.toEquiv.nontrivial
  change Representation.asAlgebraHom W.ρ c.val = 1 at blockSupport
  change Representation.asAlgebraHom W.ρ e = 1 at support
  have nonzero : c.val * e ≠ 0 := by
    intro zeroProduct
    have image := congrArg (Representation.asAlgebraHom W.ρ) zeroProduct
    have impossible : (1 : Module.End k W) = 0 := by
      simpa only [map_mul, blockSupport, support, map_zero, one_mul] using image
    exact one_ne_zero impossible
  change c.val * e = c.val
  exact (c.property.mul_eq_zero_or_eq_self_of_central_idempotent
    idempotent central).resolve_left nonzero

end SupportConverse

open TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBLeviRepresentativeCarriers TypeBLeviRepresentativeSelection
open TypeBRankThreeJordanOriginalTransport TypeBRankThreeJordanMap

variable {p f : ℕ} {F A E k K : Type}
  [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A]
  {N : NormSource 3 F} {Nbar : NormSource 3 A}
  {Frob : MulAut (SpecialClifford 3 A)}
  [Finite (SpecialClifford 3 F)] [Finite (Spin 3 F N)]
  [Finite (fixedPoints Frob.toMonoidHom)]
  [Group E] [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)
  (Lbar : Subgroup (SpecialClifford 3 A))
  (field : FieldData Frob Lbar E)
  (perfect : commutator (Spin 3 F N) = ⊤)
  (iotaL : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
  (iotaG : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))
  {IL IG : Type} [Fintype IL] [Fintype IG]
  {bL : IL → k[L Frob.toMonoidHom Lbar]}
  {bG : IG → k[Spin 3 F N]}
  (blocksL : BlockIdempotentDecomposition bL)
  (blocksG : BlockIdempotentDecomposition bG)
  (eL : k[L Frob.toMonoidHom Lbar]) (eG : k[Spin 3 F N])
  (gammaInvariant : ∀ m : Gamma Frob Lbar,
    MonoidAlgebra.mapDomainRingEquiv k (originalConjugation Frob Lbar m) eL = eL)
  (fieldInvariant : ∀ a : E,
    MonoidAlgebra.mapDomainRingEquiv k (originalField Frob Lbar field a) eL = eL)
  (J : ModularJordanMap points Lbar field perfect iotaL iotaG
    blocksL blocksG eL eG gammaInvariant fieldInvariant)

/-- The base Morita preimage and uniform calibration make the stored Jordan
packet map surjective. The actual consumer sets J to source.jordan. -/
theorem packetMap_surjective
    (tensorSupport : TensorSupportPrinciple k)
    (simpleSupported : SupportedSimplePrinciple k)
    (M : Rep.{0} k ((Spin 3 F N) × (L Frob.toMonoidHom Lbar)ᵐᵒᵖ))
    [Module.Finite k M]
    (leftSupport : LeftSupport M eG)
    (baseMorita : TypeBRankThreeMoritaPhysicalSource.BaseMorita
      tensorSupport M eL eG leftSupport)
    (sameJordan : TypeBRankThreeMoritaPhysicalSource.SameJordanCalibration
      iotaL iotaG blocksL eL J.character M)
    (idempotentL : IsIdempotentElem eL) (centralL : IsMulCentral eL) :
    Function.Surjective
      (TypeBRankThreeJordanMap.packetMap points Lbar field perfect iotaL iotaG
        blocksL blocksG eL eG gammaInvariant fieldInvariant J) := by
  let T : SupportedFDRep eL ⥤ SupportedFDRep eG :=
    supportedTensorFDFunctor M eL eG
      (fun V _ => tensorSupport M eG leftSupport V)
  letI : T.IsEquivalence := baseMorita
  intro phi
  obtain ⟨V, irreducibleV, affordsV⟩ := phi.val.property
  let Vs : SupportedFDRep eG :=
    ⟨V, packet_affording_supported iotaG blocksG eG phi V irreducibleV affordsV⟩
  let Ws : SupportedFDRep eL := T.objPreimage Vs
  let comparison : T.obj Ws ≅ Vs := T.objObjPreimageIso Vs
  have simpleV : CategoryTheory.Simple Vs := (simpleSupported eG Vs).mpr irreducibleV
  have simpleTensor : CategoryTheory.Simple (T.obj Ws) :=
    (CategoryTheory.Simple.iff_of_iso comparison).mpr simpleV
  have simpleW : CategoryTheory.Simple Ws :=
    (CategoryTheory.simple_obj_iff T Ws).mp simpleTensor
  have irreducibleW : Representation.IsIrreducible Ws.obj.ρ :=
    (simpleSupported eL Ws).mp simpleW
  let psiValue : IBr iotaL :=
    ⟨Representation.brauerCharacterOfRootEmbedding Ws.obj.ρ iotaL,
      ⟨Ws.obj, irreducibleW, rfl⟩⟩
  let psi : Packet iotaL blocksL eL :=
    ⟨psiValue, irreducible_supported_in_packet iotaL blocksL eL
      idempotentL centralL psiValue Ws.obj irreducibleW Ws.property rfl⟩
  let comparisonFD : tensorFDObj M Ws.obj ≅ V :=
    (supported eG).ι.mapIso comparison
  have sameCharacter := Representation.brauerCharacterOfRootEmbedding_iso iotaG comparisonFD
  have calibration := sameJordan psi Ws.obj irreducibleW rfl
  refine ⟨psi, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (J.character psi).val = phi.val.val
  exact calibration.symm.trans (sameCharacter.trans affordsV.symm)

end ModularRep.PaperProofs.TypeBRankThreeMoritaPacketSurjectivity


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
