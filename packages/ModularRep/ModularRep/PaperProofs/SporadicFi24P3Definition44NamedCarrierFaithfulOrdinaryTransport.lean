import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps

/-! Ordinary local-map covariance and the stable-radical equivalence of
original global Brauer fixedness and original local ordinary fixedness. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryTransport

open ModularRep ModularRep.CharacterWeight
open TypeBCentralKernelNormalizerInertia
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "A" => (MulAut G)ᵐᵒᵖ
local notation "S" => FaithfulSector (k := k) (X := G)
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1
local notation "pX" => faithfulBrauerSector iota hinj blocks R E1
local notation "pY" => faithfulWeightSector iota hinj blocks R E1

def brauerTransport (e : FB ≃ FW)
    (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi)
    (nu : S) (Q : RadicalSubgroup (p := p) (G := G)) (a : A)
    (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q) :
    BrauerAtSectorRadical iota hinj blocks R E1 e (a • nu) (Q.rightTwist a.unop) := by
  refine ⟨a • phi.1, ?_, ?_⟩
  · rw [brauerProjection_equivariant, phi.2.1]
  · rw [he]
    change radicalClass (a • (e phi.1).val) = _
    rw [radicalClass_equivariant, phi.2.2]
    rfl

theorem localMap_covariance (e : FB ≃ FW)
    (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi)
    (hs : ∀ phi : FB, pY (e phi) = pX phi)
    (CU : ∀ (Q : RadicalSubgroup (p := p) (G := G))
      (theta : LocalDefectZeroCharacter (K := K) Q),
      CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (nu : S) (Q : RadicalSubgroup (p := p) (G := G)) (a : A)
    (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q) :
    (localMap iota hinj blocks R E1 e hs (a • nu) (Q.rightTwist a.unop)
      (CU (Q.rightTwist a.unop)) compatibility
      (brauerTransport iota hinj blocks R E1 e he nu Q a phi)).val =
      SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localCharacterTwist
        iota.prime Q a (localMap iota hinj blocks R E1 e hs nu Q (CU Q) compatibility phi).val := by
  apply classAt_injective iota.prime (Q.rightTwist a.unop)
  rw [localMap_class]
  change (e (a • phi.1)).val = a • classAt iota.prime Q
    (localMap iota hinj blocks R E1 e hs nu Q (CU Q) compatibility phi).val
  rw [he, localMap_class]
  rfl

theorem original_local_fixed_iff (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (alpha : MulAut G) (stable : V.subgroup.comap alpha.toMonoidHom = V.subgroup) :
    MulOpposite.op alpha • phi.val = phi.val ↔
      OrdinaryIrreducibleCharacter.twist K _ V.localCharacter
        (localAut V.subgroup alpha stable) = V.localCharacter := by
  let Q : RadicalSubgroup (p := p) (G := G) := ⟨V.subgroup, V.radical⟩
  let theta : LocalDefectZeroCharacter (K := K) Q := ⟨V.localCharacter, V.defectZero⟩
  have hc : classAt iota.prime Q theta = (e phi).val := hmatch
  exact (hFamily.2.2.2.1 (MulOpposite.op alpha) phi).trans (by
    simpa only [hc] using
      (classAt_fixed_iff_local_fixed iota.prime Q alpha stable theta))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
