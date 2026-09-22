import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints

/-! Actual ordinary local bijections in the retained-root central sector,
constructed from the SAME faithful family. The representative class law
retains the original global image and removes dependence on reductions. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints

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

abbrev BrauerAtSectorRadical (e : FB ≃ FW) (nu : S)
    (Q : RadicalSubgroup (p := p) (G := G)) :=
  {phi : FB // pX phi = nu ∧ radicalClass (e phi).val =
    (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G))}

def brauerWeightFibreEquiv (e : FB ≃ FW) (hs : ∀ phi : FB, pY (e phi) = pX phi)
    (nu : S) (Q : RadicalSubgroup (p := p) (G := G)) :
    BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ WeightSectorRadicalFibre R nu.val Q where
  toFun phi := ⟨⟨(e phi.1).val, phi.2.2⟩, congrArg Subtype.val ((hs phi.1).trans phi.2.1)⟩
  invFun w :=
    let wF : FW := ⟨w.1.1, by rw [w.2]; exact nu.2⟩
    ⟨e.symm wF, by
      constructor
      · rw [← hs, e.apply_symm_apply]
        exact Subtype.ext w.2
      · rw [e.apply_symm_apply]
        exact w.1.2⟩
  left_inv phi := by
    apply Subtype.ext
    change e.symm (e phi.1) = phi.1
    exact e.symm_apply_apply phi.1
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    change (e (e.symm _)).val = w.1.1
    rw [e.apply_symm_apply]

def localMap (e : FB ≃ FW) (hs : ∀ phi : FB, pY (e phi) = pX phi)
    (nu : S) (Q : RadicalSubgroup (p := p) (G := G))
    (CU : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
      CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations) :
    BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ RootSectorLocal iota nu.val Q :=
  (brauerWeightFibreEquiv iota hinj blocks R E1 e hs nu Q).trans
    (rootSectorLocalToWeight iota R nu.val Q CU compatibility).symm

theorem localMap_class (e : FB ≃ FW) (hs : ∀ phi : FB, pY (e phi) = pX phi)
    (nu : S) (Q : RadicalSubgroup (p := p) (G := G))
    (CU : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
      CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q) :
    classAt iota.prime Q (localMap iota hinj blocks R E1 e hs nu Q CU compatibility phi).val =
      (e phi.val).val := by
  have h := (rootSectorLocalToWeight iota R nu.val Q CU compatibility).apply_symm_apply
    (brauerWeightFibreEquiv iota hinj blocks R E1 e hs nu Q phi)
  have hv := congrArg (fun w : WeightSectorRadicalFibre R nu.val Q => w.1.1) h
  change (localDefectZeroEquivWeightRadicalFibre iota.prime Q
    (localMap iota hinj blocks R E1 e hs nu Q CU compatibility phi).val).val = (e phi.val).val at hv
  simpa only [localDefectZeroEquivWeightRadicalFibre_apply_val, classAt,
    brauerWeightFibreEquiv] using hv

theorem localMap_independent_of_reductions
    (e : FB ≃ FW) (hs : ∀ phi : FB, pY (e phi) = pX phi)
    (nu : S) (Q : RadicalSubgroup (p := p) (G := G))
    (CU CU' : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
      CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations) :
    localMap iota hinj blocks R E1 e hs nu Q CU compatibility =
      localMap iota hinj blocks R E1 e hs nu Q CU' compatibility := by
  apply Equiv.ext
  intro phi
  apply Subtype.ext
  apply classAt_injective iota.prime Q
  rw [localMap_class, localMap_class]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
