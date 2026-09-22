import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryTransport

/-! The manuscript's actual ordinary local bijections and their covariance
for the SAME transported faithful family, with the original raw-match law
and stable-radical ordinary fixedness. Lower canonical availability is
chosen internally after e; no local-map or action conclusion is supplied. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily

open ModularRep ModularRep.CharacterWeight Formalisation
open TypeBCentralKernelNormalizerInertia (localAut)
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryTransport

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

local notation "hpX" => brauerProjection_equivariant iota hinj blocks R E1
local notation "hpY" => weightProjection_equivariant iota hinj blocks R E1

/-- Lower availability on actual ordinary local rows, covering both directions. -/
def LocalCanonicalAvailability : Prop :=
  ∀ (Q : RadicalSubgroup (p := p) (G := G))
    (theta : LocalDefectZeroCharacter (K := K) Q),
    Nonempty (CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))

/-- Concrete original-pair fixedness, constructed without reductions. -/
def StableMatchedOrdinaryFixed (e : FB ≃ FW) : Prop :=
  ∀ (phi : FB) (V : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val →
    ∀ (alpha : MulAut G) (stable : V.subgroup.comap alpha.toMonoidHom = V.subgroup),
      MulOpposite.op alpha • phi.val = phi.val ↔
        OrdinaryIrreducibleCharacter.twist K _ V.localCharacter
          (localAut V.subgroup alpha stable) = V.localCharacter

/-- A fixed OUTPUT family of actual ordinary equivalences, with all required laws. -/
def OrdinaryLocalOutput (e : FB ≃ FW)
    (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi) : Prop :=
  ∃ Omega : ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ RootSectorLocal iota nu.val Q,
    (∀ nu Q phi, classAt iota.prime Q (Omega nu Q phi).val = (e phi.val).val) ∧
    (∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)) (a : A)
      (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q),
      (Omega (a • nu) (Q.rightTwist a.unop)
        (brauerTransport iota hinj blocks R E1 e he nu Q a phi)).val =
        SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localCharacterTwist
          iota.prime Q a (Omega nu Q phi).val) ∧
    ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G))
      (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q)
      (alpha : MulAut G) (stable : Q.val.comap alpha.toMonoidHom = Q.val),
      MulOpposite.op alpha • phi.val.val = phi.val.val ↔
        OrdinaryIrreducibleCharacter.twist K _ (Omega nu Q phi).val.val
          (localAut Q.val alpha stable) = (Omega nu Q phi).val.val

theorem ordinary_output_of_availability (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota) :
    OrdinaryLocalOutput iota hinj blocks R E1 e hFamily.1 := by
  let CU := fun Q theta => Classical.choice (availability Q theta)
  let Omega := fun nu Q => localMap iota hinj blocks R E1 e hFamily.2.1 nu Q (CU Q) compatibility
  have hclass : ∀ nu Q phi, classAt iota.prime Q (Omega nu Q phi).val = (e phi.val).val := by
    intro nu Q phi
    exact localMap_class iota hinj blocks R E1 e hFamily.2.1 nu Q (CU Q) compatibility phi
  refine ⟨Omega, hclass, ?_, ?_⟩
  · intro nu Q a phi
    exact localMap_covariance iota hinj blocks R E1 e hFamily.1 hFamily.2.1
      CU compatibility nu Q a phi
  · intro nu Q phi alpha stable
    exact (hFamily.2.2.2.1 (MulOpposite.op alpha) phi.val).trans (by
      simpa only [hclass nu Q phi] using
        (classAt_fixed_iff_local_fixed iota.prime Q alpha stable (Omega nu Q phi).val))

/-- The family is chosen before compatibility/reduction realization inputs. -/
theorem family_ordinary_deduction (nu0 : S) (hcase : FaithfulSectorOrbitCases (G := G))
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e),
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      StableMatchedOrdinaryFixed iota hinj blocks R E1 e ∧
      (CanonicalLocalBlockCompatibility iota R.1.operations → LocalCanonicalAvailability iota →
        OrdinaryLocalOutput iota hinj blocks R E1 e hFamily.1) := by
  obtain ⟨e, hFamily, hIndependent⟩ := family_from_sector_orbit iota hinj blocks R E1 nu0
    (faithfulSector_orbit nu0 hcase) e0 he0
  refine ⟨e, hFamily, hIndependent, ?_, ?_⟩
  · intro phi V hmatch alpha stable
    exact original_local_fixed_iff iota hinj blocks R E1 e hFamily phi V hmatch alpha stable
  · exact ordinary_output_of_availability iota hinj blocks R E1 e hFamily

/-- The specified family/fixedness theorem, with ordinary realization after e. -/
theorem faithful_family_ordinary_transport
    (nu0 : FaithfulSector (k := k) (X := G)) (hcase : FaithfulSectorOrbitCases (G := G)) :
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let inj := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    let bP := faithfulBrauerSector iota inj bs R routine
    let wP := faithfulWeightSector iota inj bs R routine
    ∀ (e0 : Fibre bP nu0 ≃ Fibre wP nu0),
      (∀ (a : (MulAut G)ᵐᵒᵖ) (ha : a • nu0 = nu0) (x : Fibre bP nu0),
        e0 (stabilizerFibreEquiv bP
          (brauerProjection_equivariant iota inj bs R routine) nu0 a ha x) =
          stabilizerFibreEquiv wP
            (weightProjection_equivariant iota inj bs R routine) nu0 a ha (e0 x)) →
      ∃ (e : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine)
        (hFamily : FamilyProperties iota inj bs R routine e),
        (∀ (t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ)
          (ht : ∀ nu, t nu • nu0 = nu),
          e = transportedEquivalence iota inj bs R routine nu0 t ht e0) ∧
        StableMatchedOrdinaryFixed iota inj bs R routine e ∧
        (CanonicalLocalBlockCompatibility iota R.1.operations → LocalCanonicalAvailability iota →
          OrdinaryLocalOutput iota inj bs R routine e hFamily.1) := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  exact family_ordinary_deduction iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks R ⟨⟩ nu0 hcase

/-- AD(2)'s actual retained-root ordinary bijections and covariance, with
stable-radical ordinary fixedness, on the original transported family. -/
theorem faithful_family_ordinary_bijections
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (nu0 : FaithfulSector (k := k) (X := G)) (hcase : FaithfulSectorOrbitCases (G := G)) :
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let inj := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    let bP := faithfulBrauerSector iota inj bs R routine
    let wP := faithfulWeightSector iota inj bs R routine
    ∀ (e0 : Fibre bP nu0 ≃ Fibre wP nu0),
      (∀ (a : (MulAut G)ᵐᵒᵖ) (ha : a • nu0 = nu0) (x : Fibre bP nu0),
        e0 (stabilizerFibreEquiv bP
          (brauerProjection_equivariant iota inj bs R routine) nu0 a ha x) =
          stabilizerFibreEquiv wP
            (weightProjection_equivariant iota inj bs R routine) nu0 a ha (e0 x)) →
      ∃ (e : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine)
        (hFamily : FamilyProperties iota inj bs R routine e),
        (∀ (t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ)
          (ht : ∀ nu, t nu • nu0 = nu),
          e = transportedEquivalence iota inj bs R routine nu0 t ht e0) ∧
        StableMatchedOrdinaryFixed iota inj bs R routine e ∧
        OrdinaryLocalOutput iota inj bs R routine e hFamily.1 := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro e0 he0
  obtain ⟨e, hFamily, hIndependent, hFixed, hOrdinary⟩ :=
    faithful_family_ordinary_transport iota R nu0 hcase e0 he0
  exact ⟨e, hFamily, hIndependent, hFixed, hOrdinary compatibility availability⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
