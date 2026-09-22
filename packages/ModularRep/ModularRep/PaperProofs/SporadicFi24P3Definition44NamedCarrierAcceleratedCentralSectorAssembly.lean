import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
import ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

/-! Central character decompositions of raw extension and block constructions. Root compatibility must be supplied separately before these data express the full inductive condition. -/
noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCentralSectorAssembly
open Formalisation ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open EvenFieldFLZSourceConditions
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalSpathWitness
open SporadicFi24P3Definition44NamedCarrierOriginalActualPacket
open SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
open SporadicFi24P3Definition44NamedCarrierNormalizedPairs
open SporadicFi24P3Definition44NamedCarrierRepresentativePackets
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
universe u
variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (E1 : RoutineTransportInput iota hinj blocks R)
variable (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
variable (D : DefectZeroReductionSource iota)
variable (T : TrivialWeightSource (p := p) (X := X))

structure SectorInputs where
  family : EquivariantFibreEquiv
    (brauerSector iota hinj blocks) (weightSector (R := R))
    (brauerSector_equivariant iota hinj blocks E1)
    (weightSector_equivariant_actual (iota := iota) (hinj := hinj)
      (blocks := blocks) (R := R) E1)
  blockInduction : ∀ (nu : CentralSector (k := k) (X := X))
      (phi : Fibre (brauerSector iota hinj blocks) nu),
    R.1.weightBlock (family.fibreEquiv nu phi) = brauerBlock iota hinj blocks phi
  classQOne : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
    (family.fibreEquiv (brauerSector iota hinj blocks (D.reduce (iota := iota) d))
      ⟨D.reduce (iota := iota) d, rfl⟩).val = T.atOne d
  compatibility : CanonicalLocalBlockCompatibility iota R.1.operations
  packets : ∀ (nu : CentralSector (k := k) (X := X))
      (phi : Fibre (brauerSector iota hinj blocks) nu) (V : CharacterWeight p K X),
    (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := X)) = (family.fibreEquiv nu phi).val →
    OriginalActualWeightPacket
      (problemAt iota hinj R (canonicalSelectedReduction iota R C) phi.val)
      (ownBrauerAt iota hinj R (canonicalSelectedReduction iota R C) phi.val) V

variable (Cover : EllPrimeCoverSource p X)

def assemble (I : SectorInputs iota hinj blocks R E1 C D T) :
    Definition41Witness iota hinj R C Cover D T := by
  refine {
    Omega := I.family.assemble
    equivariant := EquivariantFibreEquiv.assemble_equivariant I.family
    block_preserving := ?_
    classQOne := I.classQOne
    compatibility := I.compatibility
    packets := ?_ }
  · intro phi
    exact (I.blockInduction (brauerSector iota hinj blocks phi) ⟨phi, rfl⟩).trans
      (operationsBlock_eq iota hinj R blocks phi).symm
  · intro Q xi
    exact I.packets (brauerSector iota hinj blocks xi.1) ⟨xi.1, rfl⟩
      (characterWeightAt iota.prime Q (localMap iota I.family.assemble iota.prime Q xi))
      (localMap_class iota I.family.assemble iota.prime Q xi)

/-- The disjoint union satisfies the fixed complete condition, including its
representative local maps, extensions, all intermediate blocks and both Q=1 laws. -/
theorem definition41_from_sector_inputs (I : SectorInputs iota hinj blocks R E1 C D T) :
    RawDefinition41Certificate iota R Cover :=
  raw_of_original iota R Cover C D T ⟨assemble iota hinj blocks R E1 C D T Cover I⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCentralSectorAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
