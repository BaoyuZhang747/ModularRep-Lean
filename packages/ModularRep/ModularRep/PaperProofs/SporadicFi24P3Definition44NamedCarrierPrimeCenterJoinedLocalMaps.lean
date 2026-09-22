import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorJoin
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints

/-! All actual radical rows of the same joined correspondence. -/
noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterJoinedLocalMaps

open ModularRep Formalisation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorSplit

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
local notation "C" => Subgroup.center G
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1
local notation "TB" => Fibre (brauerSector iota hinj blocks) (1 : CentralSector (k := k) (X := G))
local notation "W" => CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)
local notation "SW" => SectorWeights R C


open SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorCarriers
variable (hprime : (Nat.card (Subgroup.center G)).Prime)
variable (eT : Fibre (brauerSector iota hinj blocks) (1 : CentralSector (k := k) (X := G)) ≃
  SectorWeights R (Subgroup.center G))
variable (eF : FaithfulIBr iota hinj blocks R E1 ≃ FaithfulWeight iota hinj blocks R E1)

open ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorJoin
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
local notation "J" => joined iota hinj blocks R E1 hprime eT eF
local notation "RC" => RadicalConjugacyClass (p := p) (G := G)

def radicalPart (q : RC) : Set (IBr iota) :=
  {phi | radicalClass (J phi) = q}

def radicalPartition : IBr iota ≃ Sigma fun q : RC =>
    {phi : IBr iota // phi ∈ radicalPart iota hinj blocks R E1 hprime eT eF q} :=
  (Equiv.sigmaFiberEquiv (fun phi : IBr iota => radicalClass (J phi))).symm

theorem radicalPart_cover :
    (⋃ q, radicalPart iota hinj blocks R E1 hprime eT eF q) = Set.univ := by
  ext phi
  simp only [radicalPart, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ⟨_, rfl⟩

theorem radicalPart_disjoint : Pairwise (fun q q' : RC => Disjoint
    (radicalPart iota hinj blocks R E1 hprime eT eF q)
    (radicalPart iota hinj blocks R E1 hprime eT eF q')) := by
  intro q q' hne
  apply Set.disjoint_left.mpr
  intro phi h h'
  exact hne (h.symm.trans h')

def trivialGlobalRow (Q : RadicalSubgroup (p := p) (G := G)) (phi : TB)
    (hQ : radicalClass (eT phi).val = (Quotient.mk'' Q : RC)) :
    BrauerAtRadical iota J Q :=
  ⟨phi.val, by rw [joined_trivial]; exact hQ⟩

def faithfulGlobalRow (Q : RadicalSubgroup (p := p) (G := G)) (phi : FB)
    (hQ : radicalClass (eF phi).val = (Quotient.mk'' Q : RC)) :
    BrauerAtRadical iota J Q :=
  ⟨phi.val, by rw [joined_faithful]; exact hQ⟩

theorem joined_local_trivial (Q : RadicalSubgroup (p := p) (G := G)) (phi : TB)
    (hQ : radicalClass (eT phi).val = (Quotient.mk'' Q : RC))
    (theta : LocalDefectZeroCharacter (K := K) Q)
    (hclass : classAt iota.prime Q theta = (eT phi).val) :
    localMap iota J iota.prime Q
      (trivialGlobalRow iota hinj blocks R E1 hprime eT eF Q phi hQ) = theta := by
  apply classAt_injective iota.prime Q
  exact (localMap_class iota J iota.prime Q _).trans
    ((joined_trivial iota hinj blocks R E1 hprime eT eF phi).trans hclass.symm)

theorem joined_local_faithful (Q : RadicalSubgroup (p := p) (G := G)) (phi : FB)
    (hQ : radicalClass (eF phi).val = (Quotient.mk'' Q : RC))
    (theta : LocalDefectZeroCharacter (K := K) Q)
    (hclass : classAt iota.prime Q theta = (eF phi).val) :
    localMap iota J iota.prime Q
      (faithfulGlobalRow iota hinj blocks R E1 hprime eT eF Q phi hQ) = theta := by
  apply classAt_injective iota.prime Q
  exact (localMap_class iota J iota.prime Q _).trans
    ((joined_faithful iota hinj blocks R E1 hprime eT eF phi).trans hclass.symm)

theorem radicalPart_support (Q : RadicalSubgroup (p := p) (G := G)) :
    (radicalPart iota hinj blocks R E1 hprime eT eF (Quotient.mk'' Q)).Nonempty ↔
      Nonempty (LocalDefectZeroCharacter (K := K) Q) := by
  constructor
  · rintro ⟨phi, hphi⟩
    exact ⟨localMap iota J iota.prime Q ⟨phi, hphi⟩⟩
  · rintro ⟨theta⟩
    let phi := (localMap iota J iota.prime Q).symm theta
    exact ⟨phi.val, phi.property⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterJoinedLocalMaps


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
