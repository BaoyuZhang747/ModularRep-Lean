import ModularRep.PaperProofs.TypeBCentralKernelButterflyAmbientIsomorphism
import ModularRep.PaperProofs.TypeBCentralKernelButterflyCharacterIdentification
import ModularRep.PaperProofs.TypeBCentralKernelTripleRootFamily

/-!
# Full literal block-triple transport through an anchored ambient equivalence

The target root family is constructed from the source roots and the actual
ambient, base and local equivalences. Specified catalogues remain on their
literal target groups. All group, root and character-identification guards
of the one-way Butterfly certificate are deductions. The only triple input
is the existing source-side witness; no target witness is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelButterflyWitnessTransport

open ModularRep TypeBCentralKernelTripleCertificate
open TypeBCentralKernelTripleRootFamily TypeBCentralKernelButterflyCertificate
open TypeBCentralKernelButterflyAmbientIsomorphism

universe u

variable {p : ℕ} {k K T1 T2 : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group T1] [Group T2] [Finite T1] [Finite T2]
variable (N1 : Subgroup T1) (N2 : Subgroup T2) [N1.Normal] [N2.Normal]
variable (H1 : Subgroup T1) (eT : T1 ≃* T2) (eN : N1 ≃* N2)
variable (D1 : TripleData (p := p) (k := k) (K := K) N1 H1)

abbrev targetLocalAmbient := secondLocalAmbient N1 N2 eN H1

def localId (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1) :
    LocalIdentification N1 N2 eN H1 (targetLocalAmbient N1 N2 H1 eN) :=
  constructedLocalIdentification N1 N2 eN H1 centralizer_le

theorem targetBaseRoots
    (z : rootsOfUnity (primeRegularExponent p N2) k) :
    (D1.base.iota.alongMulEquiv eN).lift ((z : kˣ) : k) =
      (D1.ambientRoot.alongMulEquiv eT).lift ((z : kˣ) : k) :=
  (alongMulEquiv_agrees D1.ambientRoot D1.base.iota eN D1.baseRoots z).trans
    (D1.ambientRoot.alongMulEquiv_lift eT _).symm

theorem targetLocalRoots
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (z : rootsOfUnity
      (primeRegularExponent p (localBase N2 (targetLocalAmbient N1 N2 H1 eN))) k) :
    (D1.localData.iota.alongMulEquiv (localId N1 N2 H1 eN centralizer_le).equiv).lift
        ((z : kˣ) : k) =
      (D1.ambientRoot.alongMulEquiv eT).lift ((z : kˣ) : k) :=
  (alongMulEquiv_agrees D1.ambientRoot D1.localData.iota
    (localId N1 N2 H1 eN centralizer_le).equiv D1.localRoots z).trans
      (D1.ambientRoot.alongMulEquiv_lift eT _).symm

/-- Construct every target root and character-separation proof while retaining
the actual target primitive-block catalogues. -/
def targetData
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (blocks : PhysicalBlockFamily (k := k) N2 (targetLocalAmbient N1 N2 H1 eN)) :
    TripleData (p := p) (k := k) (K := K) N2 (targetLocalAmbient N1 N2 H1 eN) :=
  withPrescribedRoots N2 (targetLocalAmbient N1 N2 H1 eN)
    (D1.ambientRoot.alongMulEquiv eT)
    (D1.base.iota.alongMulEquiv eN)
    (D1.localData.iota.alongMulEquiv (localId N1 N2 H1 eN centralizer_le).equiv)
    (targetBaseRoots N1 N2 H1 eT eN D1)
    (targetLocalRoots N1 N2 H1 eT eN D1 centralizer_le) blocks

theorem targetData_ambientRoot
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (blocks : PhysicalBlockFamily (k := k) N2 (targetLocalAmbient N1 N2 H1 eN)) :
    (targetData N1 N2 H1 eT eN D1 centralizer_le blocks).ambientRoot =
      D1.ambientRoot.alongMulEquiv eT := rfl

theorem targetData_base_iota
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (blocks : PhysicalBlockFamily (k := k) N2 (targetLocalAmbient N1 N2 H1 eN)) :
    (targetData N1 N2 H1 eT eN D1 centralizer_le blocks).base.iota =
      D1.base.iota.alongMulEquiv eN := rfl

theorem targetData_local_iota
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (blocks : PhysicalBlockFamily (k := k) N2 (targetLocalAmbient N1 N2 H1 eN)) :
    (targetData N1 N2 H1 eT eN D1 centralizer_le blocks).localData.iota =
      D1.localData.iota.alongMulEquiv (localId N1 N2 H1 eN centralizer_le).equiv := rfl

theorem ambientRootsCompatible
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (blocks : PhysicalBlockFamily (k := k) N2 (targetLocalAmbient N1 N2 H1 eN)) :
    AmbientRootsCompatible D1 (targetData N1 N2 H1 eT eN D1 centralizer_le blocks) := by
  intro z _ _
  exact (D1.ambientRoot.alongMulEquiv_lift eT (z : k)).symm

def targetTheta
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (blocks : PhysicalBlockFamily (k := k) N2 (targetLocalAmbient N1 N2 H1 eN))
    (theta : IBr D1.base.iota) :
    IBr (targetData N1 N2 H1 eT eN D1 centralizer_le blocks).base.iota :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv D1.base.iota eN theta

def targetPhi
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (blocks : PhysicalBlockFamily (k := k) N2 (targetLocalAmbient N1 N2 H1 eN))
    (phi : IBr D1.localData.iota) :
    IBr (targetData N1 N2 H1 eT eN D1 centralizer_le blocks).localData.iota :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv D1.localData.iota
    (localId N1 N2 H1 eN centralizer_le).equiv phi

theorem baseIdentification
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (blocks : PhysicalBlockFamily (k := k) N2 (targetLocalAmbient N1 N2 H1 eN))
    (theta : IBr D1.base.iota) :
    CharacterIdentification eN D1.base
      (targetData N1 N2 H1 eT eN D1 centralizer_le blocks).base theta
      (targetTheta N1 N2 H1 eT eN D1 centralizer_le blocks theta) :=
  TypeBCentralKernelButterflyCharacterIdentification.of_lift_eq eN D1.base
    (targetData N1 N2 H1 eT eN D1 centralizer_le blocks).base theta
    (targetTheta N1 N2 H1 eT eN D1 centralizer_le blocks theta)
    (funext (D1.base.iota.alongMulEquiv_lift eN)) rfl

theorem localIdentification
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (blocks : PhysicalBlockFamily (k := k) N2 (targetLocalAmbient N1 N2 H1 eN))
    (phi : IBr D1.localData.iota) :
    CharacterIdentification (localId N1 N2 H1 eN centralizer_le).equiv D1.localData
      (targetData N1 N2 H1 eT eN D1 centralizer_le blocks).localData phi
      (targetPhi N1 N2 H1 eT eN D1 centralizer_le blocks phi) :=
  TypeBCentralKernelButterflyCharacterIdentification.of_lift_eq
    (localId N1 N2 H1 eN centralizer_le).equiv D1.localData
    (targetData N1 N2 H1 eT eN D1 centralizer_le blocks).localData phi
    (targetPhi N1 N2 H1 eT eN D1 centralizer_le blocks phi)
    (funext (D1.localData.iota.alongMulEquiv_lift
      (localId N1 N2 H1 eN centralizer_le).equiv)) rfl

/-- Transfer into independently prescribed literal target data. Root
compatibility is equality of actual lift functions, never equality of root
records. Character hypotheses are the precise pullback equations on the
anchored base and constructed local equivalences; specified block matching
is then a deduction of the checked character-identification helper. -/
theorem transfer_to_prescribed
    (anchor : ∀ n : N1, eT (n : T1) = (eN n : T2))
    (D2 : TripleData (p := p) (k := k) (K := K) N2 (targetLocalAmbient N1 N2 H1 eN))
    (theta : IBr D1.base.iota) (phi : IBr D1.localData.iota)
    (witness : BlockTripleWitness D1 theta phi)
    (theta2 : IBr D2.base.iota) (phi2 : IBr D2.localData.iota)
    (ambientRoots : AmbientRootsCompatible D1 D2)
    (baseLifts : D2.base.iota.lift = D1.base.iota.lift)
    (localLifts : D2.localData.iota.lift = D1.localData.iota.lift)
    (baseValues : theta2.val = PrimeRegularClassFunction.pullback eN.symm.toMonoidHom theta.val)
    (localValues : phi2.val = PrimeRegularClassFunction.pullback
      (localId N1 N2 H1 eN witness.centralizer_le).equiv.symm.toMonoidHom phi.val)
    (certificate : ButterflyCertificate p k K) :
    Nonempty (BlockTripleWitness D2 theta2 phi2) :=
  certificate.transfer T1 T2 N1 N2 eN H1 D1 D2
    (localId N1 N2 H1 eN witness.centralizer_le) theta phi theta2 phi2
    (sameConjugationImage N1 N2 eT eN anchor) ambientRoots
    (TypeBCentralKernelButterflyCharacterIdentification.of_lift_eq
      eN D1.base D2.base theta theta2 baseLifts baseValues)
    (TypeBCentralKernelButterflyCharacterIdentification.of_lift_eq
      (localId N1 N2 H1 eN witness.centralizer_le).equiv
      D1.localData D2.localData phi phi2 localLifts localValues)
    ⟨witness⟩

/-- Exact one-way certificate application. The target root family and both
target characters are constructed; the old witness supplies its own
centralizer guard. No target-side block-triple premise occurs. -/
theorem transfer
    (anchor : ∀ n : N1, eT (n : T1) = (eN n : T2))
    (blocks : PhysicalBlockFamily (k := k) N2 (targetLocalAmbient N1 N2 H1 eN))
    (theta : IBr D1.base.iota) (phi : IBr D1.localData.iota)
    (witness : BlockTripleWitness D1 theta phi)
    (certificate : ButterflyCertificate p k K) :
    Nonempty (BlockTripleWitness
      (targetData N1 N2 H1 eT eN D1 witness.centralizer_le blocks)
      (targetTheta N1 N2 H1 eT eN D1 witness.centralizer_le blocks theta)
      (targetPhi N1 N2 H1 eT eN D1 witness.centralizer_le blocks phi)) :=
  transfer_to_prescribed N1 N2 H1 eT eN D1 anchor
    (targetData N1 N2 H1 eT eN D1 witness.centralizer_le blocks)
    theta phi witness
    (targetTheta N1 N2 H1 eT eN D1 witness.centralizer_le blocks theta)
    (targetPhi N1 N2 H1 eT eN D1 witness.centralizer_le blocks phi)
    (ambientRootsCompatible N1 N2 H1 eT eN D1 witness.centralizer_le blocks)
    (funext (D1.base.iota.alongMulEquiv_lift eN))
    (funext (D1.localData.iota.alongMulEquiv_lift
      (localId N1 N2 H1 eN witness.centralizer_le).equiv))
    rfl rfl certificate

end ModularRep.PaperProofs.TypeBCentralKernelButterflyWitnessTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
