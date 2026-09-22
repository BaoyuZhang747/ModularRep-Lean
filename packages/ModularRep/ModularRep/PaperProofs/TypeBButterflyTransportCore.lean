import ModularRep.PaperProofs.TypeBCentralKernelButterflyCharacterIdentification

/-!
# Prescribed Butterfly transfer

The proved local subgroup equality and prescribed reference character maps
supply the two elementary transport steps used by the actual selected consumer.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyTransport

open ModularRep
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleRootFamily
open TypeBCentralKernelButterflyCertificate

section LiteralTransfer

variable {p : ℕ} {k K T1 T2 : Type}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group T1] [Group T2] [Finite T1] [Finite T2]
  (N1 : Subgroup T1) (N2 : Subgroup T2) [N1.Normal] [N2.Normal]
  (e : N1 ≃* N2) (U1 : Subgroup T1) (U2 : Subgroup T2)

/-- Rewrite the proved actual local subgroup, then use the forward source. -/
theorem transfer_to_actualLocal
    (source : ButterflyCertificate p k K)
    (local_eq : secondLocalAmbient N1 N2 e U1 = U2)
    (D1 : TripleData (p := p) (k := k) (K := K) N1 U1)
    (D2 : TripleData (p := p) (k := k) (K := K) N2 U2)
    (localId : LocalIdentification N1 N2 e U1 U2)
    (theta1 : IBr D1.base.iota) (phi1 : IBr D1.localData.iota)
    (theta2 : IBr D2.base.iota) (phi2 : IBr D2.localData.iota)
    (images : SameConjugationImage N1 N2 e)
    (ambientRoots : AmbientRootsCompatible D1 D2)
    (baseCharacter : CharacterIdentification e D1.base D2.base theta1 theta2)
    (localCharacter :
      CharacterIdentification localId.equiv D1.localData D2.localData phi1 phi2)
    (witness : Nonempty (BlockTripleWitness D1 theta1 phi1)) :
    Nonempty (BlockTripleWitness D2 theta2 phi2) := by
  subst U2
  exact source.transfer T1 T2 N1 N2 e U1 D1 D2 localId theta1 phi1 theta2 phi2
    images ambientRoots baseCharacter localCharacter witness

end LiteralTransfer

section ReferenceCharacter

variable {p : ℕ} {k K H X Y : Type}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group H] [Finite H] [Group X] [Finite X] [Group Y] [Finite Y]

/-- The two prescribed reference coordinates identify the actual base characters. -/
theorem baseCharacterIdentification
    (root : PrimeRegularRootEmbedding p k K H) (theta : IBr root)
    (c : H ≃* X) (d : H ≃* Y)
    (DX : CharacterData p k K X) (thetaX : IBr DX.iota)
    (blocks : PhysicalBlocks k Y)
    (sourceRoots : DX.iota.lift = root.lift)
    (sourceValues : thetaX.val = PrimeRegularClassFunction.pullback
      c.symm.toMonoidHom theta.val) :
    CharacterIdentification (c.symm.trans d) DX
      (characterData (root.alongMulEquiv d) blocks) thetaX
      (IrreducibleBrauerCharacter.equivAlongMulEquiv root d theta) := by
  apply TypeBCentralKernelButterflyCharacterIdentification.of_lift_eq
    (c.symm.trans d) DX (characterData (root.alongMulEquiv d) blocks)
    thetaX (IrreducibleBrauerCharacter.equivAlongMulEquiv root d theta)
  · exact (funext (root.alongMulEquiv_lift d)).trans sourceRoots.symm
  · rw [sourceValues]
    ext x
    change theta.val (PrimeRegularElement.map d.symm.toMonoidHom x) =
      theta.val (PrimeRegularElement.map c.symm.toMonoidHom
        (PrimeRegularElement.map (c.symm.trans d).symm.toMonoidHom x))
    congr 1
    apply Subtype.ext
    exact (c.symm_apply_apply (d.symm x.val)).symm

end ReferenceCharacter

end ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
