import ModularRep.PaperProofs.TypeBCentralKernelButterflyWitnessTransport

/-!
# Literal block triples on an independently specified conjugate local group

The existing Butterfly transport constructs a local group as a preimage
under the action on the normal base. Here an actual ambient isomorphism
and its subgroup-image equation identify that group with a prescribed
target. The local character guard is a pointwise equation on the same
ambient elements, retaining the actual prime regular domains.

Only an existing source-side BlockTripleWitness is transported. The
one-way Butterfly certificate, root compatibility and literal specified
character data remain explicit. No arbitrary relation-preservation or
target-triple premise is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelConjugateTripleTransport

open ModularRep TypeBCentralKernelTripleCertificate
open TypeBCentralKernelButterflyCertificate
open TypeBCentralKernelButterflyWitnessTransport

universe u

variable {p : ℕ} {k K T1 T2 : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group T1] [Group T2] [Finite T1] [Finite T2]
  (N1 : Subgroup T1) (N2 : Subgroup T2) [N1.Normal] [N2.Normal]
  (U1 : Subgroup T1) (U2 : Subgroup T2)
  (eT : T1 ≃* T2) (eN : N1 ≃* N2)

/-- Transport every clause of the literal witness to the actual image
local group. The base and local characters are independently prescribed,
then identified by their values, never by a desired block correspondence. -/
theorem transfer_to_image
    (anchor : ∀ n : N1, eT (n : T1) = (eN n : T2))
    (localImage : U1.map eT.toMonoidHom = U2)
    (D1 : TripleData (p := p) (k := k) (K := K) N1 U1)
    (D2 : TripleData (p := p) (k := k) (K := K) N2 U2)
    (theta1 : IBr D1.base.iota) (phi1 : IBr D1.localData.iota)
    (theta2 : IBr D2.base.iota) (phi2 : IBr D2.localData.iota)
    (witness : BlockTripleWitness D1 theta1 phi1)
    (ambientRoots : AmbientRootsCompatible D1 D2)
    (baseLifts : D2.base.iota.lift = D1.base.iota.lift)
    (localLifts : D2.localData.iota.lift = D1.localData.iota.lift)
    (baseValues : theta2.val = PrimeRegularClassFunction.pullback eN.symm.toMonoidHom theta1.val)
    (localValues : ∀ (x : PrimeRegularElement (G := localBase N1 U1) p)
        (y : PrimeRegularElement (G := localBase N2 U2) p),
      eT x.val.val.val = y.val.val.val → phi2.val y = phi1.val x)
    (certificate : ButterflyCertificate p k K) :
    Nonempty (BlockTripleWitness D2 theta2 phi2) := by
  have localEq : targetLocalAmbient N1 N2 U1 eN = U2 :=
    (TypeBCentralKernelButterflyAmbientIsomorphism.secondLocalAmbient_eq_map
      N1 N2 eT eN anchor U1 witness.centralizer_le).trans localImage
  cases localEq
  apply transfer_to_prescribed N1 N2 U1 eT eN D1 anchor D2
    theta1 phi1 witness theta2 phi2 ambientRoots baseLifts localLifts baseValues
    ?_ certificate
  ext y
  let eLocal := (localId N1 N2 U1 eN witness.centralizer_le).equiv
  change phi2.val y = phi1.val (PrimeRegularElement.map eLocal.symm.toMonoidHom y)
  apply localValues (PrimeRegularElement.map eLocal.symm.toMonoidHom y) y
  change eT (eLocal.symm y.val).val.val = y.val.val.val
  have anchored :=
    TypeBCentralKernelButterflyAmbientIsomorphism.localIdentification_ambient_value
      N1 N2 eT eN anchor U1 witness.centralizer_le (eLocal.symm y.val)
  exact anchored.symm.trans
    (congrArg (fun z : localBase N2 (targetLocalAmbient N1 N2 U1 eN) => z.val.val)
      (eLocal.apply_symm_apply y.val))

end ModularRep.PaperProofs.TypeBCentralKernelConjugateTripleTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
