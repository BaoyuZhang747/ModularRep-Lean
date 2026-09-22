import ModularRep.BrauerCharacterHomPullback

/-!
# Transport of Brauer-character extension witnesses

An ambient group equivalence and a compatible equivalence of normal
subgroups transport a Brauer-character extension witness.  The subgroup
character on the target may be supplied independently, provided its class
function is the transported source character.
-/

noncomputable section

namespace Representation.Extension

universe u

open ModularRep

variable {p : ℕ} {k K H H' : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H] [Group H'] [Finite H']

/-- Transport an extension witness across a commuting square of ambient and
base-group equivalences, with an explicitly identified target base
character. -/
noncomputable def BrauerCharacterExtensionWitness.alongMulEquivOfBase
    {N : Subgroup H} {N' : Subgroup H'}
    (eH : H ≃* H') (eN : N ≃* N')
    (hsquare : eH.symm.toMonoidHom.comp N'.subtype =
      N.subtype.comp eN.symm.toMonoidHom)
    {iotaH : PrimeRegularRootEmbedding p k K H}
    {iotaN : PrimeRegularRootEmbedding p k K N}
    {phiN : IBr iotaN}
    (W : BrauerCharacterExtensionWitness iotaH iotaN phiN)
    (iotaN' : PrimeRegularRootEmbedding p k K N')
    (phiN' : IBr iotaN')
    (hphi : PrimeRegularClassFunction.pullback
      eN.symm.toMonoidHom phiN.1 = phiN'.1) :
    BrauerCharacterExtensionWitness
      (iotaH.alongMulEquiv eH) iotaN' phiN' := by
  refine ⟨IrreducibleBrauerCharacter.alongMulEquiv iotaH eH W.1, ?_⟩
  apply PrimeRegularClassFunction.ext
  intro x
  have hx :
      PrimeRegularElement.map eH.symm.toMonoidHom
          (PrimeRegularElement.map N'.subtype x) =
        PrimeRegularElement.map N.subtype
          (PrimeRegularElement.map eN.symm.toMonoidHom x) := by
    apply Subtype.ext
    exact congrArg (fun f : N' →* H ↦ f x.1) hsquare
  change W.1.1
      (PrimeRegularElement.map eH.symm.toMonoidHom
        (PrimeRegularElement.map N'.subtype x)) = phiN'.1 x
  calc
    _ = W.1.1 (PrimeRegularElement.map N.subtype
          (PrimeRegularElement.map eN.symm.toMonoidHom x)) := by
      rw [hx]
    _ = phiN.1 (PrimeRegularElement.map eN.symm.toMonoidHom x) :=
      congrArg (fun f : PrimeRegularClassFunction K N p ↦
        f (PrimeRegularElement.map eN.symm.toMonoidHom x)) W.2
    _ = phiN'.1 x :=
      congrArg (fun f : PrimeRegularClassFunction K N' p ↦ f x) hphi

end Representation.Extension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
