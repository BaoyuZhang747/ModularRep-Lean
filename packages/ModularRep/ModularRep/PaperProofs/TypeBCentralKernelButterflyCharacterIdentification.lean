import ModularRep.PaperProofs.TypeBCentralKernelButterflyCertificate
import ModularRep.PaperProofs.TypeBCentralKernelTripleRootFamily
import ModularRep.IrreducibleBrauerCharacterEquiv

/-!
# Literal character and specified-block identification under a group equivalence

The group algebra image of a supporting primitive block supports the actual
pulled-back irreducible representation. Consequently independently presented
specified block catalogues select the same primitive block. The Butterfly
character-identification guard is therefore a deduction from the actual
character pullback and root-lift equations, not a new source input.

The full lift equality used below is proved for the canonical transported
roots. It is not inferred from an arbitrary agreement on a smaller root
domain. No published-result certificate or target-side triple is assumed.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCentralKernelButterflyCharacterIdentification

open ModularRep TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelTripleCertificate TypeBCentralKernelButterflyCertificate

universe u

variable {p : ℕ} {k K X Y : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group X] [Finite X] [Group Y] [Finite Y]

/-- Actual module support transports through the same group-basis map. -/
theorem supported_along_of_lift_eq (e : X ≃* Y)
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (b : LiteralPrimitiveBlock k X) (thetaX : IBr iotaX) (thetaY : IBr iotaY)
    (lifts : iotaY.lift = iotaX.lift)
    (values : thetaY.val = PrimeRegularClassFunction.pullback e.symm.toMonoidHom thetaX.val)
    (support : Supported iotaX b thetaX) :
    Supported iotaY (blockAlong e b) thetaY := by
  obtain ⟨V, hV, hchar, hsupp⟩ := support
  refine ⟨FDRep.of (Representation.pullback V.ρ e.symm.toMonoidHom),
    hV.pullback e.symm.toMonoidHom e.symm.surjective, ?_, ?_⟩
  · change thetaY.val = Representation.brauerCharacterOfRootEmbedding
      (Representation.pullback V.ρ e.symm.toMonoidHom) iotaY
    exact values.trans
      ((congrArg (PrimeRegularClassFunction.pullback e.symm.toMonoidHom) hchar).trans
        (Representation.brauerCharacterOfRootEmbedding_pullback_of_lift_eq
          V.ρ iotaX iotaY e.symm.toMonoidHom lifts).symm)
  · change (Representation.pullback V.ρ e.symm.toMonoidHom).asAlgebraHom
      (MonoidAlgebra.domCongr k k e b.val) = 1
    rw [Representation.pullback_asAlgebraHom_domCongr_apply]
    exact hsupp

/-- A specified catalogue's selected block supports the actual character. -/
theorem supported_characterBlock (D : CharacterData p k K X) (theta : IBr D.iota) :
    Supported D.iota (D.block theta) theta := by
  letI := D.blocks.blockFintype
  exact (supported_iff_block D.iota D.blocks.decomposition (D.block theta) theta).mpr rfl

/-- The specified primitive-block equality does not depend on how the two
complete catalogues were presented. -/
theorem blockAlong_eq_of_lift_eq (e : X ≃* Y)
    (DX : CharacterData p k K X) (DY : CharacterData p k K Y)
    (thetaX : IBr DX.iota) (thetaY : IBr DY.iota)
    (lifts : DY.iota.lift = DX.iota.lift)
    (values : thetaY.val = PrimeRegularClassFunction.pullback e.symm.toMonoidHom thetaX.val) :
    blockAlong e (DX.block thetaX) = DY.block thetaY := by
  have support := supported_along_of_lift_eq e DX.iota DY.iota
    (DX.block thetaX) thetaX thetaY lifts values (supported_characterBlock DX thetaX)
  letI := DY.blocks.blockFintype
  exact ((supported_iff_block DY.iota DY.blocks.decomposition
    (blockAlong e (DX.block thetaX)) thetaY).mp support).symm

/-- Construct every literal Butterfly character-identification guard from
the actual pullback equation and equal field-level lift functions. -/
theorem of_lift_eq (e : X ≃* Y)
    (DX : CharacterData p k K X) (DY : CharacterData p k K Y)
    (thetaX : IBr DX.iota) (thetaY : IBr DY.iota)
    (lifts : DY.iota.lift = DX.iota.lift)
    (values : thetaY.val = PrimeRegularClassFunction.pullback e.symm.toMonoidHom thetaX.val) :
    CharacterIdentification e DX DY thetaX thetaY := by
  refine ⟨?_, ?_, blockAlong_eq_of_lift_eq e DX DY thetaX thetaY lifts values⟩
  · intro z
    exact (congrFun lifts ((z : kˣ) : k)).symm
  · intro x
    rw [values]
    change thetaX.val x = thetaX.val
      (PrimeRegularElement.map e.symm.toMonoidHom (PrimeRegularElement.map e.toMonoidHom x))
    congr 1
    apply Subtype.ext
    exact (e.symm_apply_apply x.val).symm

/-- In the canonical transport, both identifying equations are constructed;
only the actual target specified catalogue is supplied. -/
theorem alongMulEquiv (DX : CharacterData p k K X) (e : X ≃* Y)
    (blocksY : PhysicalBlocks k Y) (thetaX : IBr DX.iota) :
    CharacterIdentification e DX
      (TypeBCentralKernelTripleRootFamily.characterData (DX.iota.alongMulEquiv e) blocksY)
      thetaX (IrreducibleBrauerCharacter.equivAlongMulEquiv DX.iota e thetaX) := by
  apply of_lift_eq e DX
    (TypeBCentralKernelTripleRootFamily.characterData (DX.iota.alongMulEquiv e) blocksY)
    thetaX (IrreducibleBrauerCharacter.equivAlongMulEquiv DX.iota e thetaX)
  · exact funext (DX.iota.alongMulEquiv_lift e)
  · rfl

end ModularRep.PaperProofs.TypeBCentralKernelButterflyCharacterIdentification


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
