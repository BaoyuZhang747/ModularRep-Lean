import ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
import ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport

/-!
# The actual automorphism group of a routed principal family

The routed carrier supplies a character in the SAME family block whose
values are one. The existing family Brauer-block action therefore fixes
that block under every automorphism. The existing Definition 3.5 adapter
then identifies its Gamma with the full actual automorphism group, with
value exactly the family's original gamma homomorphism.

Composing with conjugation by the carrier's actual Sp group equivalence
gives the literal symplectic automorphism coordinates. All declarations
are K. No block fixedness, faithfulness, surjectivity, action matching,
weight map, compatible-root square or relation is an additional input.
This uses FAMILY blocks, not an assumed equality with the operations'
ambient catalogue. Their separately recorded primitive binding is not
needed for this group-action calculation.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalFamilyAutomorphisms

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport

universe u

variable (family : Definition35Family.{u} 2) (block : family.Block)
variable {rank : ℕ} {F : Type u} [Field F] [Fintype F]
variable (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F)

/-- Actual constant-one class-function values imply full automorphism
fixedness of the underlying family Brauer character. -/
theorem principalCharacter_fixed (alpha : (MulAut family.H)ᵐᵒᵖ) :
    @HSMul.hSMul (MulAut family.H)ᵐᵒᵖ (IBr family.iota) (IBr family.iota)
      inferInstance alpha carrier.principalCharacter.1 =
      (carrier.principalCharacter.1 : IBr family.iota) := by
  apply Subtype.ext
  ext x
  change carrier.principalCharacter.1.1 _ = carrier.principalCharacter.1.1 x
  exact (carrier.principalCharacter_value_one _).trans
    (carrier.principalCharacter_value_one x).symm

include carrier in
/-- The block is fixed using its actual family decomposition and the
membership of the same constant-one character. -/
theorem principalBlock_fixed (alpha : (MulAut family.H)ᵐᵒᵖ) :
    alpha • block = block := by
  calc
    alpha • block = alpha • irreducibleBrauerCharacterBlock family.iota
        family.irreducibleBrauerInjective family.blocks
        carrier.principalCharacter.1 :=
      congrArg (fun b : family.Block => alpha • b) carrier.principalCharacter.2.symm
    _ = irreducibleBrauerCharacterBlock family.iota
        family.irreducibleBrauerInjective family.blocks
        (@HSMul.hSMul (MulAut family.H)ᵐᵒᵖ (IBr family.iota) (IBr family.iota)
          inferInstance alpha carrier.principalCharacter.1) :=
      (family.brauerBlock_transport alpha carrier.principalCharacter.1).symm
    _ = irreducibleBrauerCharacterBlock family.iota
        family.irreducibleBrauerInjective family.blocks
        carrier.principalCharacter.1 := by
      rw [principalCharacter_fixed family block carrier]
    _ = block := carrier.principalCharacter.2

private def fullAutomorphismEquiv (P : Definition35Problem.{u})
    (adapter : Definition35AutomorphismStabilizerAdapter P)
    (fixed : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, alpha • P.block = P.block) :
    P.Gamma ≃* MulAut P.H where
  toFun := P.gamma
  invFun alpha := adapter.equiv.symm
    ⟨MulOpposite.op alpha⁻¹, fixed (MulOpposite.op alpha⁻¹)⟩
  left_inv a := by
    apply adapter.equiv.injective
    apply Subtype.ext
    calc
      (adapter.equiv (adapter.equiv.symm
          ⟨MulOpposite.op (P.gamma a)⁻¹, fixed _⟩)).1 =
          MulOpposite.op (P.gamma a)⁻¹ :=
        congrArg Subtype.val (adapter.equiv.apply_symm_apply _)
      _ = (adapter.equiv a).1 := by
        have h := (adapter.equiv_coe a).symm
        change MulOpposite.op (P.gamma a⁻¹) =
          (adapter.equiv a).1 at h
        simpa only [map_inv] using h
  right_inv alpha := by
    let z : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ P.block :=
      ⟨MulOpposite.op alpha⁻¹, fixed _⟩
    have h := (adapter.equiv_coe (adapter.equiv.symm z)).symm.trans
      (congrArg Subtype.val (adapter.equiv.apply_symm_apply z))
    change MulOpposite.op
        (P.gamma (adapter.equiv.symm z)⁻¹) =
      MulOpposite.op alpha⁻¹ at h
    rw [map_inv] at h
    exact inv_injective (MulOpposite.op_injective h)
  map_mul' := P.gamma.map_mul

variable (adapter : Definition35AutomorphismStabilizerAdapter (family.problem block))

/-- The inverse/op map from the supplied actual block stabilizer adapter
has value exactly gamma. Its inverse uses the K principal-block fixedness. -/
def familyAutEquiv :
    (family.automorphisms block).Gamma ≃* MulAut family.H :=
  fullAutomorphismEquiv (family.problem block) adapter
    (principalBlock_fixed family block carrier)

@[simp] theorem familyAutEquiv_apply (a : (family.automorphisms block).Gamma) :
    familyAutEquiv family block carrier adapter a =
      (family.automorphisms block).gamma a := rfl

/-- The computed inverse is an actual inverse to the original gamma. -/
@[simp] theorem familyAutEquiv_symm_gamma (alpha : MulAut family.H) :
    (family.automorphisms block).gamma
        ((familyAutEquiv family block carrier adapter).symm alpha) = alpha :=
  (familyAutEquiv family block carrier adapter).apply_symm_apply alpha

include carrier adapter in
/-- Faithfulness and surjectivity are consequences of the fixed adapter;
they are not new source requirements on the family action. -/
theorem familyGamma_bijective :
    Function.Bijective (family.automorphisms block).gamma :=
  (familyAutEquiv family block carrier adapter).bijective

/-- The literal Sp automorphism equivalence uses the SAME group
equivalence supplied by the routed carrier. -/
def symplecticAutEquiv :
    (family.automorphisms block).Gamma ≃*
      MulAut (Matrix.symplecticGroup (Fin rank) F) :=
  (familyAutEquiv family block carrier adapter).trans
    (MulAut.congr carrier.symplecticEquiv)

@[simp] theorem symplecticAutEquiv_apply (a : (family.automorphisms block).Gamma) :
    symplecticAutEquiv family block carrier adapter a =
      MulAut.congr carrier.symplecticEquiv ((family.automorphisms block).gamma a) := rfl

/-- The actual action square, on every element of the original group. -/
theorem symplecticAutEquiv_apply_image
    (a : (family.automorphisms block).Gamma) (x : family.H) :
    symplecticAutEquiv family block carrier adapter a (carrier.symplecticEquiv x) =
      carrier.symplecticEquiv ((family.automorphisms block).gamma a x) := by
  change carrier.symplecticEquiv ((family.automorphisms block).gamma a
    (carrier.symplecticEquiv.symm (carrier.symplecticEquiv x))) = _
  exact congrArg carrier.symplecticEquiv
    (congrArg ((family.automorphisms block).gamma a)
      (carrier.symplecticEquiv.symm_apply_apply x))

/-- The reverse acting-group map has the corresponding actual square. -/
theorem symplecticAutEquiv_symm_coordinates
    (alpha : MulAut (Matrix.symplecticGroup (Fin rank) F)) (x : family.H) :
    carrier.symplecticEquiv ((family.automorphisms block).gamma
        ((symplecticAutEquiv family block carrier adapter).symm alpha) x) =
      alpha (carrier.symplecticEquiv x) := by
  have h := symplecticAutEquiv_apply_image family block carrier adapter
    ((symplecticAutEquiv family block carrier adapter).symm alpha) x
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

/-- The inverse/op convention in the canonical character and weight
actions commutes with precisely the same group coordinates. -/
theorem symplecticAutEquiv_inverseOp_coordinates
    (a : (family.automorphisms block).Gamma) (x : family.H) :
    carrier.symplecticEquiv
        ((inverseOpHom (family.automorphisms block).gamma a).unop x) =
      (inverseOpHom (MonoidHom.id
        (MulAut (Matrix.symplecticGroup (Fin rank) F)))
        (symplecticAutEquiv family block carrier adapter a)).unop
          (carrier.symplecticEquiv x) := by
  change carrier.symplecticEquiv ((family.automorphisms block).gamma a⁻¹ x) =
    (symplecticAutEquiv family block carrier adapter a)⁻¹ (carrier.symplecticEquiv x)
  have h := symplecticAutEquiv_apply_image family block carrier adapter a⁻¹ x
  simpa only [map_inv] using h.symm

end ModularRep.PaperProofs.OddTwoPrincipalFamilyAutomorphisms


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
