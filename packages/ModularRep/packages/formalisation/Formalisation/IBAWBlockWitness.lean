import Formalisation.IBAWAssembly

/-!
# Blockwise witnesses and aggregation

A `BlockWitness` is the set-theoretic and compatibility datum attached to one
block.  It is intentionally not called the inductive BAW condition: the
manuscript's passage from the quotient by a central character kernel to such a
witness is an external character-theoretic theorem.

This file proves that global iBAW data restrict to block witnesses and that a
coherent family of block witnesses combines back into global data.
-/

namespace Formalisation.IBAW

variable {A B R S X Y DZ : Type*} [Group A]
  [MulAction A B] [MulAction A R] [MulAction A S]
  [MulAction A X] [MulAction A Y] [MulAction A DZ]

variable {C : Context A B R S X Y DZ}

/-- The complete witness on one block, equivariant under the stabiliser of
that block. -/
structure BlockWitness (C : Context A B R S X Y DZ) (b : B) where
  equiv : Fibre C.brauerBlock b ≃ Fibre C.weightBlock b
  stabilizer_equivariant : ∀ (a : A) (ha : a • b = b)
    (x : Fibre C.brauerBlock b),
    equiv (stabilizerFibreEquiv C.brauerBlock
        C.brauerBlock_equivariant b a ha x) =
      stabilizerFibreEquiv C.weightBlock
        C.weightBlock_equivariant b a ha (equiv x)
  intermediateBlockEqualities : ∀ x : Fibre C.brauerBlock b,
    C.intermediateBlockEqualitiesOK x (equiv x)
  extensions : ∀ x : Fibre C.brauerBlock b,
    C.extensionsOK x (equiv x)
  characterTriple : ∀ x : Fibre C.brauerBlock b,
    C.characterTripleOK x (equiv x)
  normalisation : ∀ (d : DZ) (hd : C.brauerBlock (C.reduce d) = b),
    equiv ⟨C.reduce d, hd⟩ =
      ⟨C.atOne d, (C.atOne_block d).trans hd⟩

namespace BlockWitness

variable {b : B} (W : BlockWitness C b)

/-- The radical part inside a block is again derived from the local image. -/
def part (x : Fibre C.brauerBlock b) : R :=
  C.weightRadical (W.equiv x)

/-- Local restriction inside a fixed block. -/
def localEquiv (r : R) :
    {x : Fibre C.brauerBlock b // W.part x = r} ≃
      {y : Fibre C.weightBlock b // C.weightRadical y = r} where
  toFun x := ⟨W.equiv x, x.property⟩
  invFun y := ⟨W.equiv.symm y, by simpa [part] using y.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (W.equiv.symm_apply_apply (x : Fibre C.brauerBlock b))
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (W.equiv.apply_symm_apply (y : Fibre C.weightBlock b))

end BlockWitness

/-- Restrict global data to one block. -/
def Data.toBlockWitness (D : Data C) (b : B) : BlockWitness C b where
  equiv := D.blockEquiv b
  stabilizer_equivariant a ha x := by
    apply Subtype.ext
    change D.equiv (a • (x : X)) = a • D.equiv x
    exact D.equiv_equivariant a x
  intermediateBlockEqualities x := D.intermediateBlockEqualities x
  extensions x := D.extensions x
  characterTriple x := D.characterTriple x
  normalisation d hd := by
    apply Subtype.ext
    exact D.normalisation d

/-- Cross-block naturality needed to combine block witnesses.  Stabiliser
equivariance is its special case when `a • b = b`. -/
def BlockWitnessFamilyEquivariant (W : ∀ b : B, BlockWitness C b) : Prop :=
  ∀ (a : A) (b : B) (x : Fibre C.brauerBlock b),
    (W (a • b)).equiv
        (actFibre C.brauerBlock C.brauerBlock_equivariant a b x) =
      actFibre C.weightBlock C.weightBlock_equivariant a b ((W b).equiv x)

/-- The block witnesses obtained by restricting global data are coherent
across the entire automorphism action. -/
theorem Data.blockWitnessFamilyEquivariant (D : Data C) :
    BlockWitnessFamilyEquivariant (D.toBlockWitness : ∀ b, BlockWitness C b) := by
  intro a b x
  apply Subtype.ext
  change D.equiv (a • (x : X)) = a • D.equiv x
  exact D.equiv_equivariant a x

/-- A coherent blockwise family gives the fibre data required for global
construction. -/
def equivariantFibresOfBlockWitnesses
    (W : ∀ b : B, BlockWitness C b)
    (hW : BlockWitnessFamilyEquivariant W) :
    EquivariantFibreEquiv C.brauerBlock C.weightBlock
      C.brauerBlock_equivariant C.weightBlock_equivariant where
  fibreEquiv := fun b => (W b).equiv
  map_actFibre := hW

/-- Coherent witnesses for all blocks combine into global iBAW data.  This
is the pure aggregation step; producing the witnesses from the blockwise
inductive condition remains external. -/
def dataOfBlockWitnesses
    (W : ∀ b : B, BlockWitness C b)
    (hW : BlockWitnessFamilyEquivariant W) : Data C := by
  let F := equivariantFibresOfBlockWitnesses W hW
  apply dataOfBlockFibres F
  · exact fun b x => (W b).intermediateBlockEqualities x
  · exact fun b x => (W b).extensions x
  · exact fun b x => (W b).characterTriple x
  · intro d
    rw [EquivariantFibreEquiv.assemble_apply]
    have h := (W (C.brauerBlock (C.reduce d))).normalisation d rfl
    exact congrArg Subtype.val h

end Formalisation.IBAW


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
