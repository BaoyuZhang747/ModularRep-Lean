import ModularRep.BlockIdempotentInCenter

/-!
# Block central characters

For a finite group over an algebraically closed field, Navarro's Theorem
(3.11) identifies the blocks with the algebra homomorphisms from the centre
of the group algebra to the coefficient field.  This file gives that standard
block theoretic input a source shaped interface attached to an already fixed
complete family of primitive block idempotents.

The catalogue records exactly two facts from the theorem.  A block central
character takes value one on its own block idempotent and zero on every other
block idempotent, and every algebra homomorphism from the centre occurs in
this way.  Injectivity, uniqueness, and the resulting equivalence are then
proved in the kernel.

No assertion of the false form `z * e = lambda z * e` is made.  In modular
block theory that scalar identity is valid only after passage to the relevant
residue field, or equivalently modulo the local radical.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

/-- The standard block central characters attached to a specified complete
primitive block idempotent decomposition.

The two delta fields and `exhaustive` are the precise external block
theoretic content of Navarro, Theorem (3.11).  The remaining results in this
file are deduced from them. -/
structure BlockCentralCharacterCatalogue
    {k G Block : Type*} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Fintype Block] {blockIdempotent : Block → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent) where
  /-- The central algebra homomorphism belonging to a block. -/
  centralCharacter : Block → GroupAlgebraCenter k G →ₐ[k] k
  /-- A block central character takes value one on its own block
  idempotent. -/
  delta_own : ∀ B,
    centralCharacter B (blocks.blockIdempotentInCenter B) = 1
  /-- A block central character vanishes on every other block idempotent. -/
  delta_other : ∀ B C, B ≠ C →
    centralCharacter B (blocks.blockIdempotentInCenter C) = 0
  /-- Every algebra homomorphism from the centre of the group algebra to the
  coefficient field is the central character of a block. -/
  exhaustive : Function.Surjective centralCharacter

namespace BlockCentralCharacterCatalogue

variable {k G Block : Type*} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
variable [Fintype Block] {blockIdempotent : Block → k[G]}
variable {blocks : BlockIdempotentDecomposition blockIdempotent}

/-- A block central character takes value one on its own idempotent. -/
@[simp]
theorem centralCharacter_own
    (catalogue : BlockCentralCharacterCatalogue blocks) (B : Block) :
    catalogue.centralCharacter B (blocks.blockIdempotentInCenter B) = 1 :=
  catalogue.delta_own B

/-- A block central character vanishes on every other block idempotent. -/
theorem centralCharacter_other
    (catalogue : BlockCentralCharacterCatalogue blocks) {B C : Block}
    (hne : B ≠ C) :
    catalogue.centralCharacter B (blocks.blockIdempotentInCenter C) = 0 :=
  catalogue.delta_other B C hne

/-- Distinct blocks have distinct central characters.  This is derived from
the delta law, rather than included as a source field. -/
theorem centralCharacter_injective
    (catalogue : BlockCentralCharacterCatalogue blocks) :
    Function.Injective catalogue.centralCharacter := by
  intro B C hcharacter
  by_contra hne
  have hevaluation := congrArg
    (fun lambda : GroupAlgebraCenter k G →ₐ[k] k ↦
      lambda (blocks.blockIdempotentInCenter B)) hcharacter
  have hCB : C ≠ B := Ne.symm hne
  rw [catalogue.centralCharacter_own,
    catalogue.centralCharacter_other hCB] at hevaluation
  exact one_ne_zero hevaluation

/-- The block central character family is bijective. -/
theorem centralCharacter_bijective
    (catalogue : BlockCentralCharacterCatalogue blocks) :
    Function.Bijective catalogue.centralCharacter :=
  ⟨catalogue.centralCharacter_injective, catalogue.exhaustive⟩

/-- Blocks are equivalent to the algebra homomorphisms from the centre of
the group algebra to the coefficient field. -/
noncomputable def centralCharacterEquiv
    (catalogue : BlockCentralCharacterCatalogue blocks) :
    Block ≃ (GroupAlgebraCenter k G →ₐ[k] k) :=
  Equiv.ofBijective catalogue.centralCharacter
    catalogue.centralCharacter_bijective

/-- The equivalence sends a block to its supplied central character. -/
@[simp]
theorem centralCharacterEquiv_apply
    (catalogue : BlockCentralCharacterCatalogue blocks) (B : Block) :
    catalogue.centralCharacterEquiv B = catalogue.centralCharacter B :=
  rfl

/-- Every central algebra homomorphism belongs to a unique block. -/
theorem existsUnique_centralCharacter_eq
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (lambda : GroupAlgebraCenter k G →ₐ[k] k) :
    ∃! B, catalogue.centralCharacter B = lambda := by
  obtain ⟨B, hB⟩ := catalogue.exhaustive lambda
  refine ⟨B, hB, ?_⟩
  intro C hC
  exact catalogue.centralCharacter_injective (hC.trans hB.symm)

end BlockCentralCharacterCatalogue

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
