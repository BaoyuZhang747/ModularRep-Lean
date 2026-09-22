import ModularRep.BlockIdempotentDecomposition
import ModularRep.BrauerCharacterSeparation

/-!
# Blocks of function-valued irreducible Brauer characters

A complete family of primitive central idempotents assigns a unique block
index to every simple group algebra module.  Under the explicit hypothesis
that Brauer characters distinguish simple-module classes, this file transports
that block index to the function-valued set `IBr`.  It then proves that every
Brauer character belongs to a unique block and identifies the corresponding
module and character fibres.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.FDRepSimpleClassKZero

universe u v w

variable {p : ℕ} {k G : Type u} {K : Type v} {ι : Type w}
variable [Field k] [Field K] [Group G] [Finite G] [Fintype ι]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

/-- The block index supporting a simple module class in a fixed complete
family of block idempotents. -/
noncomputable def simpleModuleClassBlock
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (X : SimpleModuleClass k[G]) : ι := by
  letI : IsSimpleModule k[G]
      (Representation.asModule (simpleClassFDRep X).ρ) :=
    simple_iff_isSimpleModule.mp (simpleClassFDRep_underlying_simple X)
  exact D.moduleBlock
    (V := Representation.asModule (simpleClassFDRep X).ρ)

/-- The simple module classes supported by one block idempotent. -/
def SimpleModuleClassBlock
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b) (i : ι) :=
  {X : SimpleModuleClass k[G] // simpleModuleClassBlock D X = i}

/-- Transport the block index of simple modules to function-valued
irreducible Brauer characters. -/
noncomputable def irreducibleBrauerCharacterBlock
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (phi : IBr iota) : ι :=
  simpleModuleClassBlock D ((simpleModuleClassEquivIBr iota hinj).symm phi)

@[simp]
theorem irreducibleBrauerCharacterBlock_simpleClassToIBr
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (X : SimpleModuleClass k[G]) :
    irreducibleBrauerCharacterBlock iota hinj D
        (simpleClassToIBr iota X) =
      simpleModuleClassBlock D X := by
  change simpleModuleClassBlock D
      ((simpleModuleClassEquivIBr iota hinj).symm
        ((simpleModuleClassEquivIBr iota hinj) X)) =
    simpleModuleClassBlock D X
  rw [Equiv.symm_apply_apply]

/-- The function-valued irreducible Brauer characters supported by one block
idempotent. -/
def IBrBlock
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b) (i : ι) :=
  {phi : IBr iota // irreducibleBrauerCharacterBlock iota hinj D phi = i}

/-- Every function-valued irreducible Brauer character belongs to a unique
block in the fixed block-idempotent decomposition. -/
theorem irreducibleBrauerCharacter_existsUnique_block
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (phi : IBr iota) :
    ∃! i : ι, irreducibleBrauerCharacterBlock iota hinj D phi = i := by
  exact ⟨irreducibleBrauerCharacterBlock iota hinj D phi, rfl,
    fun i hi ↦ hi.symm⟩

/-- The simple-module and irreducible Brauer character fibres belonging to a
fixed block are equivalent. -/
noncomputable def simpleModuleClassBlockEquivIBrBlock
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b) (i : ι) :
    SimpleModuleClassBlock D i ≃ IBrBlock iota hinj D i where
  toFun X :=
    ⟨simpleClassToIBr iota X.1, by
      rw [irreducibleBrauerCharacterBlock_simpleClassToIBr]
      exact X.2⟩
  invFun phi :=
    ⟨(simpleModuleClassEquivIBr iota hinj).symm phi.1, phi.2⟩
  left_inv X := by
    apply Subtype.ext
    exact (simpleModuleClassEquivIBr iota hinj).symm_apply_apply X.1
  right_inv phi := by
    apply Subtype.ext
    exact (simpleModuleClassEquivIBr iota hinj).apply_symm_apply phi.1

/-- Every function-valued irreducible Brauer character block is finite. -/
noncomputable instance finiteIBrBlock
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (i : ι) : Finite (IBrBlock iota hinj D i) :=
  finiteIBrSubtype iota _

end ModularRep.FDRepSimpleClassKZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
