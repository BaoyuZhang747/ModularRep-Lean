import ModularRep.PaperProofs.SporadicDefectZeroWeightFibreActual
import ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

/-!
# Literal trivial-radical normalisation for the Fischer construction

This module connects the sectorwise Fischer construction to the literal
defect-zero constructions already used for Lemma 5.2.  The reduction map is
selected by its uniqueness on prime regular elements and the weight at the
trivial radical subgroup is constructed from the literal local quotient.

The earlier conclusion-shaped premise about the corrected An--Dietrich map is
not needed.  Navarro's defect-zero block theorem supplies the independent E1
fact that the reduction is the only irreducible Brauer character in its block.
Since the sectorwise construction restricts to an equivalence on every block and
the constructed weight at the trivial subgroup belongs to that block, Lean
forces the desired normalisation.  The compatible-extension consequence then
uses the E2 Spath input.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual

open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

variable (IntermediateBlockEqualities CompatibleExtensions ModularCharacterTriple :
  IBr iota → WeightClass (p := p) (K := K) (X := X) → Prop)

variable {IntermediateBlockEqualities CompatibleExtensions ModularCharacterTriple}
variable {AD : AnDietrichSectorInput iota hinj blocks E1
  ModularCharacterTriple}

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Any equivalence between the literal fibres over a defect-zero block must
send its unique Brauer character to the constructed weight at the trivial
subgroup.  This is the map-independent kernel argument. -/
theorem blockEquiv_literal_qOne_normalisation
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
    (e :
      {phi : IBr iota //
        brauerBlock iota hinj blocks phi =
          brauerBlock iota hinj blocks (D.reduce (iota := iota) d)} ≃
      {w : WeightClass (p := p) (K := K) (X := X) //
        R.1.weightBlock w =
          brauerBlock iota hinj blocks (D.reduce (iota := iota) d)}) :
    (e ⟨D.reduce (iota := iota) d, rfl⟩).1 = T.atOne d := by
  let x : {phi : IBr iota //
      brauerBlock iota hinj blocks phi =
        brauerBlock iota hinj blocks (D.reduce (iota := iota) d)} :=
    ⟨D.reduce (iota := iota) d, rfl⟩
  let y : {w : WeightClass (p := p) (K := K) (X := X) //
      R.1.weightBlock w =
        brauerBlock iota hinj blocks (D.reduce (iota := iota) d)} :=
    ⟨T.atOne d, C.block_atOne d⟩
  have hpre : e.symm y = x := by
    apply Subtype.ext
    exact DefectZeroOrdinaryBlockSource.uniqueBrauer
      (iota := iota) (hinj := hinj) (blocks := blocks)
      D B d (e.symm y).1 (e.symm y).2
  have hxy : e x = y := by
    rw [← hpre, e.apply_symm_apply]
  exact congrArg Subtype.val hxy

/-- Block preservation and defect-zero block uniqueness force the literal
normalisation of the combined Fischer equivalence.  This is a kernel
deduction over the independent U/E1 block witness and the E2 An--Dietrich
block-fibre equivalence. -/
theorem assembled_literal_qOne_normalisation
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    AnDietrichSectorInput.assemble iota hinj blocks E1 AD
        (D.reduce (iota := iota) d) =
      T.atOne d := by
  let b := brauerBlock iota hinj blocks (D.reduce (iota := iota) d)
  let e := AnDietrichSectorInput.assembledBlockEquiv
    iota hinj blocks E1 AD b
  change (e ⟨D.reduce (iota := iota) d, rfl⟩).1 = T.atOne d
  exact blockEquiv_literal_qOne_normalisation
    (iota := iota) (hinj := hinj) (blocks := blocks)
    D T C B d e

/-- The combined partition assigns every canonical defect-zero reduction
to the literal class of the trivial radical subgroup.  This is a kernel
deduction over the same U/E1 and E2 inputs as the combined normalisation. -/
theorem assembled_literal_qOne_part
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    AnDietrichSectorInput.part iota hinj blocks E1 AD
        (D.reduce (iota := iota) d) =
      CharacterWeight.RadicalConjugacyClass.trivialClass
        T.trivialRadical := by
  calc
    AnDietrichSectorInput.part iota hinj blocks E1 AD
          (D.reduce (iota := iota) d) =
        CharacterWeight.radicalClass
          (AnDietrichSectorInput.assemble iota hinj blocks E1 AD
            (D.reduce (iota := iota) d)) := rfl
    _ = CharacterWeight.radicalClass (T.atOne d) :=
      congrArg CharacterWeight.radicalClass
        (assembled_literal_qOne_normalisation
          (iota := iota) (hinj := hinj) (blocks := blocks)
          (E1 := E1) (AD := AD) D T C B d)
    _ = CharacterWeight.RadicalConjugacyClass.trivialClass
          T.trivialRadical :=
      T.radicalClass_atOne d

/-- The E2 compatible-extension clause for the resulting map therefore
holds for the literal normalised pair.  This is L over E1 and E2. -/
theorem assembled_literal_qOne_compatibleExtensions
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X)
    (S : SpathLemma61Input iota hinj blocks E1
      IntermediateBlockEqualities CompatibleExtensions
      ModularCharacterTriple AD)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    CompatibleExtensions (D.reduce (iota := iota) d) (T.atOne d) := by
  rw [← assembled_literal_qOne_normalisation
    (iota := iota) (hinj := hinj) (blocks := blocks)
    (E1 := E1) (AD := AD) D T C B d]
  exact AnDietrichSectorInput.assembled_compatibleExtensions
    iota hinj blocks E1 AD S (D.reduce (iota := iota) d)

/-- Clause inventory for the Fischer construction with the literal
trivial-radical normalisation exposed.  It contains no iBAW conclusion. -/
structure Fi24AssembledClausesWithQOne
    (AD : AnDietrichSectorInput iota hinj blocks E1
      ModularCharacterTriple)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X) where
  base : Fi24AssembledClauses iota hinj blocks E1
    IntermediateBlockEqualities CompatibleExtensions
    ModularCharacterTriple AD
  qOneNormalisation : ∀ d :
      GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
    AnDietrichSectorInput.assemble iota hinj blocks E1 AD
        (D.reduce (iota := iota) d) =
      T.atOne d
  qOneCompatibleExtensions : ∀ d :
      GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
    CompatibleExtensions (D.reduce (iota := iota) d) (T.atOne d)

/-- Strongest honest Fischer construction after connecting Lemmas 5.2 and 5.6.
The normalisation is derived from independent E1 block facts. -/
def fi24_source_shaped_assembly_with_qOne
    (AD : AnDietrichSectorInput iota hinj blocks E1
      ModularCharacterTriple)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X)
    (S : SpathLemma61Input iota hinj blocks E1
      IntermediateBlockEqualities CompatibleExtensions
      ModularCharacterTriple AD)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D) :
    Fi24AssembledClausesWithQOne
      (IntermediateBlockEqualities := IntermediateBlockEqualities)
      (CompatibleExtensions := CompatibleExtensions)
      (ModularCharacterTriple := ModularCharacterTriple)
      iota hinj blocks E1 AD D T where
  base := fi24_source_shaped_assembly iota hinj blocks E1
    IntermediateBlockEqualities CompatibleExtensions
    ModularCharacterTriple AD S
  qOneNormalisation := assembled_literal_qOne_normalisation
    (iota := iota) (hinj := hinj) (blocks := blocks)
    (E1 := E1) (AD := AD) D T C B
  qOneCompatibleExtensions := assembled_literal_qOne_compatibleExtensions
    (iota := iota) (hinj := hinj) (blocks := blocks)
    (E1 := E1) (AD := AD) D T S C B

end ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
