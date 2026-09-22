import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual

/-!
# Defect-zero weight fibres on the literal carriers

This module isolates the block-theoretic input needed to identify the entire
weight fibre of a defect-zero block.  Its import boundary deliberately excludes
the An--Dietrich sector equivalences and every combined character--weight map.

This module introduces two explicit representation theoretic source
boundaries. `DefectZeroOrdinaryBlockSource` records the selected ordinary
block, its literal reduction-block equality, and the singleton Brauer fibre.
`DefectZeroWeightSubgroupSource` records that a raw weight inducing to that
defect-zero block has trivial radical subgroup. For a weight `(Q, theta)`, the
latter follows from `Q = O_p(N_X(Q))`, Navarro's theorem that the `p`-core lies
in every defect group of the local block, and containment of a defect group of
an inducing block in a defect group of the induced block. Conditional on
upstream D/T/C and these B/Z records, the remaining radical, uniqueness,
subsingleton, and equivalence statements are kernel deductions.
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

/-- Function-valued defect-zero ordinary characters from the literal
Lemma 5.2 construction. -/
abbrev GlobalDefectZeroCharacter :=
  SporadicCompleteCollapseLemma52Actual.GlobalDefectZeroCharacter
    (p := p) (K := K) (X := X)

/-- The exact source selecting the unique Brauer reduction on prime regular
elements. -/
abbrev DefectZeroReductionSource
    (iota : PrimeRegularRootEmbedding p k K X) :=
  SporadicCompleteCollapseLemma52Actual.DefectZeroReductionSource
    (p := p) (K := K) (X := X) iota

/-- The exact source constructing the weight at the trivial radical
subgroup. -/
abbrev TrivialWeightSource (p : ℕ) (X : Type u) [Group X] :=
  SporadicCompleteCollapseLemma52Actual.TrivialWeightSource
    (p := p) (X := X)

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable {R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X)}

/-- Literal block compatibility for the constructed weight at the trivial
subgroup. -/
abbrev TrivialWeightBlockCompatibility
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X) :=
  SporadicCompleteCollapseLemma52Actual.TrivialWeightBlockCompatibility
    iota hinj blocks R D T

/-- Source-shaped interface for the ordinary defect-zero block.  Navarro's
defect-zero block theorem supplies the singleton Brauer fibre.  The fields do
not mention a character--weight map. -/
structure DefectZeroOrdinaryBlockSource
    (D : DefectZeroReductionSource iota) where
  ordinaryBlock :
    GlobalDefectZeroCharacter (p := p) (K := K) (X := X) →
      ActualBlock (k := k) (X := X)
  reduction_block : ∀
      d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
    brauerBlock iota hinj blocks (D.reduce (iota := iota) d) =
      ordinaryBlock d
  brauerFibre_subsingleton : ∀
      d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
    Subsingleton
      {phi : IBr iota //
        brauerBlock iota hinj blocks phi = ordinaryBlock d}

namespace DefectZeroOrdinaryBlockSource

/-- The singleton fibre and the literal block identification force uniqueness
in the block of the selected reduction. -/
theorem uniqueBrauer
    (D : DefectZeroReductionSource iota)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
    (phi : IBr iota)
    (hphi : brauerBlock iota hinj blocks phi =
      brauerBlock iota hinj blocks (D.reduce (iota := iota) d)) :
    phi = D.reduce (iota := iota) d := by
  let x : {psi : IBr iota //
      brauerBlock iota hinj blocks psi = B.ordinaryBlock d} :=
    ⟨phi, hphi.trans (B.reduction_block d)⟩
  let y : {psi : IBr iota //
      brauerBlock iota hinj blocks psi = B.ordinaryBlock d} :=
    ⟨D.reduce (iota := iota) d, B.reduction_block d⟩
  exact congrArg Subtype.val
    (@Subsingleton.elim _ (B.brauerFibre_subsingleton d) x y)

end DefectZeroOrdinaryBlockSource

/-- The sole additional block-theoretic source fact.  If the induced block of
a raw weight is the block of a defect-zero reduction, then its radical
subgroup is trivial. -/
structure DefectZeroWeightSubgroupSource
    (D : DefectZeroReductionSource iota) : Prop where
  subgroup_eq_bot_of_block_eq : ∀
      (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
      (W : CharacterWeight p K X),
    R.1.operations.rawWeightBlock W =
        brauerBlock iota hinj blocks (D.reduce (iota := iota) d) →
      W.subgroup = ⊥

/-- Every weight in the block of a defect-zero reduction has the trivial
radical class. -/
theorem radicalClass_eq_trivial_of_mem_defectZeroBlock
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X)
    (Z : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X))
    (hw : R.1.weightBlock w =
      brauerBlock iota hinj blocks (D.reduce (iota := iota) d)) :
    CharacterWeight.radicalClass w =
      CharacterWeight.RadicalConjugacyClass.trivialClass T.trivialRadical := by
  refine Quotient.inductionOn w ?_ hw
  intro w0 hw0
  refine Quotient.inductionOn w0 ?_ hw0
  intro W hW
  have hQ : W.subgroup = ⊥ := Z.subgroup_eq_bot_of_block_eq d W (by
    simpa only [CharacterWeight.LocalBlockInductionSource.weightBlock_mk]
      using hW)
  rw [CharacterWeight.radicalClass_mk]
  exact congrArg
    (fun Q : CharacterWeight.RadicalSubgroup (p := p) (G := X) =>
      (Quotient.mk'' Q :
        CharacterWeight.RadicalConjugacyClass (p := p) (G := X)))
    (Subtype.ext hQ)

/-- Every weight in the block of a defect-zero reduction is the constructed
weight at the trivial subgroup. -/
theorem weight_eq_atOne_of_mem_defectZeroBlock
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (Z : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X))
    (hw : R.1.weightBlock w =
      brauerBlock iota hinj blocks (D.reduce (iota := iota) d)) :
    w = T.atOne d := by
  obtain ⟨d', hd'⟩ := T.exists_atOne_of_radicalClass_eq_trivial w
    (radicalClass_eq_trivial_of_mem_defectZeroBlock
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R)
      D T Z d w hw)
  have hblock :
      brauerBlock iota hinj blocks (D.reduce (iota := iota) d') =
        brauerBlock iota hinj blocks (D.reduce (iota := iota) d) := by
    calc
      brauerBlock iota hinj blocks (D.reduce (iota := iota) d') =
          R.1.weightBlock (T.atOne d') := (C.block_atOne d').symm
      _ = R.1.weightBlock w := congrArg R.1.weightBlock hd'
      _ = brauerBlock iota hinj blocks (D.reduce (iota := iota) d) := hw
  have hreduce : D.reduce (iota := iota) d' =
      D.reduce (iota := iota) d :=
    DefectZeroOrdinaryBlockSource.uniqueBrauer
      (iota := iota) (hinj := hinj) (blocks := blocks)
      D B d (D.reduce (iota := iota) d') hblock
  have hdd : d' = d := D.reduce_injective (iota := iota) hreduce
  exact hd'.symm.trans (congrArg T.atOne hdd)

/-- The entire weight fibre of a defect-zero block is a singleton. -/
theorem defectZeroWeightFibre_subsingleton
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (Z : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    Subsingleton
      {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X) //
        R.1.weightBlock w =
          brauerBlock iota hinj blocks (D.reduce (iota := iota) d)} := by
  constructor
  intro w w'
  apply Subtype.ext
  exact (weight_eq_atOne_of_mem_defectZeroBlock
    (iota := iota) (hinj := hinj) (blocks := blocks) (R := R)
    D T C B Z d w.1 w.2).trans
      (weight_eq_atOne_of_mem_defectZeroBlock
        (iota := iota) (hinj := hinj) (blocks := blocks) (R := R)
        D T C B Z d w'.1 w'.2).symm

/-- The Brauer-character fibre of a defect-zero block is a singleton. -/
theorem defectZeroBrauerFibre_subsingleton
    (D : DefectZeroReductionSource iota)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    Subsingleton
      {phi : IBr iota //
        brauerBlock iota hinj blocks phi =
          brauerBlock iota hinj blocks (D.reduce (iota := iota) d)} := by
  constructor
  intro phi psi
  apply Subtype.ext
  exact (DefectZeroOrdinaryBlockSource.uniqueBrauer
    (iota := iota) (hinj := hinj) (blocks := blocks)
    D B d phi.1 phi.2).trans
      (DefectZeroOrdinaryBlockSource.uniqueBrauer
        (iota := iota) (hinj := hinj) (blocks := blocks)
        D B d psi.1 psi.2).symm

/-- The canonical equivalence between the complete Brauer and weight fibres
of a defect-zero block. -/
def defectZeroBlockFibreEquiv
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (Z : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    {phi : IBr iota //
      brauerBlock iota hinj blocks phi =
        brauerBlock iota hinj blocks (D.reduce (iota := iota) d)} ≃
    {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X) //
      R.1.weightBlock w =
        brauerBlock iota hinj blocks (D.reduce (iota := iota) d)} where
  toFun _ := ⟨T.atOne d, C.block_atOne d⟩
  invFun _ := ⟨D.reduce (iota := iota) d, rfl⟩
  left_inv phi := by
    apply Subtype.ext
    exact (DefectZeroOrdinaryBlockSource.uniqueBrauer
      (iota := iota) (hinj := hinj) (blocks := blocks)
      D B d phi.1 phi.2).symm
  right_inv w := by
    apply Subtype.ext
    exact (weight_eq_atOne_of_mem_defectZeroBlock
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R)
      D T C B Z d w.1 w.2).symm

end ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
