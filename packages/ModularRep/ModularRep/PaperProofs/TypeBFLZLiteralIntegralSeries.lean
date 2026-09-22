import ModularRep.PaperProofs.TypeBFLZBlockUnionSplitting
import ModularRep.PaperProofs.TypeBOrdinaryBlockSplitting

/-!
# FLZ integral series on the literal full ordinary and Brauer unions

The Brauer union is defined through an actual ordinary member of the full
Broue--Michel union and equality of their specified primitive blocks. The
checked full-union certificate and ordinary-block surjectivity identify
this literal carrier with the existing Brauer-index fibre.

The only new E2 input is one-way FLZ Theorem 2.3 on the individual literal
rational series and these actual Brauer unions, with the SAME stable
decomposition equation. Reindexing constructs the old per-series packet.
No global basic-set map or ordinary/Brauer set matching is an input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBFLZLiteralIntegralSeries

open ModularRep OrdinaryIrreducibleCharacter
open DecompositionBasicSetBridge ExactGrothendieckGroup FDRepSimpleClassKZero
open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBFLZLabelSource (UnipotentPredicate FullCharacterPair AdmissibleParameter
  BlockPair SourceIndex)
open TypeBFLZLabelSplittingSource TypeBFLZBlockUnionSplitting
open TypeBRationalSeriesBasicSet
open TypeBIntegralSeriesSplitting (brauerIndex IntegralSeriesData Theorem23Hypotheses)

universe u

variable {p ell n : ℕ} {F K O k : Type u}
variable [Field F] [Finite F] [CharP F p] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable [Fintype (SourceIndex F p ell n)]
variable [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable (Msys : ModularSystem ell K O k)
variable (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {unipotent : UnipotentPredicate F K p n}
variable [MulAction (CSp F n) (FullCharacterPair F K p n unipotent)]
variable (S : Equation34Source (ell := ell) unipotent)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.val))
variable (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
  Msys iota hinj blocks (ordinaryRoots := S.ordinary_roots))

/-- The actual Brauer characters in the full union of specified blocks:
their block contains an ordinary character in the literal ordinary union. -/
def brauerUnion (i : SourceIndex F p ell n) (phi : IBr iota) : Prop :=
  ∃ chi : Irr K (SpecialClifford n F), indexedOrdinaryUnion S i chi ∧
    (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock chi =
      irreducibleBrauerCharacterBlock iota hinj blocks phi

/-- The literal membership subtype, retaining the same actual Brauer value. -/
abbrev BrauerUnion (i : SourceIndex F p ell n) :=
  {phi : IBr iota // brauerUnion Msys iota hinj S blocks ordinary i phi}

/-- Include the literal Brauer union in the free group on all actual IBr. -/
def brauerUnionInclusion (i : SourceIndex F p ell n) :
    MonoidAlgebra ℤ (BrauerUnion Msys iota hinj S blocks ordinary i) →ₗ[ℤ]
      MonoidAlgebra ℤ (IBr iota) :=
  MonoidAlgebra.mapDomainLinearMap ℤ ℤ Subtype.val

@[simp]
theorem brauerUnionInclusion_single (i : SourceIndex F p ell n)
    (phi : BrauerUnion Msys iota hinj S blocks ordinary i) :
    brauerUnionInclusion Msys iota hinj S blocks ordinary i (MonoidAlgebra.single phi 1) =
      MonoidAlgebra.single phi.val 1 := by
  simp only [brauerUnionInclusion, MonoidAlgebra.mapDomainLinearMap_single]

section BlockIdentification

variable {Core : AdmissibleParameter F p ell n → Type u}
variable [MulAction (CSp F n) (BlockPair F p ell n Core)]
variable (T : Theorem63Source unipotent S Core
  (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks)
variable (U : BlockUnionCertificate S Core
  (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks T)

include U in
/-- The exact full-union statement and specified ordinary-block surjectivity
force the Brauer union to be the existing primitive-block-index fibre. -/
theorem brauerUnion_iff_index (i : SourceIndex F p ell n) (phi : IBr iota) :
    brauerUnion Msys iota hinj S blocks ordinary i phi ↔
      brauerIndex iota hinj blocks T.blockSeries phi = i := by
  constructor
  · rintro ⟨chi, hchi, hblock⟩
    have hi := (indexedOrdinaryUnion_iff_blockSeries S U i chi).mp hchi
    exact (congrArg T.blockSeries hblock).symm.trans hi
  · intro hphi
    obtain ⟨chi, hchi⟩ :=
      (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock_surjective
      (irreducibleBrauerCharacterBlock iota hinj blocks phi)
    refine ⟨chi, ?_, hchi⟩
    apply (indexedOrdinaryUnion_iff_blockSeries S U i chi).mpr
    exact (congrArg T.blockSeries hchi).trans hphi

/-- Reconcile two membership subtypes by fixing the actual Brauer character.
The full-union certificate U is used in both directions. -/
def brauerUnionEquivFibre (i : SourceIndex F p ell n) :
    BrauerUnion Msys iota hinj S blocks ordinary i ≃
      SeriesFibre (brauerIndex iota hinj blocks T.blockSeries) i where
  toFun phi := ⟨phi.val, (brauerUnion_iff_index Msys iota hinj S blocks ordinary T U i phi.val).mp
    phi.property⟩
  invFun phi := ⟨phi.val, (brauerUnion_iff_index Msys iota hinj S blocks ordinary T U i phi.val).mpr
    phi.property⟩
  left_inv phi := by apply Subtype.ext; rfl
  right_inv phi := by apply Subtype.ext; rfl

@[simp]
theorem brauerUnionEquivFibre_val (i : SourceIndex F p ell n)
    (phi : BrauerUnion Msys iota hinj S blocks ordinary i) :
    (brauerUnionEquivFibre Msys iota hinj S blocks ordinary T U i phi).val = phi.val := rfl

@[simp]
theorem brauerUnionEquivFibre_symm_val (i : SourceIndex F p ell n)
    (phi : SeriesFibre (brauerIndex iota hinj blocks T.blockSeries) i) :
    ((brauerUnionEquivFibre Msys iota hinj S blocks ordinary T U i).symm phi).val =
      phi.val := rfl

/-- Reindexing the literal Brauer union preserves its inclusion in the SAME
free integral group on actual IBr. This is proved on ordinary generators. -/
theorem brauerUnionInclusion_reindex (i : SourceIndex F p ell n)
    (v : MonoidAlgebra ℤ (BrauerUnion Msys iota hinj S blocks ordinary i)) :
    seriesInclusion (brauerIndex iota hinj blocks T.blockSeries) i
        (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
          (brauerUnionEquivFibre Msys iota hinj S blocks ordinary T U i) v) =
      brauerUnionInclusion Msys iota hinj S blocks ordinary i v := by
  have h :
      (seriesInclusion (brauerIndex iota hinj blocks T.blockSeries) i).comp
          (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
            (brauerUnionEquivFibre Msys iota hinj S blocks ordinary T U i)).toLinearMap =
        brauerUnionInclusion Msys iota hinj S blocks ordinary i := by
    apply MonoidAlgebra.lhom_ext'
    intro phi
    apply LinearMap.ext_ring
    simp only [MonoidAlgebra.lsingle_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      MonoidAlgebra.mapDomainLinearEquiv_single, seriesInclusion_single,
      brauerUnionEquivFibre_val, brauerUnionInclusion_single]
  exact DFunLike.congr_fun h v

end BlockIdentification

section LiteralSource

variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)

/-- The individual integral basic-set conclusions on literal source and
target membership carriers. The target is the actual full block union above,
not a separately supplied Brauer-index partition. -/
structure LiteralIntegralSeriesData where
  perSeries : ∀ i : SourceIndex F p ell n,
    MonoidAlgebra ℤ {chi : Irr K (SpecialClifford n F) // chi ∈ S.rationalFamily i} ≃ₗ[ℤ]
      MonoidAlgebra ℤ (BrauerUnion Msys iota hinj S blocks ordinary i)
  sourceGenerator : ∀ (i : SourceIndex F p ell n)
    (chi : {chi : Irr K (SpecialClifford n F) // chi ∈ S.rationalFamily i}),
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
        (brauerUnionInclusion Msys iota hinj S blocks ordinary i
          (perSeries i (MonoidAlgebra.single chi 1))) =
      decompositionMapOfStableReduction Msys iota hcompat
        (simpleClassToFDRepKZeroGenerator (TypeBOrdinaryLabelSplitting.ordinaryLabel chi.val))

/-- One-way FLZ Theorem 2.3 at connected-centre coinvariant order one.
S fixes the finite-field/rank and the TWO ordinary root scopes; the specified
ordinary source fixes the SAME modular system, root and decomposition numbers.
Algebraic finite-point, centre and coefficient realizations remain E1/E2/U.
Only individual integral maps with their actual reduction equations occur. -/
structure LiteralTheorem23Certificate where
  applies : Theorem23Hypotheses p ell 1 →
    Nonempty (LiteralIntegralSeriesData Msys iota hinj S blocks ordinary hcompat)

variable {Core : AdmissibleParameter F p ell n → Type u}
variable [MulAction (CSp F n) (BlockPair F p ell n Core)]
variable (T : Theorem63Source unipotent S Core
  (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks)
variable (U : BlockUnionCertificate S Core
  (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks T)

/-- Construct the existing per-series packet by reindexing the literal
Brauer union. The full-union U is genuinely used in the target equivalence. -/
def toIntegralSeriesData
    (data : LiteralIntegralSeriesData Msys iota hinj S blocks ordinary hcompat) :
    IntegralSeriesData Msys iota hcompat hinj S.rationalSeriesSource blocks T.blockSeries where
  perSeries i := (data.perSeries i).trans
    (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
      (brauerUnionEquivFibre Msys iota hinj S blocks ordinary T U i))
  sourceGenerator i chi := by
    change labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
        (seriesInclusion (brauerIndex iota hinj blocks T.blockSeries) i
          (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
            (brauerUnionEquivFibre Msys iota hinj S blocks ordinary T U i)
              (data.perSeries i (MonoidAlgebra.single chi 1)))) = _
    rw [brauerUnionInclusion_reindex]
    exact data.sourceGenerator i chi

/-- Transport the exact one-way literal FLZ source into the frozen
Theorem23Certificate interface, with the SAME sufficient ordinary roots. -/
def toTheorem23Certificate
    (source : LiteralTheorem23Certificate Msys iota hinj S blocks ordinary hcompat) :
    TypeBIntegralSeriesSplitting.Theorem23Certificate Msys iota hcompat hinj
      S.rationalSeriesSource blocks T.blockSeries p 1 (ordinaryRoots := S.ordinary_roots) := by
  letI := S.ordinary_roots
  refine { applies := ?_ }
  intro h
  obtain ⟨data⟩ := source.applies h
  exact ⟨toIntegralSeriesData Msys iota hinj S blocks ordinary hcompat T U data⟩

end LiteralSource

end ModularRep.PaperProofs.TypeBFLZLiteralIntegralSeries


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
