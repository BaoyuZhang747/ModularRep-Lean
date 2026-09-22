import ModularRep.PaperProofs.TypeBBroueMichelBlockIndex
import ModularRep.PaperProofs.TypeBFLZLiteralIntegralSeries

/-!
# Special-Clifford block indices from the actual Broue--Michel unions

The SAME equation-(3.4) rational family and specified ordinary selector
determine a block index from ordinary coverage, disjointness and block
closure. No core labels or Theorem-6.3 classification are used.

The individual literal FLZ-2.3 packet is reused unchanged. Its Brauer union
is defined by specified block equality; ordinary-selector surjectivity
therefore gives the value-preserving reindexing without an extra
existence-above hypothesis. Selected same-block parameters are conjugate.
These deductions supply precisely the data needed by the SC Conlon join.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpecialCliffordBroueMichelSource

open ModularRep OrdinaryIrreducibleCharacter FDRepSimpleClassKZero
open DecompositionBasicSetBridge ExactGrothendieckGroup
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBRationalSeriesBasicSet
open TypeBFLZLabelSource (UnipotentPredicate FullCharacterPair CharacterPair
  AdmissibleParameter SourceIndex parameterIndex parameterIndex_eq_iff admissibleToSemisimple)
open TypeBFLZLabelSplittingSource TypeBFLZBlockUnionSplitting
open TypeBIntegralSeriesSplitting (brauerIndex IntegralSeriesData)
open TypeBFLZLiteralIntegralSeries (BrauerUnion brauerUnion brauerUnionInclusion
  brauerUnionInclusion_single LiteralIntegralSeriesData LiteralTheorem23Certificate)

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

/-- Ordinary partition and Broue--Michel block closure on the literal
full unions of the SAME rational family. Coverage/disjointness are the
ordinary partition and commuting prime-part consequences; blockClosed is
FLZ Section 2.4.2, p.537. No block index or core classification is supplied. -/
structure BlockUnionCertificate
    [finiteDefiningField : Finite F] [definingCharacteristic : CharP F p]
    [ordinaryCharacteristic : CharZero K] : Prop where
  coverage : ∀ chi, ∃ s, indexedOrdinaryUnion S s chi
  disjoint : ∀ s t chi,
    indexedOrdinaryUnion S s chi → indexedOrdinaryUnion S t chi → s = t
  blockClosed : ∀ s chi psi,
    (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock chi =
      (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock psi →
    indexedOrdinaryUnion S s chi → indexedOrdinaryUnion S s psi

variable (C : BlockUnionCertificate Msys iota hinj S blocks ordinary)

/-- Construct the semisimple class of each specified block. This map need
not be injective: several blocks may have the same semisimple parameter. -/
def blockSeries : LiteralPrimitiveBlock k (SpecialClifford n F) → SourceIndex F p ell n := by
  letI := S.ordinary_roots
  exact TypeBBroueMichelBlockIndex.physicalBlockIndex Msys iota hinj blocks ordinary
    (indexedOrdinaryUnion S) C.coverage C.blockClosed

theorem ordinaryUnion_iff_blockSeries (s : SourceIndex F p ell n)
    (chi : Irr K (SpecialClifford n F)) :
    indexedOrdinaryUnion S s chi ↔
      blockSeries Msys iota hinj S blocks ordinary C
        ((ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock chi) = s := by
  letI := S.ordinary_roots
  exact TypeBBroueMichelBlockIndex.ordinaryUnion_iff_index Msys iota hinj blocks ordinary
    (indexedOrdinaryUnion S) C.coverage C.blockClosed C.disjoint s chi

/-- The constructed block index agrees with the selected ordinary index
on the identical specified ordinary character. -/
theorem blockSeries_familyOrdinaryBlock (chi : S.rationalSeriesSource.Basic) :
    blockSeries Msys iota hinj S blocks ordinary C
        ((ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock chi.val) =
      S.rationalSeriesSource.ordinaryIndex chi := by
  apply (ordinaryUnion_iff_blockSeries Msys iota hinj S blocks ordinary C _ chi.val).mp
  exact rationalFamily_mem_indexedOrdinaryUnion S _ chi.val
    (S.rationalSeriesSource.ordinaryIndex_mem chi)

include C in
/-- Two ell-prime rational-series characters in one specified block have
conjugate actual CSp parameters. Only union closure/disjointness is used. -/
theorem parameters_isConj_of_same_block (s t : AdmissibleParameter F p ell n)
    (chi psi : Irr K (SpecialClifford n F))
    (hs : S.rationalSeries (admissibleToSemisimple F p ell n s) chi)
    (ht : S.rationalSeries (admissibleToSemisimple F p ell n t) psi)
    (hb : (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock chi =
      (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock psi) :
    IsConj s.val t.val := by
  have hu : indexedOrdinaryUnion S (parameterIndex F p ell n s) chi :=
    ⟨s, rfl, rationalSeries_mem_ordinaryUnion S s chi hs⟩
  have hv : indexedOrdinaryUnion S (parameterIndex F p ell n t) psi :=
    ⟨t, rfl, rationalSeries_mem_ordinaryUnion S t psi ht⟩
  exact (parameterIndex_eq_iff F p ell n s t).mp
    (C.disjoint _ _ psi (C.blockClosed _ chi psi hb hu) hv)

include C in
/-- The same implication on the actual equation-(3.4) character labels
used by the tensor-translation argument. No core pair is needed. -/
theorem family_parameters_isConj_of_same_block
    (l r : CharacterPair F K p ell n unipotent)
    (hb : (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock
        (S.familyCharacter l).val =
      (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock
        (S.familyCharacter r).val) :
    IsConj l.1.1 r.1.1 := by
  exact parameters_isConj_of_same_block Msys iota hinj S blocks ordinary C l.1 r.1
    (S.character l).val (S.character r).val
    ((S.character_rational_membership _ l).mpr (IsConj.refl _))
    ((S.character_rational_membership _ r).mpr (IsConj.refl _)) hb

/-- The EXISTING literal SC Brauer union is exactly the newly constructed
index fibre. Its reverse direction needs only specified block surjectivity. -/
theorem brauerUnion_iff_index (s : SourceIndex F p ell n) (phi : IBr iota) :
    brauerUnion Msys iota hinj S blocks ordinary s phi ↔
      brauerIndex iota hinj blocks (blockSeries Msys iota hinj S blocks ordinary C) phi = s := by
  constructor
  · rintro ⟨chi, hchi, hb⟩
    have hi := (ordinaryUnion_iff_blockSeries Msys iota hinj S blocks ordinary C s chi).mp hchi
    exact (congrArg (blockSeries Msys iota hinj S blocks ordinary C) hb).symm.trans hi
  · intro hphi
    obtain ⟨chi, hchi⟩ :=
      (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock_surjective
        (irreducibleBrauerCharacterBlock iota hinj blocks phi)
    refine ⟨chi, ?_, hchi⟩
    apply (ordinaryUnion_iff_blockSeries Msys iota hinj S blocks ordinary C s chi).mpr
    exact (congrArg (blockSeries Msys iota hinj S blocks ordinary C) hchi).trans hphi

/-- Reindex only membership proofs; both directions fix the actual IBr. -/
def brauerUnionEquivFibre (s : SourceIndex F p ell n) :
    BrauerUnion Msys iota hinj S blocks ordinary s ≃
      SeriesFibre (brauerIndex iota hinj blocks
        (blockSeries Msys iota hinj S blocks ordinary C)) s where
  toFun phi := ⟨phi.val, (brauerUnion_iff_index Msys iota hinj S blocks ordinary C s phi.val).mp
    phi.property⟩
  invFun phi := ⟨phi.val, (brauerUnion_iff_index Msys iota hinj S blocks ordinary C s phi.val).mpr
    phi.property⟩
  left_inv phi := by apply Subtype.ext; rfl
  right_inv phi := by apply Subtype.ext; rfl

@[simp]
theorem brauerUnionEquivFibre_val (s : SourceIndex F p ell n)
    (phi : BrauerUnion Msys iota hinj S blocks ordinary s) :
    (brauerUnionEquivFibre Msys iota hinj S blocks ordinary C s phi).val = phi.val := rfl

@[simp]
theorem brauerUnionEquivFibre_symm_val (s : SourceIndex F p ell n)
    (phi : SeriesFibre (brauerIndex iota hinj blocks
      (blockSeries Msys iota hinj S blocks ordinary C)) s) :
    ((brauerUnionEquivFibre Msys iota hinj S blocks ordinary C s).symm phi).val = phi.val := rfl

/-- The inclusion square preserves the same free integral Brauer generator. -/
theorem brauerUnionInclusion_reindex (s : SourceIndex F p ell n)
    (v : MonoidAlgebra ℤ (BrauerUnion Msys iota hinj S blocks ordinary s)) :
    seriesInclusion (brauerIndex iota hinj blocks
        (blockSeries Msys iota hinj S blocks ordinary C)) s
      (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
        (brauerUnionEquivFibre Msys iota hinj S blocks ordinary C s) v) =
      brauerUnionInclusion Msys iota hinj S blocks ordinary s v := by
  have h :
      (seriesInclusion (brauerIndex iota hinj blocks
        (blockSeries Msys iota hinj S blocks ordinary C)) s).comp
        (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
          (brauerUnionEquivFibre Msys iota hinj S blocks ordinary C s)).toLinearMap =
        brauerUnionInclusion Msys iota hinj S blocks ordinary s := by
    apply MonoidAlgebra.lhom_ext'
    intro phi
    apply LinearMap.ext_ring
    simp only [MonoidAlgebra.lsingle_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      MonoidAlgebra.mapDomainLinearEquiv_single, seriesInclusion_single,
      brauerUnionEquivFibre_val, brauerUnionInclusion_single]
  exact DFunLike.congr_fun h v

variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)

/-- Reuse the existing individual literal FLZ map, with only a
value-preserving reindexing of its target and the same generator equation. -/
def toIntegralSeriesData
    (data : LiteralIntegralSeriesData Msys iota hinj S blocks ordinary hcompat) :
    IntegralSeriesData Msys iota hcompat hinj S.rationalSeriesSource blocks
      (blockSeries Msys iota hinj S blocks ordinary C) where
  perSeries s := (data.perSeries s).trans
    (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
      (brauerUnionEquivFibre Msys iota hinj S blocks ordinary C s))
  sourceGenerator s chi := by
    change labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
        (seriesInclusion (brauerIndex iota hinj blocks
          (blockSeries Msys iota hinj S blocks ordinary C)) s
          (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
            (brauerUnionEquivFibre Msys iota hinj S blocks ordinary C s)
              (data.perSeries s (MonoidAlgebra.single chi 1)))) = _
    rw [brauerUnionInclusion_reindex]
    exact data.sourceGenerator s chi

/-- The old integral source certificate is derived from literal23;
the same ordinary primitive-root scope is explicitly installed. -/
def toTheorem23Certificate
    (source : LiteralTheorem23Certificate Msys iota hinj S blocks ordinary hcompat) :
    TypeBIntegralSeriesSplitting.Theorem23Certificate Msys iota hcompat hinj
      S.rationalSeriesSource blocks (blockSeries Msys iota hinj S blocks ordinary C)
      p 1 (ordinaryRoots := S.ordinary_roots) := by
  letI := S.ordinary_roots
  refine { applies := ?_ }
  intro h
  obtain ⟨data⟩ := source.applies h
  exact ⟨toIntegralSeriesData Msys iota hinj S blocks ordinary C hcompat data⟩

end ModularRep.PaperProofs.TypeBSpecialCliffordBroueMichelSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
