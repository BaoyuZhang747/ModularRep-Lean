import ModularRep.PaperProofs.TypeBSpinPrincipalDecompositionBinding
import ModularRep.PaperProofs.TypeBIntegralSeriesSplitting
import ModularRep.LiteralOrdinaryPBlockSource

/-!
# Specified ordinary decomposition support for the consistent Type B basic set

The row below counts actual simple factors of the SAME chosen stable-lattice
reduction of the checked ordinary representation. The existing generic
Jordan--Holder coordinate map is reused. The ordinary-block source is fixed
to these actual nonzero multiplicities. The derived basic-set generator row
is identified with that specified row, so forward block support is a theorem,
not another lattice-support source input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBOrdinaryBlockSplitting

open ModularRep ExactGrothendieckGroup FDRepSimpleClassKZero
open OrdinaryIrreducibleCharacter DecompositionBasicSetBridge BlockFibreRestriction
open TypeBOrdinaryLabelSplitting
open TypeBSpinPrincipalDecompositionBinding
  (brauerCoordinates brauerCoordinates_nonneg brauerCoordinates_character)

universe u

variable {p : ℕ} {K O k G : Type u}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k p] [IsAlgClosed k] [Group G] [Finite G]

/-- Actual integral simple-factor coordinates of the prescribed reduction. -/
def decompositionRow (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G) (chi : Irr K G) : IBr iota →₀ ℤ :=
  brauerCoordinates iota (chosenReductionClass Msys (representation chi))

theorem decompositionRow_nonneg (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G) (chi : Irr K G) (phi : IBr iota) :
    0 ≤ decompositionRow Msys iota chi phi :=
  brauerCoordinates_nonneg iota
    (stableLatticeReduction Msys (representation chi)
      (chosenStableLattice O (representation chi))) phi

/-- The actual nonnegative decomposition number, not a supplied matrix. -/
def decompositionNumber (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G) (chi : Irr K G) (phi : IBr iota) : ℕ :=
  (decompositionRow Msys iota chi phi).toNat

theorem decompositionNumber_int (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G) (chi : Irr K G) (phi : IBr iota) :
    (decompositionNumber Msys iota chi phi : ℤ) = decompositionRow Msys iota chi phi :=
  Int.toNat_of_nonneg (decompositionRow_nonneg Msys iota chi phi)

/-- The stable-lattice row is the row of the SAME exact decomposition map. -/
theorem decompositionRow_exact (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (chi : Irr K G) :
    decompositionRow Msys iota chi = brauerCoordinates iota
      (decompositionMapOfStableReduction Msys iota hcompat
        (classOf (FDRep K G) (representation chi))) := by
  apply congrArg (brauerCoordinates iota)
  apply brauerCharacterKZeroHom_injective iota
  have hchosen := ExactCharacterBridge.chosenReductionClass_compatible Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat) (representation chi)
  have hexact := congrArg
    (fun h => h (classOf (FDRep K G) (representation chi)))
    (decompositionMapOfStableReduction_characterSquare Msys iota hcompat)
  exact hchosen.trans hexact.symm

/-- The actual prime regular character expansion of this row. -/
theorem decompositionRow_character (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (chi : Irr K G) :
    Finsupp.linearCombination ℤ (fun phi : IBr iota => phi.val.toFun)
        (decompositionRow Msys iota chi) =
      fun x : PrimeRegularElement (G := G) p => chi x.val := by
  rw [decompositionRow, brauerCoordinates_character]
  have hchosen := ExactCharacterBridge.chosenReductionClass_compatible Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat) (representation chi)
  change brauerCharacterKZeroHom iota _ = ordinaryCharacterKZero p _ at hchosen
  rw [hchosen]
  funext x
  rw [ordinaryCharacterKZero_classOf_apply]
  exact congrFun (representation_character chi) x.val

/-- The specified Brauer labels recover exactly the free integral coefficients. -/
theorem brauerCoordinates_labelled (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota) (v : MonoidAlgebra ℤ (IBr iota)) :
    brauerCoordinates iota
        (labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm v) = v.coeff := by
  change FreeAbelianGroup.toFinsupp
    (FreeAbelianGroup.map (simpleClassToIBr iota)
      (fdRepSimpleJordanHolderHom
        (simpleClassToFDRepKZero
          (FreeAbelianGroup.map (simpleModuleClassEquivIBr iota hinj).symm
            (Finsupp.toFreeAbelianGroup v.coeff))))) = v.coeff
  rw [fdRepSimpleJordanHolderHom_simpleClassToFDRepKZero,
    ← FreeAbelianGroup.map_comp_apply]
  have hcomp : (simpleClassToIBr iota) ∘ (simpleModuleClassEquivIBr iota hinj).symm = id := by
    funext phi
    exact (simpleModuleClassEquivIBr iota hinj).apply_symm_apply phi
  rw [hcomp, FreeAbelianGroup.map_id_apply, FreeAbelianGroup.toFinsupp_toFreeAbelianGroup]

section BasicSet

variable {I : Type u} [Fintype I]
  (Msys : ModularSystem p K O k)
  (iota : PrimeRegularRootEmbedding p k K G)
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  (S : TypeBRationalSeriesSource.RationalSeriesSource K G I)
  [Fintype (LiteralPrimitiveBlock k G)]
  (blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G => b.val))
  (blockSeries : LiteralPrimitiveBlock k G → I)
  (data : TypeBIntegralSeriesSplitting.IntegralSeriesData
    Msys iota hcompat hinj S blocks blockSeries)

/-- The constructed integral basic set has the specified decomposition row
on each actual ordinary generator. No row equality is an input. -/
theorem basicSet_generator_coeff (x : S.Basic) :
    ((data.globalBasicSet Msys iota hcompat hinj S blocks blockSeries).linearEquiv
      (MonoidAlgebra.single x 1)).coeff = decompositionRow Msys iota x.val := by
  let basic := data.globalBasicSet Msys iota hcompat hinj S blocks blockSeries
  have h := congrArg (brauerCoordinates iota)
    (basic.restricts_decomposition (MonoidAlgebra.single x 1))
  rw [brauerCoordinates_labelled] at h
  have hlabel : labelledSimpleClassKZero basic.ordinaryLabel (MonoidAlgebra.single x 1) =
      classOf (FDRep K G) (representation x.val) := by
    rw [labelledSimpleClassKZero_single]
    exact classOf_iso (FDRep K G)
      (simpleClassOfIrreducibleFDRepIso (representation x.val)
        (representation_irreducible x.val))
  rw [hlabel] at h
  exact h.trans (decompositionRow_exact Msys iota hcompat x.val).symm

end BasicSet

section PhysicalBlocks

variable (Msys : ModularSystem p K O k)
  (iota : PrimeRegularRootEmbedding p k K G)
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  [Fintype (LiteralPrimitiveBlock k G)]
  (blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G => b.val))

/-- Narrow E1/U ordinary-block input, with support fixed to actual stable
reduction multiplicities in this splitting modular system. No lattice map
or selected-series support predicate is supplied. -/
structure OrdinaryBlockSource [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card G)] where
  physical : LiteralOrdinaryPBlockSource iota hinj blocks
    (fun chi phi => decompositionNumber Msys iota chi phi ≠ 0)

variable [HasEnoughRootsOfUnity K (Nat.card G)]
  (ordinary : OrdinaryBlockSource Msys iota hinj blocks)

/-- Every nonzero actual decomposition coefficient belongs to the literal
ordinary block fixed by the standard selector source. -/
theorem block_of_nonzero_row (chi : Irr K G) (phi : IBr iota)
    (h : decompositionRow Msys iota chi phi ≠ 0) :
    irreducibleBrauerCharacterBlock iota hinj blocks phi = ordinary.physical.ordinaryBlock chi := by
  have hn : decompositionNumber Msys iota chi phi ≠ 0 := by
    intro hn
    apply h
    rw [← decompositionNumber_int Msys iota chi phi, hn]
    rfl
  have hb := (ordinary.physical.support_nonempty_and_sound chi).2 phi hn
  have heq : literalBrauerBlock iota hinj blocks phi =
      irreducibleBrauerCharacterBlock iota hinj blocks phi := by
    apply Subtype.ext
    rfl
  exact heq.symm.trans hb

/-- Forward support for the SAME derived integral packet now follows from
the specified ordinary selector and actual decomposition row. -/
theorem forwardSupport {I : Type u} [Fintype I]
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (S : TypeBRationalSeriesSource.RationalSeriesSource K G I)
    (blockSeries : LiteralPrimitiveBlock k G → I)
    (data : TypeBIntegralSeriesSplitting.IntegralSeriesData
      Msys iota hcompat hinj S blocks blockSeries)
    (x : S.Basic) :
    (data.globalBasicSet Msys iota hcompat hinj S blocks blockSeries).linearEquiv
        (MonoidAlgebra.single x 1) ∈ MonoidAlgebra.supported ℤ ℤ
      (blockFibreSet (irreducibleBrauerCharacterBlock iota hinj blocks)
        (ordinary.physical.ordinaryBlock x.val)) := by
  apply MonoidAlgebra.mem_supported.mpr
  intro phi hphi
  have hn : decompositionRow Msys iota x.val phi ≠ 0 := by
    rw [← basicSet_generator_coeff Msys iota hcompat hinj S blocks blockSeries data x]
    exact Finsupp.mem_support_iff.mp hphi
  exact block_of_nonzero_row Msys iota hinj blocks ordinary x.val phi hn

end PhysicalBlocks

end ModularRep.PaperProofs.TypeBOrdinaryBlockSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
