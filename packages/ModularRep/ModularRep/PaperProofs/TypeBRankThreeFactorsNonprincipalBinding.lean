import ModularRep.PaperProofs.TypeBRankThreeNonprincipalApplication
import ModularRep.PaperProofs.TypeBRankThreeFactorsApplication

/-!
# Factor inventory on the preceding nonprincipal reduction's actual Levi

This interface retains the original Omega block, its constructed Spin block,
dual label and least proper dual Levi by taking the preceding checked output.
The paired chart is indexed by that very Levi, and its dual Frobenius is the
same coordinate Frobenius `Phi frobenius`. The finite Clifford descent uses
the same field, characteristic, exponent and norm source as the Spin block.

The paired pinning and one-component normalization certificates remain the
explicit source boundary. No separate proper-Levi choice, component list,
finite factor equivalence or block conclusion is assumed at this join.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsNonprincipalBinding

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBCentralKernelBlockSource
open TypeBOrdinaryBlockSplitting TypeBRankThreeNonprincipalBlockBinding
open TypeBRankThreeNonprincipalSeriesBinding TypeBRankThreeNonprincipalDualLift
open TypeBRankThreeNonprincipalGeometry TypeBRankThreeNonprincipalBonnafeBinding
open TypeBRankThreeNonprincipalApplication TypeBRegularLeviRationalCarriers
open TypeBRankThreeFactorsPointSource TypeBRankThreeFactorsComponentModels
open TypeBRankThreeFactorsApplication

variable {p f : ℕ} {F A K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field A] [IsAlgClosed A] [CharP A p] [Algebra F A]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]
  (parameters : OddFieldParameters F p f) (N : NormSource 3 F)
  (orthogonal : TypeBCliffordOrthogonalSourceBinding.Source
    3 F p f parameters (by decide) N)
  [Finite (Spin 3 F N)]
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))

variable
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin 3 F N) => b.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (ordinary : OrdinaryBlockSource Msys iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks)
  (series : Sources parameters Msys iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    blocks ordinary)
  (frobenius : FrobeniusSource p f A)
  (points : RationalPointSource F A p f frobenius)
  (geometry : GeometrySource F A p f frobenius points)
  (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (reduction : ManuscriptReduction parameters N orthogonal Msys iota blocks ordinary
    series frobenius points geometry b)

variable (Nbar : NormSource 3 A) (chart : PairedChart Nbar reduction.levi)
  (cliffordFrobenius : MulAut (SpecialClifford 3 A))
  (stable : chart.primalLevi.map cliffordFrobenius.toMonoidHom = chart.primalLevi)
  (components : ComponentSource chart cliffordFrobenius stable)
  (cliffordPoints : CliffordFixedPointSource 3 p f F A N Nbar cliffordFrobenius)

/-- Output at the same retained dual Levi and coordinate Frobenius. -/
structure ManuscriptFactorReduction where
  dual_isLevi : geometry.IsLevi reduction.levi
  dual_frobenius : reduction.levi.map (Phi frobenius).toMonoidHom = reduction.levi
  inventory : ActualInventory chart cliffordFrobenius stable components
    p f N cliffordPoints (Phi frobenius)

/-- The actual predecessor output supplies properness; all carrier choices in
the factor endpoint are now tied to that output rather than a fresh Levi. -/
theorem nonprincipal_factor_inventory
    (pairing : RationalPairingSource chart cliffordFrobenius stable p f N
      cliffordPoints components (Phi frobenius))
    (normalizations : NormalizationSource (F := F) chart cliffordFrobenius stable components) :
    Nonempty (ManuscriptFactorReduction parameters N orthogonal Msys iota blocks
      ordinary series frobenius points geometry b reduction Nbar chart
      cliffordFrobenius stable components cliffordPoints) := by
  obtain ⟨inventory⟩ := source_instantiated_factor_inventory chart cliffordFrobenius
    stable components p f N cliffordPoints (Phi frobenius) reduction.levi_proper
    pairing normalizations
  exact ⟨⟨reduction.levi_isLevi, reduction.levi_frobenius, inventory⟩⟩

end ModularRep.PaperProofs.TypeBRankThreeFactorsNonprincipalBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
