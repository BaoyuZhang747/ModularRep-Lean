import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralV3BlockAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierThreeBlockFixedPoints
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3NonprincipalBrauerSignature
import ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow

/-! Derive stability of every specified block from the literal rows and fusion.
A common zero excludes the trivial character from the selected block. These
two distinct fixed blocks exhaust the possible movement on three blocks. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierV3BlockStability
open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualBlockBrauerAction
open SporadicFi24P3Definition44NamedCarrierP3NonprincipalBrauerSignature
open SporadicFi24P3Definition44NamedCarrierLiteralV3Rows
open SporadicFi24P3Definition44NamedCarrierLiteralV3BlockAction
open SporadicFi24P3Definition44NamedCarrierThreeBlockFixedPoints
open SporadicFi24P3V3RawRankCertificate
open SporadicFi24P3PlusRankReplayContract
open SporadicFi24P3Definition44Clause3ACWindow (trivialIBr trivialIBr_apply trivialIBr_fixed)

universe u v

theorem trivialBrauerBlock_ne_of_ordinary_rows_vanish
    {p : ℕ} {k K G I : Type u} {Row : Type v}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G] [Fintype I]
    {idempotents : I → k[G]}
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition idempotents)
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (b : ActualBlock (k := k) (X := G))
    (selected : Row → OrdinaryIrreducibleCharacter.Irr K G)
    (hcomplete : ∀ chi, D.ordinaryBlock chi = b ↔ ∃ r, selected r = chi)
    (g : PrimeRegularElement (G := G) p)
    (hzero : ∀ r, (selected r).1 g.1 = 0) :
    brauerBlock iota hinj blocks (trivialIBr iota) ≠ b := by
  let ev : PrimeRegularFunction K G p →ₗ[K] K := {
    toFun := fun f => f g
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hvan :
      Submodule.span K
        (Set.range fun r => actualOrdinaryRestriction (p := p) (selected r)) ≤
      LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    change (selected r).1 g.1 = 0
    exact hzero r
  intro hblock
  have hmem : actualBrauerFunction iota (trivialIBr iota) ∈
      actualBlockBrauerSpan iota hinj blocks b :=
    Submodule.subset_span ⟨⟨trivialIBr iota, hblock⟩, rfl⟩
  rw [← actualBlockOrdinaryRows_span iota hinj blocks D b selected hcomplete] at hmem
  have hz := hvan hmem
  change (trivialIBr iota).1 g = 0 at hz
  exact one_ne_zero ((trivialIBr_apply iota g).symm.trans hz)

variable {k K G I : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype I]
variable {idempotents : I → k[G]}
variable (iota : PrimeRegularRootEmbedding 3 k K G)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition idempotents)
variable (D : ActualOrdinaryDecomposition iota hinj blocks)
variable (b : ActualBlock (k := k) (X := G))
variable (selected : Fin 6 → OrdinaryIrreducibleCharacter.Irr K G)
variable (hcomplete : ∀ chi, D.ordinaryBlock chi = b ↔ ∃ r, selected r = chi)
variable (A : PrimeRegularRepresentativeCover 3 G (Fin 30))
variable (encoding : PrimitiveTwentyNineEncoding K)
variable (hvalues : ∀ r c, (selected r).1 (A.representative c).1 = literalV3Rows encoding r c)
variable (tau : MulAut G)
variable (fusion : ∀ c : Fin 30, ∃ x : G, tau (A.representative c).1 =
  x * (A.representative (regularOuterPermutation c)).1 * x⁻¹)
include hcomplete hvalues fusion

theorem actual_b1_fixed_of_literal_values : MulOpposite.op tau • b = b := by
  have closed := actualBlockBrauer_closed_of_ordinary_values
    iota hinj blocks b tau D selected hcomplete A
    (literalV3Rows encoding) hvalues regularOuterPermutation fusion
    ordinaryOuterPermutation (literalV3Rows_outer encoding)
  have hcard := actual_b1_card_four iota hinj blocks D b selected
    hcomplete A encoding (literalV3Binding encoding) hvalues
  have hpos : 0 < Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b} := by
    rw [hcard]
    decide
  obtain ⟨phi⟩ := (Nat.card_pos_iff.mp hpos).1
  have hb := closed phi.1 phi.2
  rwa [brauerBlock_transport iota hinj blocks, phi.2] at hb

theorem all_blocks_fixed_of_literal_values
    (roles : Fin 3 ≃ ActualBlock (k := k) (X := G)) :
    ∀ c : ActualBlock (k := k) (X := G), MulOpposite.op tau • c = c := by
  have hb := actual_b1_fixed_of_literal_values iota hinj blocks D b selected
    hcomplete A encoding hvalues tau fusion
  let c := brauerBlock iota hinj blocks (trivialIBr iota)
  have hc : MulOpposite.op tau • c = c := by
    dsimp only [c]
    rw [← brauerBlock_transport iota hinj blocks]
    change brauerBlock iota hinj blocks
      (IrreducibleBrauerCharacter.twist iota (trivialIBr iota) tau) = _
    rw [trivialIBr_fixed]
  have hne : c ≠ b :=
    trivialBrauerBlock_ne_of_ordinary_rows_vanish iota hinj blocks D b selected
      hcomplete (A.representative 23)
      (fun r => (hvalues r 23).trans (literalV3Rows_zero_column encoding r))
  exact eq_self_of_two_fixed_three roles (fun d => MulOpposite.op tau • d)
    (MulAction.injective (MulOpposite.op tau)) c b hne hc hb

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierV3BlockStability


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
