import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrincipalBrauerSupport

/-! The unique degree-one row identifies the principal block on the actual
catalogue. Its Sylow support excludes a defect group of order nine. The
defect-zero role is separately excluded by its already derived bottom support. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectPrincipal
open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44Clause3ACWindow (trivialIBr trivialIBr_apply)
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierPrincipalBrauerSupport
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData

theorem degree_one_iff : ∀ r : Fin 108, degrees r = 1 ↔ r = 0 := by
  decide

universe u
variable {k K G : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem first_row_trivial (C : FullOrdinaryDegreeTable K G) :
    C.character 0 = ordinaryLinearIrr (1 : G →* Kˣ) := by
  obtain ⟨r, hr⟩ := C.complete (ordinaryLinearIrr (1 : G →* Kˣ))
  have hdK : (degrees r : K) = 1 := by
    rw [← C.degree r, hr]
    rfl
  have hd : degrees r = 1 := (Nat.cast_eq_one (R := K)).mp hdK
  have hr0 : r = 0 := (degree_one_iff r).mp hd
  simpa only [hr0] using hr

theorem principal_index
    (iota : PrimeRegularRootEmbedding 3 k K G)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
    (roles : Fin 3 ≃ ActualBlock (k := k) (X := G))
    (Dordinary : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ActualOrdinaryDecomposition iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R.1.operations.ambientBlockData.blocks)
    (C : FullOrdinaryDegreeTable K G)
    (allocation : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ∀ r, Dordinary.ordinaryBlock (C.character r) = roles (blockLabels r)) :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    irreducibleBrauerCharacterBlock iota
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R.1.operations.ambientBlockData.blocks (trivialIBr iota) = roles 0 := by
  classical
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  let hinj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let blocks := R.1.operations.ambientBlockData.blocks
  let phiOne := trivialIBr iota
  have hres : actualOrdinaryRestriction (p := 3) (C.character 0) =
      actualBrauerFunction iota phiOne := by
    funext x
    change (C.character 0).val x.val = phiOne.val x
    rw [first_row_trivial C]
    change (1 : K) = phiOne.val x
    exact (trivialIBr_apply iota x).symm
  have hcols : Dordinary.decomposition.columns (C.character 0) =
      Finsupp.single phiOne (1 : K) := by
    apply (irreducibleBrauerCharacters_linearIndependent iota).finsuppLinearCombination_injective
    calc
      Finsupp.linearCombination K (actualBrauerFunction iota)
          (Dordinary.decomposition.columns (C.character 0)) =
          actualOrdinaryRestriction (p := 3) (C.character 0) :=
        (Dordinary.decomposition.ordinary_eq_decomposition (C.character 0)).symm
      _ = actualBrauerFunction iota phiOne := hres
      _ = Finsupp.linearCombination K (actualBrauerFunction iota)
          (Finsupp.single phiOne (1 : K)) := by simp
  have hcoeff : Dordinary.decomposition.columns (C.character 0) phiOne ≠ 0 := by
    rw [hcols, Finsupp.single_eq_same]
    exact one_ne_zero
  have halloc : Dordinary.ordinaryBlock (C.character 0) = roles 0 := allocation 0
  have hprincipal : brauerBlock iota hinj blocks phiOne = roles 0 :=
    (Dordinary.decomposition.column_support (C.character 0) phiOne hcoeff).symm.trans halloc
  change operationsBlock iota hinj R phiOne = roles 0
  exact (operationsBlock_eq iota hinj R blocks phiOne).trans hprincipal

theorem principal_ne_of_defect_card_ne
    {I : Type u} [Fintype I] {e : I → k[G]}
    (iota : PrimeRegularRootEmbedding 3 k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition e)
    (b : I) (Q : Subgroup G)
    (hDefect : IsMaximalCentralBrauerDefect (p := 3) blocks b Q)
    (hcard : Nat.card Q ≠ ordProj[3] (Nat.card G)) :
    irreducibleBrauerCharacterBlock iota hinj blocks (trivialIBr iota) ≠ b := by
  intro hb
  obtain ⟨S, hQS⟩ := hDefect.isPGroup.exists_le_sylow
  have hs := trivialBlock_hasNonzeroCentralBrauerRestriction
    iota hinj blocks (S : Subgroup G) S.isPGroup'
  rw [hb] at hs
  have heq : Q = (S : Subgroup G) :=
    hDefect.eq_of_nonzero_le (S : Subgroup G) S.isPGroup' hs hQS
  apply hcard
  calc
    Nat.card Q = Nat.card (S : Subgroup G) :=
      congrArg (fun H : Subgroup G => Nat.card H) heq
    _ = ordProj[3] (Nat.card G) := S.card_eq_multiplicity

theorem block_eq_role_one_of_defect_nine
    (iota : PrimeRegularRootEmbedding 3 k K G)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
    (roles : Fin 3 ≃ ActualBlock (k := k) (X := G))
    (Dordinary : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ActualOrdinaryDecomposition iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R.1.operations.ambientBlockData.blocks)
    (C : FullOrdinaryDegreeTable K G)
    (allocation : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ∀ r, Dordinary.ordinaryBlock (C.character r) = roles (blockLabels r))
    (hZero : letI := R.1.operations.ambientBlockData.fintypeBlock
      IsMaximalCentralBrauerDefect (p := 3) R.1.operations.ambientBlockData.blocks
        (roles 2) (⊥ : Subgroup G))
    (b : ActualBlock (k := k) (X := G)) (Q : Subgroup G)
    (hQcard : Nat.card Q = 9)
    (hDefect : letI := R.1.operations.ambientBlockData.fintypeBlock
      IsMaximalCentralBrauerDefect (p := 3) R.1.operations.ambientBlockData.blocks b Q) :
    b = roles 1 := by
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  have h0 : b ≠ roles 0 := by
    intro hb
    have hne := principal_ne_of_defect_card_ne iota
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R.1.operations.ambientBlockData.blocks b Q hDefect (by
        rw [hQcard, C.groupOrder, group_order_three_part]
        decide)
    exact hne ((principal_index iota R roles Dordinary C allocation).trans hb.symm)
  have h2 : b ≠ roles 2 := by
    intro hb
    have hs := hDefect.nonzero_at_D
    rw [hb] at hs
    have heq := hZero.eq_of_nonzero_le Q hDefect.isPGroup hs bot_le
    have hc : Nat.card Q = 1 := by
      rw [← heq]
      simp
    omega
  obtain ⟨j, rfl⟩ := roles.surjective b
  fin_cases j <;> simp_all

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectPrincipal


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
