import ModularRep.PaperProofs.TypeBQ3PrincipalPairBlockChoice

/-! Restriction of the block equations for two fixed extensions to a subgroup
containing the base. The block labels and their specified catalogues are
transported from the original intermediate groups. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3PrincipalCriterionBlockTransport

open ModularRep ModularRep.FDRepSimpleClassKZero
open TypeBQ3PrincipalPairBlockChoice

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

variable {A : Type u} [Group A]

/-- The literal subgroup image of an intermediate subgroup. -/
def imageEquiv (I : Subgroup A) (J : Subgroup I) : J ≃* J.map I.subtype :=
  J.equivMapOfInjective I.subtype I.subtype_injective

/-- The local intersection is transported by the same subgroup image map. -/
def localImageEquiv (D I : Subgroup A) (J : Subgroup I) :
    localIntersection (localIntersection D I) J ≃*
      localIntersection D (J.map I.subtype) where
  toFun x := ⟨imageEquiv I J x.1, x.2⟩
  invFun x := ⟨(imageEquiv I J).symm x.1, by
    change ((((imageEquiv I J).symm x.1 : J) : I) : A) ∈ D
    have h := congrArg (fun y : J.map I.subtype => (y : A))
      ((imageEquiv I J).apply_symm_apply x.1)
    change ((((imageEquiv I J).symm x.1 : J) : I) : A) = (x.1 : A) at h
    rw [h]
    exact x.2⟩
  left_inv x := Subtype.ext ((imageEquiv I J).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((imageEquiv I J).apply_symm_apply x.1)
  map_mul' x y := Subtype.ext ((imageEquiv I J).map_mul x.1 y.1)

theorem localImage_square (D I : Subgroup A) (J : Subgroup I) :
    (imageEquiv I J).symm.toMonoidHom.comp
        (localIntersection D (J.map I.subtype)).subtype =
      (localIntersection (localIntersection D I) J).subtype.comp
        (localImageEquiv D I J).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro x
  rfl

variable {p : Nat} {k K : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [Fact p.Prime]
variable [Fintype A]

/-- Carry the complete datum at the image of an intermediate subgroup back to
its subgroup presentation. Both restriction equations refer to the original
characters. -/
def restrictIntermediate (D I : Subgroup A)
    (globalCharacter : PrimeRegularClassFunction K A p)
    (localCharacter : PrimeRegularClassFunction K D p)
    (J : Subgroup I)
    (data : IntermediateBlockData p k K D globalCharacter localCharacter
      (J.map I.subtype)) :
    IntermediateBlockData p k K (localIntersection D I)
      (PrimeRegularClassFunction.pullback I.subtype globalCharacter)
      (PrimeRegularClassFunction.pullback (localInclusion D I) localCharacter) J := by
  let eG := (imageEquiv I J).symm
  let eL := (localImageEquiv D I J).symm
  refine {
    globalRoot := data.globalRoot.alongMulEquiv eG
    globalBrauer := IrreducibleBrauerCharacter.alongMulEquiv data.globalRoot eG data.globalBrauer
    globalRestriction := ?_
    localRoot := data.localRoot.alongMulEquiv eL
    localBrauer := IrreducibleBrauerCharacter.alongMulEquiv data.localRoot eL data.localBrauer
    localRestriction := ?_
    GlobalBlock := data.GlobalBlock
    LocalBlock := data.LocalBlock
    globalBlockIdempotent := fun b => MonoidAlgebra.domCongr k k eG (data.globalBlockIdempotent b)
    localBlockIdempotent := fun b => MonoidAlgebra.domCongr k k eL (data.localBlockIdempotent b)
    globalBlocks := data.globalBlocks.alongMulEquiv eG
    localBlocks := data.localBlocks.alongMulEquiv eL
    globalBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    localBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    globalCentralCharacters := data.globalCentralCharacters.alongMulEquiv eG
    localCentralCharacters := data.localCentralCharacters.alongMulEquiv eL
    globalCentralCharactersNavarro311 := ⟨data.globalCentralCharactersNavarro311.fieldSource⟩
    localCentralCharactersNavarro311 := ⟨data.localCentralCharactersNavarro311.fieldSource⟩
    inductionEquality := ?_ }
  · apply PrimeRegularClassFunction.ext
    intro x
    exact congrArg
      (fun chi : PrimeRegularClassFunction K (J.map I.subtype) p =>
        chi (PrimeRegularElement.map (imageEquiv I J).toMonoidHom x))
      data.globalRestriction
  · apply PrimeRegularClassFunction.ext
    intro x
    exact congrArg
      (fun chi : PrimeRegularClassFunction K (localIntersection D (J.map I.subtype)) p =>
        chi (PrimeRegularElement.map (localImageEquiv D I J).toMonoidHom x))
      data.localRestriction
  · rw [irreducibleBrauerCharacterBlock_alongMulEquiv data.localRoot
        data.localBrauerInjective eL (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
        data.localBlocks data.localBrauer,
      irreducibleBrauerCharacterBlock_alongMulEquiv data.globalRoot
        data.globalBrauerInjective eG (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
        data.globalBlocks data.globalBrauer]
    exact blockInducesTo_alongMulEquiv
      (localIntersection D (J.map I.subtype)) (localIntersection (localIntersection D I) J)
      eG eL (localImage_square D I J)
      data.localCentralCharacters data.globalCentralCharacters
      (data.localCentralCharacters.alongMulEquiv eL)
      (data.globalCentralCharacters.alongMulEquiv eG) rfl rfl data.inductionEquality

/-- The lifted intermediate subgroup still contains the original base. -/
theorem base_le_image (B I : Subgroup A) (hBI : B ≤ I)
    (J : Subgroup I) (hJ : B.comap I.subtype ≤ J) :
    B ≤ J.map I.subtype := by
  intro b hb
  exact ⟨⟨b, hBI hb⟩, hJ hb, rfl⟩

/-- Restrict a fixed family of intermediate block equations to a subgroup
containing the base. The new ambient and local characters are the irreducible
restrictions already supplied by that same family at I. -/
def restrictedIntermediate (B D I : Subgroup A) (hBI : B ≤ I)
    (globalCharacter : PrimeRegularClassFunction K A p)
    (localCharacter : PrimeRegularClassFunction K D p)
    (family : ∀ J : Subgroup A, B ≤ J →
      IntermediateBlockData p k K D globalCharacter localCharacter J)
    (J : Subgroup I) (hJ : B.comap I.subtype ≤ J) :
    IntermediateBlockData p k K (localIntersection D I)
      (family I hBI).globalBrauer.val (family I hBI).localBrauer.val J := by
  have transported := restrictIntermediate D I globalCharacter localCharacter J
    (family (J.map I.subtype) (base_le_image B I hBI J hJ))
  rw [(family I hBI).globalRestriction, (family I hBI).localRestriction] at transported
  exact transported

end ModularRep.PaperProofs.TypeBQ3PrincipalCriterionBlockTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
