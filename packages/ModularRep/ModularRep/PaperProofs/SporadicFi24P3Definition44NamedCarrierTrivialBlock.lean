import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual
import ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport
import ModularRep.IBrBlockEquivTransport
import ModularRep.NavarroLocalReductionInflationBlockCompatibility

/-! The trivial-weight block identity is derived from actual reduction,
self-induction, and the existing complete block catalogues. It is not a
separate source premise for the complete-collapse correspondence. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialBlock

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs

universe u

theorem primitiveBlockOfIndex_moduleBlock_eq
    {A V I J : Type*}
    [Ring A] [AddCommGroup V] [Module A V] [IsSimpleModule A V]
    [Fintype I] [Fintype J] {b : I → A} {c : J → A}
    (B : BlockIdempotentDecomposition b) (C : BlockIdempotentDecomposition c) :
    B.primitiveBlockOfIndex (B.moduleBlock (V := V)) =
      C.primitiveBlockOfIndex (C.moduleBlock (V := V)) := by
  obtain ⟨i, hi⟩ := B.primitiveBlockOfIndex_surjective
    (C.primitiveBlockOfIndex (C.moduleBlock (V := V)))
  have hisupport : i = B.moduleBlock (V := V) := by
    apply B.moduleBlock_eq_of_smul_eq_self (V := V)
    intro v
    have hvalue := congrArg Subtype.val hi
    change b i = c (C.moduleBlock (V := V)) at hvalue
    rw [hvalue]
    exact C.moduleBlock_smul (V := V) v
  rw [← hisupport]
  exact hi

theorem centralCharacter_eq_of_idempotent_eq
    {k G I J : Type*}
    [Field k] [IsAlgClosed k] [Group G] [Fintype G] [Fintype I] [Fintype J]
    {b : I → k[G]} {c : J → k[G]}
    (B : BlockIdempotentDecomposition b) (C : BlockIdempotentDecomposition c)
    (catB : BlockCentralCharacterCatalogue B) (catC : BlockCentralCharacterCatalogue C)
    {i : I} {j : J} (h : b i = c j) :
    catB.centralCharacter i = catC.centralCharacter j := by
  have hcenter : B.blockIdempotentInCenter i = C.blockIdempotentInCenter j := Subtype.ext h
  obtain ⟨j', hj'⟩ := catC.exhaustive (catB.centralCharacter i)
  have hvalue : catC.centralCharacter j' (C.blockIdempotentInCenter j) = 1 := by
    rw [hj', ← hcenter]
    exact catB.centralCharacter_own i
  have hj : j' = j := by
    by_contra hne
    exact zero_ne_one ((catC.centralCharacter_other hne).symm.trans hvalue)
  subst j'
  exact hj'.symm

theorem centralCharacter_eq_of_same_IBr
    {p : ℕ} {k K G I J : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G] [Fintype I] [Fintype J]
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {b : I → k[G]} {c : J → k[G]}
    (B : BlockIdempotentDecomposition b) (C : BlockIdempotentDecomposition c)
    (catB : BlockCentralCharacterCatalogue B) (catC : BlockCentralCharacterCatalogue C)
    (phi : IBr iota) :
    catB.centralCharacter (irreducibleBrauerCharacterBlock iota hinj B phi) =
      catC.centralCharacter (irreducibleBrauerCharacterBlock iota hinj C phi) := by
  let cls := (simpleModuleClassEquivIBr iota hinj).symm phi
  let V := Representation.asModule (simpleClassFDRep cls).ρ
  let : IsSimpleModule k[G] V :=
    simple_iff_isSimpleModule.mp (simpleClassFDRep_underlying_simple cls)
  change catB.centralCharacter (B.moduleBlock (V := V)) = catC.centralCharacter (C.moduleBlock (V := V))
  exact centralCharacter_eq_of_idempotent_eq B C catB catC
    (congrArg Subtype.val (primitiveBlockOfIndex_moduleBlock_eq (V := V) B C))

theorem trivialWeightBlockCompatibilityOfOperations
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source R.1.operations) :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    TrivialWeightBlockCompatibility iota hinj R.1.operations.ambientBlockData.blocks R D T := by
  classical
  let O := R.1.operations
  let := O.ambientBlockData.fintypeBlock
  refine ⟨?_⟩
  intro d
  let W := T.rawAtOne d
  let N : Subgroup X := Subgroup.normalizer ((⊥ : Subgroup X) : Set X)
  let : Fintype N := Fintype.ofFinite _
  let : Fintype (Subgroup.normalizer (W.subgroup : Set X)) := Fintype.ofFinite _
  let localData := O.inflatedNormalizerBlockData W.subgroup
  let := localData.fintypeBlock
  let e : N ≃* X := trivialNormalizerEquiv
  have he : e.toMonoidHom = N.subtype := by
    ext n
    rfl
  let phi := D.reduce (iota := iota) d
  let rootN := iota.alongMulEquiv e.symm
  let phiN := IrreducibleBrauerCharacter.alongMulEquiv iota e.symm phi
  let injN := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rootN
  have hReduction : NormalizerInflatedReduction W.subgroup W.localCharacter rootN phiN := by
    intro n
    change d.1 n.1.1 = phi.1 (PrimeRegularElement.map e.toMonoidHom n)
    exact D.reduce_isReduction (iota := iota) d (PrimeRegularElement.map e.toMonoidHom n)
  let bG := irreducibleBrauerCharacterBlock iota hinj O.ambientBlockData.blocks phi
  let bL := O.inflateToNormalizer W.subgroup (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero)
  have hLocal : irreducibleBrauerCharacterBlock rootN injN localData.blocks phiN = bL :=
    compatibility.normalizerBrauerBlock_eq_inflateToNormalizer W rootN phiN hReduction
  have hTransported : irreducibleBrauerCharacterBlock rootN injN
      (O.ambientBlockData.blocks.alongMulEquiv e.symm) phiN = bG :=
    irreducibleBrauerCharacterBlock_alongMulEquiv iota hinj e.symm injN O.ambientBlockData.blocks phi
  have hCatalogue : (O.ambientBlockData.catalogue.alongMulEquiv e.symm).centralCharacter bG =
      localData.catalogue.centralCharacter bL := by
    rw [← hTransported, ← hLocal]
    exact centralCharacter_eq_of_same_IBr rootN injN
      (O.ambientBlockData.blocks.alongMulEquiv e.symm) localData.blocks
      (O.ambientBlockData.catalogue.alongMulEquiv e.symm) localData.catalogue phiN
  have hSelf := blockInducesTo_self_of_equiv_subtype
    (k := k) (H := N) O.ambientBlockData.blocks O.ambientBlockData.catalogue e he bG
  have hActual : BlockInducesTo N localData.catalogue O.ambientBlockData.catalogue bL bG := by
    simpa only [BlockInducesTo, hCatalogue] using hSelf
  have hInduced : bG = O.induceToAmbient W :=
    eq_inducedBlock_of_blockInducesTo N localData.catalogue O.ambientBlockData.catalogue bL
      (O.blockInductionDefined W) hActual
  calc
    R.1.weightBlock (T.atOne d) = O.induceToAmbient W := rfl
    _ = bG := hInduced.symm
    _ = operationsBlock iota hinj R phi := rfl
    _ = _ := operationsBlock_eq iota hinj R O.ambientBlockData.blocks phi

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
