import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.TypeBCentralKernelBrauerBlocks
import ModularRep.PaperProofs.TypeBLiteralBlockReindex
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
import ModularRep.PaperProofs.SporadicDefectZeroWeightFibreActual

/-!
The fixed defect-zero block on the SAME matrix G3 has singleton actual Brauer
and weight fibres. This is a supporting deduction for B4/B5, with no independent
manuscript-window credit. The specified block, selected ordinary character and
its actual reduction remain explicit source data. Navarro 3.18 supplies the
singleton Brauer fibre and selected defect-zero regular-restriction uniqueness;
the latter follows from defect-zero vanishing on prime-singular elements.
Navarro 4.8 and 4.13 supply the guarded consequence that a weight inducing to
this block has subgroup one. Canonical reduction and the normalizer selector
are required only for raw weights assigned this block and the selected atOne
weight. They use the SAME root and operations. No global reduction-choice
source, global ordinary-block source, correspondence or criterion is supplied.

The normalizer root, actual Brauer pullback, specified self-induction and
trivial-weight block compatibility are deductions. Every supported raw weight
has the literal local ordinary/Brauer value anchor for the selected phi. The
complete singleton matching and its action graph are then constructed.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B45DefectZeroMatching

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open SporadicCompleteCollapseLemma52Actual
  (GlobalDefectZeroCharacter TrivialWeightSource trivialNormalizerQuotientEquiv
    trivialNormalizerQuotientEquiv_symm_apply)
open SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierTrivialBlock

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance matrixFintype : Fintype G3 :=
  TypeBRankThreePrincipalCountBinding.groupFintype G3
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The simple nonabelian matrix group cannot be a two-group. -/
theorem not_two_group (matrixSource : MatrixExceptionalSource) :
    ¬ IsPGroup 2 G3 := by
  letI : IsSimpleGroup G3 := matrixSource.simple
  intro h
  have lt := h.bot_lt_center
  rw [TypeBExceptionalCanonicalCover.center_eq_bot_of_nonabelian_simple
    matrixSource.simple matrixSource.nonabelian] at lt
  exact (lt_irrefl _) lt

/-- No new radical-class source is needed on G3. -/
def trivialSource (matrixSource : MatrixExceptionalSource) :
    TrivialWeightSource (p := 2) (X := G3) := by
  letI : IsSimpleGroup G3 := matrixSource.simple
  exact TrivialWeightSource.ofSimpleNonPGroup Nat.prime_two
    (not_two_group matrixSource)

variable (root : PrimeRegularRootEmbedding 2 k K G3)
  (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))

/-- The actual normalizer inclusion is an equivalence when Q is trivial. -/
def normalizerEquiv (W : CharacterWeight 2 K G3) (hW : W.subgroup = ⊥) :
    Subgroup.normalizer (W.subgroup : Set G3) ≃* G3 :=
  (MulEquiv.subgroupCongr
    (show Subgroup.normalizer (W.subgroup : Set G3) = (⊤ : Subgroup G3) from by
      rw [hW]
      exact Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G3)))).trans
    (Subgroup.topEquiv : (⊤ : Subgroup G3) ≃* G3)

theorem normalizerEquiv_hom (W : CharacterWeight 2 K G3) (hW : W.subgroup = ⊥) :
    (normalizerEquiv W hW).toMonoidHom =
      (Subgroup.normalizer (W.subgroup : Set G3)).subtype := by
  ext n
  rfl

/-- Restriction and transport of the SAME root recover the original root. -/
theorem normalizerRoot_along (W : CharacterWeight 2 K G3)
    (hW : W.subgroup = ⊥) (s : CanonicalRawReduction root W) :
    s.normalizerRoot.alongMulEquiv (normalizerEquiv W hW) = root := by
  rw [s.normalizerRoot_eq, normalizerRootAt_eq_subgroupRoot]
  have hN : primeRegularExponent 2
      (Subgroup.normalizer (W.subgroup : Set G3)) ∣ primeRegularExponent 2 G3 := by
    simpa only [primeRegularExponent] using
      Nat.ordCompl_dvd_ordCompl_of_dvd
        (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (W.subgroup : Set G3))) 2
  simpa only [subgroupRoot, commonRoot_self] using
    ofCommonRoot_alongMulEquiv root.prime root.toMulEquiv hN (dvd_refl _)
      (normalizerEquiv W hW)

/-- The actual local reduction transported to G3 at its original root. -/
def globalBrauer (W : CharacterWeight 2 K G3)
    (hW : W.subgroup = ⊥) (s : CanonicalRawReduction root W) : IBr root := by
  let psi := IrreducibleBrauerCharacter.alongMulEquiv s.normalizerRoot
    (normalizerEquiv W hW) s.localBrauer
  refine ⟨psi.val, ?_⟩
  exact Eq.mp (congrArg (fun r : PrimeRegularRootEmbedding 2 k K G3 =>
    IsIrreducibleBrauerCharacter r psi.val) (normalizerRoot_along root W hW s))
    psi.property

theorem globalBrauer_pullback (W : CharacterWeight 2 K G3)
    (hW : W.subgroup = ⊥) (s : CanonicalRawReduction root W) :
    s.localBrauer.val = PrimeRegularClassFunction.pullback
      (Subgroup.normalizer (W.subgroup : Set G3)).subtype
      (globalBrauer root W hW s).val := by
  apply PrimeRegularClassFunction.ext
  intro n
  change s.localBrauer.val n = s.localBrauer.val
    (PrimeRegularElement.map (normalizerEquiv W hW).symm.toMonoidHom
      (PrimeRegularElement.map
        (Subgroup.normalizer (W.subgroup : Set G3)).subtype n))
  exact congrArg (fun x : PrimeRegularElement
    (G := Subgroup.normalizer (W.subgroup : Set G3)) 2 => s.localBrauer.val x)
    (Subtype.ext ((normalizerEquiv W hW).symm_apply_apply n.val).symm)

/-- The specified self-induction proof is the selected-row version of the
canonical trivial-block theorem. Its local selector is not a final block map. -/
theorem rawWeightBlock_of_qOne_pullback
    (W : CharacterWeight 2 K G3) (hW : W.subgroup = ⊥)
    (s : CanonicalRawReduction root W) (psi : IBr root)
    (values : s.localBrauer.val = PrimeRegularClassFunction.pullback
      (Subgroup.normalizer (W.subgroup : Set G3)).subtype psi.val)
    (selector : NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
      R.operations W.subgroup s.normalizerRoot s.localBrauer =
      R.operations.inflateToNormalizer W.subgroup
        (R.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero)) :
    letI := R.operations.ambientBlockData.fintypeBlock
    R.operations.rawWeightBlock W = irreducibleBrauerCharacterBlock root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      R.operations.ambientBlockData.blocks psi := by
  let O := R.operations
  letI := O.ambientBlockData.fintypeBlock
  let N := Subgroup.normalizer (W.subgroup : Set G3)
  letI : Fintype N := Fintype.ofFinite N
  letI : Fintype (Subgroup.normalizer (W.subgroup : Set G3)) := Fintype.ofFinite _
  let e : N ≃* G3 := normalizerEquiv W hW
  let localData := O.inflatedNormalizerBlockData W.subgroup
  letI := localData.fintypeBlock
  let injN := irreducibleBrauerCharacterInjectivity_of_rootEmbedding s.normalizerRoot
  let bG := irreducibleBrauerCharacterBlock root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) O.ambientBlockData.blocks psi
  let bL := O.inflateToNormalizer W.subgroup
    (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero)
  have hLocal : irreducibleBrauerCharacterBlock s.normalizerRoot injN
      localData.blocks s.localBrauer = bL := selector
  have hlift : s.normalizerRoot.lift = root.lift := by
    exact (funext (PrimeRegularRootEmbedding.alongMulEquiv_lift s.normalizerRoot e)).symm.trans
      (congrArg (fun r : PrimeRegularRootEmbedding 2 k K G3 => r.lift)
        (normalizerRoot_along root W hW s))
  have hvalues : s.localBrauer.val =
      PrimeRegularClassFunction.pullback e.toMonoidHom psi.val := by
    exact values.trans (congrArg
      (fun f : N →* G3 => PrimeRegularClassFunction.pullback f psi.val)
      (normalizerEquiv_hom W hW).symm)
  have hTransported : irreducibleBrauerCharacterBlock s.normalizerRoot injN
      (O.ambientBlockData.blocks.alongMulEquiv e.symm) s.localBrauer = bG :=
    irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      s.normalizerRoot injN e.symm O.ambientBlockData.blocks psi s.localBrauer hlift hvalues
  have hCatalogue : (O.ambientBlockData.catalogue.alongMulEquiv e.symm).centralCharacter bG =
      localData.catalogue.centralCharacter bL := by
    rw [← hTransported, ← hLocal]
    exact centralCharacter_eq_of_same_IBr s.normalizerRoot injN
      (O.ambientBlockData.blocks.alongMulEquiv e.symm) localData.blocks
      (O.ambientBlockData.catalogue.alongMulEquiv e.symm) localData.catalogue s.localBrauer
  have hSelf := blockInducesTo_self_of_equiv_subtype
    (k := k) (H := N) O.ambientBlockData.blocks O.ambientBlockData.catalogue e
    (normalizerEquiv_hom W hW) bG
  have hActual : BlockInducesTo N localData.catalogue O.ambientBlockData.catalogue bL bG := by
    simpa only [BlockInducesTo, hCatalogue] using hSelf
  exact (eq_inducedBlock_of_blockInducesTo N localData.catalogue
    O.ambientBlockData.catalogue bL (O.blockInductionDefined W) hActual).symm

/-- At one literal index, support is exactly the selector equality. -/
theorem supported_iff_selector (b : LiteralPrimitiveBlock k G3)
    (literalAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
    (psi : IBr root) :
    letI := R.operations.ambientBlockData.fintypeBlock
    Supported root b psi ↔ irreducibleBrauerCharacterBlock root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      R.operations.ambientBlockData.blocks psi = b := by
  letI := R.operations.ambientBlockData.fintypeBlock
  let B := R.operations.ambientBlockData.blocks
  let D := TypeBLiteralBlockReindex.literalBlocks B
  let cls := (simpleModuleClassEquivIBr root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)).symm psi
  let V := Representation.asModule (simpleClassFDRep cls).ρ
  letI : IsSimpleModule k[G3] V :=
    simple_iff_isSimpleModule.mp (simpleClassFDRep_underlying_simple cls)
  have physical : TypeBCentralKernelBrauerBlocks.block root D psi =
      B.primitiveBlockOfIndex (irreducibleBrauerCharacterBlock root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) B psi) := by
    exact primitiveBlockOfIndex_moduleBlock_eq (V := V) D B
  rw [TypeBCentralKernelBrauerBlocks.supported_iff_block root D, physical]
  have hb : B.primitiveBlockOfIndex b = b := Subtype.ext literalAt
  constructor
  · intro h
    exact B.primitiveBlockOfIndex_injective (h.trans hb.symm)
  · intro h
    exact (congrArg B.primitiveBlockOfIndex h).trans hb

/-- Fixed-block literature and specified-source boundary. All raw reduction
and selector guards are restricted to this block, plus its chosen atOne row. -/
structure FixedBlockSource (matrixSource : MatrixExceptionalSource)
    (b : LiteralPrimitiveBlock k G3) (phi : IBr root) where
  d : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3)
  reduction : IsBrauerReduction root d.val phi
  regular_unique : ∀ d' : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3),
    (∀ g : PrimeRegularElement (G := G3) 2, d'.val g.val = d.val g.val) → d' = d
  support : Supported root b phi
  unique : ∀ psi : IBr root, Supported root b psi → psi = phi
  ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val
  atOneReduction : CanonicalRawReduction root ((trivialSource matrixSource).rawAtOne d)
  atOneSelector : NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
    R.operations ((trivialSource matrixSource).rawAtOne d).subgroup
      atOneReduction.normalizerRoot atOneReduction.localBrauer =
    R.operations.inflateToNormalizer ((trivialSource matrixSource).rawAtOne d).subgroup
      (R.operations.localCharacterBlock ((trivialSource matrixSource).rawAtOne d).subgroup
        ((trivialSource matrixSource).rawAtOne d).localCharacter
        ((trivialSource matrixSource).rawAtOne d).defectZero)
  rawTrivial : ∀ W : CharacterWeight 2 K G3,
    R.operations.rawWeightBlock W = b → W.subgroup = ⊥
  rawReduction : ∀ (W : CharacterWeight 2 K G3),
    R.operations.rawWeightBlock W = b → CanonicalRawReduction root W
  rawSelector : ∀ (W : CharacterWeight 2 K G3) (hw : R.operations.rawWeightBlock W = b),
    NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
      R.operations W.subgroup (rawReduction W hw).normalizerRoot (rawReduction W hw).localBrauer =
    R.operations.inflateToNormalizer W.subgroup
      (R.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero)

variable {root R} {matrixSource : MatrixExceptionalSource}
  {b : LiteralPrimitiveBlock k G3} {phi : IBr root}
  (source : FixedBlockSource root R matrixSource b phi)

/-- The prescribed atOne weight has the SAME specified ambient block. -/
theorem atOne_block : R.weightBlock ((trivialSource matrixSource).atOne source.d) = b := by
  letI := R.operations.ambientBlockData.fintypeBlock
  let W := (trivialSource matrixSource).rawAtOne source.d
  have values : source.atOneReduction.localBrauer.val =
      PrimeRegularClassFunction.pullback (Subgroup.normalizer (W.subgroup : Set G3)).subtype
        phi.val := by
    apply PrimeRegularClassFunction.ext
    intro n
    exact (source.atOneReduction.localBrauer_reduction n).symm.trans
      (source.reduction (PrimeRegularElement.map
        (Subgroup.normalizer (W.subgroup : Set G3)).subtype n))
  exact (rawWeightBlock_of_qOne_pullback root R W rfl source.atOneReduction phi
    values source.atOneSelector).trans
    ((supported_iff_selector root R b source.ambientAt phi).mp source.support)

/-- Every supported raw reduction is the pullback of the SAME singleton phi. -/
theorem raw_localBrauer (W : CharacterWeight 2 K G3)
    (hw : R.operations.rawWeightBlock W = b) :
    (source.rawReduction W hw).localBrauer.val = PrimeRegularClassFunction.pullback
      (Subgroup.normalizer (W.subgroup : Set G3)).subtype phi.val := by
  letI := R.operations.ambientBlockData.fintypeBlock
  let s := source.rawReduction W hw
  let psi := globalBrauer root W (source.rawTrivial W hw) s
  have block := rawWeightBlock_of_qOne_pullback root R W (source.rawTrivial W hw)
    s psi (globalBrauer_pullback root W (source.rawTrivial W hw) s) (source.rawSelector W hw)
  have supported : Supported root b psi :=
    (supported_iff_selector root R b source.ambientAt psi).mpr (block.symm.trans hw)
  have same := source.unique psi supported
  exact (globalBrauer_pullback root W (source.rawTrivial W hw) s).trans
    (congrArg (fun x : IBr root => PrimeRegularClassFunction.pullback
      (Subgroup.normalizer (W.subgroup : Set G3)).subtype x.val) same)

include source in
/-- This is the literal value anchor consumed by the Q=1 extension proof. -/
theorem raw_local_anchor (W : CharacterWeight 2 K G3)
    (hw : R.operations.rawWeightBlock W = b) :
    W.subgroup = ⊥ ∧
      ∀ n : PrimeRegularElement (G := Subgroup.normalizer (W.subgroup : Set G3)) 2,
        phi.val (PrimeRegularElement.map
          (Subgroup.normalizer (W.subgroup : Set G3)).subtype n) =
        W.localCharacter (QuotientGroup.mk n.val) := by
  refine ⟨source.rawTrivial W hw, ?_⟩
  intro n
  have values := congrArg (fun f => f n) (raw_localBrauer source W hw)
  exact values.symm.trans ((source.rawReduction W hw).localBrauer_reduction n).symm

/-- Extract the ordinary character from a raw Q=1 row, retaining its values. -/
theorem exists_atOne_from_raw (W : CharacterWeight 2 K G3) (hQ : W.subgroup = ⊥) :
    ∃ d : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3),
      (trivialSource matrixSource).atOne d =
        (Quotient.mk'' (Quotient.mk'' W) : ConjugacyClass (p := 2) (K := K) (G := G3)) ∧
      ∀ n : Subgroup.normalizer (W.subgroup : Set G3),
        W.localCharacter (QuotientGroup.mk n) = d.val n.val := by
  rcases W with ⟨hprime, Q, hradical, chi, hdefect⟩
  change Q = ⊥ at hQ
  subst Q
  let e : NormalizerQuotient (⊥ : Subgroup G3) ≃* G3 := trivialNormalizerQuotientEquiv
  let d : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3) :=
    ⟨OrdinaryIrreducibleCharacter.mapEquiv chi e, hdefect.mapEquiv e⟩
  refine ⟨d, ?_, ?_⟩
  · apply congrArg Quotient.mk''
    apply Quotient.sound
    refine ⟨rfl, ?_⟩
    change OrdinaryIrreducibleCharacter.mapEquiv
      (OrdinaryIrreducibleCharacter.mapEquiv chi e) e.symm = chi
    rw [OrdinaryIrreducibleCharacter.mapEquiv_trans, MulEquiv.self_trans_symm,
      OrdinaryIrreducibleCharacter.mapEquiv_refl]
  · intro n
    change chi (QuotientGroup.mk n) = chi (trivialNormalizerQuotientEquiv.symm n.val)
    rw [trivialNormalizerQuotientEquiv_symm_apply]
    rfl

/-- Arbitrary supported raw rows belong to the selected atOne class. -/
theorem raw_class_eq_atOne (W : CharacterWeight 2 K G3)
    (hw : R.operations.rawWeightBlock W = b) :
    (Quotient.mk'' (Quotient.mk'' W) : ConjugacyClass (p := 2) (K := K) (G := G3)) =
      (trivialSource matrixSource).atOne source.d := by
  obtain ⟨hQ, anchor⟩ := raw_local_anchor source W hw
  obtain ⟨d', same, values⟩ := exists_atOne_from_raw (matrixSource := matrixSource) W hQ
  have hd : d' = source.d := by
    apply source.regular_unique
    intro g
    let n := PrimeRegularElement.map (normalizerEquiv W hQ).symm.toMonoidHom g
    have hn : PrimeRegularElement.map
        (Subgroup.normalizer (W.subgroup : Set G3)).subtype n = g := by
      apply Subtype.ext
      change (normalizerEquiv W hQ) ((normalizerEquiv W hQ).symm g.val) = g.val
      exact (normalizerEquiv W hQ).apply_symm_apply g.val
    have val := (anchor n).trans (values n.val)
    rw [hn] at val
    have hng : n.val.val = g.val := congrArg Subtype.val hn
    rw [hng] at val
    exact val.symm.trans (source.reduction g).symm
  exact same.symm.trans (congrArg (trivialSource matrixSource).atOne hd)

theorem weight_eq_atOne (w : R.Fibre b) :
    w.val = (trivialSource matrixSource).atOne source.d := by
  obtain ⟨iso, hiso⟩ := Quotient.exists_rep w.val
  obtain ⟨W, hW⟩ := Quotient.exists_rep iso
  have same : (Quotient.mk'' (Quotient.mk'' W) :
      ConjugacyClass (p := 2) (K := K) (G := G3)) = w.val :=
    (congrArg (fun t : CharacterWeight.IsoClass (p := 2) (K := K) (G := G3) =>
      (Quotient.mk'' t : ConjugacyClass (p := 2) (K := K) (G := G3))) hW).trans hiso
  have hw : R.operations.rawWeightBlock W = b := by
    change R.weightBlock (Quotient.mk'' (Quotient.mk'' W)) = b
    rw [same]
    exact w.property
  exact same.symm.trans (raw_class_eq_atOne source W hw)

/-- The complete matching uses the actual selected atOne weight. -/
def fixedBlockEquiv : BrauerFibre root b ≃ R.Fibre b where
  toFun _ := ⟨(trivialSource matrixSource).atOne source.d, atOne_block source⟩
  invFun _ := ⟨phi, source.support⟩
  left_inv psi := Subtype.ext (source.unique psi.val psi.property).symm
  right_inv w := Subtype.ext (weight_eq_atOne source w).symm

/-- The singleton proof applies after the actual automorphism is shown to
stabilize this specified block; no all-character fixedness premise is used. -/
theorem fixedBlockEquiv_graph :
    ∀ (alpha : (MulAut G3)ᵐᵒᵖ) (psi chi : BrauerFibre root b),
      chi.val = alpha • psi.val →
        (fixedBlockEquiv source chi).val = alpha • (fixedBlockEquiv source psi).val := by
  letI := R.operations.ambientBlockData.fintypeBlock
  let D := TypeBLiteralBlockReindex.literalBlocks R.operations.ambientBlockData.blocks
  intro alpha psi chi values
  have hpsi := (TypeBCentralKernelBrauerBlocks.supported_iff_block root D b psi.val).mp psi.property
  have hchi := (TypeBCentralKernelBrauerBlocks.supported_iff_block root D b chi.val).mp chi.property
  have twisted := TypeBCentralKernelBrauerBlocks.block_twist root D alpha.unop psi.val
  change TypeBCentralKernelBrauerBlocks.block root D (alpha • psi.val) =
    LiteralPrimitiveBlock.rightTwistBlock (TypeBCentralKernelBrauerBlocks.block root D psi.val)
      alpha.unop at twisted
  rw [← values, hpsi, hchi] at twisted
  let actor : MulAction.stabilizer (MulAut G3)ᵐᵒᵖ b := ⟨alpha, by
    change LiteralPrimitiveBlock.rightTwistBlock b alpha.unop = b
    exact twisted.symm⟩
  let w : R.Fibre b := actor • fixedBlockEquiv source psi
  calc
    (fixedBlockEquiv source chi).val = w.val :=
      (weight_eq_atOne source (fixedBlockEquiv source chi)).trans
        (weight_eq_atOne source w).symm
    _ = alpha • (fixedBlockEquiv source psi).val :=
      R.fibre_smul_val b actor (fixedBlockEquiv source psi)

end ModularRep.PaperProofs.TypeBQ3B45DefectZeroMatching


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
