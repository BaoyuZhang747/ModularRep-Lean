import ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
import ModularRep.BrauerQuotientLinearCharacterAction

/-!
# Equality candidates adjacent to FLZ 3.18(iii)

This module constructs the equality candidates suggested by the specialisation
of Feng--Li--Zhang, Theorem 3.18(iii), in which the regular overgroup is the
group itself and the group is centreless.  The fibres below are defined by
equality of the literal function-valued Brauer characters and equality of the
literal character-weight conjugacy classes.  They are the uniquely forced
equal-group candidates on the carriers already used for manuscript Lemma 2.10.

The module proves in the kernel that:

* the ordinary linear character group of the quotient `H / H` is trivial;
* the literal Brauer restriction fibre and the weight equality-candidate fibre
  are singletons;
* the centreless central character fibres, defined by literal restriction
  formulas, are the whole corresponding block fibres;
* every inner stabiliser of a Brauer character is the whole group;
* the selected local character has a chosen identity extension to the same
  normaliser quotient; and
* the inflated block of that chosen extension literally induces to the block
  of the equal-group Clifford correspondent.

Several source identifications remain outside this module: the source ordinary
`Lin_{ell'}` carrier, reduction from ordinary linear characters to `LinBr`,
the source restriction fibres and the passage `nu` to `nu^0`, the source
definition of the central character fibre for weights, the DGN covering
relation, the Clifford correspondence, induction of the chosen local
extension, and the map `Delta_phi`.  The DGN and `Delta_phi` identifications
are deep cited input, not routine consequences of the carrier definitions.
This module therefore does not claim any part of FLZ 3.18(iii) itself, invoke
that theorem, or conclude BAW-goodness or iBAW.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverEqualGroupClauseIII

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover

universe u

section QuotientLinearCharacters

variable {K H : Type u} [Field K] [Group H]

/-- A characteristic-zero homomorphism model for ordinary linear characters
of `H` that factor through the self-cover quotient `H / H`.  Identifying it
with the source carrier `Lin_{ell'}(G_tilde/G)` remains a source adapter.  The
prime-to-`ell` qualification is automatic because the quotient is trivial. -/
abbrev SelfCoverOrdinaryQuotientLinearCharacters [CharZero K] :=
  linearCharactersTrivialOn (k := K) (⊤ : Subgroup H)

variable [CharZero K]

/-- Canonical passage from the pullback description to homomorphisms on the
literal quotient `H / H`. -/
def selfCoverOrdinaryQuotientLinearCharactersEquiv :
    SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H) ≃*
      (H ⧸ (⊤ : Subgroup H) →* Kˣ) :=
  LinearCharactersTrivialOn.quotientMulEquiv
    (k := K) (⊤ : Subgroup H)

/-- Every ordinary linear character of the quotient `H / H` is trivial. -/
theorem selfCoverOrdinaryQuotientLinearCharacter_eq_one
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H)) :
    lambda = 1 := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro h
  exact lambda.2 (Subgroup.mem_top h)

/-- The ordinary quotient linear character group in clause (iii) is a
singleton in the self-cover specialisation. -/
instance selfCoverOrdinaryQuotientLinearCharacters_subsingleton :
    Subsingleton
      (SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H)) where
  allEq lambda mu := by
    rw [selfCoverOrdinaryQuotientLinearCharacter_eq_one lambda,
      selfCoverOrdinaryQuotientLinearCharacter_eq_one mu]

/-- The ordinary quotient linear character factor acts trivially in every
action because it has only its identity element. -/
theorem selfCoverOrdinaryQuotientLinearCharacter_smul
    {X : Type u}
    [MulAction
      (SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H)) X]
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H))
    (x : X) : lambda • x = x := by
  rw [selfCoverOrdinaryQuotientLinearCharacter_eq_one lambda, one_smul]

end QuotientLinearCharacters

section EqualGroupCoveringFibres

variable {p : ℕ} {k K H ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)

/-- Literal restriction in the equal-group case: the two function-valued
Brauer characters agree. -/
def SameGroupBrauerRestriction
    (psiTilde psi : BrauerFibre iota hinj blocks block) : Prop :=
  psiTilde.1.1 = psi.1.1

/-- Equality of the literal characters is equivalent to equality in the
block fibre. -/
theorem sameGroupBrauerRestriction_iff_eq
    (psiTilde psi : BrauerFibre iota hinj blocks block) :
    SameGroupBrauerRestriction iota hinj blocks block psiTilde psi ↔
      psiTilde = psi := by
  constructor
  · intro h
    apply Subtype.ext
    exact Subtype.ext h
  · intro h
    subst psiTilde
    rfl

/-- The literal equal-group Brauer restriction fibre. -/
def SameGroupBrauerCoveringFibre
    (psi : BrauerFibre iota hinj blocks block) :
    Set (BrauerFibre iota hinj blocks block) :=
  {psiTilde | SameGroupBrauerRestriction
    iota hinj blocks block psiTilde psi}

/-- The equality candidate for covering weights in the equal-group case. -/
def SameGroupWeightCoveringCandidate
    (wTilde w : WeightFibre blockSource block) : Prop :=
  wTilde.1 = w.1

/-- Equal-group covering of literal weight classes is equality in the block
fibre. -/
theorem sameGroupWeightCoveringCandidate_iff_eq
    (wTilde w : WeightFibre blockSource block) :
    SameGroupWeightCoveringCandidate blockSource block wTilde w ↔
      wTilde = w := by
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    subst wTilde
    rfl

/-- The uniquely forced equal-group candidate for the weight covering
fibre.  Its identification with the source DGN covering relation remains
external. -/
def SameGroupWeightCoveringCandidateFibre
    (w : WeightFibre blockSource block) :
    Set (WeightFibre blockSource block) :=
  {wTilde | SameGroupWeightCoveringCandidate blockSource block wTilde w}

/-- Restricting a Brauer character from `H` to the same group gives a
singleton covering fibre. -/
theorem sameGroupBrauerCoveringFibre_eq_singleton
    (psi : BrauerFibre iota hinj blocks block) :
    SameGroupBrauerCoveringFibre iota hinj blocks block psi = {psi} := by
  ext psiTilde
  simp only [SameGroupBrauerCoveringFibre, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  exact sameGroupBrauerRestriction_iff_eq
    iota hinj blocks block psiTilde psi

/-- The weight equality-candidate fibre is a singleton. -/
theorem sameGroupWeightCoveringCandidateFibre_eq_singleton
    (w : WeightFibre blockSource block) :
    SameGroupWeightCoveringCandidateFibre blockSource block w = {w} := by
  ext wTilde
  simp only [SameGroupWeightCoveringCandidateFibre, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  exact sameGroupWeightCoveringCandidate_iff_eq blockSource block wTilde w

/-- Any literal blockwise bijection carries the equal-group Brauer
restriction fibre to the uniquely forced equality candidate on weights. -/
theorem sameGroupCoveringCandidateFibre_image
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (psi : BrauerFibre iota hinj blocks block) :
    omega '' SameGroupBrauerCoveringFibre
        iota hinj blocks block psi =
      SameGroupWeightCoveringCandidateFibre blockSource block (omega psi) := by
  rw [sameGroupBrauerCoveringFibre_eq_singleton,
    sameGroupWeightCoveringCandidateFibre_eq_singleton]
  exact Set.image_singleton

end EqualGroupCoveringFibres

section CentrelessCentralFibres

variable {p : ℕ} {k K H ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)

/-- The unique `p`-regular element represented by an element of a trivial
centre. -/
def centrePrimeRegularElement
    (hcenter : Subgroup.center H = ⊥) (z : Subgroup.center H) :
    PrimeRegularElement (G := H) p := by
  have hz : (z : H) = 1 := by
    have : (z : H) ∈ (⊥ : Subgroup H) := by
      rw [← hcenter]
      exact z.property
    simpa using this
  exact ⟨z, by simpa [hz] using (isPrimeRegular_one (p := p) (G := H))⟩

/-- A Brauer character lies over an ordinary linear character of the centre
when its literal central restriction is its degree multiple of that linear
character.  This formula is used only in the centreless case, where every
central element is `1`. -/
def SameGroupBrauerLiesOver
    (hcenter : Subgroup.center H = ⊥)
    (nu : Subgroup.center H →* Kˣ)
    (psi : BrauerFibre iota hinj blocks block) : Prop :=
  ∀ z : Subgroup.center H,
    psi.1.1 (centrePrimeRegularElement (p := p) hcenter z) =
      psi.1.1 ⟨1, isPrimeRegular_one⟩ * (nu z : K)

/-- In a centreless group every literal Brauer character lies over the
unique central linear character. -/
theorem sameGroupBrauerLiesOver_of_centerless
    (hcenter : Subgroup.center H = ⊥)
    (nu : Subgroup.center H →* Kˣ)
    (psi : BrauerFibre iota hinj blocks block) :
    SameGroupBrauerLiesOver iota hinj blocks block hcenter nu psi := by
  intro z
  have hz : z = 1 := by
    apply Subtype.ext
    have hzbot : (z : H) ∈ (⊥ : Subgroup H) := by
      rw [← hcenter]
      exact z.property
    simpa using hzbot
  subst z
  simp [centrePrimeRegularElement]

/-- The centre maps naturally to the local normaliser quotient.  Under
centrelessness this is the unique map, but its value is expressed through
the actual quotient map. -/
def centreToNormalizerQuotient
    (hcenter : Subgroup.center H = ⊥) (Q : Subgroup H) :
    Subgroup.center H →* NormalizerQuotient Q := by
  let centreToNormalizer : Subgroup.center H →*
      Subgroup.normalizer (Q : Set H) :=
    { toFun := fun z ↦ ⟨z.1, by
        have hz : (z : H) = 1 := by
          have hzbot : (z : H) ∈ (⊥ : Subgroup H) := by
            rw [← hcenter]
            exact z.property
          simpa using hzbot
        simpa [hz] using
          (Subgroup.one_mem (Subgroup.normalizer (Q : Set H)))⟩
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' := fun z w ↦ by
        apply Subtype.ext
        rfl }
  exact (QuotientGroup.mk' (Q.subgroupOf
    (Subgroup.normalizer (Q : Set H)))).comp centreToNormalizer

/-- A literal weight lies over `nu` when the inflation of its selected local
character has the corresponding restriction to the centre.  Evaluation
through `centreToNormalizerQuotient` is precisely inflation followed by
restriction. -/
def SameGroupWeightLiesOver
    (hcenter : Subgroup.center H = ⊥)
    (nu : Subgroup.center H →* Kˣ)
    (w : WeightFibre blockSource block) : Prop :=
  let W := selectedCharacterWeight blockSource block w
  ∀ z : Subgroup.center H,
    W.localCharacter
        (centreToNormalizerQuotient hcenter W.subgroup z) =
      W.localCharacter 1 * (nu z : K)

/-- In a centreless group every literal weight lies over the unique central
linear character. -/
theorem sameGroupWeightLiesOver_of_centerless
    (hcenter : Subgroup.center H = ⊥)
    (nu : Subgroup.center H →* Kˣ)
    (w : WeightFibre blockSource block) :
    SameGroupWeightLiesOver blockSource block hcenter nu w := by
  intro z
  have hz : z = 1 := by
    apply Subtype.ext
    have hzbot : (z : H) ∈ (⊥ : Subgroup H) := by
      rw [← hcenter]
      exact z.property
    simpa using hzbot
  subst z
  change
    (selectedCharacterWeight blockSource block w).localCharacter
        (centreToNormalizerQuotient hcenter
          (selectedCharacterWeight blockSource block w).subgroup 1) =
      (selectedCharacterWeight blockSource block w).localCharacter 1 *
        ((nu 1 : Kˣ) : K)
  rw [map_one, map_one]
  simp

/-- The literal Brauer central character fibre in the centreless
specialisation. -/
def SameGroupBrauerCentralFibre
    (hcenter : Subgroup.center H = ⊥)
    (nu : Subgroup.center H →* Kˣ) :
    Set (BrauerFibre iota hinj blocks block) :=
  {psi | SameGroupBrauerLiesOver
    iota hinj blocks block hcenter nu psi}

/-- The literal weight central character fibre in the centreless
specialisation. -/
def SameGroupWeightCentralFibre
    (hcenter : Subgroup.center H = ⊥)
    (nu : Subgroup.center H →* Kˣ) :
    Set (WeightFibre blockSource block) :=
  {w | SameGroupWeightLiesOver blockSource block hcenter nu w}

/-- The literal Brauer central character fibre is the whole block fibre. -/
theorem sameGroupBrauerCentralFibre_eq_univ
    (hcenter : Subgroup.center H = ⊥)
    (nu : Subgroup.center H →* Kˣ) :
    SameGroupBrauerCentralFibre
      iota hinj blocks block hcenter nu = Set.univ := by
  ext psi
  simp only [SameGroupBrauerCentralFibre, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]
  exact sameGroupBrauerLiesOver_of_centerless
    iota hinj blocks block hcenter nu psi

/-- The literal weight central character fibre is the whole block fibre. -/
theorem sameGroupWeightCentralFibre_eq_univ
    (hcenter : Subgroup.center H = ⊥)
    (nu : Subgroup.center H →* Kˣ) :
    SameGroupWeightCentralFibre
      blockSource block hcenter nu = Set.univ := by
  ext w
  simp only [SameGroupWeightCentralFibre, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]
  exact sameGroupWeightLiesOver_of_centerless
    blockSource block hcenter nu w

/-- Any literal blockwise bijection carries the centreless central character
fibre candidates on Brauer characters to the corresponding weight fibre
candidate.  Identifying these predicates with the source fibres remains an
external source adapter. -/
theorem sameGroupCentralFibre_image
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (hcenter : Subgroup.center H = ⊥)
    (nu : Subgroup.center H →* Kˣ) :
    omega '' SameGroupBrauerCentralFibre
        iota hinj blocks block hcenter nu =
      SameGroupWeightCentralFibre
        blockSource block hcenter nu := by
  rw [sameGroupBrauerCentralFibre_eq_univ,
    sameGroupWeightCentralFibre_eq_univ]
  exact Set.image_univ_of_surjective omega.surjective

end CentrelessCentralFibres

section ClauseIIIc

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (phi : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)
variable (T : FibreTransportSource iota hinj blocks phi block)

/-- The stabiliser under inner automorphisms of any literal Brauer character
in the block is the whole self-cover. -/
theorem sameGroupBrauerInnerStabilizer_eq_top
    (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    MulAction.stabilizer H psi = ⊤ := by
  dsimp only
  letI : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (FibreTransportSource.innerBlock_fixed
        (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  apply top_unique
  intro h _
  exact FibreTransportSource.inner_fixes_brauerFibre
    (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
    (blockSource := blockSource) (block := block) (T := T) h psi

/-- Every element of the normaliser fixes the selected local character under
the induced inner action on `N_H(Q) / Q`.  Thus its local character
stabiliser is the whole normaliser in the self-cover case. -/
theorem selectedLocalCharacter_normalizer_conjugation_fixed
    (w : WeightFibre blockSource block)
    (n x : Subgroup.normalizer
      ((selectedCharacterWeight blockSource block w).subgroup : Set H)) :
    let Q := (selectedCharacterWeight blockSource block w).subgroup
    let QN := Q.subgroupOf (Subgroup.normalizer (Q : Set H))
    let chi := (selectedCharacterWeight blockSource block w).localCharacter
    chi (QuotientGroup.mk' QN n * QuotientGroup.mk' QN x *
        (QuotientGroup.mk' QN n)⁻¹) =
      chi (QuotientGroup.mk' QN x) := by
  dsimp only
  exact ordinaryCharacter_conj
    (selectedCharacterWeight blockSource block w).localCharacter
    (QuotientGroup.mk' _ n) (QuotientGroup.mk' _ x)

/-- A chosen ordinary character extension in the equal-group case.  The
extended character is retained as data because induction, `Delta`, and block
induction in FLZ 3.18(iii)(c) must all refer to this same choice. -/
structure SameGroupLocalCharacterExtensionData
    (w : WeightFibre blockSource block) where
  extendedCharacter : OrdinaryIrreducibleCharacter.Irr K
    (NormalizerQuotient
      (selectedCharacterWeight blockSource block w).subgroup)
  extendedCharacter_eq : extendedCharacter =
    (selectedCharacterWeight blockSource block w).localCharacter
  realisation : OrdinaryIrreducibleCharacter.Realisation K
    (NormalizerQuotient
      (selectedCharacterWeight blockSource block w).subgroup)
    extendedCharacter.1
  extension : Representation.Extension
    (⊤ : Subgroup (NormalizerQuotient
      (selectedCharacterWeight blockSource block w).subgroup))
    (Representation.pullback realisation.representation
      (⊤ : Subgroup (NormalizerQuotient
        (selectedCharacterWeight blockSource block w).subgroup)).subtype)

/-- The chosen identity extension of the selected local character. -/
def sameGroupLocalCharacterExtensionData
    (w : WeightFibre blockSource block) :
    SameGroupLocalCharacterExtensionData blockSource block w := by
  let R := Classical.choice
    (selectedCharacterWeight blockSource block w).localCharacter.2
  exact {
    extendedCharacter :=
      (selectedCharacterWeight blockSource block w).localCharacter
    extendedCharacter_eq := rfl
    realisation := R
    extension := identityExtension R.representation
  }

/-- Compatibility wrapper retaining the former proposition-valued API. -/
def SameGroupLocalCharacterExtension
    (w : WeightFibre blockSource block) : Prop :=
  Nonempty (SameGroupLocalCharacterExtensionData blockSource block w)

/-- The proposition-valued form of the actual identity extension. -/
theorem sameGroupLocalCharacterExtension
    (w : WeightFibre blockSource block) :
    SameGroupLocalCharacterExtension blockSource block w :=
  ⟨sameGroupLocalCharacterExtensionData blockSource block w⟩

/-- The chosen extended character remains defect zero. -/
theorem sameGroupLocalCharacterExtensionData_defectZero
    (w : WeightFibre blockSource block)
    (extensionData :
      SameGroupLocalCharacterExtensionData blockSource block w) :
    IsDefectZeroOrdinaryCharacter p extensionData.extendedCharacter := by
  rw [extensionData.extendedCharacter_eq]
  exact (selectedCharacterWeight blockSource block w).defectZero

/-- The inflated normaliser block belonging to the chosen extension. -/
def sameGroupLocalCharacterExtensionInflatedBlock
    (w : WeightFibre blockSource block)
    (extensionData :
      SameGroupLocalCharacterExtensionData blockSource block w) :
    InflatedNormalizerBlock (k := k)
      (selectedCharacterWeight blockSource block w).subgroup :=
  blockSource.operations.inflateToNormalizer
    (selectedCharacterWeight blockSource block w).subgroup
    (blockSource.operations.localCharacterBlock
      (selectedCharacterWeight blockSource block w).subgroup
      extensionData.extendedCharacter
      (sameGroupLocalCharacterExtensionData_defectZero
        blockSource block w extensionData))

/-- Literal block induction from the inflated block of the chosen extension
to the block of the equal-group Clifford correspondent. -/
def SameGroupLocalExtensionBlockInducesTo
    (w : WeightFibre blockSource block)
    (extensionData :
      SameGroupLocalCharacterExtensionData blockSource block w)
    (hatPsi : BrauerFibre iota hinj blocks block) : Prop :=
  let W := selectedCharacterWeight blockSource block w
  let O := blockSource.operations
  let targetBlock :=
    irreducibleBrauerCharacterBlock iota hinj blocks hatPsi.1
  let localData := O.inflatedNormalizerBlockData W.subgroup
  letI : Fintype ι := O.ambientBlockData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    localData.fintypeBlock
  ModularRep.BlockInducesTo
    (Subgroup.normalizer (W.subgroup : Set H))
    localData.catalogue O.ambientBlockData.catalogue
    (sameGroupLocalCharacterExtensionInflatedBlock
      blockSource block w extensionData)
    targetBlock

/-- In the equal-group case, the block of the chosen identity extension
literally induces to the block containing the Clifford correspondent. -/
theorem sameGroupLocalExtensionBlockInducesTo
    (w : WeightFibre blockSource block)
    (extensionData :
      SameGroupLocalCharacterExtensionData blockSource block w)
    (hatPsi : BrauerFibre iota hinj blocks block) :
    SameGroupLocalExtensionBlockInducesTo iota hinj blocks blockSource block
      w extensionData hatPsi := by
  let W := selectedCharacterWeight blockSource block w
  let O := blockSource.operations
  let targetBlock :=
    irreducibleBrauerCharacterBlock iota hinj blocks hatPsi.1
  let localData := O.inflatedNormalizerBlockData W.subgroup
  letI : Fintype ι := O.ambientBlockData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    localData.fintypeBlock
  let extensionBlock := sameGroupLocalCharacterExtensionInflatedBlock
    blockSource block w extensionData
  have extensionBlock_eq : extensionBlock =
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero) := by
    dsimp only [extensionBlock,
      sameGroupLocalCharacterExtensionInflatedBlock, W, O]
    simpa only [extensionData.extendedCharacter_eq]
  have inducedBlock_eq :
      O.induceToAmbient W = targetBlock := by
    calc
      O.induceToAmbient W = O.rawWeightBlock W := rfl
      _ = block := selectedCharacterWeight_block blockSource block w
      _ = targetBlock := by
        simpa only [targetBlock] using hatPsi.2.symm
  change ModularRep.BlockInducesTo
    (Subgroup.normalizer (W.subgroup : Set H))
    localData.catalogue O.ambientBlockData.catalogue extensionBlock
    targetBlock
  rw [extensionBlock_eq, ← inducedBlock_eq]
  exact ModularRep.inducedBlock_spec
    (Subgroup.normalizer (W.subgroup : Set H))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer W.subgroup
      (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
    (O.blockInductionDefined W)

/-- Equality candidate for the Clifford correspondent when the ambient group
and the normal subgroup are the same literal group. -/
def SameGroupCliffordCorrespondentCandidate
    (hatPsi psiTilde : BrauerFibre iota hinj blocks block) : Prop :=
  hatPsi.1.1 = psiTilde.1.1

/-- The equal-group Clifford equality candidate holds exactly when the two
characters are equal. -/
theorem sameGroupCliffordCorrespondentCandidate_iff_eq
    (hatPsi psiTilde : BrauerFibre iota hinj blocks block) :
    SameGroupCliffordCorrespondentCandidate
        iota hinj blocks block hatPsi psiTilde ↔
      hatPsi = psiTilde := by
  constructor
  · intro h
    apply Subtype.ext
    exact Subtype.ext h
  · intro h
    subst hatPsi
    rfl

/-- Equality candidate for the result of induction and the DGN map in the
equal-group specialisation.  Matching the source operation `Delta_phi` with
this relation remains a source-semantic adapter. -/
def SameGroupDeltaInductionCandidate
    (hatWeight liftedWeight : CharacterWeight p K H) : Prop :=
  hatWeight = liftedWeight

/-- Literal equality-candidate data obtained from clause (ii)'s already
constructed bijection.  The chosen local extension is data, and the induction
and `Delta` candidates form a chain starting from that choice.  Identifying
the candidates with the source restriction, Clifford, induction, and DGN
operations remains external. -/
structure EqualGroupClauseIIIcCarrierCandidateData
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (psi : BrauerFibre iota hinj blocks block) where
  liftedBrauer : BrauerFibre iota hinj blocks block
  liftedBrauer_restrictionCandidate : SameGroupBrauerRestriction
    iota hinj blocks block liftedBrauer psi
  cliffordCandidate : BrauerFibre iota hinj blocks block
  cliffordCandidate_spec : SameGroupCliffordCorrespondentCandidate
    iota hinj blocks block cliffordCandidate liftedBrauer
  liftedWeight : CharacterWeight p K H
  liftedWeight_spec :
    (Quotient.mk'' (Quotient.mk'' liftedWeight) :
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H)) =
        (omega liftedBrauer).1
  localCharacterExtension : SameGroupLocalCharacterExtensionData
    blockSource block (omega psi)
  inducedWeight : CharacterWeight p K H
  inducedWeight_spec : inducedWeight =
    selectedCharacterWeight blockSource block (omega psi)
  deltaInduction_spec : SameGroupDeltaInductionCandidate
    liftedWeight inducedWeight

/-- Construction of the literal carrier candidate adjacent to
FLZ 3.18(iii)(c).  The identity extension and the two identity-operation
candidates are selected without assuming a block conclusion. -/
def equalGroupClauseIIIcCarrierCandidateData
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (psi : BrauerFibre iota hinj blocks block) :
    EqualGroupClauseIIIcCarrierCandidateData
      iota hinj blocks blockSource block omega psi where
  liftedBrauer := psi
  liftedBrauer_restrictionCandidate := rfl
  cliffordCandidate := psi
  cliffordCandidate_spec := rfl
  liftedWeight := selectedCharacterWeight blockSource block (omega psi)
  liftedWeight_spec := selectedCharacterWeight_spec blockSource block (omega psi)
  localCharacterExtension :=
    sameGroupLocalCharacterExtensionData blockSource block (omega psi)
  inducedWeight :=
    selectedCharacterWeight blockSource block (omega psi)
  inducedWeight_spec := rfl
  deltaInduction_spec := rfl

/-- Clause (ii)'s protected equivalence supplies the equal-group clause
(iii)(c) data without an additional equivalence input. -/
def equalGroupClauseIIIcCarrierCandidateData_of_cyclicEndgame
    (localReduction : ∀ w : LiteralWeightFibre blockSource block,
      SelectedLocalReductionSource blockSource block w)
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction)
    (psi : BrauerFibre iota hinj blocks block) :
    EqualGroupClauseIIIcCarrierCandidateData iota hinj blocks blockSource block
      endgame.omega.toEquiv psi :=
  equalGroupClauseIIIcCarrierCandidateData iota hinj blocks blockSource block
    endgame.omega.toEquiv psi

/-- The clause-(iii) equal-group candidate derived from the protected cyclic
endgame.  Parts (a) and (b) are literal fibre equalities.  Part (c) contains
the chosen identity extension and the induction and DGN equality candidates
whose match with the source operations is still external. -/
structure EqualGroupClauseIIICandidate
    (hcenter : Subgroup.center H = ⊥)
    (localReduction : ∀ w : LiteralWeightFibre blockSource block,
      SelectedLocalReductionSource blockSource block w)
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction) where
  covering_fibres : ∀ psi : BrauerFibre iota hinj blocks block,
    endgame.omega.toEquiv ''
        SameGroupBrauerCoveringFibre iota hinj blocks block psi =
      SameGroupWeightCoveringCandidateFibre blockSource block
        (endgame.omega.toEquiv psi)
  central_character_fibres :
    ∀ nu : Subgroup.center H →* Kˣ,
      endgame.omega.toEquiv ''
          SameGroupBrauerCentralFibre
            iota hinj blocks block hcenter nu =
        SameGroupWeightCentralFibre
          blockSource block hcenter nu
  block_and_identity_data :
    ∀ psi : BrauerFibre iota hinj blocks block,
      EqualGroupClauseIIIcCarrierCandidateData
        iota hinj blocks blockSource block
        endgame.omega.toEquiv psi

/-- Construct the equal-group clause-(iii) candidate from the already
protected cyclic endgame, without a new equivalence or conclusion premise. -/
def equalGroupClauseIIICandidate_of_cyclicEndgame
    (hcenter : Subgroup.center H = ⊥)
    (localReduction : ∀ w : LiteralWeightFibre blockSource block,
      SelectedLocalReductionSource blockSource block w)
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction) :
    EqualGroupClauseIIICandidate iota hinj blocks phi blockSource block T
      hcenter localReduction endgame where
  covering_fibres := fun psi ↦
    sameGroupCoveringCandidateFibre_image iota hinj blocks blockSource block
      endgame.omega.toEquiv psi
  central_character_fibres := fun nu ↦
    sameGroupCentralFibre_image iota hinj blocks blockSource block
      endgame.omega.toEquiv hcenter nu
  block_and_identity_data := fun psi ↦
    equalGroupClauseIIIcCarrierCandidateData_of_cyclicEndgame
      iota hinj blocks phi blockSource block T localReduction endgame psi

end ClauseIIIc

end ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverEqualGroupClauseIII


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
