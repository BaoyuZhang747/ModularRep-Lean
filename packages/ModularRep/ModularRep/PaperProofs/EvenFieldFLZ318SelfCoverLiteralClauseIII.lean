import ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
import ModularRep.BrauerQuotientLinearCharacterAction
import ModularRep.BlockIdempotentDecomposition

/-!
# A centreless self-cover carrier model adjacent to FLZ 3.18(iii)

This module replaces the abstract carrier models in
`EvenFieldFLZ318SelfCover` by existing Brauer- and weight-block fibres.  It
formalises only the carrier-level identities suggested by setting a regular
overgroup equal to `H` and assuming `Z(H) = 1`.  In that model:

* modular homomorphisms on `H` trivial on `top` form a subsingleton group and
  are canonically equivalent to homomorphisms on the actual quotient
  `H / top`;
* the semidirect carrier acts through its projection to `E`; no comparison
  with the source tensor actions is asserted;
* model restriction and projection maps are identities, so their equation
  fibres are singletons;
* ordinary and modular centre-label carriers are homomorphism types on
  `Z(H)` and become subsingletons under centrelessness; and
* modular block-sector labels are formed with
  `BlockIdempotentDecomposition.centralCharacterSector`, on the weight side
  after `LocalBlockInductionSource.weightBlock`.

The word "model" is essential.  The declarations below do not identify the
quotient homomorphisms with Feng--Li--Zhang's ordinary `Lin` carrier, the
projected actions with the source tensor-and-field actions, the identity maps
with character restriction or covering of weights, or the model centre-label
map with ordinary-to-Brauer reduction.  They also do not construct a Clifford
correspondent, an extension, induction, or a Delta/DGN correspondent.  Those
representation- and block-theoretic identifications remain external.

Consequently, no declaration in this module is an instance or verification
of FLZ 3.18(iii).  The module invokes neither that theorem nor a BAW or iBAW
conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverLiteralClauseIII

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge

universe u

section QuotientLinearCharacters

variable {k H E : Type u}
variable [Field k] [Group H] [Group E]

/-- Pullback model for modular homomorphisms on the self-cover quotient:
homomorphisms on `H` that are trivial on the whole subgroup. -/
abbrev SelfCoverQuotientLinBr :=
  linearCharactersTrivialOn (k := k) (⊤ : Subgroup H)

/-- Canonical equivalence from the pullback model to homomorphisms on the
actual quotient `H / top`.  This is a quotient-carrier statement; it does not
identify either side with FLZ's ordinary `Lin_{ℓ'}` carrier. -/
def selfCoverQuotientLinBrEquivQuotientHom :
    SelfCoverQuotientLinBr (k := k) (H := H) ≃*
      (H ⧸ (⊤ : Subgroup H) →* kˣ) :=
  LinearCharactersTrivialOn.quotientMulEquiv
    (k := k) (⊤ : Subgroup H)

/-- As a subgroup of all modular linear characters, the characters trivial
on the whole self-cover are exactly the bottom subgroup. -/
theorem linearCharactersTrivialOn_top_eq_bot :
    linearCharactersTrivialOn (k := k) (⊤ : Subgroup H) = ⊥ := by
  apply le_antisymm
  · intro lambda hlambda
    change lambda = 1
    apply MonoidHom.ext
    intro h
    exact hlambda (Subgroup.mem_top h)
  · exact bot_le

/-- Every element of the pullback quotient-homomorphism model is trivial. -/
theorem selfCoverQuotientLinBr_eq_one
    (lambda : SelfCoverQuotientLinBr (k := k) (H := H)) :
    lambda = 1 := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro h
  exact lambda.2 (Subgroup.mem_top h)

/-- The pullback quotient-homomorphism model is a singleton. -/
instance selfCoverQuotientLinBrSubsingleton :
    Subsingleton (SelfCoverQuotientLinBr (k := k) (H := H)) where
  allEq lambda mu := by
    rw [selfCoverQuotientLinBr_eq_one lambda,
      selfCoverQuotientLinBr_eq_one mu]

/-- Every automorphism preserves the top subgroup. -/
theorem selfCoverTop_isFieldStable (field : E →* MulAut H) :
    LinearCharactersTrivialOn.IsFieldStable
      (⊤ : Subgroup H) field := by
  intro e h hh
  exact Subgroup.mem_top (field e h)

/-- Semidirect carrier used by the self-cover model.  Its left factor is the
pullback quotient-homomorphism carrier above, which is trivial here. -/
abbrev SelfCoverQuotientActingGroup (field : E →* MulAut H) :=
  SelfCoverQuotientLinBr (k := k) (H := H) ⋊[
    LinearCharactersTrivialOn.fieldAction (k := k) field
      (selfCoverTop_isFieldStable field)] E

end QuotientLinearCharacters

section CarrierFibreActions

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (field : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)
variable (T : FibreTransportSource iota hinj blocks field block)

/-- Projected model action on the Brauer block fibre.  It factors through `E`
and is not asserted to be the source tensor-and-field action. -/
@[instance_reducible]
def selfCoverQuotientBrauerFibreAction :
    MulAction (SelfCoverQuotientActingGroup (k := k) field)
      (BrauerFibre iota hinj blocks block) := by
  let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks field block
      T.outerBlock_fixed T.brauerBlock_transport
  exact MulAction.compHom _ SemidirectProduct.rightHom

/-- Projected model action on the weight block fibre, again pulled back
through the right projection. -/
@[instance_reducible]
def selfCoverQuotientWeightFibreAction :
    MulAction (SelfCoverQuotientActingGroup (k := k) field)
      (WeightFibre blockSource block) := by
  let _ : MulAction E (WeightFibre blockSource block) :=
    rightWeightFibreMulAction field blockSource block T.outerBlock_fixed
  exact MulAction.compHom _ SemidirectProduct.rightHom

@[simp]
theorem selfCoverQuotientBrauerFibre_smul
    (a : SelfCoverQuotientActingGroup (k := k) field)
    (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks field block
        T.outerBlock_fixed T.brauerBlock_transport
    let _ : MulAction (SelfCoverQuotientActingGroup (k := k) field)
        (BrauerFibre iota hinj blocks block) :=
      selfCoverQuotientBrauerFibreAction iota hinj blocks field block T
    a • psi = a.right • psi := by
  rfl

@[simp]
theorem selfCoverQuotientWeightFibre_smul
    (a : SelfCoverQuotientActingGroup (k := k) field)
    (w : WeightFibre blockSource block) :
    let _ : MulAction E (WeightFibre blockSource block) :=
      rightWeightFibreMulAction field blockSource block T.outerBlock_fixed
    let _ : MulAction (SelfCoverQuotientActingGroup (k := k) field)
        (WeightFibre blockSource block) :=
      selfCoverQuotientWeightFibreAction
        (k := k) iota hinj blocks field blockSource block T
    a • w = a.right • w := by
  rfl

/-- The exact input needed to transport an `E`-equivariant equivalence to the
projected model actions.  No extension or cyclic-endgame fields are stored. -/
abbrev SelfCoverModelOmegaInput :=
  EquivariantEquiv E
    (BrauerFibre iota hinj blocks block)
    (WeightFibre blockSource block)
    (rightIBrBlockMulAction iota hinj blocks field block
      T.outerBlock_fixed T.brauerBlock_transport).smul
    (rightWeightFibreMulAction field blockSource block
      T.outerBlock_fixed).smul

/-- An explicit `E`-equivariant equivalence is equivariant for the projected
self-cover model actions because both actions factor through `rightHom`. -/
theorem selfCoverModelOmega_equivariant
    (omega : SelfCoverModelOmegaInput
      iota hinj blocks field blockSource block T) :
    let _ : MulAction (SelfCoverQuotientActingGroup (k := k) field)
        (BrauerFibre iota hinj blocks block) :=
      selfCoverQuotientBrauerFibreAction iota hinj blocks field block T
    let _ : MulAction (SelfCoverQuotientActingGroup (k := k) field)
        (WeightFibre blockSource block) :=
      selfCoverQuotientWeightFibreAction
        (k := k) iota hinj blocks field blockSource block T
    ∀ (a : SelfCoverQuotientActingGroup (k := k) field)
      (psi : BrauerFibre iota hinj blocks block),
      omega.toEquiv (a • psi) = a • omega.toEquiv psi := by
  dsimp only
  letI : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks field block
      T.outerBlock_fixed T.brauerBlock_transport
  letI : MulAction E (WeightFibre blockSource block) :=
    rightWeightFibreMulAction field blockSource block T.outerBlock_fixed
  letI : MulAction (SelfCoverQuotientActingGroup (k := k) field)
      (BrauerFibre iota hinj blocks block) :=
    selfCoverQuotientBrauerFibreAction iota hinj blocks field block T
  letI : MulAction (SelfCoverQuotientActingGroup (k := k) field)
      (WeightFibre blockSource block) :=
    selfCoverQuotientWeightFibreAction
      (k := k) iota hinj blocks field blockSource block T
  intro a psi
  change omega.toEquiv (a.right • psi) =
    a.right • omega.toEquiv psi
  exact omega.equivariant a.right psi

/-- The same transport packaged as an equivariant equivalence for the two
projected model actions. -/
def selfCoverQuotientEquivariantEquiv
    (omega : SelfCoverModelOmegaInput
      iota hinj blocks field blockSource block T) :
    EquivariantEquiv (SelfCoverQuotientActingGroup (k := k) field)
      (BrauerFibre iota hinj blocks block)
      (WeightFibre blockSource block)
      (selfCoverQuotientBrauerFibreAction
        iota hinj blocks field block T).smul
      (selfCoverQuotientWeightFibreAction
        (k := k) iota hinj blocks field blockSource block T).smul where
  toEquiv := omega.toEquiv
  equivariant := selfCoverModelOmega_equivariant
    iota hinj blocks field blockSource block T omega

end CarrierFibreActions

section IdentityFibres

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

/-- Identity map used as the carrier model for self-cover restriction.  No
character-restriction operation is identified with it here. -/
def selfCoverBrauerRestriction :
    BrauerFibre iota hinj blocks block →
      BrauerFibre iota hinj blocks block := id

/-- Identity map used as the carrier model for projection of a self-cover
weight to its base weight. -/
def selfCoverWeightProjection :
    WeightFibre blockSource block → WeightFibre blockSource block := id

/-- Identity lift in the Brauer-fibre carrier model. -/
def selfCoverBrauerLift :
    BrauerFibre iota hinj blocks block →
      BrauerFibre iota hinj blocks block := id

/-- Identity lift in the weight-fibre carrier model. -/
def selfCoverWeightLift :
    WeightFibre blockSource block → WeightFibre blockSource block := id

/-- Identity function used as the carrier model for a self-cover Clifford
correspondent.  It is not a construction of the source Clifford operation. -/
def selfCoverCliffordCorrespondent :
    BrauerFibre iota hinj blocks block →
      BrauerFibre iota hinj blocks block := id

@[simp]
theorem selfCoverBrauerRestriction_lift
    (psi : BrauerFibre iota hinj blocks block) :
    selfCoverBrauerRestriction iota hinj blocks block
        (selfCoverBrauerLift iota hinj blocks block psi) = psi :=
  rfl

@[simp]
theorem selfCoverWeightProjection_lift
    (w : WeightFibre blockSource block) :
    selfCoverWeightProjection blockSource block
        (selfCoverWeightLift blockSource block w) = w :=
  rfl

@[simp]
theorem selfCoverCliffordCorrespondent_eq
    (psi : BrauerFibre iota hinj blocks block) :
    selfCoverCliffordCorrespondent iota hinj blocks block psi = psi :=
  rfl

/-- Model Brauer covering fibre: the equation fibre of the identity map
above, not the source covering relation. -/
def SelfCoverBrauerCoveringFibre
    (psi : BrauerFibre iota hinj blocks block) :
    Set (BrauerFibre iota hinj blocks block) :=
  {psiTilde | selfCoverBrauerRestriction iota hinj blocks block psiTilde = psi}

/-- Model weight covering fibre: the equation fibre of the identity map
above, not the source covering relation. -/
def SelfCoverWeightCoveringFibre
    (w : WeightFibre blockSource block) :
    Set (WeightFibre blockSource block) :=
  {wTilde | selfCoverWeightProjection blockSource block wTilde = w}

/-- Identity restriction makes every model Brauer equation fibre a
singleton. -/
theorem selfCoverBrauerCoveringFibre_eq_singleton
    (psi : BrauerFibre iota hinj blocks block) :
    SelfCoverBrauerCoveringFibre iota hinj blocks block psi = {psi} := by
  ext chi
  rfl

/-- Identity projection makes every model weight equation fibre a
singleton. -/
theorem selfCoverWeightCoveringFibre_eq_singleton
    (w : WeightFibre blockSource block) :
    SelfCoverWeightCoveringFibre blockSource block w = {w} := by
  ext v
  rfl

/-- Any equivalence maps the singleton Brauer equation fibre onto the
corresponding singleton weight equation fibre. -/
theorem selfCoverCoveringFibre_image
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (psi : BrauerFibre iota hinj blocks block) :
    omega '' SelfCoverBrauerCoveringFibre iota hinj blocks block psi =
      SelfCoverWeightCoveringFibre blockSource block (omega psi) := by
  simp [selfCoverBrauerCoveringFibre_eq_singleton,
    selfCoverWeightCoveringFibre_eq_singleton]

end IdentityFibres

section CentreCharacters

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

noncomputable local instance selfCoverCenterFintype :
    Fintype (Subgroup.center H) :=
  Fintype.ofFinite _

/-- Ordinary homomorphism label carrier for the centre. -/
abbrev SelfCoverOrdinaryCentralCharacter := Subgroup.center H →* Kˣ

/-- Modular homomorphism label carrier for the centre. -/
abbrev SelfCoverModularCentralCharacter := Subgroup.center H →* kˣ

/-- A centre identified with the bottom subgroup has a subsingleton carrier. -/
theorem selfCoverCenter_subsingleton
    (hcenter : Subgroup.center H = ⊥) :
    Subsingleton (Subgroup.center H) := by
  constructor
  intro z w
  apply Subtype.ext
  have hz : (z : H) = 1 := by
    have hzbot : (z : H) ∈ (⊥ : Subgroup H) := by
      rw [← hcenter]
      exact z.property
    simpa using hzbot
  have hw : (w : H) = 1 := by
    have hwbot : (w : H) ∈ (⊥ : Subgroup H) := by
      rw [← hcenter]
      exact w.property
    simpa using hwbot
  exact hz.trans hw.symm

/-- The centre has one element in the centreless specialisation. -/
theorem selfCoverCenter_card_eq_one
    (hcenter : Subgroup.center H = ⊥) :
    Fintype.card (Subgroup.center H) = 1 := by
  letI : Subsingleton (Subgroup.center H) :=
    selfCoverCenter_subsingleton hcenter
  exact Fintype.card_eq_one_iff.mpr
    ⟨1, fun z ↦ Subsingleton.elim z 1⟩

/-- Centrelessness supplies the invertibility needed by central character
idempotents, rather than leaving it as an extra source input. -/
def selfCoverCenterCardInvertible
    (hcenter : Subgroup.center H = ⊥) :
    Invertible (Fintype.card (Subgroup.center H) : k) := by
  exact invertibleOfNonzero (by
    rw [selfCoverCenter_card_eq_one hcenter]
    simpa using (one_ne_zero : (1 : k) ≠ 0))

/-- Homomorphisms out of the centreless centre are a subsingleton, for any
monoid codomain. -/
theorem selfCoverCenterHom_subsingleton
    {M : Type u} [Monoid M]
    (hcenter : Subgroup.center H = ⊥) :
    Subsingleton (Subgroup.center H →* M) := by
  letI : Subsingleton (Subgroup.center H) :=
    selfCoverCenter_subsingleton hcenter
  constructor
  intro nu mu
  ext z
  have hz : z = 1 := Subsingleton.elim z 1
  simp [hz]

/-- The ordinary centre-label carrier is a subsingleton. -/
theorem selfCoverOrdinaryCentralCharacter_subsingleton
    (hcenter : Subgroup.center H = ⊥) :
    Subsingleton (SelfCoverOrdinaryCentralCharacter (K := K) (H := H)) :=
  selfCoverCenterHom_subsingleton hcenter

/-- The modular centre-label carrier is a subsingleton. -/
theorem selfCoverModularCentralCharacter_subsingleton
    (hcenter : Subgroup.center H = ⊥) :
    Subsingleton (SelfCoverModularCentralCharacter (k := k) (H := H)) :=
  selfCoverCenterHom_subsingleton hcenter

/-- The modular central character sector of the selected block. -/
def selfCoverBlockCentralCharacter
    (hcenter : Subgroup.center H = ⊥) :
    SelfCoverModularCentralCharacter (k := k) (H := H) := by
  letI : Invertible (Fintype.card (Subgroup.center H) : k) :=
    selfCoverCenterCardInvertible (k := k) hcenter
  exact blocks.centralCharacterSector (Subgroup.center H) le_rfl block

/-- The modular block-sector label of a Brauer-fibre element. -/
def selfCoverBrauerCentralCharacter
    (hcenter : Subgroup.center H = ⊥)
    (psi : BrauerFibre iota hinj blocks block) :
    SelfCoverModularCentralCharacter (k := k) (H := H) := by
  letI : Invertible (Fintype.card (Subgroup.center H) : k) :=
    selfCoverCenterCardInvertible (k := k) hcenter
  exact blocks.centralCharacterSector (Subgroup.center H) le_rfl
    (irreducibleBrauerCharacterBlock iota hinj blocks psi.1)

/-- The modular block-sector label of a weight-fibre element, formed through
the induced block `weightBlock`.  This is not an ordinary central character
of the weight. -/
def selfCoverWeightCentralCharacter
    (hcenter : Subgroup.center H = ⊥)
    (w : WeightFibre blockSource block) :
    SelfCoverModularCentralCharacter (k := k) (H := H) := by
  letI : Invertible (Fintype.card (Subgroup.center H) : k) :=
    selfCoverCenterCardInvertible (k := k) hcenter
  exact blocks.centralCharacterSector (Subgroup.center H) le_rfl
    (blockSource.weightBlock w.1)

/-- Every element of the Brauer block fibre has the selected block's modular
central character sector. -/
theorem selfCoverBrauerCentralCharacter_eq_block
    (hcenter : Subgroup.center H = ⊥)
    (psi : BrauerFibre iota hinj blocks block) :
    selfCoverBrauerCentralCharacter iota hinj blocks block hcenter psi =
      selfCoverBlockCentralCharacter blocks block hcenter := by
  unfold selfCoverBrauerCentralCharacter selfCoverBlockCentralCharacter
  rw [psi.2]

/-- Every element of the weight block fibre has that same modular sector
because its induced `weightBlock` is the selected block. -/
theorem selfCoverWeightCentralCharacter_eq_block
    (hcenter : Subgroup.center H = ⊥)
    (w : WeightFibre blockSource block) :
    selfCoverWeightCentralCharacter blocks blockSource block hcenter w =
      selfCoverBlockCentralCharacter blocks block hcenter := by
  have hw : blockSource.weightBlock w.1 = block := by
    simpa only [LocalBlockInductionSource.equivariantBlockAssignment_blockOf]
      using w.2
  unfold selfCoverWeightCentralCharacter selfCoverBlockCentralCharacter
  rw [hw]

/-- The unique possible map between the two centre-label carriers, available
only under the centreless hypothesis.  This is a carrier-model map, not a
construction of ordinary-to-Brauer reduction. -/
def selfCoverCentralReduction
    (_hcenter : Subgroup.center H = ⊥)
    (_ : SelfCoverOrdinaryCentralCharacter (K := K) (H := H)) :
    SelfCoverModularCentralCharacter (k := k) (H := H) := 1

/-- Model Brauer central fibre defined from the modular block-sector map. -/
def SelfCoverBrauerCentralFibre
    (hcenter : Subgroup.center H = ⊥)
    (nu : SelfCoverOrdinaryCentralCharacter (K := K) (H := H)) :
    Set (BrauerFibre iota hinj blocks block) :=
  {psi | selfCoverBrauerCentralCharacter
      iota hinj blocks block hcenter psi =
    selfCoverCentralReduction (k := k) hcenter nu}

/-- Model weight central fibre defined from the modular sector of the induced
`weightBlock`.  It is not the source ordinary-character fibre. -/
def SelfCoverWeightCentralFibre
    (hcenter : Subgroup.center H = ⊥)
    (nu : SelfCoverOrdinaryCentralCharacter (K := K) (H := H)) :
    Set (WeightFibre blockSource block) :=
  {w | selfCoverWeightCentralCharacter
      blocks blockSource block hcenter w =
    selfCoverCentralReduction (k := k) hcenter nu}

/-- Centrelessness makes every model Brauer central fibre universal. -/
theorem selfCoverBrauerCentralFibre_eq_univ
    (hcenter : Subgroup.center H = ⊥)
    (nu : SelfCoverOrdinaryCentralCharacter (K := K) (H := H)) :
    SelfCoverBrauerCentralFibre
      iota hinj blocks block hcenter nu = Set.univ := by
  ext psi
  simp only [SelfCoverBrauerCentralFibre, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  exact (selfCoverModularCentralCharacter_subsingleton
    (k := k) hcenter).elim _ _

/-- Centrelessness makes every model weight central fibre universal. -/
theorem selfCoverWeightCentralFibre_eq_univ
    (hcenter : Subgroup.center H = ⊥)
    (nu : SelfCoverOrdinaryCentralCharacter (K := K) (H := H)) :
    SelfCoverWeightCentralFibre
      (k := k) blocks blockSource block hcenter nu = Set.univ := by
  ext w
  simp only [SelfCoverWeightCentralFibre, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  exact (selfCoverModularCentralCharacter_subsingleton
    (k := k) hcenter).elim _ _

/-- Any equivalence maps the universal Brauer model fibre onto the universal
weight model fibre. -/
theorem selfCoverCentralFibre_image
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (hcenter : Subgroup.center H = ⊥)
    (nu : SelfCoverOrdinaryCentralCharacter (K := K) (H := H)) :
    omega '' SelfCoverBrauerCentralFibre
        iota hinj blocks block hcenter nu =
      SelfCoverWeightCentralFibre
        (k := k) blocks blockSource block hcenter nu := by
  rw [selfCoverBrauerCentralFibre_eq_univ,
    selfCoverWeightCentralFibre_eq_univ]
  exact Set.image_univ_of_surjective omega.surjective

end CentreCharacters

section CarrierModelBlockEquality

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
variable (omega : BrauerFibre iota hinj blocks block ≃
  WeightFibre blockSource block)

/-- Model weight attached to `psi`: apply the chosen equivalence, then the
identity weight lift. -/
def selfCoverModelWeight
    (psi : BrauerFibre iota hinj blocks block) :
    WeightFibre blockSource block :=
  selfCoverWeightLift blockSource block (omega psi)

/-- A raw character-weight representative selected from the model weight
class.  This selection contains no Clifford, extension, or DGN operation. -/
def selfCoverModelSelectedCharacterWeight
    (psi : BrauerFibre iota hinj blocks block) : CharacterWeight p K H :=
  selectedCharacterWeight blockSource block
    (selfCoverModelWeight iota hinj blocks blockSource block omega psi)

/-- The two identity functions used in the carrier model compose to the
identity.  This is not a Clifford-correspondence theorem. -/
theorem selfCoverCliffordCorrespondent_lift
    (psi : BrauerFibre iota hinj blocks block) :
    selfCoverCliffordCorrespondent iota hinj blocks block
        (selfCoverBrauerLift iota hinj blocks block psi) = psi :=
  rfl

/-- The chosen model equivalence sends the identity Brauer lift to the model
weight attached to `psi`. -/
theorem selfCoverModelOmega_lift
    (psi : BrauerFibre iota hinj blocks block) :
    omega (selfCoverBrauerLift iota hinj blocks block psi) =
      selfCoverModelWeight iota hinj blocks blockSource block omega psi :=
  rfl

/-- The selected raw character weight represents the chosen model weight
class. -/
theorem selfCoverModelSelectedCharacterWeight_spec
    (psi : BrauerFibre iota hinj blocks block) :
    (Quotient.mk'' (Quotient.mk''
      (selfCoverModelSelectedCharacterWeight
        iota hinj blocks blockSource block omega psi)) :
        CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H)) =
      (selfCoverModelWeight
        iota hinj blocks blockSource block omega psi).1 :=
  selectedCharacterWeight_spec blockSource block
    (selfCoverModelWeight iota hinj blocks blockSource block omega psi)

/-- Carrier-model block bookkeeping: both sides equal the block already
stored in their respective fibre subtypes.  This is not FLZ 3.18(iii)(c) and
asserts no Clifford, extension, induction, or Delta/DGN compatibility. -/
theorem selfCover_carrier_model_block_equality
    (psi : BrauerFibre iota hinj blocks block) :
    irreducibleBrauerCharacterBlock iota hinj blocks
        (selfCoverCliffordCorrespondent iota hinj blocks block
          (selfCoverBrauerLift iota hinj blocks block psi)).1 =
      blockSource.operations.rawWeightBlock
        (selfCoverModelSelectedCharacterWeight
          iota hinj blocks blockSource block omega psi) := by
  calc
    irreducibleBrauerCharacterBlock iota hinj blocks
        (selfCoverCliffordCorrespondent iota hinj blocks block
          (selfCoverBrauerLift iota hinj blocks block psi)).1 = block := psi.2
    _ = blockSource.operations.rawWeightBlock
        (selfCoverModelSelectedCharacterWeight
          iota hinj blocks blockSource block omega psi) := by
      exact (selectedCharacterWeight_block blockSource block
        (selfCoverModelWeight
          iota hinj blocks blockSource block omega psi)).symm

end CarrierModelBlockEquality

end ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverLiteralClauseIII


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
