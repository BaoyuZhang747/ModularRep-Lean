import ModularRep.PaperProofs.TypeCOddTwoOriginalReferenceAmbient
import ModularRep.BrauerCharacterExtensionWitnessTransport

/-!
# The original chosen local reduction and extensions in reference coordinates

The quotient local weight still uses the exact original selected quotient
reduction. Its inflation is identified with the SAME original matched own
normalizer reduction by the two ordinary reduction equations. The roots
remain independently stored; no compatibility is inferred from that value
identity. Global and local ambient extension characters are the original
ones, transported only through the proved ambient/local-base coordinates.

This supplies actual SpathCharacterExtensions, not a complete block witness.
Every-J specified induction and finite root-table coherence remain separate.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalChosenExtensions

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open OddTwoLiteralSpathTarget TypeCOddTwoOriginalBlockMatching
open TypeCOddTwoOriginalReferenceAmbient

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable {P : Problem n F} (D : Definition41 P) (b : P.Block)
variable (reference psi : Definition35Brauer (P.blockProblem b))

local instance chosenExtensionSubgroupFintype {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : Fintype H := Fintype.ofFinite _

abbrev OwnNormalizer :=
  P.Normalizer (TypeCOddTwoOriginalBlockMatching.selectedRadical D b psi)

abbrev ReferenceNormalizer := Subgroup.normalizer
  (quotientRadical (P.blockProblem b) reference (blockEquiv D b psi) :
    Set (CentralCharacterQuotient (P.blockProblem b) reference))

/-- The actual original-normalizer to reference-normalizer equivalence. -/
def referenceNormalizerEquiv : OwnNormalizer D b psi ≃*
    ReferenceNormalizer D b reference psi :=
  normalizerEquiv (G := X n F) (referenceQuotientEquiv b reference)
    (selectedPair D b psi).subgroup

/-- The own ordinary character in the selected matched packet is exactly
the already selected weight character. -/
theorem selected_own_reduction (x : PrimeRegularElement (G := OwnNormalizer D b psi) 2) :
    (selectedPair D b psi).localCharacter (QuotientGroup.mk x.1) =
      (selectedMatched D b psi).localReduction.brauer.1 x := by
  have h := (selectedMatched D b psi).localReduction.reduction x
  have hc := congrArg
    (fun theta : LocalDefectZeroCharacter (K := P.K)
        (TypeCOddTwoOriginalBlockMatching.selectedRadical D b psi) =>
      theta.1 (QuotientGroup.mk x.1)) (selectedLocalCharacter_eq D b psi)
  exact hc.symm.trans h

/-- The quotient ordinary character uses the actual normalizer square. -/
theorem reference_ordinary_value (x : ReferenceNormalizer D b reference psi) :
    (quotientPacket D b reference psi).ordinary (QuotientGroup.mk x) =
      (selectedPair D b psi).localCharacter
        (QuotientGroup.mk ((referenceNormalizerEquiv D b reference psi).symm x)) := by
  have h := quotientPacket_ordinary D b reference psi
    (QuotientGroup.mk ((referenceNormalizerEquiv D b reference psi).symm x))
  have hx : quotientNormalizerMap (P.blockProblem b) reference (blockEquiv D b psi)
      (QuotientGroup.mk ((referenceNormalizerEquiv D b reference psi).symm x)) =
        QuotientGroup.mk x := by
    change QuotientGroup.mk ((referenceNormalizerEquiv D b reference psi)
      ((referenceNormalizerEquiv D b reference psi).symm x)) = QuotientGroup.mk x
    exact congrArg (fun z : ReferenceNormalizer D b reference psi => QuotientGroup.mk z)
      ((referenceNormalizerEquiv D b reference psi).apply_symm_apply x)
  exact (congrArg (quotientPacket D b reference psi).ordinary hx).symm.trans h

/-- This root is computed from the chosen OWN normalizer reduction. -/
def normalizerRoot : PrimeRegularRootEmbedding 2 P.k P.K
    (ReferenceNormalizer D b reference psi) :=
  (selectedMatched D b psi).localReduction.root.alongMulEquiv
    (referenceNormalizerEquiv D b reference psi)

def normalizerBrauer : IBr (normalizerRoot D b reference psi) :=
  IrreducibleBrauerCharacter.alongMulEquiv
    (selectedMatched D b psi).localReduction.root
    (referenceNormalizerEquiv D b reference psi)
    (selectedMatched D b psi).localReduction.brauer

/-- Two OWN reductions prove function inflation. This is not a deduction
of root compatibility or equality of independently chosen root tables. -/
def localInflation : QuotientLocalInflationSource (P.blockProblem b) reference
    (blockEquiv D b psi) (quotientPacket D b reference psi) where
  iota := normalizerRoot D b reference psi
  brauer := normalizerBrauer D b reference psi
  inflation := by
    apply PrimeRegularClassFunction.ext
    intro x
    let q := QuotientGroup.mk'
      ((quotientRadical (P.blockProblem b) reference (blockEquiv D b psi)).subgroupOf
        (ReferenceNormalizer D b reference psi))
    have hq := (quotientPacket D b reference psi).reduction
      (PrimeRegularElement.map q x)
    exact hq.symm.trans ((reference_ordinary_value D b reference psi x.1).trans
      (selected_own_reduction D b psi
        (PrimeRegularElement.map
          (referenceNormalizerEquiv D b reference psi).symm.toMonoidHom x)))

@[simp] theorem localInflation_root :
    (localInflation D b reference psi).iota =
      (selectedMatched D b psi).localReduction.root.alongMulEquiv
        (referenceNormalizerEquiv D b reference psi) := rfl

theorem localInflation_values (x : PrimeRegularElement
    (G := ReferenceNormalizer D b reference psi) 2) :
    (localInflation D b reference psi).brauer.1 x =
      (selectedMatched D b psi).localReduction.brauer.1
        (PrimeRegularElement.map
          (referenceNormalizerEquiv D b reference psi).symm.toMonoidHom x) := rfl

abbrev OwnLocalGroup := P.LocalGroup (selectedMatched D b psi).ambient
  (TypeCOddTwoOriginalBlockMatching.selectedRadical D b psi)

abbrev ReferenceLocalGroup := AmbientLocalGroup (P.blockProblem b) reference psi
  (blockEquiv D b psi) (referenceSource P b reference psi)
  (selectedReferenceAmbient D b reference psi)

/-- Equality of actual normalizers changes only membership proofs. -/
def ambientLocalEquiv : OwnLocalGroup D b psi ≃* ReferenceLocalGroup D b reference psi :=
  MulEquiv.subgroupCongr (selectedReference_localGroup D b reference psi).symm

@[simp] theorem ambientLocalEquiv_value (x : OwnLocalGroup D b psi) :
    (ambientLocalEquiv D b reference psi x).1 = x.1 := rfl

abbrev OwnLocalBase := P.localBase (selectedMatched D b psi).ambient
  (TypeCOddTwoOriginalBlockMatching.selectedRadical D b psi)

abbrev ReferenceLocalBase := AmbientLocalBase (P.blockProblem b) reference psi
  (blockEquiv D b psi) (referenceSource P b reference psi)
  (selectedReferenceAmbient D b reference psi)

/-- The intersections with the SAME ambient base have the same elements. -/
def ambientLocalBaseEquiv : OwnLocalBase D b psi ≃*
    ReferenceLocalBase D b reference psi where
  toFun x := ⟨ambientLocalEquiv D b reference psi x.1, x.2⟩
  invFun x := ⟨(ambientLocalEquiv D b reference psi).symm x.1, x.2⟩
  left_inv x := Subtype.ext ((ambientLocalEquiv D b reference psi).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((ambientLocalEquiv D b reference psi).apply_symm_apply x.1)
  map_mul' x y := Subtype.ext (map_mul (ambientLocalEquiv D b reference psi) x.1 y.1)

theorem ambientLocalBase_square :
    (ambientLocalEquiv D b reference psi).symm.toMonoidHom.comp
        (ReferenceLocalBase D b reference psi).subtype =
      (OwnLocalBase D b psi).subtype.comp
        (ambientLocalBaseEquiv D b reference psi).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro x
  rfl

/-- Use the original stored own local-base map between the two computed
coordinate changes, rather than selecting a different map. -/
def referenceLocalBaseEquiv : ReferenceNormalizer D b reference psi ≃*
    ReferenceLocalBase D b reference psi :=
  (referenceNormalizerEquiv D b reference psi).symm.trans
    ((selectedMatched D b psi).extensions.localBaseEquiv.trans
      (ambientLocalBaseEquiv D b reference psi))

theorem referenceLocalBase_natural (x : ReferenceNormalizer D b reference psi) :
    (referenceLocalBaseEquiv D b reference psi x).1.1 =
      quotientToAmbient (P.blockProblem b) reference psi
        (referenceSource P b reference psi) (selectedReferenceAmbient D b reference psi) x.1 := by
  have he := congrArg (fun f : X n F →* (selectedMatched D b psi).ambient.A =>
      f ((referenceNormalizerEquiv D b reference psi).symm x).1)
    (referenceAmbient_embedding_square P b reference psi (selectedMatched D b psi).ambient)
  have hx : centralCharacterQuotientMap (P.blockProblem b) reference
      ((referenceNormalizerEquiv D b reference psi).symm x).1 = x.1 :=
    congrArg Subtype.val ((referenceNormalizerEquiv D b reference psi).apply_symm_apply x)
  exact ((selectedMatched D b psi).extensions.localBaseEquiv_natural
    ((referenceNormalizerEquiv D b reference psi).symm x)).trans
      (he.symm.trans (congrArg
        (quotientToAmbient (P.blockProblem b) reference psi
          (referenceSource P b reference psi) (selectedReferenceAmbient D b reference psi)) hx))

/-- The global base character is the SAME character in reference coordinates. -/
theorem globalBase_values :
    (IrreducibleBrauerCharacter.alongMulEquiv
      (referenceSource P b reference psi).iota
      (selectedReferenceAmbient D b reference psi).baseEquiv
      (referenceSource P b reference psi).brauer).1 =
    (IrreducibleBrauerCharacter.alongMulEquiv (P.quotientSource psi.1).iota
      (selectedMatched D b psi).ambient.baseEquiv
      (P.quotientSource psi.1).brauer).1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  have ht := congrArg
    (fun f : PrimeRegularClassFunction P.K
        (CentralCharacterQuotient (P.blockProblem b) reference) 2 =>
      f (PrimeRegularElement.map
        (selectedReferenceAmbient D b reference psi).baseEquiv.symm.toMonoidHom x))
    (reference_brauer_transport P b reference psi)
  have hm : PrimeRegularElement.map (referenceToOwn b reference psi).toMonoidHom
      (PrimeRegularElement.map
        (selectedReferenceAmbient D b reference psi).baseEquiv.symm.toMonoidHom x) =
        PrimeRegularElement.map
          (selectedMatched D b psi).ambient.baseEquiv.symm.toMonoidHom x := by
    apply Subtype.ext
    exact (referenceToOwn b reference psi).apply_symm_apply
      ((selectedMatched D b psi).ambient.baseEquiv.symm x.1)
  exact ht.symm.trans (congrArg (P.quotientSource psi.1).brauer.1 hm)

/-- Exact pullback of the SAME local base character. Independent quotient
and normalizer root conventions are not identified by this equality. -/
theorem localBase_values :
    PrimeRegularClassFunction.pullback
        (ambientLocalBaseEquiv D b reference psi).symm.toMonoidHom
        (IrreducibleBrauerCharacter.alongMulEquiv
          (selectedMatched D b psi).localReduction.root
          (selectedMatched D b psi).extensions.localBaseEquiv
          (selectedMatched D b psi).localReduction.brauer).1 =
      (IrreducibleBrauerCharacter.alongMulEquiv
        (localInflation D b reference psi).iota (referenceLocalBaseEquiv D b reference psi)
        (localInflation D b reference psi).brauer).1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  change (selectedMatched D b psi).localReduction.brauer.1
      (PrimeRegularElement.map
        (selectedMatched D b psi).extensions.localBaseEquiv.symm.toMonoidHom
        (PrimeRegularElement.map (ambientLocalBaseEquiv D b reference psi).symm.toMonoidHom x)) =
    (selectedMatched D b psi).localReduction.brauer.1
      (PrimeRegularElement.map (referenceNormalizerEquiv D b reference psi).symm.toMonoidHom
        (PrimeRegularElement.map (referenceLocalBaseEquiv D b reference psi).symm.toMonoidHom x))
  apply congrArg (selectedMatched D b psi).localReduction.brauer.1
  apply Subtype.ext
  exact ((referenceNormalizerEquiv D b reference psi).symm_apply_apply
    ((selectedMatched D b psi).extensions.localBaseEquiv.symm
      ((ambientLocalBaseEquiv D b reference psi).symm x.1))).symm

/-- Both existing extension characters are reused; only local ambient
membership coordinates are transported. No extension existence input. -/
def referenceExtensions : SpathCharacterExtensions (P.blockProblem b) reference psi
    (blockEquiv D b psi) (referenceSource P b reference psi)
    (quotientPacket D b reference psi) (localInflation D b reference psi)
    (selectedReferenceAmbient D b reference psi) where
  ambientRoot := (selectedMatched D b psi).extensions.ambientRoot
  globalExtension := ⟨(selectedMatched D b psi).extensions.globalExtension.1,
    (selectedMatched D b psi).extensions.globalExtension.2.trans
      (globalBase_values D b reference psi).symm⟩
  localBaseEquiv := referenceLocalBaseEquiv D b reference psi
  localBaseEquiv_natural := referenceLocalBase_natural D b reference psi
  localAmbientRoot := (selectedMatched D b psi).extensions.localAmbientRoot.alongMulEquiv
    (ambientLocalEquiv D b reference psi)
  localExtension := Representation.Extension.BrauerCharacterExtensionWitness.alongMulEquivOfBase
    (ambientLocalEquiv D b reference psi) (ambientLocalBaseEquiv D b reference psi)
    (ambientLocalBase_square D b reference psi)
    (selectedMatched D b psi).extensions.localExtension
    ((localInflation D b reference psi).iota.alongMulEquiv
      (referenceLocalBaseEquiv D b reference psi))
    (IrreducibleBrauerCharacter.alongMulEquiv (localInflation D b reference psi).iota
      (referenceLocalBaseEquiv D b reference psi) (localInflation D b reference psi).brauer)
    (localBase_values D b reference psi)

@[simp] theorem referenceExtensions_ambientRoot :
    (referenceExtensions D b reference psi).ambientRoot =
      (selectedMatched D b psi).extensions.ambientRoot := rfl

@[simp] theorem referenceExtensions_globalCharacter :
    (referenceExtensions D b reference psi).globalExtension.1 =
      (selectedMatched D b psi).extensions.globalExtension.1 := rfl

theorem referenceExtensions_local_values (x : PrimeRegularElement
    (G := ReferenceLocalGroup D b reference psi) 2) :
    (referenceExtensions D b reference psi).localExtension.1.1 x =
      (selectedMatched D b psi).extensions.localExtension.1.1
        (PrimeRegularElement.map (ambientLocalEquiv D b reference psi).symm.toMonoidHom x) := rfl

/-- Any equality of the two SAME original extension functions is preserved.
The later Q=1 consumer must supply the original D.oneExtensions instance. -/
theorem extension_equality_transport
    (same : ∀ x : PrimeRegularElement (G := OwnLocalGroup D b psi) 2,
      (selectedMatched D b psi).extensions.localExtension.1.1 x =
        (selectedMatched D b psi).extensions.globalExtension.1.1
          (PrimeRegularElement.map (OwnLocalGroup D b psi).subtype x))
    (x : PrimeRegularElement (G := ReferenceLocalGroup D b reference psi) 2) :
    (referenceExtensions D b reference psi).localExtension.1.1 x =
      (referenceExtensions D b reference psi).globalExtension.1.1
        (PrimeRegularElement.map (ReferenceLocalGroup D b reference psi).subtype x) :=
  same (PrimeRegularElement.map (ambientLocalEquiv D b reference psi).symm.toMonoidHom x)

end ModularRep.PaperProofs.TypeCOddTwoOriginalChosenExtensions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
