import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotients
import ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalRepresentationExtension
import ModularRep.PaperProofs.CyclicOuterEmbeddedPairNormalizer
import ModularRep.SemidirectEmbeddedConjugation

/-!
# The selected global and local associated projective models

Every selected object uses the same `EquivariantMatch`. Actual cyclic
extension witnesses produce ambient operators with quotient multiplier one.
The global affording equation and the local ordinary/Brauer reduction are
retained explicitly. No quotient representation or obstruction-class
comparison is supplied as input.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelectedModels

open Formalisation ModularRep ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.CyclicOuterEmbeddedPairNormalizer
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalRepresentationExtension
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotients
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel

universe u

variable (P : Definition35Problem.{u}) (M : EquivariantMatch P)
variable (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))

local instance outerFinite : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : P.H → P.H))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

local instance outerFintype : Fintype (SelectedOuterGroup S) := Fintype.ofFinite _

abbrev globalRoot := P.iota.alongMulEquiv (selectedClause3BaseEquiv P M.theta S)

abbrev globalCharacter : IBr (globalRoot P M S) :=
  IrreducibleBrauerCharacter.alongMulEquiv P.iota
    (selectedClause3BaseEquiv P M.theta S) M.theta.1

/-- A model of the selected theta, on the embedded X in the named G_theta. -/
structure GlobalModel where
  W : FDRep P.k (XInGTheta P M S)
  irreducible : Representation.IsIrreducible W.ρ
  affords : (globalCharacter P M S).1 =
    Representation.brauerCharacterOfRootEmbedding W.ρ (globalRoot P M S)
  projective : AssociatedProjectiveModel (XInGTheta P M S) W.ρ
  factor_one : projective.factorSet = ScalarFactorSet.trivial

theorem selectedGlobalModel
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k) :
    Nonempty (GlobalModel P M S) := by
  let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  obtain ⟨W, hW, hchar, ⟨E⟩⟩ :=
    global_extension_actual P.iota (selectedOuterField S) principle M.theta.1
      (globalRoot P M S)
      (IrreducibleBrauerCharacter.pullback_isIrreducibleBrauerCharacter
        P.iota (selectedClause3BaseEquiv P M.theta S) M.theta.1)
      (fun d x ↦ canonicalEmbedded_conjugationSquare (selectedOuterField S)
        M.theta.1 (selectedBrauer_inner_fixed P.iota S M.theta.1) d x)
  exact ⟨⟨W, hW, hchar, AssociatedProjectiveModel.ofExtension E, rfl⟩⟩

abbrev localQuotientInput := canonicalRawNormalizerQuotientInput
  (p := P.p) (K := P.K) (H := P.H)

abbrev LocalQuotientBase :=
  CyclicOuterLemma37LiteralLocalExtension.LocalBase
    (selectedOuterField S) P.blockSource P.block (localQuotientInput P) M.weight

abbrev localRoot := transportedLocalRootEmbedding
  (selectedOuterField S) P.blockSource P.block (localQuotientInput P)
  M.weight (P.localReduction M.weight)

abbrev localBrauer := transportedLocalBrauer
  (selectedOuterField S) P.blockSource P.block (localQuotientInput P)
  M.weight (P.localReduction M.weight)

abbrev localOrdinary := transportedLocalOrdinary
  (selectedOuterField S) P.blockSource P.block (localQuotientInput P) M.weight

local instance radicalNormal :
    (EmbeddedRadical (selectedOuterField S) P.blockSource P.block
      (localQuotientInput P) M.weight).Normal :=
  embeddedRadical_normal (phi := selectedOuterField S)
    (blockSource := P.blockSource) (block := P.block) (localQuotientInput P) M.weight

abbrev rawBaseToQuotient : SelectedPairBase P S M.weight →* LocalQuotientBase P M S :=
  subgroupToQuotientImage
    (EmbeddedRadical (selectedOuterField S) P.blockSource P.block
      (localQuotientInput P) M.weight) (SelectedPairBase P S M.weight)

theorem rawBaseToQuotient_surjective : Function.Surjective (rawBaseToQuotient P M S) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
  exact ⟨⟨n, hn⟩, rfl⟩

abbrev namedBaseToQuotient :
    SporadicFi24P3Definition44NamedCarrierQuotients.LocalBase P M S →*
      LocalQuotientBase P M S :=
  (rawBaseToQuotient P M S).comp (pairBaseEquiv P M S).symm.toMonoidHom

theorem namedBaseToQuotient_surjective :
    Function.Surjective (namedBaseToQuotient P M S) :=
  (rawBaseToQuotient_surjective P M S).comp (pairBaseEquiv P M S).symm.surjective

/-- Transport an actual local extension along the proved normaliser square. -/
def namedLocalExtension (W : FDRep P.k (LocalQuotientBase P M S))
    (E : Representation.Extension (SelectedPairBase P S M.weight)
      (Representation.pullback W.ρ (rawBaseToQuotient P M S))) :
    Representation.Extension
      (SporadicFi24P3Definition44NamedCarrierQuotients.LocalBase P M S)
      (Representation.pullback W.ρ (namedBaseToQuotient P M S)) where
  representation := E.representation.pullback (pairNormalizerEquiv P M S).symm.toMonoidHom
  restrictionEquiv := by
    have hsquare : (pairNormalizerEquiv P M S).symm.toMonoidHom.comp
        (SporadicFi24P3Definition44NamedCarrierQuotients.LocalBase P M S).subtype =
      (SelectedPairBase P S M.weight).subtype.comp
        (pairBaseEquiv P M S).symm.toMonoidHom := by
      apply MonoidHom.ext
      intro n
      apply (pairNormalizerEquiv P M S).injective
      change pairNormalizerEquiv P M S ((pairNormalizerEquiv P M S).symm n.1) =
        pairNormalizerEquiv P M S ((pairBaseEquiv P M S).symm n).1
      calc
        _ = n.1 := (pairNormalizerEquiv P M S).apply_symm_apply n.1
        _ = _ := (congrArg Subtype.val ((pairBaseEquiv P M S).apply_symm_apply n)).symm
    rw [Representation.pullback_comp, hsquare, ← Representation.pullback_comp]
    exact E.restrictionEquiv.pullback (pairBaseEquiv P M S).symm.toMonoidHom

/-- The local model retains the selected quotient character and its reduction,
then inflates along the actual named local-base map. -/
structure LocalModel where
  W : FDRep P.k (LocalQuotientBase P M S)
  irreducible : Representation.IsIrreducible W.ρ
  affords : (localBrauer P M S).1 =
    Representation.brauerCharacterOfRootEmbedding W.ρ (localRoot P M S)
  reduction :
    SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      (localRoot P M S) (localOrdinary P M S) (localBrauer P M S)
  inflated_irreducible :
    Representation.IsIrreducible (Representation.pullback W.ρ (namedBaseToQuotient P M S))
  projective : AssociatedProjectiveModel
    (SporadicFi24P3Definition44NamedCarrierQuotients.LocalBase P M S)
    (Representation.pullback W.ρ (namedBaseToQuotient P M S))
  factor_one : projective.factorSet = ScalarFactorSet.trivial

theorem selectedLocalModel
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k) :
    Nonempty (LocalModel P M S) := by
  obtain ⟨W, hW, hchar, hred, ⟨E⟩⟩ :=
    selectedPairLocalRepresentationExtension P S principle M.weight
  exact ⟨⟨W, hW, hchar, hred,
    hW.pullback _ (namedBaseToQuotient_surjective P M S),
    AssociatedProjectiveModel.ofExtension (namedLocalExtension P M S W E), rfl⟩⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelectedModels


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
