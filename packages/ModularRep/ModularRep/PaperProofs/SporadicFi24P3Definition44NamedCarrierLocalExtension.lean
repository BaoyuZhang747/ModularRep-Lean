import ModularRep.PaperProofs.SporadicFi24SelectedOuterFixedLocalExtension
import ModularRep.PrimeRegularRootEmbeddingPQuotient

/-!
# The local extension with its derived root agreement

Construct the normalizer root from the actual quotient root. Reselect the
pair-stabilizer root to agree with this prescribed base convention, and
retain that agreement when transporting the cyclic character extension to
the literal local ambient group. All three root-compatibility premises of
the older local-extension API are derived here.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalExtension

open Formalisation ModularRep
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SporadicFi24SelectedOuterAmbientLocalCharacterExtension
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterPairLocalCharacterExtension
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

local instance selectedOuterFinite
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

theorem exists_local_extension_with_retained_root_agreement
    (P : Definition35Problem.{u}) (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P) (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seedPair : PrimeRegularRootEmbedding P.p P.k P.K (SelectedPairStabilizer P S w)) :
    let weight := centerlessQuotientWeightBrauerSource P hcenter reference w
    let ambient := SelectedSpathAmbient P hcenter reference psi S haut
    ∃ localInflation : QuotientLocalInflationSource P reference w weight,
      ∃ fixedLocal : FixedLocalExtensionData localInflation ambient,
        localInflation.iota.lift = (P.localReduction w).iota.lift ∧
        ∀ zeta : rootsOfUnity (primeRegularExponent P.p
            (SelectedLocalBase P hcenter reference psi w S haut)) P.k,
          (localInflation.iota.alongMulEquiv
            (canonicalLocalBaseEquiv (w := w) ambient)).lift (((zeta : P.kˣ) : P.k)) =
            fixedLocal.localAmbientRoot.lift (((zeta : P.kˣ) : P.k)) := by
  dsimp only
  let weight := centerlessQuotientWeightBrauerSource P hcenter reference w
  let ambient := SelectedSpathAmbient P hcenter reference psi S haut
  let N := Subgroup.normalizer
    (quotientRadical P reference w : Set (CentralCharacterQuotient P reference))
  let QN := (quotientRadical P reference w).subgroupOf N
  let : QN.Normal := by
    dsimp only [QN, N]
    infer_instance
  have hQN : IsPGroup P.p QN := weight.radical.isPGroup.comap_subtype
  let rN : PrimeRegularRootEmbedding P.p P.k P.K N :=
    PrimeRegularRootEmbeddingPQuotient.ofPQuotient QN hQN weight.iota
  have rN_lift_weight (z : P.k) : rN.lift z = weight.iota.lift z :=
    PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift QN hQN weight.iota z
  have rN_lift_selected (z : P.k) :
      rN.lift z = (P.localReduction w).iota.lift z := by
    calc
      rN.lift z = weight.iota.lift z := rN_lift_weight z
      _ = (P.localReduction w).iota.lift z :=
        (P.localReduction w).iota.alongMulEquiv_lift
          (centerlessQuotientNormalizerEquiv P hcenter reference w) z
  have qCompat : SelectedQuotientInflationRootCompatibility P hcenter reference w rN := by
    intro x a
    exact rN_lift_weight a.1
  let localInflation := selectedQuotientLocalInflation P hcenter reference w rN qCompat
  let eN := selectedPairBaseEquivQuotientNormalizer P hcenter reference w S
  let rPB := selectedPairBaseRoot P hcenter reference w S rN
  have rPB_lift_rN (z : P.k) : rPB.lift z = rN.lift z :=
    rN.alongMulEquiv_lift eN.symm z
  have rPB_lift_selected (z : P.k) :
      rPB.lift z = (P.localReduction w).iota.lift z :=
    (rPB_lift_rN z).trans (rN_lift_selected z)
  let quotientInput := canonicalRawNormalizerQuotientInput (p := P.p) (K := P.K) (H := P.H)
  have baseCompat : SelectedPairBaseRootCompatibility P hcenter reference w S rN := by
    intro W x a
    change rPB.lift a.1 =
      (transportedLocalRootEmbedding (selectedOuterField S) P.blockSource P.block
        quotientInput w (P.localReduction w)).lift a.1
    exact (rPB_lift_selected a.1).trans
      ((P.localReduction w).iota.alongMulEquiv_lift
        (normalizerQuotientEquivLocalBase (selectedOuterField S) P.blockSource P.block
          quotientInput w) a.1).symm
  obtain ⟨pairRoot, pairAgreement⟩ :=
    PrimeRegularRootEmbedding.exists_ambient_agreeing_on_subgroup
      (SelectedPairBase P S w) rPB ⟨seedPair⟩
  have restrictionCompat :
      SelectedPairRestrictionRootCompatibility P hcenter reference w S rN pairRoot := by
    intro W extension
    exact Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
      extension.representation pairRoot rPB (SelectedPairBase P S w).subtype pairAgreement
  let eA := selectedPairStabilizerEquivAmbientLocalGroup
    P hcenter reference psi w S Omega hOmega hmatch haut
  let eB := selectedPairBaseEquivAmbientLocalBase
    P hcenter reference psi w S Omega hOmega hmatch haut
  obtain ⟨extension⟩ := selectedAmbientLocalBrauerCharacterExtension
    P hcenter reference psi w S Omega hOmega hmatch haut
    principle rN pairRoot qCompat baseCompat restrictionCompat
  let fixedLocal : FixedLocalExtensionData localInflation ambient :=
    { localAmbientRoot := pairRoot.alongMulEquiv eA
      localExtension := extension }
  refine ⟨localInflation, fixedLocal, funext rN_lift_selected, ?_⟩
  intro zeta
  have hExponent : primeRegularExponent P.p (SelectedPairBase P S w) =
      primeRegularExponent P.p (SelectedLocalBase P hcenter reference psi w S haut) :=
    congrArg (fun n : ℕ ↦ ordCompl[P.p] n) (Nat.card_congr eB.toEquiv)
  let zetaPair : rootsOfUnity
      (primeRegularExponent P.p (SelectedPairBase P S w)) P.k :=
    ⟨zeta.1, by simpa only [hExponent] using zeta.2⟩
  change (rN.alongMulEquiv (canonicalLocalBaseEquiv (w := w) ambient)).lift
      (((zeta : P.kˣ) : P.k)) = (pairRoot.alongMulEquiv eA).lift (((zeta : P.kˣ) : P.k))
  simp only [PrimeRegularRootEmbedding.alongMulEquiv_lift]
  calc
    rN.lift (((zeta : P.kˣ) : P.k)) = rPB.lift (((zeta : P.kˣ) : P.k)) :=
      (rPB_lift_rN (((zeta : P.kˣ) : P.k))).symm
    _ = pairRoot.lift (((zeta : P.kˣ) : P.k)) := pairAgreement zetaPair

theorem exists_local_extension_with_root_agreement
    (P : Definition35Problem.{u}) (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P) (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seedPair : PrimeRegularRootEmbedding P.p P.k P.K (SelectedPairStabilizer P S w)) :
    let weight := centerlessQuotientWeightBrauerSource P hcenter reference w
    let ambient := SelectedSpathAmbient P hcenter reference psi S haut
    ∃ localInflation : QuotientLocalInflationSource P reference w weight,
      ∃ fixedLocal : FixedLocalExtensionData localInflation ambient,
        ∀ zeta : rootsOfUnity (primeRegularExponent P.p
            (SelectedLocalBase P hcenter reference psi w S haut)) P.k,
          (localInflation.iota.alongMulEquiv
            (canonicalLocalBaseEquiv (w := w) ambient)).lift (((zeta : P.kˣ) : P.k)) =
            fixedLocal.localAmbientRoot.lift (((zeta : P.kˣ) : P.k)) := by
  obtain ⟨localInflation, fixedLocal, _, hlocal⟩ :=
    exists_local_extension_with_retained_root_agreement P hcenter reference psi w S
      Omega hOmega hmatch haut principle seedPair
  exact ⟨localInflation, fixedLocal, hlocal⟩
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
