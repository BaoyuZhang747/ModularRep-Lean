import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneExtensions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual
import ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets

/-!
# The Q=1 base-character identity from the same normalized correspondence

Extract the ordinary character from the selected raw weight itself. The
normalization of Omega identifies its reduction with the matched theta.
The actual ordinary descent and Brauer inflation equations then identify
the two base characters, independently of root-lift equality.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCharacters

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathQOneCharacterExtensions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC

universe u

theorem exists_atOne_from_raw
    {p : ℕ} {K X : Type u} [Field K] [CharZero K] [Group X] [Fintype X]
    (T : TrivialWeightSource (p := p) (X := X))
    (W : CharacterWeight p K X) (hQ : W.subgroup = ⊥) :
    ∃ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      T.atOne d = (Quotient.mk'' (Quotient.mk'' W) : WeightClass (p := p) (K := K) (X := X)) ∧
      ∀ n : Subgroup.normalizer (W.subgroup : Set X),
        W.localCharacter (QuotientGroup.mk n) = d.1 n.1 := by
  rcases W with ⟨hprime, Q, hradical, chi, hdefect⟩
  change Q = ⊥ at hQ
  subst Q
  let e : NormalizerQuotient (⊥ : Subgroup X) ≃* X := trivialNormalizerQuotientEquiv
  let d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X) :=
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
    change chi (QuotientGroup.mk n) = chi (trivialNormalizerQuotientEquiv.symm n.1)
    rw [trivialNormalizerQuotientEquiv_symm_apply]
    rfl

theorem selected_raw_reduction_eq_theta
    (P : Definition35Problem.{u}) (M : EquivariantMatch P)
    (D : DefectZeroReductionSource P.iota) (T : TrivialWeightSource (p := P.p) (X := P.H))
    (hOmegaOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
      M.Omega (D.reduce (iota := P.iota) d) = T.atOne d)
    (hQ : selectedRadical P M.weight = ⊥) :
    ∀ n : PrimeRegularElement
        (G := Subgroup.normalizer (selectedRadical P M.weight : Set P.H)) P.p,
      (selectedCharacterWeight P.blockSource P.block M.weight).localCharacter
          (QuotientGroup.mk n.1) =
        M.theta.1.1 (PrimeRegularElement.map
          (Subgroup.normalizer (selectedRadical P M.weight : Set P.H)).subtype n) := by
  obtain ⟨d, hd, heval⟩ := exists_atOne_from_raw T
    (selectedCharacterWeight P.blockSource P.block M.weight) hQ
  have hw : T.atOne d = M.weight.1 :=
    hd.trans (selectedCharacterWeight_spec P.blockSource P.block M.weight)
  have htheta : M.theta.1 = D.reduce (iota := P.iota) d :=
    M.Omega.injective (M.matched.symm.trans (hw.symm.trans (hOmegaOne d).symm))
  intro n
  exact (heval n.1).trans
    ((D.reduce_isReduction (iota := P.iota) d
      (PrimeRegularElement.map
        (Subgroup.normalizer (selectedRadical P M.weight : Set P.H)).subtype n)).trans
      (congrArg (fun phi : IBr P.iota => phi.1
        (PrimeRegularElement.map
          (Subgroup.normalizer (selectedRadical P M.weight : Set P.H)).subtype n)) htheta.symm))

theorem localInflation_eq_global_restriction
    (P : Definition35Problem.{u}) (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P} {w : Definition35Weight P}
    (quotient : CentralQuotientBrauerSource P reference psi)
    (weight : QuotientWeightBrauerSource P reference w)
    (localInflation : QuotientLocalInflationSource P reference w weight)
    (hraw : ∀ n : PrimeRegularElement
        (G := Subgroup.normalizer (selectedRadical P w : Set P.H)) P.p,
      (selectedCharacterWeight P.blockSource P.block w).localCharacter (QuotientGroup.mk n.1) =
        psi.1.1 (PrimeRegularElement.map
          (Subgroup.normalizer (selectedRadical P w : Set P.H)).subtype n)) :
    localInflation.brauer.1 = PrimeRegularClassFunction.pullback
      (Subgroup.normalizer (quotientRadical P reference w :
        Set (CentralCharacterQuotient P reference))).subtype quotient.brauer.1 := by
  let Q := selectedRadical P w
  let N := Subgroup.normalizer (Q : Set P.H)
  let Qbar := quotientRadical P reference w
  let Nbar := Subgroup.normalizer (Qbar : Set (CentralCharacterQuotient P reference))
  let eH := centerlessCentralCharacterQuotientMapEquiv P hcenter reference
  let eN : N ≃* Nbar := ModularRep.normalizerEquiv eH Q
  let qN : N →* NormalizerQuotient Q := QuotientGroup.mk' (Q.subgroupOf N)
  let qNbar : Nbar →* NormalizerQuotient Qbar := QuotientGroup.mk' (Qbar.subgroupOf Nbar)
  apply PrimeRegularClassFunction.ext
  intro nbar
  let n := PrimeRegularElement.map eN.symm.toMonoidHom nbar
  have hn : eN n.1 = nbar.1 := eN.apply_symm_apply nbar.1
  have hq : quotientNormalizerMap P reference w (qN n.1) = qNbar nbar.1 := by
    change qNbar (normalizerMap (centralCharacterQuotientMap P reference) Q n.1) = qNbar nbar.1
    apply congrArg qNbar
    exact (show normalizerMap (centralCharacterQuotientMap P reference) Q n.1 = eN n.1
      from Subtype.ext rfl).trans hn
  have hbase : PrimeRegularElement.map (centralCharacterQuotientMap P reference)
      (PrimeRegularElement.map N.subtype n) = PrimeRegularElement.map Nbar.subtype nbar := by
    apply Subtype.ext
    change eH n.1.1 = nbar.1.1
    exact congrArg (fun z : Nbar => z.1) hn
  have hI := congrArg (fun chi => chi nbar) localInflation.inflation
  have hR := weight.reduction (PrimeRegularElement.map qNbar nbar)
  have hO := weight.ordinaryDescends (qN n.1)
  have hG := congrArg (fun chi => chi (PrimeRegularElement.map N.subtype n)) quotient.inflation
  calc
    localInflation.brauer.1 nbar = weight.brauer.1 (PrimeRegularElement.map qNbar nbar) := hI.symm
    _ = weight.ordinary (qNbar nbar.1) := hR.symm
    _ = weight.ordinary (quotientNormalizerMap P reference w (qN n.1)) := congrArg weight.ordinary hq.symm
    _ = (selectedCharacterWeight P.blockSource P.block w).localCharacter (qN n.1) := hO
    _ = psi.1.1 (PrimeRegularElement.map N.subtype n) := hraw n
    _ = quotient.brauer.1 (PrimeRegularElement.map (centralCharacterQuotientMap P reference)
        (PrimeRegularElement.map N.subtype n)) := hG.symm
    _ = quotient.brauer.1 (PrimeRegularElement.map Nbar.subtype nbar) := congrArg quotient.brauer.1 hbase
    _ = (PrimeRegularClassFunction.pullback Nbar.subtype quotient.brauer.1) nbar := rfl

theorem qOneLocalDataOfNormalizedMatch
    (P : Definition35Problem.{u}) (M : EquivariantMatch P)
    (hcenter : Subgroup.center P.H = ⊥) (reference : Definition35Brauer P)
    (D : DefectZeroReductionSource P.iota) (T : TrivialWeightSource (p := P.p) (X := P.H))
    (hOmegaOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
      M.Omega (D.reduce (iota := P.iota) d) = T.atOne d)
    (hQ : selectedRadical P M.weight = ⊥)
    {quotient : CentralQuotientBrauerSource P reference M.theta}
    {weight : QuotientWeightBrauerSource P reference M.weight}
    (localInflation : QuotientLocalInflationSource P reference M.weight weight)
    (ambient : SpathAmbientGroup P reference M.theta quotient) :
    QOneLocalTransportData localInflation ambient := by
  have hQbar : quotientRadical P reference M.weight = ⊥ := by
    unfold quotientRadical
    rw [hQ]
    exact Subgroup.map_bot _
  have hlocal := localInflation_eq_global_restriction P hcenter quotient weight localInflation
    (selected_raw_reduction_eq_theta P M D T hOmegaOne hQ)
  refine { quotientRadical_eq_bot := hQbar, localBrauerCompatibility := ?_ }
  apply PrimeRegularClassFunction.ext
  intro a
  let Nbar := Subgroup.normalizer (quotientRadical P reference M.weight :
    Set (CentralCharacterQuotient P reference))
  let n := PrimeRegularElement.map (canonicalLocalBaseEquiv ambient).symm.toMonoidHom a
  have hmap : PrimeRegularElement.map ambient.baseEquiv.symm.toMonoidHom
      (PrimeRegularElement.map (qOneAmbientBaseEquiv ambient hQbar).symm.toMonoidHom a) =
      PrimeRegularElement.map Nbar.subtype n := by
    apply Subtype.ext
    apply ambient.baseEquiv.injective
    apply ambient.base.subtype_injective
    change (ambient.baseEquiv (ambient.baseEquiv.symm
      ((qOneAmbientBaseEquiv ambient hQbar).symm a.1))).1 =
      (ambient.baseEquiv (((canonicalLocalBaseEquiv ambient).symm a.1).1)).1
    rw [ambient.baseEquiv.apply_symm_apply]
    exact (canonicalLocalBaseEquiv_symm_natural ambient a.1).symm
  have hp := congrArg (fun chi => chi n) hlocal
  calc
    (PrimeRegularClassFunction.pullback (qOneAmbientBaseEquiv ambient hQbar).symm.toMonoidHom
      (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota ambient.baseEquiv quotient.brauer).1) a =
        quotient.brauer.1 (PrimeRegularElement.map ambient.baseEquiv.symm.toMonoidHom
          (PrimeRegularElement.map (qOneAmbientBaseEquiv ambient hQbar).symm.toMonoidHom a)) := rfl
    _ = quotient.brauer.1 (PrimeRegularElement.map Nbar.subtype n) := congrArg quotient.brauer.1 hmap
    _ = localInflation.brauer.1 n := hp.symm
    _ = (IrreducibleBrauerCharacter.alongMulEquiv localInflation.iota
      (canonicalLocalBaseEquiv ambient) localInflation.brauer).1 a := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCharacters


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
