import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathWitness
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeTransport

/-!
# The extension packet's values on its own raw character

These equations unpack the actual extension, inflation, reduction and
ordinary-descent fields. They require no further compatibility input. The
normalizer map is the restriction of the same global embedding.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPacketValues

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeTransport

universe u

variable {P : Definition35Problem.{u}} {reference psi : Definition35Brauer P}
variable {w : Definition35Weight P}

def rawEmbedding (packet : SpathMatchedBlockCondition P reference psi w) :
    P.H →* packet.ambient.A :=
  (quotientToAmbient P reference psi packet.quotient packet.ambient).comp
    (centralCharacterQuotientMap P reference)

def rawNormalizerIntoLocal (packet : SpathMatchedBlockCondition P reference psi w) :
    Subgroup.normalizer (selectedRadical P w : Set P.H) →*
      AmbientLocalGroup P reference psi w packet.quotient packet.ambient :=
  (AmbientLocalBase P reference psi w packet.quotient packet.ambient).subtype.comp
    (packet.extensions.localBaseEquiv.toMonoidHom.comp
      (normalizerMap (centralCharacterQuotientMap P reference) (selectedRadical P w)))

theorem rawEmbedding_injective (packet : SpathMatchedBlockCondition P reference psi w)
    (hcenter : Subgroup.center P.H = ⊥) : Function.Injective (rawEmbedding packet) :=
  Subtype.val_injective.comp (packet.ambient.baseEquiv.injective.comp
    (centralCharacterQuotientMap_bijective_of_centerless P hcenter reference).1)

theorem rawEmbedding_range (packet : SpathMatchedBlockCondition P reference psi w) :
    (rawEmbedding packet).range = packet.ambient.base := by
  apply Subgroup.ext
  intro a
  constructor
  · rintro ⟨x, rfl⟩
    exact (packet.ambient.baseEquiv (centralCharacterQuotientMap P reference x)).2
  · intro ha
    obtain ⟨y, hy⟩ := packet.ambient.baseEquiv.surjective ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (centralCharacterKernel P reference) y
    exact ⟨x, congrArg Subtype.val hy⟩

theorem rawNormalizerIntoLocal_range
    (packet : SpathMatchedBlockCondition P reference psi w)
    (hcenter : Subgroup.center P.H = ⊥) :
    (rawNormalizerIntoLocal packet).range =
      AmbientLocalBase P reference psi w packet.quotient packet.ambient := by
  let f := centralCharacterQuotientMap P reference
  let Q := selectedRadical P w
  have hf : Function.Bijective f :=
    centralCharacterQuotientMap_bijective_of_centerless P hcenter reference
  have hker : f.ker ≤ Q := by
    intro x hx
    have hx1 : x = 1 := hf.1 ((show f x = 1 from hx).trans (map_one f).symm)
    rw [hx1]
    exact Q.one_mem
  have hsurj := normalizerMap_surjective f hf.2 Q hker
  apply Subgroup.ext
  intro d
  constructor
  · rintro ⟨n, rfl⟩
    exact (packet.extensions.localBaseEquiv (normalizerMap f Q n)).2
  · intro hd
    obtain ⟨y, hy⟩ := packet.extensions.localBaseEquiv.surjective ⟨d, hd⟩
    obtain ⟨n, rfl⟩ := hsurj y
    exact ⟨n, congrArg Subtype.val hy⟩

theorem rawNormalizerIntoLocal_natural
    (packet : SpathMatchedBlockCondition P reference psi w) :
    (AmbientLocalGroup P reference psi w packet.quotient packet.ambient).subtype.comp
        (rawNormalizerIntoLocal packet) =
      (rawEmbedding packet).comp (Subgroup.normalizer (selectedRadical P w : Set P.H)).subtype := by
  ext n
  exact packet.extensions.localBaseEquiv_natural
    (normalizerMap (centralCharacterQuotientMap P reference) (selectedRadical P w) n)

theorem packet_globalExtension_raw_value
    (packet : SpathMatchedBlockCondition P reference psi w)
    (x : PrimeRegularElement (G := P.H) P.p) :
    packet.extensions.globalExtension.1.1
      (PrimeRegularElement.map (rawEmbedding packet) x) = psi.1.1 x := by
  let A := packet.ambient
  let E := packet.extensions
  let y := PrimeRegularElement.map (centralCharacterQuotientMap P reference) x
  let z := PrimeRegularElement.map A.baseEquiv.toMonoidHom y
  have hinverse : PrimeRegularElement.map A.baseEquiv.symm.toMonoidHom z = y := by
    apply Subtype.ext
    exact A.baseEquiv.symm_apply_apply y.1
  have hrestrict := congrArg (fun chi => chi z) E.globalExtension.2
  change E.globalExtension.1.1 (PrimeRegularElement.map A.base.subtype z) =
    packet.quotient.brauer.1 (PrimeRegularElement.map A.baseEquiv.symm.toMonoidHom z) at hrestrict
  rw [hinverse] at hrestrict
  have hinflate := congrArg (fun chi => chi x) packet.quotient.inflation
  calc
    E.globalExtension.1.1 (PrimeRegularElement.map (rawEmbedding packet) x) =
      E.globalExtension.1.1 (PrimeRegularElement.map A.base.subtype z) := rfl
    _ = packet.quotient.brauer.1 y := hrestrict
    _ = psi.1.1 x := hinflate

theorem packet_localExtension_raw_value
    (packet : SpathMatchedBlockCondition P reference psi w)
    (n : PrimeRegularElement (G := Subgroup.normalizer (selectedRadical P w : Set P.H)) P.p) :
    packet.extensions.localExtension.1.1
      (PrimeRegularElement.map (rawNormalizerIntoLocal packet) n) =
      (selectedCharacterWeight P.blockSource P.block w).localCharacter (QuotientGroup.mk n.1) := by
  let Q := selectedRadical P w
  let N := Subgroup.normalizer (Q : Set P.H)
  let Qbar := quotientRadical P reference w
  let Nbar := Subgroup.normalizer (Qbar : Set (CentralCharacterQuotient P reference))
  let fN : N →* Nbar := normalizerMap (centralCharacterQuotientMap P reference) Q
  let qN : N →* NormalizerQuotient Q := QuotientGroup.mk' (Q.subgroupOf N)
  let qbar : Nbar →* NormalizerQuotient Qbar := QuotientGroup.mk' (Qbar.subgroupOf Nbar)
  let B := AmbientLocalBase P reference psi w packet.quotient packet.ambient
  let E := packet.extensions
  let nbar := PrimeRegularElement.map fN n
  let nB := PrimeRegularElement.map E.localBaseEquiv.toMonoidHom nbar
  have hinverse : PrimeRegularElement.map E.localBaseEquiv.symm.toMonoidHom nB = nbar := by
    apply Subtype.ext
    exact E.localBaseEquiv.symm_apply_apply nbar.1
  have hrestrict := congrArg (fun chi => chi nB) E.localExtension.2
  change E.localExtension.1.1 (PrimeRegularElement.map B.subtype nB) =
    packet.localInflation.brauer.1
      (PrimeRegularElement.map E.localBaseEquiv.symm.toMonoidHom nB) at hrestrict
  rw [hinverse] at hrestrict
  have hinflate := congrArg (fun chi => chi nbar) packet.localInflation.inflation
  have hreduce := packet.weight.reduction (PrimeRegularElement.map qbar nbar)
  have hord := packet.weight.ordinaryDescends (qN n.1)
  calc
    E.localExtension.1.1 (PrimeRegularElement.map (rawNormalizerIntoLocal packet) n) =
      E.localExtension.1.1 (PrimeRegularElement.map B.subtype nB) := rfl
    _ = packet.localInflation.brauer.1 nbar := hrestrict
    _ = packet.weight.brauer.1 (PrimeRegularElement.map qbar nbar) := hinflate.symm
    _ = packet.weight.ordinary (qbar nbar.1) := hreduce.symm
    _ = packet.weight.ordinary (quotientNormalizerMap P reference w (qN n.1)) := rfl
    _ = (selectedCharacterWeight P.blockSource P.block w).localCharacter (qN n.1) := hord

theorem packet_globalExtension_inner_value
    (packet : SpathMatchedBlockCondition P reference psi w)
    (g : P.H) (x : PrimeRegularElement (G := P.H) P.p) :
    packet.extensions.globalExtension.1.1
      (PrimeRegularElement.map ((rawEmbedding packet).comp (MulAut.conj g⁻¹).toMonoidHom) x) =
      psi.1.1 x := by
  exact (packet_globalExtension_raw_value packet
    (PrimeRegularElement.map (MulAut.conj g⁻¹).toMonoidHom x)).trans (psi.1.1.map_conj g⁻¹ x)

theorem packet_localExtension_representative_value
    (packet : SpathMatchedBlockCondition P reference psi w)
    (V : CharacterWeight P.p P.K P.H) (alpha : MulAut P.H)
    (hpair : (selectedCharacterWeight P.blockSource P.block w).rightTwist alpha = V)
    (n : PrimeRegularElement (G := Subgroup.normalizer (V.subgroup : Set P.H)) P.p) :
    packet.extensions.localExtension.1.1
      (PrimeRegularElement.map ((rawNormalizerIntoLocal packet).comp
        (backNormalizerEquiv (selectedCharacterWeight P.blockSource P.block w)
          V alpha hpair).toMonoidHom) n) =
      V.localCharacter (QuotientGroup.mk n.1) := by
  exact (packet_localExtension_raw_value packet
    (PrimeRegularElement.map
      (backNormalizerEquiv (selectedCharacterWeight P.blockSource P.block w)
        V alpha hpair).toMonoidHom n)).trans
    (ordinary_normalizer_values (selectedCharacterWeight P.blockSource P.block w)
      V alpha hpair n.1).symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPacketValues


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
