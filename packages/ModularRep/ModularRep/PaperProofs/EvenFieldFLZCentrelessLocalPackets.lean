import ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel

/-!
# Local character packets in the centreless FLZ specialisation

For a centreless `Definition35Problem`, the central character quotient map is
an equivalence.  This module transports the selected radical subgroup, its
defect-zero ordinary character, and its Brauer reduction across that
equivalence.  Thus the quotient-weight packet is derived rather than supplied
as source data.

The final construction inflates a quotient-local Brauer character to the
normaliser.  Its only additional input is compatibility of the chosen root
embeddings along the quotient map.  No character extension, block equality,
BAW, or iBAW conclusion is used or proved here.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

local instance subgroupFintype {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- The canonical quotient map, regarded as a group equivalence in the
centreless case. -/
def centerlessCentralCharacterQuotientMapEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P) :
    P.H ≃* CentralCharacterQuotient P reference :=
  MulEquiv.ofBijective
    (centralCharacterQuotientMap P reference)
    (centralCharacterQuotientMap_bijective_of_centerless
      P hcenter reference)

theorem centerlessCentralCharacterQuotientMapEquiv_apply
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (x : P.H) :
    centerlessCentralCharacterQuotientMapEquiv P hcenter reference x =
      centralCharacterQuotientMap P reference x :=
  rfl

@[simp]
theorem centerlessCentralCharacterQuotientMapEquiv_toMonoidHom
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P) :
    (centerlessCentralCharacterQuotientMapEquiv
      P hcenter reference).toMonoidHom =
        centralCharacterQuotientMap P reference :=
  rfl

/-- In the centreless case the canonical quotient map induces an equivalence
between the two local normaliser quotients. -/
def centerlessQuotientNormalizerEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P) :
    NormalizerQuotient (selectedRadical P w) ≃*
      NormalizerQuotient (quotientRadical P reference w) := by
  let f := centralCharacterQuotientMap P reference
  have hf : Function.Bijective f :=
    centralCharacterQuotientMap_bijective_of_centerless
      P hcenter reference
  have hker : f.ker ≤ selectedRadical P w := by
    rw [(MonoidHom.ker_eq_bot_iff f).2 hf.1]
    exact bot_le
  exact normalizerQuotientEquivOfSurjectiveOfKerLE
    f hf.2 (selectedRadical P w) hker

/-- The forward map of the centreless normaliser equivalence is the canonical
normaliser-quotient map used in the quotient-weight source structure. -/
@[simp]
theorem centerlessQuotientNormalizerEquiv_toMonoidHom
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P) :
    (centerlessQuotientNormalizerEquiv
      P hcenter reference w).toMonoidHom =
        quotientNormalizerMap P reference w := by
  rfl

/-- For a centreless group, the quotient weight and its Brauer reduction are
obtained by transport from the selected literal weight. -/
def centerlessQuotientWeightBrauerSource
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P) :
    QuotientWeightBrauerSource P reference w := by
  let eH :=
    centerlessCentralCharacterQuotientMapEquiv P hcenter reference
  let eN :=
    centerlessQuotientNormalizerEquiv P hcenter reference w
  let theta :=
    (selectedCharacterWeight P.blockSource P.block w).localCharacter
  let source := P.localReduction w
  refine {
    radical := ?_
    ordinary := OrdinaryIrreducibleCharacter.mapEquiv theta eN
    defectZero :=
      (selectedCharacterWeight
        P.blockSource P.block w).defectZero.mapEquiv eN
    ordinaryDescends := ?_
    iota := source.iota.alongMulEquiv eN
    brauer :=
      IrreducibleBrauerCharacter.alongMulEquiv
        source.iota eN source.brauer
    reduction := ?_
    brauerDescends := ?_ }
  · change IsRadicalSubgroup P.p
      ((selectedRadical P w).map eH.toMonoidHom)
    exact
      (selectedCharacterWeight
        P.blockSource P.block w).radical.map_equiv eH
  · intro x
    rw [← centerlessQuotientNormalizerEquiv_toMonoidHom
      P hcenter reference w]
    exact congrArg theta (eN.symm_apply_apply x)
  · intro g
    change theta (eN.symm g.1) =
      source.brauer.1
        (PrimeRegularElement.map eN.symm.toMonoidHom g)
    convert source.reduction
      (PrimeRegularElement.map eN.symm.toMonoidHom g) using 1
    all_goals rfl
  · rw [← centerlessQuotientNormalizerEquiv_toMonoidHom
      P hcenter reference w]
    apply PrimeRegularClassFunction.ext
    intro x
    simp only [
      IrreducibleBrauerCharacter.alongMulEquiv_val,
      PrimeRegularClassFunction.pullback_apply
    ]
    congr 1
    apply Subtype.ext
    exact eN.symm_apply_apply x.1

/-- The quotient map from the normaliser of the quotient radical to its
normaliser quotient. -/
abbrev quotientLocalInflationMap
    (P : Definition35Problem.{u})
    (reference : Definition35Brauer P)
    (w : Definition35Weight P) :
    Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference)) →*
      NormalizerQuotient (quotientRadical P reference w) :=
  QuotientGroup.mk'
    ((quotientRadical P reference w).subgroupOf
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference))))

/-- Inflate the quotient-local Brauer character to the normaliser when the
chosen root embeddings are compatible along the quotient map. -/
def quotientLocalInflationSourceOfCompatible
    (P : Definition35Problem.{u})
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (weight : QuotientWeightBrauerSource P reference w)
    (iotaN : PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference))))
    (compatible : Representation.BrauerRootLiftCompatibleAlong
        (chosenIBrRepresentation weight.iota weight.brauer).ρ
        weight.iota iotaN
        (quotientLocalInflationMap P reference w)) :
    QuotientLocalInflationSource P reference w weight := by
  let QN :=
    (quotientRadical P reference w).subgroupOf
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference)))
  let q := quotientLocalInflationMap P reference w
  let V := chosenIBrRepresentation weight.iota weight.brauer
  let inflated : IBr iotaN := by
    refine ⟨PrimeRegularClassFunction.pullback q weight.brauer.1, ?_⟩
    refine ⟨FDRep.of (Representation.pullback V.ρ q), ?_, ?_⟩
    · exact
        (Classical.choose_spec weight.brauer.2).1.pullback q
          (QuotientGroup.mk'_surjective QN)
    · rw [FDRep.of_ρ']
      calc
        PrimeRegularClassFunction.pullback q weight.brauer.1 =
            PrimeRegularClassFunction.pullback q
              (Representation.brauerCharacterOfRootEmbedding
                V.ρ weight.iota) :=
          congrArg (PrimeRegularClassFunction.pullback q)
            (chosenIBrRepresentation_character
              weight.iota weight.brauer)
        _ =
            Representation.brauerCharacterOfRootEmbedding
              (Representation.pullback V.ρ q) iotaN :=
          (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
              V.ρ weight.iota iotaN q compatible).symm
  exact {
    iota := iotaN
    brauer := inflated
    inflation := rfl }

/-- The same inflation construction under equality of the two field-level
root lifts. -/
def quotientLocalInflationSourceOfLiftEq
    (P : Definition35Problem.{u})
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (weight : QuotientWeightBrauerSource P reference w)
    (iotaN : PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference))))
    (hlift : iotaN.lift = weight.iota.lift) :
    QuotientLocalInflationSource P reference w weight :=
  quotientLocalInflationSourceOfCompatible
    P reference w weight iotaN
    (fun _ a ↦ congrFun hlift a.1)

/-- In the centreless case, the only additional datum needed for local
inflation is a normaliser root embedding whose lift agrees with the selected
local root embedding. -/
def centerlessQuotientLocalInflationSourceOfLiftEq
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (iotaN : PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference))))
    (hlift : iotaN.lift = (P.localReduction w).iota.lift) :
    QuotientLocalInflationSource P reference w
      (centerlessQuotientWeightBrauerSource
        P hcenter reference w) := by
  let weight :=
    centerlessQuotientWeightBrauerSource P hcenter reference w
  apply quotientLocalInflationSourceOfLiftEq
    P reference w weight iotaN
  funext z
  calc
    iotaN.lift z = (P.localReduction w).iota.lift z :=
      congrFun hlift z
    _ = weight.iota.lift z := by
      exact (PrimeRegularRootEmbedding.alongMulEquiv_lift
        (P.localReduction w).iota
        (centerlessQuotientNormalizerEquiv
          P hcenter reference w) z).symm

end ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
