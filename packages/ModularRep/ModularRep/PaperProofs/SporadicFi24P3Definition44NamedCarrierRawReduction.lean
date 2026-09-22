import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCharacters
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeTransport
import ModularRep.BrauerReduction
import ModularRep.PrimeRegularRootEmbeddingPQuotient

/-!
# Own local reductions for the identity-ambient window

Each raw reduction is transported from the existing selected quotient
reduction family. The descriptor states only Navarro 3.18 reduction on
the normalizer quotient. Inflation and its root convention are derived
using the normal p-subgroup. There is no ambient character, matching,
extension or block equality in this descriptor or the external source.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCharacters

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

def rawNormalizerQuotientMap (V : CharacterWeight p K X) :
    Subgroup.normalizer (V.subgroup : Set X) →* NormalizerQuotient V.subgroup :=
  QuotientGroup.mk' (V.subgroup.subgroupOf (Subgroup.normalizer (V.subgroup : Set X)))

structure RawReductionSource (V : CharacterWeight p K X) where
  quotientRoot : PrimeRegularRootEmbedding p k K (NormalizerQuotient V.subgroup)
  quotientBrauer : IBr quotientRoot
  quotientReduction : IsBrauerReduction quotientRoot V.localCharacter quotientBrauer

namespace RawReductionSource

variable {V : CharacterWeight p K X} (source : RawReductionSource (k := k) V)

def rightTwist (alpha : MulAut X) : RawReductionSource (k := k) (V.rightTwist alpha) := by
  let e := (rightNormalizerQuotientEquiv alpha V.subgroup).symm
  exact {
    quotientRoot := source.quotientRoot.alongMulEquiv e
    quotientBrauer := IrreducibleBrauerCharacter.alongMulEquiv source.quotientRoot e source.quotientBrauer
    quotientReduction := fun x => source.quotientReduction (PrimeRegularElement.map e.symm.toMonoidHom x) }

def normalizerRoot : PrimeRegularRootEmbedding p k K (Subgroup.normalizer (V.subgroup : Set X)) :=
  PrimeRegularRootEmbeddingPQuotient.ofPQuotient
    (V.subgroup.subgroupOf (Subgroup.normalizer (V.subgroup : Set X)))
    V.radical.isPGroup.comap_subtype source.quotientRoot

theorem normalizerRoot_lift (z : k) : source.normalizerRoot.lift z = source.quotientRoot.lift z :=
  PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift _ _ _ z

def localBrauer : IBr source.normalizerRoot := by
  let q := rawNormalizerQuotientMap V
  let rep := chosenIBrRepresentation source.quotientRoot source.quotientBrauer
  refine ⟨PrimeRegularClassFunction.pullback q source.quotientBrauer.1, ?_⟩
  refine ⟨FDRep.of (Representation.pullback rep.ρ q), ?_, ?_⟩
  · exact (Classical.choose_spec source.quotientBrauer.2).1.pullback q
      (QuotientGroup.mk'_surjective _)
  · rw [FDRep.of_ρ']
    calc
      _ = PrimeRegularClassFunction.pullback q
          (Representation.brauerCharacterOfRootEmbedding rep.ρ source.quotientRoot) :=
        congrArg (PrimeRegularClassFunction.pullback q)
          (chosenIBrRepresentation_character source.quotientRoot source.quotientBrauer)
      _ = Representation.brauerCharacterOfRootEmbedding
          (Representation.pullback rep.ρ q) source.normalizerRoot :=
        (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
          rep.ρ source.quotientRoot source.normalizerRoot q
          (fun _ a => source.normalizerRoot_lift a.1)).symm

theorem localBrauer_reduction : NormalizerInflatedReduction V.subgroup V.localCharacter
    source.normalizerRoot source.localBrauer := by
  intro n
  exact source.quotientReduction (PrimeRegularElement.map (rawNormalizerQuotientMap V) n)

end RawReductionSource

def rawReductionOfSelected
    {Block : Type u} [MulAction (MulAut X)ᵐᵒᵖ Block]
    (R : LocalBlockInductionSource (p := p) (k := k) (K := K) (G := X) (Block := Block))
    (sources : ∀ (b : Block) (w : LiteralWeightFibre R b), SelectedLocalReductionSource R b w)
    (V : CharacterWeight p K X) : RawReductionSource (k := k) V := by
  let := R.operations.ambientBlockData.fintypeBlock
  let c : ConjugacyClass (p := p) (K := K) (G := X) := Quotient.mk'' (Quotient.mk'' V)
  let b := R.weightBlock c
  let w : LiteralWeightFibre R b := ⟨c, rfl⟩
  let W := selectedCharacterWeight R b w
  let source : RawReductionSource (k := k) W := {
    quotientRoot := (sources b w).iota
    quotientBrauer := (sources b w).brauer
    quotientReduction := (sources b w).reduction }
  have hexists :=
    SporadicFi24P3Definition44NamedCarrierRepresentativeTransport.exists_inner_raw W V
      (selectedCharacterWeight_spec R b w).symm
  exact (Classical.choose_spec hexists) ▸ source.rightTwist (MulAut.conj (Classical.choose hexists)⁻¹)

def selectedLocalReduction
    {Block : Type u} [MulAction (MulAut X)ᵐᵒᵖ Block]
    (R : LocalBlockInductionSource (p := p) (k := k) (K := K) (G := X) (Block := Block))
    (sources : ∀ V : CharacterWeight p K X, RawReductionSource (k := k) V)
    (b : Block) (w : LiteralWeightFibre R b) : SelectedLocalReductionSource R b w where
  iota := (sources (selectedCharacterWeight R b w)).quotientRoot
  brauer := (sources (selectedCharacterWeight R b w)).quotientBrauer
  reduction := (sources (selectedCharacterWeight R b w)).quotientReduction

theorem raw_atOne_values
    (iota : PrimeRegularRootEmbedding p k K X)
    (Omega : IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d)
    (phi : IBr iota) (V : CharacterWeight p K X)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass (p := p) (K := K) (G := X)) = Omega phi)
    (hV : V.subgroup = ⊥) :
    ∀ n : PrimeRegularElement (G := Subgroup.normalizer (V.subgroup : Set X)) p,
      V.localCharacter (QuotientGroup.mk n.1) =
        phi.1 (PrimeRegularElement.map (Subgroup.normalizer (V.subgroup : Set X)).subtype n) := by
  obtain ⟨d, hd, heval⟩ := exists_atOne_from_raw T V hV
  have hphi : D.reduce (iota := iota) d = phi :=
    Omega.injective ((hOne d).trans (hd.trans hclass))
  intro n
  exact (heval n.1).trans
    ((D.reduce_isReduction (iota := iota) d
      (PrimeRegularElement.map (Subgroup.normalizer (V.subgroup : Set X)).subtype n)).trans
      (congrArg (fun chi : IBr iota => chi.1
        (PrimeRegularElement.map (Subgroup.normalizer (V.subgroup : Set X)).subtype n)) hphi))

theorem localBrauer_atOne
    (iota : PrimeRegularRootEmbedding p k K X)
    (Omega : IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d)
    (phi : IBr iota) (V : CharacterWeight p K X)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass (p := p) (K := K) (G := X)) = Omega phi)
    (source : RawReductionSource (k := k) V) (hV : V.subgroup = ⊥) :
    PrimeRegularClassFunction.pullback (Subgroup.normalizer (V.subgroup : Set X)).subtype phi.1 =
      source.localBrauer.1 := by
  apply PrimeRegularClassFunction.ext
  intro n
  exact (raw_atOne_values iota Omega D T hOne phi V hclass hV n).symm.trans
    (source.localBrauer_reduction n)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
