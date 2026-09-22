import ModularRep.PaperProofs.SporadicFi24P3QOneNormalisationFromSources
import ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport

/-!
# The `Q = 1` extension and intermediate-block obligations for `Fi'_{24}` at three

This file isolates only the two obligations left after the source-facing
Fischer correspondence has been normalised at the trivial radical subgroup.
The published cyclic-extension theorem remains the explicit
`BrauerCyclicExtensionPrinciple`; no BAW or iBAW assertion is assumed.

The first kernel step is the carrier bridge which was previously missing:
if a literal weight has the trivial radical conjugacy class, then the
representative selected by the Definition 3.5 carrier has subgroup `bot`.
Consequently its image in the central character quotient is also `bot`.

For such a pair, the ambient and local extension characters come from one
common cyclic extension.  At every intermediate subgroup the local normaliser
is the subgroup itself, so a supplied global block catalogue transports to
the local side and its selected block induces to itself.  The remaining
inputs are the cyclic-extension principle, quotient cyclicity, fixedness of
the precise base Brauer character, ambient root-lift compatibility, local
Brauer-character compatibility, and the global intermediate catalogues.
They are kept as separate arguments rather than bundled into an iBAW-shaped
certificate.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3QOneExtensionBlockObligationsFromSources

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SpathQOneCharacterExtensions
open ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport

universe u

/-! ## The normalised trivial-radical carrier -/

/-- If a literal Definition 3.5 weight lies over the trivial radical
conjugacy class, then the representative selected from its two quotient
carriers has literally trivial subgroup.  This is purely a quotient/orbit
deduction; no character correspondence is used. -/
theorem selectedRadical_eq_bot_of_radicalClass_eq_trivial
    (P : Definition35Problem.{u})
    (w : Definition35Weight P)
    (htrivial : IsRadicalSubgroup P.p (⊥ : Subgroup P.H))
    (hw : CharacterWeight.radicalClass w.1 =
      RadicalConjugacyClass.trivialClass htrivial) :
    selectedRadical P w = ⊥ := by
  let W := selectedCharacterWeight P.blockSource P.block w
  let Q0 : RadicalSubgroup (p := P.p) (G := P.H) := ⟨⊥, htrivial⟩
  have hclass :
      (Quotient.mk''
          (⟨W.subgroup, W.radical⟩ :
            RadicalSubgroup (p := P.p) (G := P.H)) :
        RadicalConjugacyClass (p := P.p) (G := P.H)) =
        (Quotient.mk'' Q0 :
          RadicalConjugacyClass (p := P.p) (G := P.H)) := by
    calc
      _ = CharacterWeight.radicalClass
          (Quotient.mk'' (Quotient.mk'' W) :
            CharacterWeight.ConjugacyClass
              (p := P.p) (K := P.K) (G := P.H)) :=
        (CharacterWeight.radicalClass_mk W).symm
      _ = CharacterWeight.radicalClass w.1 :=
        congrArg CharacterWeight.radicalClass
          (selectedCharacterWeight_spec P.blockSource P.block w)
      _ = RadicalConjugacyClass.trivialClass htrivial := hw
      _ = Quotient.mk'' Q0 := rfl
  have horbit :
      (⟨W.subgroup, W.radical⟩ :
        RadicalSubgroup (p := P.p) (G := P.H)) ∈
        MulAction.orbit P.H Q0 :=
    (MulAction.orbitRel_apply.mp (Quotient.exact hclass))
  rcases horbit with ⟨g, hg⟩
  have hvalue := congrArg
    (fun Q : RadicalSubgroup (p := P.p) (G := P.H) => Q.1) hg
  have hgbot : (g • Q0).1 = (⊥ : Subgroup P.H) := by
    ext x
    simp only [Q0, RadicalSubgroup.smul_eq_rightTwist_conj,
      RadicalSubgroup.rightTwist, Subgroup.mem_comap, Subgroup.mem_bot]
    simpa using (conj_eq_one_iff (a := g⁻¹) (b := x))
  change W.subgroup = (⊥ : Subgroup P.H)
  exact hvalue.symm.trans hgbot

/-- The central character quotient image of a normalised `Q = 1` weight is
literally the trivial subgroup. -/
theorem quotientRadical_eq_bot_of_radicalClass_eq_trivial
    (P : Definition35Problem.{u})
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (htrivial : IsRadicalSubgroup P.p (⊥ : Subgroup P.H))
    (hw : CharacterWeight.radicalClass w.1 =
      RadicalConjugacyClass.trivialClass htrivial) :
    quotientRadical P reference w = ⊥ := by
  unfold quotientRadical
  rw [selectedRadical_eq_bot_of_radicalClass_eq_trivial P w htrivial hw]
  exact Subgroup.map_bot _

/-- Source-facing form of the preceding result.  An equality with the
canonical weight `T.atOne d` is exactly the output provided by the
normalisation theorem in `SporadicFi24P3QOneNormalisationFromSources`. -/
theorem quotientRadical_eq_bot_of_weight_eq_atOne
    (P : Definition35Problem.{u})
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (T : TrivialWeightSource (p := P.p) (X := P.H))
    (d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H))
    (hw : w.1 = T.atOne d) :
    quotientRadical P reference w = ⊥ := by
  apply quotientRadical_eq_bot_of_radicalClass_eq_trivial
    P reference w T.trivialRadical
  calc
    CharacterWeight.radicalClass w.1 =
        CharacterWeight.radicalClass (T.atOne d) :=
      congrArg CharacterWeight.radicalClass hw
    _ = RadicalConjugacyClass.trivialClass T.trivialRadical :=
      T.radicalClass_atOne d

/-! ## One common extension from the cyclic-extension theorem -/

/-- The local coherence packet at `Q = 1` has no radical source field once
normalisation is known.  Its sole external equality identifies the local
Brauer character with the transported global one. -/
theorem localTransportDataOfWeightEqAtOne
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation : QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient)
    (T : TrivialWeightSource (p := P.p) (X := P.H))
    (d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H))
    (hw : w.1 = T.atOne d)
    (localBrauerCompatibility :
      PrimeRegularClassFunction.pullback
          (qOneAmbientBaseEquiv ambient
            (quotientRadical_eq_bot_of_weight_eq_atOne
              P reference w T d hw)).symm.toMonoidHom
          (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
            ambient.baseEquiv quotient.brauer).1 =
        (IrreducibleBrauerCharacter.alongMulEquiv localInflation.iota
          (canonicalLocalBaseEquiv ambient) localInflation.brauer).1) :
    QOneLocalTransportData localInflation ambient where
  quotientRadical_eq_bot :=
    quotientRadical_eq_bot_of_weight_eq_atOne P reference w T d hw
  localBrauerCompatibility := localBrauerCompatibility

/-- Choose the single common representation extension supplied by Navarro's
cyclic-extension theorem.  Fixedness of the precise base Brauer character is
kept explicit; the result is much smaller than a BAW/iBAW certificate. -/
noncomputable def commonExtensionOfCyclicSources
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (principle :
      Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (hcyclic : IsCyclic (ambient.A ⧸ ambient.base))
    (hfixed : ∀ a : ambient.A,
      IrreducibleBrauerCharacter.twist
          (quotient.iota.alongMulEquiv ambient.baseEquiv)
          (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
            ambient.baseEquiv quotient.brauer)
          (MulAut.conjNormal a) =
        IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
          ambient.baseEquiv quotient.brauer) :
    LiveQOneCommonExtensionData ambient :=
  Classical.choice <|
    exists_qOneCommonExtensionData principle
      (quotient.iota.alongMulEquiv ambient.baseEquiv)
      (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
        ambient.baseEquiv quotient.brauer)
      hcyclic hfixed

/-- Construct the compatible global/local extension packet at the normalised
trivial radical.  Both characters are transports of the one extension chosen
above; compatible extensions are not assumed as an output-shaped source. -/
noncomputable def characterExtensionsOfWeightEqAtOneFromCyclicSources
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation : QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient)
    (T : TrivialWeightSource (p := P.p) (X := P.H))
    (d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H))
    (hw : w.1 = T.atOne d)
    (principle :
      Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (hcyclic : IsCyclic (ambient.A ⧸ ambient.base))
    (hfixed : ∀ a : ambient.A,
      IrreducibleBrauerCharacter.twist
          (quotient.iota.alongMulEquiv ambient.baseEquiv)
          (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
            ambient.baseEquiv quotient.brauer)
          (MulAut.conjNormal a) =
        IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
          ambient.baseEquiv quotient.brauer)
    (ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A)
    (hlift : (quotient.iota.alongMulEquiv ambient.baseEquiv).lift =
      ambientRoot.lift)
    (localBrauerCompatibility :
      PrimeRegularClassFunction.pullback
          (qOneAmbientBaseEquiv ambient
            (quotientRadical_eq_bot_of_weight_eq_atOne
              P reference w T d hw)).symm.toMonoidHom
          (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
            ambient.baseEquiv quotient.brauer).1 =
        (IrreducibleBrauerCharacter.alongMulEquiv localInflation.iota
          (canonicalLocalBaseEquiv ambient) localInflation.brauer).1) :
    SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient :=
  spathCharacterExtensionsOfQOneCommon
    (commonExtensionOfCyclicSources ambient principle hcyclic hfixed)
    ambientRoot hlift
    (localTransportDataOfWeightEqAtOne localInflation ambient T d hw
      localBrauerCompatibility)

/-! ## Intermediate block equality from global catalogues -/

/-- At every intermediate group, transport the supplied global block
catalogue across the literal `Q = 1` carrier equality.  The local catalogue,
local restriction, and block-induction equality are deductions, not source
fields. -/
noncomputable def intermediateBlockSourceOfWeightEqAtOneFromGlobal
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation : QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient)
    (T : TrivialWeightSource (p := P.p) (X := P.H))
    (d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H))
    (hw : w.1 = T.atOne d)
    (common : LiveQOneCommonExtensionData ambient)
    (ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A)
    (hlift : (quotient.iota.alongMulEquiv ambient.baseEquiv).lift =
      ambientRoot.lift)
    (localBrauerCompatibility :
      PrimeRegularClassFunction.pullback
          (qOneAmbientBaseEquiv ambient
            (quotientRadical_eq_bot_of_weight_eq_atOne
              P reference w T d hw)).symm.toMonoidHom
          (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
            ambient.baseEquiv quotient.brauer).1 =
        (IrreducibleBrauerCharacter.alongMulEquiv localInflation.iota
          (canonicalLocalBaseEquiv ambient) localInflation.brauer).1)
    (global : QOneIntermediateGlobalBlockSource
      (spathCharacterExtensionsOfQOneCommon common ambientRoot hlift
        (localTransportDataOfWeightEqAtOne localInflation ambient T d hw
          localBrauerCompatibility))) :
    IntermediateBlockSource P reference psi w quotient weight localInflation
      ambient
        (spathCharacterExtensionsOfQOneCommon common ambientRoot hlift
          (localTransportDataOfWeightEqAtOne localInflation ambient T d hw
            localBrauerCompatibility)) :=
  intermediateBlockSourceOfQOneGlobal common ambientRoot hlift
    (localTransportDataOfWeightEqAtOne localInflation ambient T d hw
      localBrauerCompatibility) global

end ModularRep.PaperProofs.SporadicFi24P3QOneExtensionBlockObligationsFromSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
