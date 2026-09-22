import ModularRep.PaperProofs.EvenFieldSourceShaped

/-!
# A source-shaped representative proof for manuscript Lemma 3.6

This module combines the Lang calculation, restriction of a maximal
extension, innerness on the relative quotient, Gallagher factorisation, and
Clifford induction.  Deep representation theoretic results are exposed as
universal or relational inputs.  No field fixes a character, a correspondent,
a representative, or its orbit by assumption.
-/

namespace ModularRep.PaperProofs.EvenFieldLemma35

open ModularRep.ManuscriptVerification.EvenFieldFixed
open ModularRep.PaperProofs.EvenFieldCliffordEndgame
open ModularRep.PaperProofs.EvenFieldSourceShaped

universe u

variable {G Weight Value : Type u} [Group G] [MulAction G Weight]

/-- Source-shaped data for one generic-weight representative and one field
automorphism.  `maximalExtendibility` has the universal form of Späth's
theorem on the selected stabiliser.  `gallagherClifford` is relational and is
required for every extension returned by that theorem.

The normalising, equivariance, and uniqueness fields are the structural
consequences needed to instantiate ordinary Clifford theory.  None of them
asserts either fixation conclusion. -/
structure LocalData
    (F sigma : G →* G) (sigmaWeight : Weight → Weight)
    (weight : Weight) where
  langWitness : G
  rationalLeviRepresentative : G
  langEquation :
    langWitness⁻¹ * F langWitness = rationalLeviRepresentative
  rationalLeviRepresentative_fixed :
    sigma rationalLeviRepresentative = rationalLeviRepresentative

  Large : Type u
  largeGroup : Group Large
  inertia : let _ := largeGroup; Subgroup Large
  tau : Large
  tau_normalises_inertia :
    let _ := largeGroup
    ConjugatesInto inertia tau

  Lambda : Type u
  Unipotent : Lambda → Prop
  lambda : Lambda
  lambda_unipotent : Unipotent lambda
  Extends : Lambda → (Large → Value) → Prop
  maximalExtendibility :
    let _ := largeGroup
    ∀ lam, Unipotent lam →
      ∃ largeCharacter,
        Extends lam largeCharacter ∧
          IsConjugationInvariant largeCharacter

  RelativeQuotient : Type u
  relativeQuotientGroup : Group RelativeQuotient
  quotientInnerElement : RelativeQuotient

  Correspondent : Type u
  correspondentAction : Correspondent → Correspondent
  Multiplies :
    (inertia → Value) → (RelativeQuotient → Value) →
      Correspondent → Prop
  Induces : Correspondent → Weight → Prop

  gallagherClifford :
    let _ := largeGroup
    let _ := relativeQuotientGroup
    ∀ largeCharacter, Extends lambda largeCharacter →
      ∃ quotientCharacter correspondent,
        IsConjugationInvariant quotientCharacter ∧
          Multiplies (restrictFunction inertia largeCharacter)
            quotientCharacter correspondent ∧
          Induces correspondent weight

  multiplicationEquivariant :
    let _ := largeGroup
    let _ := relativeQuotientGroup
    ∀ extension quotientCharacter correspondent,
      Multiplies extension quotientCharacter correspondent →
        Multiplies
          (conjugationActionOnSubgroup inertia tau
            tau_normalises_inertia extension)
          (innerConjugationAction quotientInnerElement quotientCharacter)
          (correspondentAction correspondent)
  multiplicationUnique :
    ∀ extension quotientCharacter correspondent₁ correspondent₂,
      Multiplies extension quotientCharacter correspondent₁ →
        Multiplies extension quotientCharacter correspondent₂ →
          correspondent₁ = correspondent₂
  inductionEquivariant :
    ∀ correspondent representative,
      Induces correspondent representative →
        Induces (correspondentAction correspondent)
          (innerTwistElement sigma langWitness •
            sigmaWeight representative)
  inductionUnique :
    ∀ correspondent representative₁ representative₂,
      Induces correspondent representative₁ →
        Induces correspondent representative₂ →
          representative₁ = representative₂

/-- Every generic-weight representative carrying the exact source-shaped
data above has a field-stable orbit under the finite fixed-point group. -/
theorem representative_orbit_fixed
    (F sigma : G →* G) (sigmaWeight : Weight → Weight)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (weight : Weight)
    (D : LocalData (Value := Value) F sigma sigmaWeight weight) :
    let H := frobeniusFixedSubgroup F
    let _ : MulAction H Weight := MulAction.compHom Weight H.subtype
    MulAction.orbit H (sigmaWeight weight) = MulAction.orbit H weight := by
  dsimp only
  letI : Group D.Large := D.largeGroup
  letI : Group D.RelativeQuotient := D.relativeQuotientGroup
  obtain ⟨largeCharacter, hExtends, hLargeClass⟩ :=
    D.maximalExtendibility D.lambda D.lambda_unipotent
  obtain ⟨quotientCharacter, correspondent, hQuotientClass,
      hMultiplies, hInduces⟩ :=
    D.gallagherClifford largeCharacter hExtends
  let extension := restrictFunction D.inertia largeCharacter
  let extensionAction : (D.inertia → Value) → (D.inertia → Value) :=
    conjugationActionOnSubgroup D.inertia D.tau
      D.tau_normalises_inertia
  let quotientAction :
      (D.RelativeQuotient → Value) →
        (D.RelativeQuotient → Value) :=
    innerConjugationAction D.quotientInnerElement
  let weightAction : Weight → Weight :=
    fun representative ↦
      innerTwistElement sigma D.langWitness • sigmaWeight representative
  let endgame : Data (D.inertia → Value)
      (D.RelativeQuotient → Value) D.Correspondent Weight
      extensionAction quotientAction D.correspondentAction weightAction
      D.Multiplies D.Induces correspondent weight := {
    extension := extension
    quotientCharacter := quotientCharacter
    gallagherFactorisation := hMultiplies
    extensionFixed :=
      restricted_classFunction_fixed D.inertia D.tau
        D.tau_normalises_inertia largeCharacter hLargeClass
    quotientCharacterFixed :=
      innerConjugationAction_fixed D.quotientInnerElement
        quotientCharacter hQuotientClass
    multiplicationEquivariant := D.multiplicationEquivariant
    multiplicationUnique := D.multiplicationUnique
    cliffordInduction := hInduces
    inductionEquivariant := D.inductionEquivariant
    inductionUnique := D.inductionUnique
  }
  have hRepresentative : weightAction weight = weight :=
    (cliffordGallagherInduction_fixed endgame).2
  have hInner := innerTwistElement_mem_frobeniusFixedSubgroup
    F sigma D.langWitness D.rationalLeviRepresentative commute
      D.langEquation D.rationalLeviRepresentative_fixed
  let H := frobeniusFixedSubgroup F
  let _ : MulAction H Weight := MulAction.compHom Weight H.subtype
  let h : H := ⟨innerTwistElement sigma D.langWitness, hInner⟩
  apply inner_twist_fixed_implies_orbit_fixed sigmaWeight h weight
  exact hRepresentative

/-- Pointwise representative form of the generic-weight conclusion in
Lemma 3.6.  The predicate `Generic` selects the actual generic-weight
representatives.  For each selected representative, the external sources
must instantiate `LocalData`; Lean then derives equality of its orbit classes. -/
theorem generic_weight_orbit_classes_fixed
    (F sigma : G →* G) (sigmaWeight : Weight → Weight)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (Generic : Weight → Prop)
    (source : ∀ weight, Generic weight →
      LocalData (Value := Value) F sigma sigmaWeight weight) :
    let H := frobeniusFixedSubgroup F
    let _ : MulAction H Weight := MulAction.compHom Weight H.subtype
    ∀ weight, Generic weight →
      (Quotient.mk'' (sigmaWeight weight) : WeightOrbit H Weight) =
        Quotient.mk'' weight := by
  dsimp only
  let H := frobeniusFixedSubgroup F
  let _ : MulAction H Weight := MulAction.compHom Weight H.subtype
  intro weight hweight
  apply MulAction.orbitRel.Quotient.orbit_injective
  simpa using representative_orbit_fixed F sigma sigmaWeight commute weight
    (source weight hweight)

/-- The subset of the orbit quotient represented by points satisfying
`Generic`.  In the manuscript this is the set `\mathcal W(C)` of
`H`-conjugacy classes of generic weights belonging to the block. -/
def orbitClassesOf
    {H X : Type*} [Group H] [MulAction H X]
    (Generic : X → Prop) : Set (WeightOrbit H X) :=
  {omega | ∃ x, Generic x ∧ (Quotient.mk'' x : WeightOrbit H X) = omega}

/-- Class-level form of the generic-weight conclusion in Lemma 3.6.  This
closes the passage from a representative calculation to the actual set of
`H`-conjugacy classes occurring in the statement of the manuscript. -/
theorem generic_weight_classes_fixed
    (F sigma : G →* G) (sigmaWeight : Weight → Weight)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (compatible :
      let H := frobeniusFixedSubgroup F
      let _ : MulAction H Weight := MulAction.compHom Weight H.subtype
      ∀ h : H, ∀ x : Weight,
        sigmaWeight (h • x) =
          frobeniusFixedSubgroupHom F sigma commute h • sigmaWeight x)
    (Generic : Weight → Prop)
    (source : ∀ weight, Generic weight →
      LocalData (Value := Value) F sigma sigmaWeight weight) :
    let H := frobeniusFixedSubgroup F
    let _ : MulAction H Weight := MulAction.compHom Weight H.subtype
    ∀ omega, omega ∈ orbitClassesOf Generic →
      inducedOrbitMap (frobeniusFixedSubgroupHom F sigma commute)
          sigmaWeight compatible omega = omega := by
  dsimp only
  intro omega
  rintro ⟨weight, hweight, rfl⟩
  rw [inducedOrbitMap_mk]
  exact generic_weight_orbit_classes_fixed F sigma sigmaWeight commute
    Generic source weight hweight

section OrdinaryCharacters

variable {DualLabel Character : Type u} [Group DualLabel]

/-- The exact ordinary-character inputs used at the start of Lemma 3.6.
The label statement is the conjunction of membership in an `ell'`-series and
Cabanes--Enguehard's `ell`-element series statement for a unipotent block.
Disjointness of rational Lusztig series and field invariance of unipotent
characters are supplied universally, not for a preselected fixed character. -/
structure OrdinaryData
    (ell : ℕ) (Series : Character → DualLabel → Prop)
    (sigmaCharacter : Character → Character)
    (XC : Set Character) where
  seriesDisjoint : ∀ {chi : Character} {s t : DualLabel},
    Series chi s → Series chi t →
      ∃ x : DualLabel, t = x * s * x⁻¹
  fieldFixesUnipotent : ∀ chi,
    Series chi 1 → sigmaCharacter chi = chi
  labels : ∀ chi, chi ∈ XC →
    ∃ s t : DualLabel,
      Series chi s ∧ Series chi t ∧
        IsPrimeRegular ell s ∧
          ∃ a : ℕ, t ^ (ell ^ a) = 1

/-- The ordinary-character half of Lemma 3.6, derived from the two rational
series labels rather than assumed as field fixation. -/
theorem ordinary_characters_fixed
    (ell : ℕ) (Series : Character → DualLabel → Prop)
    (sigmaCharacter : Character → Character)
    (XC : Set Character)
    (D : OrdinaryData ell Series sigmaCharacter XC) :
    ∀ chi, chi ∈ XC → sigmaCharacter chi = chi := by
  intro chi hchi
  obtain ⟨s, t, hsSeries, htSeries, hs, ht⟩ := D.labels chi hchi
  exact common_series_character_fixed Series sigmaCharacter
    D.seriesDisjoint D.fieldFixesUnipotent hsSeries htSeries hs ht

end OrdinaryCharacters

section FullFieldGroup

variable {Automorphism DualLabel Character : Type u} [Group DualLabel]

/-- Project-relative form of the complete conclusion of Lemma 3.6.  For every
field automorphism, Lean proves pointwise fixation of `XC` and equality of the
generic-weight orbit classes.  The function `localSource` must instantiate
the exact source-shaped local data for each genuine generic representative;
it cannot supply either of the two equalities in the conclusion. -/
theorem lemma_3_5_pointwise
    (ell : ℕ) (Series : Character → DualLabel → Prop)
    (XC : Set Character)
    (F : G →* G)
    (sigmaG : Automorphism → G →* G)
    (characterAction : Automorphism → Character → Character)
    (weightAction : Automorphism → Weight → Weight)
    (Generic : Weight → Prop)
    (commute : ∀ a x, F (sigmaG a x) = sigmaG a (F x))
    (ordinarySource : ∀ a,
      OrdinaryData ell Series (characterAction a) XC)
    (localSource : ∀ a weight, Generic weight →
      LocalData (Value := Value) F (sigmaG a) (weightAction a) weight) :
    PointwiseFixed characterAction XC ∧
      (let H := frobeniusFixedSubgroup F
       let _ : MulAction H Weight := MulAction.compHom Weight H.subtype
       ∀ a weight, Generic weight →
         (Quotient.mk'' (weightAction a weight) : WeightOrbit H Weight) =
           Quotient.mk'' weight) := by
  constructor
  · intro a chi hchi
    exact ordinary_characters_fixed ell Series (characterAction a) XC
      (ordinarySource a) chi hchi
  · dsimp only
    intro a
    exact generic_weight_orbit_classes_fixed F (sigmaG a) (weightAction a)
      (commute a) Generic (localSource a)

/-- Exact class-level project statement corresponding to manuscript
Lemma 3.6.  The second conjunct concerns the induced field action on the set
of `H`-conjugacy classes of genuine generic weights, rather than merely a
chosen representative. -/
theorem lemma_3_5
    (ell : ℕ) (Series : Character → DualLabel → Prop)
    (XC : Set Character)
    (F : G →* G)
    (sigmaG : Automorphism → G →* G)
    (characterAction : Automorphism → Character → Character)
    (weightAction : Automorphism → Weight → Weight)
    (Generic : Weight → Prop)
    (commute : ∀ a x, F (sigmaG a x) = sigmaG a (F x))
    (compatible : ∀ a,
      let H := frobeniusFixedSubgroup F
      let _ : MulAction H Weight := MulAction.compHom Weight H.subtype
      ∀ h : H, ∀ x : Weight,
        weightAction a (h • x) =
          frobeniusFixedSubgroupHom F (sigmaG a) (commute a) h •
            weightAction a x)
    (ordinarySource : ∀ a,
      OrdinaryData ell Series (characterAction a) XC)
    (localSource : ∀ a weight, Generic weight →
      LocalData (Value := Value) F (sigmaG a) (weightAction a) weight) :
    PointwiseFixed characterAction XC ∧
      (let H := frobeniusFixedSubgroup F
       let _ : MulAction H Weight := MulAction.compHom Weight H.subtype
       ∀ a omega, omega ∈ orbitClassesOf Generic →
         inducedOrbitMap
             (frobeniusFixedSubgroupHom F (sigmaG a) (commute a))
             (weightAction a) (compatible a) omega = omega) := by
  constructor
  · intro a chi hchi
    exact ordinary_characters_fixed ell Series (characterAction a) XC
      (ordinarySource a) chi hchi
  · dsimp only
    intro a
    exact generic_weight_classes_fixed F (sigmaG a) (weightAction a)
      (commute a) (compatible a) Generic (localSource a)

end FullFieldGroup

end ModularRep.PaperProofs.EvenFieldLemma35


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
