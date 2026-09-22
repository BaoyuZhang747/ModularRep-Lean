import ModularRep.EvenFieldFixed
import ModularRep.PaperProofs.EvenFieldConcreteQuotient
import ModularRep.PaperProofs.EvenFieldTypedCharacterEndgame

/-!
# The two components of a generic weight in manuscript Lemma 3.6

The former abstraction let Clifford induction determine an arbitrary
`WeightRepresentative`.  That was too strong: a generic weight is a pair
consisting of a torus and a local character, whereas Clifford theory controls
only the local character.  This module separates the two deductions.

The torus is fixed because it is the characteristic Sylow `e`-torus attached
to a fixed Levi subgroup.  The local character is fixed by the
Clifford--Gallagher--induction argument.  Only after both equalities have been
proved are they combined into equality of the orbit of the pair.
-/

namespace ModularRep.PaperProofs.EvenFieldWeightPair

open ModularRep.ManuscriptVerification.EvenFieldFixed
open ModularRep.PaperProofs.EvenFieldConcreteQuotient
open ModularRep.PaperProofs.EvenFieldTypedCharacterEndgame

universe u

/-- Naturality of the characteristic-torus construction transfers fixation
of the Levi subgroup to fixation of its associated torus. -/
theorem characteristicTorus_fixed
    {Levi Torus : Type u}
    (centralSylow : Levi → Torus)
    (leviAction : Levi → Levi) (torusAction : Torus → Torus)
    (naturality : ∀ M, torusAction (centralSylow M) =
      centralSylow (leviAction M))
    (M : Levi) (hM : leviAction M = M) :
    torusAction (centralSylow M) = centralSylow M := by
  rw [naturality, hM]

/-- Source-shaped data for one generic-weight pair.  The typed Gallagher and
Clifford equivalences end in `LocalCharacter`, not in the whole pair.  Thus
they cannot supply the torus equality appearing in the conclusion. -/
structure Data
    (H Torus LocalCharacter Levi : Type u)
    [Group H] [MulAction H Torus] [MulAction H LocalCharacter]
    (sigmaTorus : Torus → Torus)
    (sigmaLocal : LocalCharacter → LocalCharacter)
    (torus : Torus) (localCharacter : LocalCharacter)
    (innerTwist : H) where
  levi : Levi
  centralSylow : Levi → Torus
  leviAction : Levi → Levi
  torusAction : Torus → Torus
  centralSylow_natural : ∀ M,
    torusAction (centralSylow M) = centralSylow (leviAction M)
  torus_is_centralSylow : torus = centralSylow levi
  levi_fixed : leviAction levi = levi

  torusAction_eq_innerTwist :
    torusAction torus = innerTwist • sigmaTorus torus

  localAction : LocalCharacter → LocalCharacter
  localAction_eq_innerTwist :
    localAction localCharacter = innerTwist • sigmaLocal localCharacter

  ExtensionCharacter : Type u
  quotientData : EvenFieldConcreteQuotient.Data
  Correspondent : Type u
  extensionAction : ExtensionCharacter → ExtensionCharacter
  correspondentAction : Correspondent → Correspondent
  characterData :
    let _ : Group quotientData.Inertia := quotientData.inertiaGroup
    let _ : quotientData.Base.Normal := quotientData.baseNormal
    EvenFieldTypedCharacterEndgame.Data ExtensionCharacter
      (EvenFieldConcreteQuotient.ClassFunction
        (quotientData.Inertia ⧸ quotientData.Base) quotientData.Value)
      Correspondent LocalCharacter extensionAction
      quotientData.quotientAction correspondentAction localAction

variable
    {H Torus LocalCharacter Levi : Type u}
    [Group H] [MulAction H Torus] [MulAction H LocalCharacter]
    {sigmaTorus : Torus → Torus}
    {sigmaLocal : LocalCharacter → LocalCharacter}
    {torus : Torus} {localCharacter : LocalCharacter} {innerTwist : H}

/-- The torus component is fixed under the inner-twisted field action. -/
theorem torus_fixed
    (D : Data H Torus LocalCharacter Levi sigmaTorus sigmaLocal
      torus localCharacter innerTwist) :
    D.torusAction torus = torus := by
  calc
    D.torusAction torus =
        D.torusAction (D.centralSylow D.levi) :=
      congrArg D.torusAction D.torus_is_centralSylow
    _ = D.centralSylow D.levi :=
      characteristicTorus_fixed D.centralSylow D.leviAction
        D.torusAction D.centralSylow_natural D.levi D.levi_fixed
    _ = torus := D.torus_is_centralSylow.symm

/-- Clifford--Gallagher induction fixes only the local-character component. -/
theorem localCharacter_fixed
    (D : Data H Torus LocalCharacter Levi sigmaTorus sigmaLocal
      torus localCharacter innerTwist) :
    D.localAction localCharacter = localCharacter := by
  letI : Group D.quotientData.Inertia := D.quotientData.inertiaGroup
  letI : D.quotientData.Base.Normal := D.quotientData.baseNormal
  exact EvenFieldTypedCharacterEndgame.localCharacter_fixed D.characterData
    D.quotientData.quotientCharactersFixed localCharacter

/-- The two separately proved component equalities give equality of the
`H`-orbit of the generic-weight pair. -/
theorem genericWeightPair_orbit_fixed
    (D : Data H Torus LocalCharacter Levi sigmaTorus sigmaLocal
      torus localCharacter innerTwist) :
    MulAction.orbit H (sigmaTorus torus, sigmaLocal localCharacter) =
      MulAction.orbit H (torus, localCharacter) := by
  apply inner_twist_fixed_implies_orbit_fixed
    (fun pair : Torus × LocalCharacter ↦
      (sigmaTorus pair.1, sigmaLocal pair.2)) innerTwist
      (torus, localCharacter)
  apply Prod.ext
  · change innerTwist • sigmaTorus torus = torus
    rw [← D.torusAction_eq_innerTwist]
    exact torus_fixed D
  · change innerTwist • sigmaLocal localCharacter = localCharacter
    rw [← D.localAction_eq_innerTwist]
    exact localCharacter_fixed D

end ModularRep.PaperProofs.EvenFieldWeightPair


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
