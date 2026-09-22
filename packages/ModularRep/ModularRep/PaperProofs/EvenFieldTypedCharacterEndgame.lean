import Mathlib.Logic.Equiv.Defs

/-!
# Typed Gallagher and Clifford correspondences for Lemma 3.6

The earlier relational endgame was useful for isolating the logical pattern,
but arbitrary relations could conceal the selected fixed-point conclusion.
Here the two cited correspondences have their published functional shape:

* after choosing an extension, Gallagher gives an equivalence from quotient
  characters to characters above the fixed constituent;
* Clifford correspondence gives an equivalence from that fibre to the
  characters of the full normaliser lying above the constituent.

The only action assumptions are universal commuting squares for these
equivalences.  No selected correspondent or selected local character is
assumed fixed.
-/

namespace ModularRep.PaperProofs.EvenFieldTypedCharacterEndgame

universe uE uQ uC uL

/-- Source-shaped input for the typed Gallagher and Clifford endgame.
`gallagher` depends on the selected extension, as in Gallagher's theorem.
The two naturality fields are universally quantified commuting diagrams. -/
structure Data
    (Extension : Type uE) (QuotientCharacter : Type uQ)
    (Correspondent : Type uC) (LocalCharacter : Type uL)
    (extensionAction : Extension → Extension)
    (quotientAction : QuotientCharacter → QuotientCharacter)
    (correspondentAction : Correspondent → Correspondent)
    (localAction : LocalCharacter → LocalCharacter) where
  extension : Extension
  extensionFixed : extensionAction extension = extension
  gallagher : Extension → (QuotientCharacter ≃ Correspondent)
  clifford : Correspondent ≃ LocalCharacter
  gallagher_natural : ∀ ext xi,
    correspondentAction (gallagher ext xi) =
      gallagher (extensionAction ext) (quotientAction xi)
  clifford_natural : ∀ kappa,
    localAction (clifford kappa) = clifford (correspondentAction kappa)

variable
    {Extension : Type uE}
    {QuotientCharacter : Type uQ}
    {Correspondent : Type uC}
    {LocalCharacter : Type uL}
    {extensionAction : Extension → Extension}
    {quotientAction : QuotientCharacter → QuotientCharacter}
    {correspondentAction : Correspondent → Correspondent}
    {localAction : LocalCharacter → LocalCharacter}

/-- The Clifford correspondent of a selected local character is fixed. -/
theorem correspondentOfLocal_fixed
    (D : Data Extension QuotientCharacter Correspondent LocalCharacter
      extensionAction quotientAction correspondentAction localAction)
    (quotientCharactersFixed : ∀ xi, quotientAction xi = xi)
    (eta : LocalCharacter) :
    correspondentAction (D.clifford.symm eta) = D.clifford.symm eta := by
  let kappa := D.clifford.symm eta
  let xi := (D.gallagher D.extension).symm kappa
  have hkappa : D.gallagher D.extension xi = kappa := by
    exact (D.gallagher D.extension).apply_symm_apply kappa
  calc
    correspondentAction kappa =
        correspondentAction (D.gallagher D.extension xi) :=
      congrArg correspondentAction hkappa.symm
    _ = D.gallagher (extensionAction D.extension) (quotientAction xi) :=
      D.gallagher_natural D.extension xi
    _ = D.gallagher D.extension xi := by
      rw [D.extensionFixed, quotientCharactersFixed]
    _ = kappa := hkappa

/-- The typed Gallagher and Clifford correspondences fix the selected local
character. -/
theorem localCharacter_fixed
    (D : Data Extension QuotientCharacter Correspondent LocalCharacter
      extensionAction quotientAction correspondentAction localAction)
    (quotientCharactersFixed : ∀ xi, quotientAction xi = xi)
    (eta : LocalCharacter) :
    localAction eta = eta := by
  let kappa := D.clifford.symm eta
  have heta : D.clifford kappa = eta := D.clifford.apply_symm_apply eta
  calc
    localAction eta = localAction (D.clifford kappa) :=
      congrArg localAction heta.symm
    _ = D.clifford (correspondentAction kappa) := D.clifford_natural kappa
    _ = D.clifford kappa :=
      congrArg D.clifford
        (correspondentOfLocal_fixed D quotientCharactersFixed eta)
    _ = eta := heta

end ModularRep.PaperProofs.EvenFieldTypedCharacterEndgame


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
