import ModularRep.OrdinaryIrreducibleCharacterSurjectiveDescent
import ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

/-!
# Ordinary-character descent along the central prime-to-ell local map

This experimental module applies the neutral surjective-descent API to the
literal `qW`.  The Navarro--Tiep packet supplies only the surjectivity of that
group homomorphism.  The character-value premise is consumed twice by finite
averaging: once for the internally selected irreducible realisation and once
for the exact defect-zero `FDRep` witness.

No character weight, block relation, correspondence, BAW, iBAW, or Lemma 5.2
conclusion is constructed here.
-/

noncomputable section

namespace ModularRep.PaperProofs.CentralEllPrimeWeightLocalOrdinaryDescent

open ModularRep.OrdinaryIrreducibleCharacterSurjectiveDescent
open ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

universe u

/-- The ordinary irreducible character descended along the literal `qW`.
Its target carrier is written without relying on a public abbreviation from
the qW implementation module. -/
noncomputable def qWDescendedOrdinary
    {ell : Nat} {K X : Type u}
    [Field K] [CharZero K]
    [Group X] [Finite X] [Fact ell.Prime]
    (Z0 : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X)
    (hZ0PrimeTo : ¬ ell ∣ Nat.card Z0)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup ell Q)
    (S : NavarroTiep23cFixedCentralQuotientSource
      Z0 hZ0central hZ0PrimeTo Q hQ)
    (theta : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
    (hconstant : ∀ x : (qW Z0 Q).ker,
      theta (x : NormalizerQuotient Q) =
        theta (1 : NormalizerQuotient Q)) :
    OrdinaryIrreducibleCharacter.Irr K
      (NormalizerQuotient (Q.map (QuotientGroup.mk' Z0))) :=
  descendCharacter
    (qW Z0 Q)
    (qW_surjective_ofNavarroTiep
      Z0 hZ0central hZ0PrimeTo Q hQ S)
    theta hconstant

/-- The descended character pulls back to the supplied cover-local
character, in the manuscript orientation. -/
theorem qWDescendedOrdinary_factorisation
    {ell : Nat} {K X : Type u}
    [Field K] [CharZero K]
    [Group X] [Finite X] [Fact ell.Prime]
    (Z0 : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X)
    (hZ0PrimeTo : ¬ ell ∣ Nat.card Z0)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup ell Q)
    (S : NavarroTiep23cFixedCentralQuotientSource
      Z0 hZ0central hZ0PrimeTo Q hQ)
    (theta : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
    (hconstant : ∀ x : (qW Z0 Q).ker,
      theta (x : NormalizerQuotient Q) =
        theta (1 : NormalizerQuotient Q)) :
    theta.1 = fun x : NormalizerQuotient Q ↦
      qWDescendedOrdinary
        Z0 hZ0central hZ0PrimeTo Q hQ S theta hconstant
        (qW Z0 Q x) := by
  simpa only [qWDescendedOrdinary] using
    (descendCharacter_factorisation
      (qW Z0 Q)
      (qW_surjective_ofNavarroTiep
        Z0 hZ0central hZ0PrimeTo Q hQ S)
      theta hconstant)

/-- Defect zero descends using the same exact `FDRep` witness supplied by
`htheta` and the prime-to-`ell` cardinality of the literal qW kernel. -/
theorem qWDescendedOrdinary_defectZero
    {ell : Nat} {K X : Type u}
    [Field K] [CharZero K]
    [Group X] [Finite X] [Fact ell.Prime]
    (Z0 : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X)
    (hZ0PrimeTo : ¬ ell ∣ Nat.card Z0)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup ell Q)
    (S : NavarroTiep23cFixedCentralQuotientSource
      Z0 hZ0central hZ0PrimeTo Q hQ)
    (theta : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
    (hconstant : ∀ x : (qW Z0 Q).ker,
      theta (x : NormalizerQuotient Q) =
        theta (1 : NormalizerQuotient Q))
    (htheta : ModularRep.IsDefectZeroOrdinaryCharacter ell theta) :
    ModularRep.IsDefectZeroOrdinaryCharacter ell
      (qWDescendedOrdinary
        Z0 hZ0central hZ0PrimeTo Q hQ S theta hconstant) := by
  simpa only [qWDescendedOrdinary] using
    (descendCharacter_defectZero
      (qW Z0 Q)
      (qW_surjective_ofNavarroTiep
        Z0 hZ0central hZ0PrimeTo Q hQ S)
      (qW_ker_card_not_dvd Z0 Q hZ0central hZ0PrimeTo)
      theta hconstant htheta)

end ModularRep.PaperProofs.CentralEllPrimeWeightLocalOrdinaryDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
