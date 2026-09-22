import ModularRep.PaperProofs.CharacterInductionEquivariance
import ModularRep.PaperProofs.EvenFieldGallagherFormula

/-!
# Formula-level local-character endgame for Lemma 3.6

Gallagher's multiplication formula fixes the Clifford correspondent on the
inertia subgroup.  The standard induced-character formula then fixes the
original local character.  The two external inputs have their actual
mathematical forms; no arbitrary equivalence or assumed naturality square
appears.
-/

namespace ModularRep.PaperProofs.EvenFieldLocalCharacterFormula

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CharacterInductionEquivariance
open ModularRep.PaperProofs.EvenFieldGallagherFormula

universe u

variable {k N : Type u} [Field k] [CharZero k] [Group N] [Fintype N]

/-- Source-shaped Clifford input for a selected correspondent: the ambient
character is the character induced from that correspondent. -/
def HasCliffordInduction (I : Subgroup N)
    (kappa : Irr k I) (eta : Irr k N) : Prop :=
  (eta : N → k) = inducedCharacter I kappa

/-- The local-character conclusion of manuscript Lemma 3.6 from the exact
Gallagher product and Clifford induction formulas. -/
theorem localCharacter_fixed
    (I : Subgroup N) (tau : MulAut N)
    (stable : ∀ x : N, x ∈ I ↔ tau x ∈ I)
    (B : Subgroup I) [B.Normal]
    (difference_mem : ∀ x : I,
      x⁻¹ * restrictAut I tau stable x ∈ B)
    (extension : I → k)
    (extension_fixed : ∀ x : I,
      extension (restrictAut I tau stable x) = extension x)
    (kappa : Irr k I)
    (gallagher : HasGallagherFactorisation B extension kappa)
    (eta : Irr k N)
    (clifford : HasCliffordInduction I kappa eta) :
    twist k N eta tau = eta := by
  let tauI := restrictAut I tau stable
  have hkappa : twist k I kappa tauI = kappa :=
    EvenFieldGallagherFormula.character_fixed B tauI difference_mem
      extension extension_fixed kappa gallagher
  have hkappa_pointwise : ∀ x : I, kappa (tauI x) = kappa x := by
    intro x
    have h := congrArg (fun chi : Irr k I ↦ chi x) hkappa
    exact h
  have hinduced :
      (fun g ↦ inducedCharacter I kappa (tau g)) =
        inducedCharacter I kappa :=
    inducedCharacter_fixed I tau stable kappa hkappa_pointwise
  apply OrdinaryIrreducibleCharacter.ext
  intro g
  rw [twist_apply]
  calc
    eta (tau g) = inducedCharacter I kappa (tau g) :=
      congrFun clifford (tau g)
    _ = inducedCharacter I kappa g := congrFun hinduced g
    _ = eta g := (congrFun clifford g).symm

end ModularRep.PaperProofs.EvenFieldLocalCharacterFormula


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
