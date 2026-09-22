import ModularRep.PaperProofs.EvenFieldFLZSourceConditions

/-!
# Forward transport for Definition 3.5 witnesses

This module contains the kernel construction transporting a fixed Definition 3.5
iBAW witness between two fixed presentations from explicit carrier and
semantic adapters.  The source record contains
only the three carrier equivalences, their compatibility with the canonical
actions, and a forward implication between the two already fixed Definition
3.5 semantic relations.

In particular, it contains no iBAW witness, BAW-goodness assertion,
equation-(3.17) relation, arbitrary result proposition, or alternate target
semantics.  The carrier maps and the relation implication are source-facing
E1/U and E2/U inputs; `map` is their kernel construction.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZDefinition35Transport

open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u v

/-- Fixed-carrier data sufficient to transport a Definition 3.5 witness in
the forward direction.  The action instances in the naturality fields are
the canonical ones attached to the two literal problems. -/
structure Definition35ForwardTransport
    (P : Definition35Problem.{u})
    (Paut : Definition35AutomorphismStabilizerAdapter P)
    (Psource : FLZSourceSemantics P Paut)
    (Q : Definition35Problem.{v})
    (Qaut : Definition35AutomorphismStabilizerAdapter Q)
    (Qsource : FLZSourceSemantics Q Qaut) where
  gammaEquiv : P.Gamma ≃* Q.Gamma
  brauerEquiv : Definition35Brauer P ≃ Definition35Brauer Q
  weightEquiv : Definition35Weight P ≃ Definition35Weight Q
  brauer_naturality :
    let _ : MulAction P.Gamma (Definition35Brauer P) :=
      definition35BrauerAction P
    let _ : MulAction Q.Gamma (Definition35Brauer Q) :=
      definition35BrauerAction Q
    ∀ (g : P.Gamma) (psi : Definition35Brauer P),
      brauerEquiv (g • psi) = gammaEquiv g • brauerEquiv psi
  weight_naturality :
    let _ : MulAction P.Gamma (Definition35Weight P) :=
      definition35WeightAction P
    let _ : MulAction Q.Gamma (Definition35Weight Q) :=
      definition35WeightAction Q
    ∀ (g : P.Gamma) (w : Definition35Weight P),
      weightEquiv (g • w) = gammaEquiv g • weightEquiv w
  relation_forward : ∀ (psi : Definition35Brauer P) (w : Definition35Weight P),
    Psource.definition35BlockIsomorphic psi w →
      Qsource.definition35BlockIsomorphic (brauerEquiv psi) (weightEquiv w)

namespace Definition35ForwardTransport

variable {P : Definition35Problem.{u}}
variable {Paut : Definition35AutomorphismStabilizerAdapter P}
variable {Psource : FLZSourceSemantics P Paut}
variable {Q : Definition35Problem.{v}}
variable {Qaut : Definition35AutomorphismStabilizerAdapter Q}
variable {Qsource : FLZSourceSemantics Q Qaut}

/-- Transport a fixed Definition 3.5 iBAW witness along fixed carrier maps.
Only forward preservation of the source relation is needed. -/
def map
    (T : Definition35ForwardTransport P Paut Psource Q Qaut Qsource)
    (witness : Definition35IBAWBijection P Paut Psource) :
    Definition35IBAWBijection Q Qaut Qsource where
  omega := T.brauerEquiv.symm.trans (witness.omega.trans T.weightEquiv)
  equivariant := by
    letI : MulAction P.Gamma (Definition35Brauer P) :=
      definition35BrauerAction P
    letI : MulAction P.Gamma (Definition35Weight P) :=
      definition35WeightAction P
    letI : MulAction Q.Gamma (Definition35Brauer Q) :=
      definition35BrauerAction Q
    letI : MulAction Q.Gamma (Definition35Weight Q) :=
      definition35WeightAction Q
    intro g psi
    have hbrauer :
        T.brauerEquiv.symm (g • psi) =
          T.gammaEquiv.symm g • T.brauerEquiv.symm psi := by
      apply T.brauerEquiv.injective
      calc
        T.brauerEquiv (T.brauerEquiv.symm (g • psi)) = g • psi :=
          T.brauerEquiv.apply_symm_apply _
        _ = T.gammaEquiv (T.gammaEquiv.symm g) •
              T.brauerEquiv (T.brauerEquiv.symm psi) := by
            rw [T.gammaEquiv.apply_symm_apply,
              T.brauerEquiv.apply_symm_apply]
        _ = T.brauerEquiv
              (T.gammaEquiv.symm g • T.brauerEquiv.symm psi) :=
            (T.brauer_naturality _ _).symm
    have hwitness :
        witness.omega
            (T.gammaEquiv.symm g • T.brauerEquiv.symm psi) =
          T.gammaEquiv.symm g • witness.omega (T.brauerEquiv.symm psi) := by
      exact witness.equivariant _ _
    calc
      (T.brauerEquiv.symm.trans (witness.omega.trans T.weightEquiv))
          (g • psi) =
          T.weightEquiv (witness.omega (T.brauerEquiv.symm (g • psi))) := rfl
      _ = T.weightEquiv
            (witness.omega
              (T.gammaEquiv.symm g • T.brauerEquiv.symm psi)) := by
            rw [hbrauer]
      _ = T.weightEquiv
            (T.gammaEquiv.symm g • witness.omega (T.brauerEquiv.symm psi)) := by
            rw [hwitness]
      _ = T.gammaEquiv (T.gammaEquiv.symm g) •
            T.weightEquiv (witness.omega (T.brauerEquiv.symm psi)) :=
            T.weight_naturality _ _
      _ = g • T.weightEquiv (witness.omega (T.brauerEquiv.symm psi)) := by
            rw [T.gammaEquiv.apply_symm_apply]
      _ = g •
            (T.brauerEquiv.symm.trans (witness.omega.trans T.weightEquiv)) psi := rfl
  blockIsomorphism := by
    intro psi
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
      T.relation_forward (T.brauerEquiv.symm psi)
        (witness.omega (T.brauerEquiv.symm psi))
        (witness.blockIsomorphism (T.brauerEquiv.symm psi))

end Definition35ForwardTransport

end ModularRep.PaperProofs.EvenFieldFLZDefinition35Transport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
