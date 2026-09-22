import ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
import ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport

/-!
# Diagonal-orbit correction of the intrinsic principal correspondence

Brough--Spaeth, Lemma 4.6 (`CohomPairs2` in the source TeX), supplies its
block-triple relation for some conformal conjugate of the Brauer character.
The proof of Theorem 4.5 chooses that character before defining the final
correspondence.  It does not prove the relation for an arbitrary map already
chosen by Feng--Malle, Theorem 6.2.

This file proves the elementary correction when each relevant conformal
orbit consists of a character and its diagonal image.  If the original
pair satisfies the relation, retain it; otherwise interchange that diagonal
orbit.  Simultaneous covariance makes this decision invariant, so the
correction is an involution and commutes with the full automorphism action.
No finite-cardinality argument or additional assumed bijection is needed.

K: the correction, bijectivity, full equivariance, orbit retention, and the
Definition 3.5 constructor.  E1/U: the literal diagonal action is involutive
and commutes on Brauer characters with the full action.  E2/U: covariance
of the exact modular block-triple relation and the pointwise orbit witness.
The latter still requires the covering-character, covering-weight,
extension, and intermediate-block hypotheses in Brough--Spaeth Lemma 4.6,
and passage to the exact FLZ Definition 3.5 relation.  Neither FM Theorem
6.2 nor FM Corollary 4.6 alone provides it.  In particular, the distinction
between the prime-to-two cover and the full symplectic cover remains an
explicit source join; this file does not apply that lemma to the wrong cover.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalOrbitAdjustment

namespace InvolutiveCorrection

universe u v w

variable {A : Type u} {X : Type v} {Y : Type w}
variable [Group A] [MulAction A X] [MulAction A Y]
variable (diagonal : A) (f : X ≃ Y) (R : X → Y → Prop)

/-- Retain a good matched pair and otherwise move its source by the
diagonal action.  Invariance of this decision is proved below. -/
def correction (x : X) : X := by
  classical
  exact if R x (f x) then x else diagonal • x

variable
  (hf : ∀ (a : A) (x : X), f (a • x) = a • f x)
  (hR : ∀ (a : A) (x : X) (y : Y), R (a • x) (a • y) ↔ R x y)

include hf hR

theorem good_smul_iff (a : A) (x : X) :
    R (a • x) (f (a • x)) ↔ R x (f x) := by
  rw [hf]
  exact hR a x (f x)

theorem correction_involutive
    (hdiagonal : Function.Involutive (fun x : X => diagonal • x)) :
    Function.Involutive (correction diagonal f R) := by
  classical
  intro x
  by_cases hx : R x (f x)
  · simp [correction, hx]
  · have hdx : ¬ R (diagonal • x) (f (diagonal • x)) := by
      intro h
      exact hx ((good_smul_iff f R hf hR diagonal x).mp h)
    simpa [correction, hx, hdx] using hdiagonal x

theorem correction_equivariant
    (hcommute : ∀ (a : A) (x : X),
      diagonal • (a • x) = a • (diagonal • x))
    (a : A) (x : X) :
    correction diagonal f R (a • x) = a • correction diagonal f R x := by
  classical
  by_cases hx : R x (f x)
  · have hax := (good_smul_iff f R hf hR a x).mpr hx
    simp [correction, hx, hax]
  · have hax : ¬ R (a • x) (f (a • x)) := by
      intro h
      exact hx ((good_smul_iff f R hf hR a x).mp h)
    simpa [correction, hx, hax] using hcommute a x

omit hf hR in
theorem correction_same_diagonal_orbit (x : X) :
    correction diagonal f R x = x ∨
      correction diagonal f R x = diagonal • x := by
  classical
  by_cases hx : R x (f x)
  · exact Or.inl (by simp [correction, hx])
  · exact Or.inr (by simp [correction, hx])

/-- The repaired correspondence is the original equivalence after an
explicit involutive permutation of its source. -/
def refinedEquiv
    (hdiagonal : Function.Involutive (fun x : X => diagonal • x)) : X ≃ Y :=
  ({ toFun := correction diagonal f R
     invFun := correction diagonal f R
     left_inv := correction_involutive diagonal f R hf hR hdiagonal
     right_inv := correction_involutive diagonal f R hf hR hdiagonal } : X ≃ X).trans f

@[simp] theorem refinedEquiv_apply
    (hdiagonal : Function.Involutive (fun x : X => diagonal • x)) (x : X) :
    refinedEquiv diagonal f R hf hR hdiagonal x =
      f (correction diagonal f R x) := rfl

theorem refinedEquiv_equivariant
    (hdiagonal : Function.Involutive (fun x : X => diagonal • x))
    (hcommute : ∀ (a : A) (x : X),
      diagonal • (a • x) = a • (diagonal • x))
    (a : A) (x : X) :
    refinedEquiv diagonal f R hf hR hdiagonal (a • x) =
      a • refinedEquiv diagonal f R hf hR hdiagonal x := by
  rw [refinedEquiv_apply,
    correction_equivariant diagonal f R hf hR hcommute,
    hf, refinedEquiv_apply]

theorem refinedEquiv_same_diagonal_orbit
    (hdiagonal : Function.Involutive (fun x : X => diagonal • x)) (x : X) :
    refinedEquiv diagonal f R hf hR hdiagonal x = f x ∨
      refinedEquiv diagonal f R hf hR hdiagonal x = diagonal • f x := by
  rw [refinedEquiv_apply]
  rcases correction_same_diagonal_orbit diagonal f R x with h | h
  · exact Or.inl (congrArg f h)
  · exact Or.inr ((congrArg f h).trans (hf diagonal x))

/-- The source supplies a good pair somewhere in the original matched
diagonal orbit.  The conclusion concerns the newly constructed map. -/
theorem refinedEquiv_relation
    (hdiagonal : Function.Involutive (fun x : X => diagonal • x))
    (horbit : ∀ x : X, R x (f x) ∨ R (diagonal • x) (f x))
    (x : X) :
    R x (refinedEquiv diagonal f R hf hR hdiagonal x) := by
  classical
  rw [refinedEquiv_apply]
  by_cases hx : R x (f x)
  · simpa [correction, hx] using hx
  · have hdx : R (diagonal • x) (f x) := (horbit x).resolve_left hx
    have h := (hR diagonal (diagonal • x) (f x)).mpr hdx
    have hd : diagonal • (diagonal • x) = x := hdiagonal x
    rw [hd, ← hf diagonal x] at h
    simpa [correction, hx] using h

end InvolutiveCorrection

open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier.PrincipalCharacterData
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport

universe u v

section IntrinsicPrincipal

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)
variable (FM : D.FengMalleTheorem62LiteralCertificate)
variable (source : FLZSourceSemantics (D.problem reduction) (D.automorphisms reduction))

local instance : MulAction (D.problem reduction).Gamma
    (Definition35Brauer (D.problem reduction)) :=
  definition35BrauerAction (D.problem reduction)

local instance : MulAction (D.problem reduction).Gamma
    (Definition35Weight (D.problem reduction)) :=
  definition35WeightAction (D.problem reduction)

/-- The remaining narrow source joins for correcting the actual intrinsic
FM principal map.  The two alternatives in `orbitWitness` are the conclusion
needed after the Brough--Spaeth source argument and cover transport; they
are not claimed as a theorem of FM 6.2 alone.  This packet contains neither
a replacement equivalence nor a Definition 3.5 seed.  The covering-character
and covering-weight correspondence must be compatible with this particular
`FM.omega`; existence of an unrelated good pair does not supply the field. -/
structure PrincipalOrbitCorrectionInput where
  diagonal : (D.problem reduction).Gamma
  brauer_involutive : Function.Involutive
    (fun psi : Definition35Brauer (D.problem reduction) => diagonal • psi)
  diagonal_commutes : ∀ (a : (D.problem reduction).Gamma)
      (psi : Definition35Brauer (D.problem reduction)),
    diagonal • (a • psi) = a • (diagonal • psi)
  relation_covariant : ∀ (a : (D.problem reduction).Gamma)
      (psi : Definition35Brauer (D.problem reduction))
      (w : Definition35Weight (D.problem reduction)),
    source.definition35BlockIsomorphic (a • psi) (a • w) ↔
      source.definition35BlockIsomorphic psi w
  orbitWitness : ∀ psi : Definition35Brauer (D.problem reduction),
    source.definition35BlockIsomorphic psi (D.definition35Equiv reduction FM psi) ∨
      source.definition35BlockIsomorphic (diagonal • psi)
        (D.definition35Equiv reduction FM psi)

namespace PrincipalOrbitCorrectionInput

variable {D reduction FM source}
variable (C : PrincipalOrbitCorrectionInput D reduction FM source)

def refinedEquiv : Definition35Brauer (D.problem reduction) ≃
    Definition35Weight (D.problem reduction) :=
  InvolutiveCorrection.refinedEquiv C.diagonal
    (D.definition35Equiv reduction FM) source.definition35BlockIsomorphic
    (D.definition35Equiv_equivariant reduction FM)
    C.relation_covariant C.brauer_involutive

theorem refinedEquiv_equivariant :
    Definition35Equivariant (D.problem reduction) C.refinedEquiv :=
  InvolutiveCorrection.refinedEquiv_equivariant C.diagonal
    (D.definition35Equiv reduction FM) source.definition35BlockIsomorphic
    (D.definition35Equiv_equivariant reduction FM)
    C.relation_covariant C.brauer_involutive C.diagonal_commutes

theorem refinedEquiv_same_diagonal_orbit
    (psi : Definition35Brauer (D.problem reduction)) :
    C.refinedEquiv psi = D.definition35Equiv reduction FM psi ∨
      C.refinedEquiv psi =
        C.diagonal • D.definition35Equiv reduction FM psi :=
  InvolutiveCorrection.refinedEquiv_same_diagonal_orbit C.diagonal
    (D.definition35Equiv reduction FM) source.definition35BlockIsomorphic
    (D.definition35Equiv_equivariant reduction FM)
    C.relation_covariant C.brauer_involutive psi

theorem refinedEquiv_blockIsomorphism
    (psi : Definition35Brauer (D.problem reduction)) :
    source.definition35BlockIsomorphic psi (C.refinedEquiv psi) :=
  InvolutiveCorrection.refinedEquiv_relation C.diagonal
    (D.definition35Equiv reduction FM) source.definition35BlockIsomorphic
    (D.definition35Equiv_equivariant reduction FM)
    C.relation_covariant C.brauer_involutive C.orbitWitness psi

/-- Definition 3.5 on the actual principal carriers with the corrected map.
The local relation is derived from the orbit witness, not assumed for this
map or for the original FM map.  Authentication of the source joins in `C`
remains separate. -/
def definition35Seed :
    Definition35IBAWBijection (D.problem reduction) (D.automorphisms reduction) source where
  omega := C.refinedEquiv
  equivariant := C.refinedEquiv_equivariant
  blockIsomorphism := C.refinedEquiv_blockIsomorphism

@[simp] theorem definition35Seed_omega
    (psi : Definition35Brauer (D.problem reduction)) :
    C.definition35Seed.omega psi = C.refinedEquiv psi := rfl

variable {Q : Definition35Problem.{v}}
variable {Qaut : Definition35AutomorphismStabilizerAdapter Q}
variable {Qsource : FLZSourceSemantics Q Qaut}

/-- The actual Jordan carrier transport consumes the newly corrected seed.
Its source principal-carrier component is computed from `D` and the same
FM rank and odd-field hypotheses.  The group, coefficient field, Brauer,
selected local-weight, and action maps are those in `T`. -/
def transportedSeed
    (T : PrincipalSeedCarrierTransport
      (D.problem reduction) (D.automorphisms reduction) source
      Q Qaut Qsource n F) :
    Definition35IBAWBijection Q Qaut Qsource :=
  (IntrinsicPrincipalSeed.transportWithIntrinsicCarrier
    D reduction FM source T).transport.map C.definition35Seed

/-- The transported result uses the refined principal correspondence on
the inverse Brauer-carrier image, without assuming the local relation for
the original FM map a second time. -/
@[simp] theorem transportedSeed_omega_apply
    (T : PrincipalSeedCarrierTransport
      (D.problem reduction) (D.automorphisms reduction) source
      Q Qaut Qsource n F)
    (psi : Definition35Brauer Q) :
    (C.transportedSeed T).omega psi =
      T.transport.weightEquiv (C.refinedEquiv (T.transport.brauerEquiv.symm psi)) := rfl

end PrincipalOrbitCorrectionInput

end IntrinsicPrincipal

end ModularRep.PaperProofs.OddTwoPrincipalOrbitAdjustment


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
