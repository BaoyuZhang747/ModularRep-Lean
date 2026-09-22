import ModularRep.PaperProofs.TypeCOddTwoOriginalTrivialNormalization
import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# Global clauses for blocks constructed from the original odd-two map

These K construction lemmas identify the complete target's existential radical
fibres with the original radical-class parts. Each supplied block must
already have its omega identified with the original specified block map.
The lemmas construct no block witnesses and add no published source input.
They preserve the original local equivalences, whole-character transport,
central values and trivial-radical reduction. The separate SAME-extension
normalization must still be supplied by the actual matched construction.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalGlobalClauses

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete EvenFieldFLZSourceConditions
open EvenFieldFLZDefinition35Family OddTwoLiteralSpathTarget
open TypeCOddTwoOriginalBlockMatching TypeBFullBlockCondition

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable {P : Problem n F} (D : Definition41 P)
variable (W : ∀ b : P.Block, BlockWitness (family P) (familyCover P) b)
variable (hOmega : ∀ b : P.Block, (W b).relative.omega = blockEquiv D b)

include hOmega in
/-- Recombination uses the original global map, not an independent choice. -/
theorem globalWeight_eq (psi : IBr P.iota) :
    globalWeight (family := family P) (cover := familyCover P) W psi = D.map.equiv psi := by
  exact congrArg
    (fun omega : Definition35Brauer ((family P).problem (brauerBlock (family P) psi)) ≃
        Definition35Weight ((family P).problem (brauerBlock (family P) psi)) =>
      (omega (inOwnBlock (family P) psi)).1)
    (hOmega (brauerBlock (family P) psi))

include hOmega in
theorem naturality (a : (MulAut (X n F))ᵐᵒᵖ) (b : P.Block)
    (psi : Definition35Brauer ((family P).problem b)) :
    (W (a • b)).relative.omega ((family P).transportBrauer a psi) =
      (family P).transportWeight a ((W b).relative.omega psi) := by
  rw [hOmega, hOmega]
  exact blockEquiv_naturality D b psi a

include hOmega in
theorem global_bijective : Function.Bijective
    (globalWeight (family := family P) (cover := familyCover P) W) := by
  have h : globalWeight (family := family P) (cover := familyCover P) W =
      D.map.equiv := funext (globalWeight_eq D W hOmega)
  rw [h]
  exact D.map.equiv.bijective

include hOmega in
theorem global_equivariant (a : (MulAut (X n F))ᵐᵒᵖ) (psi : IBr P.iota) :
    globalWeight (family := family P) (cover := familyCover P) W (a • psi) =
      CharacterWeight.rightTwistConjugacyClass (p := 2)
        (K := (family P).K) (G := (family P).H)
        a.unop (globalWeight (family := family P) (cover := familyCover P) W psi) := by
  rw [globalWeight_eq D W hOmega, globalWeight_eq D W hOmega]
  exact D.map.equivariant a psi

/-- The complete target's existence fibre and the original radical-class
part are the same characters. Both directions are derived from the own map. -/
def fibrePartEquiv (Q : RadicalSubgroup (p := 2) (G := X n F)) :
    RadicalBrauerFibre (family := family P) (cover := familyCover P) W Q ≃ D.map.Part Q where
  toFun psi := ⟨psi.1, by
    obtain ⟨theta, htheta⟩ := psi.2
    have h := congrArg radicalClass
      (htheta.trans (globalWeight_eq D W hOmega psi.1)).symm
    exact h⟩
  invFun psi := ⟨psi.1, D.map.localMap Q psi,
    (IntrinsicGlobalToRepresentativeMaps.localMap_class
      P.iota D.map.equiv Nat.prime_two Q psi).trans
        (globalWeight_eq D W hOmega psi.1).symm⟩
  left_inv psi := Subtype.ext rfl
  right_inv psi := Subtype.ext rfl

@[simp] theorem fibrePartEquiv_value (Q : RadicalSubgroup (p := 2) (G := X n F))
    (psi : RadicalBrauerFibre (family := family P) (cover := familyCover P) W Q) :
    (fibrePartEquiv D W hOmega Q psi).1 = psi.1 := rfl

/-- The target uses the original local equivalence, through the proved
identity of its domain with the exact complete radical fibre. -/
def radicalEquiv (Q : RadicalSubgroup (p := 2) (G := X n F)) :
    RadicalBrauerFibre (family := family P) (cover := familyCover P) W Q ≃
      RadicalOrdinary (family := family P) Q :=
  (fibrePartEquiv D W hOmega Q).trans (D.map.localMap Q)

include hOmega in
theorem radical_matches (Q : RadicalSubgroup (p := 2) (G := X n F))
    (psi : RadicalBrauerFibre (family := family P) (cover := familyCover P) W Q) :
    radicalWeightClass (family := family P) Q (radicalEquiv D W hOmega Q psi) =
      globalWeight (family := family P) (cover := familyCover P) W psi.1 :=
  (IntrinsicGlobalToRepresentativeMaps.localMap_class P.iota D.map.equiv Nat.prime_two
    Q (fibrePartEquiv D W hOmega Q psi)).trans (globalWeight_eq D W hOmega psi.1).symm

include hOmega in
/-- Covariance identifies the transported own ordinary character, not just
the subgroup or the ambient conjugacy class. -/
theorem radical_transport (Q : RadicalSubgroup (p := 2) (G := X n F))
    (psi : RadicalBrauerFibre (family := family P) (cover := familyCover P) W Q)
    (alpha : MulAut (X n F)) (Q' : RadicalSubgroup (p := 2) (G := X n F))
    (psi' : RadicalBrauerFibre (family := family P) (cover := familyCover P) W Q')
    (hQ : Q'.1 = Q.1.comap alpha.toMonoidHom)
    (hpsi : (show IBr P.iota from psi'.1) =
      MulOpposite.op alpha • (show IBr P.iota from psi.1)) :
    CharacterWeight.Isomorphic
      ((radicalRawWeight (family := family P) Q
        (radicalEquiv D W hOmega Q psi)).rightTwist alpha)
      (radicalRawWeight (family := family P) Q'
        (radicalEquiv D W hOmega Q' psi')) := by
  have hQ' : Q' = RadicalSubgroup.rightTwist Q alpha := Subtype.ext hQ
  subst Q'
  have hp : fibrePartEquiv D W hOmega (RadicalSubgroup.rightTwist Q alpha) psi' =
      D.map.partTransport (MulOpposite.op alpha) Q (fibrePartEquiv D W hOmega Q psi) :=
    Subtype.ext hpsi
  refine ⟨rfl, ?_⟩
  change ((characterWeightAt Nat.prime_two Q
    (D.map.localMap Q (fibrePartEquiv D W hOmega Q psi))).rightTwist alpha).localCharacter =
      (D.map.localMap (RadicalSubgroup.rightTwist Q alpha)
        (fibrePartEquiv D W hOmega (RadicalSubgroup.rightTwist Q alpha) psi')).1
  rw [hp]
  exact (congrArg Subtype.val (D.map.localMap_covariance
    (MulOpposite.op alpha) Q (fibrePartEquiv D W hOmega Q psi))).symm

include hOmega in
/-- The original group has trivial centre, so the full central-value clause
holds on every actual central regular element. No central argument is omitted. -/
theorem central_values (Q : RadicalSubgroup (p := 2) (G := X n F))
    (psi : RadicalBrauerFibre (family := family P) (cover := familyCover P) W Q)
    (z : PrimeRegularElement (G := Subgroup.normalizer (Q.1 : Set (X n F))) 2)
    (hz : z.1.1 ∈ Subgroup.center (X n F)) :
    inflatedRadicalOrdinary (family := family P) Q (radicalEquiv D W hOmega Q psi) z.1 *
        psi.1.1 ⟨1, isPrimeRegular_one⟩ =
      inflatedRadicalOrdinary (family := family P) Q (radicalEquiv D W hOmega Q psi) 1 *
        (PrimeRegularClassFunction.pullback
          (Subgroup.normalizer (Q.1 : Set (X n F))).subtype psi.1.1) z := by
  have hzX : z.1.1 = 1 := by
    rw [P.center_eq_bot] at hz
    exact hz
  have hzN : z.1 = 1 := Subtype.ext hzX
  have hzR : z = ⟨1, isPrimeRegular_one⟩ := Subtype.ext hzN
  rw [hzR]
  rfl

include hOmega in
/-- The original normalization is retained at EVERY trivial radical fibre. -/
theorem trivial_reduction (Q : RadicalSubgroup (p := 2) (G := X n F))
    (psi : RadicalBrauerFibre (family := family P) (cover := familyCover P) W Q)
    (hQ : Q.1 = ⊥)
    (x : PrimeRegularElement (G := Subgroup.normalizer (Q.1 : Set (X n F))) 2) :
    inflatedRadicalOrdinary (family := family P) Q (radicalEquiv D W hOmega Q psi) x.1 =
      (PrimeRegularClassFunction.pullback
        (Subgroup.normalizer (Q.1 : Set (X n F))).subtype psi.1.1) x :=
  TypeCOddTwoOriginalTrivialNormalization.trivialPart_reduction
    D Q (fibrePartEquiv D W hOmega Q psi) hQ x

end ModularRep.PaperProofs.TypeCOddTwoOriginalGlobalClauses


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
