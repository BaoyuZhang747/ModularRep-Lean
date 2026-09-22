import ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
import ModularRep.PaperProofs.OddTwoActualSemidirectQuotient

/-!
# Definition 3.5 interpreted on the actual principal tuples

The only source field equates two interpretations of the SAME standard
modular block-triple relation. It is universal in both matched objects and
every admissible common-root packet; it asserts neither relation. The
global and full local group equivalences are the existing computed maps,
with their literal ambient coordinates. The same-FM consumer proves its
containment prerequisite using the checked stabilizer join.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoDefinition35TupleBinding

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction

universe u

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)

/-- The action in the exact Definition 3.5 problem is the full actual
automorphism action. The inverse/opposite convention is in its action
construction and the already computed stabilizer adapter. -/
theorem problem_gamma :
    (D.problem reduction).gamma = MonoidHom.id (MulAut (Sp n F)) := rfl

theorem automorphisms_equiv_coe (a : MulAut (Sp n F)) :
    ((D.automorphisms reduction).equiv a).1 =
      MulOpposite.op a⁻¹ := rfl

/-- The literal source global group Sp semidirect Aut(Sp)_psi maps to the
tuple's actual stabilizer by the already checked coordinate-preserving map. -/
def selectedGlobalEquiv (psi : D.PrincipalBrauer) (w : D.PrincipalWeight)
    (roots : SelectedNormalizerRoots D reduction w) :
    OddTwoActualSemidirectQuotient.BrauerSemidirect D.iota psi.1 ≃*
      (selectedArguments D reduction w roots psi).G :=
  OddTwoActualSemidirectQuotient.brauerSemidirectEquiv D.iota psi.1

@[simp] theorem selectedGlobalEquiv_left (psi : D.PrincipalBrauer)
    (w : D.PrincipalWeight) (roots : SelectedNormalizerRoots D reduction w)
    (d : OddTwoActualSemidirectQuotient.BrauerSemidirect D.iota psi.1) :
    (selectedGlobalEquiv D reduction psi w roots d).1.left = d.left := rfl

@[simp] theorem selectedGlobalEquiv_right (psi : D.PrincipalBrauer)
    (w : D.PrincipalWeight) (roots : SelectedNormalizerRoots D reduction w)
    (d : OddTwoActualSemidirectQuotient.BrauerSemidirect D.iota psi.1) :
    (selectedGlobalEquiv D reduction psi w roots d).1.right = d.right.1 := rfl

/-- Actual containment identifies the FULL own raw stabilizer with the
local subgroup of the tuple. There is no free local group equivalence. -/
def selectedFullLocalEquiv (psi : D.PrincipalBrauer) (w : D.PrincipalWeight)
    (roots : SelectedNormalizerRoots D reduction w)
    (contained : rawStabilizer (MonoidHom.id (MulAut (Sp n F)))
      (weightRepresentative D w) ≤
      globalStabilizer D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1) :
    rawStabilizer (MonoidHom.id (MulAut (Sp n F))) (weightRepresentative D w) ≃*
      (selectedArguments D reduction w roots psi).H :=
  fullRawStabilizerEquiv D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1
    (weightRepresentative D w) contained

@[simp] theorem selectedFullLocalEquiv_ambient (psi : D.PrincipalBrauer)
    (w : D.PrincipalWeight) (roots : SelectedNormalizerRoots D reduction w)
    (contained : rawStabilizer (MonoidHom.id (MulAut (Sp n F)))
      (weightRepresentative D w) ≤
      globalStabilizer D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1)
    (g : rawStabilizer (MonoidHom.id (MulAut (Sp n F))) (weightRepresentative D w)) :
    (selectedFullLocalEquiv D reduction psi w roots contained g).1.1 = g.1 := rfl

/-- E1/U definition interpretation only. FLZ Definition 3.5(ii), printed
p.10, and S must both mean the SAME standard modular block-triple relation.
The field is not an assertion for arbitrary unrelated interpretations.

The global group is identified by selectedGlobalEquiv; the full local
group by selectedFullLocalEquiv under the displayed containment. Both base
characters are the checked alongMulEquiv transports, and the own normalizer
character is COMPUTED from P.localReduction with both common-root squares.
Every admissible root packet is quantified, not a favourable packet chosen
to make a relation true. No FM map or relation truth is a source field. -/
structure Definition35TupleInterpretation
    (flz : FLZSourceSemantics (D.problem reduction) (D.automorphisms reduction))
    (standard : BlockTripleSourceSemantics 2 k K) : Prop where
  relation_iff : ∀ (psi : D.PrincipalBrauer) (w : D.PrincipalWeight)
    (roots : SelectedNormalizerRoots D reduction w),
    rawStabilizer (MonoidHom.id (MulAut (Sp n F))) (weightRepresentative D w) ≤
      globalStabilizer D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1 →
      (flz.definition35BlockIsomorphic psi w ↔
        standard.blockIsomorphic (selectedArguments D reduction w roots psi))

/-- The same FM image satisfies the group prerequisite in K. This result
only identifies the two relation expressions; it proves neither of them. -/
theorem sameFengMalle_relation_iff
    (flz : FLZSourceSemantics (D.problem reduction) (D.automorphisms reduction))
    (standard : BlockTripleSourceSemantics 2 k K)
    (interpretation : Definition35TupleInterpretation D reduction flz standard)
    (FM : D.FengMalleTheorem62LiteralCertificate) (psi : D.PrincipalBrauer)
    (roots : SelectedNormalizerRoots D reduction (FM.omega psi)) :
    flz.definition35BlockIsomorphic psi (D.definition35Equiv reduction FM psi) ↔
      standard.blockIsomorphic
        (OddTwoDefinition35OwnReduction.principalArguments D reduction FM psi roots) :=
  interpretation.relation_iff psi (FM.omega psi) roots
    (OddTwoPrincipalTripleStabilizerJoin.rawStabilizer_le_globalStabilizer D FM
      (MonoidHom.id (MulAut (Sp n F))) psi)

end ModularRep.PaperProofs.OddTwoDefinition35TupleBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
