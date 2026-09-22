import ModularRep.PaperProofs.OddTwoActualStabilizerTriple
import ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier

/-!
# The own principal representative in the actual stabilizer triple

The raw representative is the existing selected pair of the SAME intrinsic
Feng--Malle image. Its actual semidirect stabilizer is contained in the
actual Brauer stabilizer: passage to the ambient weight class is equivariant,
inner actions fix classes, and the same FM map is equivariant and injective.
No representative-equivariance, stabilizer equality, or triple relation is
assumed. The full-Aut specialization supplies the actual Definition 3.5
group tuple, with a reduction of this own character on its own normalizer.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalTripleStabilizerJoin

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.CyclicOuterRawPairNormalizer
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

universe u

section InnerActions

variable {p : ℕ} {k K H E : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E]

/-- The inner component acts trivially on the actual Brauer character. -/
theorem brauer_semidirect_smul_eq_right
    (iota : PrimeRegularRootEmbedding p k K H)
    (action : E →* MulAut H) (g : H ⋊[action] E) (psi : IBr iota) :
    let _ := actualBrauerAction iota action
    g • psi = inverseOpHom action g.right • psi := by
  dsimp only
  change MulOpposite.op (MulAut.conj g.left⁻¹) •
    (inverseOpHom action g.right • psi) = _
  exact inner_fixes_ibr iota g.left _

/-- The inner component acts trivially on the actual ambient weight class. -/
theorem weight_semidirect_smul_eq_right
    (action : E →* MulAut H) (g : H ⋊[action] E)
    (w : ConjugacyClass (p := p) (K := K) (G := H)) :
    let _ := canonicalWeightSemidirectAction (p := p) (K := K) action
    g • w = inverseOpHom action g.right • w := by
  dsimp only
  change MulOpposite.op (MulAut.conj g.left⁻¹) •
    (inverseOpHom action g.right • w) = _
  exact inner_fixes_weightClass g.left _

/-- Passage to the actual ambient quotient is equivariant for every
displayed acting group; no cyclicity hypothesis is needed. -/
theorem rawWeightOrbit_semidirect_smul_actual
    (action : E →* MulAut H) (g : H ⋊[action] E)
    (r : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ := canonicalRawSemidirectAction (p := p) (K := K) action
    let _ := canonicalWeightSemidirectAction (p := p) (K := K) action
    rawWeightOrbit (g • r) = g • rawWeightOrbit r := by
  dsimp only
  letI := canonicalRawSemidirectAction (p := p) (K := K) action
  letI := canonicalWeightSemidirectAction (p := p) (K := K) action
  refine Quotient.inductionOn r ?_
  intro W
  rfl

end InnerActions

section Principal

variable {n : ℕ} {F k K Block E : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group E] [Finite E]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _
local instance actingFintype : Fintype E := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))

local instance principalWeightAction : MulAction (MulAut (Sp n F)) D.PrincipalWeight :=
  D.principalWeightAction

local instance principalBrauerAction : MulAction (MulAut (Sp n F)) D.PrincipalBrauer :=
  D.principalBrauerAction

variable (FM : D.FengMalleTheorem62LiteralCertificate)

/-- The already chosen representative of this SAME FM image. -/
def selectedPair (psi : D.PrincipalBrauer) : CharacterWeight 2 K (Sp n F) := by
  letI : Fintype Block := D.blockSource.operations.ambientBlockData.fintypeBlock
  exact selectedCharacterWeight D.blockSource D.principalBlock (FM.omega psi)

theorem selectedPair_class (psi : D.PrincipalBrauer) :
    (Quotient.mk'' (Quotient.mk'' (selectedPair D FM psi)) :
      ConjugacyClass (p := 2) (K := K) (G := Sp n F)) = (FM.omega psi).1 := by
  letI : Fintype Block := D.blockSource.operations.ambientBlockData.fintypeBlock
  exact selectedCharacterWeight_spec D.blockSource D.principalBlock (FM.omega psi)

/-- Matching equivariance proves actual containment for the own raw pair.
The action may be any displayed subgroup of actual automorphisms; neither
cyclicity nor a new correspondence on that subgroup is required. -/
theorem rawStabilizer_le_globalStabilizer
    (action : E →* MulAut (Sp n F)) (psi : D.PrincipalBrauer) :
    rawStabilizer action (selectedPair D FM psi) ≤
      globalStabilizer D.iota action psi.1 := by
  letI := canonicalRawSemidirectAction (p := 2) (K := K) action
  letI := canonicalWeightSemidirectAction (p := 2) (K := K) action
  letI := actualBrauerAction D.iota action
  intro g hg
  let r : RawWeightClass (p := 2) (K := K) (H := Sp n F) :=
    Quotient.mk'' (selectedPair D FM psi)
  have hraw : g • r = r := hg
  have horbit : g • rawWeightOrbit r = rawWeightOrbit r :=
    (rawWeightOrbit_semidirect_smul_actual action g r).symm.trans
      (congrArg rawWeightOrbit hraw)
  have hselected : rawWeightOrbit r = (FM.omega psi).1 :=
    selectedPair_class D FM psi
  rw [hselected] at horbit
  have hweightVal : inverseOpHom action g.right • (FM.omega psi).1 =
      (FM.omega psi).1 :=
    (weight_semidirect_smul_eq_right action g (FM.omega psi).1).symm.trans horbit
  have hweight : action g.right • FM.omega psi = FM.omega psi := by
    apply Subtype.ext
    change MulOpposite.op (action g.right)⁻¹ • (FM.omega psi).1 = _
    change MulOpposite.op (action g.right⁻¹) • (FM.omega psi).1 =
      (FM.omega psi).1 at hweightVal
    simpa only [map_inv] using hweightVal
  have hpsi : action g.right • psi = psi :=
    FM.omega.injective ((FM.equivariant (action g.right) psi).trans hweight)
  change g • psi.1 = psi.1
  rw [brauer_semidirect_smul_eq_right]
  change MulOpposite.op (action g.right⁻¹) • psi.1 = psi.1
  have hpsiVal := congrArg (fun x : D.PrincipalBrauer => x.1) hpsi
  change MulOpposite.op (action g.right)⁻¹ • psi.1 = psi.1 at hpsiVal
  simpa only [map_inv] using hpsiVal

/-- The full raw stabilizer is now the literal local subgroup of the
actual tuple, using proved containment rather than a supplied equality. -/
def selectedFullRawStabilizerEquiv
    (action : E →* MulAut (Sp n F)) (psi : D.PrincipalBrauer) :
    rawStabilizer action (selectedPair D FM psi) ≃*
      localSubgroup D.iota action psi.1 (selectedPair D FM psi) :=
  fullRawStabilizerEquiv D.iota action psi.1 (selectedPair D FM psi)
    (rawStabilizer_le_globalStabilizer D FM action psi)

@[simp] theorem selectedFullRawStabilizerEquiv_ambient
    (action : E →* MulAut (Sp n F)) (psi : D.PrincipalBrauer)
    (g : rawStabilizer action (selectedPair D FM psi)) :
    (selectedFullRawStabilizerEquiv D FM action psi g).1.1 = g.1 := rfl

/-- The selected pair is definitionally the one used by the exact
Definition 3.5 map. No independent choice of FM images is introduced. -/
theorem selectedPair_definition35
    (reduction : ∀ w : D.PrincipalWeight,
      SelectedLocalReductionSource D.blockSource D.principalBlock w)
    (psi : D.PrincipalBrauer) :
    selectedPair D FM psi =
      selectedCharacterWeight (D.problem reduction).blockSource
        (D.problem reduction).block (D.definition35Equiv reduction FM psi) := rfl

/-- The literal full-Aut Definition 3.5 tuple for the same image and its
own normalizer reduction. Existing quotient reductions are not silently
used as normalizer reductions. This definition asserts no triple relation. -/
def principalArguments (psi : D.PrincipalBrauer)
    (R : OwnNormalizerReduction (k := k) (selectedPair D FM psi)) :
    BlockTripleArguments 2 k K :=
  arguments D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1
    (selectedPair D FM psi) R

theorem principalArguments_theta_values (psi : D.PrincipalBrauer)
    (R : OwnNormalizerReduction (k := k) (selectedPair D FM psi))
    (x : PrimeRegularElement (G := baseSubgroup D.iota
      (MonoidHom.id (MulAut (Sp n F))) psi.1) 2) :
    (principalArguments D FM psi R).theta.1 x =
      psi.1.1 (PrimeRegularElement.map (baseEquiv D.iota
        (MonoidHom.id (MulAut (Sp n F))) psi.1).symm.toMonoidHom x) := rfl

theorem principalArguments_phi_own_values (psi : D.PrincipalBrauer)
    (R : OwnNormalizerReduction (k := k) (selectedPair D FM psi))
    (x : PrimeRegularElement (G := ↥(baseSubgroup D.iota
      (MonoidHom.id (MulAut (Sp n F))) psi.1 ⊓
      localSubgroup D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1
        (selectedPair D FM psi))) 2) :
    (principalArguments D FM psi R).phi.1 x =
      (selectedPair D FM psi).localCharacter (QuotientGroup.mk
        ((normalizerEquivIntersection D.iota
          (MonoidHom.id (MulAut (Sp n F))) psi.1
          (selectedPair D FM psi)).symm x.1)) :=
  arguments_phi_own_values D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1
    (selectedPair D FM psi) R x

end Principal

end ModularRep.PaperProofs.OddTwoPrincipalTripleStabilizerJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
