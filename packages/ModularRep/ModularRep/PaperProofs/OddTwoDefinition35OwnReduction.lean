import ModularRep.PaperProofs.OddTwoPrincipalTripleStabilizerJoin
import ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
import ModularRep.IrreducibleBrauerCharacterSurjectiveDescent

/-!
# The selected Definition 3.5 quotient reduction on its own normalizer

The quotient Brauer character is exactly P.localReduction of the selected
weight. Its normalizer character is computed by representation inflation
along the actual normalizer quotient projection. The root packet keeps both
quotient-to-normalizer and ambient-to-normalizer compatibility. No normalizer
character, inflation equation, block conclusion or triple relation is an
extra source field.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoDefinition35OwnReduction

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

universe u

/-- The actual quotient by Q inside its own normalizer. -/
def normalizerProjection {G : Type u} [Group G] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) →* NormalizerQuotient Q :=
  QuotientGroup.mk' (Q.subgroupOf (Subgroup.normalizer (Q : Set G)))

theorem normalizerProjection_surjective {G : Type u} [Group G] (Q : Subgroup G) :
    Function.Surjective (normalizerProjection Q) :=
  QuotientGroup.mk'_surjective _

section Principal

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))

/-- The same selected representative, for an arbitrary principal weight. -/
def weightRepresentative (w : D.PrincipalWeight) : CharacterWeight 2 K (Sp n F) :=
  selectedCharacterWeight D.blockSource D.principalBlock w

variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)

/-- Retain the exact local reduction stored by the actual Definition 3.5
problem, rather than selecting another quotient Brauer character. -/
def selectedQuotientReduction (w : D.PrincipalWeight) :
    SelectedLocalReductionSource D.blockSource D.principalBlock w :=
  (D.problem reduction).localReduction w

/-- Standard common-root data on the OWN quotient and normalizer.
Both maps are literal. The ambient square is retained for the actual
local-block and modular-triple interpretation, not inferred from values. -/
structure SelectedNormalizerRoots (w : D.PrincipalWeight) where
  root : PrimeRegularRootEmbedding 2 k K
    (Subgroup.normalizer ((weightRepresentative D w).subgroup : Set (Sp n F)))
  quotientCompatible : RootCompatibleAlong
    (selectedQuotientReduction D reduction w).iota root
    (normalizerProjection (weightRepresentative D w).subgroup)
  ambientCompatible : RootCompatibleAlong D.iota root
    (Subgroup.normalizer ((weightRepresentative D w).subgroup : Set (Sp n F))).subtype

variable (w : D.PrincipalWeight)
variable (roots : SelectedNormalizerRoots D reduction w)

/-- Actual representation inflation constructs the normalizer IBr. The
existing constructor requires surjectivity and compatible roots only;
no prime-to-two hypothesis is imposed on the quotient kernel. -/
def inflatedSelectedBrauer : IBr roots.root :=
  (inflateToKernelTrivialIBrAlong
    (normalizerProjection (weightRepresentative D w).subgroup)
    (normalizerProjection_surjective (weightRepresentative D w).subgroup)
    roots.root (selectedQuotientReduction D reduction w).iota
    roots.quotientCompatible (selectedQuotientReduction D reduction w).brauer).1

theorem inflatedSelectedBrauer_values
    (x : PrimeRegularElement (G := Subgroup.normalizer
      ((weightRepresentative D w).subgroup : Set (Sp n F))) 2) :
    (inflatedSelectedBrauer D reduction w roots).1 x =
      (selectedQuotientReduction D reduction w).brauer.1
        (PrimeRegularElement.map
          (normalizerProjection (weightRepresentative D w).subgroup) x) := rfl

/-- The exact selected quotient reduction gives the own ordinary inflation
identity for the COMPUTED normalizer Brauer character. -/
theorem inflatedSelectedBrauer_ownReduction :
    NormalizerInflatedReduction (weightRepresentative D w).subgroup
      (weightRepresentative D w).localCharacter roots.root
      (inflatedSelectedBrauer D reduction w roots) := by
  intro x
  exact (selectedQuotientReduction D reduction w).reduction
    (PrimeRegularElement.map
      (normalizerProjection (weightRepresentative D w).subgroup) x)

/-- The own normalizer reduction is now computed from P.localReduction. -/
def ownReduction : OwnNormalizerReduction (k := k) (weightRepresentative D w) where
  root := roots.root
  brauer := inflatedSelectedBrauer D reduction w roots
  own_reduction := inflatedSelectedBrauer_ownReduction D reduction w roots

theorem ownReduction_ambientCompatible :
    RootCompatibleAlong D.iota (ownReduction D reduction w roots).root
      (Subgroup.normalizer ((weightRepresentative D w).subgroup : Set (Sp n F))).subtype :=
  roots.ambientCompatible

theorem ownReduction_quotientCompatible :
    RootCompatibleAlong (selectedQuotientReduction D reduction w).iota
      (ownReduction D reduction w roots).root
      (normalizerProjection (weightRepresentative D w).subgroup) :=
  roots.quotientCompatible

/-- Universal actual tuple, independent of any chosen FM map. The local
subgroup is initially the actual intersection; full raw containment is a
separate K fact when w is the same matched image. -/
def selectedArguments (psi : D.PrincipalBrauer) : BlockTripleArguments 2 k K :=
  arguments D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1
    (weightRepresentative D w) (ownReduction D reduction w roots)

theorem selectedArguments_phi_own_values (psi : D.PrincipalBrauer)
    (x : PrimeRegularElement (G := ↥(baseSubgroup D.iota
      (MonoidHom.id (MulAut (Sp n F))) psi.1 ⊓
      localSubgroup D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1
        (weightRepresentative D w))) 2) :
    (selectedArguments D reduction w roots psi).phi.1 x =
      (weightRepresentative D w).localCharacter (QuotientGroup.mk
        ((normalizerEquivIntersection D.iota
          (MonoidHom.id (MulAut (Sp n F))) psi.1
          (weightRepresentative D w)).symm x.1)) :=
  arguments_phi_own_values D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1
    (weightRepresentative D w) (ownReduction D reduction w roots) x

end Principal

section SameFengMalleImage

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance spFintype' : Fintype (Sp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)
variable (FM : D.FengMalleTheorem62LiteralCertificate)
variable (psi : D.PrincipalBrauer)
variable (roots : SelectedNormalizerRoots D reduction (FM.omega psi))

/-- The tuple on the SAME FM image uses the computed normalizer reduction. -/
def principalArguments : BlockTripleArguments 2 k K :=
  selectedArguments D reduction (FM.omega psi) roots psi

theorem principalArguments_eq_checkedTuple :
    principalArguments D reduction FM psi roots =
      ModularRep.PaperProofs.OddTwoPrincipalTripleStabilizerJoin.principalArguments
        D FM psi (ownReduction D reduction (FM.omega psi) roots) := rfl

/-- The quotient IBr fed to inflation is literally the reduction of the
exact Definition 3.5 value, not merely an equal or isomorphic weight. -/
theorem selectedQuotientReduction_sameDefinition35 :
    selectedQuotientReduction D reduction (FM.omega psi) =
      (D.problem reduction).localReduction (D.definition35Equiv reduction FM psi) := rfl

theorem principalArguments_phi_own_values
    (x : PrimeRegularElement (G := ↥(baseSubgroup D.iota
      (MonoidHom.id (MulAut (Sp n F))) psi.1 ⊓
      localSubgroup D.iota (MonoidHom.id (MulAut (Sp n F))) psi.1
        (weightRepresentative D (FM.omega psi)))) 2) :
    (principalArguments D reduction FM psi roots).phi.1 x =
      (weightRepresentative D (FM.omega psi)).localCharacter (QuotientGroup.mk
        ((normalizerEquivIntersection D.iota
          (MonoidHom.id (MulAut (Sp n F))) psi.1
          (weightRepresentative D (FM.omega psi))).symm x.1)) :=
  selectedArguments_phi_own_values D reduction (FM.omega psi) roots psi x

end SameFengMalleImage

end ModularRep.PaperProofs.OddTwoDefinition35OwnReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
