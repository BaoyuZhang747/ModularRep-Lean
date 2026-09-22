import ModularRep.BrauerCharacterCommonRootCompatibility
import ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
import ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent

/-!
# Joint own reductions from the fixed Sp root convention

The only E1 data identify the existing downstairs ambient root and EVERY
exact selected quotient root with restrictions of `D.iota.toMulEquiv`.
All exponents, normalizer roots, representation inflations, and own local
character equations are then constructed in K. The downstairs character is
transported through the actual selected normalizer-quotient equivalence.

No reduction-existence source, character choice, root-compatibility field,
automorphism-dependent convention, block conclusion, or relation is added.
The common exponent only bounds the actual Sp/PSp subquotients; it makes no
claim about unrelated field-extension inertia groups.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoCommonRootSelectedPairReductions

open ModularRep.CharacterWeight
open ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier

universe u

section CommonRootFacts

variable {p m : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [Group G] [Finite G] [Group H] [Finite H]

/-- Divisibility of group orders supplies the exact prime regular exponent
bound used by the finite common root group. -/
theorem exponent_dvd_of_card_dvd (h : Nat.card H ∣ Nat.card G) :
    primeRegularExponent p H ∣ primeRegularExponent p G := by
  simpa only [primeRegularExponent] using Nat.ordCompl_dvd_ordCompl_of_dvd h p

/-- Root records with the same literal root-group equivalence are equal. -/
theorem root_eq_of_table_eq (i j : PrimeRegularRootEmbedding p k K G)
    (h : i.toMulEquiv = j.toMulEquiv) : i = j := by
  cases i
  cases j
  cases h
  rfl

/-- Restricting the ambient table to its own exponent changes nothing. -/
theorem ofCommonRoot_self (i : PrimeRegularRootEmbedding p k K G) :
    PrimeRegularRootEmbedding.ofCommonRoot i.prime i.toMulEquiv
      (dvd_refl (primeRegularExponent p G)) = i := by
  apply root_eq_of_table_eq
  apply MulEquiv.ext
  intro z
  apply Subtype.ext
  rfl

variable [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Compatibility along an actual homomorphism is K for restrictions of one
fixed finite root equivalence. No compatibility square is a source field. -/
theorem commonRoot_compatible (hp : p.Prime)
    (e : rootsOfUnity m k ≃* rootsOfUnity m K)
    (hG : primeRegularExponent p G ∣ m) (hH : primeRegularExponent p H ∣ m)
    (f : H →* G) :
    RootCompatibleAlong (PrimeRegularRootEmbedding.ofCommonRoot hp e hG)
      (PrimeRegularRootEmbedding.ofCommonRoot hp e hH) f := by
  intro V
  exact Representation.brauerRootLiftCompatibleAlong_of_commonRoot V.ρ f hp e hG hH

end CommonRootFacts

section LiteralSelectedPair

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]

local instance commonRootSpFintype : Fintype (LiteralSp n F) := Fintype.ofFinite _
local instance commonRootPSpFintype : Fintype (LiteralPSp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)
variable (cover : OddSymplecticFullCoverSource n F)
variable (iotaDown : PrimeRegularRootEmbedding 2 k K (LiteralPSp n F))

/-- The common exponent is exactly the prime-to-two part of the actual Sp
order, not a new unspecified bound. -/
abbrev commonExponent := primeRegularExponent 2 (LiteralSp n F)

include cover in
theorem projective_exponent_dvd :
    primeRegularExponent 2 (LiteralPSp n F) ∣ commonExponent (n := n) (F := F) :=
  exponent_dvd_of_card_dvd
    (Subgroup.card_dvd_of_surjective (literalProjection n F) cover.fullCover.1.1)

theorem upNormalizer_exponent_dvd (w : D.PrincipalWeight) :
    primeRegularExponent 2
      (Subgroup.normalizer ((weightRepresentative D w).subgroup : Set (LiteralSp n F))) ∣
        commonExponent (n := n) (F := F) :=
  exponent_dvd_of_card_dvd (Subgroup.card_subgroup_dvd_card _)

theorem upQuotient_exponent_dvd (w : D.PrincipalWeight) :
    primeRegularExponent 2 (NormalizerQuotient (weightRepresentative D w).subgroup) ∣
      commonExponent (n := n) (F := F) := by
  apply dvd_trans (exponent_dvd_of_card_dvd
    (((weightRepresentative D w).subgroup.subgroupOf
      (Subgroup.normalizer ((weightRepresentative D w).subgroup :
        Set (LiteralSp n F)))).card_quotient_dvd_card))
  exact upNormalizer_exponent_dvd D w

theorem downNormalizer_exponent_dvd (w : D.PrincipalWeight) :
    primeRegularExponent 2
      (Subgroup.normalizer ((spQuotientPair cover (weightRepresentative D w)).subgroup :
        Set (LiteralPSp n F))) ∣ commonExponent (n := n) (F := F) :=
  (exponent_dvd_of_card_dvd (Subgroup.card_subgroup_dvd_card _)).trans
    (projective_exponent_dvd cover)

theorem downQuotient_exponent_dvd (w : D.PrincipalWeight) :
    primeRegularExponent 2
      (NormalizerQuotient (spQuotientPair cover (weightRepresentative D w)).subgroup) ∣
        commonExponent (n := n) (F := F) := by
  apply dvd_trans (exponent_dvd_of_card_dvd
    (((spQuotientPair cover (weightRepresentative D w)).subgroup.subgroupOf
      (Subgroup.normalizer ((spQuotientPair cover (weightRepresentative D w)).subgroup :
        Set (LiteralPSp n F)))).card_quotient_dvd_card))
  exact downNormalizer_exponent_dvd D cover w

/-- The same finite root table is restricted to any actual bounded group. -/
def rootAt (H : Type u) [Group H] [Finite H]
    (h : primeRegularExponent 2 H ∣ commonExponent (n := n) (F := F)) :
    PrimeRegularRootEmbedding 2 k K H :=
  PrimeRegularRootEmbedding.ofCommonRoot D.iota.prime D.iota.toMulEquiv h

theorem ambient_rootAt : rootAt D (LiteralSp n F) (dvd_refl _) = D.iota :=
  ofCommonRoot_self D.iota

/-- Exact E1 convention bindings. They assert no compatibility, reduction,
character equality, block support, or source relation. Both tables are
identified with restrictions of the SAME already fixed ambient table. -/
structure CommonRootConvention : Prop where
  downRoot_eq : iotaDown = rootAt D (LiteralPSp n F) (projective_exponent_dvd cover)
  selectedRoot_eq : ∀ w : D.PrincipalWeight,
    (selectedQuotientReduction D reduction w).iota =
      rootAt D (NormalizerQuotient (weightRepresentative D w).subgroup)
        (upQuotient_exponent_dvd D w)

variable (C : CommonRootConvention D reduction cover iotaDown)

def upNormalizerRoot (w : D.PrincipalWeight) :=
  rootAt D
    (Subgroup.normalizer ((weightRepresentative D w).subgroup : Set (LiteralSp n F)))
    (upNormalizer_exponent_dvd D w)

def downNormalizerRoot (w : D.PrincipalWeight) :=
  rootAt D
    (Subgroup.normalizer ((spQuotientPair cover (weightRepresentative D w)).subgroup :
      Set (LiteralPSp n F))) (downNormalizer_exponent_dvd D cover w)

def downQuotientRoot (w : D.PrincipalWeight) :=
  rootAt D
    (NormalizerQuotient (spQuotientPair cover (weightRepresentative D w)).subgroup)
    (downQuotient_exponent_dvd D cover w)

/-- This root is fixed by w alone, independently of any automorphism or
inner conjugator. All its required compatibility is proved in K. -/
def selectedNormalizerRoots (w : D.PrincipalWeight) :
    SelectedNormalizerRoots D reduction w where
  root := upNormalizerRoot D w
  quotientCompatible := by
    rw [C.selectedRoot_eq w]
    exact commonRoot_compatible D.iota.prime D.iota.toMulEquiv
      (upQuotient_exponent_dvd D w) (upNormalizer_exponent_dvd D w)
      (normalizerProjection (weightRepresentative D w).subgroup)
  ambientCompatible := by
    rw [← ambient_rootAt D]
    exact commonRoot_compatible D.iota.prime D.iota.toMulEquiv
      (dvd_refl _) (upNormalizer_exponent_dvd D w)
      (Subgroup.normalizer ((weightRepresentative D w).subgroup : Set (LiteralSp n F))).subtype

/-- The actual quotient isomorphism, retaining the original own pair. -/
def localQuotientEquiv (w : D.PrincipalWeight) :
    NormalizerQuotient (weightRepresentative D w).subgroup ≃*
      NormalizerQuotient (spQuotientPair cover (weightRepresentative D w)).subgroup :=
  selectedLocalQuotientEquiv (literalProjection n F) cover.fullCover.1.1
    cover.projection_twoKernel (weightRepresentative D w)

theorem localQuotientEquiv_mk (w : D.PrincipalWeight)
    (x : Subgroup.normalizer ((weightRepresentative D w).subgroup : Set (LiteralSp n F))) :
    localQuotientEquiv D cover w
        (normalizerProjection (weightRepresentative D w).subgroup x) =
      normalizerProjection (spQuotientPair cover (weightRepresentative D w)).subgroup
        (normalizerMap (literalProjection n F) (weightRepresentative D w).subgroup x) := rfl

theorem localCharacter_inverse (w : D.PrincipalWeight)
    (z : NormalizerQuotient (spQuotientPair cover (weightRepresentative D w)).subgroup) :
    (spQuotientPair cover (weightRepresentative D w)).localCharacter z =
      (weightRepresentative D w).localCharacter ((localQuotientEquiv D cover w).symm z) := by
  have h := quotientPair_localCharacter (literalProjection n F) cover.fullCover.1.1
    cover.projection_twoKernel (weightRepresentative D w) ((localQuotientEquiv D cover w).symm z)
  change (spQuotientPair cover (weightRepresentative D w)).localCharacter
      (localQuotientEquiv D cover w ((localQuotientEquiv D cover w).symm z)) = _ at h
  simpa only [MulEquiv.apply_symm_apply] using h

/-- The exact selected quotient IBr is pulled through the inverse of the
actual quotient equivalence. Its affording representation is transported by
the existing surjective-pullback construction. -/
def downQuotientBrauer (w : D.PrincipalWeight) : IBr (downQuotientRoot D cover w) :=
  (inflateToKernelTrivialIBrAlong (localQuotientEquiv D cover w).symm.toMonoidHom
    (localQuotientEquiv D cover w).symm.surjective (downQuotientRoot D cover w)
    (selectedQuotientReduction D reduction w).iota (by
      rw [C.selectedRoot_eq w]
      exact commonRoot_compatible D.iota.prime D.iota.toMulEquiv
        (upQuotient_exponent_dvd D w) (downQuotient_exponent_dvd D cover w)
        (localQuotientEquiv D cover w).symm.toMonoidHom)
    (selectedQuotientReduction D reduction w).brauer).1

theorem downQuotientBrauer_values (w : D.PrincipalWeight)
    (x : PrimeRegularElement (G := NormalizerQuotient
      (spQuotientPair cover (weightRepresentative D w)).subgroup) 2) :
    (downQuotientBrauer D reduction cover iotaDown C w).1 x =
      (selectedQuotientReduction D reduction w).brauer.1
        (PrimeRegularElement.map (localQuotientEquiv D cover w).symm.toMonoidHom x) := rfl

/-- Inflation to the OWN downstairs normalizer; its kernel is the selected
radical subgroup, with no prime-to-two assumption. -/
def downNormalizerBrauer (w : D.PrincipalWeight) : IBr (downNormalizerRoot D cover w) :=
  (inflateToKernelTrivialIBrAlong
    (normalizerProjection (spQuotientPair cover (weightRepresentative D w)).subgroup)
    (normalizerProjection_surjective _)
    (downNormalizerRoot D cover w) (downQuotientRoot D cover w)
    (commonRoot_compatible D.iota.prime D.iota.toMulEquiv
      (downQuotient_exponent_dvd D cover w) (downNormalizer_exponent_dvd D cover w)
      (normalizerProjection (spQuotientPair cover (weightRepresentative D w)).subgroup))
    (downQuotientBrauer D reduction cover iotaDown C w)).1

/-- The downstairs IBr reduces the actual quotient pair's OWN ordinary
character; the only ordinary reduction used is the exact selected one. -/
theorem downNormalizerBrauer_ownReduction (w : D.PrincipalWeight) :
    NormalizerInflatedReduction
      (spQuotientPair cover (weightRepresentative D w)).subgroup
      (spQuotientPair cover (weightRepresentative D w)).localCharacter
      (downNormalizerRoot D cover w)
      (downNormalizerBrauer D reduction cover iotaDown C w) := by
  intro x
  let y := PrimeRegularElement.map
    (normalizerProjection (spQuotientPair cover (weightRepresentative D w)).subgroup) x
  let z := PrimeRegularElement.map (localQuotientEquiv D cover w).symm.toMonoidHom y
  calc
    (spQuotientPair cover (weightRepresentative D w)).localCharacter
        (normalizerProjection (spQuotientPair cover (weightRepresentative D w)).subgroup x.1) =
      (weightRepresentative D w).localCharacter z.1 := localCharacter_inverse D cover w y.1
    _ = (selectedQuotientReduction D reduction w).brauer.1 z :=
      (selectedQuotientReduction D reduction w).reduction z
    _ = (downNormalizerBrauer D reduction cover iotaDown C w).1 x := rfl

/-- The existing central-descent packet is COMPUTED; every local character
and compatibility field comes from the fixed convention and the own pair. -/
def compatiblePairReductions (w : D.PrincipalWeight) :
    CompatiblePairReductions cover D.iota iotaDown (weightRepresentative D w) where
  upRoot := upNormalizerRoot D w
  downRoot := downNormalizerRoot D cover w
  upCompatible := (selectedNormalizerRoots D reduction cover iotaDown C w).ambientCompatible
  downCompatible := by
    rw [C.downRoot_eq]
    exact commonRoot_compatible D.iota.prime D.iota.toMulEquiv
      (projective_exponent_dvd cover) (downNormalizer_exponent_dvd D cover w)
      (Subgroup.normalizer ((spQuotientPair cover (weightRepresentative D w)).subgroup :
        Set (LiteralPSp n F))).subtype
  quotientCompatible := commonRoot_compatible D.iota.prime D.iota.toMulEquiv
    (downNormalizer_exponent_dvd D cover w) (upNormalizer_exponent_dvd D w)
    (normalizerMap (literalProjection n F) (weightRepresentative D w).subgroup)
  upBrauer := (ownReduction D reduction w
    (selectedNormalizerRoots D reduction cover iotaDown C w)).brauer
  downBrauer := downNormalizerBrauer D reduction cover iotaDown C w
  upReduction := (ownReduction D reduction w
    (selectedNormalizerRoots D reduction cover iotaDown C w)).own_reduction
  downReduction := downNormalizerBrauer_ownReduction D reduction cover iotaDown C w

/-- The exact selected quotient reduction is compatible with the SAME
upstairs root stored in the computed central descent packet. -/
theorem selectedCompatible (w : D.PrincipalWeight) :
    RootCompatibleAlong (selectedQuotientReduction D reduction w).iota
      (compatiblePairReductions D reduction cover iotaDown C w).upRoot
      (normalizerProjection (weightRepresentative D w).subgroup) :=
  (selectedNormalizerRoots D reduction cover iotaDown C w).quotientCompatible

/-- These roots are fixed for every principal weight. Horizontal
compatibility along any actual normalizer map is therefore K as well. -/
theorem upNormalizerRoots_compatible (w v : D.PrincipalWeight)
    (f : Subgroup.normalizer ((weightRepresentative D w).subgroup : Set (LiteralSp n F)) →*
      Subgroup.normalizer ((weightRepresentative D v).subgroup : Set (LiteralSp n F))) :
    RootCompatibleAlong (upNormalizerRoot D v) (upNormalizerRoot D w) f :=
  commonRoot_compatible D.iota.prime D.iota.toMulEquiv
    (upNormalizer_exponent_dvd D v) (upNormalizer_exponent_dvd D w) f

end LiteralSelectedPair

end ModularRep.PaperProofs.OddTwoCommonRootSelectedPairReductions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
