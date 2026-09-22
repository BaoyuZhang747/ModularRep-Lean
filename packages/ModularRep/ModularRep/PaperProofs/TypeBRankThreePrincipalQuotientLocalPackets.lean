import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerFibre
import ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
import ModularRep.PaperProofs.OddTwoWeightGroupEquiv

/-!
# Selected local packets on the actual principal reference quotient

The existing centreless constructors transport each original selected weight
and its own Brauer reduction to the fixed reference quotient. The raw packet
is the canonical image of that same weight. Its calibrated quotient root
and the constructed normalizer root belong to the original modular system.
Compatibility along the literal local quotient map constructs inflation.
No new source, ambient extension, block induction or weight fibre is assumed.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientLocalPackets

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBLocalReductionInstantiation
open TypeBFixedRootDefinitionFamily TypeBModularGroupRootBinding
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZCentrelessLocalPackets
open EvenFieldFLZ318FixedTheoremGate TypeBCliffordCarriers
open CyclicOuterLemma37LiteralLocalExtension
open TypeBRankThreePrincipalReferenceBinding

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (calibration : RootResidueCompatible Msys root)
  [HasEnoughRootsOfUnity K (Nat.card (G F))]
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (guard : GuardedBlockCompatibility root S.operations)
  (b : LiteralPrimitiveBlock k (G F))

/-- Calibration of the family's actual selected local reduction is derived. -/
theorem originalLocalRoot_residue
    (w : Definition35Weight
      (problem S SH literal literalH Msys root calibration navarro guard b)) :
    RootResidueCompatible Msys
      ((problem S SH literal literalH Msys root calibration navarro guard b).localReduction w).iota := by
  change RootResidueCompatible Msys (localRoot root (SelectedRadical S b w))
  exact localRoot_residue Msys root calibration (SelectedRadical S b w)

variable {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (hb : TypeBCentralKernelBlockSource.IsPrincipal b)

/-- This presentation of the actual quotient equivalence is literally pi. -/
def quotientMapEquiv : (G F) ≃*
    TypeBRankThreePrincipalQuotientBrauerFibre.quotientGroup
      S SH literal literalH Msys root calibration navarro guard b hb :=
  centerlessCentralCharacterQuotientMapEquiv
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (centreless parameters N C centreSpin fullCover simple nonabelian)
    (reference S SH literal literalH Msys root calibration navarro guard b hb)

/-- It is the same equivalence already used by the complete Brauer fibre. -/
theorem quotientMapEquiv_eq :
    quotientMapEquiv S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb =
      TypeBRankThreePrincipalQuotientBrauerFibre.quotientEquiv
        S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb := by
  apply MulEquiv.ext
  intro g
  exact (TypeBRankThreePrincipalQuotientBrauerFibre.quotientEquiv_projection
    S SH literal literalH Msys root calibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb g).symm

variable (w : Definition35Weight
  (problem S SH literal literalH Msys root calibration navarro guard b))

/-- The packet is constructed from the same original weight and reference. -/
def quotientWeight : QuotientWeightBrauerSource
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (reference S SH literal literalH Msys root calibration navarro guard b hb) w :=
  centerlessQuotientWeightBrauerSource
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (centreless parameters N C centreSpin fullCover simple nonabelian)
    (reference S SH literal literalH Msys root calibration navarro guard b hb) w

/-- These are exactly the raw fields used by the final quotient-weight output. -/
def quotientRawWeight : CharacterWeight 2 K
    (TypeBRankThreePrincipalQuotientBrauerFibre.quotientGroup
      S SH literal literalH Msys root calibration navarro guard b hb) where
  prime := root.prime
  subgroup := quotientRadical
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (reference S SH literal literalH Msys root calibration navarro guard b hb) w
  radical := (quotientWeight S SH literal literalH Msys root calibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb w).radical
  localCharacter := (quotientWeight S SH literal literalH Msys root calibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb w).ordinary
  defectZero := (quotientWeight S SH literal literalH Msys root calibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb w).defectZero

/-- The ordinary coordinate is evaluated through the literal quotient-normalizer map. -/
theorem quotientWeight_ordinaryDescends
    (x : NormalizerQuotient (SelectedRadical S b w)) :
    (quotientWeight S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w).ordinary
        (quotientNormalizerMap
          (problem S SH literal literalH Msys root calibration navarro guard b)
          (reference S SH literal literalH Msys root calibration navarro guard b hb) w x) =
      (selectedCharacterWeight S b w).localCharacter x :=
  (quotientWeight S SH literal literalH Msys root calibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb w).ordinaryDescends x

/-- The entire raw packet is the actual canonical image, including its own character. -/
theorem quotientRawWeight_eq_mapGroupEquiv :
    quotientRawWeight S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w =
      (selectedCharacterWeight S b w).mapGroupEquiv
        (quotientMapEquiv S SH literal literalH Msys root calibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb) := by
  symm
  apply CharacterWeight.mapGroupEquiv_eq_of_normalizer_coordinates
    (selectedCharacterWeight S b w)
    (quotientMapEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
    (quotientRawWeight S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb w) rfl
    (ModularRep.normalizerEquiv
      (quotientMapEquiv S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb)
      (SelectedRadical S b w))
  · intro x
    rfl
  · intro x
    exact quotientWeight_ordinaryDescends
      S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb w (QuotientGroup.mk x)

/-- The raw map agrees with the already fixed complete-fibre quotient equivalence. -/
theorem quotientRawWeight_eq_referenceMap :
    quotientRawWeight S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w =
      (selectedCharacterWeight S b w).mapGroupEquiv
        (TypeBRankThreePrincipalQuotientBrauerFibre.quotientEquiv
          S SH literal literalH Msys root calibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb) := by
  rw [quotientRawWeight_eq_mapGroupEquiv, quotientMapEquiv_eq]

/-- The transported quotient root has the original modular-system calibration. -/
theorem quotientWeight_root_residue :
    RootResidueCompatible Msys
      (quotientWeight S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w).iota :=
  TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue Msys
    ((problem S SH literal literalH Msys root calibration navarro guard b).localReduction w).iota
    (originalLocalRoot_residue S SH literal literalH Msys root calibration navarro guard b w)
    (centerlessQuotientNormalizerEquiv
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (centreless parameters N C centreSpin fullCover simple nonabelian)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) w)

theorem quotientWeight_root_eq_groupRoot :
    (quotientWeight S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w).iota =
      groupRoot Msys (NormalizerQuotient (quotientRadical
        (problem S SH literal literalH Msys root calibration navarro guard b)
        (reference S SH literal literalH Msys root calibration navarro guard b hb) w)) :=
  eq_groupRoot_of_residue Msys _ _
    (quotientWeight_root_residue S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb w)

/-- The actual normalizer root is constructed, not independently supplied. -/
def localInflationRoot : PrimeRegularRootEmbedding 2 k K
    (Subgroup.normalizer (quotientRadical
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) w :
        Set (TypeBRankThreePrincipalQuotientBrauerFibre.quotientGroup
          S SH literal literalH Msys root calibration navarro guard b hb))) :=
  groupRoot Msys _

/-- Compatibility concerns exactly the same chosen quotient representation. -/
theorem localInflationCompatible :
    Representation.BrauerRootLiftCompatibleAlong
      (chosenIBrRepresentation
        (quotientWeight S SH literal literalH Msys root calibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb w).iota
        (quotientWeight S SH literal literalH Msys root calibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb w).brauer).ρ
      (quotientWeight S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w).iota
      (localInflationRoot S SH literal literalH Msys root calibration navarro guard b hb w)
      (quotientLocalInflationMap
        (problem S SH literal literalH Msys root calibration navarro guard b)
        (reference S SH literal literalH Msys root calibration navarro guard b hb) w) := by
  let V : FDRep k (NormalizerQuotient (quotientRadical
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) w)) :=
    chosenIBrRepresentation
      (quotientWeight S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w).iota
      (quotientWeight S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w).brauer
  letI : AddCommGroup V := V.V.obj.isAddCommGroup
  letI : Module k V := V.V.obj.isModule
  letI : FiniteDimensional k V := V.V.property
  change Representation.BrauerRootLiftCompatibleAlong (p := 2) (k := k) (K := K) V.ρ
    (quotientWeight S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb w).iota
    (groupRoot Msys (Subgroup.normalizer (quotientRadical
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) w :
        Set (TypeBRankThreePrincipalQuotientBrauerFibre.quotientGroup
          S SH literal literalH Msys root calibration navarro guard b hb))))
    (quotientLocalInflationMap
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) w)
  rw [quotientWeight_root_eq_groupRoot S SH literal literalH Msys root calibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb w]
  exact groupRoot_compatible_along Msys V.ρ
    (quotientLocalInflationMap
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) w)

/-- Honest normalizer inflation is derived before any extension ambient is chosen. -/
def localInflation : QuotientLocalInflationSource
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (reference S SH literal literalH Msys root calibration navarro guard b hb) w
    (quotientWeight S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb w) :=
  quotientLocalInflationSourceOfCompatible
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (reference S SH literal literalH Msys root calibration navarro guard b hb) w
    (quotientWeight S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb w)
    (localInflationRoot S SH literal literalH Msys root calibration navarro guard b hb w)
    (localInflationCompatible S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb w)

@[simp] theorem localInflation_iota :
    (localInflation S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w).iota =
      localInflationRoot S SH literal literalH Msys root calibration navarro guard b hb w := rfl

theorem localInflation_inflation :
    PrimeRegularClassFunction.pullback
        (quotientLocalInflationMap
          (problem S SH literal literalH Msys root calibration navarro guard b)
          (reference S SH literal literalH Msys root calibration navarro guard b hb) w)
        (quotientWeight S SH literal literalH Msys root calibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb w).brauer.val =
      (localInflation S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w).brauer.val :=
  (localInflation S SH literal literalH Msys root calibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb w).inflation

/-- The quotient root agrees with the fixed reference root on its required finite domain. -/
theorem quotientWeight_rootAgreement :
    QuotientRootAgreement
      (TypeBRankThreePrincipalQuotientBrauerFibre.quotientRoot
        S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb)
      (quotientRadical
        (problem S SH literal literalH Msys root calibration navarro guard b)
        (reference S SH literal literalH Msys root calibration navarro guard b hb) w)
      (quotientWeight S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w).iota := by
  rw [quotientWeight_root_eq_groupRoot,
    eq_groupRoot_of_residue Msys _ _
      (TypeBRankThreePrincipalQuotientBrauerFibre.quotientRoot_residue
        S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb)]
  exact groupRoot_agrees_of_dvd Msys _ _
    (Nat.ordCompl_dvd_ordCompl_of_dvd (local_order_dvd (quotientRadical
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) w)) 2)

/-- The inflated normalizer root has the same fixed-reference finite-domain agreement. -/
theorem localInflation_rootAgreement :
    NormalizerRootAgreement
      (TypeBRankThreePrincipalQuotientBrauerFibre.quotientRoot
        S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb)
      (quotientRadical
        (problem S SH literal literalH Msys root calibration navarro guard b)
        (reference S SH literal literalH Msys root calibration navarro guard b hb) w)
      (localInflation S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb w).iota := by
  rw [localInflation_iota,
    eq_groupRoot_of_residue Msys _ _
      (TypeBRankThreePrincipalQuotientBrauerFibre.quotientRoot_residue
        S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb)]
  exact groupRoot_agrees_of_dvd Msys _ _
    (Nat.ordCompl_dvd_ordCompl_of_dvd
      (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (quotientRadical
        (problem S SH literal literalH Msys root calibration navarro guard b)
        (reference S SH literal literalH Msys root calibration navarro guard b hb) w :
          Set (TypeBRankThreePrincipalQuotientBrauerFibre.quotientGroup
            S SH literal literalH Msys root calibration navarro guard b hb)))) 2)

end ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientLocalPackets


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
