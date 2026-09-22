import ModularRep.PaperProofs.TypeBCentralKernelPairRepresentativeTransport
import ModularRep.PaperProofs.TypeBLocalReductionInstantiation
import ModularRep.PaperProofs.TypeBPrincipalRootLiftBinding

/-!
# Local characters and specified pairs over one modular system

The quotient character is the reduction of the given ordinary weight's
own local character. All roots come from the same residue convention.
Literal block catalogues are retained, while the conjugate root equations
are derived from the actual group equivalences. No pair witness is an input
to these constructions.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding

open ModularRep CharacterWeight TypeBCentralKernelCarriers
open TypeBCentralKernelInertia TypeBCentralKernelTripleCertificate
open TypeBCentralKernelTripleCarriers TypeBCentralKernelTripleRootFamily
open TypeBLocalReductionInstantiation TypeBModularGroupRootBinding

variable {p : ℕ} {K O k : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k p] [IsAlgClosed k] [CharZero K]
  (Msys : ModularSystem p K O k)

section Roots

variable {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]

/-- Transport along the actual equivalence preserves residue calibration. -/
theorem alongMulEquiv_residue
    (iota : PrimeRegularRootEmbedding p k K X)
    (compatible : RootResidueCompatible Msys iota) (e : X ≃* Y) :
    RootResidueCompatible Msys (iota.alongMulEquiv e) := by
  intro z hz
  rw [PrimeRegularRootEmbedding.alongMulEquiv_lift]
  apply compatible
  have hexp : primeRegularExponent p X = primeRegularExponent p Y :=
    congrArg (fun d : ℕ => ordCompl[p] d) (Nat.card_congr e.toEquiv)
  simpa only [hexp] using hz

end Roots

section Weight

variable {G : Type} [Group G] [Finite G] (W : CharacterWeight p K G)

/-- The root on the literal normalizer quotient. -/
def quotientRoot : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup) :=
  groupRoot Msys (NormalizerQuotient W.subgroup)

theorem quotientRoot_residue : RootResidueCompatible Msys (quotientRoot Msys W) :=
  groupRoot_residue Msys (NormalizerQuotient W.subgroup)

/-- This is also the restriction of the application's calibrated root. -/
theorem quotientRoot_eq_localRoot (root : PrimeRegularRootEmbedding p k K G)
    (calibration : RootResidueCompatible Msys root) :
    quotientRoot Msys W = TypeBLocalReductionInstantiation.localRoot root W.subgroup :=
  (eq_groupRoot_of_residue Msys (NormalizerQuotient W.subgroup)
    (TypeBLocalReductionInstantiation.localRoot root W.subgroup)
    (localRoot_residue Msys root calibration W.subgroup)).symm

theorem normalizerRoot_residue : RootResidueCompatible Msys
    (TypeBCentralKernelLocalReduction.normalizerRoot W (quotientRoot Msys W)) := by
  intro z hz
  rw [PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift]
  apply quotientRoot_residue Msys W
  have hexp := PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq Msys.prime
    (TypeBCentralKernelLocalReduction.normalizerKernel W)
    (TypeBCentralKernelLocalReduction.normalizerKernel_isPGroup W)
  simpa only [hexp] using hz

variable [HasEnoughRootsOfUnity K (Nat.card G)]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding p k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- Only the finite local quotient is used to select this reduction. -/
def quotientReduction : IBr (quotientRoot Msys W) := by
  letI := localOrdinaryRoots (K := K) W.subgroup
  exact Classical.choose ((navarro (NormalizerQuotient W.subgroup)
    (quotientRoot Msys W) (quotientRoot_residue Msys W)).reduction
      W.localCharacter W.defectZero)

theorem quotientReduction_value : TypeBCentralKernelLocalReduction.Reduces
    (quotientRoot Msys W) W.localCharacter (quotientReduction Msys W navarro) := by
  letI := localOrdinaryRoots (K := K) W.subgroup
  exact Classical.choose_spec ((navarro (NormalizerQuotient W.subgroup)
    (quotientRoot Msys W) (quotientRoot_residue Msys W)).reduction
      W.localCharacter W.defectZero)

theorem quotientReduction_unique (phi : IBr (quotientRoot Msys W))
    (reduction : TypeBCentralKernelLocalReduction.Reduces
      (quotientRoot Msys W) W.localCharacter phi) :
    phi = quotientReduction Msys W navarro :=
  reduction_unique (quotientRoot Msys W) W.localCharacter phi
    (quotientReduction Msys W navarro) reduction
    (quotientReduction_value Msys W navarro)

end Weight

section Pair

variable {A : Type} [Group A] [Finite A] (G : Subgroup A) [G.Normal]
  (root : PrimeRegularRootEmbedding p k K G)
  (calibration : RootResidueCompatible Msys root)
  (theta : IBr root) (W : CharacterWeight p K G)
  (hUT : U G W ≤ T G root theta)

include calibration in
theorem baseRoot_eq_groupRoot :
    TypeBCentralKernelTripleCharacters.baseRoot G root theta =
      groupRoot Msys (inside G (T G root theta)) :=
  eq_groupRoot_of_residue Msys _ _
    (alongMulEquiv_residue Msys root calibration
      (TypeBCentralKernelTripleCharacters.baseEquiv G root theta))

theorem localRoot_eq_groupRoot :
    TypeBCentralKernelTripleCharacters.localRoot G root theta W hUT
      (quotientRoot Msys W) =
        groupRoot Msys
          (localBase (inside G (T G root theta)) (inside (U G W) (T G root theta))) :=
  eq_groupRoot_of_residue Msys _ _
    (alongMulEquiv_residue Msys
      (TypeBCentralKernelLocalReduction.normalizerRoot W (quotientRoot Msys W))
      (normalizerRoot_residue Msys W)
      (TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT))

/-- The old specified pair carrier with both root guards constructed. -/
def pairData
    (blocks : PhysicalBlockFamily (k := k)
      (inside G (T G root theta)) (inside (U G W) (T G root theta))) :
    TypeBCentralKernelConjugatePairBinding.PairData G root theta W hUT where
  quotientRoot := quotientRoot Msys W
  ambientRoot := groupRoot Msys (T G root theta)
  blocks := blocks
  baseAgree := by
    rw [baseRoot_eq_groupRoot Msys G root calibration theta]
    exact groupRoot_agrees_of_dvd Msys _ _
      (Nat.ordCompl_dvd_ordCompl_of_dvd
        (Subgroup.card_subgroup_dvd_card (inside G (T G root theta))) p)
  localAgree := by
    rw [localRoot_eq_groupRoot Msys G root theta W hUT]
    exact groupRoot_agrees_of_dvd Msys _ _
      (Nat.ordCompl_dvd_ordCompl_of_dvd
        ((Subgroup.card_subgroup_dvd_card
          (localBase (inside G (T G root theta)) (inside (U G W) (T G root theta)))).trans
          (Subgroup.card_subgroup_dvd_card (inside (U G W) (T G root theta)))) p)

@[simp] theorem pairData_quotientRoot
    (blocks : PhysicalBlockFamily (k := k)
      (inside G (T G root theta)) (inside (U G W) (T G root theta))) :
    (pairData Msys G root calibration theta W hUT blocks).quotientRoot =
      quotientRoot Msys W := rfl

@[simp] theorem pairData_ambientRoot
    (blocks : PhysicalBlockFamily (k := k)
      (inside G (T G root theta)) (inside (U G W) (T G root theta))) :
    (pairData Msys G root calibration theta W hUT blocks).ambientRoot =
      groupRoot Msys (T G root theta) := rfl

variable [HasEnoughRootsOfUnity K (Nat.card G)]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding p k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (blocks : PhysicalBlockFamily (k := k)
    (inside G (T G root theta)) (inside (U G W) (T G root theta)))

/-- Inflation and the actual normalizer equivalence give the local character. -/
def localCharacter : IBr (TypeBCentralKernelConjugatePairBinding.tripleData
    G root theta W hUT (pairData Msys G root calibration theta W hUT blocks)).localData.iota :=
  TypeBCentralKernelTripleCharacters.localBrauer G root theta W hUT
    (quotientRoot Msys W) (quotientReduction Msys W navarro)

theorem localCharacter_reduction
    (x : PrimeRegularElement
      (G := localBase (inside G (T G root theta)) (inside (U G W) (T G root theta))) p) :
    W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup
      ((TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT).symm x.val)) =
        (localCharacter Msys G root calibration theta W hUT navarro blocks).val x :=
  TypeBCentralKernelTripleCharacters.localBrauer_reduction G root theta W hUT
    (quotientRoot Msys W) (quotientReduction Msys W navarro)
    (quotientReduction_value Msys W navarro) x

/-- The literal complete witness with the constructed characters. -/
abbrev PairWitness := BlockTripleWitness
  (TypeBCentralKernelConjugatePairBinding.tripleData G root theta W hUT
    (pairData Msys G root calibration theta W hUT blocks))
  (TypeBCentralKernelConjugatePairBinding.baseCharacter G root theta W hUT
    (pairData Msys G root calibration theta W hUT blocks))
  (localCharacter Msys G root calibration theta W hUT navarro blocks)

end Pair

section Coherence

variable {A : Type} [Group A] [Finite A] (G : Subgroup A) [G.Normal]
  (root : PrimeRegularRootEmbedding p k K G)
  (calibration : RootResidueCompatible Msys root)
  (catalogues : ∀ (theta : IBr root) (W : CharacterWeight p K G)
    (hUT : U G W ≤ T G root theta), PhysicalBlockFamily (k := k)
      (inside G (T G root theta)) (inside (U G W) (T G root theta)))

/-- Equal orders of the actual conjugate groups give whole lift coherence. -/
def coherentData : TypeBCentralKernelPairRepresentativeTransport.CoherentData G root where
  data theta W hUT := pairData Msys G root calibration theta W hUT (catalogues theta W hUT)
  ambientLifts theta W hUT a := by
    exact TypeBPrincipalRootLiftBinding.groupRoot_lift_eq_of_exponent_eq Msys
      (congrArg (fun d : ℕ => ordCompl[p] d)
        (Nat.card_congr
          (TypeBCentralKernelConjugateInertia.characterInertiaEquiv G root theta a).toEquiv))
  quotientLifts theta W hUT a := by
    exact TypeBPrincipalRootLiftBinding.groupRoot_lift_eq_of_exponent_eq Msys
      (congrArg (fun d : ℕ => ordCompl[p] d)
        (Nat.card_congr
          (rightNormalizerQuotientEquiv (originalAction G a⁻¹) W.subgroup).toEquiv))

@[simp] theorem coherentData_data (theta : IBr root) (W : CharacterWeight p K G)
    (hUT : U G W ≤ T G root theta) :
    (coherentData Msys G root calibration catalogues).data theta W hUT =
      pairData Msys G root calibration theta W hUT (catalogues theta W hUT) := rfl

end Coherence

end ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
