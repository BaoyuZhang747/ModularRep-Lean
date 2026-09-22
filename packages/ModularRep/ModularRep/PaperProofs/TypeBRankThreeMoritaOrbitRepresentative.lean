import ModularRep.PaperProofs.TypeBRankThreeMoritaPacketSurjectivity
import ModularRep.PaperProofs.TypeBRankThreeJordanAmbientExtension

/-!
# A selected representative in every actual ambient packet orbit

The same Jordan map supplies the initial Levi preimage through the base
Morita equivalence. A literal nonnegative restriction expansion supplies
an initial constituent. Existing component data are required only at an
occurring constituent of that preimage. The accepted ambient-extension
theorem gives the same selected Jordan character and its extension.

This file does not identify the chosen field actor with full automorphism
inertia and does not construct local weight or block-triple data.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaOrbitRepresentative

open ModularRep FDRepSimpleClassKZero
open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBOrdinaryBlockSplitting TypeBRankThreeNonprincipalSeriesBinding
open TypeBRankThreeNonprincipalApplication TypeBRankThreeNonprincipalGeometry
open TypeBRegularLeviRationalCarriers TypeBRankThreeFactorsPointSource
open TypeBRankThreeJordanDualLabel TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeSelection TypeBLeviRepresentativeAssembly
open TypeBLeviRepresentativeTransport TypeBLeviRepresentativeClifford
open TypeBLeviRepresentativeField TypeBLemma47LeviApplication
open TypeBCharacteristicTwoConstituentSource TypeBCharacteristicTwoCorrespondenceSource
open TypeBCharacteristicTwoExtensionCarriers TypeBCharacteristicTwoCliffordKernel
open TypeBCharacteristicTwoCliffordApplication TypeBCharacteristicTwoGallagherSource
open TypeBCharacteristicTwoGallagherProduct
open TypeBRankThreeJordanSource TypeBRankThreeJordanPacketCarriers
open TypeBRankThreeJordanOriginalTransport TypeBRankThreeJordanPacketCopies
open TypeBRankThreeJordanActions TypeBRankThreeJordanCliffordCarriers
open TypeBRankThreeJordanMap TypeBRankThreeJordanTransfer
open TypeBRationalSeriesSource
open TypeBRankThreeMoritaSources TypeBRankThreeMoritaPhysicalSource
open TypeBRankThreeMoritaSimpleTransport

section LiteralRestriction

variable {A k K : Type} [Group A] [Field k] [Field K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  (Frob : MulAut A) (Lbar : Subgroup A)
  [Finite (fixedPoints Frob.toMonoidHom)]
  (iotaL : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
  (iotaN : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar))

/-- The standard restriction expansion at these literal H/N roots.
It contains no selected constituent or stabilizer conclusion. -/
structure RestrictionExpansion (psi : IBr (rootH Frob Lbar iotaL)) where
  multiplicity : IBr (rootN Frob Lbar iotaN) →₀ ℕ
  nonzero : multiplicity ≠ 0
  value : ∀ x : PrimeRegularElement (G := N Frob Lbar) 2,
    psi.val (PrimeRegularElement.map (Subgroup.inclusion (N_le_H Frob Lbar)) x) =
      multiplicity.sum (fun theta n => (n : K) * theta.val x)

/-- A nonzero coefficient gives occurrence for the actual subgroup copy. -/
theorem exists_occurs (psi : IBr (rootH Frob Lbar iotaL))
    (restriction : RestrictionExpansion Frob Lbar iotaL iotaN psi) :
    ∃ theta : IBr (rootN Frob Lbar iotaN),
      Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
        (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi theta := by
  classical
  have nonzeroCoefficient : ∃ theta, restriction.multiplicity theta ≠ 0 := by
    by_contra h
    apply restriction.nonzero
    ext theta
    exact not_not.mp (fun htheta => h ⟨theta, htheta⟩)
  obtain ⟨theta, htheta⟩ := nonzeroCoefficient
  refine ⟨theta, (occurs_iff_occursAlong (H Frob Lbar) (N Frob Lbar)
    (N_le_H Frob Lbar) (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN)
    psi theta).mpr ?_⟩
  exact ⟨restriction.multiplicity, htheta, restriction.value⟩

end LiteralRestriction

section ConstituentInputs

variable {A E k K : Type} [Group A] [Group E] [Finite E] [IsCyclic E]
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (Frob : MulAut A) (Lbar : Subgroup A)
  [Finite (fixedPoints Frob.toMonoidHom)]
  (stable : Lbar.map Frob.toMonoidHom = Lbar)
  (field : FieldData Frob Lbar E)
  (iotaN : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar))

/-- Only existing specified component and standard-factor inputs, at one
actual constituent. Cycle coordinates may depend on its orbit stabilizer. -/
structure ConstituentData (theta : IBr (rootN Frob Lbar iotaN)) where
  C : Type
  finiteC : Fintype C
  length : C → ℕ
  geometry : PrimalData Frob Lbar stable length
  presentation :
    letI := finiteC
    Presentation geometry field iotaN theta
  S : C → Type
  Q : C → Type
  J : C → Type
  groupS : ∀ c, Group (S c)
  finiteS : ∀ c, Finite (S c)
  groupQ : ∀ c, Group (Q c)
  groupJ : ∀ c, Group (J c)
  standard :
    letI := finiteC
    letI := groupS
    letI := finiteS
    letI := groupQ
    letI := groupJ
    StandardData presentation S Q J

end ConstituentInputs

variable {p f : ℕ} {F A E K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field A] [IsAlgClosed A] [CharP A p] [Algebra F A]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]
  [Group E] [Finite E] [IsCyclic E]
  (parameters : OddFieldParameters F p f) (normF : NormSource 3 F)
  (orthogonal : TypeBCliffordOrthogonalSourceBinding.Source
    3 F p f parameters (by decide) normF)
  [Finite (Spin 3 F normF)] [Finite (SpecialClifford 3 F)]
  (Msys : ModularSystem 2 K O k)
  (iotaG : PrimeRegularRootEmbedding 2 k K (Spin 3 F normF))
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F normF))]
  (blocksG : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F normF) => c.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F normF))]
  (ordinaryG : OrdinaryBlockSource Msys iotaG
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG) blocksG)
  (seriesG : Sources parameters Msys iotaG
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG) blocksG ordinaryG)
  (dualFrobenius : FrobeniusSource p f A)
  (dualPoints : RationalPointSource F A p f dualFrobenius)
  (dualGeometry : GeometrySource F A p f dualFrobenius dualPoints)
  (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (r : ManuscriptReduction parameters normF orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b)
  (normA : NormSource 3 A) (chart : PairedChart normA r.levi)
  (Frob : MulAut (SpecialClifford 3 A))
  [Finite (fixedPoints Frob.toMonoidHom)]
  (iotaL : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom chart.primalLevi))
  [Fintype (LiteralPrimitiveBlock k (L Frob.toMonoidHom chart.primalLevi))]
  (blocksL : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (L Frob.toMonoidHom chart.primalLevi) => c.val))
  [HasEnoughRootsOfUnity K (Nat.card (L Frob.toMonoidHom chart.primalLevi))]
  (ordinaryL : OrdinaryBlockSource Msys iotaL
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaL) blocksL)
  (familyL : RationalSeriesSource K (L Frob.toMonoidHom chart.primalLevi)
    (TypeBRankThreeJordanLeviPacket.FullRationalIndex p (rationalLevi r)))
  (points : CliffordFixedPointSource 3 p f F A normF normA Frob)
  (field : FieldData Frob chart.primalLevi E)
  (perfect : commutator (Spin 3 F normF) = ⊤)
  (source : Certificate parameters normF orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
    iotaL blocksL ordinaryL familyL points field perfect)
  (iotaN : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom chart.primalLevi))
  (iotaGamma : PrimeRegularRootEmbedding 2 k K (Gamma Frob chart.primalLevi))

noncomputable local instance finiteH {T : Type} [Group T]
    (sigma : MulAut T) (U : Subgroup T) [Finite (fixedPoints sigma.toMonoidHom)] :
    Fintype (H sigma U) := Fintype.ofFinite (H sigma U)
noncomputable local instance finiteNInH {T : Type} [Group T]
    (sigma : MulAut T) (U : Subgroup T) [Finite (fixedPoints sigma.toMonoidHom)] :
    Fintype ((N sigma U).subgroupOf (H sigma U)) :=
  Fintype.ofFinite ((N sigma U).subgroupOf (H sigma U))
local instance quotientCommutative {T : Type} [Group T]
    (sigma : MulAut T) (U : Subgroup T) :
    IsMulCommutative (Gamma sigma U ⧸ N sigma U) := quotientN_abelian sigma U

variable {BlockN : Type} [Fintype BlockN]
  {idempotentN : BlockN → k[(N Frob chart.primalLevi).subgroupOf (H Frob chart.primalLevi)]}
  (blocksN : BlockIdempotentDecomposition idempotentN)
  (catalogueH : BlockCentralCharacterCatalogue
    (blocksL.alongMulEquiv (originalLEquiv Frob chart.primalLevi)))
  (catalogueN : BlockCentralCharacterCatalogue blocksN)
  (tensorSupport : TensorSupportPrinciple k)
  (bimodule : Rep.{0} k
    (Spin 3 F normF × (L Frob.toMonoidHom chart.primalLevi)ᵐᵒᵖ))
  [Module.Finite k bimodule]
  (leftSupport : LeftSupport bimodule
    (ambientIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r))
  (baseMorita : BaseMorita tensorSupport bimodule
    (leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
      iotaL blocksL ordinaryL familyL)
    (ambientIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r) leftSupport)
  (calibration : SameJordanCalibration iotaL iotaG blocksL
    (leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
      iotaL blocksL ordinaryL familyL) source.jordan.character bimodule)
  (simpleSupported : SupportedSimplePrinciple k)

include baseMorita calibration simpleSupported

/-- Each ambient packet orbit contains an image selected by the existing
Levi theorem, with the extension of that SAME ambient character. -/
theorem actual_orbit_representative
    (decomposition : ∀ x : SpecialClifford 3 A,
      ∃ g ∈ SpinSubgroup 3 A normA, ∃ z ∈ Subgroup.center (SpecialClifford 3 A),
        x = g * z)
    (intersection : pairedLevi chart.primalLevi ⊓ SpinSubgroup 3 A normA ≤ chart.primalLevi)
    (lang : TypeBRankThreeJordanDiagonalProduct.LeviLangSource Frob chart.primalLevi)
    (roots_N_H : RootAgreement (H Frob chart.primalLevi) (N Frob chart.primalLevi)
      (rootH Frob chart.primalLevi iotaL) (rootN Frob chart.primalLevi iotaN))
    (fieldScope : SpathCoefficientField 2 k (rootH Frob chart.primalLevi iotaL).prime)
    (covering : FixedRestrictionCovering
      (H Frob chart.primalLevi) (N Frob chart.primalLevi) (N_le_H Frob chart.primalLevi)
      (rootH Frob chart.primalLevi iotaL) (rootN Frob chart.primalLevi iotaN)
      (blocksL.alongMulEquiv (originalLEquiv Frob chart.primalLevi)) blocksN
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (rootH Frob chart.primalLevi iotaL))
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
        (embeddedRoot (H Frob chart.primalLevi) (N Frob chart.primalLevi)
          (N_le_H Frob chart.primalLevi) (rootN Frob chart.primalLevi iotaN)))
      catalogueH catalogueN roots_N_H fieldScope)
    (restriction : ∀ psi : Packet iotaL blocksL
      (leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
        seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
        iotaL blocksL ordinaryL familyL),
      RestrictionExpansion Frob chart.primalLevi iotaL iotaN
        (characterEquiv Frob chart.primalLevi iotaL psi.val))
    (constituents : ∀ (psi : Packet iotaL blocksL
        (leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
          seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
          iotaL blocksL ordinaryL familyL))
      (theta : IBr (rootN Frob chart.primalLevi iotaN)),
      Occurs (H Frob chart.primalLevi) (N Frob chart.primalLevi)
        (N_le_H Frob chart.primalLevi) (rootH Frob chart.primalLevi iotaL)
        (rootN Frob chart.primalLevi iotaN)
        (characterEquiv Frob chart.primalLevi iotaL psi.val) theta →
      ConstituentData Frob chart.primalLevi source.primal_frobenius field iotaN theta)
    (iotaI : ∀ theta : IBr (rootN Frob chart.primalLevi iotaN),
      PrimeRegularRootEmbedding 2 k K
        (BrauerInertia (H Frob chart.primalLevi) (N Frob chart.primalLevi)
          (rootN Frob chart.primalLevi iotaN) theta))
    (iotaA : ∀ theta : IBr (rootN Frob chart.primalLevi iotaN),
      PrimeRegularRootEmbedding 2 k K
        (AmbientInertia (N Frob chart.primalLevi) (rootN Frob chart.primalLevi iotaN) theta))
    (roots_N_G : RootsAgree iotaGamma (rootN Frob chart.primalLevi iotaN))
    (roots_A_G : ∀ theta, RootsAgree iotaGamma (iotaA theta))
    (roots_N_A : ∀ theta, RootsAgree (iotaA theta) (rootN Frob chart.primalLevi iotaN))
    (roots_I_A : ∀ theta, RootsAgree (iotaA theta) (iotaI theta))
    (multiplicityFree : MultiplicityFreeRestriction (N Frob chart.primalLevi)
      iotaGamma (rootN Frob chart.primalLevi iotaN))
    (above : ExistsAbovePrinciple k K)
    (homogeneousClifford : HomogeneousCliffordPrinciple k K)
    (source87 : Navarro87Principle k K)
    (source89 : ∀ theta, Navarro89Source (H Frob chart.primalLevi) (N Frob chart.primalLevi)
      (N_le_H Frob chart.primalLevi) (rootH Frob chart.primalLevi iotaL)
      (rootN Frob chart.primalLevi iotaN) theta (iotaI theta))
    (source820 : Navarro820AbelianProductPrinciple k K)
    (source812 : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k) :
    letI := originalFieldAction Frob chart.primalLevi iotaL field
    letI := cliffordBrauerAction iotaG
    letI := spinBrauerFieldAction points field.fieldPoints perfect iotaG
    let aG := spinFieldAction points field.fieldPoints perfect
    let aL := originalField Frob chart.primalLevi field
    let eL := leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
      iotaL blocksL ordinaryL familyL
    let eG := ambientIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r
    ∀ Phi : Packet iotaG blocksG eG,
      ∃ (theta : IBr (rootN Frob chart.primalLevi iotaN))
        (y : Gamma Frob chart.primalLevi) (psiH : IBr (rootH Frob chart.primalLevi iotaL))
        (psi : Packet iotaL blocksL eL),
        characterEquiv Frob chart.primalLevi iotaL psi.val = psiH ∧
        psi.val = TypeBLeviRepresentativeOriginalExtension.originalCharacter
          Frob chart.primalLevi iotaL psiH ∧
        source.jordan.character psi = gammaEmbedding points chart.primalLevi y • Phi.val ∧
        Occurs (H Frob chart.primalLevi) (N Frob chart.primalLevi)
          (N_le_H Frob chart.primalLevi) (rootH Frob chart.primalLevi iotaL)
          (rootN Frob chart.primalLevi iotaN) psiH theta ∧
        Formalisation.SemidirectStabilizerFactors
          (cliffordFieldAction points field.fieldPoints)
          (clifford_semidirect_compatible points field.fieldPoints perfect iotaG)
          (source.jordan.character psi) ∧
        MulAction.stabilizer E (source.jordan.character psi) = MulAction.stabilizer E psi.val ∧
        InPacket iotaG blocksG eG (source.jordan.character psi) ∧
        supportingBlock iotaG blocksG (source.jordan.character psi) =
          (source.jordan.block ⟨supportingBlock iotaL blocksL psi.val, psi.property⟩).val ∧
        (∃ W : FDRep k (L Frob.toMonoidHom chart.primalLevi),
          Representation.IsIrreducible W.ρ ∧
          psi.val.val = Representation.brauerCharacterOfRootEmbedding W.ρ iotaL ∧
          ∃ rho : Representation k (FieldSemidirect iotaL aL psi.val) W,
            Representation.IsIrreducible rho ∧
            Nonempty (Representation.Equiv
              (rho.pullback (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
                FieldSemidirect iotaL aL psi.val)) W.ρ)) ∧
        ∃ V : FDRep k (Spin 3 F normF),
          Representation.IsIrreducible V.ρ ∧
          (source.jordan.character psi).val =
            Representation.brauerCharacterOfRootEmbedding V.ρ iotaG ∧
          ∃ rho : Representation k
            ((Spin 3 F normF) ⋊[aG.comp (fieldStabilizer iotaL aL psi.val).subtype]
              (fieldStabilizer iotaL aL psi.val)) V,
            Representation.IsIrreducible rho ∧
            Nonempty (Representation.Equiv
              (rho.pullback (SemidirectProduct.inl : Spin 3 F normF →*
                (Spin 3 F normF) ⋊[aG.comp (fieldStabilizer iotaL aL psi.val).subtype]
                  (fieldStabilizer iotaL aL psi.val))) V.ρ) := by
  letI := ambientBrauerAction (H Frob chart.primalLevi)
    (rootH Frob chart.primalLevi iotaL)
  letI := ambientBrauerAction (N Frob chart.primalLevi)
    (rootN Frob chart.primalLevi iotaN)
  letI := originalAmbientAction Frob chart.primalLevi iotaL
  letI := originalFieldAction Frob chart.primalLevi iotaL field
  letI := cliffordBrauerAction iotaG
  letI := spinBrauerFieldAction points field.fieldPoints perfect iotaG
  letI := gammaBrauerAction points iotaG chart.primalLevi
  let aG := spinFieldAction points field.fieldPoints perfect
  let aL := originalField Frob chart.primalLevi field
  let eL := leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
    iotaL blocksL ordinaryL familyL
  let eG := ambientIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r
  letI := TypeBRankThreeJordanMap.packetGamma (Lbar := chart.primalLevi) (iotaL := iotaL) (blocksL := blocksL)
    (eL := eL) (gammaInvariant := source.gamma_invariant)
  have idempotentL : IsIdempotentElem eL :=
    TypeBRankThreeJordanLeviPacket.idempotent_idempotent Msys iotaL blocksL ordinaryL
      familyL parameters.prime (two_ne_defining parameters) (rationalLabel r)
      (rationalLabel_defining_regular r)
  have centralL : IsMulCentral eL :=
    TypeBRankThreeJordanLeviPacket.idempotent_central Msys iotaL blocksL ordinaryL
      familyL parameters.prime (two_ne_defining parameters) (rationalLabel r)
      (rationalLabel_defining_regular r)
  have surjective := TypeBRankThreeMoritaPacketSurjectivity.packetMap_surjective
    points chart.primalLevi field perfect iotaL iotaG blocksL blocksG eL eG
    source.gamma_invariant source.field_invariant source.jordan
    tensorSupport simpleSupported bimodule leftSupport baseMorita calibration idempotentL centralL
  change ∀ Phi : Packet iotaG blocksG eG, _
  intro Phi
  let psi0 := Classical.choose (surjective Phi)
  have image0 := Classical.choose_spec (surjective Phi)
  let psiH0 := characterEquiv Frob chart.primalLevi iotaL psi0.val
  let P := MulAction.orbit (Gamma Frob chart.primalLevi) psiH0
  have initialPacket : InPacket iotaL blocksL eL
      (TypeBLeviRepresentativeOriginalExtension.originalCharacter
        Frob chart.primalLevi iotaL psiH0) := by
    exact Eq.mpr (congrArg (InPacket iotaL blocksL eL)
      ((characterEquiv Frob chart.primalLevi iotaL).symm_apply_apply psi0.val))
      psi0.property
  have occurrence := exists_occurs Frob chart.primalLevi iotaL iotaN
    psiH0 (restriction psi0)
  let theta0 := Classical.choose occurrence
  have occurs0 := Classical.choose_spec occurrence
  let inputs := constituents psi0 theta0 occurs0
  letI := inputs.finiteC
  letI := inputs.groupS
  letI := inputs.finiteS
  letI := inputs.groupQ
  letI := inputs.groupJ
  have selected := TypeBRankThreeJordanAmbientExtension.actual_representative_jordan_ambient_extension
    parameters normF orthogonal Msys iotaG blocksG ordinaryG seriesG
    dualFrobenius dualPoints dualGeometry b r normA chart Frob iotaL blocksL ordinaryL
    familyL points field perfect source inputs.geometry iotaN iotaGamma blocksN catalogueH catalogueN
    decomposition intersection lang roots_N_H fieldScope covering P psiH0 rfl initialPacket
    theta0 occurs0 inputs.presentation inputs.S inputs.Q inputs.J inputs.standard
    iotaI iotaA roots_N_G roots_A_G roots_N_A roots_I_A multiplicityFree
    above homogeneousClifford source87 source89 source820 source812
  let theta := Classical.choose selected
  have selectedTheta := Classical.choose_spec selected
  let y := Classical.choose selectedTheta
  have selectedY := Classical.choose_spec selectedTheta
  let psiH := Classical.choose selectedY
  have selectedH := Classical.choose_spec selectedY
  let psi := Classical.choose selectedH
  have selectedPsi := Classical.choose_spec selectedH
  have hpsi := selectedPsi.1
  have hoccurs := selectedPsi.2.2.2.1
  have hcopy := selectedPsi.2.2.2.2.2.1
  have horiginal := selectedPsi.2.2.2.2.2.2.1
  have hfactor := selectedPsi.2.2.2.2.2.2.2.1
  have hfixer := selectedPsi.2.2.2.2.2.2.2.2.1
  have hpacket := selectedPsi.2.2.2.2.2.2.2.2.2.1
  have hblock := selectedPsi.2.2.2.2.2.2.2.2.2.2.1
  have leviExtension := selectedPsi.2.2.2.2.2.2.2.2.2.2.2.1
  have ambientExtension := selectedPsi.2.2.2.2.2.2.2.2.2.2.2.2
  have originalOrbit : psi.val = y • psi0.val := by
    apply (characterEquiv Frob chart.primalLevi iotaL).injective
    calc
      characterEquiv Frob chart.primalLevi iotaL psi.val = psiH := hcopy
      _ = y • psiH0 := hpsi
      _ = characterEquiv Frob chart.primalLevi iotaL (y • psi0.val) :=
        (characterEquiv_ambient Frob chart.primalLevi iotaL y psi0.val).symm
  have packetOrbit : psi = y • psi0 := Subtype.ext originalOrbit
  have originalImage : source.jordan.character psi0 = Phi.val := congrArg Subtype.val image0
  have ambientOrbit : source.jordan.character psi =
      gammaEmbedding points chart.primalLevi y • Phi.val := by
    calc
      source.jordan.character psi = source.jordan.character (y • psi0) :=
        congrArg source.jordan.character packetOrbit
      _ = y • source.jordan.character psi0 := source.jordan.gamma_equivariant y psi0
      _ = gammaEmbedding points chart.primalLevi y • source.jordan.character psi0 :=
        gamma_action_eq points iotaG chart.primalLevi y (source.jordan.character psi0)
      _ = gammaEmbedding points chart.primalLevi y • Phi.val :=
        congrArg (fun chi : IBr iotaG => gammaEmbedding points chart.primalLevi y • chi)
          originalImage
  exact ⟨theta, y, psiH, psi, hcopy, horiginal, ambientOrbit, hoccurs,
    hfactor, hfixer, hpacket, hblock, leviExtension, ambientExtension⟩

end ModularRep.PaperProofs.TypeBRankThreeMoritaOrbitRepresentative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
