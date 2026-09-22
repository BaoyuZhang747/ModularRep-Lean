import ModularRep.PaperProofs.TypeBRankThreeMoritaApplication
import ModularRep.PaperProofs.TypeBRankThreeJordanRepresentativeApplication

/-!
# The selected representative and its literal Morita tensor

The representative endpoint is invoked once. Its original Levi character,
affording representation and extension are retained. The same specified
bimodule gives the literal tensor Jordan image and the induced Morita square
over that character's actual field stabilizer. Extension of the tensor follows
through that square, using the retained Levi extension.

The specified and published source interpretations keep their existing scope.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaSelectedApplication

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
open TypeBRankThreeMoritaTensor TypeBRankThreeMoritaFiniteTensor
open TypeBRankThreeMoritaSources TypeBRankThreeMoritaInduced
open TypeBRankThreeMoritaSplitApplication TypeBRankThreeMoritaPhysicalSource
open TypeBRankThreeMoritaSimpleTransport TypeBRankThreeMoritaSupportedSquare

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

variable {C : Type} [Fintype C] {m : C → ℕ}
  (geometry : PrimalData Frob chart.primalLevi source.primal_frobenius m)
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
    IsMulCommutative (Gamma sigma U ⧸ N sigma U) :=
  quotientN_abelian sigma U

variable {BlockN : Type} [Fintype BlockN]
  {idempotentN : BlockN → k[(N Frob chart.primalLevi).subgroupOf (H Frob chart.primalLevi)]}
  (blocksN : BlockIdempotentDecomposition idempotentN)
  (catalogueH : BlockCentralCharacterCatalogue
    (blocksL.alongMulEquiv (originalLEquiv Frob chart.primalLevi)))
  (catalogueN : BlockCentralCharacterCatalogue blocksN)

variable
  (finiteInduction : FiniteInductionPrinciple k)
  (tensorSupport : TensorSupportPrinciple k)
  (inducedSupport : InducedSupportPrinciple k)
  (restrictionSquare : RestrictionSquarePrinciple k finiteInduction)
  (marcus : SplitMarcusPrinciple k finiteInduction tensorSupport inducedSupport)
  (physical : PhysicalSource parameters normF orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
    iotaL blocksL ordinaryL familyL points field perfect source tensorSupport)
  (simpleSupported : SupportedSimplePrinciple k)

include inducedSupport restrictionSquare marcus simpleSupported

set_option linter.unusedSectionVars false in
/-- Finish the literal tensor/Morita tail for the SAME packet, affording
representation and original extension. Representative-orbit data
are not parameters of this private theorem. -/
private theorem packet_tensor_tail
    (psi : Packet iotaL blocksL
      (leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
        seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
        iotaL blocksL ordinaryL familyL))
    (W : FDRep k (L Frob.toMonoidHom chart.primalLevi))
    (irreducible : Representation.IsIrreducible W.ρ)
    (affords : psi.val.val = Representation.brauerCharacterOfRootEmbedding W.ρ iotaL)
    (rho : Representation k
      (FieldSemidirect iotaL (originalField Frob chart.primalLevi field) psi.val) W)
    (rhoRestricts : Nonempty (Representation.Equiv
      (rho.pullback (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
        FieldSemidirect iotaL (originalField Frob chart.primalLevi field) psi.val)) W.ρ)) :
    letI := physical.finite
    let aG := spinFieldAction points field.fieldPoints perfect
    let aL := originalField Frob chart.primalLevi field
    let fieldQ := fieldStabilizer iotaL aL psi.val
    let eL := leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
      iotaL blocksL ordinaryL familyL
    let eG := ambientIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r
    supported eL W ∧
    supported eG (tensorFDObj physical.M W) ∧
    Representation.IsIrreducible (tensorFDObj physical.M W).ρ ∧
    Representation.brauerCharacterOfRootEmbedding (tensorFDObj physical.M W).ρ iotaG =
      (source.jordan.character psi).val ∧
    (HonestExtensionAlong
      (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
        (L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp fieldQ.subtype] fieldQ) W ↔
     HonestExtensionAlong
      (SemidirectProduct.inl : Spin 3 F normF →*
        (Spin 3 F normF) ⋊[aG.comp fieldQ.subtype] fieldQ)
      (tensorFDObj physical.M W)) ∧
    HonestExtensionAlong
      (SemidirectProduct.inl : Spin 3 F normF →*
        (Spin 3 F normF) ⋊[aG.comp fieldQ.subtype] fieldQ)
      (tensorFDObj physical.M W) ∧
    (letI : Module.Finite k (inducedModule aG aL fieldQ physical.honest_action) :=
      inducedModule_finite finiteInduction aG aL physical.M physical.honest_action fieldQ
     ∃ maps : ∀ V : FDRep k
         ((L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp fieldQ.subtype] fieldQ),
         supported (inlImage (aL.comp fieldQ.subtype) eL) V →
           supported (inlImage (aG.comp fieldQ.subtype) eG)
             (tensorFDObj (inducedModule aG aL fieldQ physical.honest_action) V),
       (supportedTensorFDFunctor (inducedModule aG aL fieldQ physical.honest_action)
         (inlImage (aL.comp fieldQ.subtype) eL) (inlImage (aG.comp fieldQ.subtype) eG)
         maps).IsEquivalence ∧
       Nonempty
         ((tensorFDFunctor (inducedModule aG aL fieldQ physical.honest_action) ⋙
             fdRestriction (SemidirectProduct.inl : Spin 3 F normF →*
               (Spin 3 F normF) ⋊[aG.comp fieldQ.subtype] fieldQ)) ≅
           (fdRestriction (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
               (L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp fieldQ.subtype] fieldQ) ⋙
             tensorFDFunctor physical.M))) := by
  letI := physical.finite
  let aG := spinFieldAction points field.fieldPoints perfect
  let aL := originalField Frob chart.primalLevi field
  let fieldQ := fieldStabilizer iotaL aL psi.val
  let eL := leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
    iotaL blocksL ordinaryL familyL
  let eG := ambientIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r
  have tensorResult := TypeBRankThreeMoritaApplication.actual_packet_tensor_extension_iff
    parameters normF orthogonal Msys iotaG blocksG ordinaryG seriesG
    dualFrobenius dualPoints dualGeometry b r normA chart Frob iotaL blocksL ordinaryL
    familyL points field perfect source finiteInduction tensorSupport inducedSupport
    restrictionSquare marcus physical simpleSupported psi W irreducible affords
  rcases tensorResult with ⟨supportW, tensorIrreducible, tensorCharacter, tensorIff⟩
  have tensorSupportW : supported eG (tensorFDObj physical.M W) :=
    tensorSupport physical.M eG physical.left_support W
  have leviExtension : HonestExtensionAlong
      (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
        (L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp fieldQ.subtype] fieldQ) W :=
    ⟨rho, rhoRestricts⟩
  have tensorExtension := tensorIff.mp leviExtension
  have inducedResult := TypeBRankThreeMoritaApplication.actual_packet_induced_morita
    parameters normF orthogonal Msys iotaG blocksG ordinaryG seriesG
    dualFrobenius dualPoints dualGeometry b r normA chart Frob iotaL blocksL ordinaryL
    familyL points field perfect source finiteInduction tensorSupport inducedSupport
    restrictionSquare marcus physical psi
  exact ⟨supportW, tensorSupportW, tensorIrreducible, tensorCharacter, tensorIff,
    tensorExtension, inducedResult⟩

set_option linter.unusedSectionVars false in
/-- Keep the constructed representative and its same affording Levi extension,
then derive the tensor character, extension and actual induced square. -/
theorem actual_selected_morita_extension
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
    (P : Set (IBr (rootH Frob chart.primalLevi iotaL)))
    (psi0 : IBr (rootH Frob chart.primalLevi iotaL))
    (prescribedOrbit :
      letI := ambientBrauerAction (H Frob chart.primalLevi)
        (rootH Frob chart.primalLevi iotaL)
      P = MulAction.orbit (Gamma Frob chart.primalLevi) psi0)
    (initialPacket : InPacket iotaL blocksL
      (leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
        seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
        iotaL blocksL ordinaryL familyL)
      (TypeBLeviRepresentativeOriginalExtension.originalCharacter
        Frob chart.primalLevi iotaL psi0))
    (theta0 : IBr (rootN Frob chart.primalLevi iotaN))
    (occurs0 : Occurs (H Frob chart.primalLevi) (N Frob chart.primalLevi)
      (N_le_H Frob chart.primalLevi) (rootH Frob chart.primalLevi iotaL)
      (rootN Frob chart.primalLevi iotaN) psi0 theta0)
    (presentation : Presentation geometry field iotaN theta0)
    (S Q J : C → Type) [∀ c, Group (S c)] [∀ c, Finite (S c)]
    [∀ c, Group (Q c)] [∀ c, Group (J c)]
    (standard : StandardData presentation S Q J)
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
    letI := physical.finite
    letI := ambientBrauerAction (H Frob chart.primalLevi)
      (rootH Frob chart.primalLevi iotaL)
    letI := ambientBrauerAction (N Frob chart.primalLevi)
      (rootN Frob chart.primalLevi iotaN)
    letI := originalAmbientAction Frob chart.primalLevi iotaL
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
    ∃ (theta : IBr (rootN Frob chart.primalLevi iotaN))
      (y : Gamma Frob chart.primalLevi) (psiH : IBr (rootH Frob chart.primalLevi iotaL))
      (psi : Packet iotaL blocksL eL),
      let fieldQ := fieldStabilizer iotaL aL psi.val
      psiH = y • psi0 ∧ theta = y • theta0 ∧ psiH ∈ P ∧
      Occurs (H Frob chart.primalLevi) (N Frob chart.primalLevi)
        (N_le_H Frob chart.primalLevi) (rootH Frob chart.primalLevi iotaL)
        (rootN Frob chart.primalLevi iotaN) psiH theta ∧
      CentralCharacterCovers ((N Frob chart.primalLevi).subgroupOf (H Frob chart.primalLevi))
        (catalogueH.centralCharacter
          (blockIndex (rootH Frob chart.primalLevi iotaL)
            (blocksL.alongMulEquiv (originalLEquiv Frob chart.primalLevi)) psiH))
        (catalogueN.centralCharacter
          (irreducibleBrauerCharacterBlock
            (embeddedRoot (H Frob chart.primalLevi) (N Frob chart.primalLevi)
              (N_le_H Frob chart.primalLevi) (rootN Frob chart.primalLevi iotaN))
            (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
              (embeddedRoot (H Frob chart.primalLevi) (N Frob chart.primalLevi)
                (N_le_H Frob chart.primalLevi) (rootN Frob chart.primalLevi iotaN)))
            blocksN (embeddedCharacter (H Frob chart.primalLevi) (N Frob chart.primalLevi)
              (N_le_H Frob chart.primalLevi) (rootN Frob chart.primalLevi iotaN) theta))) ∧
      characterEquiv Frob chart.primalLevi iotaL psi.val = psiH ∧
      psi.val = TypeBLeviRepresentativeOriginalExtension.originalCharacter
        Frob chart.primalLevi iotaL psiH ∧
      Formalisation.SemidirectStabilizerFactors
        (cliffordFieldAction points field.fieldPoints)
        (clifford_semidirect_compatible points field.fieldPoints perfect iotaG)
        (source.jordan.character psi) ∧
      MulAction.stabilizer E (source.jordan.character psi) = MulAction.stabilizer E psi.val ∧
      InPacket iotaG blocksG eG (source.jordan.character psi) ∧
      supportingBlock iotaG blocksG (source.jordan.character psi) =
        (source.jordan.block ⟨supportingBlock iotaL blocksL psi.val, psi.property⟩).val ∧
      ∃ W : FDRep k (L Frob.toMonoidHom chart.primalLevi),
        Representation.IsIrreducible W.ρ ∧
        psi.val.val = Representation.brauerCharacterOfRootEmbedding W.ρ iotaL ∧
        ∃ rho : Representation k
          (FieldSemidirect iotaL aL psi.val) W,
          Representation.IsIrreducible rho ∧
          Nonempty (Representation.Equiv
            (rho.pullback (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
              FieldSemidirect iotaL aL psi.val)) W.ρ) ∧
          supported eL W ∧
          supported eG (tensorFDObj physical.M W) ∧
          Representation.IsIrreducible (tensorFDObj physical.M W).ρ ∧
          Representation.brauerCharacterOfRootEmbedding (tensorFDObj physical.M W).ρ iotaG =
            (source.jordan.character psi).val ∧
          (HonestExtensionAlong
            (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
              (L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp fieldQ.subtype] fieldQ) W ↔
           HonestExtensionAlong
            (SemidirectProduct.inl : Spin 3 F normF →*
              (Spin 3 F normF) ⋊[aG.comp fieldQ.subtype] fieldQ)
            (tensorFDObj physical.M W)) ∧
          HonestExtensionAlong
            (SemidirectProduct.inl : Spin 3 F normF →*
              (Spin 3 F normF) ⋊[aG.comp fieldQ.subtype] fieldQ)
            (tensorFDObj physical.M W) ∧
          (letI : Module.Finite k (inducedModule aG aL fieldQ physical.honest_action) :=
            inducedModule_finite finiteInduction aG aL physical.M physical.honest_action fieldQ
           ∃ maps : ∀ V : FDRep k
               ((L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp fieldQ.subtype] fieldQ),
               supported (inlImage (aL.comp fieldQ.subtype) eL) V →
                 supported (inlImage (aG.comp fieldQ.subtype) eG)
                   (tensorFDObj (inducedModule aG aL fieldQ physical.honest_action) V),
             (supportedTensorFDFunctor (inducedModule aG aL fieldQ physical.honest_action)
               (inlImage (aL.comp fieldQ.subtype) eL) (inlImage (aG.comp fieldQ.subtype) eG)
               maps).IsEquivalence ∧
             Nonempty
               ((tensorFDFunctor (inducedModule aG aL fieldQ physical.honest_action) ⋙
                   fdRestriction (SemidirectProduct.inl : Spin 3 F normF →*
                     (Spin 3 F normF) ⋊[aG.comp fieldQ.subtype] fieldQ)) ≅
                 (fdRestriction (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
                     (L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp fieldQ.subtype] fieldQ) ⋙
                   tensorFDFunctor physical.M))) := by
  letI := physical.finite
  letI := ambientBrauerAction (H Frob chart.primalLevi)
    (rootH Frob chart.primalLevi iotaL)
  letI := ambientBrauerAction (N Frob chart.primalLevi)
    (rootN Frob chart.primalLevi iotaN)
  letI := originalAmbientAction Frob chart.primalLevi iotaL
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
  have selected := TypeBRankThreeJordanRepresentativeApplication.actual_representative_jordan
    parameters normF orthogonal Msys iotaG blocksG ordinaryG seriesG
    dualFrobenius dualPoints dualGeometry b r normA chart Frob iotaL blocksL ordinaryL
    familyL points field perfect source geometry iotaN iotaGamma blocksN catalogueH catalogueN
    decomposition intersection lang roots_N_H fieldScope covering P psi0 prescribedOrbit
    initialPacket theta0 occurs0 presentation S Q J standard iotaI iotaA roots_N_G
    roots_A_G roots_N_A roots_I_A multiplicityFree above homogeneousClifford
    source87 source89 source820 source812
  rcases selected with ⟨theta, selectedTheta⟩
  rcases selectedTheta with ⟨y, selectedY⟩
  rcases selectedY with ⟨psiH, selectedH⟩
  rcases selectedH with ⟨psi, selectedPsi⟩
  rcases selectedPsi with ⟨hpsi, htheta, hinP, hoccurs, hcovers, hcopy,
    horiginal, hfactor, hfixer, hpacket, hblock, extension⟩
  let fieldQ := fieldStabilizer iotaL aL psi.val
  refine ⟨theta, y, psiH, psi, hpsi, htheta, hinP, hoccurs, hcovers, hcopy,
    horiginal, hfactor, hfixer, hpacket, hblock, ?_⟩
  rcases extension with ⟨W, irreducible, affords, extensionW⟩
  rcases extensionW with ⟨rho, rhoIrreducible, rhoRestricts⟩
  refine ⟨W, irreducible, affords, rho, rhoIrreducible, rhoRestricts, ?_⟩
  exact packet_tensor_tail
    (parameters := parameters) (normF := normF) (orthogonal := orthogonal)
    (Msys := Msys) (iotaG := iotaG) (blocksG := blocksG) (ordinaryG := ordinaryG)
    (seriesG := seriesG) (dualFrobenius := dualFrobenius) (dualPoints := dualPoints)
    (dualGeometry := dualGeometry) (b := b) (r := r) (normA := normA) (chart := chart)
    (Frob := Frob) (iotaL := iotaL) (blocksL := blocksL) (ordinaryL := ordinaryL)
    (familyL := familyL) (points := points) (field := field) (perfect := perfect)
    (source := source) (finiteInduction := finiteInduction) (tensorSupport := tensorSupport)
    (inducedSupport := inducedSupport) (restrictionSquare := restrictionSquare)
    (marcus := marcus) (physical := physical) (simpleSupported := simpleSupported)
    psi W irreducible affords rho rhoRestricts

end ModularRep.PaperProofs.TypeBRankThreeMoritaSelectedApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
