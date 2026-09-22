import ModularRep.PaperProofs.TypeBRankThreeMoritaCarriers
import ModularRep.PaperProofs.TypeBRankThreeMoritaSplitApplication
import ModularRep.PaperProofs.TypeBRankThreeMoritaPhysicalSource
import ModularRep.PaperProofs.TypeBRankThreeMoritaSimpleTransport
import ModularRep.PaperProofs.TypeBRankThreeMoritaSupportedSquare

/-!
# The induced Morita construction on the actual rank-three packet

This binds the fixed Spin group, original rational Levi, computed packet
idempotents and actual field stabilizer to literal diagonal induction.
The packet theorem is an intermediate join for the selected representative
and extension-iff manuscript deduction, not a completed window.
All specified source interpretations remain explicit E1/E2/U.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaApplication

open ModularRep FDRepSimpleClassKZero
open TypeBRankThreeMoritaTensor TypeBRankThreeMoritaFiniteTensor
open TypeBRankThreeMoritaSources TypeBRankThreeMoritaDiagonal
open TypeBRankThreeMoritaInduced TypeBRankThreeMoritaSplitApplication
open TypeBRankThreeMoritaPhysicalSource TypeBRankThreeJordanPacketCarriers
open TypeBRankThreeMoritaSimpleTransport TypeBRankThreeMoritaSupportedSquare
open TypeBLeviRepresentativeField

open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBOrdinaryBlockSplitting TypeBRankThreeNonprincipalSeriesBinding
open TypeBRankThreeNonprincipalApplication TypeBRankThreeNonprincipalGeometry
open TypeBRegularLeviRationalCarriers TypeBRankThreeFactorsPointSource
open TypeBRankThreeJordanDualLabel TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeSelection TypeBRankThreeJordanOriginalTransport
open TypeBRankThreeJordanCliffordCarriers TypeBRankThreeJordanSource
open TypeBRationalSeriesSource

variable {p f : ℕ} {F A E K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field A] [IsAlgClosed A] [CharP A p] [Algebra F A]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]
  (parameters : OddFieldParameters F p f) (N : NormSource 3 F)
  (orthogonal : TypeBCliffordOrthogonalSourceBinding.Source
    3 F p f parameters (by decide) N)
  [Finite (Spin 3 F N)] [Finite (SpecialClifford 3 F)]
  (Msys : ModularSystem 2 K O k)
  (iotaG : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocksG : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F N) => c.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (ordinaryG : OrdinaryBlockSource Msys iotaG
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG) blocksG)
  (seriesG : Sources parameters Msys iotaG
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG) blocksG ordinaryG)
  (dualFrobenius : FrobeniusSource p f A)
  (dualPoints : RationalPointSource F A p f dualFrobenius)
  (dualGeometry : GeometrySource F A p f dualFrobenius dualPoints)
  (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (r : ManuscriptReduction parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b)
  (Nbar : NormSource 3 A) (chart : PairedChart Nbar r.levi)
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
  [Group E]
  (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)
  (field : FieldData Frob chart.primalLevi E)
  (perfect : commutator (Spin 3 F N) = ⊤)
  (source : Certificate parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
    iotaL blocksL ordinaryL familyL points field perfect)


variable [Finite E]
  (finiteInduction : FiniteInductionPrinciple k)
  (tensorSupport : TensorSupportPrinciple k)
  (inducedSupport : InducedSupportPrinciple k)
  (restrictionSquare : RestrictionSquarePrinciple k finiteInduction)
  (marcus : SplitMarcusPrinciple k finiteInduction tensorSupport inducedSupport)
  (physical : PhysicalSource parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
    iotaL blocksL ordinaryL familyL points field perfect source tensorSupport)

include finiteInduction inducedSupport restrictionSquare marcus

/-- The literal induced equivalence and square at the original packet character's
actual field stabilizer. The maps are support proofs for the already fixed
tensor functor, constructed using the same specified module's support. -/
theorem actual_packet_induced_morita
    (psi : Packet iotaL blocksL
      (leviIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
        seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
        iotaL blocksL ordinaryL familyL)) :
    letI := physical.finite
    let aG := spinFieldAction points field.fieldPoints perfect
    let aL := originalField Frob chart.primalLevi field
    let Q := fieldStabilizer iotaL aL psi.val
    let eL := leviIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
      iotaL blocksL ordinaryL familyL
    let eG := ambientIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r
    letI : Module.Finite k (inducedModule aG aL Q physical.honest_action) :=
      inducedModule_finite finiteInduction aG aL physical.M physical.honest_action Q
    ∃ maps : ∀ V : FDRep k ((L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp Q.subtype] Q),
        supported (inlImage (aL.comp Q.subtype) eL) V →
          supported (inlImage (aG.comp Q.subtype) eG)
            (tensorFDObj (inducedModule aG aL Q physical.honest_action) V),
      (supportedTensorFDFunctor (inducedModule aG aL Q physical.honest_action)
        (inlImage (aL.comp Q.subtype) eL) (inlImage (aG.comp Q.subtype) eG)
        maps).IsEquivalence ∧
      Nonempty
        ((tensorFDFunctor (inducedModule aG aL Q physical.honest_action) ⋙
            fdRestriction (SemidirectProduct.inl : Spin 3 F N →*
              (Spin 3 F N) ⋊[aG.comp Q.subtype] Q)) ≅
          (fdRestriction (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
              (L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp Q.subtype] Q) ⋙
            tensorFDFunctor physical.M)) := by
  letI := physical.finite
  let aG := spinFieldAction points field.fieldPoints perfect
  let aL := originalField Frob chart.primalLevi field
  let Q := fieldStabilizer iotaL aL psi.val
  let eL := leviIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
    iotaL blocksL ordinaryL familyL
  let eG := ambientIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r
  have centralG : IsMulCentral eG :=
    TypeBRankThreeJordanAmbientPacket.idempotent_central parameters Msys iotaG
      blocksG ordinaryG seriesG
      (ambientParameter parameters N orthogonal Msys iotaG blocksG ordinaryG
        seriesG dualFrobenius dualPoints dualGeometry b r)
  have idempotentG : IsIdempotentElem eG :=
    TypeBRankThreeJordanAmbientPacket.idempotent_idempotent parameters Msys iotaG
      blocksG ordinaryG seriesG
      (ambientParameter parameters N orthogonal Msys iotaG blocksG ordinaryG
        seriesG dualFrobenius dualPoints dualGeometry b r)
  have centralL : IsMulCentral eL :=
    TypeBRankThreeJordanLeviPacket.idempotent_central Msys iotaL blocksL ordinaryL
      familyL parameters.prime (two_ne_defining parameters) (rationalLabel r)
      (rationalLabel_defining_regular r)
  have idempotentL : IsIdempotentElem eL :=
    TypeBRankThreeJordanLeviPacket.idempotent_idempotent Msys iotaL blocksL ordinaryL
      familyL parameters.prime (two_ne_defining parameters) (rationalLabel r)
      (rationalLabel_defining_regular r)
  let j := originalLSpinEmbedding points chart.primalLevi chart.primalLevi_le_spin
  have jInjective : Function.Injective j :=
    originalLSpinEmbedding_injective points chart.primalLevi chart.primalLevi_le_spin
  have jEquivariant : ∀ (e : E) (l : L Frob.toMonoidHom chart.primalLevi),
      j (aL e l) = aG e (j l) :=
    TypeBRankThreeMoritaCarriers.originalLSpinEmbedding_field points chart.primalLevi
      chart.primalLevi_le_spin field perfect
  have applied := subgroup_induced_morita finiteInduction tensorSupport inducedSupport
    restrictionSquare marcus aG aL j jInjective jEquivariant eG eL centralG idempotentG
    centralL idempotentL physical.ambient_invariant source.field_invariant
    physical.M physical.honest_action physical.honest_restriction physical.left_support
    physical.right_support physical.base_morita Q
  letI : Module.Finite k (inducedModule aG aL Q physical.honest_action) :=
    inducedModule_finite finiteInduction aG aL physical.M physical.honest_action Q
  let maps : ∀ V : FDRep k ((L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp Q.subtype] Q),
      supported (inlImage (aL.comp Q.subtype) eL) V →
        supported (inlImage (aG.comp Q.subtype) eG)
          (tensorFDObj (inducedModule aG aL Q physical.honest_action) V) :=
    fun V _ => tensorSupport (inducedModule aG aL Q physical.honest_action)
      (inlImage (aG.comp Q.subtype) eG)
      (inducedModule_support inducedSupport aG aL eG eL centralG idempotentG
        centralL idempotentL physical.ambient_invariant source.field_invariant
        physical.M physical.honest_action physical.honest_restriction
        physical.left_support physical.right_support Q).1 V
  exact ⟨maps, applied.1, applied.2⟩

/-- The same packet simple and its literal tensor Jordan image extend over
the actual original Levi field stabilizer together. The Morita equivalence
and square are derived internally, not supplied as target assumptions. -/
theorem actual_packet_tensor_extension_iff
    (simpleSupported : SupportedSimplePrinciple k)
    (psi : Packet iotaL blocksL
      (leviIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
        seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
        iotaL blocksL ordinaryL familyL))
    (W : FDRep k (L Frob.toMonoidHom chart.primalLevi))
    (irreducible : Representation.IsIrreducible W.ρ)
    (affords : psi.val.val = Representation.brauerCharacterOfRootEmbedding W.ρ iotaL) :
    letI := physical.finite
    let aG := spinFieldAction points field.fieldPoints perfect
    let aL := originalField Frob chart.primalLevi field
    let Q := fieldStabilizer iotaL aL psi.val
    let eL := leviIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
      iotaL blocksL ordinaryL familyL
    supported eL W ∧
      Representation.IsIrreducible (tensorFDObj physical.M W).ρ ∧
      Representation.brauerCharacterOfRootEmbedding (tensorFDObj physical.M W).ρ iotaG =
        (source.jordan.character psi).val ∧
      (HonestExtensionAlong
        (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
          (L Frob.toMonoidHom chart.primalLevi) ⋊[aL.comp Q.subtype] Q) W ↔
       HonestExtensionAlong
        (SemidirectProduct.inl : Spin 3 F N →* (Spin 3 F N) ⋊[aG.comp Q.subtype] Q)
        (tensorFDObj physical.M W)) := by
  letI := physical.finite
  let aG := spinFieldAction points field.fieldPoints perfect
  let aL := originalField Frob chart.primalLevi field
  let Q := fieldStabilizer iotaL aL psi.val
  let eL := leviIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
    iotaL blocksL ordinaryL familyL
  let eG := ambientIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r
  have supportW : supported eL W :=
    packet_affording_supported iotaL blocksL eL psi W irreducible affords
  have tensorIrreducible : Representation.IsIrreducible (tensorFDObj physical.M W).ρ :=
    tensor_irreducible_of_base_morita simpleSupported tensorSupport physical.M eL eG
      physical.left_support physical.base_morita W supportW irreducible
  have calibrated := physical.calibration psi W irreducible affords
  letI : Module.Finite k (inducedModule aG aL Q physical.honest_action) :=
    inducedModule_finite finiteInduction aG aL physical.M physical.honest_action Q
  have applied := actual_packet_induced_morita parameters N orthogonal Msys iotaG
    blocksG ordinaryG seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
    iotaL blocksL ordinaryL familyL points field perfect source
    finiteInduction tensorSupport inducedSupport restrictionSquare marcus physical psi
  obtain ⟨maps, upperEquivalence, ⟨square⟩⟩ := applied
  have extensionIff := honestExtension_iff (aG.comp Q.subtype) (aL.comp Q.subtype)
    eG eL physical.M (inducedModule aG aL Q physical.honest_action)
    (fun V _ => tensorSupport physical.M eG physical.left_support V) maps square
    physical.base_morita upperEquivalence W supportW
  exact ⟨supportW, tensorIrreducible, calibrated, extensionIff⟩

end ModularRep.PaperProofs.TypeBRankThreeMoritaApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
