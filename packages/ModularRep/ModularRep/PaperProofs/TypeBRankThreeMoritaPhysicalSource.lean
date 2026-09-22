import ModularRep.PaperProofs.TypeBRankThreeMoritaSources
import ModularRep.PaperProofs.TypeBRankThreeJordanSource

/-!
# Specified inputs for the same rank-three Morita bimodule

The actual abbreviation fixes the original Spin group, original rational
Levi, both computed packet idempotents and the character map of the same
Jordan certificate. Its finite bimodule has one honest action of the
full base-pair-by-field semidirect product on the same underlying module.

The base tensor equivalence is the FLZ Theorem 4.2 input. The honest action
is the Ruhstorfer Proposition 5.7 input. The uniform character calibration
is the FLZ Section 4.3 input, for the same reduced top cohomology module.
The source coefficient realization, algebraic Frobenius and its chosen
power, parabolic and scalar-change identifications remain explicit U
authentication obligations in the accompanying input contract. They are
not established by an inhabitant of this record alone.

No induced tensor equivalence, selected field subgroup, selected-character
extension or block criterion is a field. Output simplicity is not a
calibration input.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaPhysicalSource

open ModularRep FDRepSimpleClassKZero
open TypeBRankThreeMoritaTensor TypeBRankThreeMoritaFiniteTensor
open TypeBRankThreeMoritaSources TypeBRankThreeMoritaDiagonal
open TypeBRankThreeJordanPacketCarriers

section Core

variable {k K G L E I : Type}
  [Field k] [Field K] [Group G] [Group L] [Group E]
  [Finite G] [Finite L] [Fintype I]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  {d : I → k[L]}

/-- The base Morita assertion uses the already defined supported tensor functor. -/
def BaseMorita (tensorSupport : TensorSupportPrinciple k)
    (M : Rep.{0} k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (eL : k[L]) (eG : k[G]) (leftSupport : LeftSupport M eG) : Prop :=
  (supportedTensorFDFunctor M eL eG
    (fun W _ => tensorSupport M eG leftSupport W)).IsEquivalence

/-- Uniform calibration on every affording simple module, with the literal tensor output. -/
def SameJordanCalibration
    (iotaL : PrimeRegularRootEmbedding 2 k K L)
    (iotaG : PrimeRegularRootEmbedding 2 k K G)
    (blocksL : BlockIdempotentDecomposition d) (eL : k[L])
    (character : Packet iotaL blocksL eL → IBr iotaG)
    (M : Rep.{0} k (G × Lᵐᵒᵖ)) [Module.Finite k M] : Prop :=
  ∀ (psi : Packet iotaL blocksL eL) (W : FDRep k L),
    Representation.IsIrreducible W.ρ →
    psi.val.val = Representation.brauerCharacterOfRootEmbedding W.ρ iotaL →
    Representation.brauerCharacterOfRootEmbedding (tensorFDObj M W).ρ iotaG =
      (character psi).val

/-- The specified E2 data, with one module and one genuine simultaneous action. -/
structure Core
    (iotaL : PrimeRegularRootEmbedding 2 k K L)
    (iotaG : PrimeRegularRootEmbedding 2 k K G)
    (blocksL : BlockIdempotentDecomposition d) (eL : k[L]) (eG : k[G])
    (aG : E →* MulAut G) (aL : E →* MulAut L)
    (character : Packet iotaL blocksL eL → IBr iotaG)
    (tensorSupport : TensorSupportPrinciple k) where
  M : Rep.{0} k (G × Lᵐᵒᵖ)
  finite : Module.Finite k M
  left_support : LeftSupport M eG
  right_support : RightSupport M eL
  base_morita :
    letI := finite
    BaseMorita tensorSupport M eL eG left_support
  honest_action : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) M
  honest_restriction :
    honest_action.comp
      (SemidirectProduct.inl :
        G × Lᵐᵒᵖ →* (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) = M.ρ
  ambient_invariant : ∀ a : E, MonoidAlgebra.mapDomainRingEquiv k (aG a) eG = eG
  calibration :
    letI := finite
    SameJordanCalibration iotaL iotaG blocksL eL character M

end Core

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

/-- The actual specified source has no independently selected group, label,
packet idempotent, actor or Jordan character map. -/
abbrev PhysicalSource (tensorSupport : TensorSupportPrinciple k) :=
  let eL := leviIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
    iotaL blocksL ordinaryL familyL
  let eG := ambientIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r
  Core iotaL iotaG blocksL eL eG
    (spinFieldAction points field.fieldPoints perfect)
    (originalField Frob chart.primalLevi field)
    source.jordan.character tensorSupport

end ModularRep.PaperProofs.TypeBRankThreeMoritaPhysicalSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
