import ModularRep.PaperProofs.TypeBCurrentStrictRouting
import ModularRep.PaperProofs.TypeBCurrentBrauerTransport
import ModularRep.PaperProofs.TypeBMatrixOmegaPrimeToTwoCover
import ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource
import ModularRep.PaperProofs.CurrentFiniteSplittingAssembly
import ModularRep.PaperProofs.TypeBModularGroupRootBinding

/-!
# The current type B application of Jordan reduction

Spin is the full universal covering group in this application. It is not
the universal prime-to-two cover. The latter is constructed on the actual
matrix Omega group from the former's central kernel of order two.

The composite E2 boundary combines Feng--Li--Zhang Theorem 5.7 with the
choice of its groups inside the full field group, restriction of the
stabilizer and extension property, the central O2 quotient, and Spath
Theorem 4.4. It takes the full-field and complete strict-block hypotheses,
then returns witnesses on the actual primitive Omega blocks. Both lower
hypotheses are constructed before this source is applied.

K chooses the dominating blocks through their actual group algebra images
and combines the complete family using the published Koshitani--Spath
passage. That passage may choose fresh compatible maps and packets.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCurrentLocalizedReduction

open ModularRep FDRepSimpleClassKZero CharacterWeight
open TypeBCliffordCarriers TypeBFixedRootDefinitionFamily TypeBFullBlockCondition
open CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldFLZFullHG EvenFieldFLZ318FixedTheoremGate
open TypeBCliffordOrthogonalSourceBinding

/-- Total source interpretation on the same relative class. Each finite
group uses a splitting ordinary field. No algebraic closure of a discrete
valuation field is required. The relation is authenticated for every
character, selected raw weight and compatible own-normaliser reduction. -/
structure FullHGInterpretation {p : ℕ} (scope : FLZFullHGUniverse p 2)
    (coverage : FullHGDefinition35Coverage scope)
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage) where
  strictModel : ∀ pair : FullHG scope,
    EvenFieldFLZ57CentrelessGate.SourceStrictBlockModel
      (coverage.presentation pair).family.Block
  strict_iff : ∀ (pair : FullHG scope) (b : (coverage.presentation pair).family.Block),
    (strictModel pair).IsStrict b ↔ strictSource.predicate pair b
  ordinaryRoots : ∀ pair : FullHG scope,
    HasEnoughRootsOfUnity (coverage.presentation pair).family.K
      (Nat.card (coverage.presentation pair).family.H)
  ambient_idempotent : ∀ (pair : FullHG scope)
      (b : (coverage.presentation pair).family.Block),
    (coverage.presentation pair).family.blockSource.operations.ambientBlockData.blockIdempotent b =
      (coverage.presentation pair).family.blockIdempotent b
  physical : ∀ pair : FullHG scope,
    GuardedBlockCompatibility (coverage.presentation pair).family.iota
      (coverage.presentation pair).family.blockSource.operations
  standard : ∀ pair : FullHG scope,
    OddTwoCentralTwoRelationInflation.BlockTripleSourceSemantics 2
      (coverage.presentation pair).family.k (coverage.presentation pair).family.K
  coherentReduction : ∀ (pair : FullHG scope)
      (b : (coverage.presentation pair).family.Block)
      (w : Definition35Weight ((coverage.presentation pair).family.problem b)),
    ∃ R : OddTwoActualStabilizerTriple.OwnNormalizerReduction
        (k := (coverage.presentation pair).family.k)
        (OddTwoFLZ57LiteralMapSource.relativeOwnWeight (coverage.presentation pair).family b w),
      OddTwoFLZ57LiteralMapSource.RelativeRootsCompatible
        (coverage.presentation pair).family b w R
  definition35_iff : ∀ (pair : FullHG scope)
      (b : (coverage.presentation pair).family.Block)
      (psi : Definition35Brauer ((coverage.presentation pair).family.problem b))
      (w : Definition35Weight ((coverage.presentation pair).family.problem b))
      (R : OddTwoActualStabilizerTriple.OwnNormalizerReduction
        (k := (coverage.presentation pair).family.k)
        (OddTwoFLZ57LiteralMapSource.relativeOwnWeight (coverage.presentation pair).family b w)),
    OddTwoFLZ57LiteralMapSource.RelativeRootsCompatible
      (coverage.presentation pair).family b w R →
    ((blockSource.source pair b).definition35BlockIsomorphic psi w ↔
      (OddTwoActualStabilizerTriple.rawStabilizer
        ((coverage.presentation pair).family.automorphisms b).gamma
        (OddTwoFLZ57LiteralMapSource.relativeOwnWeight (coverage.presentation pair).family b w) ≤
      OddTwoActualStabilizerTriple.globalStabilizer (coverage.presentation pair).family.iota
        ((coverage.presentation pair).family.automorphisms b).gamma psi.1) ∧
      (standard pair).blockIsomorphic
        (OddTwoFLZ57LiteralMapSource.relativeArguments (coverage.presentation pair).family b psi w R))

variable {n p f : ℕ} {F k K O : Type}
  [Field F] [Finite F] [CharP F p]
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [CommRing O] [IsDomain O] [Algebra O K]
  [Finite (SpecialClifford n F)] [NeZero f]
  (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
  (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)


local instance spinFintype : Fintype (Spin n F N) := Fintype.ofFinite _
local instance omegaFintype : Fintype (TypeBOrthogonalOmegaCarriers.Omega n F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (Spin n F N))] [Fintype (LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F))]
  (Msys : ModularSystem 2 K O k)
  (iotaG : PrimeRegularRootEmbedding 2 k K (Spin n F N))
  (iotaS : PrimeRegularRootEmbedding 2 k K (TypeBOrthogonalOmegaCarriers.Omega n F))
  (blocksG : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k (Spin n F N) => b.val))
  (blocksS : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F) => b.val))
  (localG : CurrentFiniteSplittingFamily.PrimitivePhysicalSource iotaG)
  (localS : CurrentFiniteSplittingFamily.PrimitivePhysicalSource iotaS)


variable (scope : FLZFullHGUniverse p 2)
  (coverage : FullHGDefinition35Coverage scope)

/-- E1/U coordinates for the one ambient algebraic pair. The finite group
presentation is literally the primitive Spin family above. Scalar and vector
equations identify the algebraic Frobenius with the prescribed field-power map. -/
structure AmbientBinding where
  family_eq : (coverage.presentation scope.ambientPair).family = (CurrentFiniteSplittingFamily.primitiveFamily (p := 2) (k := k) (K := K) (G := Spin n F N) iotaG (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG) blocksG Nat.prime_two localG)
  Closure : Type
  [fieldClosure : Field Closure]
  [algClosedClosure : IsAlgClosed Closure]
  [charClosure : CharP Closure p]
  fieldEmbedding : F →+* Closure
  algebraicNorm : NormSource n Closure
  algebraicEquiv : scope.ambient.algebraicPair.AlgebraicGroup ≃*
    Spin n Closure algebraicNorm
  algebraicFrobenius : Clifford n Closure →+* Clifford n Closure
  frobenius_scalar : ∀ a : Closure,
    algebraicFrobenius (algebraMap Closure (Clifford n Closure) a) =
      algebraMap Closure (Clifford n Closure) (a ^ (p ^ f))
  frobenius_vector : ∀ v : Vector n Closure,
    algebraicFrobenius (CliffordAlgebra.ι (splitForm n Closure) v) =
      CliffordAlgebra.ι (splitForm n Closure) (fun i => v i ^ (p ^ f))
  frobenius_spin : ∀ x,
    toClifford n Closure (algebraicEquiv (scope.ambient.algebraicPair.steinberg x)).val =
      algebraicFrobenius (toClifford n Closure (algebraicEquiv x).val)
  baseChange : Clifford n F →+* Clifford n Closure
  baseChange_scalar : ∀ a : F,
    baseChange (algebraMap F (Clifford n F) a) =
      algebraMap Closure (Clifford n Closure) (fieldEmbedding a)
  baseChange_vector : ∀ v : Vector n F,
    baseChange (CliffordAlgebra.ι (splitForm n F) v) =
      CliffordAlgebra.ι (splitForm n Closure) (fun i => fieldEmbedding (v i))
  fixedPoint_coordinates : ∀ g : (Spin n F N),
    toClifford n Closure (algebraicEquiv
      ((coverage.presentation scope.ambientPair).fixedPointEquiv
        ((OddTwoFLZ57LiteralMapSource.familyGroupEquivOfEq family_eq).symm g)).val).val =
      baseChange (toClifford n F g.val)

attribute [instance] AmbientBinding.fieldClosure AmbientBinding.algClosedClosure
  AmbientBinding.charClosure

/-- The actual primitive block image under the constructed central quotient.
This is the standard central two-subgroup block correspondence, with no
character bijection, stabiliser or inductive-condition conclusion. -/
structure DominationSource : Prop where
  dominating : ∀ b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F),
    ∃ a : LiteralPrimitiveBlock k (Spin n F N), MonoidAlgebra.mapDomain (spinProjection n F parameters rank N C) a.val = b.val

variable (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
  (fullCover : IsUniversalCentralExtension (spinProjection n F parameters rank N C))
  (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)) (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F))

def actualCover
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (fullCover : IsUniversalCentralExtension (spinProjection n F parameters rank N C))
    (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)) (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F)) :
    EllPrimeCoverSource 2 (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  TypeBMatrixOmegaPrimeToTwoCover.identityEllPrimeCover n F parameters rank N C
    centre fullCover simple nonabelian

@[simp] theorem actualCover_quotient :
    (actualCover parameters rank N C centre fullCover simple nonabelian).quotient =
      MonoidHom.id (TypeBOrthogonalOmegaCarriers.Omega n F) := rfl

variable (fs : FieldActionSource n F p f parameters N)
  (blockSource : FullHGBlockSource coverage)
  (strictSource : FullHGStrictQuasiIsolationAdapter coverage)

/-- E2 composite of Jordan reduction, choice of the per-label groups inside
the field group, restriction to them, and the central-core block passage.
The original and quotient roots use the same modular system. Each block's
primitive idempotent is the actual image of the chosen upstairs block.

The quantifier is over every such block and retains all hypotheses of the
published reduction. It is not a source assertion of Proposition 4.13 or
an all-type-B inductive-condition theorem. The output fixes actual roots,
weights, central quotients, extensions and complete local conditions. -/
structure FLZ57DeflatedBlockSource : Prop where
  applyTheorem57 :
    (n, Nat.card F) ≠ (3, 3) →
    AmbientBinding (f := f) N iotaG blocksG localG scope coverage →
    FullHGInterpretation scope coverage blockSource strictSource →
    iotaG = TypeBModularGroupRootBinding.groupRoot Msys (Spin n F N) →
    iotaS = TypeBModularGroupRootBinding.groupRoot Msys (TypeBOrthogonalOmegaCarriers.Omega n F) →
    SpathCoefficientField 2 k Nat.prime_two →
    TypeBCurrentBrauerTransport.BrauerHypothesis fs iotaG →
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource →
    ∀ (a : LiteralPrimitiveBlock k (Spin n F N)) (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F)),
      MonoidAlgebra.mapDomain (spinProjection n F parameters rank N C) a.val = b.val →
      Nonempty (BlockWitness (CurrentFiniteSplittingFamily.primitiveFamily (p := 2) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F) iotaS (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaS) blocksS Nat.prime_two localS)
        (actualCover parameters rank N C centre fullCover simple nonabelian) b)

/-- Apply Jordan reduction to the already established strict-block and
Brauer hypotheses, selecting the actual dominating block internally. -/
theorem blocks_of_hypotheses
    (exception : (n, Nat.card F) ≠ (3, 3))
    (binding : AmbientBinding (f := f) N iotaG blocksG localG scope coverage)
    (interpretation : FullHGInterpretation scope coverage blockSource strictSource)
    (rootG : iotaG = TypeBModularGroupRootBinding.groupRoot Msys (Spin n F N))
    (rootS : iotaS = TypeBModularGroupRootBinding.groupRoot Msys (TypeBOrthogonalOmegaCarriers.Omega n F))
    (coefficient : SpathCoefficientField 2 k Nat.prime_two)
    (domination : DominationSource (k := k) parameters rank N C)
    (cited : FLZ57DeflatedBlockSource parameters rank N C Msys iotaG iotaS
      blocksG blocksS localG localS scope coverage centre fullCover simple nonabelian
      fs blockSource strictSource)
    (assumption53 : TypeBCurrentBrauerTransport.BrauerHypothesis fs iotaG)
    (strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource) :
    ∀ b, Nonempty (BlockWitness (CurrentFiniteSplittingFamily.primitiveFamily (p := 2) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F) iotaS (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaS) blocksS Nat.prime_two localS)
      (actualCover parameters rank N C centre fullCover simple nonabelian) b) := by
  intro b
  obtain ⟨a, ha⟩ := domination.dominating b
  exact cited.applyTheorem57 exception binding interpretation rootG rootS coefficient
    assumption53 strictBlocks a b ha

/-- The published block-family construction applies to the complete block
witnesses just constructed, using the same primitive family and cover. -/
theorem full_family_of_hypotheses
    (exception : (n, Nat.card F) ≠ (3, 3))
    (binding : AmbientBinding (f := f) N iotaG blocksG localG scope coverage)
    (interpretation : FullHGInterpretation scope coverage blockSource strictSource)
    (rootG : iotaG = TypeBModularGroupRootBinding.groupRoot Msys (Spin n F N))
    (rootS : iotaS = TypeBModularGroupRootBinding.groupRoot Msys (TypeBOrthogonalOmegaCarriers.Omega n F))
    (coefficient : SpathCoefficientField 2 k Nat.prime_two)
    (domination : DominationSource (k := k) parameters rank N C)
    (cited : FLZ57DeflatedBlockSource parameters rank N C Msys iotaG iotaS
      blocksG blocksS localG localS scope coverage centre fullCover simple nonabelian
      fs blockSource strictSource)
    (assembly : CurrentFiniteSplittingAssembly.Source)
    (assumption53 : TypeBCurrentBrauerTransport.BrauerHypothesis fs iotaG)
    (strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource) :
    Nonempty (FamilyWitness (CurrentFiniteSplittingFamily.primitiveFamily (p := 2) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F) iotaS (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaS) blocksS Nat.prime_two localS)
      (actualCover parameters rank N C centre fullCover simple nonabelian)) := by
  letI : Algebra O (CurrentFiniteSplittingFamily.primitiveFamily
      (p := 2) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F)
      iotaS (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaS)
      blocksS Nat.prime_two localS).K := inferInstanceAs (Algebra O K)
  apply CurrentFiniteSplittingAssembly.fullFamily (CurrentFiniteSplittingFamily.primitiveFamily (p := 2) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F) iotaS (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaS) blocksS Nat.prime_two localS)
    (actualCover parameters rank N C centre fullCover simple nonabelian) Msys assembly
    localS.ordinaryRoots rootS coefficient localS.idempotent localS.blockCompatibility
    localS.reduction_roots
  exact blocks_of_hypotheses parameters rank N C Msys iotaG iotaS blocksG blocksS
    localG localS scope coverage centre fullCover simple nonabelian fs blockSource strictSource
    exception binding interpretation rootG rootS coefficient domination cited assumption53 strictBlocks

end ModularRep.PaperProofs.TypeBCurrentLocalizedReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
