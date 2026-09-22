import ModularRep.PaperProofs.TypeBCurrentLocalizedReduction
import ModularRep.PaperProofs.TypeBCurrentBrauerHypothesis
import ModularRep.PaperProofs.TypeBCurrentStrictAssembly

/-!
# The current generic type B prime-two source application

This package contains the subordinate geometric, representation theoretic
and published source data. The Brauer hypothesis and the complete strict
relative-block family are constructed by their separate Lean proofs before
the localized reduction is applied. Neither hypothesis is an input field.

The final family is on actual matrix Omega, with its constructed identity
prime-to-two cover. The exceptional pair (3,3) is excluded only here; the
relative principal construction still includes every exceptional child.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCurrentTwoInputs

open ModularRep CharacterWeight TypeBCliffordCarriers
open CyclicOuterLemma37LiteralLocalExtension EvenFieldFLZSourceConditions
open EvenFieldFLZDefinition35Family EvenFieldFLZFullHG EvenFieldFLZ318FixedTheoremGate
open TypeBCliffordOrthogonalSourceBinding TypeBFullBlockCondition
open TypeBCurrentLocalizedReduction TypeBCurrentStrictRouting
open TypeBCurrentPrincipalResults TypeBCurrentBrauerTransport

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  [Finite (SpecialClifford n F)] [NeZero f]
  (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
  (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)

local instance spinFintype : Fintype (Spin n F N) := Fintype.ofFinite _
local instance omegaFintype : Fintype (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  Fintype.ofFinite _

-- The application uses fields and projections of this dependent data carrier,
-- not its generated constructor-injectivity or size-specification lemmas.
set_option genInjectivity false
set_option genSizeOfSpec false

/-- Source inputs for the complete current generic argument. Every
coefficient field, primitive block and relative pair retains its actual
carrier. Ordinary fields use finite splitting throughout this branch. -/
structure Inputs where
  k : Type
  K : Type
  O : Type
  [fieldk : Field k]
  [fieldK : Field K]
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraO : Algebra O K]
  [chark : CharP k 2]
  [closedk : IsAlgClosed k]
  [zeroK : CharZero K]
  [rootsUpper : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [rootsLower : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [finiteIrr : Finite (OrdinaryIrreducibleCharacter.Irr K (Spin n F N))]
  [finiteBlocksG : Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  [finiteBlocksS : Fintype (LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F))]
  Msys : ModularSystem 2 K O k
  iotaG : PrimeRegularRootEmbedding 2 k K (Spin n F N)
  iotaS : PrimeRegularRootEmbedding 2 k K (TypeBOrthogonalOmegaCarriers.Omega n F)
  rootG : iotaG = TypeBModularGroupRootBinding.groupRoot Msys (Spin n F N)
  rootS : iotaS = TypeBModularGroupRootBinding.groupRoot Msys (TypeBOrthogonalOmegaCarriers.Omega n F)
  coefficient : SpathCoefficientField 2 k Nat.prime_two
  principalBlock : LiteralPrimitiveBlock k (Spin n F N)
  gggr : GGGRContext parameters rank Msys iotaG principalBlock
  principalRaw : RankSources gggr
  fs : FieldActionSource n F p f parameters N
  principalField : FieldSources gggr fs
  cyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k
  parametersG : ParameterSource fs (k := k)
  A : Type
  [fieldA : Field A]
  [algebraA : Algebra F A]
  normA : NormSource n A
  Frob : MulAut (SpecialClifford n A)
  [finitePoints : Finite (TypeBRegularLeviRationalCarriers.fixedPoints Frob.toMonoidHom)]
  points : TypeBRegularLeviRationalCarriers.CliffordFixedPointSource n p f F A N normA Frob
  levis : ∀ b : LiteralPrimitiveBlock k (Spin n F N),
    ¬ TypeBCentralKernelBlockSource.IsPrincipal b →
      Nonempty (TypeBCurrentBrauerHypothesis.LeviSource fs iotaG gggr.blocks
        parametersG Frob points (parametersG.blockParameter b))
  localG : CurrentFiniteSplittingFamily.PrimitivePhysicalSource iotaG
  blocksS : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F) => b.val)
  localS : CurrentFiniteSplittingFamily.PrimitivePhysicalSource iotaS
  scope : FLZFullHGUniverse p 2
  coverage : FullHGDefinition35Coverage scope
  binding : AmbientBinding (f := f) N iotaG gggr.blocks localG scope coverage
  blockSource : FullHGBlockSource coverage
  strictSource : FullHGStrictQuasiIsolationAdapter coverage
  routing : FullHGRouting coverage strictSource
  strictInputs : TypeBCurrentStrictAssembly.StrictSources routing blockSource
  interpretation : FullHGInterpretation scope coverage blockSource strictSource
  centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N
  fullCover : IsUniversalCentralExtension (spinProjection n F parameters rank N C)
  simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)
  nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F)
  domination : DominationSource (k := k) parameters rank N C
  published : FLZ57DeflatedBlockSource parameters rank N C Msys iotaG iotaS
    gggr.blocks blocksS localG localS scope coverage centre fullCover simple nonabelian
    fs blockSource strictSource
  assembly : CurrentFiniteSplittingAssembly.Source

set_option genSizeOfSpec true
set_option genInjectivity true

attribute [instance] Inputs.fieldk Inputs.fieldK Inputs.ringO Inputs.domainO Inputs.algebraO
  Inputs.chark Inputs.closedk Inputs.zeroK Inputs.rootsUpper Inputs.rootsLower
  Inputs.finiteIrr Inputs.finiteBlocksG Inputs.finiteBlocksS Inputs.fieldA Inputs.algebraA
  Inputs.finitePoints

namespace Inputs

variable {parameters rank N C}

/-- The actual primitive matrix-Omega family determined by specified inputs. -/
def family (inputs : Inputs parameters rank N C) : Definition35Family 2 :=
  CurrentFiniteSplittingFamily.primitiveFamily inputs.iotaS
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding inputs.iotaS)
    inputs.blocksS Nat.prime_two inputs.localS

/-- The cover is constructed from the actual Spin projection and its
central kernel, rather than nominated independently. -/
def cover (inputs : Inputs parameters rank N C) :
    EllPrimeCoverSource 2 (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  actualCover parameters rank N C inputs.centre inputs.fullCover inputs.simple inputs.nonabelian

def target (inputs : Inputs parameters rank N C) : Prop :=
  Nonempty (FamilyWitness inputs.family inputs.cover)

/-- Combine the current principal and nonprincipal Brauer arguments. -/
theorem brauerHypothesis (inputs : Inputs parameters rank N C) :
    BrauerHypothesis inputs.fs inputs.iotaG := by
  exact TypeBCurrentBrauerHypothesis.proposition_4_12 inputs.fs inputs.iotaG
    inputs.parametersG inputs.Frob inputs.points inputs.gggr inputs.principalRaw
    inputs.principalField inputs.cyclic inputs.levis

/-- Apply the localized theorem only after both of its hypotheses have
been proved from their construction inputs. -/
theorem complete (inputs : Inputs parameters rank N C)
    (exception : (n, Nat.card F) ≠ (3, 3)) : inputs.target := by
  exact full_family_of_hypotheses parameters rank N C inputs.Msys inputs.iotaG inputs.iotaS
    inputs.gggr.blocks inputs.blocksS inputs.localG inputs.localS inputs.scope inputs.coverage
    inputs.centre inputs.fullCover inputs.simple inputs.nonabelian inputs.fs
    inputs.blockSource inputs.strictSource exception inputs.binding inputs.interpretation
    inputs.rootG inputs.rootS inputs.coefficient inputs.domination inputs.published inputs.assembly
    inputs.brauerHypothesis
    (TypeBCurrentStrictAssembly.completeRelativeHypothesis55StrictBlocks
      inputs.routing inputs.blockSource inputs.strictInputs)

end Inputs
end ModularRep.PaperProofs.TypeBCurrentTwoInputs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
