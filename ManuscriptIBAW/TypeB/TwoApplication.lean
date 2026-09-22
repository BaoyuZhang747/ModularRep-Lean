import ManuscriptIBAW.TypeB.LeviApplication
import ManuscriptIBAW.TypeB.JordanStrictApplication

/-!
# The Type B application at the prime two

The principal and nonprincipal Brauer representatives and the complete
strict block hypothesis are constructed before Jordan reduction. The
geometry for each label uses the same primitive Spin blocks, rational PCSp
parameters and strict labels. The output family and its identity cover on
the actual matrix Omega group are fixed before any witness is chosen.

The ambient pair (3,3) is excluded only in the final reduction. Lower
exceptional factors remain in the principal and complete relative sources.
All finite splitting fields, modular systems and external source
interpretations remain explicit.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ManuscriptIBAW.TypeB.TwoApplication

open ModularRep ModularRep.PaperProofs
open TypeBCliffordCarriers TypeBCliffordOrthogonalSourceBinding
open CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions EvenFieldFLZFullHG
open EvenFieldFLZ318FixedTheoremGate TypeBFullBlockCondition
open TypeBCurrentBrauerTransport TypeBCurrentPrincipalResults TypeBCurrentStrictRouting
open ManuscriptIBAW.Jordan ManuscriptIBAW.Jordan.TypeBLocalized

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  [Finite (SpecialClifford n F)] [NeZero f]
  (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
  (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)

local instance twoSpinFintype : Fintype (Spin n F N) := Fintype.ofFinite _
local instance twoOmegaFintype : Fintype (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  Fintype.ofFinite _

set_option genInjectivity false
set_option genSizeOfSpec false

/-- The full Brauer hypothesis, strict block family and completed principal
application are conclusions of the construction. -/
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
  gggr : PrincipalSeries.ContextData parameters rank Msys iotaG principalBlock
  fs : FieldActionSource n F p f parameters N
  principal : PrincipalApplication.Inputs gggr fs
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
      Nonempty (LeviSources.Source fs iotaG gggr.blocks parametersG Frob points
        (parametersG.blockParameter b))
  localG : CurrentFiniteSplittingFamily.PrimitivePhysicalSource iotaG
  blocksS : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F) => b.val)
  localS : CurrentFiniteSplittingFamily.PrimitivePhysicalSource iotaS
  scope : FLZFullHGUniverse p 2
  coverage : FullHGDefinition35Coverage scope
  binding : AmbientBinding (f := f) N iotaG gggr.blocks localG scope coverage
  blockSource : FullHGBlockSource coverage
  strictSource : FullHGStrictQuasiIsolationAdapter coverage
  interpretation : FullHGInterpretation scope coverage blockSource strictSource
  routing : FullHGRouting coverage strictSource
  strictInputs : JordanStrictApplication.Sources blockSource interpretation routing
  context : GeometricContext (ell := 2) (k := k)
    (S := SemisimpleIndex (n := n) (p := p) (F := F))
    (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs)
  geometry : GeometricSelection
    (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs) context
  series : AmbientSeriesBinding parameters N iotaG gggr.blocks localG scope coverage
    fs blockSource strictSource context parametersG binding interpretation
  centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N
  fullCover : IsUniversalCentralExtension (spinProjection n F parameters rank N C)
  simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)
  nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F)
  domination : DominationSource (k := k) parameters rank N C
  published : FLZ57PerLabelDeflatedSource parameters rank N C Msys iotaG iotaS
    gggr.blocks blocksS localG localS scope coverage centre fullCover simple nonabelian
    fs blockSource strictSource context parametersG
  assembly : CurrentFiniteSplittingAssembly.Source

set_option genSizeOfSpec true
set_option genInjectivity true

attribute [instance] Inputs.fieldk Inputs.fieldK Inputs.ringO Inputs.domainO Inputs.algebraO
  Inputs.chark Inputs.closedk Inputs.zeroK Inputs.rootsUpper Inputs.rootsLower
  Inputs.finiteIrr Inputs.finiteBlocksG Inputs.finiteBlocksS Inputs.fieldA Inputs.algebraA
  Inputs.finitePoints

namespace Inputs

variable {parameters rank N C}

/-- The original primitive matrix Omega family determined by the inputs. -/
def family (inputs : Inputs parameters rank N C) : Definition35Family 2 :=
  CurrentFiniteSplittingFamily.primitiveFamily inputs.iotaS
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding inputs.iotaS)
    inputs.blocksS Nat.prime_two inputs.localS

/-- Construct the identity prime-to-two cover from the actual Spin projection
and its central kernel, using this specified covering group. -/
def cover (inputs : Inputs parameters rank N C) :
    EllPrimeCoverSource 2 (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  actualCover parameters rank N C inputs.centre inputs.fullCover inputs.simple inputs.nonabelian

def target (inputs : Inputs parameters rank N C) : Prop :=
  Nonempty (FamilyWitness inputs.family inputs.cover)

/-- Proposition 4.13. The principal source construction and every nonprincipal
Levi factor are supplied before exhausting the original orbits. -/
theorem brauerHypothesis (inputs : Inputs parameters rank N C) :
    BrauerHypothesis inputs.fs inputs.iotaG := by
  exact LeviSources.brauerHypothesis inputs.fs inputs.iotaG
    inputs.parametersG inputs.Frob inputs.points inputs.principal.context inputs.principal.raw
    inputs.principal.fieldSources inputs.cyclic inputs.levis

/-- Restrict the same representative and extension from the full field group
after choosing each geometric subgroup. This gives the first Jordan
hypothesis. -/
theorem perLabel (inputs : Inputs parameters rank N C) :
    GeneralPerLabelHypothesis
      (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F inputs.fs)
      inputs.iotaG inputs.context :=
  ManuscriptIBAW.Jordan.TypeB.generalPerLabel inputs.fs inputs.iotaG inputs.context
    inputs.geometry inputs.brauerHypothesis

/-- Lemma 4.12 and Proposition 4.14 at the nonexceptional ambient pair. Both
hypotheses are established on the specified groups before the full inductive
condition is deduced. -/
theorem complete (inputs : Inputs parameters rank N C)
    (exception : (n, Nat.card F) ≠ (3, 3)) : inputs.target := by
  exact full_family_of_hypotheses parameters rank N C inputs.Msys inputs.iotaG inputs.iotaS
    inputs.gggr.blocks inputs.blocksS inputs.localG inputs.localS inputs.scope inputs.coverage
    inputs.centre inputs.fullCover inputs.simple inputs.nonabelian inputs.fs
    inputs.blockSource inputs.strictSource inputs.context inputs.parametersG exception
    inputs.binding inputs.interpretation inputs.series inputs.rootG inputs.rootS
    inputs.coefficient inputs.domination inputs.published inputs.assembly inputs.geometry
    inputs.brauerHypothesis (inputs.strictInputs.strictBlocks inputs.blockSource inputs.interpretation)

@[simp] theorem cover_quotient (inputs : Inputs parameters rank N C) :
    inputs.cover.quotient = MonoidHom.id (TypeBOrthogonalOmegaCarriers.Omega n F) := rfl

end Inputs
end ManuscriptIBAW.TypeB.TwoApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
