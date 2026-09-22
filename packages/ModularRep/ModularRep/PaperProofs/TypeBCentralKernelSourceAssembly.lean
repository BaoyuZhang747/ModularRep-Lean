import ModularRep.PaperProofs.TypeBCentralKernelFibreAssembly
import ModularRep.PaperProofs.TypeBCentralKernelLocalBlockBinding
import ModularRep.PaperProofs.TypeBCentralKernelSpinBinding

/-!
# Source bindings for the central-kernel principal-fibre deduction

The specified normalizer compatibility is constructed from the guarded
local block laws, coherent roots, and reduction of the same ordinary
character. Neither local block matching nor an upstairs bijection is a
source input. The quotient bijection is lower-side hypothesis data of the
conditional transfer, on the displayed literal fibres.

The Spin specialization fixes the actual Clifford/field ambient group,
its embedded Spin subgroup, the image of the Spin centre, and roots
transported from the existing literal Omega quotient. It is the fibre
constituent, not the full block-triple transfer or acceptance of Lemma 2.6.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelSourceAssembly

open TypeBCentralKernelCarriers TypeBCentralKernelBrauerInflation
open TypeBCentralKernelBlockSource TypeBCentralKernelLocalReduction
open TypeBCentralKernelFibreAssembly TypeBCentralKernelLocalBlockBinding
open TypeBFixedRootDefinitionFamily

universe u

local instance finiteGroupFintype (X : Type u) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {p : ℕ} {k K H : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [IsAlgClosed K]
  [Group H] [Finite H]
  (P : Subgroup H) [P.Normal] (hP : IsPGroup p P)
  (central : P ≤ Subgroup.center H)
  (root : PrimeRegularRootEmbedding p k K (H ⧸ P))

/-- All remaining specified normalizer matching data are filled by the
checked guarded reduction deduction. The fields below are the narrow
routine source statements and actual block operations. -/
def transportData
    (kernel : Navarro232Principle p k)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
    (blocks : NavarroCentralBlockPrinciple p k)
    (reduction : Navarro318Certificate p k K)
    (SU : CharacterWeight.LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := H) (Block := LiteralPrimitiveBlock k H))
    (SD : CharacterWeight.LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := H ⧸ P)
      (Block := LiteralPrimitiveBlock k (H ⧸ P)))
    (upLiteral : ∀ b, SU.operations.ambientBlockData.blockIdempotent b = b.val)
    (downLiteral : ∀ b, SD.operations.ambientBlockData.blockIdempotent b = b.val)
    (guardU : GuardedBlockCompatibility (upRoot P hP root) SU.operations)
    (guardD : GuardedBlockCompatibility root SD.operations) :
    TransportData P hP central root where
  kernel := kernel
  regular := regular
  blocks := blocks
  up := SU
  down := SD
  upLiteral := upLiteral
  downLiteral := downLiteral
  localPhysical := localNormalizerCompatibility_canonicalRoots P hP root
    SU.operations SD.operations central blocks reduction guardU guardD

section Spin

open TypeBCliffordCarriers TypeBAutomorphismSource TypeBWeightStabilizerSource TypeBSpinCoverSource

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  {N : NormSource n F} {parameters : OddFieldParameters F r f}
  (S : FieldActionSource n F r f parameters N)
  [Finite (TypeBCentralKernelSpinBinding.A S)]

include S in
theorem finiteSpin : Finite (Spin n F N) :=
  Finite.of_injective (spinEmbedding S) (spinEmbedding_injective S)

variable [Finite (Spin n F N)]

variable {k0 K0 : Type} [Field k0] [Field K0] [CharP k0 2]
  [IsAlgClosed k0] [CharZero K0] [IsAlgClosed K0]

/-- The prescribed root is on literal Omega=Spin/Z(Spin); its transport
uses the already checked pointwise quotient equivalence. -/
def spinQuotientRoot (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N)) :
    PrimeRegularRootEmbedding 2 k0 K0
      (QuotientG (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S)) :=
  omegaRoot.alongMulEquiv (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S)

theorem spinQuotientRoot_lift (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N))
    (z : k0) : (spinQuotientRoot S omegaRoot).lift z = omegaRoot.lift z :=
  omegaRoot.alongMulEquiv_lift (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S) z

/-- The precise transport-data type for the actual Spin application. Its
prime-kernel and centrality hypotheses are filled by the checked carrier
binding and the guarded finite-centre-order source. -/
abbrev SpinTransportData
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (rank : 3 ≤ n) (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N)) :=
  TransportData
    (kernelInG (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S))
    (TypeBCentralKernelSpinBinding.kernel_isTwoGroup S centre rank)
    (TypeBCentralKernelSpinBinding.kernel_central S) (spinQuotientRoot S omegaRoot)

/-- Partial application of the checked source constructor to the actual
Spin kernel, centre-order proof and Omega root. The remaining arguments
are exactly the displayed routine sources and specified block packages. -/
def spinTransportData
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (rank : 3 ≤ n) (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N)) :=
  transportData
    (kernelInG (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S))
    (TypeBCentralKernelSpinBinding.kernel_isTwoGroup S centre rank)
    (TypeBCentralKernelSpinBinding.kernel_central S) (spinQuotientRoot S omegaRoot)

end Spin

end ModularRep.PaperProofs.TypeBCentralKernelSourceAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
