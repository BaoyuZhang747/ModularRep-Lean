import ModularRep.PaperProofs.TypeBCentralKernelTripleCharacters
import ModularRep.PaperProofs.TypeBCentralKernelTripleProjection
import ModularRep.PaperProofs.TypeBCentralKernelLocalBlockBinding

/-!
# The two literal character inflation equations for the inertia triple

Both quotient characters live on the canonical image subgroups in T/P.
The ordinary local characters are related by the checked weight descent.
Their Brauer reductions are constructed from Navarro 3.18 at the displayed
coherent roots. Projection squares then yield the two character equations
required by the one-way MRR certificate. Neither equation is a source input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelTripleInflation

open ModularRep CharacterWeight TypeBCentralKernelCarriers
open TypeBCentralKernelInertia TypeBCentralKernelBrauerInflation
open TypeBCentralKernelTripleCarriers TypeBCentralKernelTripleCertificate
open TypeBCentralKernelTripleProjection TypeBCentralKernelTripleCharacters
open TypeBCentralKernelLocalReduction TypeBCentralKernelLocalBlockBinding

universe u

variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Finite A]

variable (P G : Subgroup A) [P.Normal] [G.Normal]
variable (hP : IsPGroup p (kernelInG G P))
variable (iotaDown : PrimeRegularRootEmbedding p k K (QuotientG G P))
variable (kernel : Navarro232Principle p k)
variable (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
variable (thetaBar : IBr iotaDown)

abbrev originalRoot := upRoot (kernelInG G P) hP iotaDown

def originalTheta : IBr (originalRoot P G hP iotaDown) :=
  brauerEquiv (kernelInG G P) hP iotaDown kernel regular thetaBar

abbrev originalInertia :=
  T G (originalRoot P G hP iotaDown) (originalTheta P G hP iotaDown kernel regular thetaBar)

local notation "iU" => originalRoot P G hP iotaDown
local notation "thetaU" => originalTheta P G hP iotaDown kernel regular thetaBar
local notation "TI" => originalInertia P G hP iotaDown kernel regular thetaBar
local notation "hGT" => G_le_T G iU thetaU

def upBaseRoot : PrimeRegularRootEmbedding p k K (N G TI) :=
  baseRoot G iU thetaU

def upBaseCharacter : IBr (upBaseRoot P G hP iotaDown kernel regular thetaBar) :=
  baseBrauer G iU thetaU

def downBaseRoot : PrimeRegularRootEmbedding p k K (Nbar P G TI) :=
  iotaDown.alongMulEquiv (baseProjectionEquiv P G TI hGT).symm

def downBaseCharacter : IBr (downBaseRoot P G hP iotaDown kernel regular thetaBar) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv iotaDown
    (baseProjectionEquiv P G TI hGT).symm thetaBar

/-- The global Brauer inflation and actual base projection square give the
literal base-character equation on N -> Nbar. -/
theorem baseInflation :
    (upBaseCharacter P G hP iotaDown kernel regular thetaBar).val =
      PrimeRegularClassFunction.pullback (quotientSubgroupMap (Z P TI) (N G TI))
        (downBaseCharacter P G hP iotaDown kernel regular thetaBar).val := by
  refine brauer_inflation_transport iU iotaDown (baseEquiv G iU thetaU)
    (baseProjectionEquiv P G TI hGT).symm (qG G P)
    (quotientSubgroupMap (Z P TI) (N G TI)) ?_ thetaU thetaBar ?_
  · intro g
    apply (baseProjectionEquiv P G TI hGT).injective
    rw [MulEquiv.apply_symm_apply]
    exact baseProjectionEquiv_mk P G TI hGT g
  · exact brauerEquiv_val (kernelInG G P) hP iotaDown kernel regular thetaBar

theorem baseLifts :
    (upBaseRoot P G hP iotaDown kernel regular thetaBar).lift =
      (downBaseRoot P G hP iotaDown kernel regular thetaBar).lift := by
  ext z
  calc
    (upBaseRoot P G hP iotaDown kernel regular thetaBar).lift z =
        (originalRoot P G hP iotaDown).lift z :=
      baseRoot_lift G iU thetaU z
    _ = iotaDown.lift z :=
      PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift (kernelInG G P) hP iotaDown z
    _ = (downBaseRoot P G hP iotaDown kernel regular thetaBar).lift z :=
      (iotaDown.alongMulEquiv_lift (baseProjectionEquiv P G TI hGT).symm z).symm

variable (W : CharacterWeight p K G)

def quotientDownRoot : PrimeRegularRootEmbedding p k K
    (NormalizerQuotient (quotientWeight P G hP W).subgroup) := by
  letI : Fintype (QuotientG G P) := Fintype.ofFinite _
  exact weightQuotientRoot iotaDown (quotientWeight P G hP W)

def quotientUpRoot : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup) :=
  (quotientDownRoot P G hP iotaDown W).alongMulEquiv
    (TypeBCentralKernelWeightTransport.localEquiv (qG G P) (qG_surjective G P)
      (quotientKernelIsPGroup G P hP) W).symm

def normalizerUpRoot : PrimeRegularRootEmbedding p k K
    (Subgroup.normalizer (W.subgroup : Set G)) :=
  normalizerRoot W (quotientUpRoot P G hP iotaDown W)

def normalizerDownRoot : PrimeRegularRootEmbedding p k K
    (Subgroup.normalizer ((quotientWeight P G hP W).subgroup : Set (QuotientG G P))) :=
  normalizerRoot (quotientWeight P G hP W) (quotientDownRoot P G hP iotaDown W)

variable [IsAlgClosed K] (navarro : Navarro318Certificate p k K)

def normalizerUpCharacter : IBr (normalizerUpRoot P G hP iotaDown W) :=
  inflatedReduction W (quotientUpRoot P G hP iotaDown W)
    (quotientReduction W (quotientUpRoot P G hP iotaDown W) navarro)

def normalizerDownCharacter : IBr (normalizerDownRoot P G hP iotaDown W) :=
  inflatedReduction (quotientWeight P G hP W) (quotientDownRoot P G hP iotaDown W)
    (quotientReduction (quotientWeight P G hP W) (quotientDownRoot P G hP iotaDown W) navarro)

/-- This equation is derived from the two constructed reductions and the
same descended ordinary character, before changing any triple carrier. -/
theorem normalizerInflation :
    (normalizerUpCharacter P G hP iotaDown W navarro).val =
      PrimeRegularClassFunction.pullback (normalizerProjectionHom P G hP W)
        (normalizerDownCharacter P G hP iotaDown W navarro).val := by
  ext x
  exact normalizer_reduction_quotient_square W (qG G P) (qG_surjective G P)
    (quotientKernelIsPGroup G P hP)
    (normalizerUpRoot P G hP iotaDown W) (normalizerDownRoot P G hP iotaDown W)
    (normalizerUpCharacter P G hP iotaDown W navarro)
    (normalizerDownCharacter P G hP iotaDown W navarro)
    (inflatedReduction_value W (quotientUpRoot P G hP iotaDown W) _
      (quotientReduction_value W (quotientUpRoot P G hP iotaDown W) navarro))
    (inflatedReduction_value (quotientWeight P G hP W) (quotientDownRoot P G hP iotaDown W) _
      (quotientReduction_value (quotientWeight P G hP W)
        (quotientDownRoot P G hP iotaDown W) navarro)) x



section LocalCharacters

-- Use the direct projection-carrier equivalences to keep elaboration local.

def upLocalRoot (hUT : U G W ≤ TI) : PrimeRegularRootEmbedding p k K (M G TI W) :=
  (normalizerUpRoot P G hP iotaDown W).alongMulEquiv
    (normalizerTripleEquiv (p := p) (K := K) G TI W hUT)

def upLocalCharacter (hUT : U G W ≤ TI) : IBr (upLocalRoot P G hP iotaDown kernel regular thetaBar W hUT) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (normalizerUpRoot P G hP iotaDown W)
    (normalizerTripleEquiv (p := p) (K := K) G TI W hUT)
    (normalizerUpCharacter P G hP iotaDown W navarro)

def downLocalRoot (hPG : P ≤ G) (hUT : U G W ≤ TI) : PrimeRegularRootEmbedding p k K (Mbar P G TI W) :=
  (normalizerDownRoot P G hP iotaDown W).alongMulEquiv
    (normalizerProjectionEquiv P G TI hPG hP W hUT).symm

def downLocalCharacter (hPG : P ≤ G) (hUT : U G W ≤ TI) :
    IBr (downLocalRoot P G hP iotaDown kernel regular thetaBar W hPG hUT) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (normalizerDownRoot P G hP iotaDown W)
    (normalizerProjectionEquiv P G TI hPG hP W hUT).symm
    (normalizerDownCharacter P G hP iotaDown W navarro)

/-- The actual normalizer projection and both canonical subgroup encodings
give the literal local-character equation M -> Mbar. -/
theorem localInflation (hPG : P ≤ G) (hUT : U G W ≤ TI) :
    (upLocalCharacter P G hP iotaDown kernel regular thetaBar W navarro hUT).val =
      PrimeRegularClassFunction.pullback (quotientLocalMap (Z P TI) (N G TI) (H G TI W))
        (downLocalCharacter P G hP iotaDown kernel regular thetaBar W navarro hPG hUT).val := by
  refine brauer_inflation_transport
    (normalizerUpRoot P G hP iotaDown W) (normalizerDownRoot P G hP iotaDown W)
    (normalizerTripleEquiv (p := p) (K := K) G TI W hUT) (normalizerProjectionEquiv P G TI hPG hP W hUT).symm
    (normalizerProjectionHom P G hP W) (quotientLocalMap (Z P TI) (N G TI) (H G TI W)) ?_
    (normalizerUpCharacter P G hP iotaDown W navarro)
    (normalizerDownCharacter P G hP iotaDown W navarro) ?_
  · intro x
    apply (normalizerProjectionEquiv P G TI hPG hP W hUT).injective
    rw [MulEquiv.apply_symm_apply]
    exact normalizerProjectionEquiv_mk P G TI hPG hP W hUT x
  · exact normalizerInflation P G hP iotaDown W navarro

theorem localLifts (hPG : P ≤ G) (hUT : U G W ≤ TI) :
    (upLocalRoot P G hP iotaDown kernel regular thetaBar W hUT).lift =
      (downLocalRoot P G hP iotaDown kernel regular thetaBar W hPG hUT).lift := by
  ext z
  calc
    (upLocalRoot P G hP iotaDown kernel regular thetaBar W hUT).lift z =
        (normalizerUpRoot P G hP iotaDown W).lift z :=
      (normalizerUpRoot P G hP iotaDown W).alongMulEquiv_lift
        (normalizerTripleEquiv (p := p) (K := K) G TI W hUT) z
    _ = (quotientUpRoot P G hP iotaDown W).lift z :=
      PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift
        (normalizerKernel W) (normalizerKernel_isPGroup W)
        (quotientUpRoot P G hP iotaDown W) z
    _ = (quotientDownRoot P G hP iotaDown W).lift z :=
      (quotientDownRoot P G hP iotaDown W).alongMulEquiv_lift
        (TypeBCentralKernelWeightTransport.localEquiv (qG G P) (qG_surjective G P)
          (quotientKernelIsPGroup G P hP) W).symm z
    _ = (normalizerDownRoot P G hP iotaDown W).lift z :=
      (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift
        (normalizerKernel (quotientWeight P G hP W))
        (normalizerKernel_isPGroup (quotientWeight P G hP W))
        (quotientDownRoot P G hP iotaDown W) z).symm
    _ = (downLocalRoot P G hP iotaDown kernel regular thetaBar W hPG hUT).lift z :=
      ((normalizerDownRoot P G hP iotaDown W).alongMulEquiv_lift
        (normalizerProjectionEquiv P G TI hPG hP W hUT).symm z).symm

end LocalCharacters

end ModularRep.PaperProofs.TypeBCentralKernelTripleInflation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
