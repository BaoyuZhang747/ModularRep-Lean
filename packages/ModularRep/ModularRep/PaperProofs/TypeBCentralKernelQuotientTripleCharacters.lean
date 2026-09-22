import ModularRep.PaperProofs.TypeBCentralKernelQuotientInertiaImages
import ModularRep.PaperProofs.TypeBCentralKernelTripleInflation

/-!
# The actual characters on the native quotient-inertia triple

The base is the embedded G/P inside its actual quotient Brauer inertia.
The local base is its intersection with the actual quotient raw-weight
stabilizer. Its normalizer identification retains the literal quotient
normalizer element, as checked by the projection square.

Both characters are constructed from the same quotient Brauer character and
the same descended ordinary weight as the canonical quotient-image triple.
Their pullback equations and complete lift-function equalities are proved.
No triple witness, character matching or block identification is sourced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelQuotientTripleCharacters

open ModularRep TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelBrauerInflation TypeBCentralKernelTripleCarriers
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleProjection
open TypeBCentralKernelTripleInflation

universe u

variable {p : ℕ} {k K A : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A]
  (P G : Subgroup A) [P.Normal] [G.Normal]
  (hP : IsPGroup p (kernelInG G P))
  (root : PrimeRegularRootEmbedding p k K (QuotientG G P))
  (kernel : Navarro232Principle p k)
  (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
  (thetaBar : IBr root)

local notation "TI" => originalInertia (p := p) (k := k) (K := K) (A := A)
  P G hP root kernel regular thetaBar
local notation "QI" => TypeBCentralKernelQuotientInertiaImages.quotientInertia P G root thetaBar
local notation "NQ" => inside (embeddedQuotientG G P) QI

def nativeBaseRoot : PrimeRegularRootEmbedding p k K NQ :=
  root.alongMulEquiv
    (TypeBCentralKernelQuotientInertiaImages.quotientBaseInsideEquiv P G hP root kernel regular thetaBar)

def nativeBaseCharacter : IBr (nativeBaseRoot P G hP root kernel regular thetaBar) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv root
    (TypeBCentralKernelQuotientInertiaImages.quotientBaseInsideEquiv P G hP root kernel regular thetaBar)
    thetaBar

theorem baseLifts :
    (downBaseRoot (p := p) (k := k) (K := K) (A := A) P G hP root kernel regular thetaBar).lift =
      (nativeBaseRoot P G hP root kernel regular thetaBar).lift := by
  ext z
  exact (root.alongMulEquiv_lift (baseProjectionEquiv P G TI
    (G_le_T G (originalRoot P G hP root) (originalTheta P G hP root kernel regular thetaBar))).symm z).trans
    (root.alongMulEquiv_lift
      (TypeBCentralKernelQuotientInertiaImages.quotientBaseInsideEquiv P G hP root kernel regular thetaBar) z).symm

theorem basePullback (hPG : P ≤ G) :
    (downBaseCharacter (p := p) (k := k) (K := K) (A := A) P G hP root kernel regular thetaBar).val =
      PrimeRegularClassFunction.pullback
        (TypeBCentralKernelQuotientInertiaImages.baseImageEquiv P G hP root kernel regular thetaBar hPG).toMonoidHom
        (nativeBaseCharacter P G hP root kernel regular thetaBar).val := by
  ext x
  change thetaBar.val (PrimeRegularElement.map
      (baseProjectionEquiv P G TI
        (G_le_T G (originalRoot P G hP root) (originalTheta P G hP root kernel regular thetaBar))).toMonoidHom x) =
    thetaBar.val (PrimeRegularElement.map
      (TypeBCentralKernelQuotientInertiaImages.quotientBaseInsideEquiv P G hP root kernel regular thetaBar).symm.toMonoidHom
      (PrimeRegularElement.map
        (TypeBCentralKernelQuotientInertiaImages.baseImageEquiv P G hP root kernel regular thetaBar hPG).toMonoidHom x))
  congr 1
  apply Subtype.ext
  apply (TypeBCentralKernelQuotientInertiaImages.quotientBaseInsideEquiv P G hP root kernel regular thetaBar).injective
  exact (TypeBCentralKernelQuotientInertiaImages.base_triangle P G hP root kernel regular thetaBar hPG x.val).symm.trans
    ((TypeBCentralKernelQuotientInertiaImages.quotientBaseInsideEquiv P G hP root kernel regular thetaBar).apply_symm_apply _).symm

variable (W : CharacterWeight p K G)

local notation "HQ" => inside (TypeBCentralKernelQuotientInertiaImages.quotientRawInertia P G hP W) QI

/-- The actual descended radical normalizer is identified with the native
quotient local base through the already anchored projection maps. -/
def nativeNormalizerEquiv (hPG : P ≤ G) (hUT : U G W ≤ TI) :
    Subgroup.normalizer ((quotientWeight P G hP W).subgroup : Set (QuotientG G P)) ≃*
      localBase NQ HQ :=
  (normalizerProjectionEquiv P G TI hPG hP W hUT).symm.trans
    (TypeBCentralKernelQuotientInertiaImages.localImageEquiv P G hP root kernel regular thetaBar hPG W)

/-- The equivalence above is anchored to the actual quotient normalizer
element, not merely to an abstract isomorphism class. -/
theorem nativeNormalizerEquiv_value (hPG : P ≤ G) (hUT : U G W ≤ TI)
    (x : Subgroup.normalizer ((quotientWeight P G hP W).subgroup : Set (QuotientG G P))) :
    (nativeNormalizerEquiv P G hP root kernel regular thetaBar W hPG hUT x).val.val.val =
      quotientEmbedding G P x.val := by
  obtain ⟨y, rfl⟩ := normalizerProjectionHom_surjective P G hP W x
  have square := normalizerProjectionEquiv_mk P G TI hPG hP W hUT y
  have inverseSquare := congrArg (normalizerProjectionEquiv P G TI hPG hP W hUT).symm square
  rw [MulEquiv.symm_apply_apply] at inverseSquare
  change (TypeBCentralKernelQuotientInertiaImages.localImageEquiv P G hP root kernel regular thetaBar hPG W
    ((normalizerProjectionEquiv P G TI hPG hP W hUT).symm
      (normalizerProjectionHom P G hP W y))).val.val.val = _
  rw [← inverseSquare]
  exact TypeBCentralKernelQuotientInertiaImages.local_normalizer_projection
    P G hP root kernel regular thetaBar hPG W hUT y

def nativeLocalRoot (hPG : P ≤ G) (hUT : U G W ≤ TI) :
    PrimeRegularRootEmbedding p k K (localBase NQ HQ) :=
  (normalizerDownRoot P G hP root W).alongMulEquiv
    (nativeNormalizerEquiv P G hP root kernel regular thetaBar W hPG hUT)

theorem localLifts (hPG : P ≤ G) (hUT : U G W ≤ TI) :
    (downLocalRoot (p := p) (k := k) (K := K) (A := A)
      P G hP root kernel regular thetaBar W hPG hUT).lift =
      (nativeLocalRoot P G hP root kernel regular thetaBar W hPG hUT).lift := by
  ext z
  exact ((normalizerDownRoot P G hP root W).alongMulEquiv_lift
    (normalizerProjectionEquiv P G TI hPG hP W hUT).symm z).trans
    ((normalizerDownRoot P G hP root W).alongMulEquiv_lift
      (nativeNormalizerEquiv P G hP root kernel regular thetaBar W hPG hUT) z).symm

variable [IsAlgClosed K]

def nativeLocalCharacter (hPG : P ≤ G) (hUT : U G W ≤ TI)
    (navarro : TypeBCentralKernelLocalReduction.Navarro318Certificate p k K) :
    IBr (nativeLocalRoot P G hP root kernel regular thetaBar W hPG hUT) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (normalizerDownRoot P G hP root W)
    (nativeNormalizerEquiv P G hP root kernel regular thetaBar W hPG hUT)
    (normalizerDownCharacter P G hP root W navarro)

theorem localPullback (hPG : P ≤ G) (hUT : U G W ≤ TI)
    (navarro : TypeBCentralKernelLocalReduction.Navarro318Certificate p k K) :
    (downLocalCharacter (p := p) (k := k) (K := K) (A := A)
      P G hP root kernel regular thetaBar W navarro hPG hUT).val =
      PrimeRegularClassFunction.pullback
        (TypeBCentralKernelQuotientInertiaImages.localImageEquiv P G hP root kernel regular thetaBar hPG W).toMonoidHom
        (nativeLocalCharacter P G hP root kernel regular thetaBar W hPG hUT navarro).val := by
  ext x
  change (normalizerDownCharacter P G hP root W navarro).val
      (PrimeRegularElement.map (normalizerProjectionEquiv P G TI hPG hP W hUT).toMonoidHom x) =
    (normalizerDownCharacter P G hP root W navarro).val
      (PrimeRegularElement.map
        (nativeNormalizerEquiv P G hP root kernel regular thetaBar W hPG hUT).symm.toMonoidHom
        (PrimeRegularElement.map
          (TypeBCentralKernelQuotientInertiaImages.localImageEquiv P G hP root kernel regular thetaBar hPG W).toMonoidHom x))
  congr 1
  apply Subtype.ext
  change (normalizerProjectionEquiv P G TI hPG hP W hUT) x.val =
    (normalizerProjectionEquiv P G TI hPG hP W hUT)
      ((TypeBCentralKernelQuotientInertiaImages.localImageEquiv P G hP root kernel regular thetaBar hPG W).symm
        ((TypeBCentralKernelQuotientInertiaImages.localImageEquiv P G hP root kernel regular thetaBar hPG W) x.val))
  exact congrArg (normalizerProjectionEquiv P G TI hPG hP W hUT)
    ((TypeBCentralKernelQuotientInertiaImages.localImageEquiv P G hP root kernel regular thetaBar hPG W).symm_apply_apply x.val).symm

end ModularRep.PaperProofs.TypeBCentralKernelQuotientTripleCharacters


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
