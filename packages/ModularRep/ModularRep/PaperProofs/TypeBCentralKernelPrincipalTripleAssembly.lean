import ModularRep.PaperProofs.TypeBCentralKernelFibreAssembly
import ModularRep.PaperProofs.TypeBCentralKernelTripleInflation
import ModularRep.PaperProofs.TypeBCentralKernelTripleDataBinding

/-!
# The same principal-fibre map and every actual raw representative

The selected downstairs character is the inverse of the checked Brauer
fibre equivalence. Descent of every raw representative is matched by the
same quotient bijection. These joins introduce no upstairs matching or
inductive-condition source input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelPrincipalTripleAssembly

open ModularRep TypeBCentralKernelCarriers TypeBCentralKernelBrauerInflation
open TypeBCentralKernelBlockSource TypeBCentralKernelFibreAssembly
open TypeBCentralKernelInertia TypeBCentralKernelWeightTransport

universe u

variable {p : ℕ} {k K A : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A]
  (G P : Subgroup A) [G.Normal] [P.Normal]
  (hP : IsPGroup p (kernelInG G P))
  (central : kernelInG G P ≤ Subgroup.center G)
  (root : PrimeRegularRootEmbedding p k K (QuotientG G P))
  (data : TransportData (kernelInG G P) hP central root)
  (B : LiteralPrimitiveBlock k G)
  (omegaDown : DownBrauer data B ≃ DownWeight data B)

def downOfUp (theta : UpBrauer data B) : DownBrauer data B :=
  (brauerLift data B).symm theta

/-- The two honest quotient layers retain the descended raw weight itself. -/
theorem descend_classOf (W : CharacterWeight p K G) :
    quotientConjugacyClassEquiv (K := K) (kernelInG G P) hP (classOf W) =
      classOf (TypeBCentralKernelTripleProjection.quotientWeight P G hP W) := rfl

/-- Every representative of the constructed upstairs image descends to
the image of its actual inverse Brauer character under the given lower map. -/
theorem matchedDown (theta : UpBrauer data B) (W : CharacterWeight p K G)
    (representative : liftedMap data B omegaDown theta = classOf W) :
    (omegaDown (downOfUp G P hP central root data B theta)).val =
      classOf (TypeBCentralKernelTripleProjection.quotientWeight P G hP W) := by
  calc
    (omegaDown (downOfUp G P hP central root data B theta)).val =
        quotientConjugacyClassEquiv (K := K) (kernelInG G P) hP
          (liftedMap data B omegaDown theta) :=
      (descended_liftedBijection data B omegaDown theta).symm
    _ = quotientConjugacyClassEquiv (K := K) (kernelInG G P) hP (classOf W) :=
      congrArg (quotientConjugacyClassEquiv (K := K) (kernelInG G P) hP) representative
    _ = classOf (TypeBCentralKernelTripleProjection.quotientWeight P G hP W) :=
      descend_classOf G P hP W

/-- A lower-side matched raw descent determines the representative of the
one constructed upstairs map; there is no second choice of bijection. -/
theorem matchedUp (thetaBar : DownBrauer data B) (W : CharacterWeight p K G)
    (representative : (omegaDown thetaBar).val =
      classOf (TypeBCentralKernelTripleProjection.quotientWeight P G hP W)) :
    liftedMap data B omegaDown (brauerLift data B thetaBar) = classOf W := by
  apply (quotientConjugacyClassEquiv (K := K) (kernelInG G P) hP).injective
  calc
    quotientConjugacyClassEquiv (K := K) (kernelInG G P) hP
        (liftedMap data B omegaDown (brauerLift data B thetaBar)) =
        (omegaDown ((brauerLift data B).symm (brauerLift data B thetaBar))).val :=
      descended_liftedBijection data B omegaDown (brauerLift data B thetaBar)
    _ = (omegaDown thetaBar).val := by rw [Equiv.symm_apply_apply]
    _ = classOf (TypeBCentralKernelTripleProjection.quotientWeight P G hP W) := representative
    _ = quotientConjugacyClassEquiv (K := K) (kernelInG G P) hP (classOf W) :=
      (descend_classOf G P hP W).symm

/-- Reinflating the selected quotient character is literally the given
upstairs character, not merely an isomorphic representation. -/
theorem reinflatedTheta_eq (theta : UpBrauer data B) :
    TypeBCentralKernelTripleInflation.originalTheta P G hP root data.kernel data.regular
      (downOfUp G P hP central root data B theta).val = theta.val :=
  congrArg Subtype.val ((brauerLift data B).apply_symm_apply theta)

/-- The hypothesis refers only to the displayed quotient actor and fibres. -/
abbrev QuotientEquivariant : Prop :=
  ∀ (a : QuotientA P) (phi phi' : DownBrauer data B),
    phi'.val = IrreducibleBrauerCharacter.twist root phi.val (quotientAction G P a⁻¹) →
      (omegaDown phi').val = CharacterWeight.rightTwistConjugacyClass
        (quotientAction G P a⁻¹) (omegaDown phi).val

variable (hb : IsPrincipal B)
  (hEquiv : QuotientEquivariant G P hP central root data B omegaDown)

include hb hEquiv in
/-- The actual inertia inclusion is deduced from the matched lower pair
and the same constructed principal-fibre map. -/
theorem matchedInertia (thetaBar : DownBrauer data B) (W : CharacterWeight p K G)
    (representative : (omegaDown thetaBar).val =
      classOf (TypeBCentralKernelTripleProjection.quotientWeight P G hP W)) :
    U G W ≤ T G (upRoot (kernelInG G P) hP root) (brauerLift data B thetaBar).val :=
  lifted_U_le_T G P hP central root data B omegaDown hb hEquiv
    (brauerLift data B thetaBar) W
    (matchedUp G P hP central root data B omegaDown thetaBar W representative)

section LiteralOutput

variable [IsAlgClosed K]
  (navarro : TypeBCentralKernelLocalReduction.Navarro318Certificate p k K)

local notation "rootUp" => upRoot (kernelInG G P) hP root

/-- The output is a literal block triple inside the given character's
actual inertia. The two root equations bind its characters to that exact
character and the reduction of the same raw ordinary weight. This is an
output record, never an external source hypothesis. -/
structure LiteralPairWitness (theta : UpBrauer data B) (W : CharacterWeight p K G) where
  inclusion : U G W ≤ T G rootUp theta.val
  tripleData : TypeBCentralKernelTripleCertificate.TripleData
    (p := p) (k := k) (K := K)
    (TypeBCentralKernelTripleProjection.N G (T G rootUp theta.val))
    (TypeBCentralKernelTripleProjection.H G (T G rootUp theta.val) W)
  baseRoot_eq : tripleData.base.iota =
    TypeBCentralKernelTripleCharacters.baseRoot G rootUp theta.val
  localRoot_eq : tripleData.localData.iota =
    (TypeBCentralKernelTripleInflation.normalizerUpRoot P G hP root W).alongMulEquiv
      (TypeBCentralKernelTripleProjection.normalizerTripleEquiv
        (p := p) (K := K) G (T G rootUp theta.val) W inclusion)
  triple : Nonempty (TypeBCentralKernelTripleCertificate.BlockTripleWitness tripleData
    (baseRoot_eq.symm ▸ TypeBCentralKernelTripleCharacters.baseBrauer G rootUp theta.val)
    (localRoot_eq.symm ▸ IrreducibleBrauerCharacter.equivAlongMulEquiv
      (TypeBCentralKernelTripleInflation.normalizerUpRoot P G hP root W)
      (TypeBCentralKernelTripleProjection.normalizerTripleEquiv
        (p := p) (K := K) G (T G rootUp theta.val) W inclusion)
      (TypeBCentralKernelTripleInflation.normalizerUpCharacter P G hP root W navarro)))

variable (hPG : P ≤ G) (hPambient : IsPGroup p P)

variable (pairData : ∀ (thetaBar : DownBrauer data B) (W : CharacterWeight p K G)
  (representative : (omegaDown thetaBar).val =
    classOf (TypeBCentralKernelTripleProjection.quotientWeight P G hP W)),
  TypeBCentralKernelTripleDataBinding.PerPairData
    (p := p) (k := k) (K := K) (A := A)
    P G hPG hPambient root data.kernel data.regular thetaBar.val W
    (matchedInertia (p := p) (k := k) (K := K) (A := A)
      G P hP central root data B omegaDown hb hEquiv thetaBar W representative))

variable (certificate : TypeBCentralKernelTripleCertificate.Lemma314Certificate p k K)

-- This is a lower-side implication hypothesis on literal quotient triples.
-- It is not a literature certificate asserting a Type B correspondence.
variable (quotientWitness : ∀ (thetaBar : DownBrauer data B) (W : CharacterWeight p K G)
  (representative : (omegaDown thetaBar).val =
    classOf (TypeBCentralKernelTripleProjection.quotientWeight P G hP W)),
  Nonempty (TypeBCentralKernelTripleCertificate.BlockTripleWitness
    (TypeBCentralKernelTripleDataBinding.downData
      (p := p) (k := k) (K := K) (A := A)
      P G hPG hPambient root data.kernel data.regular thetaBar.val W
      (matchedInertia (p := p) (k := k) (K := K) (A := A)
        G P hP central root data B omegaDown hb hEquiv thetaBar W representative)
      (pairData thetaBar W representative))
    (TypeBCentralKernelTripleDataBinding.downTheta
      (p := p) (k := k) (K := K) (A := A)
      P G hPG hPambient root data.kernel data.regular thetaBar.val W
      (matchedInertia (p := p) (k := k) (K := K) (A := A)
        G P hP central root data B omegaDown hb hEquiv thetaBar W representative)
      (pairData thetaBar W representative))
    (TypeBCentralKernelTripleDataBinding.downPhi
      (p := p) (k := k) (K := K) (A := A)
      P G hPG hPambient root data.kernel data.regular thetaBar.val W
      (matchedInertia (p := p) (k := k) (K := K) (A := A)
        G P hP central root data B omegaDown hb hEquiv thetaBar W representative)
      (pairData thetaBar W representative) navarro)))

include hPG hPambient hb hEquiv pairData certificate quotientWitness in
/-- Every upstairs character and every raw representative of its image
has the literal triple in that character's actual inertia. The proof uses
surjectivity of the same Brauer fibre equivalence, so it needs no character
choice, conjugacy choice or independently supplied upstairs triple. -/
theorem allLiteralTriples (theta : UpBrauer data B) (W : CharacterWeight p K G)
    (representative : liftedMap data B omegaDown theta = classOf W) :
    Nonempty (LiteralPairWitness G P hP central root data B navarro theta W) := by
  obtain ⟨thetaBar, rfl⟩ := (brauerLift data B).surjective theta
  have hDown : (omegaDown thetaBar).val =
      classOf (TypeBCentralKernelTripleProjection.quotientWeight P G hP W) := by
    simpa only [downOfUp, Equiv.symm_apply_apply] using
      matchedDown G P hP central root data B omegaDown (brauerLift data B thetaBar) W representative
  let hUT := matchedInertia (p := p) (k := k) (K := K) (A := A)
    G P hP central root data B omegaDown hb hEquiv thetaBar W hDown
  let D := pairData thetaBar W hDown
  refine ⟨{
    inclusion := hUT
    tripleData := TypeBCentralKernelTripleDataBinding.upData
      (p := p) (k := k) (K := K) (A := A)
      P G hPG hPambient root data.kernel data.regular thetaBar.val W hUT D
    baseRoot_eq := rfl
    localRoot_eq := rfl
    triple := ?_ }⟩
  exact TypeBCentralKernelTripleDataBinding.perPairInflate
    (p := p) (k := k) (K := K) (A := A)
    P G hPG hPambient root data.kernel data.regular thetaBar.val W hUT D navarro
    certificate (quotientWitness thetaBar W hDown)

include hPG hPambient hb hEquiv pairData certificate quotientWitness in
/-- The complete relative transfer endpoint: one constructed principal
fibre equivalence, all-A equivariance, and the literal triple for every
character and every raw representative of that same equivalence's image.
The exact lower quotient triples and all source/field/catalogue guards
remain visible hypotheses. No full-automorphism or Spin specialization is
silently asserted by this relative theorem. -/
theorem principalTransfer :
    ∃ omega : UpBrauer data B ≃ UpWeight data B,
      omega = liftedBijection data B omegaDown ∧
      (∀ (a : A) (theta : UpBrauer data B),
        (omega (fibreAction G rootUp B
          (principalStable G P hP central root data B hb) a theta)).val =
          conjugationOp G a • (omega theta).val) ∧
      (∀ (theta : UpBrauer data B) (W : CharacterWeight p K G),
        (omega theta).val = classOf W →
          Nonempty (LiteralPairWitness G P hP central root data B navarro theta W)) := by
  refine ⟨liftedBijection data B omegaDown, rfl, ?_, ?_⟩
  · intro a theta
    exact liftedMap_ambientAction G P hP central root data B omegaDown hb hEquiv a theta
  · intro theta W representative
    exact allLiteralTriples G P hP central root data B omegaDown hb hEquiv navarro
      hPG hPambient pairData certificate quotientWitness theta W representative

end LiteralOutput

end ModularRep.PaperProofs.TypeBCentralKernelPrincipalTripleAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
