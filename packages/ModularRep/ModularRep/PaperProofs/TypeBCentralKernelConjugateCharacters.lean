import ModularRep.PaperProofs.TypeBCentralKernelConjugateInertia
import ModularRep.PaperProofs.TypeBCentralKernelTripleCharacters

/-!
# Literal character values under simultaneous ambient conjugation

The global character is the actual conjugate Brauer function on the actual
conjugate inertia. The local character is independently reduced from the
ordinary character of the actual conjugate raw weight. Its value comparison
uses two reduction equations and the checked ordinary right-twist formula;
no local character or block matching is assumed.

Full lift equality for the global roots is constructed. Full lift equality
for the local roots follows only when it holds for the two prescribed
quotient roots. It is separate from the ordinary-value argument. Specified
block and complete witness transport belong to the subsequent triple join.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelConjugateCharacters

open ModularRep TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelTripleCharacters TypeBCentralKernelLocalReduction

universe u

variable {p : ℕ} {k K A : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A] (G : Subgroup A) [G.Normal]
  (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root) (a : A)

local notation "thetaA" => conjugationOp G a • theta

/-- Both global roots come from the same root on G, including its full lift. -/
theorem baseRoot_lift_eq :
    (baseRoot G root thetaA).lift = (baseRoot G root theta).lift := by
  funext z
  exact (baseRoot_lift G root thetaA z).trans (baseRoot_lift G root theta z).symm

/-- The global character square uses the same ambient conjugation as eT. -/
theorem baseBrauer_map_value
    (x : PrimeRegularElement (G := base G root theta) p) :
    (baseBrauer G root theta).val x =
      (baseBrauer G root thetaA).val
        (PrimeRegularElement.map
          (TypeBCentralKernelConjugateInertia.baseEquiv G root theta a).toMonoidHom x) := by
  rw [baseBrauer_value, baseBrauer_value]
  change theta.val (PrimeRegularElement.map
      (TypeBCentralKernelTripleCharacters.baseEquiv G root theta).symm.toMonoidHom x) =
    theta.val (PrimeRegularElement.map (originalAction G a⁻¹).toMonoidHom
      (PrimeRegularElement.map
        (TypeBCentralKernelTripleCharacters.baseEquiv G root thetaA).symm.toMonoidHom
        (PrimeRegularElement.map
          (TypeBCentralKernelConjugateInertia.baseEquiv G root theta a).toMonoidHom x)))
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val.val = a⁻¹ * (a * x.val.val.val * a⁻¹) * (a⁻¹)⁻¹
  simp [mul_assoc]

/-- Exact target-value pullback, in the form consumed by literal witness transport. -/
theorem baseBrauer_pullback :
    (baseBrauer G root thetaA).val =
      PrimeRegularClassFunction.pullback
        (TypeBCentralKernelConjugateInertia.baseEquiv G root theta a).symm.toMonoidHom
        (baseBrauer G root theta).val := by
  ext y
  have h := baseBrauer_map_value G root theta a
    (PrimeRegularElement.map
      (TypeBCentralKernelConjugateInertia.baseEquiv G root theta a).symm.toMonoidHom y)
  have mapped :
      PrimeRegularElement.map
          (TypeBCentralKernelConjugateInertia.baseEquiv G root theta a).toMonoidHom
          (PrimeRegularElement.map
            (TypeBCentralKernelConjugateInertia.baseEquiv G root theta a).symm.toMonoidHom y) = y := by
    apply Subtype.ext
    exact (TypeBCentralKernelConjugateInertia.baseEquiv G root theta a).apply_symm_apply y.val
  rw [mapped] at h
  exact h.symm

variable (W : CharacterWeight p K G) (hUT : U G W ≤ T G root theta)

/-- The inverse local identification has the same underlying ambient element. -/
theorem localEquiv_symm_ambient (x : tripleLocal G root theta W) :
    (((TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT).symm x : G) : A) =
      x.val.val.val := by
  have h := congrArg (fun z : tripleLocal G root theta W => z.val.val.val)
    ((TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT).apply_symm_apply x)
  exact (localEquiv_ambient G root theta W hUT
    ((TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT).symm x)).symm.trans h

variable (rootQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))

/-- Inflation and local subgroup transport retain the quotient root's full lift. -/
theorem localRoot_lift_eq_quotient :
    (localRoot G root theta W hUT rootQ).lift = rootQ.lift := by
  funext z
  exact (localRoot_lift G root theta W hUT rootQ z).trans
    (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift
      (normalizerKernel W) (normalizerKernel_isPGroup W) rootQ z)

local notation "WA" => TypeBCentralKernelConjugateInertia.conjugateWeight G a W

variable (hUTA : U G (TypeBCentralKernelConjugateInertia.conjugateWeight G a W) ≤
    T G root (conjugationOp G a • theta))
  (rootQA : PrimeRegularRootEmbedding p k K
    (NormalizerQuotient (TypeBCentralKernelConjugateInertia.conjugateWeight G a W).subgroup))

/-- Local lift compatibility is a consequence of the displayed quotient-root
compatibility. No comparison of independently chosen roots is invented. -/
theorem localRoot_lift_eq (quotientLifts : rootQA.lift = rootQ.lift) :
    (localRoot G root thetaA WA hUTA rootQA).lift =
      (localRoot G root theta W hUT rootQ).lift :=
  (localRoot_lift_eq_quotient G root thetaA WA hUTA rootQA).trans
    (quotientLifts.trans (localRoot_lift_eq_quotient G root theta W hUT rootQ).symm)

variable (phiQ : IBr rootQ) (phiQA : IBr rootQA)
  (reduction : Reduces rootQ W.localCharacter phiQ)
  (reductionA : Reduces rootQA
    (TypeBCentralKernelConjugateInertia.conjugateWeight G a W).localCharacter phiQA)

include reduction reductionA in
/-- Independently reduced local characters agree on corresponding actual
elements. The only character premises are reduction of the two prescribed
ordinary characters; no root equality is needed for this value argument. -/
theorem localBrauer_value_of_ambient
    (x : PrimeRegularElement (G := tripleLocal G root theta W) p)
    (y : PrimeRegularElement (G := tripleLocal G root thetaA WA) p)
    (ambient : y.val.val.val.val = a * x.val.val.val.val * a⁻¹) :
    (localBrauer G root theta W hUT rootQ phiQ).val x =
      (localBrauer G root thetaA WA hUTA rootQA phiQA).val y := by
  have normalizer_eq :
      rightNormalizerEquiv (originalAction G a⁻¹) W.subgroup
          ((TypeBCentralKernelTripleCharacters.localEquiv G root thetaA WA hUTA).symm y.val) =
        (TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT).symm x.val := by
    apply Subtype.ext
    apply Subtype.ext
    change a⁻¹ *
        (((TypeBCentralKernelTripleCharacters.localEquiv G root thetaA WA hUTA).symm y.val : G) : A) *
        (a⁻¹)⁻¹ =
      (((TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT).symm x.val : G) : A)
    rw [localEquiv_symm_ambient G root thetaA WA hUTA,
      localEquiv_symm_ambient G root theta W hUT, ambient]
    simp [mul_assoc]
  calc
    (localBrauer G root theta W hUT rootQ phiQ).val x =
        W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup
          ((TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT).symm x.val)) :=
      (localBrauer_reduction G root theta W hUT rootQ phiQ reduction x).symm
    _ = (WA).localCharacter (TypeBCentralKernelWeightTransport.localMk (WA).subgroup
          ((TypeBCentralKernelTripleCharacters.localEquiv G root thetaA WA hUTA).symm y.val)) := by
      have value := TypeBCentralKernelWeightTransport.rightTwist_localCharacter W
        (originalAction G a⁻¹)
        ((TypeBCentralKernelTripleCharacters.localEquiv G root thetaA WA hUTA).symm y.val)
      have identified := congrArg
        (fun n : Subgroup.normalizer (W.subgroup : Set G) =>
          W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup n)) normalizer_eq
      exact (value.trans identified).symm
    _ = (localBrauer G root thetaA WA hUTA rootQA phiQA).val y :=
      localBrauer_reduction G root thetaA WA hUTA rootQA phiQA reductionA y

include reduction reductionA in
/-- Any actual local equivalence anchored to the same ambient conjugation
therefore has the exact local-character pullback required by the triple join. -/
theorem localBrauer_pullback
    (eL : tripleLocal G root theta W ≃* tripleLocal G root thetaA WA)
    (anchor : ∀ x, (eL x).val.val.val = a * x.val.val.val * a⁻¹) :
    (localBrauer G root thetaA WA hUTA rootQA phiQA).val =
      PrimeRegularClassFunction.pullback eL.symm.toMonoidHom
        (localBrauer G root theta W hUT rootQ phiQ).val := by
  ext y
  have ambient : y.val.val.val.val =
      a * (eL.symm y.val).val.val.val * a⁻¹ := by
    simpa only [eL.apply_symm_apply] using anchor (eL.symm y.val)
  exact (localBrauer_value_of_ambient G root theta a W hUT rootQ hUTA rootQA
    phiQ phiQA reduction reductionA (PrimeRegularElement.map eL.symm.toMonoidHom y) y ambient).symm

/-- Navarro's two independently chosen reductions supply the two value
premises. The same source is used only for the actual ordinary characters. -/
theorem localBrauer_quotientReduction_pullback [IsAlgClosed K]
    (source : Navarro318Certificate p k K)
    (eL : tripleLocal G root theta W ≃* tripleLocal G root thetaA WA)
    (anchor : ∀ x, (eL x).val.val.val = a * x.val.val.val * a⁻¹) :
    (localBrauer G root thetaA WA hUTA rootQA (quotientReduction WA rootQA source)).val =
      PrimeRegularClassFunction.pullback eL.symm.toMonoidHom
        (localBrauer G root theta W hUT rootQ (quotientReduction W rootQ source)).val :=
  localBrauer_pullback G root theta a W hUT rootQ hUTA rootQA
    (quotientReduction W rootQ source) (quotientReduction WA rootQA source)
    (quotientReduction_value W rootQ source) (quotientReduction_value WA rootQA source)
    eL anchor

end ModularRep.PaperProofs.TypeBCentralKernelConjugateCharacters


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
