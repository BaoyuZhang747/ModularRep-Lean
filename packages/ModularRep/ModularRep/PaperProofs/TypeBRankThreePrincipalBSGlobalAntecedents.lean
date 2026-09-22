import ModularRep.PaperProofs.TypeBRankThreePrincipalRawInertiaBinding

/-!
# Global extensions on the embedded matrix Omega carrier

The existing all-conjugate extension theorems keep the original two
target groups fixed. Their realizing representations are pulled back
through the canonical base equivalence, giving extensions of precisely
the embedded characters used by the specified pair. The conjugating
actor remains the inverse of the same SO inclusion.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise commutatorElement

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalBSGlobalAntecedents

open ModularRep TypeBCriterionHypotheses TypeBCentralKernelInertia
open TypeBCliffordCarriers TypeBRankThreePrincipalCountBinding
open TypeBCliffordOrthogonalAmbientQuotient TypeBCliffordOrthogonalFullFieldBinding
open TypeBCliffordOrthogonalAmbientActionBinding TypeBRankThreePrincipalMatchedInertia
open TypeBRankThreePrincipalRawInertiaBinding TypeBCommonConjugateGlobalExtensions

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section RepresentationTransport

variable {ell : ℕ} {k K M E : Type}
  [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
  [Group M] [Finite M] [Group E] [Finite E]
  (G : Subgroup M) (field : E →* MulAut M)
  (root : PrimeRegularRootEmbedding ell k K G)
  (phi : IBr root) (I : Subgroup (Ambient field))

/-- An internally obtained extension becomes an extension along the literal
subgroup inclusion. Its target representation and coefficient fields stay fixed. -/
theorem extensionIn_to_embedded (base_le : embeddedG G field ≤ I)
    (extension : BrauerExtensionIn G field root phi I) :
    BrauerExtendsAlong (Subgroup.inclusion base_le)
      (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root)
      (TypeBCriterionEmbeddedPairBinding.brauerEquiv G field root phi) := by
  let e := TypeBCriterionEmbeddedPairBinding.baseEquiv G field
  obtain ⟨V, hV, hcharacter, rho, ⟨restriction⟩⟩ := extension.witness
  refine ⟨FDRep.of (Representation.pullback V.ρ e.symm.toMonoidHom),
    hV.pullback e.symm.toMonoidHom e.symm.surjective, ?_, rho, ?_⟩
  · change (TypeBCriterionEmbeddedPairBinding.brauerEquiv G field root phi).val =
      (Representation.pullback V.ρ e.symm.toMonoidHom).brauerCharacterOfRootEmbedding
        (root.alongMulEquiv e)
    rw [TypeBCriterionEmbeddedPairBinding.brauerEquiv_val,
      Representation.brauerCharacterOfRootEmbedding_pullback_mulEquiv]
    exact congrArg (PrimeRegularClassFunction.pullback e.symm.toMonoidHom) hcharacter
  · have inclusion_eq : extension.inclusion.comp e.symm.toMonoidHom =
        Subgroup.inclusion base_le := by
      apply MonoidHom.ext
      intro x
      apply Subtype.ext
      exact (extension.inclusion_value (e.symm x)).trans
        (congrArg Subtype.val (e.apply_symm_apply x))
    change Nonempty (Representation.Equiv
      (Representation.pullback rho (Subgroup.inclusion base_le))
      (Representation.pullback V.ρ e.symm.toMonoidHom))
    rw [← inclusion_eq]
    exact ⟨restriction.pullback e.symm.toMonoidHom⟩

end RepresentationTransport

section MatrixOmega

variable {F K k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [Field k] [CharP k 2] [IsAlgClosed k]
  {r f : ℕ} [CharP F r]
  {parameters : OddFieldParameters F r f} {N : NormSource 3 F}
  {fieldSource : FieldActionSource 3 F r f parameters N}
  {C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N}
  {root : PrimeRegularRootEmbedding 2 k K (G F)}
  {b : LiteralPrimitiveBlock k (G F)}
  {indexTwo : (G F).index = 2}

local notation "matrixField" => soFieldAction 3 F parameters le_rfl N C fieldSource
local notation "matrixAction" => matrixNaturalAction F parameters N fieldSource C
local notation "Ghat" => embeddedG (G F) matrixField
local notation "rootHat" => TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) matrixField root
local notation "thetaHat" => fun theta : OmegaBrauer F root b =>
  TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root (Subtype.val theta)
local notation "thetaConj" => fun (theta : OmegaBrauer F root b) (h : H F) =>
  TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root
    (conjugateCharacter (G F) root (Subtype.val theta) h)
local notation "JM" => fun theta : OmegaBrauer F root b =>
  originalMInertia (G F) matrixField matrixAction root (Subtype.val theta)
local notation "JE" => fun theta : OmegaBrauer F root b =>
  originalFieldInertia (G F) matrixField matrixAction root (Subtype.val theta)

/-- The canonical embedded character has exactly the inverse SO actor. -/
theorem embedded_conjugate_eq (theta : OmegaBrauer F root b) (h : H F) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    thetaConj theta h = IrreducibleBrauerCharacter.twist rootHat (thetaHat theta)
      (TypeBCriterionEmbeddedPairBinding.embeddedAction (G F) matrixField matrixAction
        ((SemidirectProduct.inl (φ := matrixField) h)⁻¹)) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  have square := TypeBCriterionEmbeddedPairBinding.brauerEquiv_twist
    (G F) matrixField matrixAction root (SemidirectProduct.inl h) theta.val
  have natural : (matrixAction).hom ((SemidirectProduct.inl (φ := matrixField) h)⁻¹) =
      MulAut.conjNormal (H := G F) h⁻¹ := by
    rw [← map_inv (SemidirectProduct.inl (φ := matrixField)) h]
    exact TypeBIndexTwoAmbientCommutator.naturalAction_inl
      (G F) matrixField matrixAction h⁻¹
  exact (congrArg (fun alpha => TypeBCriterionEmbeddedPairBinding.brauerEquiv
    (G F) matrixField root (IrreducibleBrauerCharacter.twist root theta.val alpha))
      natural.symm).trans square

/-- The base lies in the original SO target through its actual inclusion. -/
theorem originalM_base_le (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    Ghat ≤ JM theta := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  exact le_inf (TypeBGlobalExtensionBinding.base_le_brauerInertia
    (G F) matrixField matrixAction root theta.val)
    (TypeBLocalOrdinaryGeometry.embeddedG_le_embeddedM (G F) matrixField)

/-- The other original target contains the same embedded base by construction. -/
theorem originalField_base_le (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    Ghat ≤ JE theta := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  exact le_sup_left

/-- The original SO target is computed from the specified pair's exact T. -/
theorem originalM_eq_embedded (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    JM theta = T Ghat rootHat (thetaHat theta) ⊓ embeddedM matrixField := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  exact congrArg (fun I => I ⊓ embeddedM matrixField)
    (TypeBCriterionEmbeddedPairBinding.brauerInertia_eq_T
      (G F) matrixField matrixAction root theta.val)

/-- The field-side target uses the original T, before any SO conjugation. -/
theorem originalField_eq_embedded (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    JE theta = Ghat ⊔ (T Ghat rootHat (thetaHat theta) ⊓ embeddedE matrixField) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  exact congrArg (fun I => Ghat ⊔ (I ⊓ embeddedE matrixField))
    (TypeBCriterionEmbeddedPairBinding.brauerInertia_eq_T
      (G F) matrixField matrixAction root theta.val)

include indexTwo in
/-- Every SO-conjugate has the same embedded full inertia. -/
theorem embedded_inertia_all_SO_conjugates (theta : OmegaBrauer F root b) (h : H F) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    T Ghat rootHat (thetaConj theta h) = T Ghat rootHat (thetaHat theta) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  exact (TypeBCriterionEmbeddedPairBinding.brauerInertia_eq_T
    (G F) matrixField matrixAction root (conjugateCharacter (G F) root theta.val h)).symm.trans
      ((TypeBIndexTwoAmbientCommutator.brauerInertia_conjugate_eq
        (G F) matrixField matrixAction indexTwo root theta.val h).trans
          (TypeBCriterionEmbeddedPairBinding.brauerInertia_eq_T
            (G F) matrixField matrixAction root theta.val))

include indexTwo in
/-- The commutator bound is now stated on the specified pair's embedded T. -/
theorem embedded_inertia_commutator_le (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    ⁅T Ghat rootHat (thetaHat theta), embeddedM matrixField⁆ ≤
      T Ghat rootHat (thetaHat theta) ⊓ embeddedM matrixField := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  rw [← TypeBCriterionEmbeddedPairBinding.brauerInertia_eq_T
    (G F) matrixField matrixAction root theta.val]
  exact TypeBIndexTwoAmbientCommutator.brauerInertia_commutator_le
    (G F) matrixField matrixAction indexTwo root theta.val

include indexTwo in
/-- All embedded conjugates extend to one fixed original SO target. -/
theorem all_SO_conjugates_extend_embedded_originalM
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    ∀ h : H F, BrauerExtendsAlong
      (Subgroup.inclusion (originalM_base_le (parameters := parameters) (N := N)
        (fieldSource := fieldSource) (C := C) theta)) rootHat (thetaConj theta h) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  intro h
  obtain ⟨extension⟩ := TypeBCommonConjugateGlobalExtensions.allMConjugates_extend_originalM
    (G F) matrixField matrixAction indexTwo root principle theta.val h
  exact extensionIn_to_embedded (G F) matrixField root _ (JM theta)
    (originalM_base_le (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) theta) extension

include indexTwo in
/-- The second target remains the original base-and-field group for every conjugate. -/
theorem all_SO_conjugates_extend_embedded_originalField
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    ∀ h : H F, BrauerExtendsAlong
      (Subgroup.inclusion (originalField_base_le (parameters := parameters) (N := N)
        (fieldSource := fieldSource) (C := C) theta)) rootHat (thetaConj theta h) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  intro h
  obtain ⟨extension⟩ := TypeBCommonConjugateGlobalExtensions.allMConjugates_extend_originalField
    (G F) matrixField matrixAction indexTwo root principle theta.val h
  exact extensionIn_to_embedded (G F) matrixField root _ (JE theta)
    (originalField_base_le (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) theta) extension

end MatrixOmega

end ModularRep.PaperProofs.TypeBRankThreePrincipalBSGlobalAntecedents


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
