import ModularRep.PaperProofs.TypeBWeightCoveringSource
import ModularRep.PaperProofs.TypeBLocalPhysicalBlockBinding

/-!
# Ordinary weight covering in one splitting modular system

The intermediate groups, quotient maps, local characters and DGN output
are the existing literal constructions. Sufficient roots for the finite
ambient group supply the required local ordinary fields. The quotient
Brauer convention is the root constructed from the same residue map.

A DGN application and every raw covering witness both require the given
ordinary selector to equal the selector of an actual specified decomposition
source on that quotient. The correspondence is a narrowly scoped published
input; no character-to-weight matching or field covariance is supplied.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBWeightCoveringSplittingSource

open ModularRep OrdinaryIrreducibleCharacter FDRepSimpleClassKZero
open TypeBWeightCoveringSource TypeBModularGroupRootBinding
open TypeBLocalReductionInstantiation

variable {ell : ℕ} {K O k A : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  [Group A] [Finite A]
  (G0 : Subgroup A) [G0.Normal]

section LocalGroups

variable {W : BaseWeight (ell := ell) (K := K) G0}
  {V : AmbientWeight (ell := ell) (K := K) (A := A)}
  (T : IntermediateData G0 W V)

/-- The actual intermediate quotient is a subquotient of the ambient group. -/
theorem quotient_order_dvd : Nat.card T.Quotient ∣ Nat.card A := by
  letI := T.radical_normal
  exact (Subgroup.card_quotient_dvd_card
    ((baseRadicalImage G0 W).subgroupOf (intermediate G0 W V))).trans
    (Subgroup.card_subgroup_dvd_card (intermediate G0 W V))

/-- The DGN centralizer inherits the same order bound. -/
theorem centralizer_order_dvd : Nat.card T.centralizer ∣ Nat.card A :=
  (Subgroup.card_subgroup_dvd_card T.centralizer).trans (quotient_order_dvd G0 T)

/-- The DGN descent character lives on the actual normalizer quotient. -/
theorem local_order_dvd : Nat.card (NormalizerQuotient T.defect) ∣ Nat.card A :=
  (TypeBLocalReductionInstantiation.local_order_dvd T.defect).trans
    (quotient_order_dvd G0 T)

variable [HasEnoughRootsOfUnity K (Nat.card A)]

def quotientOrdinaryRoots : HasEnoughRootsOfUnity K (Nat.card T.Quotient) :=
  HasEnoughRootsOfUnity.of_dvd K (quotient_order_dvd G0 T)

def centralizerOrdinaryRoots : HasEnoughRootsOfUnity K (Nat.card T.centralizer) :=
  HasEnoughRootsOfUnity.of_dvd K (centralizer_order_dvd G0 T)

def localOrdinaryRoots : HasEnoughRootsOfUnity K (Nat.card (NormalizerQuotient T.defect)) :=
  HasEnoughRootsOfUnity.of_dvd K (local_order_dvd G0 T)

variable (Msys : ModularSystem ell K O k)

/-- The local Brauer convention is computed from the same modular system. -/
def quotientRoot : PrimeRegularRootEmbedding ell k K T.Quotient :=
  groupRoot Msys T.Quotient

theorem quotientRoot_residue : RootResidueCompatible Msys (quotientRoot G0 T Msys) :=
  groupRoot_residue Msys T.Quotient

end LocalGroups

variable (Msys : ModularSystem ell K O k)
  [HasEnoughRootsOfUnity K (Nat.card A)]

/-- Exact specified authentication of the selector in the existing defect
block data. Its support is the computed stable-reduction multiplicity of
the same modular system, with its canonical quotient root. -/
def DefectBlockCalibration
    {W : BaseWeight (ell := ell) (K := K) G0}
    {V : AmbientWeight (ell := ell) (K := K) (A := A)}
    {T : IntermediateData G0 W V}
    (L : LocalGeometry G0 T) (B : DefectBlockData (k := k) G0 L) : Prop := by
  letI := quotientOrdinaryRoots G0 T
  exact ∃ (finiteBlocks : Fintype (LiteralPrimitiveBlock k T.Quotient)),
    letI := finiteBlocks
    ∃ (blocks : BlockIdempotentDecomposition
      (fun b : LiteralPrimitiveBlock k T.Quotient => b.val)),
    ∃ (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys
      (quotientRoot G0 T Msys) (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      blocks),
      B.ordinaryBlock =
        (ordinary.physical (ordinaryRoots := quotientOrdinaryRoots G0 T)).ordinaryBlock

section PhysicalCalibration

variable {W : BaseWeight (ell := ell) (K := K) G0}
  {V : AmbientWeight (ell := ell) (K := K) (A := A)}
  {T : IntermediateData G0 W V}
  (L : LocalGeometry G0 T) (B : DefectBlockData (k := k) G0 L)
  [Fintype (LiteralPrimitiveBlock k T.Quotient)]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k T.Quotient => b.val))

/-- A given specified selector provides calibration by its literal equality. -/
theorem calibration_of_physical :
    letI := quotientOrdinaryRoots G0 T
    ∀ (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys
      (quotientRoot G0 T Msys) (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      blocks),
      B.ordinaryBlock =
        (ordinary.physical (ordinaryRoots := quotientOrdinaryRoots G0 T)).ordinaryBlock →
      DefectBlockCalibration G0 Msys L B := by
  letI := quotientOrdinaryRoots G0 T
  intro ordinary selector
  exact ⟨inferInstance, blocks, ordinary, selector⟩

end PhysicalCalibration

section Correspondent

variable {W : BaseWeight (ell := ell) (K := K) G0}
  {V : AmbientWeight (ell := ell) (K := K) (A := A)}
  {T : IntermediateData G0 W V}
  (L : LocalGeometry G0 T)

/-- The given theta embedding identifies its domain with the actual base image. -/
def thetaEquivBase : NormalizerQuotient W.subgroup ≃* T.baseImage :=
  (MonoidHom.ofInjective L.thetaEmbedding_injective).trans
    (MulEquiv.subgroupCongr L.thetaEmbedding_range)

@[simp]
theorem thetaEquivBase_val (x : NormalizerQuotient W.subgroup) :
    (thetaEquivBase G0 L x : T.Quotient) = L.thetaEmbedding x := rfl

/-- Restrict theta along the inverse onto its base image and actual inclusion. -/
def centralizerRestrictionMap : T.centralizer →* NormalizerQuotient W.subgroup :=
  (thetaEquivBase G0 L).symm.toMonoidHom.comp
    (Subgroup.inclusion (show T.centralizer ≤ T.baseImage from inf_le_left))

@[simp]
theorem centralizerRestrictionMap_anchor (x : T.centralizer) :
    L.thetaEmbedding (centralizerRestrictionMap G0 L x) = (x : T.Quotient) := by
  exact congrArg (fun y : T.baseImage => (y : T.Quotient))
    ((thetaEquivBase G0 L).apply_symm_apply
      (⟨(x : T.Quotient), x.property.1⟩ : T.baseImage))

/-- Navarro--Spaeth, Hypothesis 5.1 and Theorem 5.2(a), with trivial
intersection defect: the DGN character is the unique defect-zero
constituent whose ordinary restriction multiplicity is prime to ell. -/
structure DGNLocalCertificate extends DGNData G0 L where
  multiplicities : Irr K T.centralizer →₀ ℕ
  restriction : ∀ x : T.centralizer,
    W.localCharacter (centralizerRestrictionMap G0 L x) =
      multiplicities.sum (fun psi m => (m : K) * psi x)
  pi_multiplicity : ¬ ell ∣ multiplicities pi
  other_defectZero : ∀ psi : Irr K T.centralizer,
    IsDefectZeroOrdinaryCharacter ell psi → psi ≠ pi → ell ∣ multiplicities psi

variable (D : DGNLocalCertificate G0 L)

/-- The distinguished correspondent really occurs in that same restriction. -/
theorem pi_occurs : OrdinaryOccursInRestriction (centralizerRestrictionMap G0 L)
    W.localCharacter D.pi := by
  refine ⟨D.multiplicities, ?_, D.restriction⟩
  intro hzero
  exact D.pi_multiplicity (hzero.symm ▸ dvd_zero ell)

/-- The displayed expansion singles out precisely its DGN character. -/
theorem defectZero_multiplicity_iff (psi : Irr K T.centralizer)
    (defectZero : IsDefectZeroOrdinaryCharacter ell psi) :
    ¬ ell ∣ D.multiplicities psi ↔ psi = D.pi := by
  classical
  constructor
  · intro h
    by_contra different
    exact h (D.other_defectZero psi defectZero different)
  · intro equal
    rw [equal]
    exact D.pi_multiplicity

end Correspondent

/-- The published DGN assignment on calibrated finite local groups.
Both the finite ambient splitting scope and the same modular system are
explicit constructor indices. The local restriction certificate fixes
which defect-zero character is the correspondent. -/
structure DGNSource
    {ell : ℕ} {K O k A : Type}
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [ordinaryCharacteristic : CharZero K]
    [residueCharacteristic : CharP k ell] [residueClosure : IsAlgClosed k]
    [Group A] [finiteAmbient : Finite A]
    (G0 : Subgroup A) [normalBase : G0.Normal]
    (Msys : ModularSystem ell K O k)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card A)] where
  data : ∀ {W : BaseWeight (ell := ell) (K := K) G0}
    {V : AmbientWeight (ell := ell) (K := K) (A := A)}
    {T : IntermediateData G0 W V}
    (L : LocalGeometry G0 T) (B : DefectBlockData (k := k) G0 L),
      DefectBlockCalibration G0 Msys L B → DGNLocalCertificate G0 L

variable {Msys}

/-- Raw covering uses only the calibrated selector and the same local
restriction map and ordinary defect-zero characters. -/
def CoversRaw (dgn : DGNSource G0 Msys)
    (V : AmbientWeight (ell := ell) (K := K) (A := A))
    (W : BaseWeight (ell := ell) (K := K) G0) : Prop :=
  ∃ (T : IntermediateData G0 W V) (L : LocalGeometry G0 T)
    (B : DefectBlockData (k := k) G0 L)
    (calibration : DefectBlockCalibration G0 Msys L B),
      OrdinaryOccursInRestriction L.localEmbedding V.localCharacter
        (dgn.data L B calibration).barPi

/-- Covering on the original ordinary weight conjugacy classes. -/
def CoversClass (dgn : DGNSource G0 Msys)
    (up : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := A))
    (down : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := G0)) : Prop :=
  ∃ (V : AmbientWeight (ell := ell) (K := K) (A := A))
    (W : BaseWeight (ell := ell) (K := K) G0),
      rawClass V = up ∧ rawClass W = down ∧ CoversRaw G0 dgn V W

end ModularRep.PaperProofs.TypeBWeightCoveringSplittingSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
