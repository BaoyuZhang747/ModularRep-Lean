import ModularRep.PaperProofs.TypeBCentralKernelSpinFibreIdentification
import ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding
import ModularRep.PaperProofs.TypeBSpinRawWeightSeparationBinding

/-!+# The criterion pair in the full semidirect ambient

The base group is identified with the range of its canonical embedding
into the whole semidirect product. Roots, Brauer characters and raw
ordinary weights are transported along this same equivalence. The
natural-action square identifies the criterion inertias with the literal
conjugation inertias on the embedded base.

No character-triple witness or independently allocated embedded weight
block is supplied. The raw transport applies to every representative and
preserves its own local ordinary character on the actual normalizer maps.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCriterionEmbeddedPairBinding

open ModularRep TypeBCriterionHypotheses
open TypeBCentralKernelCarriers TypeBModularGroupRootBinding
open TypeBLocalReductionInstantiation

section Carriers

variable {M E : Type} [Group M] [Group E]
variable (G : Subgroup M) (field : E →* MulAut M)

/-- The fixed equivalence has exactly the criterion's base embedding as value. -/
def baseEquiv : G ≃* embeddedG G field :=
  MonoidHom.ofInjective
    (SemidirectProduct.inl_injective.comp Subtype.val_injective :
      Function.Injective (baseEmbedding G field))

@[simp]
theorem baseEquiv_val (g : G) :
    (baseEquiv G field g : Ambient field) = baseEmbedding G field g := rfl

/-- This is the cardinality of the actual embedded group. -/
theorem baseEquiv_card : Nat.card G = Nat.card (embeddedG G field) :=
  Nat.card_congr (baseEquiv G field).toEquiv

variable [Finite M] [Finite E] [G.Normal] (action : NaturalAction G field)

/-- Literal conjugation, with normality derived from the natural-action square. -/
def embeddedAction : Ambient field →* MulAut (embeddedG G field) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  exact originalAction (embeddedG G field)

/-- The same group equivalence intertwines the whole ambient action. -/
theorem baseEquiv_action (a : Ambient field) (g : G) :
    baseEquiv G field (action.hom a g) =
      embeddedAction G field action a (baseEquiv G field g) := by
  apply Subtype.ext
  change baseEmbedding G field (action.hom a g) =
    a * baseEmbedding G field g * a⁻¹
  exact TypeBLocalOrdinaryGeometry.baseEmbedding_natural G field action a g

/-- The displayed square uses the inverse actor of the existing right action. -/
theorem baseEquiv_inverseAction (a : Ambient field) (g : G) :
    baseEquiv G field (action.hom a⁻¹ g) =
      embeddedAction G field action a⁻¹ (baseEquiv G field g) :=
  baseEquiv_action G field action a⁻¹ g

end Carriers

section Roots

variable {ell : ℕ} {K O k M E : Type}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) (field : E →* MulAut M)

/-- The prescribed root is transported along the canonical base equivalence. -/
def embeddedRoot (root : PrimeRegularRootEmbedding ell k K G) :
    PrimeRegularRootEmbedding ell k K (embeddedG G field) :=
  root.alongMulEquiv (baseEquiv G field)

theorem embeddedRoot_lift (root : PrimeRegularRootEmbedding ell k K G) :
    (embeddedRoot G field root).lift = root.lift :=
  funext (root.alongMulEquiv_lift (baseEquiv G field))

/-- The exact residue calibration survives this transport on the same system. -/
theorem embeddedRoot_residue (Msys : ModularSystem ell K O k)
    (root : PrimeRegularRootEmbedding ell k K G)
    (calibration : RootResidueCompatible Msys root) :
    RootResidueCompatible Msys (embeddedRoot G field root) :=
  TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue
    Msys root calibration (baseEquiv G field)

/-- The embedded convention is also the canonical root of this same system. -/
theorem embeddedRoot_eq_groupRoot (Msys : ModularSystem ell K O k)
    (root : PrimeRegularRootEmbedding ell k K G)
    (calibration : RootResidueCompatible Msys root) :
    embeddedRoot G field root = groupRoot Msys (embeddedG G field) :=
  eq_groupRoot_of_residue Msys _ _ (embeddedRoot_residue G field Msys root calibration)

/-- Equal actual orders transfer sufficient roots without changing coefficients. -/
def embeddedOrdinaryRoots [HasEnoughRootsOfUnity K (Nat.card G)] :
    HasEnoughRootsOfUnity K (Nat.card (embeddedG G field)) := by
  rw [← baseEquiv_card G field]
  infer_instance

/-- Brauer transport has the prescribed embedded root as its target. -/
def brauerEquiv (root : PrimeRegularRootEmbedding ell k K G) :
    IBr root ≃ IBr (embeddedRoot G field root) :=
  TypeBCentralKernelSpinFibreIdentification.brauerEquiv (baseEquiv G field)
    root (embeddedRoot G field root) (embeddedRoot_lift G field root)

theorem brauerEquiv_val (root : PrimeRegularRootEmbedding ell k K G) (phi : IBr root) :
    (brauerEquiv G field root phi).val =
      PrimeRegularClassFunction.pullback (baseEquiv G field).symm.toMonoidHom phi.val :=
  TypeBCentralKernelSpinFibreIdentification.brauerEquiv_val (baseEquiv G field)
    root (embeddedRoot G field root) (embeddedRoot_lift G field root) phi

variable [G.Normal] (action : NaturalAction G field)

/-- The Brauer square uses the same inverse ambient actor on both carriers. -/
theorem brauerEquiv_twist (root : PrimeRegularRootEmbedding ell k K G)
    (a : Ambient field) (phi : IBr root) :
    brauerEquiv G field root (IrreducibleBrauerCharacter.twist root phi (action.hom a⁻¹)) =
      IrreducibleBrauerCharacter.twist (embeddedRoot G field root)
        (brauerEquiv G field root phi) (embeddedAction G field action a⁻¹) :=
  TypeBCentralKernelSpinFibreIdentification.brauerEquiv_twist (baseEquiv G field)
    root (embeddedRoot G field root) (embeddedRoot_lift G field root)
    (action.hom a⁻¹) (embeddedAction G field action a⁻¹)
    (baseEquiv_inverseAction G field action a) phi

/-- Equality in the full ambient, rather than only in its left factor. -/
theorem brauerInertia_eq_T (root : PrimeRegularRootEmbedding ell k K G)
    (phi : IBr root) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
    brauerInertia G field action root phi =
      TypeBCentralKernelInertia.T (embeddedG G field) (embeddedRoot G field root)
        (brauerEquiv G field root phi) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  ext a
  change a ∈ TypeBCentralKernelInertia.brauerStabilizer action.hom root phi ↔
    a ∈ TypeBCentralKernelInertia.brauerStabilizer (embeddedAction G field action)
      (embeddedRoot G field root) (brauerEquiv G field root phi)
  rw [TypeBCentralKernelInertia.mem_brauerStabilizer,
    TypeBCentralKernelInertia.mem_brauerStabilizer]
  have square := brauerEquiv_twist G field action root a phi
  constructor
  · intro h
    exact square.symm.trans (congrArg (brauerEquiv G field root) h)
  · intro h
    exact (brauerEquiv G field root).injective (square.trans h)

end Roots

section Weights

variable {ell : ℕ} {K M E : Type} [Field K] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) (field : E →* MulAut M)

/-- The existing exact normalizer-quotient transport on every raw weight. -/
def rawWeightEquiv : CharacterWeight ell K G ≃ CharacterWeight ell K (embeddedG G field) :=
  TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv (baseEquiv G field)

def weightClassEquiv :
    CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := G) ≃
      CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := embeddedG G field) :=
  TypeBCentralKernelSpinFibreIdentification.weightClassEquiv (baseEquiv G field)

/-- The radical image in the full ambient is literally the criterion's radical. -/
theorem rawWeightEquiv_embeddedRadical (W : CharacterWeight ell K G) :
    (rawWeightEquiv G field W).subgroup.map (embeddedG G field).subtype =
      embeddedRadical G field W := by
  change (W.subgroup.map (baseEquiv G field).toMonoidHom).map
    (embeddedG G field).subtype = W.subgroup.map (baseEmbedding G field)
  rw [Subgroup.map_map]
  rfl

/-- The transported character is the given weight's own ordinary character. -/
theorem rawWeightEquiv_localCharacter (W : CharacterWeight ell K G)
    (x : Subgroup.normalizer (W.subgroup : Set G))
    (y : Subgroup.normalizer ((rawWeightEquiv G field W).subgroup : Set (embeddedG G field)))
    (hxy : baseEquiv G field x = y) :
    (rawWeightEquiv G field W).localCharacter
        (TypeBCentralKernelWeightTransport.localMk (rawWeightEquiv G field W).subgroup y) =
      W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup x) :=
  TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv_localCharacter
    (baseEquiv G field) W x y hxy

theorem weightClassEquiv_classOf (W : CharacterWeight ell K G) :
    weightClassEquiv G field (TypeBCentralKernelInertia.classOf W) =
      TypeBCentralKernelInertia.classOf (rawWeightEquiv G field W) :=
  TypeBCentralKernelSpinFibreIdentification.weightClassEquiv_classOf (baseEquiv G field) W

variable [G.Normal] (action : NaturalAction G field)

theorem rawWeightEquiv_rightTwist (a : Ambient field) (W : CharacterWeight ell K G) :
    rawWeightEquiv G field (W.rightTwist (action.hom a⁻¹)) =
      (rawWeightEquiv G field W).rightTwist (embeddedAction G field action a⁻¹) :=
  TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv_rightTwist (baseEquiv G field)
    (action.hom a⁻¹) (embeddedAction G field action a⁻¹)
    (baseEquiv_inverseAction G field action a) W

theorem weightClassEquiv_rightTwist (a : Ambient field)
    (w : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := G)) :
    weightClassEquiv G field (CharacterWeight.rightTwistConjugacyClass (action.hom a⁻¹) w) =
      CharacterWeight.rightTwistConjugacyClass (embeddedAction G field action a⁻¹)
        (weightClassEquiv G field w) :=
  TypeBCentralKernelSpinFibreIdentification.weightClassEquiv_rightTwist (baseEquiv G field)
    (action.hom a⁻¹) (embeddedAction G field action a⁻¹)
    (baseEquiv_inverseAction G field action a) w

/-- Raw inertia agrees with the central-kernel notation on the embedded pair. -/
theorem rawInertia_eq_U (W : CharacterWeight ell K G) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
    rawInertia G field action W =
      TypeBCentralKernelInertia.U (embeddedG G field) (rawWeightEquiv G field W) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  ext a
  change a ∈ TypeBCentralKernelInertia.rawStabilizer action.hom W ↔
    a ∈ TypeBCentralKernelInertia.rawStabilizer (embeddedAction G field action)
      (rawWeightEquiv G field W)
  rw [TypeBCentralKernelInertia.mem_rawStabilizer,
    TypeBCentralKernelInertia.mem_rawStabilizer]
  have square := rawWeightEquiv_rightTwist G field action a W
  constructor
  · intro h
    exact square.symm.trans (congrArg (rawWeightEquiv G field) h)
  · intro h
    exact (rawWeightEquiv G field).injective (square.trans h)

/-- The literal radical normalizer is retained and is already forced by raw fixedness. -/
theorem rawNormalizerInertia_eq_U (W : CharacterWeight ell K G) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
    rawNormalizerInertia G field action W =
      TypeBCentralKernelInertia.U (embeddedG G field) (rawWeightEquiv G field W) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  rw [TypeBSpinRawWeightSeparationBinding.rawNormalizerInertia_eq_rawInertia]
  exact rawInertia_eq_U G field action W

/-- The weight-class comparison uses the same conjugation homomorphism as T and U. -/
theorem weightClassInertia_eq
    (w : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := G)) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
    weightClassInertia G field action w =
      (MulAction.stabilizer (MulAut (embeddedG G field))ᵐᵒᵖ (weightClassEquiv G field w)).comap
        (TypeBCentralKernelInertia.conjugationOp (embeddedG G field)) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  ext a
  change CharacterWeight.rightTwistConjugacyClass (action.hom a⁻¹) w = w ↔
    CharacterWeight.rightTwistConjugacyClass (embeddedAction G field action a⁻¹)
      (weightClassEquiv G field w) = weightClassEquiv G field w
  have square := weightClassEquiv_rightTwist G field action a w
  constructor
  · intro h
    exact square.symm.trans (congrArg (weightClassEquiv G field) h)
  · intro h
    exact (weightClassEquiv G field).injective (square.trans h)

end Weights

end ModularRep.PaperProofs.TypeBCriterionEmbeddedPairBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
