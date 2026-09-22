import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.TypeBQ3FaithfulLocalReduction
import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre
import ModularRep.Navarro417DefectSource
import ModularRep.SubgroupSubconjugacy

/-!
# The actual weight fibre at an order-two defect

The source is scoped to one literal block of matrix G3, its actual Navarro
defect D of order two, and a literal block of N(D). Its fields retain the
first-main correspondent, support at defect groups, and existence and
uniqueness of an ordinary defect-zero character of N(D)/D in that
correspondent. There is no global weight cardinality or matching field.

The support statement is the abelian-defect local argument used in
Koshitani--Spaeth, proof of Theorem 1.3, pp. 787--788. Navarro (4.17)--(4.18)
give the correspondent and radicality. Since D has order two, N(D)=C(D);
Navarro (9.12), p. 202, gives the unique ordinary character of the
correspondent whose kernel contains D and its quotient defect-zero character.
The restricted correspondent identification also uses (4.8), (4.13) and
(4.17). These are subordinate E1/E2 statements with their literal U joins.

The same modular system, finite ordinary roots, calibrated root, all-raw
Navarro reductions and specified selector guard index the source. They bind
the displayed quotient character and inflated block to the actual local
character, rather than to an unrelated selector. Only the selected ambient
idempotent is identified. The deduction below constructs the supported local
representative, derives conjugacy of all supported radicals from the actual
Navarro support predicates, and uses the checked representative-fibre
equivalence to prove that the complete global weight fibre is a singleton.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B3NilpotentWeights

open ModularRep CharacterWeight
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBQ3FaithfulLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Local block and ordinary-character facts for this actual order-two defect. -/
structure LocalSource
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K G3)
    (calibration : RootResidueCompatible Msys root)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card G3)]
    (navarro : ∀ W : CharacterWeight 2 K G3,
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource Msys
        (localQuotientRoot root W.subgroup)
        (localRoot_residueCanonical Msys root calibration W.subgroup))
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (physical : GuardedBlockCompatibility root R.operations)
    (b : LiteralPrimitiveBlock k G3)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
    (D : Subgroup G3)
    (defect :
      letI := R.operations.ambientBlockData.fintypeBlock
      Navarro411DefectRepresentative (p := 2) R.operations.ambientBlockData.blocks b D)
    (cardD : Nat.card D = 2) where
  radical : IsRadicalSubgroup 2 D
  correspondent : InflatedNormalizerBlock (k := k) D
  correspondent_induces :
    letI := R.operations.ambientBlockData.fintypeBlock
    letI := (R.operations.inflatedNormalizerBlockData D).fintypeBlock
    BlockInducesTo (Subgroup.normalizer (D : Set G3))
      (R.operations.inflatedNormalizerBlockData D).catalogue
      R.operations.ambientBlockData.catalogue correspondent b
  supported_defect : ∀ W : CharacterWeight 2 K G3,
    R.operations.rawWeightBlock W = b →
      letI := R.operations.ambientBlockData.fintypeBlock
      Navarro411DefectRepresentative (p := 2)
        R.operations.ambientBlockData.blocks b W.subgroup
  local_correspondent :
    ∀ (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient D))
      (hchi : IsDefectZeroOrdinaryCharacter 2 chi),
      letI := R.operations.ambientBlockData.fintypeBlock
      letI := (R.operations.inflatedNormalizerBlockData D).fintypeBlock
      BlockInducesTo (Subgroup.normalizer (D : Set G3))
        (R.operations.inflatedNormalizerBlockData D).catalogue
        R.operations.ambientBlockData.catalogue
        (R.operations.inflateToNormalizer D
          (R.operations.localCharacterBlock D chi hchi)) b →
      R.operations.inflateToNormalizer D
        (R.operations.localCharacterBlock D chi hchi) = correspondent
  local_character :
    ∃ (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient D))
      (hchi : IsDefectZeroOrdinaryCharacter 2 chi),
      R.operations.inflateToNormalizer D
        (R.operations.localCharacterBlock D chi hchi) = correspondent ∧
      ∀ (eta : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient D))
        (heta : IsDefectZeroOrdinaryCharacter 2 eta),
        R.operations.inflateToNormalizer D
          (R.operations.localCharacterBlock D eta heta) = correspondent → eta = chi

variable (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K G3)
  (calibration : RootResidueCompatible Msys root)
  [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card G3)]
  (navarro : ∀ W : CharacterWeight 2 K G3,
    letI := localOrdinaryRoots (K := K) W.subgroup
    ScopedDefectZeroReductionSource Msys
      (localQuotientRoot root W.subgroup)
      (localRoot_residueCanonical Msys root calibration W.subgroup))
  (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (physical : GuardedBlockCompatibility root R.operations)
  (b : LiteralPrimitiveBlock k G3)
  (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
  (D : Subgroup G3)
  (defect :
    letI := R.operations.ambientBlockData.fintypeBlock
    Navarro411DefectRepresentative (p := 2) R.operations.ambientBlockData.blocks b D)
  (cardD : Nat.card D = 2)
  (source : LocalSource Msys root calibration navarro R physical b ambientAt D defect cardD)

include source in
/-- Two actual Navarro defect representatives of the same block are conjugate. -/
theorem supported_radical_conjugate
    (W : CharacterWeight 2 K G3) (support : R.operations.rawWeightBlock W = b) :
    W.subgroup.AreConjugate D := by
  letI := R.operations.ambientBlockData.fintypeBlock
  let alternative := source.supported_defect W support
  have nonzeroW :=
    (alternative.support411.nonzero_iff_isSubconjugate
      W.subgroup alternative.isPGroup).mpr (Subgroup.IsSubconjugate.refl W.subgroup)
  have nonzeroD :=
    (defect.support411.nonzero_iff_isSubconjugate
      D defect.isPGroup).mpr (Subgroup.IsSubconjugate.refl D)
  have belowD : W.subgroup.IsSubconjugate D :=
    (defect.support411.nonzero_iff_isSubconjugate
      W.subgroup alternative.isPGroup).mp nonzeroW
  have belowW : D.IsSubconjugate W.subgroup :=
    (alternative.support411.nonzero_iff_isSubconjugate D defect.isPGroup).mp nonzeroD
  exact belowD.areConjugate_of_mutual belowW

include source in
/-- Local existence and uniqueness become an actual supported representative. -/
theorem representative_singleton :
    ∃ theta : RepresentativeDZ Nat.prime_two R ⟨D, source.radical⟩ b,
      ∀ eta : RepresentativeDZ Nat.prime_two R ⟨D, source.radical⟩ b, eta = theta := by
  letI := R.operations.ambientBlockData.fintypeBlock
  letI := (R.operations.inflatedNormalizerBlockData D).fintypeBlock
  obtain ⟨chi, hchi, localBlock, unique⟩ := source.local_character
  let thetaLocal : LocalDefectZeroCharacter (K := K) ⟨D, source.radical⟩ := ⟨chi, hchi⟩
  let W := characterWeightAt Nat.prime_two ⟨D, source.radical⟩ thetaLocal
  have support : R.operations.rawWeightBlock W = b := by
    change inducedBlock (Subgroup.normalizer (D : Set G3))
      (R.operations.inflatedNormalizerBlockData D).catalogue
      R.operations.ambientBlockData.catalogue
      (R.operations.inflateToNormalizer D
        (R.operations.localCharacterBlock D chi hchi))
      (R.operations.blockInductionDefined W) = b
    symm
    apply eq_inducedBlock_of_blockInducesTo
    rw [localBlock]
    exact source.correspondent_induces
  let theta : RepresentativeDZ Nat.prime_two R ⟨D, source.radical⟩ b :=
    ⟨thetaLocal, support⟩
  refine ⟨theta, ?_⟩
  intro eta
  let V := characterWeightAt Nat.prime_two ⟨D, source.radical⟩ eta.val
  have induces :
      BlockInducesTo (Subgroup.normalizer (D : Set G3))
        (R.operations.inflatedNormalizerBlockData D).catalogue
        R.operations.ambientBlockData.catalogue
        (R.operations.inflateToNormalizer D
          (R.operations.localCharacterBlock D eta.val.val eta.val.property)) b := by
    have selected :
        BlockInducesTo (Subgroup.normalizer (D : Set G3))
          (R.operations.inflatedNormalizerBlockData D).catalogue
          R.operations.ambientBlockData.catalogue
          (R.operations.inflateToNormalizer D
            (R.operations.localCharacterBlock D eta.val.val eta.val.property))
          (R.operations.rawWeightBlock V) :=
      inducedBlock_spec (Subgroup.normalizer (D : Set G3))
        (R.operations.inflatedNormalizerBlockData D).catalogue
        R.operations.ambientBlockData.catalogue _
        (R.operations.blockInductionDefined V)
    have hV : R.operations.rawWeightBlock V = b := eta.property
    exact Eq.mp (congrArg
      (fun block : LiteralPrimitiveBlock k G3 =>
        BlockInducesTo (Subgroup.normalizer (D : Set G3))
          (R.operations.inflatedNormalizerBlockData D).catalogue
          R.operations.ambientBlockData.catalogue
          (R.operations.inflateToNormalizer D
            (R.operations.localCharacterBlock D eta.val.val eta.val.property)) block)
      hV) selected
  have localEta := source.local_correspondent eta.val.val eta.val.property induces
  apply Subtype.ext
  apply Subtype.ext
  exact unique eta.val.val eta.val.property localEta

include source in
/-- Every supported global class lies over the same actual radical class. -/
theorem radical_class_eq (weight : R.Fibre b) :
    radicalClass weight.val =
      (Quotient.mk'' (⟨D, source.radical⟩ : RadicalSubgroup (p := 2) (G := G3)) :
        RadicalConjugacyClass (p := 2) (G := G3)) := by
  obtain ⟨iso, isoClass⟩ := Quotient.exists_rep weight.val
  obtain ⟨W, rawClass⟩ := Quotient.exists_rep iso
  have same :
      (Quotient.mk'' (Quotient.mk'' W) :
        ConjugacyClass (p := 2) (K := K) (G := G3)) = weight.val := by
    exact (congrArg
      (fun t : IsoClass (p := 2) (K := K) (G := G3) =>
        (Quotient.mk'' t : ConjugacyClass (p := 2) (K := K) (G := G3)))
      rawClass).trans isoClass
  have support : R.operations.rawWeightBlock W = b := by
    change R.weightBlock (Quotient.mk'' (Quotient.mk'' W)) = b
    exact (congrArg R.weightBlock same).trans weight.property
  obtain ⟨g, conjugate⟩ := supported_radical_conjugate
    Msys root calibration navarro R physical b ambientAt D defect cardD source W support
  have inverseConjugation : (MulAut.conj g).symm = MulAut.conj g⁻¹ := by
    change (MulAut.conj g)⁻¹ = MulAut.conj g⁻¹
    exact (map_inv (MulAut.conj : G3 →* MulAut G3) g).symm
  have radicalEquality :
      (⟨W.subgroup, W.radical⟩ : RadicalSubgroup (p := 2) (G := G3)) =
        RadicalSubgroup.rightTwist (p := 2) (G := G3)
          (⟨D, source.radical⟩ : RadicalSubgroup (p := 2) (G := G3))
          (MulAut.conj g⁻¹) := by
    apply Subtype.ext
    change W.subgroup = D.comap (MulAut.conj g⁻¹).toMonoidHom
    calc
      W.subgroup = D.map (MulAut.conj g).toMonoidHom := conjugate
      _ = D.comap (MulAut.conj g).symm.toMonoidHom :=
        Subgroup.map_equiv_eq_comap_symm (MulAut.conj g) D
      _ = D.comap (MulAut.conj g⁻¹).toMonoidHom := by rw [inverseConjugation]
  have orbit : MulAction.orbitRel G3 (RadicalSubgroup (p := 2) (G := G3))
      (⟨W.subgroup, W.radical⟩ : RadicalSubgroup (p := 2) (G := G3))
      (⟨D, source.radical⟩ : RadicalSubgroup (p := 2) (G := G3)) := by
    refine ⟨g, ?_⟩
    exact radicalEquality.symm
  exact (congrArg radicalClass same).symm.trans (Quotient.sound orbit)

include source in
/-- The complete supported weight fibre has one actual class. -/
theorem weight_fibre_singleton :
    ∃ weight : R.Fibre b, ∀ other : R.Fibre b, other = weight := by
  obtain ⟨theta, unique⟩ := representative_singleton
    Msys root calibration navarro R physical b ambientAt D defect cardD source
  let equivalence := representativeDZEquivWeightBlockRadicalFibre
    Nat.prime_two R (⟨D, source.radical⟩ : RadicalSubgroup (p := 2) (G := G3)) b
  let weight : R.Fibre b := ⟨(equivalence theta).val, (equivalence theta).property.1⟩
  refine ⟨weight, ?_⟩
  intro other
  let otherAtD : WeightBlockRadicalFibre R
      (⟨D, source.radical⟩ : RadicalSubgroup (p := 2) (G := G3)) b :=
    ⟨other.val, other.property,
      radical_class_eq Msys root calibration navarro R physical b ambientAt D defect cardD
        source other⟩
  have same : otherAtD = equivalence theta := by
    calc
      otherAtD = equivalence (equivalence.symm otherAtD) :=
        (equivalence.apply_symm_apply otherAtD).symm
      _ = equivalence theta := congrArg equivalence (unique (equivalence.symm otherAtD))
  apply Subtype.ext
  exact congrArg
    (fun w : WeightBlockRadicalFibre R
      (⟨D, source.radical⟩ : RadicalSubgroup (p := 2) (G := G3)) b => w.val) same

include source in
/-- Cardinality one is a consequence of the constructed singleton fibre. -/
theorem weight_fibre_card_one : Nat.card (R.Fibre b) = 1 :=
  Nat.card_eq_one_iff_exists.mpr
    (weight_fibre_singleton Msys root calibration navarro R physical b ambientAt D defect cardD
      source)

end ModularRep.PaperProofs.TypeBQ3B3NilpotentWeights


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
