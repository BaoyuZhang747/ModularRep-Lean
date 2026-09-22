import ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier

/-!
# A unique local character binds the selected actual weight pair

An, (4G), p. 191, and equation (6.1), p. 195, describe local defect-zero
characters for the named basic subgroups. The wreath factors contribute
their Steinberg characters. For the symplectic `x - 1` families, the local
character for each fixed basic subgroup is unique except when `a = 2` and
the Feng--Malle parameter `gamma = 0`. That exception has three characters,
including after the wreath construction. Feng--Malle, Lemma 5.1 and its
proof, pp. 11--12, retain this distinction: when `a > 2` and `gamma = 0`,
the three characters instead belong to three different subgroup classes.

The narrow E2 input below is uniqueness on the actual normaliser quotient
of a specified subgroup. Authenticating that subgroup as one of the
nonexceptional source subgroups, and authenticating the ordinary splitting
field, remain source obligations. No source instance, family-wide
uniqueness, or uniqueness in the three-character exception is declared.

K: uniqueness gives equality of transported local character functions,
then equality of actual raw weight pairs, and then equality in the same
intrinsic principal fibre after actual conjugation. The character equality
and weight-class equality are conclusions, not source premises.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

section ActualLocalCharacters

variable {K G : Type u} [Field K] [CharZero K] [Group G] [Finite G]

/-- Actual ordinary defect-zero characters of the specified normaliser
quotient. A source uniqueness hypothesis on this type identifies functions,
not merely names or members of an unrelated set of characters. -/
abbrev LocalDefectZeroCharacters (R : Subgroup G) :=
  {chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient R) //
    IsDefectZeroOrdinaryCharacter 2 chi}

theorem castLocalCharacter_defectZero
    {Q R : Subgroup G} (hQ : Q = R)
    {chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)}
    (hchi : IsDefectZeroOrdinaryCharacter 2 chi) :
    IsDefectZeroOrdinaryCharacter 2 (castLocalCharacter hQ chi) := by
  subst R
  exact hchi

theorem localCharacter_eq_of_unique
    {R : Subgroup G}
    (unique : Subsingleton (LocalDefectZeroCharacters (K := K) R))
    {chi psi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient R)}
    (hchi : IsDefectZeroOrdinaryCharacter 2 chi)
    (hpsi : IsDefectZeroOrdinaryCharacter 2 psi) :
    chi = psi := by
  letI := unique
  exact congrArg Subtype.val (Subsingleton.elim
    (show LocalDefectZeroCharacters (K := K) R from ⟨chi, hchi⟩)
    (show LocalDefectZeroCharacters (K := K) R from ⟨psi, hpsi⟩))

theorem castLocalCharacter_eq_of_unique
    {Q R : Subgroup G} (hQ : Q = R)
    (unique : Subsingleton (LocalDefectZeroCharacters (K := K) R))
    {chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)}
    {psi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient R)}
    (hchi : IsDefectZeroOrdinaryCharacter 2 chi)
    (hpsi : IsDefectZeroOrdinaryCharacter 2 psi) :
    castLocalCharacter hQ chi = psi :=
  localCharacter_eq_of_unique unique
    (castLocalCharacter_defectZero hQ hchi) hpsi

/-- At an actual subgroup with a unique local defect-zero character, the
subgroup determines the complete raw character-weight pair. -/
theorem characterWeight_eq_of_subgroup_eq_of_unique
    {W V : CharacterWeight 2 K G} (hQ : W.subgroup = V.subgroup)
    (unique : Subsingleton (LocalDefectZeroCharacters (K := K) V.subgroup)) :
    W = V :=
  eq_of_isomorphic ⟨hQ,
    castLocalCharacter_eq_of_unique hQ unique W.defectZero V.defectZero⟩

theorem weightsOverSubgroup_subsingleton
    (R : Subgroup G)
    (unique : Subsingleton (LocalDefectZeroCharacters (K := K) R)) :
    Subsingleton {W : CharacterWeight 2 K G // W.subgroup = R} := by
  constructor
  intro W V
  apply Subtype.ext
  have hV : Subsingleton (LocalDefectZeroCharacters (K := K) V.1.subgroup) := by
    rw [V.2]
    exact unique
  exact characterWeight_eq_of_subgroup_eq_of_unique (W.2.trans V.2.symm) hV

/-- The local character is transported by the existing actual automorphism
action. Its equality is deduced from uniqueness at the target subgroup. -/
theorem rightTwist_eq_of_subgroup_eq_of_unique
    {W V : CharacterWeight 2 K G} (alpha : MulAut G)
    (hQ : (W.rightTwist alpha).subgroup = V.subgroup)
    (unique : Subsingleton (LocalDefectZeroCharacters (K := K) V.subgroup)) :
    W.rightTwist alpha = V :=
  characterWeight_eq_of_subgroup_eq_of_unique hQ unique

/-- Genuine ambient conjugacy of the selected subgroups, together with
local uniqueness, identifies the actual weight conjugacy classes. -/
theorem weightClass_eq_of_conjugate_subgroup_of_unique
    {W V : CharacterWeight 2 K G} (g : G)
    (hQ : (W.rightTwist (MulAut.conj g⁻¹)).subgroup = V.subgroup)
    (unique : Subsingleton (LocalDefectZeroCharacters (K := K) V.subgroup)) :
    (Quotient.mk'' (Quotient.mk'' W) :
      CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G)) =
      Quotient.mk'' (Quotient.mk'' V) := by
  symm
  apply Quotient.sound
  refine ⟨g, ?_⟩
  change (Quotient.mk'' (W.rightTwist (MulAut.conj g⁻¹)) :
    CharacterWeight.IsoClass (p := 2) (K := K) (G := G)) = Quotient.mk'' V
  rw [rightTwist_eq_of_subgroup_eq_of_unique (MulAut.conj g⁻¹) hQ unique]

end ActualLocalCharacters

section IntrinsicPrincipalFibre

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))

/-- This conclusion concerns the fixed intrinsic fibre used for both FYZ
and Feng--Malle. It does not compare arbitrary independently named carriers. -/
theorem principalWeight_eq_of_conjugate_selected_subgroup_of_unique
    (w v : D.PrincipalWeight) (g : Sp n F)
    (hQ : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
      (MulAut.conj g⁻¹)).subgroup =
        (selectedCharacterWeight D.blockSource D.principalBlock v).subgroup)
    (unique : Subsingleton (LocalDefectZeroCharacters (K := K)
      (selectedCharacterWeight D.blockSource D.principalBlock v).subgroup)) :
    w = v := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  apply Subtype.ext
  have h := weightClass_eq_of_conjugate_subgroup_of_unique g hQ unique
  exact (selectedCharacterWeight_spec D.blockSource D.principalBlock w).symm.trans
    (h.trans (selectedCharacterWeight_spec D.blockSource D.principalBlock v))

theorem principalWeight_eq_of_selected_subgroup_eq_of_unique
    (w v : D.PrincipalWeight)
    (hQ : (selectedCharacterWeight D.blockSource D.principalBlock w).subgroup =
      (selectedCharacterWeight D.blockSource D.principalBlock v).subgroup)
    (unique : Subsingleton (LocalDefectZeroCharacters (K := K)
      (selectedCharacterWeight D.blockSource D.principalBlock v).subgroup)) :
    w = v := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  apply Subtype.ext
  have h := characterWeight_eq_of_subgroup_eq_of_unique hQ unique
  calc
    w.1 = (Quotient.mk'' (Quotient.mk''
        (selectedCharacterWeight D.blockSource D.principalBlock w)) :
          CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Sp n F)) :=
      (selectedCharacterWeight_spec D.blockSource D.principalBlock w).symm
    _ = Quotient.mk'' (Quotient.mk''
        (selectedCharacterWeight D.blockSource D.principalBlock v)) := by rw [h]
    _ = v.1 := selectedCharacterWeight_spec D.blockSource D.principalBlock v

/-! The following slice starts with an actual An/FM raw pair, without
assuming it lies in the principal block. For a source application, the
subgroup conjugacy comes from the appropriate basic x-1 construction and
the uniqueness clause comes from An (4G)/(6.1). In particular this is not
a uniqueness assertion for arbitrary orthogonal products of basic factors
or for the a=2, gamma=0 three-character exception. -/

variable (w : D.PrincipalWeight) (V : CharacterWeight 2 K (Sp n F))
variable (g : Sp n F)
variable (hQ : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
  (MulAut.conj g⁻¹)).subgroup = V.subgroup)
variable (unique : Subsingleton (LocalDefectZeroCharacters (K := K) V.subgroup))

include w V g hQ unique

/-- The source pair has the original intrinsic weight class. Its principal
membership is not a premise. Only the subgroup conjugacy and actual local
uniqueness are used to identify the selected character. -/
theorem conjugateUniquePair_class :
    (Quotient.mk'' (Quotient.mk'' V) :
      CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Sp n F)) = w.1 := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  exact (weightClass_eq_of_conjugate_subgroup_of_unique g hQ unique).symm.trans
    (selectedCharacterWeight_spec D.blockSource D.principalBlock w)

/-- Principal block membership of the An/FM raw pair follows from the
proved class equation, not from a principal tag on that pair. -/
theorem conjugateUniquePair_principalBlock :
    D.blockSource.operations.rawWeightBlock V = D.principalBlock := by
  have h := congrArg D.blockSource.weightBlock
    (conjugateUniquePair_class D w V g hQ unique)
  exact h.trans w.2

/-- The actual Feng--Malle principal weight represented by the source pair.
No equivalence with an independently named weight universe is supplied. -/
def fengMalleWeightOfConjugateUnique : D.FengMallePrincipalWeight :=
  ⟨Quotient.mk'' (Quotient.mk'' V),
    conjugateUniquePair_principalBlock D w V g hQ unique⟩

theorem fengMalleWeightOfConjugateUnique_eq :
    fengMalleWeightOfConjugateUnique D w V g hQ unique =
      D.intrinsicWeightEquiv w := by
  apply Subtype.ext
  exact conjugateUniquePair_class D w V g hQ unique

/-- Block induction uses V's own subgroup and selected ordinary character,
including its actual inflation to the normalizer. -/
theorem conjugateUniquePair_blockInducesTo :
    let O := D.blockSource.operations
    let localData := O.inflatedNormalizerBlockData V.subgroup
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    ModularRep.BlockInducesTo
      (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer V.subgroup
        (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
      D.principalBlock := by
  let O := D.blockSource.operations
  let localData := O.inflatedNormalizerBlockData V.subgroup
  letI := O.ambientBlockData.fintypeBlock
  letI := localData.fintypeBlock
  have hblock : O.induceToAmbient V = D.principalBlock :=
    conjugateUniquePair_principalBlock D w V g hQ unique
  change ModularRep.BlockInducesTo
    (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer V.subgroup
      (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
    D.principalBlock
  rw [← hblock]
  exact ModularRep.inducedBlock_spec
    (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer V.subgroup
      (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
    (O.blockInductionDefined V)

end IntrinsicPrincipalFibre

end ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
