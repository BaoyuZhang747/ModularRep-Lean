import ModularRep.PaperProofs.EvenFieldLemmas35_36Actual
import Mathlib.Data.ZMod.Basic

/-!
# The common unipotent pair in the CE and KM block labellings

This file proves the comparison used in Lemma 3.7. The two source label maps
are compared on the same pair through an actual common constituent of its
Lusztig induction. The resulting equality constructs the initial restricted
pair and reindexes the FMZ 7.5 map. No source field asserts the comparison
or the final Lemma 3.7 bijection.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC.PairLabelComparison

open ModularRep ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.PaperProofs
open EvenFieldConcreteTypeC EvenFieldFMZGenericPair EvenFieldEJGCPairActual
open EvenFieldAlgebraicTorusPairInertiaBridge EvenFieldLemmas35_36Actual
open EvenFieldOrdinaryCharacters

variable {H A Block k : Type} [Group H] [Fintype H]
  [MulAction (MulAut H) A] [Field k] [IsAlgClosed k]
  {ell : ℕ} [CharP k ell]
  (D : Definitions ℂ H A Block) (pairs : PairClassSource ell k D)

/-- The symplectic specialisation in even characteristic (U/E1). The e-split and
cuspidality predicates must refer to this same finite fixed point group and
multiplicative order. -/
structure TypeCSetting (r a : ℕ) where
  exponent_positive : 0 < a
  coefficient_prime : Nat.Prime ell
  coefficient_odd : ell ≠ 2
  fixedPointEquiv : H ≃* FiniteSymplecticFixed r a
  e : ℕ
  e_eq_order : e = orderOf ((2 ^ a : ℕ) : ZMod ell)

theorem TypeCSetting.nondefining {r a : ℕ}
    (setting : TypeCSetting (H := H) (ell := ell) r a) : ¬ ell ∣ 2 ^ a := by
  intro h
  have hd : ell ∣ 2 := setting.coefficient_prime.dvd_of_dvd_pow h
  exact setting.coefficient_odd
    ((Nat.prime_dvd_prime_iff_eq setting.coefficient_prime Nat.prime_two).mp hd)

/-- The coefficient of a complex irreducible character in the supplied virtual
character. Its support is defined from these coefficients. -/
def inductionCoefficient (induced : H → ℂ) (chi : Irr ℂ H) : ℂ :=
  (Fintype.card H : ℂ)⁻¹ * ∑ h : H, induced h * chi h⁻¹

/-- Source interpretations for the specified Levi subgroups and their
characters. Both block assignments use the same ordinary character block
map, identified with the block predicate and central characters.
Reduced ordinary central characters remain external data (E1/U). -/
structure LabelData (InBlock : Block → Irr ℂ H → Prop) where
  eSplit : A → Prop
  unipotent : RawPair D → Prop
  eCuspidal : RawPair D → Prop
  eJordanCuspidal : RawPair D → Prop
  ellPrimeSeries : RawPair D → Prop
  inL_eSplit : ∀ (C : Block) (P : RawPair D), D.inL C P.1 P.2 → eSplit P.1
  lusztigInduction : RawPair D → H → ℂ
  induction_classFunction : ∀ P h x,
    lusztigInduction P (h * x * h⁻¹) = lusztigInduction P x
  ceLabel : RawPair D → Block
  kmLabel : RawPair D → Block
  ordinaryBlock : Irr ℂ H → Block
  inBlock_iff : ∀ B chi, InBlock B chi ↔ ordinaryBlock chi = B
  reducedCentralCharacter : Irr ℂ H → GroupAlgebraCenter k H →ₐ[k] k
  catalogue_eq : letI := pairs.blockInduction.ambient.fintypeBlock
    ∀ chi, reducedCentralCharacter chi =
    pairs.blockInduction.ambient.catalogue.centralCharacter (ordinaryBlock chi)

namespace LabelData

variable {D pairs} {InBlock : Block → Irr ℂ H → Prop}
  (data : LabelData D pairs InBlock)

def InductionSupport (P : RawPair D) : Set (Irr ℂ H) :=
  {chi | inductionCoefficient (data.lusztigInduction P) chi ≠ 0}

def IsUnipotentECuspidal (P : RawPair D) : Prop :=
  data.eSplit P.1 ∧ data.unipotent P ∧ data.eCuspidal P

end LabelData

/-- The actual extension condition in the Levi's own character inertia
group. Its restriction is equality of complex character functions. -/
def ExtendsToOwnInertia (P : RawPair D) : Prop := by
  let B := finiteLeviInNormalizer D P.1
  letI : B.Normal := by
    dsimp [B, finiteLeviInNormalizer]
    infer_instance
  let lambda := finiteLeviNormalizerCharacter D P
  exact ∃ chiHat : Irr ℂ (characterInertia B lambda),
    ∀ x : baseInInertia B lambda,
      chiHat x.val = lambda ⟨x.val.val, x.property⟩

variable {r a : ℕ} (setting : TypeCSetting (H := H) (ell := ell) r a)
  {InBlock : Block → Irr ℂ H → Prop} (data : LabelData D pairs InBlock)

/-- The cited constituent statements concern the same groups and characters. KM
A(a) is the supporting clause on characters in a block implicit in the
manuscript's citation of A(e). These are constituent statements, not
equality of the label maps. The setting parameter fixes the applicable
symplectic/prime/order scope. -/
structure KMCESource (setting : TypeCSetting (H := H) (ell := ell) r a) where
  /-- KM Definition 2.1 and Remark 2.2(2), on unipotent characters. -/
  unipotent_cuspidality : ∀ P, data.eSplit P.1 → data.unipotent P →
    (data.eCuspidal P ↔ data.eJordanCuspidal P)
  unipotent_prime_series : ∀ P, data.unipotent P → data.ellPrimeSeries P
  /-- Nonempty generalised Harish-Chandra series in CE 4.4(i). -/
  ce_support_nonempty : ∀ P, data.IsUnipotentECuspidal P →
    (data.InductionSupport P).Nonempty
  /-- CE 4.4(i): all such constituents belong to its labelled block. -/
  ce_constituent_block : ∀ P, data.IsUnipotentECuspidal P →
    ∀ chi ∈ data.InductionSupport P, data.ordinaryBlock chi = data.ceLabel P
  /-- KM A(a), for the labelling used in A(e). -/
  km_constituent_block : ∀ P, data.eSplit P.1 → data.eJordanCuspidal P →
    data.ellPrimeSeries P → ∀ chi ∈ data.InductionSupport P,
      data.ordinaryBlock chi = data.kmLabel P
  /-- The FMZ (7.2) interpretation of the initial pair labelled by KM. -/
  km_initial_inL : ∀ P, data.IsUnipotentECuspidal P →
    data.eJordanCuspidal P → D.inL (data.kmLabel P) P.1 P.2

-- Keep the arithmetic setting as an explicit parameter of each
-- source instance, even though its mathematical interpretation is external.
-- The individual theorem fields above are all scoped to this realisation.

variable (source : KMCESource D pairs data setting)

include source in
/-- A common constituent belongs to both labelled blocks, so the labels agree on
the same pair. -/
theorem same_block_label (P : RawPair D) (hP : data.IsUnipotentECuspidal P) :
    data.ceLabel P = data.kmLabel P := by
  have hJordan := (source.unipotent_cuspidality P hP.1 hP.2.1).mp hP.2.2
  obtain ⟨chi, hchi⟩ := source.ce_support_nonempty P hP
  exact (source.ce_constituent_block P hP chi hchi).symm.trans
    (source.km_constituent_block P hP.1 hJordan
      (source.unipotent_prime_series P hP.2.1) chi hchi)

include source in
/-- The comparison also preserves the actual central characters. -/
theorem same_catalogue_label (P : RawPair D) (hP : data.IsUnipotentECuspidal P) :
    letI := pairs.blockInduction.ambient.fintypeBlock
    pairs.blockInduction.ambient.catalogue.centralCharacter (data.ceLabel P) =
      pairs.blockInduction.ambient.catalogue.centralCharacter (data.kmLabel P) := by
  rw [same_block_label D pairs setting data source P hP]

/-- Construct the initial element of `RestrictedPair C` from the original pair
labelled by CE. -/
def initialPair (P : RawPair D) (hP : data.IsUnipotentECuspidal P)
    (C : Block) (hC : data.ceLabel P = C) : pairs.RestrictedPair C := by
  refine ⟨P, ?_⟩
  have hJordan := (source.unipotent_cuspidality P hP.1 hP.2.1).mp hP.2.2
  have hlabel : data.kmLabel P = C :=
    (same_block_label D pairs setting data source P hP).symm.trans hC
  change D.inL C P.1 P.2
  rw [← hlabel]
  exact source.km_initial_inL P hP hJordan

@[simp] theorem initialPair_val (P : RawPair D) (hP : data.IsUnipotentECuspidal P)
    (C : Block) (hC : data.ceLabel P = C) :
    (initialPair D pairs setting data source P hP C hC).val = P := rfl

include source in
/-- The constructed pair has the induced block determined by the central
character catalogues, using the deduction from Feng–Malle–Zhang, Proposition
3.24. -/
theorem initialPair_blockInducesTo (P : RawPair D)
    (hP : data.IsUnipotentECuspidal P) (C : Block) (hC : data.ceLabel P = C) :
    pairs.blockInduction.BlockInducesTo P C :=
  pairs.restrictedPair_blockInducesTo
    (initialPair D pairs setting data source P hP C hC)

/-- Feng–Malle–Zhang's maximal extendibility hypothesis and Theorem 7.5, on the
specified e-split pairs and inertia quotients. The map uses the KM block
label. The preceding comparison identifies it with the block in the
manuscript. -/
structure FMZSource (setting : TypeCSetting (H := H) (ell := ell) r a) where
  proposition320 : ∀ P, data.eSplit P.1 → ExtendsToOwnInertia D P
  theorem75 : ∀ P, data.IsUnipotentECuspidal P → data.eJordanCuspidal P →
    (∀ Q, data.eSplit Q.1 → ExtendsToOwnInertia D Q) →
    Irr ℂ (pairs.RelativeWeylGroupAt P) ≃ pairs.DefectZeroUnion (data.kmLabel P)

variable {Dual CitedRelativeWeylGroup : Type} [Group Dual] [Group CitedRelativeWeylGroup]
  (coherence : InnerCoherence D) (Series : Irr ℂ H → Dual → Prop)
  (P : RawPair D) (hP : data.IsUnipotentECuspidal P)
  (C : Block) (hC : data.ceLabel P = C)
  (GeneralisedSeries : Set (Irr ℂ H))
  [Fintype (W D coherence C)] [Fintype (pairs.DefectZeroUnion C)]

/-- The remaining maps required by `CitedData`, for the same pair. The initial
pair and the map from Theorem 7.5 are constructed separately. -/
structure RemainingCitedData where
  /-- The definition identifies the generalised series with the
  actual induction support of this same pair. -/
  series_support : GeneralisedSeries = data.InductionSupport P
  ce44 : unipotentBlockPart (InBlock C) Series = GeneralisedSeries
  cs28 : Irr ℂ CitedRelativeWeylGroup ≃ ↑GeneralisedSeries
  relativeWeylIdentification : pairs.RelativeWeylGroupAt P ≃* CitedRelativeWeylGroup
  /-- The identifications from Feng–Malle–Zhang, Definitions 3.17–3.18, Lemma
3.21, the orbit count in Section 7.1, and Clifford uniqueness. The extension
hypothesis covers every pair in the specified union over blocks. -/
  genericWeightDictionary : (∀ Q : RawPair D, D.inL C Q.1 Q.2 → ExtendsToOwnInertia D Q) →
    Nonempty (pairs.DefectZeroUnion C ≃ W D coherence C)

/-- Construct `CitedData` after comparing the KM and CE labels. Its `initial`
field uses the same pair. The map from Theorem 7.5 is transported along the
proved equality of blocks. -/
def toCitedData (fmz : FMZSource D pairs data setting)
    (remaining : RemainingCitedData D pairs data coherence Series P C GeneralisedSeries
      (CitedRelativeWeylGroup := CitedRelativeWeylGroup) (InBlock := InBlock)) :
    EvenFieldLemmas35_36Actual.CitedData (CitedRelativeWeylGroup := CitedRelativeWeylGroup)
      ell (InBlock C) Series D coherence C pairs
      (initialPair D pairs setting data source P hP C hC) GeneralisedSeries where
  cabanesEnguehardTheorem44 := remaining.ce44
  cabanesSpathTheorem28 := remaining.cs28
  finiteRelativeWeylIdentification := remaining.relativeWeylIdentification
  fmzTheorem75 := by
    have hJordan := (source.unipotent_cuspidality P hP.1 hP.2.1).mp hP.2.2
    have hlabel : data.kmLabel P = C :=
      (same_block_label D pairs setting data source P hP).symm.trans hC
    have map := fmz.theorem75 P hP hJordan fmz.proposition320
    rw [hlabel] at map
    exact map
  fmzWeightCardinality :=
    (Fintype.card_congr (Classical.choice (remaining.genericWeightDictionary
      (fun Q hQ => fmz.proposition320 Q (data.inL_eSplit C Q hQ))))).symm

/-- State the predicate for each block using the specified ordinary characters,
pair and source maps. The complex coefficients are independent of the root
convention. -/
def toCitedDataFor (fmz : FMZSource D pairs data setting)
    (remaining : RemainingCitedData D pairs data coherence Series P C GeneralisedSeries
      (CitedRelativeWeylGroup := CitedRelativeWeylGroup) (InBlock := InBlock))
    (currentInBlock : Irr ℂ H → Prop) (predicate_eq : currentInBlock = InBlock C) :
    EvenFieldLemmas35_36Actual.CitedData (CitedRelativeWeylGroup := CitedRelativeWeylGroup)
      ell currentInBlock Series D coherence C pairs
      (initialPair D pairs setting data source P hP C hC) GeneralisedSeries := by
  cases predicate_eq
  exact toCitedData D pairs setting data source coherence Series P hP C hC
    GeneralisedSeries fmz remaining

end ManuscriptIBAW.TypeC.PairLabelComparison

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
