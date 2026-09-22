import ModularRep.OrdinaryBlockFibreCommonWitness

/-!
# Ordinary-block uniqueness from Navarro 9.9(c) and Spath 2.11

This nonmanifest experimental module keeps the two E1/U statements separate
and derives the
fixed-cover quotient-block equality in K.

The Navarro source is characterwise: conditional on an explicitly named
common ordinary character, it states both that inflation sends every member
of the quotient fibre into the fixed cover fibre and that every member of the
cover fibre is the inflation of a member of that quotient fibre.  It does not
store a set equality. Once a common witness is supplied, these two directions
are extensionally equivalent to the local image-fibre equality, not weaker
than that equality.

The Spath source stores only the one-way inclusion of the inflated fibre of
the caller-designated quotient-block label in the fixed cover fibre. The
caller must independently identify that label with the selected induced
quotient block in a concrete application. Selector
surjectivity and the existing neutral adapter construct the second common
ordinary character in K.

No field contains the desired quotient-block equality, a preassembled fibre
equality, a character triple, a weight, BAW, or iBAW.
-/

noncomputable section

namespace ModularRep.Navarro99cSpath211OrdinaryBlockUniqueness

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.OrdinaryBlockFibre
open ModularRep.OrdinaryBlockFibreCommonWitness

universe u v w

/-- E1/U literal ordinary-character rendering of Navarro (9.9)(c), scoped
to the exact prime, prime-to-kernel quotient map, and block selectors.

The two directions are bundled in one proof field.  The field is conditional
on a common character and uses the same `pi`, `hpi`, `quotientBlockOf`, and
`coverBlockOf` in both directions. -/
structure Navarro99cOrdinaryFibreCorrespondenceSource
    {K CoverG QuotientG : Type u}
    {CoverBlock : Type v} {QuotientBlock : Type w}
    [Field K] [CharZero K] [Group CoverG] [Group QuotientG]
    [Finite CoverG] [Finite QuotientG]
    (p : Nat) (hp : p.Prime)
    (pi : CoverG →* QuotientG) (hpi : Function.Surjective pi)
    (hkernelPrimeTo : ¬ p ∣ Nat.card pi.ker)
    (quotientBlockOf :
      OrdinaryIrreducibleCharacter.Irr K QuotientG -> QuotientBlock)
    (coverBlockOf :
      OrdinaryIrreducibleCharacter.Irr K CoverG -> CoverBlock) : Prop where
  characterwise_of_common :
    ∀ {q : QuotientBlock} {B : CoverBlock},
      CommonInflatedOrdinaryCharacter pi hpi
          quotientBlockOf coverBlockOf q B ->
        (∀ chi, quotientBlockOf chi = q ->
          coverBlockOf (inflateAlong pi hpi chi) = B) ∧
        (∀ eta, coverBlockOf eta = B ->
          ∃ chi, quotientBlockOf chi = q ∧
            inflateAlong pi hpi chi = eta)

/-- E1/U literal one-way ordinary-fibre output of Spath, Corollary 2.11,
after its source hypotheses and exact carrier bindings have been discharged.
The caller-designated qind is not identified with an induced block by this API.
It contains neither a reverse implication nor a selected character. -/
structure Spath211OrdinaryFibreInclusionSource
    {K CoverG QuotientG : Type u}
    {CoverBlock : Type v} {QuotientBlock : Type w}
    [Field K] [CharZero K] [Group CoverG] [Group QuotientG]
    (pi : CoverG →* QuotientG) (hpi : Function.Surjective pi)
    (quotientBlockOf :
      OrdinaryIrreducibleCharacter.Irr K QuotientG -> QuotientBlock)
    (coverBlockOf :
      OrdinaryIrreducibleCharacter.Irr K CoverG -> CoverBlock)
    (qind : QuotientBlock) (B : CoverBlock) : Prop where
  inflated_fibre_subset :
    Set.image (inflateAlong pi hpi)
        (ordinaryBlockFibreSet quotientBlockOf qind) ≤
      ordinaryBlockFibreSet coverBlockOf B

/-- Fixed-cover quotient-block uniqueness.

`h_bbar_B` is the first common witness, comparing `bbar` with `B`.
`S211` is indexed by `qind` and the same `B`; its one-way inclusion constructs
the second common witness comparing `qind` with `B`.  The Navarro source then
gives the two characterwise correspondences, from which the proof derives
the necessary set equalities locally before applying fibre-label
injectivity. -/
theorem quotientBlock_eq_of_first_common_and_spath211
    {K CoverG QuotientG : Type u}
    {CoverBlock : Type v} {QuotientBlock : Type w}
    [Field K] [CharZero K] [Group CoverG] [Group QuotientG]
    [Finite CoverG] [Finite QuotientG]
    (p : Nat) (hp : p.Prime)
    (pi : CoverG →* QuotientG) (hpi : Function.Surjective pi)
    (hkernelPrimeTo : ¬ p ∣ Nat.card pi.ker)
    (quotientBlockOf :
      OrdinaryIrreducibleCharacter.Irr K QuotientG -> QuotientBlock)
    (coverBlockOf :
      OrdinaryIrreducibleCharacter.Irr K CoverG -> CoverBlock)
    (S99 : Navarro99cOrdinaryFibreCorrespondenceSource
      p hp pi hpi hkernelPrimeTo quotientBlockOf coverBlockOf)
    (hquotientBlockOf : Function.Surjective quotientBlockOf)
    {bbar qind : QuotientBlock} {B : CoverBlock}
    (h_bbar_B : CommonInflatedOrdinaryCharacter
      pi hpi quotientBlockOf coverBlockOf bbar B)
    (S211 : Spath211OrdinaryFibreInclusionSource
      pi hpi quotientBlockOf coverBlockOf qind B) :
    bbar = qind := by
  have h_qind_B : CommonInflatedOrdinaryCharacter
      pi hpi quotientBlockOf coverBlockOf qind B :=
    commonInflatedOrdinaryCharacter_of_image_fibre_subset
      pi hpi quotientBlockOf coverBlockOf
      hquotientBlockOf S211.inflated_fibre_subset
  have image_eq_of_common :
      ∀ {q : QuotientBlock},
        CommonInflatedOrdinaryCharacter
            pi hpi quotientBlockOf coverBlockOf q B ->
          Set.image (inflateAlong pi hpi)
              (ordinaryBlockFibreSet quotientBlockOf q) =
            ordinaryBlockFibreSet coverBlockOf B := by
    intro q h_q_B
    rcases S99.characterwise_of_common h_q_B with
      ⟨hforward, hbackward⟩
    ext eta
    constructor
    · rintro ⟨chi, hchi, rfl⟩
      change quotientBlockOf chi = q at hchi
      change coverBlockOf (inflateAlong pi hpi chi) = B
      exact hforward chi hchi
    · intro heta
      change coverBlockOf eta = B at heta
      obtain ⟨chi, hchi, hinflate⟩ := hbackward eta heta
      refine ⟨chi, ?_, hinflate⟩
      change quotientBlockOf chi = q
      exact hchi
  apply imageOrdinaryBlockFibreSet_injective
    quotientBlockOf (inflateAlong pi hpi)
    hquotientBlockOf (inflateAlong_injective pi hpi)
  exact (image_eq_of_common h_bbar_B).trans
    (image_eq_of_common h_qind_B).symm

end ModularRep.Navarro99cSpath211OrdinaryBlockUniqueness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
