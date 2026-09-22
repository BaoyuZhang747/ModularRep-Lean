import ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase
import Mathlib.Data.Fintype.Sum

/-!
# Canonical Type-B q=3 weight routing

This module gives exact and global-faithful-swap finite routing interfaces over
the canonical literal primitive-block action. The latter permits one
identity-or-faithful-sector swap fixed before quantification over labels; it
does not choose the orientation or identify a raw row with B6 or B7.
It does not assert the final correspondence as an assumption.

The central-sector adapters make their E1/E3/U inputs explicit: an injective
realisation of transcript tags as literal central characters, block-sector
coherence, and raw-output sector coherence. The cardinality results consume
those inputs rather than infer them from transcript totals.

The resulting fibres are `R.Fibre (primitiveBlockOfLabel blocks i)`, i.e.
fibres over a selected catalogue index whose carrier is a literal primitive
block. Interpreting them as fibres over the catalogue idempotent `b.1`
additionally requires the separate literal-catalogue coherence
`R.operations.ambientBlockData.blockIdempotent b = b.1`.
This additional identification is not included among the routing hypotheses.

The literal-carrier import supplies the canonical right action only; this
module has no An--Dietrich, Q=1, signature, cancellation, or iBAW dependency.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual

open Formalisation.ComputationArithmetic
open ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Relative
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharZero K] [Group X] [Fintype X]
variable [CharP k 2] [IsAlgClosed k]
variable {blockIdempotent : Q3Block -> k[X]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

/-! ## Canonical reindexing of the selected block index -/

/-- Reindex the `PrimitiveBlock k X`-valued result of `R.weightBlock` through
the complete `primitiveBlockEquiv`.  The `LocalBlockInductionSource` is formed
using the canonical `LiteralPrimitiveBlock.rightMulAction` supplied by the
literal carrier import; there is no unrelated free block-action parameter. -/
def canonicalWeightBlockRouting
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X)) :
    WeightBlockRouting where
  blockOf label :=
    (primitiveBlockEquiv blocks).symm
      (R.weightBlock (M.classOfLabel label))

/-- Canonical reindexing supplies the existing generic output-fibre
compatibility by the inverse law alone.  It says nothing about the ambient
catalogue idempotent map and nothing about a sector or a cardinality. -/
theorem canonicalWeightBlockRouting_compatible
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X)) :
    WeightBlockFibreCompatible blocks R M
      (canonicalWeightBlockRouting blocks R M) := by
  intro label
  change R.weightBlock (M.classOfLabel label) =
    (primitiveBlockEquiv blocks)
      ((primitiveBlockEquiv blocks).symm
        (R.weightBlock (M.classOfLabel label)))
  exact ((primitiveBlockEquiv blocks).apply_symm_apply
    (R.weightBlock (M.classOfLabel label))).symm

/-! ## Explicit transcript-sector boundary -/

/-- The exact non-numerical compatibility needed by the finite cancellation.
It binds a printed occurrence only to its *central sector*, not to a
particular `B6`/`B7` block or to a final Brauer--weight correspondence. -/
def canonicalWeightRoutingSectorCompatible
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X)) : Prop :=
  ∀ label,
    q3Sector ((canonicalWeightBlockRouting blocks R M).blockOf label) =
      label.sector

/-- The global-faithful-swap alternative to exact transcript-sector compatibility.
One sigma is chosen before the label quantifier and is either identity or the
existing finite faithful-sector swap. sectorOuterAction is used only as a
three-constructor enum action; no realised outer automorphism is an input or
conclusion. -/
def canonicalWeightRoutingSectorCompatibleUpToFaithfulSwap
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X)) : Prop :=
  ∃ σ : Equiv.Perm Q3Sector,
    (σ = Equiv.refl Q3Sector ∨ σ = sectorOuterAction) ∧
      ∀ label,
        q3Sector ((canonicalWeightBlockRouting blocks R M).blockOf label) =
          σ label.sector
section CentralSectorInterpretation

noncomputable local instance canonicalRoutingCenterFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable [Invertible (Fintype.card (Subgroup.center X) : k)]

/-- A lower, source-visible route to the preceding finite compatibility.

`nu` is an injective realisation of the three transcript tags as literal
central characters.  The first binding anchors named computed blocks to their
literal primitive idempotents; the second anchors each raw output occurrence
to the selected block-index sector.  These are precisely the facts absent
from the current transcript certificate.  This lemma uses no count and no
blockwise correspondence conclusion. -/
theorem canonicalWeightRoutingSectorCompatible_of_centralSectorData
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (nu : Q3Sector → CentralSector (k := k) (X := X))
    (nu_injective : Function.Injective nu)
    (block_sector : ∀ block,
      blockSector (k := k) (X := X) (primitiveBlockOfLabel blocks block) =
        nu (q3Sector block))
    (row_sector : ∀ label,
      blockSector (k := k) (X := X)
          (R.weightBlock (M.classOfLabel label)) =
        nu label.sector) :
    canonicalWeightRoutingSectorCompatible blocks R M := by
  intro label
  apply nu_injective
  calc
    nu (q3Sector ((canonicalWeightBlockRouting blocks R M).blockOf label)) =
        blockSector (k := k) (X := X)
          (primitiveBlockOfLabel blocks
            ((canonicalWeightBlockRouting blocks R M).blockOf label)) :=
      (block_sector _).symm
    _ = blockSector (k := k) (X := X)
          (R.weightBlock (M.classOfLabel label)) := by
      rw [← canonicalWeightBlockRouting_compatible blocks R M label]
    _ = nu label.sector := row_sector label

/-- The lower adapter for global-faithful-swap compatibility. Its residual
source fact is an actual row-sector coherence equation, possibly after one
global faithful-tag swap. It neither identifies a raw row with a named block
nor supplies a cardinality. -/
theorem canonicalWeightRoutingSectorCompatibleUpToFaithfulSwap_of_centralSectorData
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (nu : Q3Sector → CentralSector (k := k) (X := X))
    (nu_injective : Function.Injective nu)
    (σ : Equiv.Perm Q3Sector)
    (sigma_cases : σ = Equiv.refl Q3Sector ∨ σ = sectorOuterAction)
    (block_sector : ∀ block,
      blockSector (k := k) (X := X) (primitiveBlockOfLabel blocks block) =
        nu (q3Sector block))
    (row_sector : ∀ label,
      blockSector (k := k) (X := X)
          (R.weightBlock (M.classOfLabel label)) =
        nu (σ label.sector)) :
    canonicalWeightRoutingSectorCompatibleUpToFaithfulSwap blocks R M := by
  refine ⟨σ, sigma_cases, ?_⟩
  intro label
  apply nu_injective
  calc
    nu (q3Sector ((canonicalWeightBlockRouting blocks R M).blockOf label)) =
        blockSector (k := k) (X := X)
          (primitiveBlockOfLabel blocks
            ((canonicalWeightBlockRouting blocks R M).blockOf label)) :=
      (block_sector _).symm
    _ = blockSector (k := k) (X := X)
          (R.weightBlock (M.classOfLabel label)) := by
      rw [← canonicalWeightBlockRouting_compatible blocks R M label]
    _ = nu (σ label.sector) := row_sector label
end CentralSectorInterpretation

/-! ## Kernel fibre partition -/

/-- Partition one printed sector fibre into the two routed block fibres in
that sector.  The exhaustive two-block condition is discharged by cases for
the fixed `Q3Sector` data below; it is not supplied as a count equation. -/
def routedSectorPairFibreEquiv
    (routing : WeightBlockRouting)
    (sector_compatible : ∀ label,
      q3Sector (routing.blockOf label) = label.sector)
    {sector : Q3Sector} {left right : Q3Block}
    (left_sector : q3Sector left = sector)
    (right_sector : q3Sector right = sector)
    (left_ne_right : left ≠ right)
    (exhaustive : ∀ block, q3Sector block = sector →
      block = left ∨ block = right) :
    {label : WeightOutputLabel // label.sector = sector} ≃
      WeightOutputFibre routing left ⊕ WeightOutputFibre routing right :=
  (Equiv.ofBijective
    (β := {label : WeightOutputLabel // label.sector = sector})
    (fun x : WeightOutputFibre routing left ⊕ WeightOutputFibre routing right =>
      match x with
      | .inl x =>
          ⟨x.1, by
            calc
              x.1.sector = q3Sector (routing.blockOf x.1) :=
                (sector_compatible x.1).symm
              _ = q3Sector left := congrArg q3Sector x.2
              _ = sector := left_sector⟩
      | .inr x =>
          ⟨x.1, by
            calc
              x.1.sector = q3Sector (routing.blockOf x.1) :=
                (sector_compatible x.1).symm
              _ = q3Sector right := congrArg q3Sector x.2
              _ = sector := right_sector⟩)
    (by
      constructor
      · intro x y hxy
        rcases x with x | x <;> rcases y with y | y
        · exact congrArg Sum.inl
            (Subtype.ext (congrArg
              (fun z : {label : WeightOutputLabel // label.sector = sector} =>
                z.1) hxy))
        · exact False.elim (left_ne_right (by
            calc
              left = routing.blockOf x.1 := x.2.symm
              _ = routing.blockOf y.1 :=
                congrArg routing.blockOf (congrArg Subtype.val hxy)
              _ = right := y.2))
        · exact False.elim (left_ne_right (by
            calc
              left = routing.blockOf y.1 := y.2.symm
              _ = routing.blockOf x.1 :=
                congrArg routing.blockOf (congrArg Subtype.val hxy).symm
              _ = right := x.2))
        · exact congrArg Sum.inr
            (Subtype.ext (congrArg
              (fun z : {label : WeightOutputLabel // label.sector = sector} =>
                z.1) hxy))
      · intro label
        have routed_sector : q3Sector (routing.blockOf label.1) = sector := by
          calc
            q3Sector (routing.blockOf label.1) = label.1.sector :=
              sector_compatible label.1
            _ = sector := label.2
        rcases exhaustive (routing.blockOf label.1) routed_sector with hleft | hright
        · refine ⟨Sum.inl ⟨label.1, hleft⟩, ?_⟩
          apply Subtype.ext
          rfl
        · refine ⟨Sum.inr ⟨label.1, hright⟩, ?_⟩
          apply Subtype.ext
          rfl)).symm

/-! ## The faithful-sector subtraction -/

/-- The manuscript's `8 - 2 = 6` calculation on actual output and
local-induction fibres.

The two faithful-sector sum equations are produced by
`routedSectorPairFibreEquiv`; they are not hypotheses.  The known `B8` and
`B9` inputs are cardinalities of the genuine local-induction fibres.  They
are transferred to output fibres by the already kernel-built
`weightBlockFibreEquiv`. -/
theorem canonical_faithful_output_cards
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (map_injective : Function.Injective M.classOfLabel)
    (map_surjective : Function.Surjective M.classOfLabel)
    (sector_compatible : canonicalWeightRoutingSectorCompatible blocks R M)
    (B8_weight_fibre_card :
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B8)) = 2)
    (B9_weight_fibre_card :
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B9)) = 2) :
    Fintype.card
        (WeightOutputFibre (canonicalWeightBlockRouting blocks R M) .B6) =
        q3BrauerCount .B6 ∧
      Fintype.card
        (WeightOutputFibre (canonicalWeightBlockRouting blocks R M) .B7) =
        q3BrauerCount .B7 := by
  let routing : WeightBlockRouting := canonicalWeightBlockRouting blocks R M
  have routing_sector : ∀ label,
      q3Sector (routing.blockOf label) = label.sector := by
    simpa only [routing, canonicalWeightRoutingSectorCompatible] using
      sector_compatible
  have routing_compatible : WeightBlockFibreCompatible blocks R M routing := by
    simpa only [routing] using
      (canonicalWeightBlockRouting_compatible blocks R M)
  have B8_output_fibre_natCard :
      Nat.card (WeightOutputFibre routing .B8) = 2 := by
    calc
      Nat.card (WeightOutputFibre routing .B8) =
          Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B8)) :=
        Nat.card_congr (weightBlockFibreEquiv blocks R M routing
          map_injective map_surjective routing_compatible .B8)
      _ = 2 := B8_weight_fibre_card
  have B9_output_fibre_natCard :
      Nat.card (WeightOutputFibre routing .B9) = 2 := by
    calc
      Nat.card (WeightOutputFibre routing .B9) =
          Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B9)) :=
        Nat.card_congr (weightBlockFibreEquiv blocks R M routing
          map_injective map_surjective routing_compatible .B9)
      _ = 2 := B9_weight_fibre_card
  have B8_output_fibre_card :
      Fintype.card (WeightOutputFibre routing .B8) = 2 := by
    simpa only [← Nat.card_eq_fintype_card] using B8_output_fibre_natCard
  have B9_output_fibre_card :
      Fintype.card (WeightOutputFibre routing .B9) = 2 := by
    simpa only [← Nat.card_eq_fintype_card] using B9_output_fibre_natCard
  have faithfulOne_equiv :
      {label : WeightOutputLabel // label.sector = .faithfulOne} ≃
        WeightOutputFibre routing .B6 ⊕ WeightOutputFibre routing .B8 :=
    routedSectorPairFibreEquiv routing routing_sector
      (sector := .faithfulOne) (left := .B6) (right := .B8)
      (by rfl) (by rfl) (by decide) (by
        intro block hblock
        cases block <;> simp [q3Sector] at hblock ⊢)
  have faithfulTwo_equiv :
      {label : WeightOutputLabel // label.sector = .faithfulTwo} ≃
        WeightOutputFibre routing .B7 ⊕ WeightOutputFibre routing .B9 :=
    routedSectorPairFibreEquiv routing routing_sector
      (sector := .faithfulTwo) (left := .B7) (right := .B9)
      (by rfl) (by rfl) (by decide) (by
        intro block hblock
        cases block <;> simp [q3Sector] at hblock ⊢)
  have faithfulOne_sum :
      Fintype.card (WeightOutputFibre routing .B6) +
        Fintype.card (WeightOutputFibre routing .B8) = 8 := by
    calc
      Fintype.card (WeightOutputFibre routing .B6) +
          Fintype.card (WeightOutputFibre routing .B8) =
          Fintype.card
            (WeightOutputFibre routing .B6 ⊕ WeightOutputFibre routing .B8) :=
        Fintype.card_sum.symm
      _ = Fintype.card
          {label : WeightOutputLabel // label.sector = .faithfulOne} :=
        (Fintype.card_congr faithfulOne_equiv).symm
      _ = 8 := WeightOutputLabel.sector_fibre_card_exact.2.1
  have faithfulTwo_sum :
      Fintype.card (WeightOutputFibre routing .B7) +
        Fintype.card (WeightOutputFibre routing .B9) = 8 := by
    calc
      Fintype.card (WeightOutputFibre routing .B7) +
          Fintype.card (WeightOutputFibre routing .B9) =
          Fintype.card
            (WeightOutputFibre routing .B7 ⊕ WeightOutputFibre routing .B9) :=
        Fintype.card_sum.symm
      _ = Fintype.card
          {label : WeightOutputLabel // label.sector = .faithfulTwo} :=
        (Fintype.card_congr faithfulTwo_equiv).symm
      _ = 8 := WeightOutputLabel.sector_fibre_card_exact.2.2
  have forced := faithful_sector_counts_forced
    (fun block => Fintype.card (WeightOutputFibre routing block))
    faithfulOne_sum faithfulTwo_sum B8_output_fibre_card B9_output_fibre_card
  constructor
  · simpa only [routing, q3BrauerCount] using forced.1
  · simpa only [routing, q3BrauerCount] using forced.2

/-! ## Global faithful-swap route -/

/-- Partition a fixed named block sector using raw labels transported by one
global sector permutation.  The permutation is an argument outside the label
quantifier; this lemma itself does not permit rowwise permutations or a block
permutation. -/
def routedSectorPairFibreEquiv_of_globalFaithfulSwap
    (routing : WeightBlockRouting)
    (σ : Equiv.Perm Q3Sector)
    (sector_compatible : ∀ label,
      q3Sector (routing.blockOf label) = σ label.sector)
    {sector : Q3Sector} {left right : Q3Block}
    (left_sector : q3Sector left = sector)
    (right_sector : q3Sector right = sector)
    (left_ne_right : left ≠ right)
    (exhaustive : ∀ block, q3Sector block = sector →
      block = left ∨ block = right) :
    {label : WeightOutputLabel // label.sector = σ.symm sector} ≃
      WeightOutputFibre routing left ⊕ WeightOutputFibre routing right :=
  (Equiv.ofBijective
    (β := {label : WeightOutputLabel // label.sector = σ.symm sector})
    (fun x : WeightOutputFibre routing left ⊕ WeightOutputFibre routing right =>
      match x with
      | .inl x =>
          ⟨x.1, by
            apply σ.injective
            calc
              σ x.1.sector = q3Sector (routing.blockOf x.1) :=
                (sector_compatible x.1).symm
              _ = q3Sector left := congrArg q3Sector x.2
              _ = sector := left_sector
              _ = σ (σ.symm sector) :=
                (σ.apply_symm_apply sector).symm⟩
      | .inr x =>
          ⟨x.1, by
            apply σ.injective
            calc
              σ x.1.sector = q3Sector (routing.blockOf x.1) :=
                (sector_compatible x.1).symm
              _ = q3Sector right := congrArg q3Sector x.2
              _ = sector := right_sector
              _ = σ (σ.symm sector) :=
                (σ.apply_symm_apply sector).symm⟩)
    (by
      constructor
      · intro x y hxy
        rcases x with x | x <;> rcases y with y | y
        · exact congrArg Sum.inl
            (Subtype.ext (congrArg
              (fun z : {label : WeightOutputLabel //
                label.sector = σ.symm sector} => z.1) hxy))
        · exact False.elim (left_ne_right (by
            calc
              left = routing.blockOf x.1 := x.2.symm
              _ = routing.blockOf y.1 :=
                congrArg routing.blockOf (congrArg Subtype.val hxy)
              _ = right := y.2))
        · exact False.elim (left_ne_right (by
            calc
              left = routing.blockOf y.1 := y.2.symm
              _ = routing.blockOf x.1 :=
                congrArg routing.blockOf (congrArg Subtype.val hxy).symm
              _ = right := x.2))
        · exact congrArg Sum.inr
            (Subtype.ext (congrArg
              (fun z : {label : WeightOutputLabel //
                label.sector = σ.symm sector} => z.1) hxy))
      · intro label
        have routed_sector : q3Sector (routing.blockOf label.1) = sector := by
          calc
            q3Sector (routing.blockOf label.1) = σ label.1.sector :=
              sector_compatible label.1
            _ = σ (σ.symm sector) := by rw [label.2]
            _ = sector := σ.apply_symm_apply sector
        rcases exhaustive (routing.blockOf label.1) routed_sector with hleft | hright
        · refine ⟨Sum.inl ⟨label.1, hleft⟩, ?_⟩
          apply Subtype.ext
          rfl
        · refine ⟨Sum.inr ⟨label.1, hright⟩, ?_⟩
          apply Subtype.ext
          rfl)).symm

/-- The same actual 8 - 2 = 6 endpoint without deciding whether the raw
faithfulOne tag has the fixed named-block orientation or its single global
faithful swap.  The named pairings B6/B8 and B7/B9 remain fixed. -/
theorem canonical_faithful_output_cards_upToFaithfulSwap
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (map_injective : Function.Injective M.classOfLabel)
    (map_surjective : Function.Surjective M.classOfLabel)
    (sector_compatible :
      canonicalWeightRoutingSectorCompatibleUpToFaithfulSwap blocks R M)
    (B8_weight_fibre_card :
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B8)) = 2)
    (B9_weight_fibre_card :
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B9)) = 2) :
    Fintype.card
        (WeightOutputFibre (canonicalWeightBlockRouting blocks R M) .B6) =
        q3BrauerCount .B6 ∧
      Fintype.card
        (WeightOutputFibre (canonicalWeightBlockRouting blocks R M) .B7) =
        q3BrauerCount .B7 := by
  let routing : WeightBlockRouting := canonicalWeightBlockRouting blocks R M
  rcases sector_compatible with ⟨σ, sigma_cases, raw_routing_sector⟩
  have routing_sector : ∀ label,
      q3Sector (routing.blockOf label) = σ label.sector := by
    simpa only [routing] using raw_routing_sector
  have routing_compatible : WeightBlockFibreCompatible blocks R M routing := by
    simpa only [routing] using
      (canonicalWeightBlockRouting_compatible blocks R M)
  have B8_output_fibre_natCard :
      Nat.card (WeightOutputFibre routing .B8) = 2 := by
    calc
      Nat.card (WeightOutputFibre routing .B8) =
          Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B8)) :=
        Nat.card_congr (weightBlockFibreEquiv blocks R M routing
          map_injective map_surjective routing_compatible .B8)
      _ = 2 := B8_weight_fibre_card
  have B9_output_fibre_natCard :
      Nat.card (WeightOutputFibre routing .B9) = 2 := by
    calc
      Nat.card (WeightOutputFibre routing .B9) =
          Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B9)) :=
        Nat.card_congr (weightBlockFibreEquiv blocks R M routing
          map_injective map_surjective routing_compatible .B9)
      _ = 2 := B9_weight_fibre_card
  have B8_output_fibre_card :
      Fintype.card (WeightOutputFibre routing .B8) = 2 := by
    simpa only [← Nat.card_eq_fintype_card] using B8_output_fibre_natCard
  have B9_output_fibre_card :
      Fintype.card (WeightOutputFibre routing .B9) = 2 := by
    simpa only [← Nat.card_eq_fintype_card] using B9_output_fibre_natCard
  have source_faithfulOne_card :
      Fintype.card
          {label : WeightOutputLabel //
            label.sector = σ.symm .faithfulOne} = 8 := by
    rcases sigma_cases with hsigma | hsigma
    · subst σ
      change Fintype.card
          {label : WeightOutputLabel // label.sector = .faithfulOne} = 8
      exact WeightOutputLabel.sector_fibre_card_exact.2.1
    · subst σ
      change Fintype.card
          {label : WeightOutputLabel // label.sector = .faithfulTwo} = 8
      exact WeightOutputLabel.sector_fibre_card_exact.2.2
  have source_faithfulTwo_card :
      Fintype.card
          {label : WeightOutputLabel //
            label.sector = σ.symm .faithfulTwo} = 8 := by
    rcases sigma_cases with hsigma | hsigma
    · subst σ
      change Fintype.card
          {label : WeightOutputLabel // label.sector = .faithfulTwo} = 8
      exact WeightOutputLabel.sector_fibre_card_exact.2.2
    · subst σ
      change Fintype.card
          {label : WeightOutputLabel // label.sector = .faithfulOne} = 8
      exact WeightOutputLabel.sector_fibre_card_exact.2.1
  have faithfulOne_equiv :
      {label : WeightOutputLabel //
        label.sector = σ.symm .faithfulOne} ≃
        WeightOutputFibre routing .B6 ⊕ WeightOutputFibre routing .B8 :=
    routedSectorPairFibreEquiv_of_globalFaithfulSwap routing σ routing_sector
      (sector := .faithfulOne) (left := .B6) (right := .B8)
      (by rfl) (by rfl) (by decide) (by
        intro block hblock
        cases block <;> simp [q3Sector] at hblock ⊢)
  have faithfulTwo_equiv :
      {label : WeightOutputLabel //
        label.sector = σ.symm .faithfulTwo} ≃
        WeightOutputFibre routing .B7 ⊕ WeightOutputFibre routing .B9 :=
    routedSectorPairFibreEquiv_of_globalFaithfulSwap routing σ routing_sector
      (sector := .faithfulTwo) (left := .B7) (right := .B9)
      (by rfl) (by rfl) (by decide) (by
        intro block hblock
        cases block <;> simp [q3Sector] at hblock ⊢)
  have faithfulOne_sum :
      Fintype.card (WeightOutputFibre routing .B6) +
        Fintype.card (WeightOutputFibre routing .B8) = 8 := by
    calc
      Fintype.card (WeightOutputFibre routing .B6) +
          Fintype.card (WeightOutputFibre routing .B8) =
          Fintype.card
            (WeightOutputFibre routing .B6 ⊕ WeightOutputFibre routing .B8) :=
        Fintype.card_sum.symm
      _ = Fintype.card
          {label : WeightOutputLabel //
            label.sector = σ.symm .faithfulOne} :=
        (Fintype.card_congr faithfulOne_equiv).symm
      _ = 8 := source_faithfulOne_card
  have faithfulTwo_sum :
      Fintype.card (WeightOutputFibre routing .B7) +
        Fintype.card (WeightOutputFibre routing .B9) = 8 := by
    calc
      Fintype.card (WeightOutputFibre routing .B7) +
          Fintype.card (WeightOutputFibre routing .B9) =
          Fintype.card
            (WeightOutputFibre routing .B7 ⊕ WeightOutputFibre routing .B9) :=
        Fintype.card_sum.symm
      _ = Fintype.card
          {label : WeightOutputLabel //
            label.sector = σ.symm .faithfulTwo} :=
        (Fintype.card_congr faithfulTwo_equiv).symm
      _ = 8 := source_faithfulTwo_card
  have forced := faithful_sector_counts_forced
    (fun block => Fintype.card (WeightOutputFibre routing block))
    faithfulOne_sum faithfulTwo_sum B8_output_fibre_card B9_output_fibre_card
  constructor
  · simpa only [routing, q3BrauerCount] using forced.1
  · simpa only [routing, q3BrauerCount] using forced.2

/-!
## Canonical actual-fibre consumer

This section specializes the existing generic actual-fibre construction to the
canonical literal right action and canonical routing. The canonical
Brauer-block transport statement is kernel-derived from the existing literal
carrier theorem; no block-good predicate, iBAW wrapper, or new external source
premise is introduced here.
-/

open ModularRep.FDRepSimpleClassKZero

variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)

/-- Under the canonical literal block action, Brauer blocks transport by the
same source-style right automorphism action as Brauer characters. This removes
the generic theorem's brauerBlock_transport argument without adding a
certificate field. -/
theorem canonical_brauerBlock_transport
    (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    brauerPrimitiveBlock iota hinj blocks (alpha • phi) =
      alpha • brauerPrimitiveBlock iota hinj blocks phi := by
  simpa only [brauerPrimitiveBlock, primitiveBlockOfLabel,
    BlockIdempotentDecomposition.primitiveBlockOfIndex] using
    ModularRep.FDRepSimpleClassKZero.primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
      iota hinj blocks alpha phi

/-- The existing generic actual-fibre construction, specialized only by
canonical K transport and canonical routing. The output_card argument is the
preceding global-faithful-swap count endpoint; no actual-fibre equivalence or
equivariance is supplied as an input. -/
theorem canonical_actualFibreEquiv_of_output_card
    (quotient : C2OuterQuotientInput ((MulAut X)ᵐᵒᵖ))
    (inner_fixes_blocks : ∀ alpha,
      alpha ∈ quotient.innerSubgroup -> ∀ block : PrimitiveBlock k X,
        alpha • block = block)
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_nontrivial : quotient.outerClass outer ≠ 1)
    (block_action_compatible : OuterBlockGeneratorCompatible blocks outer)
    (inner_fixes_brauer : ∀ alpha,
      alpha ∈ quotient.innerSubgroup -> ∀ phi : IBr iota,
        alpha • phi = phi)
    (inner_fixes_weight : ∀ alpha,
      alpha ∈ quotient.innerSubgroup ->
        ∀ weight : CharacterWeight.ConjugacyClass
          (p := 2) (K := K) (G := X), alpha • weight = weight)
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (brauerMap : LiteralBrauerOutputMap iota)
    (brauerMap_injective : Function.Injective brauerMap.character)
    (brauerMap_surjective : Function.Surjective brauerMap.character)
    (brauerBlock_compatible :
      BrauerBlockFibreCompatible iota hinj blocks brauerMap)
    (weightMap : LiteralWeightOutputMap (K := K) (X := X))
    (weightMap_injective : Function.Injective weightMap.classOfLabel)
    (weightMap_surjective : Function.Surjective weightMap.classOfLabel)
    (block : Q3Block)
    (hblock : block = .B6 ∨ block = .B7 ∨ block = .B8 ∨ block = .B9)
    (output_card : Fintype.card
      (WeightOutputFibre (canonicalWeightBlockRouting blocks R weightMap) block) =
        q3BrauerCount block) :
    ∃ equivalence : ActualBrauerFibre iota hinj blocks block ≃
        R.Fibre (primitiveBlockOfLabel blocks block),
      ∀ alpha : actualBlockStabilizer blocks block, ∀ phi,
        equivalence
            (brauerFibreAction iota hinj blocks
              (canonical_brauerBlock_transport blocks iota hinj)
              block alpha phi) =
          alpha • equivalence phi := by
  exact exists_stabilizerEquivariant_actualFibreEquiv_of_output_card
    iota hinj blocks quotient inner_fixes_blocks outer outer_nontrivial
    block_action_compatible
    (canonical_brauerBlock_transport blocks iota hinj)
    inner_fixes_brauer inner_fixes_weight R brauerMap brauerMap_injective
    brauerMap_surjective brauerBlock_compatible weightMap
    (canonicalWeightBlockRouting blocks R weightMap)
    weightMap_injective weightMap_surjective
    (canonicalWeightBlockRouting_compatible blocks R weightMap)
    block hblock output_card

/-- Consume the global-faithful-swap count theorem for B6 and B7. Its two
output-card equalities match the preceding theorem's final argument
definitionally, so this adds no routing, cardinality, or correspondence premise.
-/
theorem canonical_faithful_actualFibreEquivs_upToFaithfulSwap
    (quotient : C2OuterQuotientInput ((MulAut X)ᵐᵒᵖ))
    (inner_fixes_blocks : ∀ alpha,
      alpha ∈ quotient.innerSubgroup -> ∀ block : PrimitiveBlock k X,
        alpha • block = block)
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_nontrivial : quotient.outerClass outer ≠ 1)
    (block_action_compatible : OuterBlockGeneratorCompatible blocks outer)
    (inner_fixes_brauer : ∀ alpha,
      alpha ∈ quotient.innerSubgroup -> ∀ phi : IBr iota,
        alpha • phi = phi)
    (inner_fixes_weight : ∀ alpha,
      alpha ∈ quotient.innerSubgroup ->
        ∀ weight : CharacterWeight.ConjugacyClass
          (p := 2) (K := K) (G := X), alpha • weight = weight)
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (brauerMap : LiteralBrauerOutputMap iota)
    (brauerMap_injective : Function.Injective brauerMap.character)
    (brauerMap_surjective : Function.Surjective brauerMap.character)
    (brauerBlock_compatible :
      BrauerBlockFibreCompatible iota hinj blocks brauerMap)
    (weightMap : LiteralWeightOutputMap (K := K) (X := X))
    (weightMap_injective : Function.Injective weightMap.classOfLabel)
    (weightMap_surjective : Function.Surjective weightMap.classOfLabel)
    (sector_compatible :
      canonicalWeightRoutingSectorCompatibleUpToFaithfulSwap
        blocks R weightMap)
    (B8_weight_fibre_card :
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B8)) = 2)
    (B9_weight_fibre_card :
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B9)) = 2) :
    (∃ equivalence : ActualBrauerFibre iota hinj blocks .B6 ≃
        R.Fibre (primitiveBlockOfLabel blocks .B6),
      ∀ alpha : actualBlockStabilizer blocks .B6, ∀ phi,
        equivalence
            (brauerFibreAction iota hinj blocks
              (canonical_brauerBlock_transport blocks iota hinj)
              .B6 alpha phi) =
          alpha • equivalence phi) ∧
      (∃ equivalence : ActualBrauerFibre iota hinj blocks .B7 ≃
        R.Fibre (primitiveBlockOfLabel blocks .B7),
      ∀ alpha : actualBlockStabilizer blocks .B7, ∀ phi,
        equivalence
            (brauerFibreAction iota hinj blocks
              (canonical_brauerBlock_transport blocks iota hinj)
              .B7 alpha phi) =
          alpha • equivalence phi) := by
  have output_cards :=
    canonical_faithful_output_cards_upToFaithfulSwap blocks R weightMap
      weightMap_injective weightMap_surjective sector_compatible
      B8_weight_fibre_card B9_weight_fibre_card
  constructor
  · exact canonical_actualFibreEquiv_of_output_card blocks iota hinj
      quotient inner_fixes_blocks outer outer_nontrivial
      block_action_compatible inner_fixes_brauer inner_fixes_weight R
      brauerMap brauerMap_injective brauerMap_surjective
      brauerBlock_compatible weightMap weightMap_injective
      weightMap_surjective .B6 (by exact Or.inl rfl) output_cards.1
  · exact canonical_actualFibreEquiv_of_output_card blocks iota hinj
      quotient inner_fixes_blocks outer outer_nontrivial
      block_action_compatible inner_fixes_brauer inner_fixes_weight R
      brauerMap brauerMap_injective brauerMap_surjective
      brauerBlock_compatible weightMap weightMap_injective
      weightMap_surjective .B7 (by exact Or.inr (Or.inl rfl)) output_cards.2

end ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual




/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
