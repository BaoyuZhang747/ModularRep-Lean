import ModularRep.PaperProofs.TypeBWeightCoveringSplittingSource
import ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitCount
import ModularRep.PaperProofs.TypeBLocalReductionInstantiation
import ModularRep.PaperProofs.TypeBFixedRootDefinitionFamily

/-!
# Principal covering and the count-derived seed in one modular system

The classification concerns the literal calibrated DGN relation. Its unique
upper class determines the covering map. The numerical and orbit consequences
then reuse the existing finite involution and constituent-count arguments.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalCoverSplitting

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalCountBinding TypeBGreenPrincipalConstituentSource
open TypeBRankThreePrincipalBrauerOrbitBinding NavarroCoveringBrauerExtension
open TypeBExceptionalQ3Proposition416Relative
open TypeBFixedRootDefinitionFamily TypeBLocalReductionInstantiation

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {r f : ℕ} [CharP F r]

/-- The six independent classification clauses concern only actual ordinary
weight covering. The root and block calibrations are fixed indices. -/
structure PublishedWeightCovering
    (F : Type) [Field F] [Finite F] [CharP F r]
    (S : OmegaWeightSource (k := k) (K := K) F)
    (SH : SOWeightSource (k := k) (K := K) F)
    (root : PrimeRegularRootEmbedding 2 k K (G F))
    (rootH : PrimeRegularRootEmbedding 2 k K (H F))
    (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
    (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
    (delta : H F) (indexTwo : (G F).index = 2) (outside : delta ∉ G F)
    (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
    (Msys : ModularSystem 2 K O k)
    (rootCalibration : RootResidueCompatible Msys root)
    (rootHCalibration : RootResidueCompatible Msys rootH)
    (guard : GuardedBlockCompatibility root S.operations)
    (guardH : GuardedBlockCompatibility rootH SH.operations)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (H F))]
    (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys) where
  splits : SOWeight F SH bH → Prop
  splitsDecidable : DecidablePred splits
  splittingParametrisation : {h : SOWeight F SH bH // splits h} ≃ SplittingParameterIndex
  unique_above : ∀ w : OmegaWeight F S b, ∃! h : SOWeight F SH bH,
    TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn h.val w.val
  fibre_card : ∀ h : SOWeight F SH bH,
    Nat.card {w : OmegaWeight F S b //
      TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn h.val w.val} =
        @ite ℕ (splits h) (splitsDecidable h) 2 1
  covered_orbit : ∀ (h : SOWeight F SH bH) (w v : OmegaWeight F S b),
    TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn h.val w.val →
      (TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn h.val v.val ↔
        v = w ∨ v = weightPermutation F S literal b hb delta indexTwo w)

variable {S : OmegaWeightSource (k := k) (K := K) F}
  {SH : SOWeightSource (k := k) (K := K) F}
  {root : PrimeRegularRootEmbedding 2 k K (G F)}
  {rootH : PrimeRegularRootEmbedding 2 k K (H F)}
  {b : LiteralPrimitiveBlock k (G F)} {hb : IsPrincipal b}
  {bH : LiteralPrimitiveBlock k (H F)} {hbH : IsPrincipal bH}
  {literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val}
  {literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val}
  {delta : H F} {indexTwo : (G F).index = 2} {outside : delta ∉ G F}
  {parameters : OddFieldParameters F r f} {notThree : Nat.card F ≠ 3}
  {Msys : ModularSystem 2 K O k}
  {rootCalibration : RootResidueCompatible Msys root}
  {rootHCalibration : RootResidueCompatible Msys rootH}
  {guard : GuardedBlockCompatibility root S.operations}
  {guardH : GuardedBlockCompatibility rootH SH.operations}
  [HasEnoughRootsOfUnity K (Nat.card (H F))]
  {dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys}
  (covering : PublishedWeightCovering F S SH root rootH b hb bH hbH literal literalH
    delta indexTwo outside parameters notThree Msys rootCalibration rootHCalibration guard guardH dgn)

namespace PublishedWeightCovering

/-- The upper ordinary weight class is chosen from its literal uniqueness. -/
def cover (w : OmegaWeight F S b) : SOWeight F SH bH :=
  Classical.choose (covering.unique_above w)

theorem cover_covers (w : OmegaWeight F S b) :
    TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (covering.cover w).val w.val :=
  (Classical.choose_spec (covering.unique_above w)).1

theorem covers_iff (h : SOWeight F SH bH) (w : OmegaWeight F S b) :
    TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn h.val w.val ↔
      covering.cover w = h := by
  constructor
  · intro related
    exact ((Classical.choose_spec (covering.unique_above w)).2 h related).symm
  · rintro rfl
    exact covering.cover_covers w

theorem cover_eq_iff (w v : OmegaWeight F S b) :
    covering.cover w = covering.cover v ↔
      v = w ∨ v = weightPermutation F S literal b hb delta indexTwo w := by
  exact eq_comm.trans ((covering.covers_iff (covering.cover w) v).symm.trans
    (covering.covered_orbit (covering.cover w) w v (covering.cover_covers w)))

theorem cover_action (w : OmegaWeight F S b) :
    covering.cover (weightPermutation F S literal b hb delta indexTwo w) = covering.cover w :=
  ((covering.cover_eq_iff w _).mpr (Or.inr rfl)).symm

theorem cover_surjective : Function.Surjective covering.cover := by
  classical
  intro h
  have positive : 0 < Nat.card {w : OmegaWeight F S b //
      TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn h.val w.val} := by
    rw [covering.fibre_card]
    split_ifs <;> decide
  obtain ⟨⟨w, related⟩⟩ := (Nat.card_pos_iff.mp positive).1
  exact ⟨w, (covering.covers_iff h w).mp related⟩

variable [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]

theorem cover_fibre_card (h : SOWeight F SH bH) :
    Fintype.card {w : OmegaWeight F S b // covering.cover w = h} =
      @ite ℕ (covering.splits h) (covering.splitsDecidable h) 2 1 := by
  let e : {w : OmegaWeight F S b // covering.cover w = h} ≃
      {w : OmegaWeight F S b //
        TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn h.val w.val} :=
    Equiv.subtypeEquivRight (fun w => (covering.covers_iff h w).symm)
  exact (Nat.card_eq_fintype_card.symm.trans (Nat.card_congr e)).trans
    (covering.fibre_card h)

theorem split_weights_are_moved (w : OmegaWeight F S b)
    (split : covering.splits (covering.cover w)) :
    weightPermutation F S literal b hb delta indexTwo w ≠ w := by
  classical
  intro fixed
  let Fibre := {v : OmegaWeight F S b // covering.cover v = covering.cover w}
  have one : Fintype.card Fibre = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨w, rfl⟩, ?_⟩
    intro v
    apply Subtype.ext
    rcases (covering.cover_eq_iff w v.val).mp v.property.symm with equal | equal
    · exact equal
    · exact equal.trans fixed
  have two : Fintype.card Fibre = 2 := by
    simpa only [if_pos split] using covering.cover_fibre_card (covering.cover w)
  omega

theorem coversClass_cover_iff (w v : OmegaWeight F S b) :
    TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn (covering.cover w).val v.val ↔
      v = w ∨ v = weightPermutation F S literal b hb delta indexTwo w :=
  covering.covered_orbit (covering.cover w) w v (covering.cover_covers w)

end PublishedWeightCovering

section Counts

variable [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)
  (roots : RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)

/-- The old numerical carrier is filled by the literal constituent theorem. -/
def principalCliffordOrbitCount :
    PrincipalCliffordOrbitCount F S literal root b hb delta indexTwo
      SH rootH bH parameters notThree outside hbH literalH where
  orbit_count := TypeBRankThreePrincipalOrbitCount.principal_orbit_count
    F S literal root b hb delta indexTwo outside rootH bH hbH roots fieldScope
    green principalLift clifford principalRestriction

include counts outside green principalLift clifford principalRestriction in
theorem principalBrauer_action_signature :
    (Fintype.card (OmegaBrauer F root b),
      Fintype.card (Function.fixedPoints
        (brauerPermutation F S literal root b hb delta indexTwo))) = (12, 8) :=
  TypeBRankThreePrincipalCountBinding.principalBrauer_action_signature
    F S literal root b hb delta indexTwo parameters notThree outside SH literalH rootH bH hbH
    counts (principalCliffordOrbitCount roots fieldScope green principalLift clifford principalRestriction)

/-- The existing finite covering arithmetic consumes only derived map laws. -/
def coveringInput : PrincipalWeightCoveringInput (SOWeight F SH bH) (OmegaWeight F S b) where
  splits := covering.splits
  splitsDecidable := covering.splitsDecidable
  splittingParametrisation := covering.splittingParametrisation
  cover := covering.cover
  cover_surjective := covering.cover_surjective
  weightAction := weightPermutation F S literal b hb delta indexTwo
  weightAction_involutive := weightStep_involutive F S literal b hb delta indexTwo
  cover_action := covering.cover_action
  fibre_card := covering.cover_fibre_card
  split_weights_are_moved := covering.split_weights_are_moved
  hWeight_card := counts.soWeight_card

include counts covering in
theorem principalWeight_action_signature :
    (Fintype.card (OmegaWeight F S b),
      Fintype.card (Function.fixedPoints
        (weightPermutation F S literal b hb delta indexTwo))) = (12, 8) :=
  (coveringInput covering counts).principalWeight_action_signature

include counts covering green principalLift clifford principalRestriction in
/-- The same actual involutions yield a seed by their derived signatures. -/
theorem exists_principalOmega_equivariantEquiv :
    ∃ seed : OmegaBrauer F root b ≃ OmegaWeight F S b,
      ∀ theta,
        seed (brauerPermutation F S literal root b hb delta indexTwo theta) =
          weightPermutation F S literal b hb delta indexTwo (seed theta) := by
  have brauer := principalBrauer_action_signature (delta := delta) (indexTwo := indexTwo)
    (outside := outside)
    counts roots fieldScope
    green principalLift clifford principalRestriction
  have weight := principalWeight_action_signature covering counts
  exact Formalisation.C2Cancellation.exists_equivariantEquiv_of_card_eq_of_fixed_card_eq
    (brauerPermutation F S literal root b hb delta indexTwo)
    (weightPermutation F S literal b hb delta indexTwo)
    (brauerStep_involutive F S literal root b hb delta indexTwo)
    (weightStep_involutive F S literal b hb delta indexTwo)
    ((congrArg Prod.fst brauer).trans (congrArg Prod.fst weight).symm)
    ((congrArg Prod.snd brauer).trans (congrArg Prod.snd weight).symm)

/-- One fixed choice of the constructed seed for all subsequent consumers. -/
def principalOmegaEquiv : OmegaBrauer F root b ≃ OmegaWeight F S b :=
  Classical.choose (exists_principalOmega_equivariantEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction)

theorem principalOmegaEquiv_delta (theta : OmegaBrauer F root b) :
    principalOmegaEquiv covering counts roots fieldScope green principalLift clifford
      principalRestriction (brauerPermutation F S literal root b hb delta indexTwo theta) =
    weightPermutation F S literal b hb delta indexTwo
      (principalOmegaEquiv covering counts roots fieldScope green principalLift clifford
        principalRestriction theta) :=
  Classical.choose_spec (exists_principalOmega_equivariantEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction) theta

end Counts

end ModularRep.PaperProofs.TypeBRankThreePrincipalCoverSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
