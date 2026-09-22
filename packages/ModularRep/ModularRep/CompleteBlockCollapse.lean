import Formalisation.IBAWCollapse

/-!
# Collapse from the numerical blockwise conjecture when the outer action is trivial

This file formalises the set-theoretic and equivariance argument in manuscript
Lemma 5.2 (`lem:complete-collapse`).  The input `NumericalBlockwiseAWC` is only
the equality of the two finite cardinalities in each block.  Lean constructs
blockwise equivalences extending the prescribed defect-zero normalisation,
combines them into one global equivalence, derives the radical partition and
all local bijections through `Formalisation.IBAW.Candidate`, and proves
equivariance from triviality of the actions on the two class sets.

The representation theoretic extension and intermediate-block conditions are
not inferred from cardinalities.  They appear only in the final
`IdentityCertification` upgrade and receive no kernel-proof credit; the
preceding candidate construction is independent of them.
-/

noncomputable section

namespace ModularRep.ManuscriptVerification.CompleteBlockCollapse

open Formalisation.IBAW

universe uA uB uR uS uX uY uDZ

variable
  {A : Type uA} {B : Type uB} {R : Type uR} {S : Type uS}
  {X : Type uX} {Y : Type uY} {DZ : Type uDZ}
  [Group A]
  [MulAction A B] [MulAction A R] [MulAction A S]
  [MulAction A X] [MulAction A Y] [MulAction A DZ]
  (C : Context A B R S X Y DZ)

/-- The numerical blockwise Alperin weight conjecture, expressed without a
chosen bijection: each block fibre of Brauer objects has the same cardinality
as the corresponding fibre of weights. -/
def NumericalBlockwiseAWC [Fintype X] [Fintype Y] [DecidableEq B] : Prop :=
  ∀ b : B,
    Fintype.card {x : X // C.brauerBlock x = b} =
      Fintype.card {y : Y // C.weightBlock y = b}

/-- Every action of a subsingleton group is trivial.  Thus, after the
concrete outer action has been identified with the trivial outer group, no
separate fixed-point hypotheses are needed for the character and weight
sets. -/
theorem actionTrivial_of_subsingleton [Subsingleton A] : ActionTrivial A X := by
  intro a x
  rw [Subsingleton.elim a 1, one_smul]

section Finite

variable [Fintype X] [Fintype Y] [Fintype DZ]
  [DecidableEq B] [DecidableEq X] [DecidableEq Y]

/-- The defect-zero objects whose reductions belong to a fixed block. -/
abbrev DefectZeroFibre (b : B) :=
  {d : DZ // C.brauerBlock (C.reduce d) = b}

/-- The Brauer-character fibre over a fixed block. -/
abbrev BrauerFibre (b : B) := {x : X // C.brauerBlock x = b}

/-- The weight fibre over a fixed block. -/
abbrev WeightFibre (b : B) := {y : Y // C.weightBlock y = b}

/-- Reduction, restricted to one block fibre. -/
def reduceInBlock (b : B) : DefectZeroFibre C b → BrauerFibre C b :=
  fun d => ⟨C.reduce d, d.property⟩

/-- The normalised local weight at the trivial radical class, restricted to
one block fibre. -/
def atOneInBlock (b : B) : DefectZeroFibre C b → WeightFibre C b :=
  fun d => ⟨C.atOne d, C.atOne_block d |>.trans d.property⟩

omit [Fintype X] [Fintype Y] [Fintype DZ]
  [DecidableEq B] [DecidableEq X] [DecidableEq Y] in
theorem reduceInBlock_injective (b : B) :
    Function.Injective (reduceInBlock C b) := by
  intro d d' h
  apply Subtype.ext
  exact C.reduce_injective (congrArg Subtype.val h)

omit [Fintype X] [Fintype Y] [Fintype DZ]
  [DecidableEq B] [DecidableEq X] [DecidableEq Y] in
theorem atOneInBlock_injective
    (hatOne : Function.Injective C.atOne) (b : B) :
    Function.Injective (atOneInBlock C b) := by
  intro d d' h
  apply Subtype.ext
  exact hatOne (congrArg Subtype.val h)

/-- The prescribed normalisation as an equivalence between its images inside
one block fibre. -/
def normalisationImageEquiv
    (hatOne : Function.Injective C.atOne) (b : B) :
    Set.range (reduceInBlock C b) ≃ Set.range (atOneInBlock C b) :=
  (Equiv.ofInjective (reduceInBlock C b) (reduceInBlock_injective C b)).symm.trans
    (Equiv.ofInjective (atOneInBlock C b)
      (atOneInBlock_injective C hatOne b))

omit [Fintype X] [Fintype Y] [Fintype DZ]
  [DecidableEq B] [DecidableEq X] [DecidableEq Y] in
@[simp]
theorem normalisationImageEquiv_reduce
    (hatOne : Function.Injective C.atOne) (b : B)
    (d : DefectZeroFibre C b) :
    (normalisationImageEquiv C hatOne b
      ⟨reduceInBlock C b d, Set.mem_range_self d⟩ : WeightFibre C b) =
      atOneInBlock C b d := by
  simp [normalisationImageEquiv]

/-- Equal total block cardinalities leave equal cardinalities on the
complements of the two normalisation images. -/
theorem card_compl_normalisation_eq
    (hatOne : Function.Injective C.atOne) (b : B)
    (hcard : Fintype.card (BrauerFibre C b) =
      Fintype.card (WeightFibre C b)) :
    Fintype.card ↥((Set.range (reduceInBlock C b))ᶜ) =
      Fintype.card ↥((Set.range (atOneInBlock C b))ᶜ) := by
  rw [Fintype.card_compl_set, Fintype.card_compl_set]
  rw [hcard]
  congr 1
  exact Fintype.card_congr (normalisationImageEquiv C hatOne b)

/-- A blockwise equivalence constructed only from the numerical cardinality
equality.  It is chosen to extend the required map `reduce d ↦ atOne d`. -/
def blockEquiv
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C) (b : B) :
    BrauerFibre C b ≃ WeightFibre C b := by
  let e₀ := normalisationImageEquiv C hatOne b
  let eCompl :
      ↥((Set.range (reduceInBlock C b))ᶜ) ≃
        ↥((Set.range (atOneInBlock C b))ᶜ) :=
    Fintype.equivOfCardEq
      (card_compl_normalisation_eq C hatOne b (hAWC b))
  exact ((Equiv.Set.compl e₀).symm eCompl).1

theorem blockEquiv_reduce
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C) (b : B)
    (d : DefectZeroFibre C b) :
    blockEquiv C hatOne hAWC b (reduceInBlock C b d) =
      atOneInBlock C b d := by
  let e₀ := normalisationImageEquiv C hatOne b
  let eCompl :
      ↥((Set.range (reduceInBlock C b))ᶜ) ≃
        ↥((Set.range (atOneInBlock C b))ᶜ) :=
    Fintype.equivOfCardEq
      (card_compl_normalisation_eq C hatOne b (hAWC b))
  change (((Equiv.Set.compl e₀).symm eCompl).1 (reduceInBlock C b d)) = _
  have hExtension := ((Equiv.Set.compl e₀).symm eCompl).2
  exact (hExtension
    ⟨reduceInBlock C b d, Set.mem_range_self d⟩).trans
      (normalisationImageEquiv_reduce C hatOne b d)

/-- Combine the independently chosen blockwise equivalences into a global
equivalence. -/
def globalEquiv
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C) : X ≃ Y :=
  (Equiv.sigmaFiberEquiv C.brauerBlock).symm |>.trans
    (Equiv.sigmaCongrRight (blockEquiv C hatOne hAWC)) |>.trans
    (Equiv.sigmaFiberEquiv C.weightBlock)

@[simp]
theorem globalEquiv_apply
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C) (x : X) :
    globalEquiv C hatOne hAWC x =
      (blockEquiv C hatOne hAWC (C.brauerBlock x)
        ⟨x, rfl⟩ : WeightFibre C (C.brauerBlock x)) := rfl

theorem globalEquiv_block_preserving
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C) (x : X) :
    C.weightBlock (globalEquiv C hatOne hAWC x) = C.brauerBlock x := by
  exact (blockEquiv C hatOne hAWC (C.brauerBlock x) ⟨x, rfl⟩).property

theorem globalEquiv_normalisation
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C) (d : DZ) :
    globalEquiv C hatOne hAWC (C.reduce d) = C.atOne d := by
  let d' : DefectZeroFibre C (C.brauerBlock (C.reduce d)) := ⟨d, rfl⟩
  change
    (blockEquiv C hatOne hAWC (C.brauerBlock (C.reduce d))
      (reduceInBlock C _ d') : WeightFibre C _) = C.atOne d
  exact congrArg Subtype.val (blockEquiv_reduce C hatOne hAWC _ d')

/-- The candidate constructed by the proof of Lemma 5.2.  No extension,
block-equality, or character-triple conclusion occurs among its inputs. -/
def candidate
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y) : Candidate C where
  equiv := globalEquiv C hatOne hAWC
  equiv_equivariant := equivariant_of_trivial_actions _ hX hY
  block_preserving := globalEquiv_block_preserving C hatOne hAWC

/-- The candidate when the acting outer group is trivial.  Triviality of the
actions on Brauer objects and weights is now a theorem, not an additional
input. -/
def candidateOfSubsingleton [Subsingleton A]
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C) : Candidate C :=
  candidate C hatOne hAWC
    (actionTrivial_of_subsingleton (A := A) (X := X))
    (actionTrivial_of_subsingleton (A := A) (X := Y))

/-- The constructed candidate already satisfies the prescribed normalisation;
this does not depend on any extension or block-equality input. -/
theorem candidate_normalisation
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (d : DZ) :
    (candidate C hatOne hAWC hX hY).equiv (C.reduce d) = C.atOne d :=
  globalEquiv_normalisation C hatOne hAWC d

/-- Every defect-zero reduction lies in the part indexed by the trivial
radical class before the representation theoretic certification is added. -/
theorem candidate_part_reduce
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (d : DZ) :
    (candidate C hatOne hAWC hX hY).part (C.reduce d) = C.oneRadical := by
  rw [Candidate.part, candidate_normalisation C hatOne hAWC hX hY,
    C.atOne_radical]

/-- The part at the trivial radical class consists exactly of the reductions
of defect-zero objects.  This is a consequence of the constructed
normalisation and the completeness field already present in `Context`. -/
theorem candidate_part_eq_one_iff
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (x : X) :
    (candidate C hatOne hAWC hX hY).part x = C.oneRadical ↔
      ∃ d : DZ, C.reduce d = x := by
  constructor
  · intro hx
    obtain ⟨d, hd⟩ := C.atOne_complete
      ((candidate C hatOne hAWC hX hY).equiv x) hx
    refine ⟨d, (candidate C hatOne hAWC hX hY).equiv.injective ?_⟩
    rw [candidate_normalisation C hatOne hAWC hX hY, hd]
  · rintro ⟨d, rfl⟩
    exact candidate_part_reduce C hatOne hAWC hX hY d

/-- Each object in the trivial part is the reduction of a unique defect-zero
object. -/
theorem candidate_unique_reduce_of_part_eq_one
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (x : X)
    (hx : (candidate C hatOne hAWC hX hY).part x = C.oneRadical) :
    ∃! d : DZ, C.reduce d = x := by
  obtain ⟨d, hd⟩ :=
    (candidate_part_eq_one_iff C hatOne hAWC hX hY x).mp hx
  exact ⟨d, hd, fun d' hd' => C.reduce_injective (hd'.trans hd.symm)⟩

/-- The canonical equivalence from defect-zero objects to the complete
trivial part, available before the extension conditions are certified. -/
def candidateTrivialPartEquiv
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y) :
    DZ ≃ {x : X //
      (candidate C hatOne hAWC hX hY).part x = C.oneRadical} :=
  Equiv.ofBijective
    (fun d : DZ =>
      ⟨C.reduce d, candidate_part_reduce C hatOne hAWC hX hY d⟩)
    ⟨
      fun d d' h => C.reduce_injective (congrArg Subtype.val h),
      fun x => by
        obtain ⟨d, hd⟩ :=
          (candidate_part_eq_one_iff C hatOne hAWC hX hY x).mp x.property
        exact ⟨d, Subtype.ext hd⟩
    ⟩

/-- The complete partition by radical class is already determined by the
constructed candidate and does not use the extension certification. -/
abbrev candidatePartitionEquiv
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y) :=
  (candidate C hatOne hAWC hX hY).partitionEquiv

/-- The blockwise local bijection at a fixed radical class, derived before
the extension certification is attached. -/
abbrev candidateLocalEquiv
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (b : B) (r : R) :=
  (candidate C hatOne hAWC hX hY).localEquiv b r

/-- The radical part of the constructed partition is equivariant. -/
theorem candidate_part_equivariant
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (a : A) (x : X) :
    (candidate C hatOne hAWC hX hY).part (a • x) =
      a • (candidate C hatOne hAWC hX hY).part x :=
  (candidate C hatOne hAWC hX hY).part_equivariant a x

/-- The constructed local matching preserves the central sector determined
by the block label. -/
theorem candidate_sector_preserving
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (x : X) :
    C.blockSector
        (C.weightBlock ((candidate C hatOne hAWC hX hY).equiv x)) =
      C.blockSector (C.brauerBlock x) :=
  (candidate C hatOne hAWC hX hY).sector_preserving x

/-- The remaining representation theoretic obligations in the complete
outer-trivial case.  The first field is the intermediate block induction
equality.  The second packages the compatible identity extensions and the
resulting modular-character-triple condition.  Normalisation is absent: Lean
has already forced it in the constructed candidate. -/
structure IdentityCertification
    (W : Candidate C) : Prop where
  intermediateBlockEqualities : ∀ x : X,
    C.intermediateBlockEqualitiesOK x (W.equiv x)
  identityExtensions : ∀ x : X,
    C.extensionsOK x (W.equiv x) ∧ C.characterTripleOK x (W.equiv x)

/-- Upgrade the constructed candidate to full abstract iBAW data from only
the exact extension and intermediate-block inputs that are not consequences
of the numerical conjecture. -/
def data
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (hcert : IdentityCertification C (candidate C hatOne hAWC hX hY)) :
    Data C where
  toCandidate := candidate C hatOne hAWC hX hY
  intermediateBlockEqualities := hcert.intermediateBlockEqualities
  extensions x := (hcert.identityExtensions x).1
  characterTriple x := (hcert.identityExtensions x).2
  normalisation := globalEquiv_normalisation C hatOne hAWC

/-- Full abstract iBAW data when the acting outer group is trivial.  The only
remaining certification is the same explicit identity-extension and
intermediate-block input as for `data`. -/
def dataOfSubsingleton [Subsingleton A]
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hcert : IdentityCertification C
      (candidateOfSubsingleton C hatOne hAWC)) : Data C :=
  data C hatOne hAWC
    (actionTrivial_of_subsingleton (A := A) (X := X))
    (actionTrivial_of_subsingleton (A := A) (X := Y)) hcert

/-- The constructed datum has exactly the manuscript's normalisation at the
trivial radical class. -/
theorem data_normalisation
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (hcert : IdentityCertification C (candidate C hatOne hAWC hX hY))
    (d : DZ) :
    (data C hatOne hAWC hX hY hcert).equiv (C.reduce d) = C.atOne d :=
  globalEquiv_normalisation C hatOne hAWC d

/-- The induced part at the trivial radical class is precisely the image of
the defect-zero reduction map. -/
theorem data_part_eq_one_iff
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (hcert : IdentityCertification C (candidate C hatOne hAWC hX hY))
    (x : X) :
    (data C hatOne hAWC hX hY hcert).toCandidate.part x = C.oneRadical ↔
      ∃ d : DZ, C.reduce d = x :=
  (data C hatOne hAWC hX hY hcert).part_eq_one_iff x

/-- The full partition of Brauer objects by radical class, constructed from
the global equivalence rather than supplied as input. -/
abbrev dataPartitionEquiv
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (hcert : IdentityCertification C (candidate C hatOne hAWC hX hY)) :=
  (data C hatOne hAWC hX hY hcert).toCandidate.partitionEquiv

/-- The local bijection for a fixed block and radical class, derived from the
constructed global equivalence. -/
abbrev dataLocalEquiv
    (hatOne : Function.Injective C.atOne)
    (hAWC : NumericalBlockwiseAWC C)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (hcert : IdentityCertification C (candidate C hatOne hAWC hX hY))
    (b : B) (r : R) :=
  (data C hatOne hAWC hX hY hcert).localEquiv b r

end Finite

end ModularRep.ManuscriptVerification.CompleteBlockCollapse


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
