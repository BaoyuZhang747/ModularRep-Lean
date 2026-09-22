import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.QuotientGroup.Basic
import ModularRep.CompleteBlockCollapse

/-!
# Source-shaped deductions for manuscript Lemma 5.2

The existing `CompleteBlockCollapse` module kernel-checks the finite set part
of Lemma 5.2: blockwise numerical equalities give a block-preserving global
bijection, the prescribed defect-zero normalisation can be retained, and a
trivial effective outer action makes the construction equivariant.

This file checks the group-theoretic collapse used in the final paragraph of
the proof.  If `X` is perfect and `Z0` is central, then quotienting by `Z0`
does not create a larger centre.  Consequently

`(X / Z0) / Z(X / Z0) ≅ X / Z(X)`.

After the standard conjugation identification of `X / Z(X)` with the full
automorphism stabiliser is supplied, Lean constructs the group required in
Späth's extension clause.  It also proves that the interval of intermediate
groups collapses to one group and constructs the two identity extensions.
The local extension is deliberately typed as a Brauer object: in the
manuscript it is the Brauer reduction of the inflated defect-zero ordinary
character, not that ordinary character itself.

Späth 2017, Theorem 4.4, which identifies clause (iii) with a block
isomorphism of modular character triples, remains an exact external
representation theoretic interface.  No iBAW conclusion is assumed here.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Relative

section Centres

variable {G H : Type*} [Group G] [Group H]

/-- A surjective homomorphism sends central elements to central elements.
Surjectivity is essential here. -/
theorem map_center_le_center_of_surjective
    (f : G →* H) (hf : Function.Surjective f) :
    (Subgroup.center G).map f ≤ Subgroup.center H := by
  rintro _ ⟨z, hz, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨x, rfl⟩ := hf y
  simpa only [map_mul] using congrArg f
    (Subgroup.mem_center_iff.mp hz x)

/-- If a central quotient is centreless, the quotient kernel is the whole
centre.  This is the elementary reverse inclusion used below. -/
theorem center_eq_of_central_quotient_centerless
    (K : Subgroup G) [K.Normal]
    (hK : K ≤ Subgroup.center G)
    (hcenter : Subgroup.center (G ⧸ K) = ⊥) :
    Subgroup.center G = K := by
  apply le_antisymm
  · intro z hz
    have hzmap : QuotientGroup.mk' K z ∈ Subgroup.center (G ⧸ K) :=
      map_center_le_center_of_surjective (QuotientGroup.mk' K)
        (QuotientGroup.mk'_surjective K) ⟨z, hz, rfl⟩
    rw [hcenter, Subgroup.mem_bot] at hzmap
    exact (QuotientGroup.eq_one_iff z).mp hzmap
  · exact hK

/-- A central quotient of a perfect group acquires no new central elements.
Equivalently, its centre is exactly the image of the original centre.

The proof uses Grün's lemma in the form
`Group.IsPerfect.center_quotient_center_eq_bot`, together with the third
isomorphism theorem.  The equality claimed in Lemma 5.2 is therefore proved
in the kernel rather than supplied as a structural input. -/
theorem center_eq_map_center_of_le_center
    [Group.IsPerfect G] (Z0 : Subgroup G) [Z0.Normal]
    (hZ0 : Z0 ≤ Subgroup.center G) :
    Subgroup.center (G ⧸ Z0) =
      (Subgroup.center G).map (QuotientGroup.mk' Z0) := by
  let K : Subgroup (G ⧸ Z0) :=
    (Subgroup.center G).map (QuotientGroup.mk' Z0)
  let _ : (Subgroup.center G).Normal :=
    Subgroup.normal_of_characteristic (Subgroup.center G)
  let _ : K.Normal :=
    (show (Subgroup.center G).Normal from inferInstance).map
      (QuotientGroup.mk' Z0) (QuotientGroup.mk'_surjective Z0)
  have hK : K ≤ Subgroup.center (G ⧸ Z0) :=
    map_center_le_center_of_surjective (QuotientGroup.mk' Z0)
      (QuotientGroup.mk'_surjective Z0)
  apply center_eq_of_central_quotient_centerless K hK
  let e : ((G ⧸ Z0) ⧸ K) ≃* (G ⧸ Subgroup.center G) :=
    QuotientGroup.quotientQuotientEquivQuotient
      Z0 (Subgroup.center G) hZ0
  apply le_antisymm
  · intro z hz
    have hez : e z ∈ Subgroup.center (G ⧸ Subgroup.center G) :=
      map_center_le_center_of_surjective e.toMonoidHom e.surjective
        ⟨z, hz, rfl⟩
    rw [Group.IsPerfect.center_quotient_center_eq_bot G,
      Subgroup.mem_bot] at hez
    rw [Subgroup.mem_bot]
    exact e.injective (hez.trans e.map_one.symm)
  · exact bot_le

/-- The quotient-centre identification used to take
`A(phi) = X / Z0` in Späth's definition. -/
def quotientCenterEquiv
    [Group.IsPerfect G] (Z0 : Subgroup G) [Z0.Normal]
    (hZ0 : Z0 ≤ Subgroup.center G) :
    ((G ⧸ Z0) ⧸ Subgroup.center (G ⧸ Z0)) ≃*
      (G ⧸ Subgroup.center G) :=
  (QuotientGroup.quotientMulEquivOfEq
      (center_eq_map_center_of_le_center Z0 hZ0)).trans
    (QuotientGroup.quotientQuotientEquivQuotient
      Z0 (Subgroup.center G) hZ0)

/-- Compose the quotient-centre calculation with the standard conjugation
identification of `X / Z(X)` with the automorphism stabiliser.  In the
manuscript, triviality of `Out(X)` says that this stabiliser consists of the
inner automorphisms. -/
def quotientCenterStabilizerEquiv
    [Group.IsPerfect G] {AutStabilizer : Type*} [Group AutStabilizer]
    (Z0 : Subgroup G) [Z0.Normal]
    (hZ0 : Z0 ≤ Subgroup.center G)
    (innerStabilizer : (G ⧸ Subgroup.center G) ≃* AutStabilizer) :
    ((G ⧸ Z0) ⧸ Subgroup.center (G ⧸ Z0)) ≃*
      AutStabilizer :=
  (quotientCenterEquiv Z0 hZ0).trans innerStabilizer

end Centres

section TrivialAction

variable {A Omega : Type*} [Group A] [MulAction A Omega]

/-- If the effective outer action is trivial, every point stabiliser is the
whole acting group.  This is the exact stabiliser deduction behind
`Aut(X)_phi = Inn(X)` after the action is factored through `Out(X)`. -/
theorem stabilizer_eq_top_of_action_trivial
    (htrivial : Formalisation.IBAW.ActionTrivial A Omega) (x : Omega) :
    MulAction.stabilizer A x = ⊤ := by
  apply top_unique
  intro a _
  exact (MulAction.mem_stabilizer_iff.mpr (htrivial a x))

/-- Source-shaped form for the actual automorphism group.  If every
automorphism is inner and inner automorphisms fix the objects under
consideration, then the full automorphism action is trivial. -/
theorem actionTrivial_of_all_inner
    (IsInner : A → Prop)
    (allInner : ∀ a : A, IsInner a)
    (innerFix : ∀ (a : A), IsInner a → ∀ x : Omega, a • x = x) :
    Formalisation.IBAW.ActionTrivial A Omega := by
  intro a x
  exact innerFix a (allInner a) x

/-- Hence `Out(X)=1` gives `Aut(X)_phi=Aut(X)=Inn(X)` once the standard fact
that inner automorphisms fix character and weight classes is supplied. -/
theorem stabilizer_eq_top_of_all_inner
    (IsInner : A → Prop)
    (allInner : ∀ a : A, IsInner a)
    (innerFix : ∀ (a : A), IsInner a → ∀ x : Omega, a • x = x)
    (x : Omega) : MulAction.stabilizer A x = ⊤ :=
  stabilizer_eq_top_of_action_trivial
    (actionTrivial_of_all_inner IsInner allInner innerFix) x

/-- A subsingleton effective outer group acts trivially, so its point
stabilisers are automatically the whole group. -/
theorem stabilizer_eq_top_of_subsingleton [Subsingleton A] (x : Omega) :
    MulAction.stabilizer A x = ⊤ :=
  stabilizer_eq_top_of_action_trivial
    (ModularRep.ManuscriptVerification.CompleteBlockCollapse.actionTrivial_of_subsingleton
      (A := A) (X := Omega)) x

end TrivialAction

section IntermediateGroups

variable {G : Type*} [Group G]

/-- Groups in the interval occurring in Späth's intermediate block
condition. -/
abbrev IntermediateGroup (lower upper : Subgroup G) :=
  {H : Subgroup G // lower ≤ H ∧ H ≤ upper}

/-- If the two endpoints coincide, every intermediate group is that common
endpoint. -/
theorem intermediateGroup_eq_lower
    {lower upper : Subgroup G} (h : upper = lower)
    (H : IntermediateGroup lower upper) : (H : Subgroup G) = lower := by
  subst upper
  exact le_antisymm H.property.2 H.property.1

/-- In the complete-group collapse, `A(phi) = Xbar`, and hence
`N_A(Qbar) = N_Xbar(Qbar)`.  Therefore the universal quantifier over
intermediate groups reduces to the already known block induction equality
at the single lower endpoint. -/
theorem every_intermediate_property_of_eq
    {lower upper : Subgroup G} (h : upper = lower)
    (P : Subgroup G → Prop) (hLower : P lower) :
    ∀ H : IntermediateGroup lower upper, P H := by
  intro H
  rw [intermediateGroup_eq_lower h H]
  exact hLower

/-- The actual normaliser interval when the ambient group in the extension
clause is the quotient group itself. -/
theorem every_normalizer_intermediate_property
    (Q : Subgroup G) (P : Subgroup G → Prop)
    (hNormaliser : P (Subgroup.normalizer (Q : Set G))) :
    ∀ H : IntermediateGroup (Subgroup.normalizer (Q : Set G))
      (Subgroup.normalizer (Q : Set G)), P H :=
  every_intermediate_property_of_eq rfl P hNormaliser

end IntermediateGroups

section IdentityExtensions

variable {GlobalBrauer LocalBrauer : Type*}

/-- Exact typed interface for the standard reduction and inflation step at a
weight `(Q, theta)`.

`QuotientDefectZeroOrdinary` is the carrier of irreducible defect-zero
ordinary characters of `N_X(Q) / Q`.  Thus `reduceDefectZero` is precisely
the E1 input `SF-DEFECT-ZERO-REDUCTION`.  The two inflation maps and their
compatibility with restriction to regular elements are the routine local
character-theoretic input.  No extension, block equality, character-triple
relation, or iBAW conclusion is a field of this structure. -/
structure DefectZeroReductionInflation
    (QuotientDefectZeroOrdinary QuotientBrauer
      InflatedDefectZeroOrdinary LocalBrauer : Type*) where
  reduceDefectZero : QuotientDefectZeroOrdinary → QuotientBrauer
  inflateOrdinary : QuotientDefectZeroOrdinary → InflatedDefectZeroOrdinary
  inflateBrauer : QuotientBrauer → LocalBrauer
  reduceInflated : InflatedDefectZeroOrdinary → LocalBrauer
  reduceInflated_inflateOrdinary : ∀ theta,
    reduceInflated (inflateOrdinary theta) =
      inflateBrauer (reduceDefectZero theta)

namespace DefectZeroReductionInflation

variable
  {QuotientDefectZeroOrdinary QuotientBrauer
    InflatedDefectZeroOrdinary LocalBrauer : Type*}

/-- The local Brauer character required by Späth's extension clause: first
take the irreducible Brauer reduction of the defect-zero quotient character,
then inflate it from `N_X(Q) / Q` to `N_X(Q)`. -/
def localBrauer
    (R : DefectZeroReductionInflation QuotientDefectZeroOrdinary
      QuotientBrauer InflatedDefectZeroOrdinary LocalBrauer)
    (theta : QuotientDefectZeroOrdinary) : LocalBrauer :=
  R.inflateBrauer (R.reduceDefectZero theta)

/-- The preceding local Brauer character is also the Brauer reduction of the
inflated ordinary character.  This is the typed correction to the phrase
"the local ordinary character" in the manuscript proof. -/
theorem localBrauer_eq_reduceInflated
    (R : DefectZeroReductionInflation QuotientDefectZeroOrdinary
      QuotientBrauer InflatedDefectZeroOrdinary LocalBrauer)
    (theta : QuotientDefectZeroOrdinary) :
    R.localBrauer theta = R.reduceInflated (R.inflateOrdinary theta) :=
  (R.reduceInflated_inflateOrdinary theta).symm

end DefectZeroReductionInflation

/-- The two extensions in clause (iii) when both extension groups equal the
groups on which the original Brauer characters are defined. -/
structure IdentityExtensionPair
    (global : GlobalBrauer) (localBrauer : LocalBrauer) where
  globalExtension : GlobalBrauer
  localExtension : LocalBrauer
  global_restricts : globalExtension = global
  local_restricts : localExtension = localBrauer

/-- Identity extensions exist without any character-theoretic extension
theorem once the two ambient groups have collapsed. -/
def identityExtensionPair
    (global : GlobalBrauer) (localBrauer : LocalBrauer) :
    IdentityExtensionPair global localBrauer where
  globalExtension := global
  localExtension := localBrauer
  global_restricts := rfl
  local_restricts := rfl

/-- Construct the local identity extension from an ordinary defect-zero
quotient character without ever placing that ordinary character in a Brauer
slot. -/
def identityExtensionPairOfDefectZero
    {QuotientDefectZeroOrdinary QuotientBrauer
      InflatedDefectZeroOrdinary : Type*}
    (R : DefectZeroReductionInflation QuotientDefectZeroOrdinary
      QuotientBrauer InflatedDefectZeroOrdinary LocalBrauer)
    (global : GlobalBrauer) (theta : QuotientDefectZeroOrdinary) :
    IdentityExtensionPair global (R.localBrauer theta) :=
  identityExtensionPair global (R.localBrauer theta)

@[simp]
theorem identityExtensionPairOfDefectZero_localExtension
    {QuotientDefectZeroOrdinary QuotientBrauer
      InflatedDefectZeroOrdinary : Type*}
    (R : DefectZeroReductionInflation QuotientDefectZeroOrdinary
      QuotientBrauer InflatedDefectZeroOrdinary LocalBrauer)
    (global : GlobalBrauer) (theta : QuotientDefectZeroOrdinary) :
    (identityExtensionPairOfDefectZero R global theta).localExtension =
      R.reduceInflated (R.inflateOrdinary theta) := by
  exact R.localBrauer_eq_reduceInflated theta

/-- At `Q = 1`, the normalisation identifies the global Brauer character
with the same reduction.  Hence the two identity extensions are literally
the same Brauer object, rather than an ordinary character and a Brauer
character being conflated. -/
def identityExtensionPairAtOneOfDefectZero
    {QuotientDefectZeroOrdinary QuotientBrauer
      InflatedDefectZeroOrdinary : Type*}
    (R : DefectZeroReductionInflation QuotientDefectZeroOrdinary
      QuotientBrauer InflatedDefectZeroOrdinary GlobalBrauer)
    (theta : QuotientDefectZeroOrdinary) :
    IdentityExtensionPair (R.localBrauer theta) (R.localBrauer theta) :=
  identityExtensionPair (R.localBrauer theta) (R.localBrauer theta)

@[simp]
theorem identityExtensionPairAtOneOfDefectZero_extensions_eq
    {QuotientDefectZeroOrdinary QuotientBrauer
      InflatedDefectZeroOrdinary : Type*}
    (R : DefectZeroReductionInflation QuotientDefectZeroOrdinary
      QuotientBrauer InflatedDefectZeroOrdinary GlobalBrauer)
    (theta : QuotientDefectZeroOrdinary) :
    (identityExtensionPairAtOneOfDefectZero R theta).globalExtension =
      (identityExtensionPairAtOneOfDefectZero R theta).localExtension := rfl

end IdentityExtensions

section ClauseIII

variable {G AutStabilizer GlobalBrauer LocalBrauer : Type*}
  [Group G] [Group.IsPerfect G] [Group AutStabilizer]

/-- Source-shaped witness for clause (iii) after choosing
`A(phi) = X / Z0`.

`centrePrimeTo` is the routine fact that a quotient of the original
ell-prime centre is again ell-prime.  `innerStabilizer` is the standard
conjugation identification after `Out(X) = 1`.  The only block-theoretic
input is `hNormaliser`, namely the block induction equality already required
of the chosen local bijection. -/
structure IdentityClauseIIIWitness
    (Z0 : Subgroup G) [Z0.Normal]
    (AutStabilizer : Type*) [Group AutStabilizer]
    (CentrePrimeTo : Prop)
    (global : GlobalBrauer) (localBrauer : LocalBrauer)
    (Qbar : Subgroup (G ⧸ Z0))
    (IntermediateBlockEquality : Subgroup (G ⧸ Z0) → Prop) where
  actingGroupQuotient :
    ((G ⧸ Z0) ⧸ Subgroup.center (G ⧸ Z0)) ≃* AutStabilizer
  centrePrimeTo : CentrePrimeTo
  extensions : IdentityExtensionPair global localBrauer
  intermediateBlockEqualities :
    ∀ H : IntermediateGroup
      (Subgroup.normalizer (Qbar : Set (G ⧸ Z0)))
      (Subgroup.normalizer (Qbar : Set (G ⧸ Z0))),
      IntermediateBlockEquality H

/-- Construct every structural part of clause (iii) in the identity case.
Neither a clause-(iii) witness nor a character-triple relation is an input. -/
def identityClauseIIIWitness
    (Z0 : Subgroup G) [Z0.Normal]
    (hZ0 : Z0 ≤ Subgroup.center G)
    (innerStabilizer :
      (G ⧸ Subgroup.center G) ≃* AutStabilizer)
    (centrePrimeTo : Prop) (hCentrePrimeTo : centrePrimeTo)
    (global : GlobalBrauer) (localBrauer : LocalBrauer)
    (Qbar : Subgroup (G ⧸ Z0))
    (IntermediateBlockEquality : Subgroup (G ⧸ Z0) → Prop)
    (hNormaliser : IntermediateBlockEquality
      (Subgroup.normalizer (Qbar : Set (G ⧸ Z0)))) :
    IdentityClauseIIIWitness Z0 AutStabilizer centrePrimeTo global localBrauer Qbar
      IntermediateBlockEquality where
  actingGroupQuotient :=
    quotientCenterStabilizerEquiv Z0 hZ0 innerStabilizer
  centrePrimeTo := hCentrePrimeTo
  extensions := identityExtensionPair global localBrauer
  intermediateBlockEqualities :=
    every_normalizer_intermediate_property Qbar
      IntermediateBlockEquality hNormaliser

/-- The complete typed bridge for the last paragraph of Lemma 5.2.  It
forms the local Brauer character from the ordinary defect-zero quotient
character and then performs the identity-extension and one-intermediate-group
collapse.  The only representation theoretic inputs are the explicit
reduction/inflation interface, the standard inner-stabiliser identification,
and the already required block equality at the normaliser. -/
def identityClauseIIIWitnessOfDefectZero
    {QuotientDefectZeroOrdinary QuotientBrauer
      InflatedDefectZeroOrdinary : Type*}
    (R : DefectZeroReductionInflation QuotientDefectZeroOrdinary
      QuotientBrauer InflatedDefectZeroOrdinary LocalBrauer)
    (theta : QuotientDefectZeroOrdinary)
    (Z0 : Subgroup G) [Z0.Normal]
    (hZ0 : Z0 ≤ Subgroup.center G)
    (innerStabilizer :
      (G ⧸ Subgroup.center G) ≃* AutStabilizer)
    (centrePrimeTo : Prop) (hCentrePrimeTo : centrePrimeTo)
    (global : GlobalBrauer)
    (Qbar : Subgroup (G ⧸ Z0))
    (IntermediateBlockEquality : Subgroup (G ⧸ Z0) → Prop)
    (hNormaliser : IntermediateBlockEquality
      (Subgroup.normalizer (Qbar : Set (G ⧸ Z0)))) :
    IdentityClauseIIIWitness Z0 AutStabilizer centrePrimeTo global
      (R.localBrauer theta) Qbar IntermediateBlockEquality :=
  let W := identityClauseIIIWitness Z0 hZ0 innerStabilizer centrePrimeTo
    hCentrePrimeTo global (R.localBrauer theta) Qbar
    IntermediateBlockEquality hNormaliser
  { W with extensions := identityExtensionPairOfDefectZero R global theta }

@[simp]
theorem identityClauseIIIWitnessOfDefectZero_localExtension
    {QuotientDefectZeroOrdinary QuotientBrauer
      InflatedDefectZeroOrdinary : Type*}
    (R : DefectZeroReductionInflation QuotientDefectZeroOrdinary
      QuotientBrauer InflatedDefectZeroOrdinary LocalBrauer)
    (theta : QuotientDefectZeroOrdinary)
    (Z0 : Subgroup G) [Z0.Normal]
    (hZ0 : Z0 ≤ Subgroup.center G)
    (innerStabilizer :
      (G ⧸ Subgroup.center G) ≃* AutStabilizer)
    (centrePrimeTo : Prop) (hCentrePrimeTo : centrePrimeTo)
    (global : GlobalBrauer)
    (Qbar : Subgroup (G ⧸ Z0))
    (IntermediateBlockEquality : Subgroup (G ⧸ Z0) → Prop)
    (hNormaliser : IntermediateBlockEquality
      (Subgroup.normalizer (Qbar : Set (G ⧸ Z0)))) :
    (identityClauseIIIWitnessOfDefectZero R theta Z0 hZ0 innerStabilizer
      centrePrimeTo hCentrePrimeTo global Qbar IntermediateBlockEquality
      hNormaliser).extensions.localExtension =
        R.reduceInflated (R.inflateOrdinary theta) := by
  exact R.localBrauer_eq_reduceInflated theta

/-- Abstract statement of the exact external bridge in Späth 2017,
Theorem 4.4.  The bridge is deliberately an equivalence, not an assumed
character-triple conclusion. -/
structure SpathTheorem44Interface
    (ClauseIII TripleRelation : Prop) : Prop where
  equivalent : ClauseIII ↔ TripleRelation

/-- The modular character triple relation follows from the clause-(iii)
witness through the exact cited equivalence. -/
theorem modularCharacterTripleRelation_of_clauseIII
    {ClauseIII TripleRelation : Prop}
    (spath44 : SpathTheorem44Interface ClauseIII TripleRelation)
    (hClauseIII : ClauseIII) : TripleRelation :=
  spath44.equivalent.mp hClauseIII

/-- Apply Späth's character-triple reformulation to the witness constructed
above.  The only representation theoretic leaf is the exact Theorem 4.4
interface. -/
theorem modularCharacterTripleRelation_of_identityCollapse
    (Z0 : Subgroup G) [Z0.Normal]
    (hZ0 : Z0 ≤ Subgroup.center G)
    (innerStabilizer :
      (G ⧸ Subgroup.center G) ≃* AutStabilizer)
    (centrePrimeTo : Prop) (hCentrePrimeTo : centrePrimeTo)
    (global : GlobalBrauer) (localBrauer : LocalBrauer)
    (Qbar : Subgroup (G ⧸ Z0))
    (IntermediateBlockEquality : Subgroup (G ⧸ Z0) → Prop)
    (hNormaliser : IntermediateBlockEquality
      (Subgroup.normalizer (Qbar : Set (G ⧸ Z0))))
    (TripleRelation : Prop)
    (spath44 : SpathTheorem44Interface
      (Nonempty (IdentityClauseIIIWitness Z0 AutStabilizer centrePrimeTo
        global localBrauer Qbar IntermediateBlockEquality)) TripleRelation) :
    TripleRelation := by
  apply modularCharacterTripleRelation_of_clauseIII spath44
  exact ⟨identityClauseIIIWitness Z0 hZ0 innerStabilizer
    centrePrimeTo hCentrePrimeTo global localBrauer Qbar
    IntermediateBlockEquality hNormaliser⟩

end ClauseIII

end ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
