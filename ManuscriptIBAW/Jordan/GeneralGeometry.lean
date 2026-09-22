import ManuscriptIBAW.Jordan.Geometry

/-!
# Geometric choices for each label in Lemma 3.2

The finite acting group E may contain field automorphisms, graph
automorphisms and graph automorphisms composed with inner automorphisms. A
finite family of graph generators allows the separate triality construction.
The geometric predicates remain explicit source interpretations. The
stabiliser factorisation, extension and restriction of Brauer characters are
proved separately.
-/

noncomputable section

namespace ManuscriptIBAW.Jordan

variable {ell : ℕ} {k G D E S : Type*}
  [Field k] [Group G] [Group D] [Group E] [Finite E]
  (regular : D →* MulAut G) (actor : E →* MulAut G)

/-- The geometric choice in Feng–Li–Zhang for the specified finite groups and
semisimple label. E is a finite group of automorphisms and need not consist
of field automorphisms. The equations on the finite fixed point group also
cover graph representatives composed with inner automorphisms when the
source chooses such a realisation. -/
structure PermissibleAutomorphismGroup
    (C : GeometricContext (ell := ell) (k := k) (S := S) regular actor) (s : S) where
  group : Subgroup E
  fieldGenerator : E
  GraphIndex : Type
  [graphIndexFinite : Finite GraphIndex]
  graphGenerator : GraphIndex → E
  generated : group = Subgroup.zpowers fieldGenerator ⊔
    Subgroup.closure (Set.range graphGenerator)
  frobeniusLift : Monoid.End C.AlgebraicOvergroup
  graphLift : GraphIndex → MulAut C.AlgebraicOvergroup
  frobenius_lift_kind : C.IsFrobeniusLift frobeniusLift
  graph_lift_kind : ∀ j, C.IsGraphLift (graphLift j)
  frobeniusIterations : ℕ
  frobeniusIterations_positive : 0 < frobeniusIterations
  frobenius_power : C.frobenius = frobeniusLift ^ frobeniusIterations
  lifts_commute : ∀ j, frobeniusLift.comp (graphLift j).toMonoidHom =
    (graphLift j).toMonoidHom.comp frobeniusLift
  field_lift_points : ∀ d, frobeniusLift (C.rationalEmbedding d) =
    C.rationalEmbedding (C.fieldOvergroup fieldGenerator d)
  graph_lift_points : ∀ j d, graphLift j (C.rationalEmbedding d) =
    C.rationalEmbedding (C.fieldOvergroup (graphGenerator j) d)
  levi : Subgroup C.AlgebraicOvergroup
  dual_minimal_levi : C.IsDualMinimalLevi s levi
  levi_frobenius : ∀ x, x ∈ levi ↔ C.frobenius x ∈ levi
  levi_field_lift : ∀ x, x ∈ levi ↔ frobeniusLift x ∈ levi
  levi_graph_lift : ∀ j x, x ∈ levi ↔ graphLift j x ∈ levi
  rationalLevi : Subgroup D
  rationalLevi_iff : ∀ d, d ∈ rationalLevi ↔ C.rationalEmbedding d ∈ levi
  levi_stable : ∀ a : group, ∀ d,
    d ∈ rationalLevi ↔ C.fieldOvergroup a.val d ∈ rationalLevi
  parameter_class_stable : ∀ a : group,
    IsConj (C.dualFieldAction a.val (C.parameter s)) (C.parameter s)
  regular_series_stable : ∀ d, regular d ∈ C.seriesStabilizer s
  actor_series_stable : ∀ a : group, actor a.val ∈ C.seriesStabilizer s
  full_outer_image :
    ((outerProjection G).comp regular).range ⊔
      (((outerProjection G).comp actor).comp group.subtype).range =
        (C.seriesStabilizer s).map (outerProjection G)

attribute [instance] PermissibleAutomorphismGroup.graphIndexFinite

/-- Standard geometric existence, without any representation theoretic
conclusion. The ambient finite acting group need not be a field group. -/
structure GeneralGeometricSelection
    (C : GeometricContext (ell := ell) (k := k) (S := S) regular actor) : Prop where
  exists_group : ∀ s, Nonempty (PermissibleAutomorphismGroup regular actor C s)

section NoGraphSpecialization

variable {C : GeometricContext (ell := ell) (k := k) (S := S) regular actor}
  {s : S}

/-- The geometric assumptions for types B and C specialise those for an
arbitrary finite automorphism group, with the same geometric data. -/
def PermissibleFieldGroup.toGeneral
    (A : PermissibleFieldGroup regular actor C s) :
    PermissibleAutomorphismGroup regular actor C s where
  group := A.group
  fieldGenerator := A.fieldGenerator
  GraphIndex := PUnit
  graphGenerator := fun _ => A.graphGenerator
  generated := by
    rw [A.generated]
    congr 1
    have hset : Set.range (fun _ : PUnit => A.graphGenerator) = {A.graphGenerator} := by
      ext e
      constructor
      · rintro ⟨_, rfl⟩
        rfl
      · intro he
        exact ⟨PUnit.unit, he.symm⟩
    rw [hset, Subgroup.zpowers_eq_closure]
  frobeniusLift := A.frobeniusLift
  graphLift := fun _ => A.graphLift
  frobenius_lift_kind := A.frobenius_lift_kind
  graph_lift_kind := fun _ => A.graph_lift_kind
  frobeniusIterations := A.frobeniusIterations
  frobeniusIterations_positive := A.frobeniusIterations_positive
  frobenius_power := A.frobenius_power
  lifts_commute := fun _ => A.lifts_commute
  field_lift_points := A.field_lift_points
  graph_lift_points := fun _ => A.graph_lift_points
  levi := A.levi
  dual_minimal_levi := A.dual_minimal_levi
  levi_frobenius := A.levi_frobenius
  levi_field_lift := A.levi_field_lift
  levi_graph_lift := fun _ => A.levi_graph_lift
  rationalLevi := A.rationalLevi
  rationalLevi_iff := A.rationalLevi_iff
  levi_stable := A.levi_stable
  parameter_class_stable := A.parameter_class_stable
  regular_series_stable := A.regular_series_stable
  actor_series_stable := A.field_series_stable
  full_outer_image := A.full_outer_image

@[simp] theorem PermissibleFieldGroup.toGeneral_group
    (A : PermissibleFieldGroup regular actor C s) :
    (A.toGeneral regular actor).group = A.group := rfl

end NoGraphSpecialization

section BrauerHypothesis

variable {K : Type*} [Field K] [Finite G]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  (iota : ModularRep.PrimeRegularRootEmbedding ell k K G)

/-- The quantifiers of Lemma 3.2(i), with an arbitrary finite automorphism group
and the specified actions on the original `IBr`. The equations in `C` state
completeness of the labels and identify their series. -/
def GeneralPerLabelHypothesis
    (C : GeometricContext (ell := ell) (k := k) (S := S) regular actor) : Prop :=
  letI := canonicalRegularAction regular iota
  letI := canonicalFieldAction actor iota
  ∀ s, ∃ A : PermissibleAutomorphismGroup regular actor C s,
    RestrictedBrauerHypothesis (D := D) iota actor A.group

/-- Restriction works for an arbitrary finite acting group and an arbitrary
permissible group chosen in it. The acting group need not be cyclic or
consist only of field automorphisms. -/
theorem generalPerLabel_of_fullActor
    (C : GeometricContext (ell := ell) (k := k) (S := S) regular actor)
    (geometry : GeneralGeometricSelection regular actor C)
    (full : letI := canonicalRegularAction regular iota
      letI := canonicalFieldAction actor iota
      FullBrauerHypothesis (D := D) iota actor) :
    GeneralPerLabelHypothesis regular actor iota C := by
  letI := canonicalRegularAction regular iota
  letI := canonicalFieldAction actor iota
  intro s
  obtain ⟨A⟩ := geometry.exists_group s
  exact ⟨A, fullBrauerHypothesis_restrict iota actor A.group full⟩

/-- Geometric source specialization followed by the proved restriction
supplies the general first hypothesis used by Lemma 3.2. -/
theorem generalPerLabel_of_fullField
    (C : GeometricContext (ell := ell) (k := k) (S := S) regular actor)
    (geometry : GeometricSelection regular actor C)
    (full : letI := canonicalRegularAction regular iota
      letI := canonicalFieldAction actor iota
      FullBrauerHypothesis (D := D) iota actor) :
    GeneralPerLabelHypothesis regular actor iota C := by
  letI := canonicalRegularAction regular iota
  letI := canonicalFieldAction actor iota
  intro s
  obtain ⟨A, hA⟩ := perLabel_of_fullField regular actor iota C geometry full s
  exact ⟨A.toGeneral regular actor, hA⟩

end BrauerHypothesis

end ManuscriptIBAW.Jordan

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
