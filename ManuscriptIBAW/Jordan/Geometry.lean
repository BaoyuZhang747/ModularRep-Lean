import ManuscriptIBAW.Jordan.BrauerRestriction

/-!
# The geometric choice before restriction

This file states the construction in Feng–Li–Zhang, Section 5, for types B
and C without triality. A permissible choice includes the geometric data and
their equations. The conditions on Brauer representatives, stabilisers and
extensions are separate.

The finite group of field automorphisms is not assumed to act on the whole
algebraic group. Only the selected generators have algebraic lifts, with
their equations on the finite fixed point group. The defining Frobenius need
not act as the identity away from those fixed points.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ManuscriptIBAW.Jordan

section OuterQuotient

variable (G : Type*) [Group G]

def innerAutomorphisms : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

instance innerAutomorphisms_normal : (innerAutomorphisms G).Normal where
  conj_mem _ ha beta := by
    obtain ⟨g, rfl⟩ := ha
    refine ⟨beta g, ?_⟩
    apply MulEquiv.ext
    intro x
    change beta g * x * (beta g)⁻¹ = beta (g * beta⁻¹ x * g⁻¹)
    simp only [map_mul, map_inv, MulAut.apply_inv_self]

abbrev OuterAutomorphism := MulAut G ⧸ innerAutomorphisms G

def outerProjection : MulAut G →* OuterAutomorphism G :=
  QuotientGroup.mk' (innerAutomorphisms G)

end OuterQuotient

variable {ell : ℕ} {k G D E S : Type*}
  [Field k] [Group G] [Group D] [Group E]
  (regular : D →* MulAut G) (field : E →* MulAut G)

/-- Source data (E1/U) for the regular embedding and semisimple labels.
`IsDualMinimalLevi s L` is specifically the geometric statement that `L` is
dual to the minimal Levi containing the connected and rational centralisers
of the chosen semisimple parameter. It is not a representation theoretic or
inductive condition predicate. -/
structure GeometricContext where
  AlgebraicOvergroup : Type*
  [algebraicGroup : Group AlgebraicOvergroup]
  rationalEmbedding : D →* AlgebraicOvergroup
  rationalEmbedding_injective : Function.Injective rationalEmbedding
  frobenius : Monoid.End AlgebraicOvergroup
  IsFrobeniusLift : Monoid.End AlgebraicOvergroup → Prop
  IsGraphLift : MulAut AlgebraicOvergroup → Prop
  fixedPoints : ∀ x, frobenius x = x ↔ ∃ d, rationalEmbedding d = x
  baseEmbedding : G →* D
  baseEmbedding_injective : Function.Injective baseEmbedding
  conjugation : ∀ d g,
    baseEmbedding (regular d g) = d * baseEmbedding g * d⁻¹
  fieldOvergroup : E →* MulAut D
  fieldOnBase : ∀ e g,
    baseEmbedding (field e g) = fieldOvergroup e (baseEmbedding g)
  DualFiniteGroup : Type*
  [dualGroup : Group DualFiniteGroup]
  [dualFinite : Finite DualFiniteGroup]
  semisimple : DualFiniteGroup → Prop
  parameter : S → DualFiniteGroup
  parameter_semisimple : ∀ s, semisimple (parameter s)
  parameter_order : ∀ s, Nat.Coprime (orderOf (parameter s)) ell
  parameter_complete : ∀ t, semisimple t → Nat.Coprime (orderOf t) ell →
    ∃ s, IsConj (parameter s) t
  dualFieldAction : E →* MulAut DualFiniteGroup
  seriesIdempotent : S → k[G]
  seriesAtParameter : DualFiniteGroup → k[G]
  series_parameter : ∀ s, seriesIdempotent s = seriesAtParameter (parameter s)
  series_conjugate : ∀ s t, IsConj s t → seriesAtParameter s = seriesAtParameter t
  series_central : ∀ s, IsMulCentral (seriesIdempotent s)
  series_idempotent : ∀ s, IsIdempotentElem (seriesIdempotent s)
  seriesStabilizer : S → Subgroup (MulAut G)
  seriesStabilizer_iff : ∀ s a,
    a ∈ seriesStabilizer s ↔
      MonoidAlgebra.mapDomainRingEquiv k a (seriesIdempotent s) = seriesIdempotent s
  IsDualMinimalLevi : S → Subgroup AlgebraicOvergroup → Prop

attribute [instance] GeometricContext.algebraicGroup
  GeometricContext.dualGroup GeometricContext.dualFinite

/-- A choice in the construction of Feng–Li–Zhang, Section 5, for types B and C
without triality. The finite acting group is the specified field group.
General graph automorphisms and type D4 require separate data. -/
structure PermissibleFieldGroup
    (C : GeometricContext (ell := ell) (k := k) (S := S) regular field) (s : S) where
  group : Subgroup E
  fieldGenerator : E
  graphGenerator : E
  generated : group = Subgroup.zpowers fieldGenerator ⊔ Subgroup.zpowers graphGenerator
  noGraph : graphGenerator = 1
  frobeniusLift : Monoid.End C.AlgebraicOvergroup
  graphLift : MulAut C.AlgebraicOvergroup
  frobenius_lift_kind : C.IsFrobeniusLift frobeniusLift
  graph_lift_kind : C.IsGraphLift graphLift
  frobeniusIterations : ℕ
  frobeniusIterations_positive : 0 < frobeniusIterations
  frobenius_power : C.frobenius = frobeniusLift ^ frobeniusIterations
  lifts_commute : frobeniusLift.comp graphLift.toMonoidHom =
    graphLift.toMonoidHom.comp frobeniusLift
  field_lift_points : ∀ d,
    frobeniusLift (C.rationalEmbedding d) =
      C.rationalEmbedding (C.fieldOvergroup fieldGenerator d)
  graph_lift_points : ∀ d,
    graphLift (C.rationalEmbedding d) =
      C.rationalEmbedding (C.fieldOvergroup graphGenerator d)
  levi : Subgroup C.AlgebraicOvergroup
  dual_minimal_levi : C.IsDualMinimalLevi s levi
  levi_frobenius : ∀ x, x ∈ levi ↔ C.frobenius x ∈ levi
  levi_field_lift : ∀ x, x ∈ levi ↔ frobeniusLift x ∈ levi
  levi_graph_lift : ∀ x, x ∈ levi ↔ graphLift x ∈ levi
  rationalLevi : Subgroup D
  rationalLevi_iff : ∀ d, d ∈ rationalLevi ↔ C.rationalEmbedding d ∈ levi
  levi_stable : ∀ a : group, ∀ d,
    d ∈ rationalLevi ↔ C.fieldOvergroup a.val d ∈ rationalLevi
  parameter_class_stable : ∀ a : group,
    IsConj (C.dualFieldAction a.val (C.parameter s)) (C.parameter s)
  regular_series_stable : ∀ d, regular d ∈ C.seriesStabilizer s
  field_series_stable : ∀ a : group, field a.val ∈ C.seriesStabilizer s
  full_outer_image :
    ((outerProjection G).comp regular).range ⊔
      (((outerProjection G).comp field).comp group.subtype).range =
        (C.seriesStabilizer s).map (outerProjection G)

/-- The geometric existence assertion from the regular embedding and
automorphism sources. -/
structure GeometricSelection
    (C : GeometricContext (ell := ell) (k := k) (S := S) regular field) : Prop where
  exists_group : ∀ s, Nonempty (PermissibleFieldGroup regular field C s)

def GeometricSelection.choose
    {C : GeometricContext (ell := ell) (k := k) (S := S) regular field}
    (source : GeometricSelection regular field C) (s : S) :
    PermissibleFieldGroup regular field C s :=
  Classical.choice (source.exists_group s)

section Application

variable {K : Type*} [Field K] [Finite G]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  (iota : ModularRep.PrimeRegularRootEmbedding ell k K G)

@[instance_reducible] def canonicalRegularAction : MulAction D (ModularRep.IBr iota) :=
  ModularRep.PaperProofs.EvenFieldAssumption53Relative.rightAutomorphismAction iota regular

@[instance_reducible] def canonicalFieldAction : MulAction E (ModularRep.IBr iota) :=
  ModularRep.PaperProofs.EvenFieldAssumption53Relative.rightAutomorphismAction iota field

/-- The order of choices agrees with manuscript Lemma 3.2(i): choose
`A_s` for each label first, then give the required representative in every orbit of the regular group. -/
theorem perLabel_of_fullField
    (C : GeometricContext (ell := ell) (k := k) (S := S) regular field)
    (geometry : GeometricSelection regular field C)
    (full : letI := canonicalRegularAction regular iota
      letI := canonicalFieldAction field iota
      FullBrauerHypothesis (D := D) iota field) :
    letI := canonicalRegularAction regular iota
    letI := canonicalFieldAction field iota
    ∀ s, ∃ A : PermissibleFieldGroup regular field C s,
      RestrictedBrauerHypothesis (D := D) iota field A.group := by
  letI := canonicalRegularAction regular iota
  letI := canonicalFieldAction field iota
  intro s
  let A := geometry.choose regular field s
  exact ⟨A, fullBrauerHypothesis_restrict iota field A.group full⟩

end Application

end ManuscriptIBAW.Jordan

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
