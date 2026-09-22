import Formalisation.EquivariantActions
import ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Relative
import ModularRep.PaperProofs.SporadicFi24P3AnDietrichCharacterTripleTransport
import ModularRep.PaperProofs.SporadicFi24ThreeBlockCharacterTripleRetentionActual
import ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier

/-!
# Concrete factor-set cohomology window for `Fi'_{24}`, `p = 3`

An--Dietrich, Definition 4.4(3d), printed pp. 331--332, compares the
cohomology classes of the factor sets belonging to the two members of a
matched pair, after the natural identification of their stabiliser quotients.
The discussion in Section 4.3.4, printed pp. 333--334, supplies the
centreless `Fi'_{24}` correspondence used by the manuscript.

The manuscript's equivariant-replacement argument does not require a new map
to equal An--Dietrich's published map.  In the centreless case equivariance
identifies the two outer stabiliser quotients, while the cited cyclic
extension theorems make both factor-set classes trivial.  The primary route
in this file formalises exactly that cohomological calculation:

* a factor set is a normalised scalar-valued two-cocycle;
* two factor sets represent the same class when their quotient is the
  coboundary of a one-cochain;
* equality of the two action stabilisers is proved from equivariance;
* a source adapter identifies the corresponding outer stabiliser quotients;
* the ordinary and Brauer cyclic-extension conclusions are supplied as
  projective models obtained by rescaling actual linear extensions; and
* Lean pulls back one cochain and divides it by the other, proving equality
  of the two factor-set cohomology classes.

This refines the cohomology-class layer of
`SporadicEquivariantReplacementLemma55Relative.CyclicFactorSetBridge`; it
reuses `Candidate.stabilizer_eq`, but does not use that bridge's
load-bearing `characterTriple_of_factorClasses` field.  A separate, stronger
same-map theorem transports a source-native Definition 4.4(3d) certificate.

The predicates in this file are deliberately direct factor-set predicates;
they do not populate the otherwise unconstrained relation field of
`FLZSourceSemantics`.  In particular, this is not a proof of the full
modular-character-triple or block-isomorphism relation.  Definition
4.4(3a)--(3c), the actual group
`G_theta`, the representative and local normaliser, the induced automorphism
group, the invariant centraliser character `gamma`, and the identification
of the displayed quotients with the concrete stabiliser groups remain
outside this window.  Existing selected-carrier modules construct important
parts of that group-theoretic infrastructure, but do not yet connect it to
the cocycles defined here.  No field contains the full relation, an
implication to it, BAW, or iBAW.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3AnDietrichConcreteCharacterTriple

open Formalisation
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.CyclicOuterRawPairNormalizer
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24Definition35Operations
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate
open
  ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate.AnDietrichFi24P3SourceCertificate
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichCharacterTripleTransport
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCharacterTripleRetentionActual

universe u

/-! ## Normalised scalar factor sets -/

/-- A normalised scalar factor set on a group.

With the convention `P(g) P(h) = alpha(g,h) P(gh)` for a projective
representation `P`, associativity gives the displayed two-cocycle identity.
The values lie in the units of the coefficient field. -/
structure NormalizedScalarFactorSet (F G : Type u) [Field F] [Group G] where
  toFun : G → G → Fˣ
  map_one_left : ∀ g : G, toFun 1 g = 1
  map_one_right : ∀ g : G, toFun g 1 = 1
  cocycle : ∀ g h j : G,
    toFun g h * toFun (g * h) j =
      toFun h j * toFun g (h * j)

namespace NormalizedScalarFactorSet

variable {F G H : Type u}
variable [Field F] [Group G] [Group H]

instance : CoeFun (NormalizedScalarFactorSet F G) (fun _ ↦ G → G → Fˣ) :=
  ⟨NormalizedScalarFactorSet.toFun⟩

/-- Pull a factor set on `H` back along a group equivalence `G ≃* H`. -/
def pullback (e : G ≃* H) (alpha : NormalizedScalarFactorSet F H) :
    NormalizedScalarFactorSet F G where
  toFun g h := alpha (e g) (e h)
  map_one_left g := by simp only [map_one, alpha.map_one_left]
  map_one_right g := by simp only [map_one, alpha.map_one_right]
  cocycle g h j := by
    simpa only [map_mul] using alpha.cocycle (e g) (e h) (e j)

@[simp]
theorem pullback_apply (e : G ≃* H)
    (alpha : NormalizedScalarFactorSet F H) (g h : G) :
    pullback e alpha g h = alpha (e g) (e h) :=
  rfl

/-- Two normalised scalar factor sets determine the same degree-two
cohomology class when they differ by the coboundary of a normalised
one-cochain. -/
def Cohomologous (alpha beta : NormalizedScalarFactorSet F G) : Prop :=
  ∃ cochain : G → Fˣ,
    cochain 1 = 1 ∧
    ∀ g h : G,
      beta g h =
        cochain g * cochain h * (cochain (g * h))⁻¹ * alpha g h

theorem cohomologous_refl (alpha : NormalizedScalarFactorSet F G) :
    Cohomologous alpha alpha := by
  refine ⟨fun _ ↦ 1, rfl, ?_⟩
  intro g h
  simp

/-- The constant-one factor set. -/
def trivial : NormalizedScalarFactorSet F G where
  toFun _ _ := 1
  map_one_left _ := rfl
  map_one_right _ := rfl
  cocycle _ _ _ := by simp

@[simp]
theorem trivial_apply (g h : G) : trivial (F := F) g h = 1 :=
  rfl

/-- Explicit one-cochain data trivialising a scalar factor set.

This is the concrete form in which the cyclic ordinary/Brauer extension
theorems enter the moving window.  It is strictly below the target pair
relation: it concerns one factor set on one stabiliser quotient. -/
structure Trivialization (alpha : NormalizedScalarFactorSet F G) where
  cochain : G → Fˣ
  cochain_one : cochain 1 = 1
  factor_eq_coboundary : ∀ g h : G,
    alpha g h = cochain g * cochain h * (cochain (g * h))⁻¹

namespace Trivialization

variable {alpha : NormalizedScalarFactorSet F G}

/-- An explicit trivialisation proves that the factor set is cohomologous to
the constant-one factor set. -/
theorem toCohomologous (T : Trivialization alpha) :
    Cohomologous (trivial (F := F) (G := G)) alpha := by
  refine ⟨T.cochain, T.cochain_one, ?_⟩
  intro g h
  simpa only [trivial_apply, mul_one] using T.factor_eq_coboundary g h

/-- Pull an explicit trivialising cochain back with its factor set. -/
def pullback (e : H ≃* G) (T : Trivialization alpha) :
    Trivialization (NormalizedScalarFactorSet.pullback e alpha) where
  cochain h := T.cochain (e h)
  cochain_one := by simpa only [map_one] using T.cochain_one
  factor_eq_coboundary g h := by
    change alpha (e g) (e h) =
      T.cochain (e g) * T.cochain (e h) *
        (T.cochain (e (g * h)))⁻¹
    simpa only [map_mul] using T.factor_eq_coboundary (e g) (e h)

end Trivialization

/-- Minimal projective-realisation data extracted from an actual cyclic
representation extension.

`linearExtension` is an honest representation of the quotient group.  The
projective operators are obtained by rescaling it by `scalarGauge`; their
factor set is consequently the coboundary defined below.  Thus neither a
factor set nor a trivialisation can be chosen independently in a source
certificate.  Identifying this model with the particular projective
representation attached to an An--Dietrich character remains a separately
stated source boundary. -/
structure CyclicExtensionProjectiveModel (F G : Type u)
    [Field F] [Group G] where
  V : ModuleCat.{u} F
  linearExtension : Representation F G V
  scalarGauge : G → Fˣ
  scalarGauge_one : scalarGauge 1 = 1

namespace CyclicExtensionProjectiveModel

variable (M : CyclicExtensionProjectiveModel F G)

/-- The concrete projective operator obtained by rescaling the actual
extension representation. -/
def projectiveOperator (g : G) : M.V →ₗ[F] M.V :=
  (M.scalarGauge g : F) • M.linearExtension g

/-- The normalized scalar factor set forced by the projective scalar lift. -/
def factorSet : NormalizedScalarFactorSet F G where
  toFun g h := M.scalarGauge g * M.scalarGauge h *
    (M.scalarGauge (g * h))⁻¹
  map_one_left g := by rw [M.scalarGauge_one]; simp
  map_one_right g := by rw [M.scalarGauge_one]; simp
  cocycle g h j := by
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- The derived factor set is the multiplier of the concrete projective
operators. -/
theorem projectiveOperator_mul (g h : G) :
    M.projectiveOperator g * M.projectiveOperator h =
      (M.factorSet g h : F) • M.projectiveOperator (g * h) := by
  ext v
  simp [projectiveOperator, factorSet, ← map_mul, smul_smul,
    mul_comm, mul_assoc]
  congr 1
  field_simp

/-- Triviality is a theorem of the projective model, rather than a field of
the surrounding source certificate. -/
def trivialization : Trivialization M.factorSet where
  cochain := M.scalarGauge
  cochain_one := M.scalarGauge_one
  factor_eq_coboundary _ _ := rfl

end CyclicExtensionProjectiveModel

/-- Two explicitly trivialised factor sets determine the same cohomology
class.  Lean constructs the comparison cochain as the quotient of the two
given cochains. -/
theorem cohomologous_of_trivializations
    {alpha beta : NormalizedScalarFactorSet F G}
    (Talpha : Trivialization alpha) (Tbeta : Trivialization beta) :
    Cohomologous alpha beta := by
  refine ⟨fun g ↦ Tbeta.cochain g * (Talpha.cochain g)⁻¹, ?_, ?_⟩
  · change Tbeta.cochain 1 * (Talpha.cochain 1)⁻¹ = 1
    rw [Talpha.cochain_one, Tbeta.cochain_one]
    simp
  · intro g h
    rw [Talpha.factor_eq_coboundary, Tbeta.factor_eq_coboundary]
    simp only [mul_inv_rev, inv_inv]
    simp [mul_comm, mul_left_comm, mul_assoc]

end NormalizedScalarFactorSet

/-! ## Concrete refinement of the cyclic factor-set bridge -/

namespace ConcreteCyclicFactorSetBridge

open ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Relative

variable {A Outer Brauer Weight F : Type u}
variable [Group A] [MulAction A Brauer] [MulAction A Weight]
variable [Group Outer]
variable [Field F]

/-- Source data below the abstract `CyclicFactorSetBridge` used by the
replacement lemma.

`Outer` is the common outer-automorphism quotient.  `outerCyclic` records the
source fact that it is cyclic (for the centreless Fischer case it is a
subquotient of `C2`).  The next three fields identify the quotient
stabilisers.  The final two fields are projective scalar-lift models obtained
from the separately cited ordinary and Brauer cyclic extensions.  Their
factor sets and trivialising one-cochains are definitions, not independently
selectable fields.  There is no field whose type is the pair relation or an
implication to it. -/
structure Source where
  outerCyclic : IsCyclic Outer
  brauerOuterStabilizer : Brauer → Subgroup Outer
  weightOuterStabilizer : Weight → Subgroup Outer
  outerStabilizers_eq_of_stabilizers_eq : ∀ (x : Brauer) (y : Weight),
    MulAction.stabilizer A x = MulAction.stabilizer A y →
      brauerOuterStabilizer x = weightOuterStabilizer y
  brauerProjectiveModel_from_cyclicExtension : ∀ x : Brauer,
    NormalizedScalarFactorSet.CyclicExtensionProjectiveModel F
      (brauerOuterStabilizer x)
  weightProjectiveModel_from_cyclicExtension : ∀ y : Weight,
    NormalizedScalarFactorSet.CyclicExtensionProjectiveModel F
      (weightOuterStabilizer y)

namespace Source

variable (source : Source (A := A) (Outer := Outer)
  (Brauer := Brauer) (Weight := Weight) (F := F))

/-- The global factor set derived from the certified projective model. -/
def brauerFactorSet (x : Brauer) :
    NormalizedScalarFactorSet F (source.brauerOuterStabilizer x) :=
  (source.brauerProjectiveModel_from_cyclicExtension x).factorSet

/-- The local factor set derived from the certified projective model. -/
def weightFactorSet (y : Weight) :
    NormalizedScalarFactorSet F (source.weightOuterStabilizer y) :=
  (source.weightProjectiveModel_from_cyclicExtension y).factorSet

/-- Kernel-derived global trivialisation. -/
def brauerTrivialization_from_cyclicExtension (x : Brauer) :
    NormalizedScalarFactorSet.Trivialization (source.brauerFactorSet x) :=
  (source.brauerProjectiveModel_from_cyclicExtension x).trivialization

/-- Kernel-derived local trivialisation. -/
def weightTrivialization_from_cyclicExtension (y : Weight) :
    NormalizedScalarFactorSet.Trivialization (source.weightFactorSet y) :=
  (source.weightProjectiveModel_from_cyclicExtension y).trivialization

end Source

variable (source : Source (A := A) (Outer := Outer)
  (Brauer := Brauer) (Weight := Weight) (F := F))

/-- The factor-set/cohomology component of Definition 4.4(3d).  The equality
field identifies the two abstract outer stabiliser quotients; the second
field says that the pulled-back local factor set and the global factor set
have the same cohomology class.  This structure does not contain clauses
(3a)--(3c), nor does it assert the full character-triple relation. -/
structure Compatible (x : Brauer) (y : Weight) : Prop where
  outerStabilizer_eq :
    source.brauerOuterStabilizer x = source.weightOuterStabilizer y
  factorSets_cohomologous : NormalizedScalarFactorSet.Cohomologous
    (source.brauerFactorSet x)
    (NormalizedScalarFactorSet.pullback
      (MulEquiv.subgroupCongr outerStabilizer_eq)
      (source.weightFactorSet y))

/-- Equal action stabilisers imply factor-set cohomology compatibility.

The outer-stabiliser identification is a source adapter.  Lean then pulls
back the local trivialising cochain and divides it by the global one. -/
theorem compatible_of_stabilizers_eq (x : Brauer) (y : Weight)
    (hStabilizer : MulAction.stabilizer A x =
      MulAction.stabilizer A y) :
    Compatible source x y := by
  let hOuter : source.brauerOuterStabilizer x =
      source.weightOuterStabilizer y :=
    source.outerStabilizers_eq_of_stabilizers_eq x y hStabilizer
  refine ⟨hOuter, ?_⟩
  exact NormalizedScalarFactorSet.cohomologous_of_trivializations
    (source.brauerTrivialization_from_cyclicExtension x)
    ((source.weightTrivialization_from_cyclicExtension y).pullback
      (MulEquiv.subgroupCongr hOuter))

/-- Concrete counterpart of
`SporadicEquivariantReplacementLemma55Relative.characterTriple_of_cyclic_factor_sets`.

It deliberately reuses that module's kernel theorem
`Candidate.stabilizer_eq`.  The older abstract bridge ends by invoking its
`characterTriple_of_factorClasses` field; here that target-producing step is
not made.  It is replaced only by the explicit cochain calculation in
`compatible_of_stabilizers_eq`. -/
theorem compatible_of_candidate
    {Sector Block Radical : Type u}
    [MulAction A Sector] [MulAction A Block] [MulAction A Radical]
    (C : ReplacementContext
      (A := A) (Sector := Sector) (Block := Block) (Radical := Radical)
      (Brauer := Brauer) (Weight := Weight))
    (W : Candidate C) (x : Brauer) :
    Compatible source x (W.equiv x) :=
  compatible_of_stabilizers_eq source x (W.equiv x)
    (Candidate.stabilizer_eq C W x)

/-- Fully equivariant equivalences are a direct source of the stabiliser
equality used by the concrete cyclic bridge.  Unlike the same-map route below,
this theorem works for an arbitrary equivariant replacement. -/
theorem compatible_of_equivariantEquiv
    (Omega : Brauer ≃ Weight)
    (hOmega : ∀ (a : A) (x : Brauer), Omega (a • x) = a • Omega x)
    (x : Brauer) : Compatible source x (Omega x) :=
  compatible_of_stabilizers_eq source x (Omega x)
    (Formalisation.stabilizer_eq_of_injective_equivariant
      Omega.injective hOmega x)

/-- Factor-set compatibility alone cannot uniformly manufacture the
remaining clauses of Definition 4.4(3), or any other proposed full
character-triple relation.  The constantly-false relation is the precise
countermodel.

This is the residual semantic boundary after the concrete cocycle
calculation above; completing it requires the actual ambient/local carrier,
centraliser and `gamma` data, and the natural quotient isomorphism. -/
theorem no_uniform_full_relation_of_compatible
    {x : Brauer} {y : Weight} (hxy : Compatible source x y) :
    ¬ (∀ fullRelation : Brauer → Weight → Prop,
      Compatible source x y → fullRelation x y) := by
  intro realization
  exact realization (fun _ _ ↦ False) hxy

end ConcreteCyclicFactorSetBridge

/-! ## Instantiation on the selected `C2` outer carrier -/

namespace SelectedOuterFactorSetWindow

open ModularRep.PaperProofs.CyclicOuterRawPairNormalizer

/-- The actual outer subgroup seen by a Brauer stabiliser: the image of the
selected semidirect stabiliser under the projection to the chosen outer
factor.  `stabilizerQuotientEquivProjectionRange` identifies this subgroup
with the stabiliser quotient by the embedded inner stabiliser. -/
noncomputable def brauerOuterStabilizer
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (psi : IBr P.iota) : Subgroup (SelectedOuterGroup S) := by
  letI : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  exact (MulAction.stabilizer (SelectedOuterAmbient S) psi).map
    SemidirectProduct.rightHom

/-- The analogous projection-range subgroup for a weight-class stabiliser. -/
noncomputable def weightOuterStabilizer
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (w : GlobalWeight P) : Subgroup (SelectedOuterGroup S) := by
  letI : MulAction (SelectedOuterAmbient S) (GlobalWeight P) :=
    canonicalWeightSemidirectAction (selectedOuterField S)
  exact (MulAction.stabilizer (SelectedOuterAmbient S) w).map
    SemidirectProduct.rightHom

/-- The chosen Brauer outer subgroup is definitionally the projection range
appearing in the first-isomorphism-theorem quotient equivalence. -/
theorem brauerOuterStabilizer_eq_projectionRange
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (psi : IBr P.iota) :
    let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
      selectedBrauerSemidirectAction P.iota S
    brauerOuterStabilizer P S psi =
      (stabilizerRightHom (phi := selectedOuterField S) psi).range := by
  dsimp only
  let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  ext e
  constructor
  · intro he
    rcases Subgroup.mem_map.mp he with ⟨g, hg, hge⟩
    exact ⟨⟨g, hg⟩, hge⟩
  · rintro ⟨g, hge⟩
    exact Subgroup.mem_map.mpr ⟨g.1, g.2, hge⟩

/-- The same projection-range identification for a weight stabiliser. -/
theorem weightOuterStabilizer_eq_projectionRange
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (w : GlobalWeight P) :
    let _ : MulAction (SelectedOuterAmbient S) (GlobalWeight P) :=
      canonicalWeightSemidirectAction (selectedOuterField S)
    weightOuterStabilizer P S w =
      (stabilizerRightHom (phi := selectedOuterField S) w).range := by
  dsimp only
  let _ : MulAction (SelectedOuterAmbient S) (GlobalWeight P) :=
    canonicalWeightSemidirectAction (selectedOuterField S)
  ext e
  constructor
  · intro he
    rcases Subgroup.mem_map.mp he with ⟨g, hg, hge⟩
    exact ⟨⟨g, hg⟩, hge⟩
  · rintro ⟨g, hge⟩
    exact Subgroup.mem_map.mpr ⟨g.1, g.2, hge⟩

/-- Natural first-isomorphism-theorem identification of the actual Brauer
stabiliser quotient with the selected outer subgroup used by the cocycles. -/
noncomputable def brauerStabilizerQuotientEquiv
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (psi : IBr P.iota) :
    let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
      selectedBrauerSemidirectAction P.iota S
    (semidirectStabilizer (phi := selectedOuterField S) psi ⧸
        embeddedHStabilizer (phi := selectedOuterField S) psi) ≃*
      brauerOuterStabilizer P S psi := by
  dsimp only
  let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  exact (stabilizerQuotientEquivProjectionRange
    (phi := selectedOuterField S) psi).trans
      (MulEquiv.subgroupCongr
        (brauerOuterStabilizer_eq_projectionRange P S psi).symm)

/-- Natural quotient identification on the local weight side. -/
noncomputable def weightStabilizerQuotientEquiv
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (w : GlobalWeight P) :
    let _ : MulAction (SelectedOuterAmbient S) (GlobalWeight P) :=
      canonicalWeightSemidirectAction (selectedOuterField S)
    (semidirectStabilizer (phi := selectedOuterField S) w ⧸
        embeddedHStabilizer (phi := selectedOuterField S) w) ≃*
      weightOuterStabilizer P S w := by
  dsimp only
  let _ : MulAction (SelectedOuterAmbient S) (GlobalWeight P) :=
    canonicalWeightSemidirectAction (selectedOuterField S)
  exact (stabilizerQuotientEquivProjectionRange
    (phi := selectedOuterField S) w).trans
      (MulEquiv.subgroupCongr
        (weightOuterStabilizer_eq_projectionRange P S w).symm)

/-- Source-certified projective realisations on the actual selected outer
projection ranges.

Each field supplies an honest linear representation and a scalar gauge;
factor sets and their trivialisations are derived from those data by Lean.
The selected extension modules separately construct global and local
character-extension witnesses.  The still-missing source bridge must extract
these particular quotient projective realisations from those witnesses and
identify them with the projective representations attached to the relevant
An--Dietrich characters.  The two fields below are exactly that model-level
boundary, not a character-triple conclusion. -/
structure Certificate
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (F : Type u) [Field F] where
  brauerProjectiveModel_from_globalCyclicExtension : ∀ psi : IBr P.iota,
    NormalizedScalarFactorSet.CyclicExtensionProjectiveModel F
      (brauerOuterStabilizer P S psi)
  weightProjectiveModel_from_localCyclicExtension : ∀ w : GlobalWeight P,
    NormalizedScalarFactorSet.CyclicExtensionProjectiveModel F
      (weightOuterStabilizer P S w)

/-- Package the selected projection-range certificate as the concrete
refinement of the older abstract cyclic bridge. -/
noncomputable def Certificate.toConcreteSource
    {F : Type u} [Field F]
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (C : Certificate P S F) :
    @ConcreteCyclicFactorSetBridge.Source
      (SelectedOuterAmbient S) (SelectedOuterGroup S)
      (IBr P.iota) (GlobalWeight P) F inferInstance
      (selectedBrauerSemidirectAction P.iota S)
      (canonicalWeightSemidirectAction (selectedOuterField S))
      inferInstance inferInstance := by
  let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  let _ : MulAction (SelectedOuterAmbient S) (GlobalWeight P) :=
    canonicalWeightSemidirectAction (selectedOuterField S)
  refine {
    outerCyclic := inferInstance
    brauerOuterStabilizer := brauerOuterStabilizer P S
    weightOuterStabilizer := weightOuterStabilizer P S
    outerStabilizers_eq_of_stabilizers_eq := ?_
    brauerProjectiveModel_from_cyclicExtension :=
      C.brauerProjectiveModel_from_globalCyclicExtension
    weightProjectiveModel_from_cyclicExtension :=
      C.weightProjectiveModel_from_localCyclicExtension }
  intro psi w hStabilizer
  change
    (MulAction.stabilizer (SelectedOuterAmbient S) psi).map
        SemidirectProduct.rightHom =
      (MulAction.stabilizer (SelectedOuterAmbient S) w).map
        SemidirectProduct.rightHom
  exact congrArg
    (fun T : Subgroup (SelectedOuterAmbient S) ↦
      T.map SemidirectProduct.rightHom) hStabilizer

/-- The generic cocycle compatibility predicate with both selected
semidirect actions fixed explicitly. -/
def Compatible
    {F : Type u} [Field F]
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (C : Certificate P S F) (psi : IBr P.iota) (w : GlobalWeight P) : Prop :=
  @ConcreteCyclicFactorSetBridge.Compatible
    (SelectedOuterAmbient S) (SelectedOuterGroup S)
    (IBr P.iota) (GlobalWeight P) F inferInstance
    (selectedBrauerSemidirectAction P.iota S)
    (canonicalWeightSemidirectAction (selectedOuterField S))
    inferInstance inferInstance (C.toConcreteSource P S) psi w

/-- An arbitrary fully automorphism-equivariant replacement has matching
selected outer projection ranges and cohomologous factor sets.  No equality
with An--Dietrich's original map is used. -/
theorem compatible_of_automorphismEquivariant
    {F : Type u} [Field F]
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (C : Certificate P S F)
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (psi : IBr P.iota) : Compatible P S C psi (Omega psi) := by
  unfold Compatible
  let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  let _ : MulAction (SelectedOuterAmbient S) (GlobalWeight P) :=
    canonicalWeightSemidirectAction (selectedOuterField S)
  apply ConcreteCyclicFactorSetBridge.compatible_of_equivariantEquiv
    (C.toConcreteSource P S) Omega
  exact selectedOmega_semidirect_equivariant P S Omega hOmega

end SelectedOuterFactorSetWindow

/-! ## Concrete selected-carrier part of Definition 4.4(3) -/

namespace SelectedClause3CarrierWindow

open ModularRep.PaperProofs.CyclicOuterRawPairNormalizer

/-- Group-theoretic data already constructed by the selected-outer Fischer
modules for one equivariantly matched pair.

The ambient group is the concrete `SelectedSpathAmbient`; the two displayed
equivalences identify the selected raw-pair stabiliser and its base with the
actual local normaliser and local base.  The centraliser conclusion is
stronger than Definition 4.4(3b), because it is trivial.

This is deliberately not called a Definition 4.4(3) witness.  It does not
contain the product assertion in (3a), the invariant character `gamma` from
(3c), or the projective representations and natural quotient comparison in
(3d). -/
structure GroupWindow
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) : Type u where
  matched : w.1 = Omega psi.1
  pairStabilizer_eq :
    SelectedPairStabilizer P S w =
      SelectedBrauerAmbient P.iota S psi.1 ⊓
        Subgroup.normalizer
          (rawAmbientRadical (selectedOuterField S)
            (selectedRawWeight P.blockSource P.block w) :
              Set (SelectedOuterAmbient S))
  baseCentralizer_eq_bot :
    Subgroup.centralizer
      (SelectedBrauerBase P.iota S psi.1 :
        Set (SelectedBrauerAmbient P.iota S psi.1)) = ⊥
  ambientCenter_eq_bot :
    Subgroup.center (SelectedBrauerAmbient P.iota S psi.1) = ⊥
  localNormalizerEquiv :
    SelectedPairStabilizer P S w ≃*
      SelectedLocalGroup P hcenter reference psi w S haut
  localBaseEquiv :
    SelectedPairBase P S w ≃*
      SelectedLocalBase P hcenter reference psi w S haut

/-- Combine the concrete selected-carrier window.  Every field is filled by
an existing selected-outer kernel construction; the only hypotheses about
the replacement are equivariance and that `w` is its value at `psi`. -/
noncomputable def ofEquivariantMatch
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    GroupWindow P hcenter reference psi w S Omega haut where
  matched := hmatch
  pairStabilizer_eq :=
    selectedPairStabilizer_eq_brauer_inf_normalizer
      P S Omega hOmega psi w hmatch
  baseCentralizer_eq_bot :=
    selectedBrauerBase_centralizer_eq_bot P S psi hcenter haut
  ambientCenter_eq_bot :=
    selectedBrauerAmbient_center_eq_bot P S psi hcenter haut
  localNormalizerEquiv :=
    selectedPairStabilizerEquivAmbientLocalGroup
      P hcenter reference psi w S Omega hOmega hmatch haut
  localBaseEquiv :=
    selectedPairBaseEquivAmbientLocalBase
      P hcenter reference psi w S Omega hOmega hmatch haut

/-- The packaged local-normaliser equivalence is the natural inclusion into
the selected semidirect ambient group. -/
@[simp]
theorem ofEquivariantMatch_localNormalizerEquiv_apply_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (d : SelectedPairStabilizer P S w) :
    (((((ofEquivariantMatch P hcenter reference psi w S Omega
          hOmega hmatch haut).localNormalizerEquiv d :
        SelectedLocalGroup P hcenter reference psi w S haut) :
      SelectedBrauerAmbient P.iota S psi.1) :
      SelectedOuterAmbient S)) = d.1 := by
  exact selectedPairStabilizerEquivAmbientLocalGroup_apply_coe
    P hcenter reference psi w S Omega hOmega hmatch haut d

/-- The packaged base equivalence is natural under the inclusions into the
selected ambient group. -/
@[simp]
theorem ofEquivariantMatch_localBaseEquiv_apply_outer_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (h : SelectedPairBase P S w) :
    (((((ofEquivariantMatch P hcenter reference psi w S Omega
          hOmega hmatch haut).localBaseEquiv h :
        SelectedLocalBase P hcenter reference psi w S haut) :
      SelectedLocalGroup P hcenter reference psi w S haut) :
      SelectedBrauerAmbient P.iota S psi.1) :
      SelectedOuterAmbient S) =
        (((h : SelectedPairStabilizer P S w) :
          SelectedOuterAmbient S)) := by
  exact selectedPairBaseEquivAmbientLocalBase_apply_outer_coe
    P hcenter reference psi w S Omega hOmega hmatch haut h

end SelectedClause3CarrierWindow

/-! ## Secondary same-map action-stabiliser model of clause (3d) -/

variable {SourceAction SourceBrauer SourceWeight F : Type u}
variable [Group SourceAction]
variable [MulAction SourceAction SourceBrauer]
variable [MulAction SourceAction SourceWeight]
variable [Field F]

variable
  (AD : AnDietrichFi24P3SourceCertificate
    (SourceAction := SourceAction)
    (SourceBrauer := SourceBrauer)
    (SourceWeight := SourceWeight))

/-- Equivariance and injectivity of the published correspondence identify the
two stabilisers of every published matched pair.  This is a kernel theorem,
not a certificate field. -/
theorem sourceStabilizer_eq (phi : SourceBrauer) :
    MulAction.stabilizer SourceAction phi =
      MulAction.stabilizer SourceAction (AD.sourceEquiv phi) :=
  Formalisation.stabilizer_eq_of_injective_equivariant
    AD.sourceEquiv.injective AD.sourceEquivariant phi

/-- The group equivalence between the two equal source-action stabilisers.

This is not, by itself, An--Dietrich's natural isomorphism between the two
displayed quotient groups in Definition 4.4(3d).  Relating this action model
to those quotients is an explicit residual source boundary. -/
def sourceStabilizerEquiv (phi : SourceBrauer) :
    MulAction.stabilizer SourceAction phi ≃*
      MulAction.stabilizer SourceAction (AD.sourceEquiv phi) :=
  MulEquiv.subgroupCongr (sourceStabilizer_eq AD phi)

/-- Source-heavy projective models for an action-stabiliser approximation to
An--Dietrich, Definition 4.4(3d).

The two model families are indexed independently by published Brauer and
weight objects.  Their factor sets and trivialising cochains are derived by
Lean from the actual linear representations and scalar gauges stored in the
models.  A concrete use as the published clause additionally requires a
source identification of these action stabilisers, representations, and
factor sets with the actual quotients and projective representations in
Definition 4.4(3d).  It neither mentions literal carriers nor contains the
live Definition 3.5 predicate. -/
structure AnDietrichDefinition44FactorSetCertificate where
  brauerProjectiveModel : ∀ phi : SourceBrauer,
    NormalizedScalarFactorSet.CyclicExtensionProjectiveModel F
      (MulAction.stabilizer SourceAction phi)
  weightProjectiveModel : ∀ weight : SourceWeight,
    NormalizedScalarFactorSet.CyclicExtensionProjectiveModel F
      (MulAction.stabilizer SourceAction weight)

namespace AnDietrichDefinition44FactorSetCertificate

variable (C : AnDietrichDefinition44FactorSetCertificate
  (SourceAction := SourceAction) (SourceBrauer := SourceBrauer)
  (SourceWeight := SourceWeight) (F := F))

def brauerFactorSet (phi : SourceBrauer) : NormalizedScalarFactorSet F
    (MulAction.stabilizer SourceAction phi) :=
  (C.brauerProjectiveModel phi).factorSet

def weightFactorSet (weight : SourceWeight) : NormalizedScalarFactorSet F
    (MulAction.stabilizer SourceAction weight) :=
  (C.weightProjectiveModel weight).factorSet

/-- Clause-(3d) cohomology at the published pair is now derived from the two
cyclic-extension projective models. -/
theorem publishedPairCohomologous (phi : SourceBrauer) :
    NormalizedScalarFactorSet.Cohomologous
      (C.brauerFactorSet phi)
      (NormalizedScalarFactorSet.pullback
        (sourceStabilizerEquiv AD phi)
        (C.weightFactorSet (AD.sourceEquiv phi))) :=
  NormalizedScalarFactorSet.cohomologous_of_trivializations
    (C.brauerProjectiveModel phi).trivialization
    ((C.weightProjectiveModel (AD.sourceEquiv phi)).trivialization.pullback
      (sourceStabilizerEquiv AD phi))

end AnDietrichDefinition44FactorSetCertificate

variable
  (factorSets : AnDietrichDefinition44FactorSetCertificate
    (SourceAction := SourceAction) (SourceBrauer := SourceBrauer)
    (SourceWeight := SourceWeight) (F := F))

/-- Concrete witness that a published Brauer object and weight object have
equal stabilisers and cohomologous factor sets under that identification. -/
structure FactorSetComparisonWitness
    (phi : SourceBrauer) (weight : SourceWeight) : Prop where
  stabilizer_eq :
    MulAction.stabilizer SourceAction phi =
      MulAction.stabilizer SourceAction weight
  cohomologous : NormalizedScalarFactorSet.Cohomologous
    (factorSets.brauerFactorSet phi)
    (NormalizedScalarFactorSet.pullback
      (MulEquiv.subgroupCongr stabilizer_eq)
      (factorSets.weightFactorSet weight))

/-- The action-stabiliser factor-set component retained in this moving
window: existence of the stabiliser identification and equality of the two
factor-set cohomology classes. -/
def FactorSetCompatible (phi : SourceBrauer) (weight : SourceWeight) : Prop :=
  FactorSetComparisonWitness factorSets phi weight

/-- The published matched pair satisfies the action-stabiliser factor-set
predicate.  Lean supplies its stabiliser equality and derives cohomology
equality from the two projective models. -/
theorem factorSetCompatible_publishedPair (phi : SourceBrauer) :
    FactorSetCompatible factorSets phi (AD.sourceEquiv phi) := by
  refine ⟨sourceStabilizer_eq AD phi, ?_⟩
  exact factorSets.publishedPairCohomologous AD phi

/-! ## Same-map transport to the literal Definition 3.5 carriers -/

variable {k K X Gamma : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable [Group Gamma] [Finite Gamma]

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
variable (block : ActualBlock (k := k) (X := X))
variable (gamma : Gamma →* MulAut X)
variable (gammaBlock_fixed : ∀ a : Gamma,
  inverseOpHom gamma a • block = block)
variable (localReduction : ∀ w : LiteralWeightFibre R.1 block,
  SelectedLocalReductionSource R.1 block w)

variable
  (Bridge : AnDietrichFi24P3LiteralCarrierBridge
    (SourceAction := SourceAction)
    (SourceBrauer := SourceBrauer)
    (SourceWeight := SourceWeight) (k := k) (K := K) (X := X) iota)

/-- Direct factor-set predicate on the literal Definition 3.5 carriers.

It transports a literal pair back to the published An--Dietrich carriers and
asks only for the explicit action-stabiliser factor-set witness above.  It is
not packaged as an FLZ semantics object and is not the live character-triple
or block-isomorphism relation. -/
def LiteralFactorSetCompatible
    (psi : Definition35Brauer
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction))
    (weight : Definition35Weight
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction)) : Prop :=
  FactorSetCompatible factorSets
    (Bridge.brauerIdentification psi.1)
    (Bridge.weightIdentification.symm weight.1)

/-- Pointwise equality with the transported published map becomes equality
of the corresponding source weight objects. -/
theorem sourceWeight_eq_of_sameMap
    (replacement : Definition35Brauer
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction) ≃
      Definition35Weight
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction))
    (sameMap : ∀ psi : Definition35Brauer
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction),
      (replacement psi).1 = literalEquiv iota AD Bridge psi.1)
    (psi : Definition35Brauer
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction)) :
    Bridge.weightIdentification.symm (replacement psi).1 =
      AD.sourceEquiv (Bridge.brauerIdentification psi.1) := by
  calc
    Bridge.weightIdentification.symm (replacement psi).1 =
        Bridge.weightIdentification.symm
          (literalEquiv iota AD Bridge psi.1) :=
      congrArg Bridge.weightIdentification.symm (sameMap psi)
    _ = AD.sourceEquiv (Bridge.brauerIdentification psi.1) := by
      change Bridge.weightIdentification.symm
        (Bridge.weightIdentification
          (AD.sourceEquiv (Bridge.brauerIdentification psi.1))) = _
      exact Bridge.weightIdentification.symm_apply_apply _

/-- Kernel transport from the source-native action-stabiliser factor-set
witness and same-map equality to the direct literal factor-set predicate.

The source certificate is used only at the published pair.  The final change
of the weight index is forced by `sameMap` and checked by Lean. -/
theorem literalFactorSetCompatible_of_sameMap
    (replacement : Definition35Brauer
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction) ≃
      Definition35Weight
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction))
    (sameMap : ∀ psi : Definition35Brauer
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction),
      (replacement psi).1 = literalEquiv iota AD Bridge psi.1)
    (psi : Definition35Brauer
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction)) :
    LiteralFactorSetCompatible
      (factorSets := factorSets) (iota := iota) (hinj := hinj)
      (R := R) (block := block) (gamma := gamma)
      (gammaBlock_fixed := gammaBlock_fixed)
      (localReduction := localReduction) (Bridge := Bridge)
      psi (replacement psi) := by
  change FactorSetCompatible factorSets
    (Bridge.brauerIdentification psi.1)
    (Bridge.weightIdentification.symm (replacement psi).1)
  rw [sourceWeight_eq_of_sameMap
    (AD := AD) (iota := iota) (hinj := hinj) (R := R) (block := block)
    (gamma := gamma) (gammaBlock_fixed := gammaBlock_fixed)
    (localReduction := localReduction) (Bridge := Bridge)
    replacement sameMap psi]
  exact factorSetCompatible_publishedPair AD factorSets
    (Bridge.brauerIdentification psi.1)

/-- The same theorem using the existing same-map binding.  Only its
`sameMap` field is needed.  The conclusion remains only the direct
factor-set predicate. -/
theorem literalFactorSetCompatible_of_binding
    (replacement : Definition35Brauer
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction) ≃
      Definition35Weight
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction))
    (binding : AnDietrichDefinition44SameMapBinding
      iota hinj R block gamma gammaBlock_fixed localReduction AD Bridge
      replacement)
    (psi : Definition35Brauer
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction)) :
    LiteralFactorSetCompatible
      (factorSets := factorSets) (iota := iota) (hinj := hinj)
      (R := R) (block := block) (gamma := gamma)
      (gammaBlock_fixed := gammaBlock_fixed)
      (localReduction := localReduction) (Bridge := Bridge)
      psi (replacement psi) :=
  literalFactorSetCompatible_of_sameMap
    (AD := AD) (factorSets := factorSets) (iota := iota) (hinj := hinj)
    (R := R) (block := block) (gamma := gamma)
    (gammaBlock_fixed := gammaBlock_fixed)
    (localReduction := localReduction) (Bridge := Bridge)
    replacement binding.sameMap psi

end ModularRep.PaperProofs.SporadicFi24P3AnDietrichConcreteCharacterTriple


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
