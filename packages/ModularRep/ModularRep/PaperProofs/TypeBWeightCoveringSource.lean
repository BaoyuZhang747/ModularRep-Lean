import ModularRep.PaperProofs.TypeBInertiaHallSource
import ModularRep.BlockCentralBrauerImage
import ModularRep.PrimitiveBlockAutomorphism

/-!
# Literal local data for weight covering in the Type B lane

The carrier below is generic in a finite ambient group and its fixed normal
subgroup, so that the published criterion can quantify over that same
carrier.  The Type B application substitutes special Clifford and Spin.

The source is Brough--Spaeth, Section 2, the construction preceding
Definition 2.6 (`DfCovWt`), Definition 2.6, and the following lemma
(`covWeight`).  The DGN construction is the use of Navarro--Spaeth,
Theorem 5.2 described there.  Theorem 2.10, p. 470 (`DZBijRDZ`) explains its relation
to relative defect-zero characters and induction; that bijection is not
an input to the deductions here.

`OrdinaryOccursInRestriction` is an actual character equation.
`CoversRaw` and `CoversClass` are definitions through the literal
intermediate quotient, defect subgroup, centralizer and DGN character.
There is no supplied `covers`, `liesOver`, matching or goodness predicate.

Source boundary: the ordinary block selector in `DefectBlockData` must be
the selector in a fixed splitting modular system. Its identification is U
until the coefficient/decomposition binding is supplied. Likewise a
`DGNSource` must be the published correspondence on exactly these carriers;
the record alone does not authenticate its values. `BroughCoveringNonemptySource`
is the exact one-way nonemptiness use of `covWeight` for that source. No
unconditional existence of these source records is claimed.
-/

noncomputable section

open scoped Pointwise MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBWeightCoveringSource

open ModularRep OrdinaryIrreducibleCharacter

variable {ell : ℕ} {K k A : Type}
variable [Field K] [CharZero K] [Field k] [CharP k ell]
variable [Group A] [Finite A]

/-- Actual occurrence along the displayed group homomorphism, expressed as
a finite nonnegative integral ordinary-character expansion. For restriction
the homomorphism is required separately to be the literal embedding. -/
def OrdinaryOccursInRestriction
    {H J : Type} [Group H] [Group J]
    (f : H →* J) (chi : Irr K J) (theta : Irr K H) : Prop :=
  ∃ multiplicity : Irr K H →₀ ℕ,
    multiplicity theta ≠ 0 ∧
      ∀ x : H, chi (f x) = multiplicity.sum (fun psi m ↦ (m : K) * psi x)

variable (G0 : Subgroup A) [G0.Normal]

abbrev BaseWeight := CharacterWeight ell K G0
abbrev AmbientWeight := CharacterWeight ell K A

/-- The ambient image of the actual downstairs radical subgroup. -/
def baseRadicalImage (W : BaseWeight (ell := ell) (K := K) G0) : Subgroup A :=
  W.subgroup.map G0.subtype

/-- The ambient image of its downstairs normalizer. -/
def baseNormalizerImage (W : BaseWeight (ell := ell) (K := K) G0) : Subgroup A :=
  (Subgroup.normalizer (W.subgroup : Set G0)).map G0.subtype

/-- The source's intermediate group is fixed as N_G(Q) Qtilde. -/
def intermediate
    (W : BaseWeight (ell := ell) (K := K) G0)
    (V : AmbientWeight (ell := ell) (K := K) (A := A)) : Subgroup A :=
  baseNormalizerImage G0 W ⊔ V.subgroup

/-- The elementary setup preceding the published covering definition.
Normality and character invariance are on actual elements, not on a supplied
action. The two normality fields permit the literal quotient carriers. -/
structure IntermediateData
    (W : BaseWeight (ell := ell) (K := K) G0)
    (V : AmbientWeight (ell := ell) (K := K) (A := A)) where
  base_le_up : baseRadicalImage G0 W ≤ V.subgroup
  normalizes_base : intermediate G0 W V ≤
    Subgroup.normalizer (baseRadicalImage G0 W : Set A)
  radical_normal :
    ((baseRadicalImage G0 W).subgroupOf (intermediate G0 W V)).Normal
  normalizer_normal :
    ((baseNormalizerImage G0 W).subgroupOf (intermediate G0 W V)).Normal
  character_invariant : ∀ m : intermediate G0 W V,
    ∀ x y : Subgroup.normalizer (W.subgroup : Set G0),
      ((y : G0) : A) = (m : A) * ((x : G0) : A) * (m : A)⁻¹ →
        W.localCharacter (QuotientGroup.mk y) =
          W.localCharacter (QuotientGroup.mk x)

namespace IntermediateData

variable {G0}
variable {W : BaseWeight (ell := ell) (K := K) G0}
variable {V : AmbientWeight (ell := ell) (K := K) (A := A)}
variable (T : IntermediateData G0 W V)

/-- M/Q, with Q its actual ambient image inside the fixed intermediate M. -/
def Quotient (_T : IntermediateData G0 W V) : Type := intermediate G0 W V ⧸
  (baseRadicalImage G0 W).subgroupOf (intermediate G0 W V)

instance quotientGroup : Group T.Quotient := by
  letI := T.radical_normal
  unfold Quotient
  infer_instance

instance quotientFinite : Finite T.Quotient := by
  unfold Quotient
  infer_instance

/-- The other literal intermediate quotient M/N_G(Q). -/
def OverBaseQuotient (_T : IntermediateData G0 W V) : Type :=
  intermediate G0 W V ⧸
    (baseNormalizerImage G0 W).subgroupOf (intermediate G0 W V)

instance overBaseQuotientGroup : Group T.OverBaseQuotient := by
  letI := T.normalizer_normal
  unfold OverBaseQuotient
  infer_instance

def quotientMap : intermediate G0 W V →* T.Quotient := by
  letI := T.radical_normal
  exact QuotientGroup.mk' _

/-- The image Qtilde/Q is the nominated defect subgroup, not an unrelated
abstract p-group. -/
def defect : Subgroup T.Quotient :=
  (V.subgroup.subgroupOf (intermediate G0 W V)).map T.quotientMap

def baseImage : Subgroup T.Quotient :=
  ((baseNormalizerImage G0 W).subgroupOf (intermediate G0 W V)).map T.quotientMap

/-- C_(N_G(Q)/Q)(Qtilde/Q), inside M/Q. -/
def centralizer : Subgroup T.Quotient :=
  T.baseImage ⊓ Subgroup.centralizer (T.defect : Set T.Quotient)

def normalizerLift (_T : IntermediateData G0 W V)
    (x : Subgroup.normalizer (W.subgroup : Set G0)) : intermediate G0 W V :=
  ⟨(x : G0),
    (show baseNormalizerImage G0 W ≤ intermediate G0 W V from le_sup_left)
      (show ((x : G0) : A) ∈ baseNormalizerImage G0 W from
        ⟨(x : G0), x.property, rfl⟩)⟩

end IntermediateData

/-- Exact quotient/centralizer comparison maps in the covering construction.
Their displayed pointwise equations bind them to inclusions and quotient
maps, so a source cannot replace a local set of characters by an unrelated
isomorphic group. The product and intersection conditions record the
complement conclusion in the source setup. -/
structure LocalGeometry
    {W : BaseWeight (ell := ell) (K := K) G0}
    {V : AmbientWeight (ell := ell) (K := K) (A := A)}
    (T : IntermediateData G0 W V) where
  quotient_isPGroup : IsPGroup ell T.OverBaseQuotient
  defect_isPGroup : IsPGroup ell T.defect
  quotient_product : T.baseImage ⊔ T.defect = ⊤
  quotient_intersection : T.baseImage ⊓ T.defect = ⊥
  thetaEmbedding : NormalizerQuotient W.subgroup →* T.Quotient
  thetaEmbedding_injective : Function.Injective thetaEmbedding
  thetaEmbedding_range : thetaEmbedding.range = T.baseImage
  thetaEmbedding_mk : ∀ x : Subgroup.normalizer (W.subgroup : Set G0),
    thetaEmbedding (QuotientGroup.mk x) = T.quotientMap (T.normalizerLift x)
  centralizerEmbedding : T.centralizer →*
    Subgroup.normalizer (T.defect : Set T.Quotient)
  centralizerEmbedding_val : ∀ x : T.centralizer,
    (centralizerEmbedding x : T.Quotient) = x
  localEmbedding : NormalizerQuotient T.defect →* NormalizerQuotient V.subgroup
  localEmbedding_injective : Function.Injective localEmbedding
  localEmbedding_mk : ∀ x : intermediate G0 W V,
    ∀ hx : (x : A) ∈ Subgroup.normalizer (V.subgroup : Set A),
    ∀ hq : T.quotientMap x ∈ Subgroup.normalizer (T.defect : Set T.Quotient),
      localEmbedding (QuotientGroup.mk ⟨T.quotientMap x, hq⟩) =
        QuotientGroup.mk ⟨(x : A), hx⟩

/-- Put a literal primitive block idempotent into the actual group algebra
centre for the coefficient-restriction definition of defect. -/
def primitiveBlockInCenter {H : Type} [Group H]
    (b : LiteralPrimitiveBlock k H) : GroupAlgebraCenter k H :=
  ⟨b.1, by
    rw [Subalgebra.mem_center_iff]
    intro x
    exact (b.2.central.comm x).eq.symm⟩

/-- The block/defect hypotheses for DGN. The block is the unique block
containing ordinary characters above the given defect-zero theta, and D is
maximal in its literal nonzero central Brauer support. The ordinary block
selector remains an explicit modular-system source identification (U).
No defect-group or covering predicate is supplied by the caller. -/
structure DefectBlockData
    {W : BaseWeight (ell := ell) (K := K) G0}
    {V : AmbientWeight (ell := ell) (K := K) (A := A)}
    {T : IntermediateData G0 W V} (L : LocalGeometry G0 T) where
  ordinaryBlock : Irr K T.Quotient → LiteralPrimitiveBlock k T.Quotient
  block : LiteralPrimitiveBlock k T.Quotient
  above_theta : ∃ chi : Irr K T.Quotient,
    ordinaryBlock chi = block ∧
      OrdinaryOccursInRestriction L.thetaEmbedding chi W.localCharacter
  unique_above_theta : ∀ chi : Irr K T.Quotient,
    OrdinaryOccursInRestriction L.thetaEmbedding chi W.localCharacter →
      ordinaryBlock chi = block
  defect : IsMaximalNonzeroPSubgroup ell
    (fun P : Subgroup T.Quotient ↦
      centralBrauerRestriction P (primitiveBlockInCenter block) ≠ 0) T.defect

/-- The DGN correspondent and its descent from the centralizer direct
factor. The inflation equation uses the literal quotient by D. -/
structure DGNData
    {W : BaseWeight (ell := ell) (K := K) G0}
    {V : AmbientWeight (ell := ell) (K := K) (A := A)}
    {T : IntermediateData G0 W V} (L : LocalGeometry G0 T) where
  pi : Irr K T.centralizer
  pi_defectZero : IsDefectZeroOrdinaryCharacter ell pi
  barPi : Irr K (NormalizerQuotient T.defect)
  barPi_inflation : ∀ x : T.centralizer,
    barPi (QuotientGroup.mk (L.centralizerEmbedding x)) = pi x

/-- One fixed published DGN source, on the exact local hypotheses and
carriers above. This contains source data, not a claim that every record
of this type has been authenticated as the published correspondence. -/
structure DGNSource where
  prime : Nat.Prime ell
  modular_characteristic : CharP k ell
  ordinary_splitting : IsAlgClosed K
  modular_splitting : IsAlgClosed k
  data : ∀ {W : BaseWeight (ell := ell) (K := K) G0}
    {V : AmbientWeight (ell := ell) (K := K) (A := A)}
    {T : IntermediateData G0 W V} (L : LocalGeometry G0 T),
    DefectBlockData (k := k) G0 L → DGNData G0 L

/-- The raw published covering relation: DGN descent followed by actual
ordinary constituent occurrence under the specified local embedding. -/
def CoversRaw (dgn : DGNSource (ell := ell) (K := K) (k := k) G0)
    (V : AmbientWeight (ell := ell) (K := K) (A := A))
    (W : BaseWeight (ell := ell) (K := K) G0) : Prop :=
  ∃ (T : IntermediateData G0 W V) (L : LocalGeometry G0 T)
    (B : DefectBlockData (k := k) G0 L),
      OrdinaryOccursInRestriction L.localEmbedding V.localCharacter
        (dgn.data L B).barPi

/-- The canonical conjugacy class of an actual raw character weight. -/
def rawClass {H : Type} [Group H] [Finite H]
    (W : CharacterWeight ell K H) :
    CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := H) :=
  Quotient.mk _ (Quotient.mk _ W)

/-- Covering on actual conjugacy classes is existence of representatives
satisfying the displayed raw local-character relation. -/
def CoversClass (dgn : DGNSource (ell := ell) (K := K) (k := k) G0)
    (up : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := A))
    (down : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := G0)) : Prop :=
  ∃ (V : AmbientWeight (ell := ell) (K := K) (A := A))
    (W : BaseWeight (ell := ell) (K := K) G0),
    rawClass V = up ∧ rawClass W = down ∧ CoversRaw G0 dgn V W

/-- The raw conjugation covariance stated immediately before `covWeight`,
and exactly the existence use of that lemma, conditional on the fixed
source DGN interpretation. Covariance makes the representative convention
agree with the source's fixed-representative wording. No orbit bijection or
criterion conclusion is included. -/
structure BroughCoveringNonemptySource
    (dgn : DGNSource (ell := ell) (K := K) (k := k) G0) : Prop where
  raw_conjugation :
    ∀ (V : AmbientWeight (ell := ell) (K := K) (A := A))
      (W : BaseWeight (ell := ell) (K := K) G0) (g : A),
      CoversRaw G0 dgn V W ↔ CoversRaw G0 dgn
        (V.rightTwist (MulAut.conj g⁻¹))
        (W.rightTwist (MulAut.conjNormal (H := G0) g⁻¹))
  covered_nonempty : ∀ up :
    CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := A),
    ∃ down, CoversClass G0 dgn up down

/-- A selected downstairs class is accompanied by its exact cover witness. -/
def selectedCoveredClass
    (dgn : DGNSource (ell := ell) (K := K) (k := k) G0)
    (source : BroughCoveringNonemptySource G0 dgn)
    (up : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := A)) :
    CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := G0) :=
  Classical.choose (source.covered_nonempty up)

theorem selectedCoveredClass_covers
    (dgn : DGNSource (ell := ell) (K := K) (k := k) G0)
    (source : BroughCoveringNonemptySource G0 dgn)
    (up : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := A)) :
    CoversClass G0 dgn up (selectedCoveredClass G0 dgn source up) :=
  Classical.choose_spec (source.covered_nonempty up)

section SpinInstantiation

open TypeBCliffordCarriers TypeBSpinStabilizer TypeBInertiaHallSource

variable {n : ℕ} {F : Type} [Field F]
variable (N : NormSource n F) [Finite (SpecialClifford n F)]

/-- The actual covered Spin class joins the published inertia-times-Hall
formula. The equality is proved for its concrete inertia by the previously
checked index argument; the nonempty-cover source supplies only the class
and its literal local-character covering witness. -/
theorem exists_covered_spin_class_with_JG_univ
    (hOdd : Odd ell)
    (diagonal : SpecialClifford n F →* DiagonalGroup)
    (surjective : Function.Surjective diagonal)
    (kernel : diagonal.ker =
      SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F))
    (hall : HallPrimeToQuotientSource N ell)
    (dgn : DGNSource (ell := ell) (K := K) (k := k) (SpinSubgroup n F N))
    (source : BroughCoveringNonemptySource (SpinSubgroup n F N) dgn)
    (up : CharacterWeight.ConjugacyClass
      (p := ell) (K := K) (G := SpecialClifford n F)) :
    ∃ down : CharacterWeight.ConjugacyClass
        (p := ell) (K := K) (G := Spin n F N),
      CoversClass (SpinSubgroup n F N) dgn up down ∧
        (weightInertia N down : Set (SpecialClifford n F)) *
          (hall.preimage : Set (SpecialClifford n F)) = Set.univ := by
  obtain ⟨down, hdown⟩ := source.covered_nonempty up
  refine ⟨down, hdown, ?_⟩
  exact weightInertia_mul_hallPreimage_eq_univ N hOdd diagonal surjective kernel hall down

end SpinInstantiation

end ModularRep.PaperProofs.TypeBWeightCoveringSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
