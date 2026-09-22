import ModularRep.PaperProofs.CyclicOuterRawPairNormalizer
import ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

/-!
# Actual character and raw-pair stabilizer triples

For the fixed semidirect action on a finite group H, construct the actual
Brauer stabilizer and the raw-pair stabilizer inside it. The normal base
subgroup is the kernel of the actual right projection. Its intersection
with the local subgroup is identified with the normalizer of the SAME
raw weight's subgroup. Both character arguments are transported through
these computed group equivalences, using transported root embeddings.

These constructions contain no block-triple relation premise or conclusion.
The local group is initially its intersection with the Brauer stabilizer.
Identifying it with the full raw-pair stabilizer requires the separate
matched-class equivariance join; it is not silently assumed here.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoActualStabilizerTriple

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

universe u

variable {p : ℕ} {k K H E : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E]
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (action : E →* MulAut H)

@[instance_reducible]
def actualBrauerAction : MulAction (H ⋊[action] E) (IBr iota) := by
  letI : MulAction H (IBr iota) :=
    rightAutomorphismAction (MulAut.conj : H →* MulAut H)
  letI : MulAction E (IBr iota) := rightAutomorphismAction action
  exact semidirectMulAction action
    (rightAutomorphismSemidirectCompatible (X := IBr iota) action)

def globalStabilizer (psi : IBr iota) : Subgroup (H ⋊[action] E) :=
  letI := actualBrauerAction iota action
  MulAction.stabilizer (H ⋊[action] E) psi

def rawStabilizer (W : CharacterWeight p K H) : Subgroup (H ⋊[action] E) :=
  letI := canonicalRawSemidirectAction (p := p) (K := K) action
  MulAction.stabilizer (H ⋊[action] E)
    (Quotient.mk'' W : RawWeightClass (p := p) (K := K) (H := H))

variable (psi : IBr iota)

theorem inl_mem_globalStabilizer (h : H) :
    (SemidirectProduct.inl h : H ⋊[action] E) ∈
      globalStabilizer iota action psi := by
  letI : MulAction H (IBr iota) :=
    rightAutomorphismAction (MulAut.conj : H →* MulAut H)
  letI : MulAction E (IBr iota) := rightAutomorphismAction action
  letI := actualBrauerAction iota action
  change (SemidirectProduct.inl h : H ⋊[action] E) • psi = psi
  rw [semidirect_inl_smul]
  exact inner_fixes_ibr iota h psi

/-- The actual copy of H in its Brauer stabilizer. -/
def baseInclusion : H →* globalStabilizer iota action psi where
  toFun h := ⟨SemidirectProduct.inl h, inl_mem_globalStabilizer iota action psi h⟩
  map_one' := Subtype.ext (map_one SemidirectProduct.inl)
  map_mul' h j := Subtype.ext (map_mul SemidirectProduct.inl h j)

/-- The normal base is the kernel of the actual right projection. -/
def baseSubgroup : Subgroup (globalStabilizer iota action psi) :=
  (SemidirectProduct.rightHom.comp
    (globalStabilizer iota action psi).subtype).ker

instance baseSubgroup_normal : (baseSubgroup iota action psi).Normal :=
  inferInstanceAs (MonoidHom.ker _).Normal

@[simp] theorem mem_baseSubgroup (g : globalStabilizer iota action psi) :
    g ∈ baseSubgroup iota action psi ↔ g.1.right = 1 := Iff.rfl

def baseToKernel : H →* baseSubgroup iota action psi where
  toFun h := ⟨baseInclusion iota action psi h, rfl⟩
  map_one' := Subtype.ext (map_one (baseInclusion iota action psi))
  map_mul' h j := Subtype.ext (map_mul (baseInclusion iota action psi) h j)

theorem baseToKernel_bijective : Function.Bijective (baseToKernel iota action psi) := by
  constructor
  · intro h j heq
    exact SemidirectProduct.inl_injective
      (congrArg (fun x : baseSubgroup iota action psi => x.1.1) heq)
  · intro g
    refine ⟨g.1.1.left, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact g.2.symm

/-- The equivalence is determined by the fixed inl embedding. -/
def baseEquiv : H ≃* baseSubgroup iota action psi :=
  MulEquiv.ofBijective (baseToKernel iota action psi)
    (baseToKernel_bijective iota action psi)

@[simp] theorem baseEquiv_ambient (h : H) :
    (baseEquiv iota action psi h).1.1 =
      (SemidirectProduct.inl h : H ⋊[action] E) := rfl

variable (W : CharacterWeight p K H)

/-- The literal local subgroup inside the actual Brauer stabilizer. -/
def localSubgroup : Subgroup (globalStabilizer iota action psi) :=
  (rawStabilizer action W).comap (globalStabilizer iota action psi).subtype

theorem inl_mem_rawStabilizer_iff (h : H) :
    (SemidirectProduct.inl h : H ⋊[action] E) ∈ rawStabilizer action W ↔
      h ∈ Subgroup.normalizer (W.subgroup : Set H) := by
  let r : RawWeightClass (p := p) (K := K) (H := H) := Quotient.mk'' W
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction action
  letI := canonicalRawSemidirectAction (p := p) (K := K) action
  change (SemidirectProduct.inl h : H ⋊[action] E) • r = r ↔ _
  rw [semidirect_inl_smul]
  constructor
  · intro hr
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (rawSubgroup r).map (MulAut.conj h).toMonoidHom = rawSubgroup r
    rw [← rawSubgroup_conjugate, hr]
  · intro hh
    exact normalizer_fixes_rawWeight canonicalRawNormalizerQuotientInput h r hh

/-- The same actual normalizer maps into the actual intersection. -/
def normalizerToIntersection :
    Subgroup.normalizer (W.subgroup : Set H) →*
      ↥(baseSubgroup iota action psi ⊓ localSubgroup iota action psi W) where
  toFun h := ⟨baseInclusion iota action psi h.1,
    ⟨rfl, (inl_mem_rawStabilizer_iff action W h.1).mpr h.2⟩⟩
  map_one' := Subtype.ext (map_one (baseInclusion iota action psi))
  map_mul' h j := Subtype.ext (map_mul (baseInclusion iota action psi) h.1 j.1)

theorem normalizerToIntersection_bijective :
    Function.Bijective (normalizerToIntersection iota action psi W) := by
  constructor
  · intro h j heq
    apply Subtype.ext
    exact SemidirectProduct.inl_injective
      (congrArg (fun x : ↥(baseSubgroup iota action psi ⊓
        localSubgroup iota action psi W) => x.1.1) heq)
  · intro g
    have hg : (SemidirectProduct.inl g.1.1.left : H ⋊[action] E) = g.1.1 := by
      apply SemidirectProduct.ext
      · rfl
      · exact g.2.1.symm
    have hnormal : g.1.1.left ∈ Subgroup.normalizer (W.subgroup : Set H) := by
      apply (inl_mem_rawStabilizer_iff action W g.1.1.left).mp
      rw [hg]
      exact g.2.2
    refine ⟨⟨g.1.1.left, hnormal⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hg

/-- K identification of N intersect H_local with the Corresponding weight normalizer. -/
def normalizerEquivIntersection :
    Subgroup.normalizer (W.subgroup : Set H) ≃*
      ↥(baseSubgroup iota action psi ⊓ localSubgroup iota action psi W) :=
  MulEquiv.ofBijective (normalizerToIntersection iota action psi W)
    (normalizerToIntersection_bijective iota action psi W)

@[simp] theorem normalizerEquivIntersection_ambient
    (h : Subgroup.normalizer (W.subgroup : Set H)) :
    (normalizerEquivIntersection iota action psi W h).1.1 =
      (SemidirectProduct.inl h.1 : H ⋊[action] E) := rfl

/-- When matching equivariance has proved actual raw-stabilizer containment,
the local subgroup includes the FULL raw stabilizer, with the literal
ambient coercion. The containment is not supplied as a relation premise. -/
def fullRawStabilizerEquiv
    (contained : rawStabilizer action W ≤ globalStabilizer iota action psi) :
    rawStabilizer action W ≃* localSubgroup iota action psi W where
  toFun g := ⟨⟨g.1, contained g.2⟩, g.2⟩
  invFun g := ⟨g.1.1, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Source reduction data are attached to this actual own ordinary character
on its actual normalizer. No unrelated local character can be substituted.
Root compatibility with other coefficient conventions is supplied at the
inflation/butterfly consumer, not inferred from equal function values. -/
structure OwnNormalizerReduction where
  root : PrimeRegularRootEmbedding p k K
    (Subgroup.normalizer (W.subgroup : Set H))
  brauer : IBr root
  own_reduction : NormalizerInflatedReduction W.subgroup W.localCharacter root brauer

/-- Both roots and characters of the triple are computed along the displayed
base and normalizer equivalences. This is the ACTUAL tuple on which a
relation source must be authenticated. It asserts no relation. -/
def arguments (R : OwnNormalizerReduction (k := k) W) :
    BlockTripleArguments p k K where
  G := globalStabilizer iota action psi
  N := baseSubgroup iota action psi
  H := localSubgroup iota action psi W
  iotaN := iota.alongMulEquiv (baseEquiv iota action psi)
  iotaM := R.root.alongMulEquiv (normalizerEquivIntersection iota action psi W)
  theta := IrreducibleBrauerCharacter.alongMulEquiv iota
    (baseEquiv iota action psi) psi
  phi := IrreducibleBrauerCharacter.alongMulEquiv R.root
    (normalizerEquivIntersection iota action psi W) R.brauer

theorem arguments_theta_values (R : OwnNormalizerReduction (k := k) W)
    (x : PrimeRegularElement (G := baseSubgroup iota action psi) p) :
    (arguments iota action psi W R).theta.1 x =
      psi.1 (PrimeRegularElement.map
        (baseEquiv iota action psi).symm.toMonoidHom x) := rfl

/-- The local triple character is the reduction of this SAME own ordinary
character, evaluated on the actual inverse normalizer identification. -/
theorem arguments_phi_own_values (R : OwnNormalizerReduction (k := k) W)
    (x : PrimeRegularElement (G := ↥(baseSubgroup iota action psi ⊓
      localSubgroup iota action psi W)) p) :
    (arguments iota action psi W R).phi.1 x =
      W.localCharacter (QuotientGroup.mk
        ((normalizerEquivIntersection iota action psi W).symm x.1)) := by
  exact (R.own_reduction (PrimeRegularElement.map
    (normalizerEquivIntersection iota action psi W).symm.toMonoidHom x)).symm

end ModularRep.PaperProofs.OddTwoActualStabilizerTriple


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
