import ModularRep.PaperProofs.OddTwoActualStabilizerTriple
import ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation

/-!
# The literal PSp triple inside the Brough conformal/field ambient group

The ambient group is the already constructed PCSp semidirect Aut(F), acting
on PSp through its fixed natural full-automorphism map. The normal base of
the triple is the actual image of PSp, not the whole PCSp left factor.
The local subgroup is the intersection of the Brauer stabilizer with the
stabilizer of the SAME raw weight's isomorphism class.

K identifies the intersection of this base with the local subgroup with
the corresponding weight normalizer in PSp. The roots and both characters in the
resulting BlockTripleArguments are transported along these computed group
equivalences. The local character is the supplied reduction of the own
ordinary normalizer-quotient character, using the existing precise record.

This is group and character-argument packaging only. BroughGroupSource is
the existing group-only E1 source on fixed matrix and quotient carriers;
no source premise or conclusion about covering objects, extensions, a
block-triple relation or the Brough orbit witness is added here. Equality
with the full raw stabilizer still requires an actual containment proof.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoBroughActualTriple

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple (OwnNormalizerReduction)

universe u

variable {n : ℕ} {F k K : Type u}
variable [Field F] [Finite F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]

local instance fieldAutFinite : Finite (F ≃+* F) :=
  Finite.of_injective (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective

local instance groupAutFinite (G : Type u) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun a : MulAut G => (a : G → G)) DFunLike.coe_injective

local instance ambientFinite : Finite (Ambient (n := n) (F := F)) :=
  Finite.of_equiv (PCSp n F × (F ≃+* F)) SemidirectProduct.equivProd.symm

local instance groupFintype (G : Type u) [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite G

variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)

/-- The prescribed full automorphism map sends the fixed base inclusion
to the actual inner automorphism. -/
@[simp] theorem fullAut_base (x : PSp n F) :
    S.fullAut (baseEmbedding C x) = MulAut.conj x :=
  S.pcspToAut_base x

/-- Conjugation in the actual ambient group agrees with its prescribed
action on the embedded base, including the field component. -/
theorem baseEmbedding_conjugate (a : Ambient (n := n) (F := F)) (x : PSp n F) :
    baseEmbedding C (S.fullAut a x) = a * baseEmbedding C x * a⁻¹ := by
  apply S.fullAut.injective
  rw [map_mul, map_mul, map_inv, fullAut_base, fullAut_base]
  ext y
  change S.fullAut a x * y * (S.fullAut a x)⁻¹ =
    S.fullAut a (x * (S.fullAut a)⁻¹ y * x⁻¹)
  simp only [map_mul, map_inv, MulAut.apply_inv_self]

/-- Normality belongs to the actual PSp image in PCSp semidirect Aut(F). -/
def baseRangeNormal : ((baseEmbedding C).range).Normal where
  conj_mem x hx a := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨S.fullAut a y, baseEmbedding_conjugate S a y⟩

variable (iota : PrimeRegularRootEmbedding 2 k K (PSp n F))

/-- The inverse/opposite convention is the same one used by the canonical
Brauer action in the existing FLZ and semidirect modules. -/
@[instance_reducible]
def actualBrauerAction : MulAction (Ambient (n := n) (F := F)) (IBr iota) :=
  rightAutomorphismAction S.fullAut.toMonoidHom

/-- This acts on raw-pair isomorphism classes, before ambient conjugacy. -/
@[instance_reducible]
def actualRawAction : MulAction (Ambient (n := n) (F := F))
    (RawWeightClass (p := 2) (K := K) (H := PSp n F)) :=
  rightAutomorphismAction S.fullAut.toMonoidHom

def globalStabilizer (psi : IBr iota) : Subgroup (Ambient (n := n) (F := F)) :=
  letI := actualBrauerAction S iota
  MulAction.stabilizer (Ambient (n := n) (F := F)) psi

def rawStabilizer (W : CharacterWeight 2 K (PSp n F)) :
    Subgroup (Ambient (n := n) (F := F)) :=
  letI := actualRawAction (K := K) S
  MulAction.stabilizer (Ambient (n := n) (F := F))
    (Quotient.mk'' W : RawWeightClass (p := 2) (K := K) (H := PSp n F))

variable (psi : IBr iota)

theorem base_mem_globalStabilizer (x : PSp n F) :
    baseEmbedding C x ∈ globalStabilizer S iota psi := by
  change MulOpposite.op (S.fullAut ((baseEmbedding C x)⁻¹)) • psi = psi
  rw [← (baseEmbedding C).map_inv, fullAut_base]
  exact inner_fixes_ibr iota x psi

/-- The literal PSp embedding, now with its proved stabilizer membership. -/
def baseInclusion : PSp n F →* globalStabilizer S iota psi where
  toFun x := ⟨baseEmbedding C x, base_mem_globalStabilizer S iota psi x⟩
  map_one' := Subtype.ext (map_one (baseEmbedding C))
  map_mul' x y := Subtype.ext (map_mul (baseEmbedding C) x y)

/-- The normal base is the preimage of the ACTUAL PSp image, not the
kernel of the field projection (whose kernel would be PCSp). -/
def baseSubgroup : Subgroup (globalStabilizer S iota psi) :=
  ((baseEmbedding C).range).comap (globalStabilizer S iota psi).subtype

instance baseSubgroup_normal : (baseSubgroup S iota psi).Normal := by
  letI := baseRangeNormal S
  change (((baseEmbedding C).range).comap
    (globalStabilizer S iota psi).subtype).Normal
  infer_instance

def baseToImage : PSp n F →* baseSubgroup S iota psi where
  toFun x := ⟨baseInclusion S iota psi x, ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one (baseInclusion S iota psi))
  map_mul' x y := Subtype.ext (map_mul (baseInclusion S iota psi) x y)

theorem baseToImage_bijective : Function.Bijective (baseToImage S iota psi) := by
  constructor
  · intro x y hxy
    exact baseEmbedding_injective C
      (congrArg (fun z : baseSubgroup S iota psi => z.1.1) hxy)
  · intro g
    obtain ⟨x, hx⟩ := g.2
    exact ⟨x, Subtype.ext (Subtype.ext hx)⟩

def baseEquiv : PSp n F ≃* baseSubgroup S iota psi :=
  MulEquiv.ofBijective (baseToImage S iota psi) (baseToImage_bijective S iota psi)

@[simp] theorem baseEquiv_ambient (x : PSp n F) :
    (baseEquiv S iota psi x).1.1 = baseEmbedding C x := rfl

variable (W : CharacterWeight 2 K (PSp n F))

def localSubgroup : Subgroup (globalStabilizer S iota psi) :=
  (rawStabilizer S W).comap (globalStabilizer S iota psi).subtype

/-- The existing own-raw-pair normalizer criterion applies because the
fixed embedded PSp element acts by the SAME inner automorphism. -/
theorem base_mem_rawStabilizer_iff (x : PSp n F) :
    baseEmbedding C x ∈ rawStabilizer S W ↔
      x ∈ Subgroup.normalizer (W.subgroup : Set (PSp n F)) := by
  let r : RawWeightClass (p := 2) (K := K) (H := PSp n F) := Quotient.mk'' W
  letI : MulAction (PSp n F) (RawWeightClass (p := 2) (K := K) (H := PSp n F)) :=
    canonicalRawHAction
  letI : MulAction (MulAut (PSp n F))
      (RawWeightClass (p := 2) (K := K) (H := PSp n F)) :=
    canonicalRawEAction (MonoidHom.id (MulAut (PSp n F)))
  letI := canonicalRawSemidirectAction (p := 2) (K := K)
    (MonoidHom.id (MulAut (PSp n F)))
  have h := OddTwoActualStabilizerTriple.inl_mem_rawStabilizer_iff
    (MonoidHom.id (MulAut (PSp n F))) W x
  change (SemidirectProduct.inl x :
    PSp n F ⋊[MonoidHom.id (MulAut (PSp n F))] MulAut (PSp n F)) • r = r ↔ _ at h
  rw [semidirect_inl_smul] at h
  change MulOpposite.op (S.fullAut ((baseEmbedding C x)⁻¹)) • r = r ↔ _
  rw [← (baseEmbedding C).map_inv, fullAut_base]
  exact h

/-- The actual normalizer maps to the computed base/local intersection. -/
def normalizerToIntersection :
    Subgroup.normalizer (W.subgroup : Set (PSp n F)) →*
      ↥(baseSubgroup S iota psi ⊓ localSubgroup S iota psi W) where
  toFun x := ⟨baseInclusion S iota psi x.1,
    ⟨⟨x.1, rfl⟩, (base_mem_rawStabilizer_iff S W x.1).mpr x.2⟩⟩
  map_one' := Subtype.ext (map_one (baseInclusion S iota psi))
  map_mul' x y := Subtype.ext (map_mul (baseInclusion S iota psi) x.1 y.1)

theorem normalizerToIntersection_bijective :
    Function.Bijective (normalizerToIntersection S iota psi W) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact baseEmbedding_injective C
      (congrArg (fun z : ↥(baseSubgroup S iota psi ⊓
        localSubgroup S iota psi W) => z.1.1) hxy)
  · intro g
    obtain ⟨x, hx⟩ := g.2.1
    have hnormal : x ∈ Subgroup.normalizer (W.subgroup : Set (PSp n F)) := by
      apply (base_mem_rawStabilizer_iff S W x).mp
      rw [hx]
      exact g.2.2
    exact ⟨⟨x, hnormal⟩, Subtype.ext (Subtype.ext hx)⟩

def normalizerEquivIntersection :
    Subgroup.normalizer (W.subgroup : Set (PSp n F)) ≃*
      ↥(baseSubgroup S iota psi ⊓ localSubgroup S iota psi W) :=
  MulEquiv.ofBijective (normalizerToIntersection S iota psi W)
    (normalizerToIntersection_bijective S iota psi W)

@[simp] theorem normalizerEquivIntersection_ambient
    (x : Subgroup.normalizer (W.subgroup : Set (PSp n F))) :
    (normalizerEquivIntersection S iota psi W x).1.1 = baseEmbedding C x.1 := rfl

/-- This identification consumes actual containment. No full raw-pair
stabilizer is silently substituted for its intersection with the global one. -/
def fullRawStabilizerEquiv
    (contained : rawStabilizer S W ≤ globalStabilizer S iota psi) :
    rawStabilizer S W ≃* localSubgroup S iota psi W where
  toFun g := ⟨⟨g.1, contained g.2⟩, g.2⟩
  invFun g := ⟨g.1.1, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem fullRawStabilizerEquiv_ambient
    (contained : rawStabilizer S W ≤ globalStabilizer S iota psi)
    (g : rawStabilizer S W) :
    (fullRawStabilizerEquiv S iota psi W contained g).1.1 = g.1 := rfl

/-- The fixed actual tuple for the later BS source application. Both
characters and roots are computed; no block-triple relation is asserted. -/
def arguments (R : OwnNormalizerReduction (k := k) W) :
    BlockTripleArguments 2 k K where
  G := globalStabilizer S iota psi
  N := baseSubgroup S iota psi
  H := localSubgroup S iota psi W
  iotaN := iota.alongMulEquiv (baseEquiv S iota psi)
  iotaM := R.root.alongMulEquiv (normalizerEquivIntersection S iota psi W)
  theta := IrreducibleBrauerCharacter.alongMulEquiv iota
    (baseEquiv S iota psi) psi
  phi := IrreducibleBrauerCharacter.alongMulEquiv R.root
    (normalizerEquivIntersection S iota psi W) R.brauer

theorem arguments_theta_values (R : OwnNormalizerReduction (k := k) W)
    (x : PrimeRegularElement (G := baseSubgroup S iota psi) 2) :
    (arguments S iota psi W R).theta.1 x =
      psi.1 (PrimeRegularElement.map
        (baseEquiv S iota psi).symm.toMonoidHom x) := rfl

/-- The local argument is exactly the reduction of the supplied raw
weight's own ordinary character on the computed inverse normalizer map. -/
theorem arguments_phi_own_values (R : OwnNormalizerReduction (k := k) W)
    (x : PrimeRegularElement (G := ↥(baseSubgroup S iota psi ⊓
      localSubgroup S iota psi W)) 2) :
    (arguments S iota psi W R).phi.1 x =
      W.localCharacter (QuotientGroup.mk
        ((normalizerEquivIntersection S iota psi W).symm x.1)) := by
  exact (R.own_reduction (PrimeRegularElement.map
    (normalizerEquivIntersection S iota psi W).symm.toMonoidHom x)).symm

end ModularRep.PaperProofs.OddTwoBroughActualTriple


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
