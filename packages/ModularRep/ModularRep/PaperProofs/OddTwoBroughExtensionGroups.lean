import ModularRep.PaperProofs.OddTwoBroughActualTriple
import ModularRep.OrdinaryCharacterCyclicExtensionBridge

/-!
# The actual field and conformal extension groups

The two constructed lanes are PSp semidirect Aut(F), embedded in the fixed
Brough ambient group by the actual projective inclusion, and PCSp, embedded
by inl. In either lane the outer projection has precisely the embedded PSp
as kernel. Its restrictions to the actual Brauer stabilizer and the SAME
raw-pair inertia subgroup have kernels identified with PSp and the own
normalizer, respectively.

The copy of the own Q is normal in the raw inertia group: its proof uses
actual raw-pair fixation and actual ambient conjugation. Quotienting by Q
retains the computed outer projection and its cyclic image. This is group
geometry only. The later character consumer must transport the OWN local
character across the normalizer-quotient identification and prove its
conjugation fixedness. No character-invariance, extension, or relation
conclusion is a source field here.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoBroughExtensionGroups

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {n : ℕ} {F k K : Type u}
variable [Field F] [Finite F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)

local instance groupFintype (G : Type u) [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite G

/-- Group geometry computed below for the two specified actual lanes.
This is not an additional external theorem or character source. -/
structure Geometry (G T : Type u) [Group G] [Group T] where
  embedding : G →* Ambient (n := n) (F := F)
  embedding_injective : Function.Injective embedding
  base : PSp n F →* G
  base_square : ∀ x, embedding (base x) = baseEmbedding C x
  outer : G →* T
  outer_ker : outer.ker = base.range

abbrev FieldGroup := PSp n F ⋊[pspFieldAction] (F ≃+* F)

/-- The field lane uses the literal projective inclusion and the identity
on the actual field automorphism group. -/
def fieldEmbedding : FieldGroup (n := n) (F := F) →*
    Ambient (n := n) (F := F) :=
  SemidirectProduct.map (pspEmbedding C) (MonoidHom.id _) (by
    intro sigma
    apply MonoidHom.ext
    intro x
    exact (field_pspEmbedding C sigma x).symm)

def fieldGeometry : Geometry (C := C) (FieldGroup (n := n) (F := F)) (F ≃+* F) where
  embedding := fieldEmbedding (C := C)
  embedding_injective := by
    intro a b hab
    apply SemidirectProduct.ext
    · exact pspEmbedding_injective C (congrArg SemidirectProduct.left hab)
    · exact congrArg (fun z : Ambient (n := n) (F := F) => z.right) hab
  base := SemidirectProduct.inl
  base_square x := by
    change (fieldEmbedding (C := C) (SemidirectProduct.inl x)) = _
    exact SemidirectProduct.map_inl _ _ _ x
  outer := SemidirectProduct.rightHom
  outer_ker := by
    ext g
    change g.right = 1 ↔ ∃ x, SemidirectProduct.inl x = g
    constructor
    · intro hg
      exact ⟨g.left, SemidirectProduct.ext rfl hg.symm⟩
    · rintro ⟨x, rfl⟩
      rfl

/-- The conformal lane's outer group is the actual PCSp/PSp quotient. -/
def conformalGeometry :
    letI := S.normal_image
    Geometry (C := C) (PCSp n F) (PCSp n F ⧸ (pspEmbedding C).range) := by
  letI := S.normal_image
  exact
    { embedding := SemidirectProduct.inl
      embedding_injective := SemidirectProduct.inl_injective
      base := pspEmbedding C
      base_square := fun _ => rfl
      outer := QuotientGroup.mk' (pspEmbedding C).range
      outer_ker := QuotientGroup.ker_mk' _ }

include S in
theorem fieldOuter_cyclic : IsCyclic (F ≃+* F) := S.field_cyclic

theorem conformalOuter_cyclic :
    letI := S.normal_image
    IsCyclic (PCSp n F ⧸ (pspEmbedding C).range) := by
  letI := S.normal_image
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isCyclic_of_prime_card S.quotient_card

namespace Geometry

variable {G T : Type u} [Group G] [Group T]
variable (L : Geometry (C := C) G T)

theorem base_injective : Function.Injective L.base := by
  intro x y hxy
  apply baseEmbedding_injective C
  rw [← L.base_square, ← L.base_square, hxy]

@[simp] theorem outer_base (x : PSp n F) : L.outer (L.base x) = 1 := by
  change L.base x ∈ L.outer.ker
  rw [L.outer_ker]
  exact ⟨x, rfl⟩

theorem base_conjugate (g : G) (x : PSp n F) :
    L.base (S.fullAut (L.embedding g) x) = g * L.base x * g⁻¹ := by
  apply L.embedding_injective
  rw [L.base_square, map_mul, map_mul, map_inv, L.base_square]
  exact OddTwoBroughActualTriple.baseEmbedding_conjugate S (L.embedding g) x

variable (iota : PrimeRegularRootEmbedding 2 k K (PSp n F))

/-- The full Brauer stabilizer in this actual lane, without a selected
principal character or extension assumption. -/
def global (psi : IBr iota) : Subgroup G :=
  (OddTwoBroughActualTriple.globalStabilizer S iota psi).comap L.embedding

def globalOuter (psi : IBr iota) : L.global S iota psi →* T :=
  L.outer.comp (L.global S iota psi).subtype

def globalBase (psi : IBr iota) : Subgroup (L.global S iota psi) :=
  (L.globalOuter S iota psi).ker

instance globalBase_normal (psi : IBr iota) : (L.globalBase S iota psi).Normal :=
  inferInstanceAs (L.globalOuter S iota psi).ker.Normal

def baseToGlobal (psi : IBr iota) : PSp n F →* L.global S iota psi where
  toFun x := ⟨L.base x, by
    change L.embedding (L.base x) ∈ OddTwoBroughActualTriple.globalStabilizer S iota psi
    rw [L.base_square]
    exact OddTwoBroughActualTriple.base_mem_globalStabilizer S iota psi x⟩
  map_one' := Subtype.ext L.base.map_one
  map_mul' x y := Subtype.ext (L.base.map_mul x y)

def baseToGlobalKernel (psi : IBr iota) : PSp n F →* L.globalBase S iota psi where
  toFun x := ⟨L.baseToGlobal S iota psi x, L.outer_base x⟩
  map_one' := Subtype.ext (map_one (L.baseToGlobal S iota psi))
  map_mul' x y := Subtype.ext (map_mul (L.baseToGlobal S iota psi) x y)

theorem baseToGlobalKernel_bijective (psi : IBr iota) :
    Function.Bijective (L.baseToGlobalKernel S iota psi) := by
  constructor
  · intro x y hxy
    exact L.base_injective (congrArg (fun z : L.globalBase S iota psi => z.1.1) hxy)
  · intro g
    have hg : g.1.1 ∈ L.base.range := by
      rw [← L.outer_ker]
      exact g.2
    obtain ⟨x, hx⟩ := hg
    exact ⟨x, Subtype.ext (Subtype.ext hx)⟩

def globalBaseEquiv (psi : IBr iota) : PSp n F ≃* L.globalBase S iota psi :=
  MulEquiv.ofBijective (L.baseToGlobalKernel S iota psi)
    (L.baseToGlobalKernel_bijective S iota psi)

@[simp] theorem globalBaseEquiv_value (psi : IBr iota) (x : PSp n F) :
    (L.globalBaseEquiv S iota psi x).1.1 = L.base x := rfl

variable (W : CharacterWeight 2 K (PSp n F))

/-- This is the inertia subgroup of the whole OWN raw pair, before
ambient conjugacy classes. In the conformal lane it is N_PCSp(Q)_theta. -/
def raw : Subgroup G :=
  (OddTwoBroughActualTriple.rawStabilizer S W).comap L.embedding

def rawOuter : L.raw S W →* T := L.outer.comp (L.raw S W).subtype

def rawBase : Subgroup (L.raw S W) := (L.rawOuter S W).ker

instance rawBase_normal : (L.rawBase S W).Normal :=
  inferInstanceAs (L.rawOuter S W).ker.Normal

theorem base_mem_raw_iff (x : PSp n F) :
    L.base x ∈ L.raw S W ↔ x ∈ Subgroup.normalizer (W.subgroup : Set (PSp n F)) := by
  change L.embedding (L.base x) ∈ OddTwoBroughActualTriple.rawStabilizer S W ↔ _
  rw [L.base_square]
  exact OddTwoBroughActualTriple.base_mem_rawStabilizer_iff S W x

def normalizerToRaw : Subgroup.normalizer (W.subgroup : Set (PSp n F)) →* L.raw S W where
  toFun x := ⟨L.base x.1, (L.base_mem_raw_iff S W x.1).mpr x.2⟩
  map_one' := Subtype.ext L.base.map_one
  map_mul' x y := Subtype.ext (L.base.map_mul x.1 y.1)

def normalizerToRawKernel :
    Subgroup.normalizer (W.subgroup : Set (PSp n F)) →* L.rawBase S W where
  toFun x := ⟨L.normalizerToRaw S W x, L.outer_base x.1⟩
  map_one' := Subtype.ext (map_one (L.normalizerToRaw S W))
  map_mul' x y := Subtype.ext (map_mul (L.normalizerToRaw S W) x y)

theorem normalizerToRawKernel_bijective : Function.Bijective (L.normalizerToRawKernel S W) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact L.base_injective (congrArg (fun z : L.rawBase S W => z.1.1) hxy)
  · intro g
    have hg : g.1.1 ∈ L.base.range := by
      rw [← L.outer_ker]
      exact g.2
    obtain ⟨x, hx⟩ := hg
    have hn : x ∈ Subgroup.normalizer (W.subgroup : Set (PSp n F)) := by
      apply (L.base_mem_raw_iff S W x).mp
      rw [hx]
      exact g.1.2
    exact ⟨⟨x, hn⟩, Subtype.ext (Subtype.ext hx)⟩

def rawBaseEquiv : Subgroup.normalizer (W.subgroup : Set (PSp n F)) ≃* L.rawBase S W :=
  MulEquiv.ofBijective (L.normalizerToRawKernel S W) (L.normalizerToRawKernel_bijective S W)

@[simp] theorem rawBaseEquiv_value (x : Subgroup.normalizer (W.subgroup : Set (PSp n F))) :
    (L.rawBaseEquiv S W x).1.1 = L.base x.1 := rfl

/-- Actual raw fixation retains the dependent own-character isomorphism.
The subsequent quotient-character consumer may not replace its character. -/
theorem raw_supplies_isomorphic (g : L.raw S W) :
    CharacterWeight.Isomorphic
      (W.rightTwist (S.fullAut ((L.embedding g.1)⁻¹))) W := by
  have hg := g.2
  change (Quotient.mk'' (W.rightTwist (S.fullAut ((L.embedding g.1)⁻¹))) :
    RawWeightClass (p := 2) (K := K) (H := PSp n F)) = Quotient.mk'' W at hg
  exact Quotient.exact hg

theorem raw_preserves_subgroup (g : L.raw S W) :
    W.subgroup.map (S.fullAut (L.embedding g.1)).toMonoidHom = W.subgroup := by
  obtain ⟨hg, _⟩ := L.raw_supplies_isomorphic S W g
  change W.subgroup.comap (S.fullAut ((L.embedding g.1)⁻¹)).toMonoidHom = _ at hg
  rw [map_inv] at hg
  exact (Subgroup.map_equiv_eq_comap_symm (S.fullAut (L.embedding g.1)) W.subgroup).trans hg

def radicalToRaw : W.subgroup →* L.raw S W :=
  (L.normalizerToRaw S W).comp (Subgroup.inclusion W.subgroup.le_normalizer)

def radical : Subgroup (L.raw S W) := (L.radicalToRaw S W).range

theorem radical_le_rawBase : L.radical S W ≤ L.rawBase S W := by
  rintro g ⟨q, rfl⟩
  exact L.outer_base q.1

instance radical_normal : (L.radical S W).Normal := by
  constructor
  rintro g ⟨q, rfl⟩ d
  have hq : S.fullAut (L.embedding d.1) q.1 ∈ W.subgroup := by
    have hm := Subgroup.mem_map_of_mem (S.fullAut (L.embedding d.1)).toMonoidHom q.2
    rw [L.raw_preserves_subgroup S W d] at hm
    exact hm
  refine ⟨⟨S.fullAut (L.embedding d.1) q.1, hq⟩, ?_⟩
  apply Subtype.ext
  exact L.base_conjugate S d.1 q.1

/-- The local inertia quotient by the actual embedded own Q. -/
abbrev LocalQuotient :=
  letI := L.radical_normal S W
  L.raw S W ⧸ L.radical S W

/-- The outer projection survives quotienting by Q, with its value fixed
on every original inertia element. -/
def localOuter : L.LocalQuotient S W →* T := by
  letI := L.radical_normal S W
  exact QuotientGroup.lift (L.radical S W) (L.rawOuter S W) (L.radical_le_rawBase S W)

theorem localOuter_ker :
    letI := L.radical_normal S W
    (L.localOuter S W).ker =
      (L.rawBase S W).map (QuotientGroup.mk' (L.radical S W)) := by
  letI := L.radical_normal S W
  exact QuotientGroup.ker_lift _ _ _

@[simp] theorem localOuter_mk (g : L.raw S W) :
    letI := L.radical_normal S W
    L.localOuter S W (QuotientGroup.mk' (L.radical S W) g) = L.outer g.1 := rfl

variable [IsCyclic T]

theorem global_outerQuotient_cyclic (psi : IBr iota) :
    IsCyclic (L.global S iota psi ⧸ L.globalBase S iota psi) :=
  isCyclic_of_injective (QuotientGroup.kerLift (L.globalOuter S iota psi))
    (QuotientGroup.kerLift_injective _)

theorem raw_outerQuotient_cyclic : IsCyclic (L.raw S W ⧸ L.rawBase S W) :=
  isCyclic_of_injective (QuotientGroup.kerLift (L.rawOuter S W))
    (QuotientGroup.kerLift_injective _)

/-- This quotient is precisely the local inertia quotient modulo its
embedded own normalizer quotient, by the proved localOuter_ker identity. -/
theorem local_outerQuotient_cyclic :
    IsCyclic (L.LocalQuotient S W ⧸ (L.localOuter S W).ker) :=
  isCyclic_of_injective (QuotientGroup.kerLift (L.localOuter S W))
    (QuotientGroup.kerLift_injective _)

end Geometry

end ModularRep.PaperProofs.OddTwoBroughExtensionGroups


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
