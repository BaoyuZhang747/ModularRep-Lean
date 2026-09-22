import ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
import ModularRep.PaperProofs.OddTwoCentralTwoWeightInflation
import ModularRep.PaperProofs.EvenFieldFLZSourceConditions

/-!
# The actual central quotient of the full automorphism semidirect groups

All ambient groups and maps are fixed: Sp, PSp, their actual automorphism
groups, and the canonical whole-centre quotient on both coordinates.
The full-cover lifting input supplies bijectivity only for that already
constructed automorphism map. The semidirect projection, its surjectivity
and its kernel (the embedded actual Sp centre) are K constructions.

Raw-pair stabilizers use the existing canonical action on IsoClass of raw
character weights, not ambient conjugacy classes. Actual quotient
naturality and the already proved injectivity of the raw quotient map give
their exact preimage equality. The global Brauer stabilizer is similarly
transported by the actual compatible-root inflation equivalence. No
stabilizer equality or character relation is a source field here.

The global stabilizer is identified with the literal Sp semidirect its
Brauer automorphism stabilizer, using inner class-function invariance.
These are group/carrier joins for the later MRR/butterfly argument; no
modular block-triple relation or covering/DGN conclusion is asserted.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoActualSemidirectQuotient

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoCentralTwoWeightInflation
open ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
  (OddSymplecticFullCoverSource)

universe u

/-- The literal full automorphism semidirect group. -/
abbrev Holomorph (G : Type u) [Group G] := G ⋊[MonoidHom.id (MulAut G)] MulAut G

local instance finiteAut (G : Type u) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun a : MulAut G => (a : G → G)) DFunLike.coe_injective

local instance groupFintype (G : Type u) [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite G

instance holomorphFinite (G : Type u) [Group G] [Finite G] : Finite (Holomorph G) :=
  Finite.of_equiv (G × MulAut G) SemidirectProduct.equivProd.symm

section LiteralProjection

variable {n : ℕ} {F : Type u} [Field F] [Finite F]

/-- The actual projection on the two literal semidirect coordinates. -/
def projection : Holomorph (Sp n F) →* Holomorph (PSp n F) :=
  SemidirectProduct.map (spProjection n F) projectiveAutHom (by
    intro alpha
    apply DFunLike.ext
    intro g
    exact (projectiveAutHom_projection alpha g).symm)

@[simp] theorem projection_left (d : Holomorph (Sp n F)) :
    (projection d).left = spProjection n F d.left := rfl

@[simp] theorem projection_right (d : Holomorph (Sp n F)) :
    (projection d).right = projectiveAutHom d.right := rfl

@[simp] theorem projection_inl (g : Sp n F) :
    projection (SemidirectProduct.inl g) = SemidirectProduct.inl (spProjection n F g) := by
  exact SemidirectProduct.map_inl _ _ _ _

@[simp] theorem projection_inr (a : MulAut (Sp n F)) :
    projection (SemidirectProduct.inr a) = SemidirectProduct.inr (projectiveAutHom a) := by
  exact SemidirectProduct.map_inr _ _ _ _

/-- The natural action homomorphisms used by the butterfly construction
commute with the SAME full semidirect projection. -/
theorem projective_semidirectToMulAut (d : Holomorph (Sp n F)) :
    projectiveAutHom (semidirectToMulAut (MonoidHom.id (MulAut (Sp n F))) d) =
      semidirectToMulAut (MonoidHom.id (MulAut (PSp n F))) (projection d) := by
  rw [← SemidirectProduct.inl_left_mul_inr_right d]
  simp only [map_mul, semidirectToMulAut_inl, semidirectToMulAut_inr,
    MonoidHom.id_apply, projection_inl, projection_inr, projectiveAutHom_inner]

/-- The kernel candidate is the actual centre embedded in the left factor. -/
def embeddedCenter : Subgroup (Holomorph (Sp n F)) :=
  (Subgroup.center (Sp n F)).map SemidirectProduct.inl

variable (cover : OddSymplecticFullCoverSource n F)
variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))

include cover L in
theorem projection_surjective : Function.Surjective (projection (n := n) (F := F)) := by
  intro d
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Sp n F)) d.left
  obtain ⟨a, ha⟩ := (L.bijective_on_full_cover cover).2 d.right
  refine ⟨⟨g, a⟩, ?_⟩
  apply SemidirectProduct.ext
  · exact hg
  · exact ha

include cover L in
theorem projection_kernel : (projection (n := n) (F := F)).ker = embeddedCenter := by
  ext d
  constructor
  · intro hd
    have hp : projection d = 1 := hd
    have hl : spProjection n F d.left = 1 := congrArg SemidirectProduct.left hp
    have hr : projectiveAutHom d.right = 1 := congrArg SemidirectProduct.right hp
    have ha : d.right = 1 := (L.bijective_on_full_cover cover).1
      (hr.trans projectiveAutHom.map_one.symm)
    refine ⟨d.left, (QuotientGroup.eq_one_iff _).mp hl, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact ha.symm
  · rintro ⟨g, hg, rfl⟩
    change projection (SemidirectProduct.inl g) = 1
    rw [projection_inl]
    have hgq : spProjection n F g = 1 := (QuotientGroup.eq_one_iff _).mpr hg
    rw [hgq, map_one]

/-- The actual quotient by the displayed kernel, with its canonical map. -/
def quotientEquiv : Holomorph (Sp n F) ⧸ (projection (n := n) (F := F)).ker ≃*
    Holomorph (PSp n F) :=
  QuotientGroup.quotientKerEquivOfSurjective projection (projection_surjective cover L)

end LiteralProjection

section CanonicalActions

variable {G k K : Type u} [Group G] [Finite G] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The exact existing canonical action on raw-pair isomorphism classes. -/
abbrev rawAction : MulAction (Holomorph G) (CharacterWeight.IsoClass (p := 2) (K := K)
    (G := G)) := canonicalRawSemidirectAction (MonoidHom.id (MulAut G))

/-- Fixing this IsoClass fixes the subgroup and its own character; it does
not mean only that an ambient conjugacy class has been fixed. -/
def rawPairStabilizer (W : CharacterWeight 2 K G) : Subgroup (Holomorph G) :=
  letI := rawAction (K := K) (G := G)
  MulAction.stabilizer (Holomorph G) (Quotient.mk'' W : CharacterWeight.IsoClass
    (p := 2) (K := K) (G := G))

/-- The canonical inverse/opposite automorphism action on actual IBr. -/
abbrev brauerAutAction (iota : PrimeRegularRootEmbedding 2 k K G) :
    MulAction (MulAut G) (IBr iota) := rightAutomorphismAction (MonoidHom.id (MulAut G))

/-- The canonical full semidirect action used by FLZ's global triple. -/
abbrev brauerAction (iota : PrimeRegularRootEmbedding 2 k K G) :
    MulAction (Holomorph G) (IBr iota) := by
  letI := rightAutomorphismAction (X := IBr iota) (MulAut.conj : G →* MulAut G)
  letI := brauerAutAction iota
  exact Formalisation.semidirectMulAction (MonoidHom.id (MulAut G))
    (rightAutomorphismSemidirectCompatible (X := IBr iota) (MonoidHom.id (MulAut G)))

def brauerStabilizer (iota : PrimeRegularRootEmbedding 2 k K G) (psi : IBr iota) :
    Subgroup (Holomorph G) :=
  letI := brauerAction iota
  MulAction.stabilizer (Holomorph G) psi

def brauerAutStabilizer (iota : PrimeRegularRootEmbedding 2 k K G) (psi : IBr iota) :
    Subgroup (MulAut G) :=
  letI := brauerAutAction iota
  MulAction.stabilizer (MulAut G) psi

/-- Inner class-function invariance identifies the full stabilizer with
the inverse image of the actual automorphism stabilizer. -/
theorem mem_brauerStabilizer_iff (iota : PrimeRegularRootEmbedding 2 k K G)
    (psi : IBr iota) (d : Holomorph G) :
    d ∈ brauerStabilizer iota psi ↔ d.right ∈ brauerAutStabilizer iota psi := by
  change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi d.right⁻¹) (MulAut.conj d.left⁻¹) = psi ↔
    IrreducibleBrauerCharacter.twist iota psi d.right⁻¹ = psi
  have hi : IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi d.right⁻¹) (MulAut.conj d.left⁻¹) =
        IrreducibleBrauerCharacter.twist iota psi d.right⁻¹ := by
    apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
    exact PrimeRegularClassFunction.twist_conj _ _
  rw [hi]

/-- The literal source global group G semidirect Aut(G)_psi. -/
abbrev BrauerSemidirect (iota : PrimeRegularRootEmbedding 2 k K G) (psi : IBr iota) :=
  G ⋊[(brauerAutStabilizer iota psi).subtype] (brauerAutStabilizer iota psi)

/-- This identification retains both coordinates and is fully constructed. -/
def brauerSemidirectEquiv (iota : PrimeRegularRootEmbedding 2 k K G) (psi : IBr iota) :
    BrauerSemidirect iota psi ≃* brauerStabilizer iota psi where
  toFun d := ⟨⟨d.left, d.right.1⟩,
    (mem_brauerStabilizer_iff iota psi ⟨d.left, d.right.1⟩).mpr d.right.2⟩
  invFun d := ⟨d.1.left, ⟨d.1.right, (mem_brauerStabilizer_iff iota psi d.1).mp d.2⟩⟩
  left_inv d := by cases d; rfl
  right_inv d := by apply Subtype.ext; rfl
  map_mul' d e := by apply Subtype.ext; rfl

@[simp] theorem brauerSemidirectEquiv_left (iota : PrimeRegularRootEmbedding 2 k K G)
    (psi : IBr iota) (d : BrauerSemidirect iota psi) :
    (brauerSemidirectEquiv iota psi d).1.left = d.left := rfl

@[simp] theorem brauerSemidirectEquiv_right (iota : PrimeRegularRootEmbedding 2 k K G)
    (psi : IBr iota) (d : BrauerSemidirect iota psi) :
    (brauerSemidirectEquiv iota psi d).1.right = d.right.1 := rfl

end CanonicalActions

section RawStabilizers

variable {n : ℕ} {F K : Type u} [Field F] [Finite F] [Field K] [CharZero K]
variable (cover : OddSymplecticFullCoverSource n F)
variable (T : ActualQuotientNaturality (K := K) (spProjection n F)
  cover.fullCover.1.1 cover.projection_twoKernel)

local instance rawUpAction : MulAction (Holomorph (Sp n F))
    (CharacterWeight.IsoClass (p := 2) (K := K) (G := Sp n F)) := rawAction
local instance rawDownAction : MulAction (Holomorph (PSp n F))
    (CharacterWeight.IsoClass (p := 2) (K := K) (G := PSp n F)) := rawAction

include T in
/-- Exact naturality under the actual two-coordinate semidirect map. -/
theorem quotientIsoClass_holomorph (d : Holomorph (Sp n F))
    (w : CharacterWeight.IsoClass (p := 2) (K := K) (G := Sp n F)) :
    quotientIsoClass (spProjection n F) cover.fullCover.1.1 cover.projection_twoKernel (d • w) =
      projection d • quotientIsoClass (spProjection n F) cover.fullCover.1.1
        cover.projection_twoKernel w := by
  change quotientIsoClass _ _ _
      (rightTwistIsoClass (MulAut.conj d.left⁻¹) (rightTwistIsoClass d.right⁻¹ w)) =
    rightTwistIsoClass (MulAut.conj (spProjection n F d.left)⁻¹)
      (rightTwistIsoClass (projectiveAutHom d.right)⁻¹ (quotientIsoClass _ _ _ w))
  rw [T.quotientIsoClass_rightTwist (MulAut.conj d.left⁻¹)
    (MulAut.conj (spProjection n F d.left)⁻¹) (by intro g; simp)]
  rw [T.quotientIsoClass_rightTwist d.right⁻¹ (projectiveAutHom d.right⁻¹)
    (by intro g; exact (projectiveAutHom_projection d.right⁻¹ g).symm)]
  rw [map_inv (projectiveAutHom (n := n) (F := F)) d.right]

include T in
/-- Equality uses injectivity ultimately proved for the actual raw quotient
map, hence retains the SAME own ordinary character. -/
theorem rawPairStabilizer_preimage (W : CharacterWeight 2 K (Sp n F)) :
    (rawPairStabilizer (spQuotientPair cover W)).comap projection = rawPairStabilizer W := by
  ext d
  change projection d • quotientIsoClass (spProjection n F) cover.fullCover.1.1
      cover.projection_twoKernel (Quotient.mk'' W) =
    quotientIsoClass (spProjection n F) cover.fullCover.1.1
      cover.projection_twoKernel (Quotient.mk'' W) ↔
    d • (Quotient.mk'' W : CharacterWeight.IsoClass (p := 2) (K := K) (G := Sp n F)) =
      Quotient.mk'' W
  rw [← quotientIsoClass_holomorph cover T d]
  let e := isoClassEquiv (K := K) (spProjection n F) cover.fullCover.1.1
    cover.projection_twoKernel
  change e (d • Quotient.mk'' W) = e (Quotient.mk'' W) ↔
    d • (Quotient.mk'' W : CharacterWeight.IsoClass (p := 2) (K := K) (G := Sp n F)) =
      Quotient.mk'' W
  exact e.injective.eq_iff

variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))

include T L in
theorem embeddedCenter_le_rawPairStabilizer (W : CharacterWeight 2 K (Sp n F)) :
    embeddedCenter ≤ rawPairStabilizer W := by
  rw [← projection_kernel cover L, ← rawPairStabilizer_preimage cover T W]
  exact Subgroup.ker_le_comap projection _

end RawStabilizers

section BrauerStabilizers

variable {n : ℕ} {F k K : Type u} [Field F] [Finite F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable {iotaUp : PrimeRegularRootEmbedding 2 k K (Sp n F)}
variable {iotaDown : PrimeRegularRootEmbedding 2 k K (PSp n F)}
variable (B : BrauerInflationSources iotaUp iotaDown)
variable (cover : OddSymplecticFullCoverSource n F)

local instance brauerUpAction : MulAction (Holomorph (Sp n F)) (IBr iotaUp) :=
  brauerAction iotaUp
local instance brauerDownAction : MulAction (Holomorph (PSp n F)) (IBr iotaDown) :=
  brauerAction iotaDown

/-- The same actual inflation map is equivariant for the full holomorph. -/
theorem brauerEquiv_holomorph (d : Holomorph (Sp n F)) (psi : IBr iotaDown) :
    B.brauerEquiv cover (projection d • psi) = d • B.brauerEquiv cover psi := by
  change B.brauerEquiv cover
      (IrreducibleBrauerCharacter.twist iotaDown
        (IrreducibleBrauerCharacter.twist iotaDown psi (projectiveAutHom d.right)⁻¹)
        (MulAut.conj (spProjection n F d.left)⁻¹)) =
    IrreducibleBrauerCharacter.twist iotaUp
      (IrreducibleBrauerCharacter.twist iotaUp (B.brauerEquiv cover psi) d.right⁻¹)
      (MulAut.conj d.left⁻¹)
  have hi : projectiveAutHom (MulAut.conj d.left⁻¹) =
      MulAut.conj (spProjection n F d.left)⁻¹ := by rw [projectiveAutHom_inner, map_inv]
  rw [← hi, ← map_inv projectiveAutHom]
  simp only [projectiveAutHom_eq_global, B.brauerEquiv_twist]

theorem brauerStabilizer_preimage (psi : IBr iotaDown) :
    (brauerStabilizer iotaDown psi).comap projection =
      brauerStabilizer iotaUp (B.brauerEquiv cover psi) := by
  ext d
  change projection d • psi = psi ↔ d • B.brauerEquiv cover psi = B.brauerEquiv cover psi
  rw [← brauerEquiv_holomorph B cover]
  exact (B.brauerEquiv cover).injective.eq_iff.symm

/-- The actual acting groups Aut(Sp)_psi and Aut(PSp)_barpsi are related
by the same canonical automorphism homomorphism, not a free adapter. -/
theorem brauerAutStabilizer_preimage (psi : IBr iotaDown) :
    (brauerAutStabilizer iotaDown psi).comap projectiveAutHom =
      brauerAutStabilizer iotaUp (B.brauerEquiv cover psi) := by
  ext a
  have h : (SemidirectProduct.inr a : Holomorph (Sp n F)) ∈
      (brauerStabilizer iotaDown psi).comap projection ↔
    (SemidirectProduct.inr a : Holomorph (Sp n F)) ∈
      brauerStabilizer iotaUp (B.brauerEquiv cover psi) := by
    rw [brauerStabilizer_preimage B cover psi]
  simpa only [Subgroup.mem_comap, projection_inr, mem_brauerStabilizer_iff,
    SemidirectProduct.right_inr] using h

variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))

include L in
theorem embeddedCenter_le_brauerStabilizer (psi : IBr iotaDown) :
    embeddedCenter ≤ brauerStabilizer iotaUp (B.brauerEquiv cover psi) := by
  rw [← projection_kernel cover L, ← brauerStabilizer_preimage B cover psi]
  exact Subgroup.ker_le_comap projection _

/-- Restrict the SAME projection to the actual global Brauer stabilizers. -/
def brauerStabilizerProjection (psi : IBr iotaDown) :
    brauerStabilizer iotaUp (B.brauerEquiv cover psi) →* brauerStabilizer iotaDown psi where
  toFun d := ⟨projection d.1, by
    exact Eq.mp (congrArg (fun Q : Subgroup (Holomorph (Sp n F)) => d.1 ∈ Q)
      (brauerStabilizer_preimage B cover psi).symm) d.2⟩
  map_one' := Subtype.ext (map_one projection)
  map_mul' d e := Subtype.ext (map_mul projection d.1 e.1)

@[simp] theorem brauerStabilizerProjection_coe (psi : IBr iotaDown)
    (d : brauerStabilizer iotaUp (B.brauerEquiv cover psi)) :
    (brauerStabilizerProjection B cover psi d : Holomorph (PSp n F)) = projection d.1 := rfl

include L in
theorem brauerStabilizerProjection_surjective (psi : IBr iotaDown) :
    Function.Surjective (brauerStabilizerProjection B cover psi) := by
  intro d
  obtain ⟨a, ha⟩ := projection_surjective cover L d.1
  have hm : a ∈ brauerStabilizer iotaUp (B.brauerEquiv cover psi) := by
    rw [← brauerStabilizer_preimage B cover psi]
    change projection a ∈ brauerStabilizer iotaDown psi
    rw [ha]
    exact d.2
  exact ⟨⟨a, hm⟩, Subtype.ext ha⟩

include L in
theorem brauerStabilizerProjection_kernel (psi : IBr iotaDown) :
    (brauerStabilizerProjection B cover psi).ker =
      embeddedCenter.subgroupOf (brauerStabilizer iotaUp (B.brauerEquiv cover psi)) := by
  ext d
  change brauerStabilizerProjection B cover psi d = 1 ↔ d.1 ∈ embeddedCenter
  rw [← projection_kernel cover L]
  change brauerStabilizerProjection B cover psi d = 1 ↔ projection d.1 = 1
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

/-- The projection on the literally displayed FLZ global semidirect groups. -/
def brauerSemidirectProjection (psi : IBr iotaDown) :
    BrauerSemidirect iotaUp (B.brauerEquiv cover psi) →* BrauerSemidirect iotaDown psi :=
  (brauerSemidirectEquiv iotaDown psi).symm.toMonoidHom.comp
    ((brauerStabilizerProjection B cover psi).comp
      (brauerSemidirectEquiv iotaUp (B.brauerEquiv cover psi)).toMonoidHom)

@[simp] theorem brauerSemidirectProjection_left (psi : IBr iotaDown)
    (d : BrauerSemidirect iotaUp (B.brauerEquiv cover psi)) :
    (brauerSemidirectProjection B cover psi d).left = spProjection n F d.left := rfl

@[simp] theorem brauerSemidirectProjection_right (psi : IBr iotaDown)
    (d : BrauerSemidirect iotaUp (B.brauerEquiv cover psi)) :
    (brauerSemidirectProjection B cover psi d).right.1 = projectiveAutHom d.right.1 := rfl

include L in
theorem brauerSemidirectProjection_surjective (psi : IBr iotaDown) :
    Function.Surjective (brauerSemidirectProjection B cover psi) :=
  (brauerSemidirectEquiv iotaDown psi).symm.surjective.comp
    ((brauerStabilizerProjection_surjective B cover L psi).comp
      (brauerSemidirectEquiv iotaUp (B.brauerEquiv cover psi)).surjective)

include L in
/-- On the literally displayed restricted semidirect product the kernel
is again exactly the centre in the left factor, with trivial automorphism
coordinate. This is the normal subgroup used by the upward MRR passage. -/
theorem brauerSemidirectProjection_kernel (psi : IBr iotaDown) :
    (brauerSemidirectProjection B cover psi).ker =
      (Subgroup.center (Sp n F)).map
        (SemidirectProduct.inl : Sp n F →* BrauerSemidirect iotaUp (B.brauerEquiv cover psi)) := by
  ext d
  constructor
  · intro hd
    have hp : brauerSemidirectProjection B cover psi d = 1 := hd
    have hl : spProjection n F d.left = 1 := congrArg SemidirectProduct.left hp
    have hr : projectiveAutHom d.right.1 = 1 :=
      congrArg (fun x : BrauerSemidirect iotaDown psi => x.right.1) hp
    have ha : d.right = 1 := Subtype.ext ((L.bijective_on_full_cover cover).1
      (hr.trans projectiveAutHom.map_one.symm))
    refine ⟨d.left, (QuotientGroup.eq_one_iff _).mp hl, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact ha.symm
  · rintro ⟨g, hg, rfl⟩
    change brauerSemidirectProjection B cover psi (SemidirectProduct.inl g) = 1
    apply SemidirectProduct.ext
    · exact (QuotientGroup.eq_one_iff _).mpr hg
    · apply Subtype.ext
      exact projectiveAutHom.map_one

variable (T : ActualQuotientNaturality (K := K) (spProjection n F)
  cover.fullCover.1.1 cover.projection_twoKernel)

include T in
/-- The local raw-pair group inside the global character stabilizer is
the exact preimage of its OWN quotient pair's local stabilizer. No choice
of a different downstairs representative or local character occurs. -/
theorem localPairStabilizer_preimage (psi : IBr iotaDown)
    (W : CharacterWeight 2 K (Sp n F)) :
    ((rawPairStabilizer (spQuotientPair cover W)).subgroupOf (brauerStabilizer iotaDown psi)).comap
        (brauerStabilizerProjection B cover psi) =
      (rawPairStabilizer W).subgroupOf (brauerStabilizer iotaUp (B.brauerEquiv cover psi)) := by
  ext d
  change projection d.1 ∈ rawPairStabilizer (spQuotientPair cover W) ↔
    d.1 ∈ rawPairStabilizer W
  change d.1 ∈ (rawPairStabilizer (spQuotientPair cover W)).comap projection ↔ _
  rw [rawPairStabilizer_preimage cover T W]

end BrauerStabilizers

end ModularRep.PaperProofs.OddTwoActualSemidirectQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
