import ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
import ModularRep.PaperProofs.OddTwoFengMalleForwardSourceJoin
import ModularRep.BrauerQuotientLinearCharacterAction
import ModularRep.NavarroBrauerRestrictionCovering
import Mathlib.Algebra.CharP.Two

/-!
# Actual PSp--PCSp covering objects for the principal orbit argument

The groups, inclusion, field automorphisms, raw weights, normalizer quotients,
and all character functions below are literal. BS Definition 2.6 is expanded
through its actual M/Q, D, centralizer, DGN character and constituent data.
Only the defect-block/DGN interpretation itself remains an explicit, narrowly
typed source meaning: this module does not reconstruct DGN theory.

The external laws are the cyclic-quotient specialization of Brauer Clifford
existence and BS 2.12, 2.14(a), 2.15(a), together with naturality of this exact
covering definition. The ordinary and modular inertia extensions used in
their proof are licensed by Isaacs 11.22 and Navarro 8.12. No uniqueness,
principal membership, matched covering pair, or orbit witness is an input.

K proves LinBr(PCSp/PSp)=1 from the actual quotient cardinal and CharP k 2,
then derives unique covering characters and weight CLASSES, their field
fixation, and the common mu=1. Actual primitive-idempotent covering, BS
Remark 4.2 and Navarro 9.6 give the common covering block. No invariant raw
covering representative is selected. No BS 4.6 or block-triple conclusion
is asserted. See the companion source contract for the exact E1/E2 scope.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.OddTwoBroughCoveringSource

open ModularRep.CharacterWeight
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoFengMalleForwardSourceJoin (CompatibleReduction)

universe u

variable {n : ℕ} {F k K : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]

local instance groupFintype {G : Type u} [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite _

variable (C : CenterIntersectionSource n F) (S : BroughGroupSource C)

/- Install this instance by `letI := S.normal_image` at an application.
Making it explicit avoids trying to infer S from a goal mentioning only C. -/
variable [projectiveBaseNormal : (pspEmbedding C).range.Normal]

abbrev BaseWeight := CharacterWeight 2 K (PSp n F)
abbrev CoverWeight := CharacterWeight 2 K (PCSp n F)
abbrev BaseWeightClass := CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := PSp n F)
abbrev CoverWeightClass := CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := PCSp n F)

def weightClass {G : Type u} [Group G] [Finite G] (W : CharacterWeight 2 K G) :
    CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G) :=
  Quotient.mk'' (Quotient.mk'' W : CharacterWeight.IsoClass (p := 2) (K := K) (G := G))

def baseNormalizerImage (W : BaseWeight (n := n) (F := F) (K := K)) : Subgroup (PCSp n F) :=
  (Subgroup.normalizer (W.subgroup : Set (PSp n F))).map (pspEmbedding C)

/-- Actual intermediate subgroup from BS Definition 2.6. The inertia
condition fixes the WHOLE supplied raw pair, including its own character. -/
structure IntermediateData (W : BaseWeight (n := n) (F := F) (K := K))
    (V : CoverWeight (n := n) (F := F) (K := K)) where
  M : Subgroup (PCSp n F)
  normalizer_le : baseNormalizerImage C W ≤ M
  base_le_cover : W.subgroup.map (pspEmbedding C) ≤ V.subgroup
  cover_le : V.subgroup ≤ M
  inertia : ∀ x : M, W.rightTwist (S.pcspToAut x.1)⁻¹ = W
  [base_normal : ((W.subgroup.map (pspEmbedding C)).subgroupOf M).Normal]

attribute [instance] IntermediateData.base_normal

namespace IntermediateData

variable {C S} {W : BaseWeight (n := n) (F := F) (K := K)}
variable {V : CoverWeight (n := n) (F := F) (K := K)}
variable (T : IntermediateData C S W V)

abbrev Quotient := T.M ⧸ (W.subgroup.map (pspEmbedding C)).subgroupOf T.M

def projection : T.M →* T.Quotient := QuotientGroup.mk' _

def D : Subgroup T.Quotient := (V.subgroup.subgroupOf T.M).map T.projection

def Nbar : Subgroup T.Quotient :=
  ((baseNormalizerImage C W).subgroupOf T.M).map T.projection

/-- Literally C_(N/Q)(D), kept as a subgroup of the actual M/Q. -/
def centralizer : Subgroup T.Quotient :=
  T.Nbar ⊓ Subgroup.centralizer (T.D : Set T.Quotient)

def normalizerToM : Subgroup.normalizer (W.subgroup : Set (PSp n F)) →* T.M where
  toFun x := ⟨pspEmbedding C x.1, T.normalizer_le (by exact ⟨x.1, x.2, rfl⟩)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

def centralizerToLocal : T.centralizer →* NormalizerQuotient T.D :=
  (QuotientGroup.mk' (T.D.subgroupOf (Subgroup.normalizer (T.D : Set T.Quotient)))).comp
    { toFun := fun x => ⟨x.1, Subgroup.centralizer_le_normalizer _ x.2.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }

/-- Only coordinate/group identifications in BS's displayed construction.
Every hom is pinned on actual lifts. There is no character choice here. -/
structure QuotientData where
  [normal_Nbar : T.Nbar.Normal]
  quotient_two_group : IsPGroup 2 (T.Quotient ⧸ T.Nbar)
  defect_two_group : IsPGroup 2 T.D
  disjoint : T.D ⊓ T.Nbar = ⊥
  product : T.Nbar ⊔ T.D = ⊤
  normalizer_product : Subgroup.normalizer (T.D : Set T.Quotient) = T.centralizer ⊔ T.D
  baseLocalEquiv : NormalizerQuotient W.subgroup ≃* T.Nbar
  baseLocal_square : ∀ x : Subgroup.normalizer (W.subgroup : Set (PSp n F)),
    (baseLocalEquiv (QuotientGroup.mk' _ x) : T.Quotient) =
      T.projection (T.normalizerToM x)
  localEmbedding : NormalizerQuotient T.D →* NormalizerQuotient V.subgroup
  localEmbedding_injective : Function.Injective localEmbedding
  normalizer_lift : ∀ x : T.M,
    T.projection x ∈ Subgroup.normalizer (T.D : Set T.Quotient) →
      x.1 ∈ Subgroup.normalizer (V.subgroup : Set (PCSp n F))
  local_square : ∀ (x : T.M)
    (hx : T.projection x ∈ Subgroup.normalizer (T.D : Set T.Quotient)),
    localEmbedding (QuotientGroup.mk' _ ⟨T.projection x, hx⟩) =
      QuotientGroup.mk' _ ⟨x.1, normalizer_lift x hx⟩

end IntermediateData

/-- The one retained semantic definition boundary. For these exact data,
`defectAndDGN T Q pi` means: D is a defect group of the unique block of
M/Q covering bl(W.localCharacter) under Q.baseLocalEquiv, and pi is its
DGN correspondent on T.centralizer. This is BS pp.468--469, immediately
before and in Definition 2.6, using Navarro--Spath Theorem 5.2.

This record supplies NO existence, uniqueness, covering weight, covariance,
block equality or orbit relation. An arbitrary predicate has no licensed
interpretation; an application must use this exact standard source meaning.
Keeping this substantial source definition external is intentional. -/
structure DGNSourceSemantics where
  defectAndDGN : ∀ {W : BaseWeight (n := n) (F := F) (K := K)}
    {V : CoverWeight (n := n) (F := F) (K := K)}
    (T : IntermediateData C S W V), T.QuotientData → Irr K T.centralizer → Prop

/-- Genuine ordinary restriction constituent support, on an actual hom. -/
def OrdinaryOccursAlong {A B : Type u} [Group A] [Group B]
    (f : A →* B) (chi : Irr K B) (theta : Irr K A) : Prop :=
  ∃ multiplicity : Irr K A →₀ ℕ, multiplicity theta ≠ 0 ∧
    ∀ x : A, chi (f x) = multiplicity.sum (fun eta r => (r : K) * eta x)

/-- BS Definition 2.6 with the actual local character of BOTH raw pairs.
The bar-pi value equation is the lift of pi times 1_D, because the actual
normalizer is C_(N/Q)(D) D and D is killed by its displayed quotient. -/
structure CoveringOccurrence (A : DGNSourceSemantics (K := K) C S)
    (W : BaseWeight (n := n) (F := F) (K := K))
    (V : CoverWeight (n := n) (F := F) (K := K)) where
  intermediate : IntermediateData C S W V
  quotient : intermediate.QuotientData
  pi : Irr K intermediate.centralizer
  pi_defectZero : IsDefectZeroOrdinaryCharacter 2 pi
  dgn : A.defectAndDGN intermediate quotient pi
  barPi : Irr K (NormalizerQuotient intermediate.D)
  barPi_value : ∀ x : intermediate.centralizer,
    barPi (intermediate.centralizerToLocal x) = pi x
  own_constituent : OrdinaryOccursAlong quotient.localEmbedding V.localCharacter barPi

/-- Definition 2.6 passed to the actual two conjugacy class carriers, with
the allowed PCSp conjugate of the base pair explicitly retained. -/
def WeightCovers (A : DGNSourceSemantics (K := K) C S)
    (w : BaseWeightClass (n := n) (F := F) (K := K))
    (v : CoverWeightClass (n := n) (F := F) (K := K)) : Prop :=
  ∃ (W : BaseWeight (n := n) (F := F) (K := K))
    (V : CoverWeight (n := n) (F := F) (K := K)) (t : PCSp n F),
    weightClass W = w ∧ weightClass V = v ∧
      Nonempty (CoveringOccurrence C S A (W.rightTwist (S.pcspToAut t)⁻¹) V)

abbrev QuotientLinBr (_source : BroughGroupSource C) :=
  (PCSp n F ⧸ (pspEmbedding C).range) →* kˣ

def ambientLinear (lambda : QuotientLinBr (k := k) C S) : PCSp n F →* kˣ :=
  lambda.comp (QuotientGroup.mk' (pspEmbedding C).range)

/-- Characteristic two has no nontrivial homomorphism C2 -> k^*. -/
theorem quotientLinBr_eq_one (lambda : QuotientLinBr (k := k) C S) : lambda = 1 := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  have hx : x ^ 2 = 1 := by simpa only [S.quotient_card] using (pow_card_eq_one' (x := x))
  have hv : (lambda x : k) ^ 2 = 1 := by
    have h := congrArg (fun y : kˣ => (y : k)) (congrArg lambda hx)
    simpa using h
  apply CharTwo.sq_injective
  simpa using hv

theorem ambientLinear_eq_one (lambda : QuotientLinBr (k := k) C S) :
    ambientLinear C S lambda = 1 := by
  rw [quotientLinBr_eq_one C S lambda]
  rfl

variable (iotaX : PrimeRegularRootEmbedding 2 k K (PSp n F))
variable (iotaT : PrimeRegularRootEmbedding 2 k K (PCSp n F))

/-- Actual nonnegative Brauer restriction expansion along the FIXED
projective matrix inclusion. The two roots are kept in the type. -/
def CharacterCovers (phi : IBr iotaX) (Phi : IBr iotaT) : Prop :=
  ∃ multiplicity : IBr iotaX →₀ ℕ, multiplicity phi ≠ 0 ∧
    ∀ x : PrimeRegularElement (G := PSp n F) 2,
      Phi.1 (PrimeRegularElement.map (pspEmbedding C) x) =
        multiplicity.sum (fun eta r => (r : K) * eta.1 x)

/-- The actual constant-one character upstairs covers the actual
constant-one character downstairs, by the one-term restriction expansion. -/
theorem constantOne_covers (oneX : IBr iotaX) (oneT : IBr iotaT)
    (hx : ∀ x, oneX.1 x = 1) (ht : ∀ x, oneT.1 x = 1) :
    CharacterCovers C iotaX iotaT oneX oneT := by
  classical
  refine ⟨Finsupp.single oneX 1, by simp, ?_⟩
  intro x
  simp [hx, ht]

private theorem lift_one : iotaT.lift (1 : k) = (1 : K) := by
  have h := iotaT.lift_coe (1 : rootsOfUnity (primeRegularExponent 2 (PCSp n F)) k)
  simpa [PrimeRegularRootEmbedding.liftRoot] using h

/-- The standard linear twist on weight CLASSES stated through actual
representatives and character values on normalizer lifts. There is no
freely selected action. Here every lambda is one, so the displayed lift is
always evaluated at a genuine root (one), never outside its domain. -/
def LinearWeightRelated (lambda : QuotientLinBr (k := k) C S)
    (v v' : CoverWeightClass (n := n) (F := F) (K := K)) : Prop :=
  ∃ (V V' : CoverWeight (n := n) (F := F) (K := K)),
    weightClass V = v ∧ weightClass V' = v' ∧
    ∃ hQ : V.subgroup = V'.subgroup,
      ∀ x : Subgroup.normalizer (V'.subgroup : Set (PCSp n F)),
        castLocalCharacter hQ V.localCharacter (QuotientGroup.mk' _ x) =
          iotaT.lift ((ambientLinear C S lambda x.1 : kˣ) : k) *
            V'.localCharacter (QuotientGroup.mk' _ x)

theorem linearWeightRelated_eq {lambda : QuotientLinBr (k := k) C S}
    {v v' : CoverWeightClass (n := n) (F := F) (K := K)}
    (h : LinearWeightRelated C S iotaT lambda v v') : v = v' := by
  obtain ⟨V, V', rfl, rfl, hQ, hchar⟩ := h
  have hVV' : V = V' := by
    apply CharacterWeight.eq_of_isomorphic
    refine ⟨hQ, ?_⟩
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
    simpa only [ambientLinear_eq_one C S lambda, MonoidHom.one_apply,
      Units.val_one, lift_one iotaT, one_mul] using hchar y
  exact congrArg weightClass hVV'

theorem linearWeightRelated_one_refl
    (v : CoverWeightClass (n := n) (F := F) (K := K)) :
    LinearWeightRelated C S iotaT 1 v v := by
  refine Quotient.inductionOn v ?_
  intro v
  refine Quotient.inductionOn v ?_
  intro V
  refine ⟨V, V, rfl, rfl, rfl, ?_⟩
  intro x
  simp only [castLocalCharacter_rfl, ambientLinear_eq_one C S,
    MonoidHom.one_apply, Units.val_one, lift_one iotaT, one_mul]

/-- Exact standard E1/E2 covering laws on these fixed source definitions.
The orbit statements retain the actual linear character and its value
formula; unique covering objects are NOT fields. Because PCSp/PSp=C2,
Hypothesis 2.13 follows from the standard cyclic inertia-extension theorems.
Their cyclic specialization, rather than an unrelated extension choice,
is included in the source license for these two orbit fields.

Field covariance includes canonical DGN isomorphism naturality for the
actual pair-preserving field automorphism. BS Remark 2.11 alone states only
ambient conjugation covariance and is not misquoted as the whole claim. -/
structure BroughCoveringLaws (A : DGNSourceSemantics (K := K) C S) where
  ordinarySplitting : IsAlgClosed K
  commonRoots : RootCompatibleAlong iotaT iotaX (pspEmbedding C)
  tensorFormula : BrauerLinearTensorProductFormula iotaT
  character_exists : ∀ phi : IBr iotaX, ∃ Phi : IBr iotaT, CharacterCovers C iotaX iotaT phi Phi
  character_orbit : ∀ (phi : IBr iotaX) (Phi Psi : IBr iotaT),
    CharacterCovers C iotaX iotaT phi Phi → CharacterCovers C iotaX iotaT phi Psi →
      ∃ lambda : QuotientLinBr (k := k) C S,
        Psi = IrreducibleBrauerCharacter.linearTwist iotaT tensorFormula Phi
          (ambientLinear C S lambda)
  weight_exists : ∀ W : BaseWeight (n := n) (F := F) (K := K),
    ∃ V : CoverWeight (n := n) (F := F) (K := K),
      Nonempty (CoveringOccurrence C S A W V)
  weight_orbit : ∀ (w : BaseWeightClass (n := n) (F := F) (K := K))
    (v v' : CoverWeightClass (n := n) (F := F) (K := K)),
    WeightCovers C S A w v → WeightCovers C S A w v' →
      ∃ lambda : QuotientLinBr (k := k) C S, LinearWeightRelated C S iotaT lambda v v'
  character_covariance : ∀ (sigma : F ≃+* F) (phi : IBr iotaX) (Phi : IBr iotaT),
    CharacterCovers C iotaX iotaT phi Phi →
      CharacterCovers C iotaX iotaT
        (IrreducibleBrauerCharacter.twist iotaX phi (pspFieldAction sigma)⁻¹)
        (IrreducibleBrauerCharacter.twist iotaT Phi (pcspFieldAction sigma)⁻¹)
  weight_covariance : ∀ (sigma : F ≃+* F)
    (w : BaseWeightClass (n := n) (F := F) (K := K))
    (v : CoverWeightClass (n := n) (F := F) (K := K)),
    WeightCovers C S A w v → WeightCovers C S A
      (rightTwistConjugacyClass (pspFieldAction sigma)⁻¹ w)
      (rightTwistConjugacyClass (pcspFieldAction sigma)⁻¹ v)

namespace BroughCoveringLaws

variable {C S iotaX iotaT} {A : DGNSourceSemantics (K := K) C S}
variable (L : BroughCoveringLaws C S iotaX iotaT A)

include L

theorem character_unique {phi : IBr iotaX} {Phi Psi : IBr iotaT}
    (hPhi : CharacterCovers C iotaX iotaT phi Phi)
    (hPsi : CharacterCovers C iotaX iotaT phi Psi) : Phi = Psi := by
  obtain ⟨lambda, h⟩ := L.character_orbit phi Phi Psi hPhi hPsi
  simpa only [ambientLinear_eq_one C S lambda,
    IrreducibleBrauerCharacter.linearTwist_one] using h.symm

theorem weight_unique {w : BaseWeightClass (n := n) (F := F) (K := K)}
    {v v' : CoverWeightClass (n := n) (F := F) (K := K)}
    (hv : WeightCovers C S A w v) (hv' : WeightCovers C S A w v') : v = v' := by
  obtain ⟨lambda, h⟩ := L.weight_orbit w v v' hv hv'
  exact linearWeightRelated_eq C S iotaT h

theorem weight_class_exists (W : BaseWeight (n := n) (F := F) (K := K)) :
    ∃ v : CoverWeightClass (n := n) (F := F) (K := K), WeightCovers C S A (weightClass W) v := by
  obtain ⟨V, hV⟩ := L.weight_exists W
  refine ⟨weightClass V, W, V, 1, rfl, rfl, ?_⟩
  have hW : W.rightTwist (1 : MulAut (PSp n F)) = W :=
    CharacterWeight.eq_of_isomorphic W.rightTwist_one_isomorphic
  simpa only [map_one, inv_one, hW] using hV

theorem character_fixed (sigma : F ≃+* F) {phi : IBr iotaX} {Phi : IBr iotaT}
    (hPhi : CharacterCovers C iotaX iotaT phi Phi)
    (hphi : IrreducibleBrauerCharacter.twist iotaX phi (pspFieldAction sigma)⁻¹ = phi) :
    IrreducibleBrauerCharacter.twist iotaT Phi (pcspFieldAction sigma)⁻¹ = Phi := by
  exact L.character_unique (by simpa only [hphi] using L.character_covariance sigma phi Phi hPhi) hPhi

theorem weight_fixed (sigma : F ≃+* F)
    {w : BaseWeightClass (n := n) (F := F) (K := K)}
    {v : CoverWeightClass (n := n) (F := F) (K := K)}
    (hv : WeightCovers C S A w v)
    (hw : rightTwistConjugacyClass (pspFieldAction sigma)⁻¹ w = w) :
    rightTwistConjugacyClass (pcspFieldAction sigma)⁻¹ v = v := by
  exact L.weight_unique (by simpa only [hw] using L.weight_covariance sigma w v hv) hv

/-- The SAME linear Brauer character works on both covering objects.
This is the short clause-(iv) deduction, not a BS 4.6 orbit witness. -/
theorem common_mu_one (sigma : F ≃+* F) {phi : IBr iotaX} {Phi : IBr iotaT}
    {w : BaseWeightClass (n := n) (F := F) (K := K)}
    {v : CoverWeightClass (n := n) (F := F) (K := K)}
    (hPhi : CharacterCovers C iotaX iotaT phi Phi) (hv : WeightCovers C S A w v)
    (hphi : IrreducibleBrauerCharacter.twist iotaX phi (pspFieldAction sigma)⁻¹ = phi)
    (hw : rightTwistConjugacyClass (pspFieldAction sigma)⁻¹ w = w) :
    ∃ lambda : QuotientLinBr (k := k) C S, lambda = 1 ∧
      IrreducibleBrauerCharacter.twist iotaT Phi (pcspFieldAction sigma)⁻¹ =
        IrreducibleBrauerCharacter.linearTwist iotaT L.tensorFormula Phi
          (ambientLinear C S lambda) ∧
      LinearWeightRelated C S iotaT lambda
        (rightTwistConjugacyClass (pcspFieldAction sigma)⁻¹ v) v := by
  refine ⟨1, rfl, ?_, ?_⟩
  · rw [ambientLinear_eq_one C S, IrreducibleBrauerCharacter.linearTwist_one]
    exact L.character_fixed sigma hPhi hphi
  · rw [L.weight_fixed sigma hv hw]
    exact linearWeightRelated_one_refl C S iotaT v

end BroughCoveringLaws

section ActualBlocks

variable {BlockX BlockT : Type u}
variable [MulAction (MulAut (PSp n F))ᵐᵒᵖ BlockX]
variable [MulAction (MulAut (PCSp n F))ᵐᵒᵖ BlockT]
variable (OX : LocalBlockInductionSource (p := 2) (k := k) (K := K) (G := PSp n F) (Block := BlockX))
variable (OT : LocalBlockInductionSource (p := 2) (k := k) (K := K) (G := PCSp n F) (Block := BlockT))
variable (injX : IrreducibleBrauerCharacterInjectivity iotaX)
variable (injT : IrreducibleBrauerCharacterInjectivity iotaT)

def baseBrauerBlock (phi : IBr iotaX) : BlockX :=
  letI := OX.operations.ambientBlockData.fintypeBlock
  irreducibleBrauerCharacterBlock iotaX injX OX.operations.ambientBlockData.blocks phi

def coverBrauerBlock (Phi : IBr iotaT) : BlockT :=
  letI := OT.operations.ambientBlockData.fintypeBlock
  irreducibleBrauerCharacterBlock iotaT injT OT.operations.ambientBlockData.blocks Phi

/-- Literal block covering by the usual nonzero primitive-idempotent
product along the ACTUAL subgroup inclusion. No free covering relation. -/
def BlocksCover (b : BlockX) (B : BlockT) : Prop :=
  OT.operations.ambientBlockData.blockIdempotent B *
    MonoidAlgebra.mapDomainAlgHom k k (pspEmbedding C)
      (OX.operations.ambientBlockData.blockIdempotent b) ≠ 0

/-- Standard block laws, separately interpreted on the same coefficient
and own-local-character operations. Navarro 9.6 is stated for every base
block and every pair of covering blocks; no chosen common block is given.
BS Remark 4.2 only says that the induced covering-weight block covers the
base weight's actual block. Their equality is derived below. -/
structure BlockCoveringLaws (A : DGNSourceSemantics (K := K) C S) where
  commonRoots : RootCompatibleAlong iotaT iotaX (pspEmbedding C)
  baseSupport : Source iotaX OX.operations
  coverSupport : Source iotaT OT.operations
  baseReductions : ∀ W : BaseWeight (n := n) (F := F) (K := K), Nonempty (CompatibleReduction iotaX W)
  coverReductions : ∀ V : CoverWeight (n := n) (F := F) (K := K), Nonempty (CompatibleReduction iotaT V)
  brauer_covering : ∀ (phi : IBr iotaX) (Phi : IBr iotaT),
    CharacterCovers C iotaX iotaT phi Phi →
      BlocksCover C OX OT (baseBrauerBlock iotaX OX injX phi) (coverBrauerBlock iotaT OT injT Phi)
  weight_covering : ∀ (w : BaseWeightClass (n := n) (F := F) (K := K))
    (v : CoverWeightClass (n := n) (F := F) (K := K)), WeightCovers C S A w v →
      BlocksCover C OX OT (OX.weightBlock w) (OT.weightBlock v)
  navarro96 : ∀ (b : BlockX) (B B' : BlockT),
    BlocksCover C OX OT b B → BlocksCover C OX OT b B' → B = B'

namespace BlockCoveringLaws

variable {C S iotaX iotaT OX OT injX injT} {A : DGNSourceSemantics (K := K) C S}
variable (B : BlockCoveringLaws C S iotaX iotaT OX OT injX injT A)

include B

/-- Common ambient block from the two independent covering laws and the
already known SAME base block. This is valid for any base block. -/
theorem common_block {phi : IBr iotaX} {Phi : IBr iotaT}
    {w : BaseWeightClass (n := n) (F := F) (K := K)}
    {v : CoverWeightClass (n := n) (F := F) (K := K)}
    (hPhi : CharacterCovers C iotaX iotaT phi Phi) (hv : WeightCovers C S A w v)
    (hsame : baseBrauerBlock iotaX OX injX phi = OX.weightBlock w) :
    coverBrauerBlock iotaT OT injT Phi = OT.weightBlock v := by
  apply B.navarro96 (OX.weightBlock w)
  · simpa only [hsame] using B.brauer_covering phi Phi hPhi
  · exact B.weight_covering w v hv

/-- Principal specialization: principality is the actual block of the
constant-one character, and only the BASE pair is known to lie there. -/
theorem common_principal_covering_block
    (oneX : IBr iotaX) (oneT : IBr iotaT)
    (oneX_value : ∀ x, oneX.1 x = 1) (oneT_value : ∀ x, oneT.1 x = 1)
    {phi : IBr iotaX} {Phi : IBr iotaT}
    {w : BaseWeightClass (n := n) (F := F) (K := K)}
    {v : CoverWeightClass (n := n) (F := F) (K := K)}
    (hPhi : CharacterCovers C iotaX iotaT phi Phi) (hv : WeightCovers C S A w v)
    (hphi : baseBrauerBlock iotaX OX injX phi = baseBrauerBlock iotaX OX injX oneX)
    (hw : OX.weightBlock w = baseBrauerBlock iotaX OX injX oneX) :
    coverBrauerBlock iotaT OT injT Phi = coverBrauerBlock iotaT OT injT oneT ∧
      OT.weightBlock v = coverBrauerBlock iotaT OT injT oneT := by
  have hone := B.brauer_covering oneX oneT
    (constantOne_covers C iotaX iotaT oneX oneT oneX_value oneT_value)
  have hPhiOne : coverBrauerBlock iotaT OT injT Phi = coverBrauerBlock iotaT OT injT oneT := by
    apply B.navarro96 (baseBrauerBlock iotaX OX injX oneX)
    · simpa only [hphi] using B.brauer_covering phi Phi hPhi
    · exact hone
  exact ⟨hPhiOne, (B.common_block hPhi hv (hphi.trans hw.symm)).symm.trans hPhiOne⟩

end BlockCoveringLaws

end ActualBlocks

end ModularRep.PaperProofs.OddTwoBroughCoveringSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
