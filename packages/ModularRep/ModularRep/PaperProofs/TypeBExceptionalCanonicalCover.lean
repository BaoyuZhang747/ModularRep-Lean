import ModularRep.PaperProofs.TypeBExceptionalOddPrimeOrder
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Index

/-!
# The canonical exceptional cover of the actual Spin-centre quotient

For a group S, take the free group on its underlying set, with its literal
evaluation map and relation kernel R. The carrier used here is
[FreeGroup S, FreeGroup S] / [R, FreeGroup S]. Its projection to S is
constructed before the source statements are introduced.

The generic E1 input is Weibel, An Introduction to Homological Algebra,
Construction 6.9.3, Lemma 6.9.4, Theorem 6.9.5 and Lemma 6.9.6,
pp. 199--201. It concerns this exact free presentation for every perfect S.
The exceptional E1 input uses Malle--Testerman, Table 24.1 p. 208,
Theorem 24.17 p. 213 and Remark 24.19/Table 24.3 p. 214: the SAME
Omega N is simple of order 2^9 * 3^9 * 5 * 7 * 13, and its multiplier is C6.
The kernel identification uses the Hopf formula in Weibel 6.8.8/6.9.3.
FLZ, proof of Theorem 1, p. 574, independently records the full cover order.

No arbitrary total group, covering map, block condition, character or
weight correspondence is an input. The generic full-cover theorem and
the exceptional facts are source statements, with no inhabitant declared.
The field and norm remain those of the caller; no transport to a separately
chosen field with three elements is required.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBExceptionalCanonicalCover

open TypeBCliffordCarriers TypeBSpinCoverSource
open EvenFieldFLZSourceConditions EvenFieldFLZ318FixedTheoremGate
open scoped commutatorElement

section FreePresentation

variable (S : Type) [Group S]

/-- Evaluation of words in the elements of the actual quotient group. -/
def freeEvaluation : FreeGroup S →* S := FreeGroup.prod

@[simp] theorem freeEvaluation_of (s : S) :
    freeEvaluation S (FreeGroup.of s) = s := by
  exact FreeGroup.prod.of

theorem freeEvaluation_surjective : Function.Surjective (freeEvaluation S) :=
  FreeGroup.prod_surjective

def relations : Subgroup (FreeGroup S) := (freeEvaluation S).ker

def derived : Subgroup (FreeGroup S) := commutator (FreeGroup S)

/-- The denominator is the relative commutator, formed in the free group. -/
def relativeCommutator : Subgroup (FreeGroup S) :=
  ⁅relations S, (⊤ : Subgroup (FreeGroup S))⁆

instance relations_normal : (relations S).Normal :=
  inferInstanceAs (freeEvaluation S).ker.Normal

instance relativeCommutator_normal : (relativeCommutator S).Normal := by
  unfold relativeCommutator
  infer_instance

theorem relativeCommutator_le_relations :
    relativeCommutator S ≤ relations S :=
  Subgroup.commutator_le_left _ _

theorem relativeCommutator_le_derived :
    relativeCommutator S ≤ derived S :=
  Subgroup.commutator_mono le_top le_rfl

/-- Pull the denominator back to the actual derived-subgroup carrier. -/
def coverRelations : Subgroup (derived S) :=
  (relativeCommutator S).comap (derived S).subtype

instance coverRelations_normal : (coverRelations S).Normal := by
  unfold coverRelations
  infer_instance

/-- A fixed group expression, independent of every external source. -/
abbrev Cover := derived S ⧸ coverRelations S

def derivedEvaluation : derived S →* S :=
  (freeEvaluation S).comp (derived S).subtype

theorem coverRelations_le_kernel :
    coverRelations S ≤ (derivedEvaluation S).ker := by
  intro x hx
  exact relativeCommutator_le_relations S hx

/-- The canonical projection is induced by evaluation, not supplied. -/
def projection : Cover S →* S :=
  QuotientGroup.lift (coverRelations S) (derivedEvaluation S)
    (coverRelations_le_kernel S)

@[simp] theorem projection_mk (x : derived S) :
    projection S (QuotientGroup.mk' (coverRelations S) x) =
      freeEvaluation S x := rfl

end FreePresentation

/-- The general free-presentation theorem, on the literal construction.
This is ordinary group theory and has no Type B or coefficient premise. -/
structure FreePresentationCoverSource : Prop where
  applies : ∀ (S : Type) [Group S], commutator S = ⊤ →
    commutator (Cover S) = ⊤ ∧
      IsUniversalCentralExtension (projection S)

section Elementary

theorem perfect_of_nonabelian_simple {S : Type} [Group S]
    (hsimple : IsSimpleGroup S) (hnonabelian : ¬ IsMulCommutative S) :
    commutator S = ⊤ := by
  letI : IsSimpleGroup S := hsimple
  have hnormal : (commutator S).Normal := inferInstance
  exact hnormal.eq_bot_or_eq_top.resolve_left
    (fun h => hnonabelian ((commutator_eq_bot_iff _).mp h))

theorem center_eq_bot_of_nonabelian_simple {S : Type} [Group S]
    (hsimple : IsSimpleGroup S) (hnonabelian : ¬ IsMulCommutative S) :
    Subgroup.center S = ⊥ := by
  letI : IsSimpleGroup S := hsimple
  have hnormal : (Subgroup.center S).Normal := inferInstance
  exact hnormal.eq_bot_or_eq_top.resolve_right
    (fun h => hnonabelian (Subgroup.center_eq_top_iff.mp h))

/-- A map over a central extension onto a perfect total group is surjective.
The source projection is already surjective; no surjectivity of the lift
is requested as an external fact. -/
theorem lift_surjective_of_perfect
    {U S D : Type} [Group U] [Group S] [Group D]
    (q : U →* S) (hq : Function.Surjective q)
    (r : D →* S) (hcentral : r.ker ≤ Subgroup.center D)
    (hperfect : commutator D = ⊤)
    (lift : U →* D) (hlift : r.comp lift = q) :
    Function.Surjective lift := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← hperfect, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨a, ha⟩ := hq (r x)
  obtain ⟨b, hb⟩ := hq (r y)
  have hxa : r (lift a) = r x := (DFunLike.congr_fun hlift a).trans ha
  have hyb : r (lift b) = r y := (DFunLike.congr_fun hlift b).trans hb
  have hx : (lift a)⁻¹ * x ∈ Subgroup.center D := hcentral (by
    change r ((lift a)⁻¹ * x) = 1
    rw [map_mul, map_inv, hxa, inv_mul_cancel])
  have hy : (lift b)⁻¹ * y ∈ Subgroup.center D := hcentral (by
    change r ((lift b)⁻¹ * y) = 1
    rw [map_mul, map_inv, hyb, inv_mul_cancel])
  have hxcomm : Commute ((lift a)⁻¹ * x) y :=
    (Subgroup.mem_center_iff.mp hx y).symm
  have hycomm : Commute (lift a) ((lift b)⁻¹ * y) :=
    Subgroup.mem_center_iff.mp hy (lift a)
  refine ⟨⁅a, b⁆, ?_⟩
  rw [map_commutatorElement]
  symm
  calc
    ⁅x, y⁆ = ⁅lift a * ((lift a)⁻¹ * x), y⁆ := by rw [mul_inv_cancel_left]
    _ = ⁅lift a, y⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hxcomm.commutator_eq]
      simp
    _ = ⁅lift a, lift b * ((lift b)⁻¹ * y)⁆ := by rw [mul_inv_cancel_left]
    _ = ⁅lift a, lift b⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hycomm.commutator_eq]
      simp

end Elementary

/-- Published facts for the exceptional simple quotient. The last field is
the multiplier of that SAME quotient, expressed as the actual kernel of
its free-presentation cover. No total-group carrier is supplied here. -/
structure ExceptionalOmegaSource
    {n p f : ℕ} {F : Type} [Field F] [finiteField : Finite F] [CharP F p]
    (N : NormSource n F) (parameters : OddFieldParameters F p f)
    (exceptional : (n, Nat.card F) = (3, 3)) : Prop where
  simple : IsSimpleGroup (Omega N)
  nonabelian : ¬ IsMulCommutative (Omega N)
  order : Nat.card (Omega N) = 2 ^ 9 * 3 ^ 9 * 5 * 7 * 13
  multiplier : Nonempty ((projection (Omega N)).ker ≃* Multiplicative (ZMod 6))

section Exceptional

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
variable (N : NormSource n F) (parameters : OddFieldParameters F p f)
variable (exceptional : (n, Nat.card F) = (3, 3))
variable (source : ExceptionalOmegaSource N parameters exceptional)

abbrev ExceptionalCover := Cover (Omega N)

abbrev exceptionalProjection : ExceptionalCover N →* Omega N := projection (Omega N)

include parameters exceptional source

theorem omega_finite : Finite (Omega N) :=
  Nat.finite_of_card_ne_zero (by rw [source.order]; decide)

def omegaFintype : Fintype (Omega N) := @Fintype.ofFinite _ (omega_finite N parameters exceptional source)

theorem kernel_card : Nat.card (exceptionalProjection N).ker = 6 := by
  obtain ⟨e⟩ := source.multiplier
  rw [Nat.card_congr e.toEquiv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem cover_finite : Finite (ExceptionalCover N) := by
  letI : Finite (Omega N) := omega_finite N parameters exceptional source
  letI : Finite (exceptionalProjection N).ker :=
    Nat.finite_of_card_ne_zero (by rw [kernel_card N parameters exceptional source]; decide)
  exact (MonoidHom.finite_iff_finite_ker_range (exceptionalProjection N)).mpr
    ⟨inferInstance, inferInstance⟩

def coverFintype : Fintype (ExceptionalCover N) :=
  @Fintype.ofFinite _ (cover_finite N parameters exceptional source)

variable (freeSource : FreePresentationCoverSource)

include freeSource

theorem cover_perfect : commutator (ExceptionalCover N) = ⊤ :=
  (freeSource.applies (Omega N)
    (perfect_of_nonabelian_simple source.simple source.nonabelian)).1

theorem projection_universal : IsUniversalCentralExtension (exceptionalProjection N) :=
  (freeSource.applies (Omega N)
    (perfect_of_nonabelian_simple source.simple source.nonabelian)).2

theorem projection_surjective : Function.Surjective (exceptionalProjection N) :=
  (projection_universal N parameters exceptional source freeSource).1.1

theorem projection_kernel_eq_center :
    (exceptionalProjection N).ker = Subgroup.center (ExceptionalCover N) := by
  have hu := projection_universal N parameters exceptional source freeSource
  apply le_antisymm hu.1.2
  intro x hx
  have himage : exceptionalProjection N x ∈ Subgroup.center (Omega N) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := hu.1.1 y
    simpa only [map_mul] using
      congrArg (exceptionalProjection N) (Subgroup.mem_center_iff.mp hx z)
  rw [center_eq_bot_of_nonabelian_simple source.simple source.nonabelian] at himage
  exact himage

theorem cover_order :
    Nat.card (ExceptionalCover N) = TypeBExceptionalOddPrimeOrder.fullCoverOrder := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (exceptionalProjection N).ker]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (exceptionalProjection N) (projection_surjective N parameters exceptional source freeSource)).toEquiv]
  rw [source.order, kernel_card N parameters exceptional source]
  norm_num [TypeBExceptionalOddPrimeOrder.fullCoverOrder]

/-- The full C6 cover is the maximal perfect prime-to-ell cover whenever
ell is odd and nondefining in this exceptional field of order three. -/
def ellPrimeCover {ell : ℕ} (prime : ell.Prime) (odd : Odd ell) (nondefining : ell ≠ 3) :
    @EllPrimeCoverSource ell (ExceptionalCover N) inferInstance
      (coverFintype N parameters exceptional source) := by
  letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional source
  exact {
  S := Omega N
  groupS := inferInstance
  fintypeS := omegaFintype N parameters exceptional source
  quotient := exceptionalProjection N
  quotient_surjective := projection_surjective N parameters exceptional source freeSource
  quotient_kernel := projection_kernel_eq_center N parameters exceptional source freeSource
  perfect := cover_perfect N parameters exceptional source freeSource
  simple := source.simple
  nonabelian := source.nonabelian
  centerPrimeTo := by
    rw [← projection_kernel_eq_center N parameters exceptional source freeSource,
      kernel_card N parameters exceptional source]
    intro h
    have h23 : ell ∣ 2 * 3 := h
    rcases prime.dvd_mul.mp h23 with h2 | h3
    · exact (prime.coprime_iff_not_dvd.mp odd.coprime_two_right) h2
    · exact nondefining ((Nat.prime_dvd_prime_iff_eq prime (by decide)).mp h3)
  maximal := by
    intro D _ _ r hr hcentral hperfect _
    have hu := projection_universal N parameters exceptional source freeSource
    obtain ⟨lift, hlift, _⟩ := hu.2 D r ⟨hr, hcentral⟩
    exact ⟨lift, lift_surjective_of_perfect (exceptionalProjection N) hu.1.1
      r hcentral hperfect lift hlift, hlift⟩ }

@[simp] theorem ellPrimeCover_simpleGroup {ell : ℕ}
    (prime : ell.Prime) (odd : Odd ell) (nondefining : ell ≠ 3) :
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional source
    (ellPrimeCover N parameters exceptional source freeSource prime odd nondefining).S =
      Omega N := rfl

@[simp] theorem ellPrimeCover_projection {ell : ℕ}
    (prime : ell.Prime) (odd : Odd ell) (nondefining : ell ≠ 3) :
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional source
    (ellPrimeCover N parameters exceptional source freeSource prime odd nondefining).quotient =
      exceptionalProjection N := rfl

end Exceptional

end ModularRep.PaperProofs.TypeBExceptionalCanonicalCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
