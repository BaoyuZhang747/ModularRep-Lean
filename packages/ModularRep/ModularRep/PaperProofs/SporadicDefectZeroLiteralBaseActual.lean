import Formalisation.SporadicPrimeArithmetic
import ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# Literal defect-zero characters and weights at the trivial subgroup

This module contains only the literal carriers and narrowly stated source
interfaces needed for defect-zero reductions and weights at the trivial
radical subgroup.  It precedes every numerical character--weight construction
and contains no global or block-fibre equivalence.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual

open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero

universe u

variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

/-- Literal blocks of the modular group algebra. -/
abbrev ActualBlock :=
  ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual.ActualBlock
    (k := k) (X := X)

/-- Literal conjugacy classes of character weights. -/
abbrev WeightClass :=
  CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X)

/-- Literal conjugacy classes of radical subgroups. -/
abbrev RadicalClass :=
  CharacterWeight.RadicalConjugacyClass (p := p) (G := X)

/-- Function-valued ordinary irreducible characters of defect zero. -/
abbrev GlobalDefectZeroCharacter :=
  {chi : OrdinaryIrreducibleCharacter.Irr K X //
    IsDefectZeroOrdinaryCharacter p chi}

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

/-- The literal primitive block containing an irreducible Brauer character. -/
def brauerBlock (phi : IBr iota) : ActualBlock (k := k) (X := X) :=
  ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual.brauerBlock
    iota hinj blocks phi

/-- The shared coherent source for local block formation, inflation, and
induction on the literal set of weights. -/
abbrev LiteralBlockSource :=
  ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual.LiteralCarrierAdapter
    (p := p) (k := k) (K := K) (X := X)

/-! ## The canonical defect-zero reduction -/

/-- Exact source facts identifying the Brauer reduction of a defect-zero
ordinary character.  There is deliberately no function field choosing
reductions. -/
structure DefectZeroReductionSource : Prop where
  existsUniqueReduction : ∀ d :
      GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
    ∃! phi : IBr iota,
      SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
        iota d.1 phi
  regularRestriction_injective :
    ∀ d d' : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      (∀ g : PrimeRegularElement (G := X) p, d.1 g.1 = d'.1 g.1) → d = d'

namespace DefectZeroReductionSource

/-- Navarro's defect-zero reduction facts suffice to construct the exact
reduction source.  Uniqueness follows because Brauer characters are stored
as their prime regular class functions, while injectivity follows by combining
equality on prime regular elements with vanishing elsewhere. -/
theorem ofExistsReduction_of_vanishesOnPrimeSingular
    (hred : ∀ d :
      GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      ∃ phi : IBr iota,
        SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
          iota d.1 phi)
    (hvan : ∀
      (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
      (x : X),
      ¬ IsPrimeRegular p x → d.1 x = 0) :
    DefectZeroReductionSource (p := p) (K := K) (X := X) iota := by
  refine
    { existsUniqueReduction := ?_
      regularRestriction_injective := ?_ }
  · intro d
    obtain ⟨phi, hphi⟩ := hred d
    refine ⟨phi, hphi, ?_⟩
    intro psi hpsi
    apply Subtype.ext
    apply PrimeRegularClassFunction.ext
    intro g
    exact (hpsi g).symm.trans (hphi g)
  · intro d d' hregular
    apply Subtype.ext
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    by_cases hx : IsPrimeRegular p x
    · exact hregular ⟨x, hx⟩
    · exact (hvan d x hx).trans (hvan d' x hx).symm

variable (D : DefectZeroReductionSource (p := p) (K := K) (X := X) iota)

/-- The unique function-valued irreducible Brauer reduction. -/
def reduce (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    IBr iota :=
  Classical.choose (D.existsUniqueReduction d)

/-- The selected Brauer character is literally the restriction of the
ordinary character to prime regular elements. -/
theorem reduce_isReduction
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      iota d.1 (D.reduce (iota := iota) d) :=
  (Classical.choose_spec (D.existsUniqueReduction d)).1

/-- Distinct defect-zero ordinary characters have distinct canonical
reductions. -/
theorem reduce_injective : Function.Injective (D.reduce (iota := iota)) := by
  intro d d' h
  apply D.regularRestriction_injective d d'
  intro g
  calc
    d.1 g.1 = (D.reduce (iota := iota) d).1 g :=
      D.reduce_isReduction (iota := iota) d g
    _ = (D.reduce (iota := iota) d').1 g := by rw [h]
    _ = d'.1 g.1 := (D.reduce_isReduction (iota := iota) d' g).symm

end DefectZeroReductionSource

/-! ## The literal weight at the trivial radical subgroup -/

/-- The canonical class of `x` in the local quotient at the trivial
subgroup. -/
def trivialNormalizerQuotientMk (x : X) :
    NormalizerQuotient (⊥ : Subgroup X) :=
  QuotientGroup.mk
    (⟨x, by
      simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]⟩ :
      Subgroup.normalizer ((⊥ : Subgroup X) : Set X))

/-- The normaliser of the trivial subgroup, identified with the ambient
group. -/
def trivialNormalizerEquiv :
    Subgroup.normalizer ((⊥ : Subgroup X) : Set X) ≃* X :=
  (MulEquiv.subgroupCongr
    (Subgroup.normalizer_eq_top (H := (⊥ : Subgroup X)))).trans
      Subgroup.topEquiv

/-- The canonical equivalence `N_X(1)/1 ≃ X`. -/
def trivialNormalizerQuotientEquiv :
    NormalizerQuotient (⊥ : Subgroup X) ≃* X :=
  ((QuotientGroup.quotientMulEquivOfEq
      (Subgroup.bot_subgroupOf
        (H := Subgroup.normalizer ((⊥ : Subgroup X) : Set X)))).trans
    QuotientGroup.quotientBot).trans trivialNormalizerEquiv

omit [Fintype X] in
/-- The canonical quotient equivalence sends the class of `x` to `x`. -/
@[simp]
theorem trivialNormalizerQuotientEquiv_mk (x : X) :
    trivialNormalizerQuotientEquiv (trivialNormalizerQuotientMk x) = x :=
  rfl

omit [Fintype X] in
/-- The inverse canonical quotient equivalence sends `x` to its quotient
class. -/
@[simp]
theorem trivialNormalizerQuotientEquiv_symm_apply (x : X) :
    trivialNormalizerQuotientEquiv.symm x =
      trivialNormalizerQuotientMk x := by
  apply trivialNormalizerQuotientEquiv.injective
  exact (trivialNormalizerQuotientEquiv.apply_symm_apply x).trans
    (trivialNormalizerQuotientEquiv_mk x).symm

/-- The remaining source data needed to construct the literal weight at the
trivial radical subgroup. -/
structure TrivialWeightSource where
  prime : p.Prime
  trivialRadical : IsRadicalSubgroup p (⊥ : Subgroup X)

namespace TrivialWeightSource

/-- Package the kernel deduction that the trivial subgroup of a simple
non-`p`-group is `p`-radical.  This constructor does not identify the group
carrier with any concrete finite group. -/
theorem ofSimpleNonPGroup [IsSimpleGroup X]
    (hp : p.Prime) (hX : ¬ IsPGroup p X) :
    TrivialWeightSource (p := p) (X := X) where
  prime := hp
  trivialRadical :=
    bot_isRadicalSubgroup_of_isSimpleGroup_of_not_isPGroup hX

/-- At `p = 3`, divisibility of the group order by `5` supplies the required
non-`3`-group hypothesis.  The concrete order and carrier identification
remain external inputs. -/
theorem atThreeOfFiveDvdCard [IsSimpleGroup X]
    (h5 : 5 ∣ Nat.card X) :
    TrivialWeightSource (p := 3) (X := X) :=
  ofSimpleNonPGroup Nat.prime_three
    (not_isPGroup_of_prime_dvd_card
      (G := X) Nat.prime_three Nat.prime_five (by decide) h5)

/-- Kernel arithmetic adapter for the intended simple Fischer carrier at
coefficient prime three. It neither identifies `X` with `Fi'₂₄` nor applies
to the central triple cover. -/
theorem atThreeOfCardEqFi24Order [IsSimpleGroup X]
    (hcard : Nat.card X =
      Formalisation.SporadicPrimeArithmetic.fi24Order) :
    TrivialWeightSource (p := 3) (X := X) := by
  refine atThreeOfFiveDvdCard (X := X) ?_
  rw [hcard]
  exact
    (Formalisation.SporadicPrimeArithmetic.prime_dvd_fi24Order_iff
      Nat.prime_five).2 (by decide)

variable (T : TrivialWeightSource (p := p) (X := X))

/-- The raw literal weight `(1, chi)` attached to a defect-zero character. -/
def rawAtOne
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    CharacterWeight p K X where
  prime := T.prime
  subgroup := ⊥
  radical := T.trivialRadical
  localCharacter := OrdinaryIrreducibleCharacter.mapEquiv d.1
    trivialNormalizerQuotientEquiv.symm
  defectZero := d.2.mapEquiv trivialNormalizerQuotientEquiv.symm

/-- On the canonical quotient class of `x`, the local character of the
constructed weight is the original defect-zero character evaluated at
`x`. -/
@[simp]
theorem rawAtOne_localCharacter_mk
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
    (x : X) :
    (T.rawAtOne d).localCharacter (trivialNormalizerQuotientMk x) = d.1 x := by
  change d.1
    (trivialNormalizerQuotientEquiv (trivialNormalizerQuotientMk x)) = d.1 x
  exact congrArg (fun y : X => d.1 y) (trivialNormalizerQuotientEquiv_mk x)

/-- The literal conjugacy class of `(1, chi)`. -/
def atOne
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    WeightClass (p := p) (K := K) (X := X) :=
  Quotient.mk'' (Quotient.mk'' (T.rawAtOne d))

/-- The radical of the constructed weight is the literal class of the
trivial subgroup. -/
@[simp]
theorem radicalClass_atOne
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    CharacterWeight.radicalClass (T.atOne d) =
      RadicalConjugacyClass.trivialClass T.trivialRadical :=
  rfl

/-- Every literal character weight whose radical class is the trivial class
comes from a defect-zero ordinary character through the canonical
identification `N_X(1)/1 ≃ X`. -/
theorem exists_atOne_of_radicalClass_eq_trivial
    (w : WeightClass (p := p) (K := K) (X := X))
    (hw : CharacterWeight.radicalClass w =
      RadicalConjugacyClass.trivialClass T.trivialRadical) :
    ∃ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      T.atOne d = w := by
  revert hw
  refine Quotient.inductionOn w ?_
  intro w hw
  revert hw
  refine Quotient.inductionOn w ?_
  intro W hw
  change
    (Quotient.mk''
      (⟨W.subgroup, W.radical⟩ :
        CharacterWeight.RadicalSubgroup (p := p) (G := X)) :
      CharacterWeight.RadicalConjugacyClass (p := p) (G := X)) =
      Quotient.mk''
        (⟨⊥, T.trivialRadical⟩ :
          CharacterWeight.RadicalSubgroup (p := p) (G := X)) at hw
  obtain ⟨g, hg⟩ := Quotient.exact hw
  have hbot :
      g • (⟨⊥, T.trivialRadical⟩ :
          CharacterWeight.RadicalSubgroup (p := p) (G := X)) =
        (⟨⊥, T.trivialRadical⟩ :
          CharacterWeight.RadicalSubgroup (p := p) (G := X)) := by
    apply Subtype.ext
    ext x
    simp only [CharacterWeight.RadicalSubgroup.smul_eq_rightTwist_conj,
      map_inv, Subgroup.mem_bot]
    constructor
    · intro hx
      change g⁻¹ * x * g = 1 at hx
      calc
        x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [hx]; simp
    · intro hx
      subst x
      change g⁻¹ * 1 * g = 1
      simp
  have hQ : W.subgroup = (⊥ : Subgroup X) :=
    (congrArg Subtype.val (hbot.symm.trans hg)).symm
  rcases W with ⟨hprime, Q, hradical, chi, hdefect⟩
  change Q = ⊥ at hQ
  subst Q
  let e : NormalizerQuotient (⊥ : Subgroup X) ≃* X :=
    trivialNormalizerQuotientEquiv
  let d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X) :=
    ⟨OrdinaryIrreducibleCharacter.mapEquiv chi e, hdefect.mapEquiv e⟩
  refine ⟨d, ?_⟩
  change
    Quotient.mk'' (Quotient.mk'' (T.rawAtOne d)) =
      Quotient.mk''
        (Quotient.mk''
          ({ prime := hprime
             subgroup := ⊥
             radical := hradical
             localCharacter := chi
             defectZero := hdefect } : CharacterWeight p K X))
  apply congrArg Quotient.mk''
  apply Quotient.sound
  refine ⟨rfl, ?_⟩
  change OrdinaryIrreducibleCharacter.mapEquiv
      (OrdinaryIrreducibleCharacter.mapEquiv chi e) e.symm = chi
  rw [OrdinaryIrreducibleCharacter.mapEquiv_trans,
    MulEquiv.self_trans_symm,
    OrdinaryIrreducibleCharacter.mapEquiv_refl]

end TrivialWeightSource

/-- Injectivity of the literal construction `T.atOne`. -/
structure TrivialWeightIdentification
    (T : TrivialWeightSource (p := p) (X := X)) : Prop where
  injective : Function.Injective
    (T.atOne : GlobalDefectZeroCharacter (p := p) (K := K) (X := X) →
      WeightClass (p := p) (K := K) (X := X))

/-! ## Literal block compatibility -/

variable (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
variable (D : DefectZeroReductionSource (p := p) (K := K) (X := X) iota)
variable (T : TrivialWeightSource (p := p) (X := X))

/-- The block induced from `(1, chi)` is the block containing the canonical
Brauer reduction of `chi`. -/
structure TrivialWeightBlockCompatibility : Prop where
  block_atOne : ∀ d :
      GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
    R.1.weightBlock (T.atOne d) =
      brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks)
        (D.reduce (iota := iota) d)

end ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
