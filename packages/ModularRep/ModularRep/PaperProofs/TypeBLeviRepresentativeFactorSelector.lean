import ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter
import ModularRep.PaperProofs.TypeBComponentReturnCarrierTransport

/-!
# A standard factor selector on the actual Levi diagonal image

The actual factor H and standard factor S are identified by a group
equivalence e. Both diagonal actions factor through the SAME adjoint group J,
and both projections onto J are surjective. Only these lower group maps and
literal value squares are inputs: full diagonal-image and character-orbit
equality are deductions below.

The sole selector source concerns the standard group S, its actual regular
diagonal action, and the specified standard return homomorphism from the
original cyclic group R. Its type-A/B2 applicability is an E2/U obligation.
The target root embedding on S is constructed from the root on H. The two
returns are compared on their chosen generator at group level, up to an
explicit inner automorphism. The existing cyclic inner-difference deduction
then compares their actions on every character for every element of SAME R.

The result selects a representative in the prescribed orbit of the literal
image Delta = actualDiagonal.range and proves its actual product stabilizer
factorization. No actual-factor selector, orbit equality, stabilizer conclusion
for H, or effective quotient of the return group is supplied as a source.
The existing component-return compatibility converts the product conclusion
to its semidirect form in the final consumer.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeFactorSelector

open EvenFieldAssumption53Relative TypeBRegularLeviCharacterActionAdapter
open TypeBComponentReturnCarrierTransport
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

universe u

variable {H S M Q J R k K : Type u}
variable [Group H] [Group S] [Group M] [Group Q] [Group J] [Group R]

/-- The two actual projections onto one adjoint group, with their literal
conjugation squares. Both surjectivity assertions concern group points. -/
structure CommonAdjointData (e : H ≃* S)
    (actualDiagonal : M →* MulAut H) (standardDiagonal : Q →* MulAut S) where
  actualProjection : M →* J
  standardProjection : Q →* J
  adjointAction : J →* MulAut S
  actual_surjective : Function.Surjective actualProjection
  standard_surjective : Function.Surjective standardProjection
  actual_value : ∀ (m : M) (h : H),
    e (actualDiagonal m h) = adjointAction (actualProjection m) (e h)
  standard_value : ∀ (q : Q) (s : S),
    standardDiagonal q s = adjointAction (standardProjection q) s

variable {e : H ≃* S}
variable {actualDiagonal : M →* MulAut H} {standardDiagonal : Q →* MulAut S}

namespace CommonAdjointData

variable (data : CommonAdjointData (J := J) e actualDiagonal standardDiagonal)

include data

theorem actual_square (m : M) :
    MulAut.congr e (actualDiagonal m) = data.adjointAction (data.actualProjection m) := by
  ext s
  change e (actualDiagonal m (e.symm s)) = data.adjointAction (data.actualProjection m) s
  simpa only [e.apply_symm_apply] using data.actual_value m (e.symm s)

theorem standard_square (q : Q) :
    standardDiagonal q = data.adjointAction (data.standardProjection q) := by
  ext s
  exact data.standard_value q s

theorem standard_lift (m : M) :
    ∃ q : Q, MulAut.congr e (actualDiagonal m) = standardDiagonal q := by
  obtain ⟨q, hq⟩ := data.standard_surjective (data.actualProjection m)
  refine ⟨q, ?_⟩
  rw [data.actual_square, data.standard_square, hq]

theorem actual_lift (q : Q) :
    ∃ m : M, MulAut.congr e (actualDiagonal m) = standardDiagonal q := by
  obtain ⟨m, hm⟩ := data.actual_surjective (data.standardProjection q)
  refine ⟨m, ?_⟩
  rw [data.actual_square, data.standard_square, hm]

/-- The full diagonal images agree after the actual group identification. -/
theorem full_diagonal_image :
    actualDiagonal.range.map (MulAut.congr e).toMonoidHom = standardDiagonal.range := by
  ext alpha
  constructor
  · rintro ⟨beta, ⟨m, rfl⟩, rfl⟩
    obtain ⟨q, hq⟩ := data.standard_lift m
    exact ⟨q, hq.symm⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨m, hm⟩ := data.actual_lift q
    exact ⟨actualDiagonal m, ⟨m, rfl⟩, hm⟩

/-- This identification is induced by e, not by a free equivalence of images. -/
def diagonalImageEquiv : actualDiagonal.range ≃* standardDiagonal.range :=
  ((MulAut.congr e).subgroupMap actualDiagonal.range).trans
    (MulEquiv.subgroupCongr data.full_diagonal_image)

theorem standard_image_lift (d : actualDiagonal.range) :
    ∃ q : Q, MulAut.congr e (d : MulAut H) = standardDiagonal q := by
  obtain ⟨m, hm⟩ := d.property
  obtain ⟨q, hq⟩ := data.standard_lift m
  exact ⟨q, by simpa only [hm] using hq⟩

theorem actual_image_lift (q : Q) :
    ∃ d : actualDiagonal.range, MulAut.congr e (d : MulAut H) = standardDiagonal q := by
  obtain ⟨m, hm⟩ := data.actual_lift q
  exact ⟨⟨actualDiagonal m, ⟨m, rfl⟩⟩, hm⟩

end CommonAdjointData

variable [Finite H] [Finite S]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The narrow published selector consequence on the actual standard
factor and specified original return group. Type and field scope remain
part of its E2/U source authentication. -/
def StandardFactorSelector
    (iotaS : PrimeRegularRootEmbedding 2 k K S)
    (standardDiagonal : Q →* MulAut S) (standardReturn : R →* MulAut S) : Prop :=
  letI := rightAutomorphismAction iotaS standardDiagonal
  letI := rightAutomorphismAction iotaS standardReturn
  ∀ base : IBr iotaS, ∃ psi : IBr iotaS,
    psi ∈ MulAction.orbit Q base ∧
      ProductStabilizerFactorization (D := Q) (E := R) psi

/-- Canonical character transport intertwines matching diagonal elements. -/
theorem diagonal_character_transport
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (d : actualDiagonal.range) (q : Q)
    (square : MulAut.congr e (d : MulAut H) = standardDiagonal q)
    (psi : IBr iota) :
    letI := rightAutomorphismAction iota actualDiagonal.range.subtype
    letI := rightAutomorphismAction (iota.alongMulEquiv e) standardDiagonal
    IrreducibleBrauerCharacter.equivAlongMulEquiv iota e (d • psi) =
      q • IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi := by
  change IrreducibleBrauerCharacter.equivAlongMulEquiv iota e
      (IrreducibleBrauerCharacter.twist iota psi (d : MulAut H)⁻¹) =
    IrreducibleBrauerCharacter.twist (iota.alongMulEquiv e)
      (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi) (standardDiagonal q⁻¹)
  rw [IrreducibleBrauerCharacter.equivAlongMulEquiv_twist]
  congr 1
  simpa only [map_inv] using congrArg Inv.inv square

/-- The prescribed actual-image orbit equals the standard diagonal orbit
under the canonical root and character transport. -/
theorem character_orbit_iff
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (data : CommonAdjointData (J := J) e actualDiagonal standardDiagonal)
    (base psi : IBr iota) :
    letI := rightAutomorphismAction iota actualDiagonal.range.subtype
    letI := rightAutomorphismAction (iota.alongMulEquiv e) standardDiagonal
    IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi ∈
        MulAction.orbit Q (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e base) ↔
      psi ∈ MulAction.orbit actualDiagonal.range base := by
  letI := rightAutomorphismAction iota actualDiagonal.range.subtype
  letI := rightAutomorphismAction (iota.alongMulEquiv e) standardDiagonal
  let beta := IrreducibleBrauerCharacter.equivAlongMulEquiv iota e
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨d, hd⟩ := data.actual_image_lift q
    refine ⟨d, beta.injective ?_⟩
    exact (diagonal_character_transport iota d q hd base).trans hq
  · rintro ⟨d, hd⟩
    obtain ⟨q, hq⟩ := data.standard_image_lift d
    refine ⟨q, ?_⟩
    exact (diagonal_character_transport iota d q hq base).symm.trans (congrArg beta hd)

/-- A single generator comparison, up to inner automorphism after e,
intertwines the actions of every element of the original return group. -/
theorem return_character_transport
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (actualReturn : R →* MulAut H) (standardReturn : R →* MulAut S)
    (generator : R) (generator_top : Subgroup.zpowers generator = ⊤)
    (generator_difference : ∃ s : S,
      MulAut.congr e (actualReturn generator) = MulAut.conj s * standardReturn generator)
    (r : R) (psi : IBr iota) :
    letI := rightAutomorphismAction iota actualReturn
    letI := rightAutomorphismAction (iota.alongMulEquiv e) standardReturn
    IrreducibleBrauerCharacter.equivAlongMulEquiv iota e (r • psi) =
      r • IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi := by
  have difference := innerDifference_of_cyclic_generator
    (transportedAut e actualReturn) standardReturn generator generator_top generator_difference
  obtain ⟨s, hs⟩ := difference r⁻¹
  change IrreducibleBrauerCharacter.equivAlongMulEquiv iota e
      (IrreducibleBrauerCharacter.twist iota psi (actualReturn r⁻¹)) =
    IrreducibleBrauerCharacter.twist (iota.alongMulEquiv e)
      (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi) (standardReturn r⁻¹)
  rw [IrreducibleBrauerCharacter.equivAlongMulEquiv_twist]
  exact brauerTwist_eq_of_eq_inner_mul (iota.alongMulEquiv e)
    (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)
    (MulAut.congr e (actualReturn r⁻¹)) (standardReturn r⁻¹) s hs

/-- Transfer the standard factorization to the literal actual image; the
diagonal element is lifted using the common adjoint projections. -/
theorem product_factorization_transport
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (data : CommonAdjointData (J := J) e actualDiagonal standardDiagonal)
    (actualReturn : R →* MulAut H) (standardReturn : R →* MulAut S)
    (generator : R) (generator_top : Subgroup.zpowers generator = ⊤)
    (generator_difference : ∃ s : S,
      MulAut.congr e (actualReturn generator) = MulAut.conj s * standardReturn generator)
    (psi : IBr iota)
    (standardFactorization :
      letI := rightAutomorphismAction (iota.alongMulEquiv e) standardDiagonal
      letI := rightAutomorphismAction (iota.alongMulEquiv e) standardReturn
      ProductStabilizerFactorization (D := Q) (E := R)
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)) :
    letI := rightAutomorphismAction iota actualDiagonal.range.subtype
    letI := rightAutomorphismAction iota actualReturn
    ProductStabilizerFactorization (D := actualDiagonal.range) (E := R) psi := by
  letI := rightAutomorphismAction iota actualDiagonal.range.subtype
  letI := rightAutomorphismAction iota actualReturn
  letI := rightAutomorphismAction (iota.alongMulEquiv e) standardDiagonal
  letI := rightAutomorphismAction (iota.alongMulEquiv e) standardReturn
  let beta := IrreducibleBrauerCharacter.equivAlongMulEquiv iota e
  intro d r
  obtain ⟨q, hq⟩ := data.standard_image_lift d
  have hdiagonal : ∀ x : IBr iota, beta (d • x) = q • beta x :=
    diagonal_character_transport iota d q hq
  have hreturn : ∀ x : IBr iota, beta (r • x) = r • beta x :=
    return_character_transport iota actualReturn standardReturn generator generator_top
      generator_difference r
  constructor
  · intro hfixed
    have hstandard : q • (r • beta psi) = beta psi := by
      rw [← hreturn, ← hdiagonal, hfixed]
    obtain ⟨hd, hr⟩ := (standardFactorization q r).mp hstandard
    exact ⟨beta.injective ((hdiagonal psi).trans hd),
      beta.injective ((hreturn psi).trans hr)⟩
  · rintro ⟨hd, hr⟩
    rw [hr, hd]

/-- Construct the local selector required by the actual component return
from the standard selector and lower group-point identification alone. -/
theorem actual_factor_selector
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (data : CommonAdjointData (J := J) e actualDiagonal standardDiagonal)
    (actualReturn : R →* MulAut H) (standardReturn : R →* MulAut S)
    (generator : R) (generator_top : Subgroup.zpowers generator = ⊤)
    (generator_difference : ∃ s : S,
      MulAut.congr e (actualReturn generator) = MulAut.conj s * standardReturn generator)
    (selector : StandardFactorSelector (iota.alongMulEquiv e) standardDiagonal standardReturn)
    (base : IBr iota) :
    letI := rightAutomorphismAction iota actualDiagonal.range.subtype
    letI := rightAutomorphismAction iota actualReturn
    ∃ psi : IBr iota, psi ∈ MulAction.orbit actualDiagonal.range base ∧
      ProductStabilizerFactorization (D := actualDiagonal.range) (E := R) psi := by
  letI := rightAutomorphismAction iota actualDiagonal.range.subtype
  letI := rightAutomorphismAction iota actualReturn
  letI := rightAutomorphismAction (iota.alongMulEquiv e) standardDiagonal
  letI := rightAutomorphismAction (iota.alongMulEquiv e) standardReturn
  let beta := IrreducibleBrauerCharacter.equivAlongMulEquiv iota e
  obtain ⟨chi, hchi, hfactor⟩ := selector (beta base)
  refine ⟨beta.symm chi, ?_, ?_⟩
  · apply (character_orbit_iff iota data base (beta.symm chi)).mp
    simpa only [beta, Equiv.apply_symm_apply] using hchi
  · apply product_factorization_transport iota data actualReturn standardReturn
      generator generator_top generator_difference (beta.symm chi)
    simpa only [beta, Equiv.apply_symm_apply] using hfactor

end ModularRep.PaperProofs.TypeBLeviRepresentativeFactorSelector


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
