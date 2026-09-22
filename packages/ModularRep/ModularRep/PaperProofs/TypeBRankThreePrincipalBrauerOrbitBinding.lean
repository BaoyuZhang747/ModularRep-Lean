import ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitBinding
import ModularRep.PaperProofs.TypeBGreenPrincipalConstituentSource

/-!
# Principal Brauer characters and actual SO orbits in rank three

The principal SO character above a supported Omega character is selected
from literal restriction occurrence and Green uniqueness. Its fibres are
the actual SO-conjugacy orbits, using checked restriction naturality and
the narrowly sourced Clifford transitivity of constituents. Factoring this
map through the actual orbit quotient constructs an equivalence.

The source clauses retain the subgroup roots, coefficient field scope and
actual quotient p-group hypothesis. No orbit equivalence, matching map,
numerical count, character triple or goodness conclusion is an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalBrauerOrbitBinding

open ModularRep CharacterWeight
open TypeBCentralKernelCarriers TypeBCentralKernelBlockSource
open TypeBCentralKernelInertia TypeBRankThreePrincipalCountBinding
open TypeBRankThreePrincipalOrbitBinding
open NavarroCoveringBrauerExtension TypeBGreenPrincipalConstituentSource

variable (F : Type) [Field F] [Finite F]

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)

/-- The actual SO action on the supported principal Brauer fibre. -/
def principalBrauerAction : MulAction (H F) (OmegaBrauer F root b) where
  smul := brauerStep F S literal root b hb
  one_smul theta := by
    apply Subtype.ext
    change conjugationOp (G F) 1 • theta.val = theta.val
    rw [map_one, one_smul]
  mul_smul h j theta := by
    apply Subtype.ext
    change conjugationOp (G F) (h * j) • theta.val =
      conjugationOp (G F) h • (conjugationOp (G F) j • theta.val)
    rw [map_mul, mul_smul]

/-- Mathlib's orbit relation for precisely the displayed SO action. -/
def principalBrauerOrbitRel : Setoid (OmegaBrauer F root b) := by
  letI := principalBrauerAction F S literal root b hb
  exact MulAction.orbitRel (H F) (OmegaBrauer F root b)

abbrev PrincipalBrauerOrbit :=
  Quotient (principalBrauerOrbitRel F S literal root b hb)

/-- The conventional orbit relation also has the forward action form used
by the frozen actual-orbit binding. -/
theorem principalBrauerOrbitRel_iff (theta eta : OmegaBrauer F root b) :
    principalBrauerOrbitRel F S literal root b hb theta eta ↔
      ∃ h : H F, brauerStep F S literal root b hb h theta = eta := by
  change (∃ h : H F, brauerStep F S literal root b hb h eta = theta) ↔ _
  constructor
  · rintro ⟨h, heq⟩
    exact ⟨h⁻¹, (congrArg (brauerStep F S literal root b hb h⁻¹) heq).symm.trans
      (brauerStep_inv F S literal root b hb h eta)⟩
  · rintro ⟨h, heq⟩
    exact ⟨h⁻¹, (congrArg (brauerStep F S literal root b hb h⁻¹) heq).symm.trans
      (brauerStep_inv F S literal root b hb h theta)⟩


section PrincipalConstituents

variable (rootH : PrimeRegularRootEmbedding 2 k K (H F))
  (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
  (roots : RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (indexTwo : (G F).index = 2)

variable (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))

/-- The unique SO character above the given actual constituent, placed in
the specified principal block by the separate principal-lifting clause. -/
def principalAbove (theta : OmegaBrauer F root b) : SOBrauer F rootH bH :=
  ⟨above (G F) rootH root roots fieldScope (quotient_isTwoGroup (G F) indexTwo) green theta.val,
    principalLift.lifts_principal bH b hbH hb _ theta.val theta.property
      (above_occurs (G F) rootH root roots fieldScope
        (quotient_isTwoGroup (G F) indexTwo) green theta.val)⟩

local notation "cover" =>
  principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo green principalLift

theorem principalAbove_occurs (theta : OmegaBrauer F root b) :
    BrauerOccursInRestriction (G F) rootH root (cover theta).val theta.val :=
  above_occurs (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo) green theta.val

/-- Literal restriction occurrence determines the selected principal
character; this is a uniqueness deduction, not a supplied map equation. -/
theorem principalAbove_eq (theta : OmegaBrauer F root b) (Phi : SOBrauer F rootH bH)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val) :
    cover theta = Phi :=
  Subtype.ext (above_eq (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo) green theta.val
    Phi.val occurs)

theorem principalAbove_occurs_iff (theta : OmegaBrauer F root b)
    (Phi : SOBrauer F rootH bH) :
    BrauerOccursInRestriction (G F) rootH root Phi.val theta.val ↔ cover theta = Phi := by
  constructor
  · exact principalAbove_eq F root b hb rootH bH hbH roots fieldScope indexTwo
      green principalLift theta Phi
  · intro equal
    rw [← equal]
    exact principalAbove_occurs F root b hb rootH bH hbH roots fieldScope indexTwo
      green principalLift theta

/-- Every actual SO actor preserves the selected overgroup character. -/
theorem principalAbove_step (h : H F) (theta : OmegaBrauer F root b) :
    cover (brauerStep F S literal root b hb h theta) = cover theta :=
  principalAbove_eq F root b hb rootH bH hbH roots fieldScope indexTwo green principalLift
    (brauerStep F S literal root b hb h theta) (cover theta)
    (occurs_brauerStep F S literal root b hb rootH h (cover theta).val theta
      (principalAbove_occurs F root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift theta))

variable (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)

include clifford in
/-- Equal actual overgroup characters are exactly one actual SO orbit of
principal Omega constituents. -/
theorem principalAbove_eq_iff (theta eta : OmegaBrauer F root b) :
    cover theta = cover eta ↔
      ∃ h : H F, brauerStep F S literal root b hb h theta = eta := by
  constructor
  · intro equal
    have occursEta := principalAbove_occurs F root b hb rootH bH hbH roots fieldScope
      indexTwo green principalLift eta
    rw [← equal] at occursEta
    obtain ⟨h, heq⟩ := clifford.constituents_conjugate (cover theta).val theta.val eta.val
      (principalAbove_occurs F root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift theta) occursEta
    exact ⟨h, Subtype.ext heq⟩
  · rintro ⟨h, rfl⟩
    exact (principalAbove_step F S literal root b hb rootH bH hbH roots fieldScope
      indexTwo green principalLift h theta).symm

include clifford principalRestriction in
/-- Every actual principal SO character is reached by one of its literal
principal Omega constituents. -/
theorem principalAbove_surjective : Function.Surjective cover := by
  intro Phi
  obtain ⟨theta, occurs⟩ := clifford.constituent_exists Phi.val
  let constituent : OmegaBrauer F root b :=
    ⟨theta, principalRestriction.restricts_principal bH b hbH hb Phi.val theta
      Phi.property occurs⟩
  exact ⟨constituent,
    principalAbove_eq F root b hb rootH bH hbH roots fieldScope indexTwo
      green principalLift constituent Phi occurs⟩

include clifford in
/-- The same fibre criterion expressed with the already checked two-point
involution, including fixed points. -/
theorem principalAbove_eq_iff_eq_or_step (delta : H F) (outside : delta ∉ G F)
    (theta eta : OmegaBrauer F root b) :
    cover theta = cover eta ↔
      eta = theta ∨ eta = brauerPermutation F S literal root b hb delta indexTwo theta :=
  (principalAbove_eq_iff F S literal root b hb rootH bH hbH roots fieldScope indexTwo
    green principalLift clifford theta eta).trans
    (exists_brauerStep_iff F S literal root b hb delta indexTwo outside theta eta)

/-- Factoring the constructed character map through the actual SO orbit
quotient. Its well-definedness needs only Green uniqueness and the checked
naturality of literal restriction occurrence. -/
def orbitMap : PrincipalBrauerOrbit F S literal root b hb → SOBrauer F rootH bH :=
  Quotient.lift cover (by
    intro theta eta related
    obtain ⟨h, heq⟩ :=
      (principalBrauerOrbitRel_iff F S literal root b hb theta eta).mp related
    rw [← heq]
    exact (principalAbove_step F S literal root b hb rootH bH hbH roots fieldScope
      indexTwo green principalLift h theta).symm)

@[simp] theorem orbitMap_mk (theta : OmegaBrauer F root b) :
    orbitMap F S literal root b hb rootH bH hbH roots fieldScope indexTwo
      green principalLift (Quotient.mk _ theta) = cover theta := rfl

include clifford in
theorem orbitMap_injective :
    Function.Injective
      (orbitMap F S literal root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro theta eta equal
  apply Quotient.sound
  apply (principalBrauerOrbitRel_iff F S literal root b hb theta eta).mpr
  exact (principalAbove_eq_iff F S literal root b hb rootH bH hbH roots fieldScope
    indexTwo green principalLift clifford theta eta).mp equal

include clifford principalRestriction in
theorem orbitMap_surjective :
    Function.Surjective
      (orbitMap F S literal root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift) := by
  intro Phi
  obtain ⟨theta, equal⟩ :=
    principalAbove_surjective F root b hb rootH bH hbH roots fieldScope indexTwo
      green principalLift clifford principalRestriction Phi
  exact ⟨Quotient.mk _ theta, equal⟩

/-- The principal SO fibre is equivalent to the quotient of the literal
principal Omega fibre by its actual SO action. All representation input
is confined to the four one-way source clauses above. -/
def principalOrbitEquiv : PrincipalBrauerOrbit F S literal root b hb ≃ SOBrauer F rootH bH :=
  Equiv.ofBijective
    (orbitMap F S literal root b hb rootH bH hbH roots fieldScope indexTwo green principalLift)
    ⟨orbitMap_injective F S literal root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift clifford,
      orbitMap_surjective F S literal root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift clifford principalRestriction⟩

@[simp] theorem principalOrbitEquiv_mk (theta : OmegaBrauer F root b) :
    principalOrbitEquiv F S literal root b hb rootH bH hbH roots fieldScope indexTwo
      green principalLift clifford principalRestriction (Quotient.mk _ theta) =
        cover theta := rfl

/-- The quotient equivalence is anchored to the original restriction
relation on each literal representative. -/
theorem principalOrbitEquiv_occurs (theta : OmegaBrauer F root b) :
    BrauerOccursInRestriction (G F) rootH root
      (principalOrbitEquiv F S literal root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift clifford principalRestriction (Quotient.mk _ theta)).val theta.val :=
  principalAbove_occurs F root b hb rootH bH hbH roots fieldScope indexTwo
    green principalLift theta

end PrincipalConstituents

end ModularRep.PaperProofs.TypeBRankThreePrincipalBrauerOrbitBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
