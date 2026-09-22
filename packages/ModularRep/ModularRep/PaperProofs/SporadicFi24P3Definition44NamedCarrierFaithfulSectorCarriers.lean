import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-! Neutral actual faithful carriers, copied from the existing source because
its native object is unavailable. The original character/weight values and
proved actions are unchanged; no character-triple context is copied. -/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers

open Formalisation
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable {BlockIndex : Type u} [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

/- The actual source operations assigning an induced ambient block to a
literal character weight. -/
variable (blockSource : LiteralCarrierAdapter
  (p := p) (k := k) (K := K) (X := X))
variable (E1 : RoutineTransportInput iota hinj blocks blockSource)

private abbrev R := blockSource

/-- Literal faithful central characters of the centre. -/
abbrev FaithfulSector :=
  {nu : CentralSector (k := k) (X := X) // Function.Injective nu}

omit [IsAlgClosed k] [Fintype X] [Invertible (Fintype.card (Subgroup.center X) : k)] in
theorem faithfulSector_smul
    (a : (MulAut X)ᵐᵒᵖ) (nu : FaithfulSector (k := k) (X := X)) :
    Function.Injective (a • (nu.1 : CentralSector (k := k) (X := X))) := by
  intro x y hxy
  apply (Representation.centerAutomorphism a.unop).injective
  apply nu.2
  exact hxy

/-- The automorphism action restricts to faithful central characters. -/
instance faithfulSectorMulAction :
    MulAction (MulAut X)ᵐᵒᵖ (FaithfulSector (k := k) (X := X)) where
  smul a nu := ⟨a • nu.1, faithfulSector_smul a nu⟩
  one_smul nu := by
    apply Subtype.ext
    exact one_smul _ _
  mul_smul a b nu := by
    apply Subtype.ext
    exact mul_smul a b nu.1

/-- Function-valued irreducible Brauer characters in faithful sectors.  The
transport record is a type parameter so that its action is inferable. -/
structure FaithfulIBr
    (E1 : RoutineTransportInput iota hinj blocks blockSource) where
  val : IBr iota
  faithful : Function.Injective (brauerSector iota hinj blocks val)

/-- Literal character-weight conjugacy classes in faithful sectors.  The
source and transport record occur in the type so that its action is
inferable. -/
structure FaithfulWeight
    (E1 : RoutineTransportInput iota hinj blocks blockSource) where
  val : WeightClass (p := p) (K := K) (X := X)
  faithful : Function.Injective (weightSector (R := R blockSource) val)

/-- The automorphism action restricts to the function-valued Brauer
characters in faithful sectors. -/
instance faithfulIBrMulAction :
    MulAction (MulAut X)ᵐᵒᵖ
      (FaithfulIBr iota hinj blocks blockSource E1) where
  smul a phi := ⟨a • phi.val, by
    rw [brauerSector_equivariant iota hinj blocks E1]
    exact faithfulSector_smul a
      ⟨brauerSector iota hinj blocks phi.val, phi.faithful⟩⟩
  one_smul phi := by
    cases phi
    rw [FaithfulIBr.mk.injEq]
    exact one_smul _ _
  mul_smul a b phi := by
    cases phi
    rw [FaithfulIBr.mk.injEq]
    exact mul_smul a b _

/-- The automorphism action restricts to literal weights in faithful
sectors. -/
instance faithfulWeightMulAction :
    MulAction (MulAut X)ᵐᵒᵖ
      (FaithfulWeight iota hinj blocks blockSource E1) where
  smul a w := ⟨a • w.val, by
    rw [weightSector_equivariant_actual
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := blockSource) E1]
    exact faithfulSector_smul a
      ⟨weightSector (R := blockSource) w.val, w.faithful⟩⟩
  one_smul w := by
    cases w
    rw [FaithfulWeight.mk.injEq]
    exact one_smul _ _
  mul_smul a b w := by
    cases w
    rw [FaithfulWeight.mk.injEq]
    exact mul_smul a b _

/-- Equality under the restricted action is exactly equality of the
underlying function-valued Brauer characters. -/
theorem faithfulIBr_smul_eq_iff (a : (MulAut X)ᵐᵒᵖ)
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    a • phi = phi ↔ a • phi.val = phi.val := by
  constructor
  · intro h
    exact congrArg (fun z => z.val) h
  · intro h
    cases phi
    rw [FaithfulIBr.mk.injEq]
    exact h

/-- Equality under the restricted action is exactly equality of the
underlying literal weight conjugacy classes. -/
theorem faithfulWeight_smul_eq_iff (a : (MulAut X)ᵐᵒᵖ)
    (w : FaithfulWeight iota hinj blocks blockSource E1) :
    a • w = w ↔ a • w.val = w.val := by
  constructor
  · intro h
    exact congrArg (fun z => z.val) h
  · intro h
    cases w
    rw [FaithfulWeight.mk.injEq]
    exact h

/-- Literal sector label on the faithful Brauer carrier. -/
def faithfulBrauerSector
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    FaithfulSector (k := k) (X := X) :=
  ⟨brauerSector iota hinj blocks phi.val, phi.faithful⟩

/-- Literal sector label on the faithful set of weights. -/
def faithfulWeightSector
    (w : FaithfulWeight iota hinj blocks blockSource E1) :
    FaithfulSector (k := k) (X := X) :=
  ⟨weightSector (R := R blockSource) w.val, w.faithful⟩

/-- Literal radical conjugacy class of a faithful weight. -/
def faithfulWeightRadical
    (w : FaithfulWeight iota hinj blocks blockSource E1) :
    RadicalClass (p := p) (X := X) :=
  weightRadical w.val

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
