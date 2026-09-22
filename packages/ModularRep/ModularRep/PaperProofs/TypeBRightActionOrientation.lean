import ModularRep.ComponentReturnFull
import ModularRep.PaperProofs.EvenFieldAssumption53Relative

/-!
# Right-action orientation in the type B component return

The manuscript writes automorphisms on the right.  Lean's `MulAction` is a
left action, so the existing character action encodes the manuscript action
of `a` as the Lean action of `a⁻¹`.  This file checks the resulting orbit,
stabiliser, component-cycle, and return bookkeeping used in Lemmas 4.5--4.6.

No algebraic-group decomposition or character-action identification is made
here.  In particular, applying these statements to the rational Levi factors
still requires the concrete naturality of the Brauer-character tuple.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRightActionOrientation

open ModularRep.ManuscriptVerification.ComponentReturnFull
open ModularRep.PaperProofs.EvenFieldAssumption53Relative

universe u v

section GenericRightAction

variable {A B Y : Type*} [Group A] [Group B]
variable [MulAction Bᵐᵒᵖ Y]

/-- Application of an element using the manuscript's right-action
convention.  The opposite group records the reversal in successive right
actions. -/
def manuscriptRightApply (rho : A →* B) (a : A) (y : Y) : Y :=
  MulOpposite.op (rho a) • y

/-- The Lean left action obtained from the manuscript right action. -/
@[instance_reducible] def inverseLeftAction (rho : A →* B) : MulAction A Y :=
  MulAction.compHom Y (inverseOpHom rho)

/-- The action induced on subsets by pointwise image.  It is kept explicit
because Mathlib deliberately provides only a pointwise `SMul` instance for
arbitrary sets. -/
@[instance_reducible] def imageSetMulAction
    {G X : Type*} [Group G] [MulAction G X] : MulAction G (Set X) where
  smul g S := (g • ·) '' S
  one_smul S := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := by simpa only [one_smul] using hxy
      rwa [← this]
    · intro hx
      exact ⟨x, hx, one_smul G x⟩
  mul_smul g h S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h • y, ⟨y, hy, rfl⟩, (mul_smul g h y).symm⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, mul_smul g h y⟩

/-- Acting on the left by `a` is exactly acting on the right by `a⁻¹`. -/
theorem inverseLeftAction_apply (rho : A →* B) (a : A) (y : Y) :
    let _ : MulAction A Y := inverseLeftAction rho
    a • y = manuscriptRightApply rho a⁻¹ y := by
  rfl

/-- The orbit written with the manuscript's right action. -/
def manuscriptRightOrbit (rho : A →* B) (y : Y) : Set Y :=
  {z | ∃ a : A, manuscriptRightApply rho a y = z}

/-- Inversion of the acting element identifies the manuscript right orbit
with the orbit for the encoded Lean left action. -/
theorem manuscriptRightOrbit_eq_leanOrbit (rho : A →* B) (y : Y) :
    let _ : MulAction A Y := inverseLeftAction rho
    manuscriptRightOrbit rho y = MulAction.orbit A y := by
  let _ : MulAction A Y := inverseLeftAction rho
  ext z
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    simpa [inverseLeftAction_apply] using ha
  · rintro ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    simpa [inverseLeftAction_apply] using ha

/-- The point stabiliser written directly in the manuscript's right-action
convention. -/
def manuscriptRightStabilizer (rho : A →* B) (y : Y) : Subgroup A where
  carrier := {a | manuscriptRightApply rho a y = y}
  one_mem' := by simp [manuscriptRightApply]
  mul_mem' := by
    intro a b ha hb
    change MulOpposite.op (rho a) • y = y at ha
    change MulOpposite.op (rho b) • y = y at hb
    simp only [Set.mem_ofPred_eq, manuscriptRightApply, map_mul,
      MulOpposite.op_mul, mul_smul]
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    change MulOpposite.op (rho a) • y = y at ha
    simp only [Set.mem_ofPred_eq, manuscriptRightApply, map_inv,
      MulOpposite.op_inv]
    rw [inv_smul_eq_iff]
    exact ha.symm

/-- Point stabilisers are unchanged by the conversion from the manuscript
right action to the inverse Lean left action. -/
theorem manuscriptRightStabilizer_eq_leanStabilizer
    (rho : A →* B) (y : Y) :
    let _ : MulAction A Y := inverseLeftAction rho
    manuscriptRightStabilizer rho y = MulAction.stabilizer A y := by
  let _ : MulAction A Y := inverseLeftAction rho
  ext a
  change manuscriptRightApply rho a y = y ↔ a • y = y
  rw [inverseLeftAction_apply]
  simp only [manuscriptRightApply, map_inv, MulOpposite.op_inv]
  rw [inv_smul_eq_iff]
  exact eq_comm

/-- The same stabiliser equality applied to a set.  Thus the manuscript's
setwise stabiliser `E_O` is the stabiliser of `O` for the inverse Lean
action. -/
theorem manuscriptRightSetwiseStabilizer_eq_leanStabilizer
    {X : Type*} [MulAction Bᵐᵒᵖ X]
    (rho : A →* B) (S : Set X) :
    let _ : MulAction Bᵐᵒᵖ (Set X) := imageSetMulAction
    let _ : MulAction A (Set X) := inverseLeftAction rho
    manuscriptRightStabilizer (Y := Set X) rho S =
      MulAction.stabilizer A S := by
  let _ : MulAction Bᵐᵒᵖ (Set X) := imageSetMulAction
  let _ : MulAction A (Set X) := inverseLeftAction rho
  exact manuscriptRightStabilizer_eq_leanStabilizer (Y := Set X) rho S

/-- The inverse Lean generator performs one forward manuscript step. -/
theorem inverseGenerator_smul_eq_manuscriptRightApply
    (rho : A →* B) (tau : A) (y : Y) :
    let _ : MulAction A Y := inverseLeftAction rho
    tau⁻¹ • y = manuscriptRightApply rho tau y := by
  simp [inverseLeftAction_apply]

/-- The `n`th power of the inverse Lean generator performs the forward
manuscript return by `tau^n`. -/
theorem inverseGenerator_pow_smul_eq_manuscriptRightPow
    (rho : A →* B) (tau : A) (n : Nat) (y : Y) :
    let _ : MulAction A Y := inverseLeftAction rho
    (tau⁻¹) ^ n • y = manuscriptRightApply rho (tau ^ n) y := by
  simp [inverseLeftAction_apply]

/-- Setwise preservation by one forward manuscript step gives exactly the
`MapsTo` hypothesis used by `ComponentReturnFull` for the inverse Lean
generator. -/
theorem forwardMapsTo_to_inverseGenerator
    (rho : A →* B) (tau : A) (S : Set Y)
    (hstable : Set.MapsTo (manuscriptRightApply rho tau) S S) :
    let _ : MulAction A Y := inverseLeftAction rho
    Set.MapsTo (tau⁻¹ • ·) S S := by
  dsimp only
  let _ : MulAction A Y := inverseLeftAction rho
  intro y hy
  change tau⁻¹ • y ∈ S
  rw [inverseGenerator_smul_eq_manuscriptRightApply]
  exact hstable hy

/-- Equality of the forward manuscript image with a set implies the exact
setwise-preservation hypothesis used for the inverse Lean generator. -/
theorem forwardSetwiseFixed_to_inverseGenerator
    (rho : A →* B) (tau : A) (S : Set Y)
    (hstable : manuscriptRightApply rho tau '' S = S) :
    let _ : MulAction A Y := inverseLeftAction rho
    Set.MapsTo (tau⁻¹ • ·) S S := by
  apply forwardMapsTo_to_inverseGenerator rho tau S
  intro y hy
  rw [← hstable]
  exact ⟨y, hy, rfl⟩

/-- A return formula written with a forward manuscript element becomes the
return formula for its inverse in the Lean action.  The translated formula
is derived, not assumed. -/
theorem forwardReturnFormula_to_inverseElement
    (rho : A →* B) (transport : Y → Y) (n : Nat)
    (tau : A) (y : Y)
    (hreturn : transport^[n] y = manuscriptRightApply rho (tau ^ n) y) :
    let _ : MulAction A Y := inverseLeftAction rho
    transport^[n] y = (tau⁻¹) ^ n • y := by
  dsimp only
  let _ : MulAction A Y := inverseLeftAction rho
  rw [inverseGenerator_pow_smul_eq_manuscriptRightPow]
  exact hreturn

end GenericRightAction

section ComponentCycle

variable {K E B : Type*} [Group E] [Group B]
variable {n : K → Nat} {X : K → Type*}
variable [MulAction Bᵐᵒᵖ (ComponentTuple n X)]

/-- The forward coordinate formulas used in the manuscript are exactly the
coordinate formulas required by `ComponentReturnFull` for the inverse Lean
generator.  No fixed tuple or return conclusion is assumed. -/
theorem forwardCoordinateFormulas_to_inverseGenerator
    (hn : ∀ k, 0 < n k)
    (rho : E →* B) (tau : E) (transport : ∀ k, X k → X k)
    (hfirst : ∀ (x : ComponentTuple n X) k,
      manuscriptRightApply rho tau x (firstIndex n hn k) =
        transport k (x (lastIndex n hn k)))
    (hsucc : ∀ (x : ComponentTuple n X) k j (hj : j + 1 < n k),
      manuscriptRightApply rho tau x ⟨k, ⟨j + 1, hj⟩⟩ =
        transport k (x ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩)) :
    let _ : MulAction E (ComponentTuple n X) := inverseLeftAction rho
    (∀ (x : ComponentTuple n X) k,
      (tau⁻¹ • x) (firstIndex n hn k) =
        transport k (x (lastIndex n hn k))) ∧
    (∀ (x : ComponentTuple n X) k j (hj : j + 1 < n k),
      (tau⁻¹ • x) ⟨k, ⟨j + 1, hj⟩⟩ =
        transport k (x ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩)) := by
  let _ : MulAction E (ComponentTuple n X) := inverseLeftAction rho
  constructor
  · intro x k
    rw [inverseGenerator_smul_eq_manuscriptRightApply]
    exact hfirst x k
  · intro x k j hj
    rw [inverseGenerator_smul_eq_manuscriptRightApply]
    exact hsucc x k j hj

/-- An inverse of a generator is again a generator.  This is the remaining
cyclic-group bookkeeping needed when `ComponentReturnFull` is invoked with
the inverse Lean generator. -/
theorem zpowers_inverseGenerator_eq_top
    (tau : E) (htau : Subgroup.zpowers tau = ⊤) :
    Subgroup.zpowers tau⁻¹ = ⊤ := by
  rw [Subgroup.zpowers_inv, htau]

end ComponentCycle

section BrauerCharacters

variable {p : Nat} {D A k K : Type u}
variable [Group D] [Finite D] [Group A]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- For function-valued irreducible Brauer characters, the generic inverse
left action is definitionally the existing `rightAutomorphismAction`. -/
theorem rightAutomorphismAction_apply
    (iota : PrimeRegularRootEmbedding p k K D)
    (rho : A →* MulAut D) (a : A) (psi : IBr iota) :
    let _ : MulAction A (IBr iota) := rightAutomorphismAction iota rho
    a • psi = IrreducibleBrauerCharacter.twist iota psi (rho a⁻¹) := by
  rfl

/-- The manuscript orbit of an irreducible Brauer character is its orbit for
the existing inverse Lean action. -/
theorem brauer_manuscriptRightOrbit_eq_leanOrbit
    (iota : PrimeRegularRootEmbedding p k K D)
    (rho : A →* MulAut D) (psi : IBr iota) :
    let _ : MulAction A (IBr iota) := rightAutomorphismAction iota rho
    manuscriptRightOrbit rho psi = MulAction.orbit A psi := by
  exact manuscriptRightOrbit_eq_leanOrbit rho psi

/-- The manuscript and Lean stabilisers of an irreducible Brauer character
are equal under `rightAutomorphismAction`. -/
theorem brauer_manuscriptRightStabilizer_eq_leanStabilizer
    (iota : PrimeRegularRootEmbedding p k K D)
    (rho : A →* MulAut D) (psi : IBr iota) :
    let _ : MulAction A (IBr iota) := rightAutomorphismAction iota rho
    manuscriptRightStabilizer rho psi = MulAction.stabilizer A psi := by
  exact manuscriptRightStabilizer_eq_leanStabilizer rho psi

end BrauerCharacters

end ModularRep.PaperProofs.TypeBRightActionOrientation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
