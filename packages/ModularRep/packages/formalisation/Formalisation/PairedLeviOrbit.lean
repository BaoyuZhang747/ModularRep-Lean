import Formalisation.ComponentReturnAssembly
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite orbit deductions in the paired-Levi argument

This module formalises the representation-free deductions used after the algebraic-group
input in the paired-Levi reduction.  The external input says that the diagonal automorphism
group induced by the regular overgroup is a direct product of its factor groups.  Once that
identification is available, `pi_orbit_eq_coordinate_orbits` proves that a diagonal orbit is
the Cartesian product of its coordinate orbits.

The module also proves that stability of a coordinate orbit supplies the correcting diagonal
element used in the component-return argument, and that a return of the form
`F⁻¹ ^ k * tau ^ t` fixes a component whenever `tau ^ t` and `F ^ k` carry it to the same
component.  It does not formalise connected reductive groups, rational fixed points, Brauer
characters, or the identification of the regular-overgroup quotient with the direct product
of factor diagonal groups.
-/

namespace Formalisation

section ProductOrbits

variable {I : Type*}
variable (D X : I → Type*)
variable [∀ i, Group (D i)] [∀ i, MulAction (D i) (X i)]

/-- For a componentwise action of a direct product, membership in an orbit is equivalent to
coordinatewise membership in the corresponding factor orbits. -/
theorem mem_pi_orbit_iff (x y : ∀ i, X i) :
    y ∈ MulAction.orbit (∀ i, D i) x ↔
      ∀ i, y i ∈ MulAction.orbit (D i) (x i) := by
  constructor
  · rw [MulAction.mem_orbit_iff]
    rintro ⟨d, rfl⟩ i
    exact MulAction.mem_orbit (x i) (d i)
  · intro h
    rw [MulAction.mem_orbit_iff]
    have hchoice : ∀ i, ∃ d : D i, d • x i = y i := by
      intro i
      exact MulAction.mem_orbit_iff.mp (h i)
    choose d hd using hchoice
    refine ⟨d, ?_⟩
    funext i
    exact hd i

/-- The orbit of a tuple under the direct product of the factor groups is exactly the
Cartesian product of its coordinate orbits. -/
theorem pi_orbit_eq_coordinate_orbits (x : ∀ i, X i) :
    MulAction.orbit (∀ i, D i) x =
      {y | ∀ i, y i ∈ MulAction.orbit (D i) (x i)} := by
  ext y
  exact mem_pi_orbit_iff D X x y

/-- Coordinatewise choices from the prescribed factor orbits combine into a point of the
original direct-product orbit. -/
theorem tuple_mem_pi_orbit (x y : ∀ i, X i)
    (h : ∀ i, y i ∈ MulAction.orbit (D i) (x i)) :
    y ∈ MulAction.orbit (∀ i, D i) x :=
  (mem_pi_orbit_iff D X x y).2 h

end ProductOrbits

section EffectiveAction

variable {D Delta E X : Type*} [Group D] [Group Delta] [Group E]
variable [MulAction D X] [MulAction Delta X] [MulAction E X]

/-- A surjective homomorphism that does not change the action does not change the orbit.
This is the finite-action step used when the regular overgroup is replaced by its effective
diagonal automorphism quotient. -/
theorem orbit_eq_of_surjective_action_hom (rho : D →* Delta)
    (hrho : Function.Surjective rho)
    (haction : ∀ (d : D) (x : X), rho d • x = d • x)
    (x : X) :
    MulAction.orbit D x = MulAction.orbit Delta x := by
  ext y
  constructor
  · rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
    rintro ⟨d, rfl⟩
    exact ⟨rho d, haction d x⟩
  · rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
    rintro ⟨delta, rfl⟩
    obtain ⟨d, rfl⟩ := hrho delta
    exact ⟨d, (haction d x).symm⟩

/-- Elementwise stabiliser factorisation for an effective quotient lifts to the original
acting group.  No faithfulness is required: the kernel acts trivially by the action
compatibility hypothesis. -/
theorem stabilizer_factorization_lifts_along_action_hom (rho : D →* Delta)
    (haction : ∀ (d : D) (x : X), rho d • x = d • x)
    (x : X)
    (hfactor : ∀ (delta : Delta) (e : E),
      delta • (e • x) = x ↔ delta • x = x ∧ e • x = x) :
    ∀ (d : D) (e : E),
      d • (e • x) = x ↔ d • x = x ∧ e • x = x := by
  intro d e
  rw [← haction d (e • x), hfactor, haction]

end EffectiveAction

section ReturnCorrection

variable {D E X : Type*} [Group D] [Group E]
variable [MulAction D X] [MulAction E X]

/-- If the return element carries a representative into its diagonal orbit, a diagonal
element corrects the return back to that representative. -/
theorem exists_correcting_element_of_return_mem_orbit (x : X) (e : E)
    (hreturn : e • x ∈ MulAction.orbit D x) :
    ∃ d : D, d • (e • x) = x := by
  obtain ⟨d, hd⟩ := MulAction.mem_orbit_iff.mp hreturn
  refine ⟨d⁻¹, ?_⟩
  rw [← hd, ← mul_smul]
  simp

/-- Local semidirect-product stabiliser factorisation turns orbit stability of the return into
fixedness of the chosen representative. -/
theorem fixed_return_of_orbit_mem_and_factorization
    (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi)
    (x : X) (e : E)
    (hfactor : SemidirectStabilizerFactors phi hcompat x)
    (hreturn : e • x ∈ MulAction.orbit D x) :
    e • x = x := by
  apply fixed_return_of_semidirect_factorization phi hcompat x e hfactor
  exact exists_correcting_element_of_return_mem_orbit x e hreturn

end ReturnCorrection

section AssemblyInOrbit

variable {K : Type*}
variable (D E X : K → Type*)
variable [∀ k, Group (D k)] [∀ k, Group (E k)]
variable [∀ k, MulAction (D k) (X k)] [∀ k, MulAction (E k) (X k)]

/-- Component return, together with coordinatewise orbit membership, produces a coherent
tuple in the original direct-product orbit.  The coordinatewise membership hypothesis is the
precise finite set content supplied in the manuscript by the Cartesian factorisation of the
regular-overgroup orbit. -/
theorem component_return_assembly_in_product_orbit
    (n : K → Nat) (hn : ∀ k, 0 < n k)
    (phi : ∀ k, E k →* MulAut (D k))
    (hcompat : ∀ k, SemidirectActionCompatible (X := X k) (phi k))
    (transport : ∀ k, X k → X k)
    (representative : ∀ k, X k)
    (returnElement : ∀ k, E k)
    (base : (i : ComponentIndex n) → X i.1)
    (htransport : ∀ k,
      (transport k)^[n k] (representative k) = returnElement k • representative k)
    (hfactor : ∀ k,
      SemidirectStabilizerFactors (phi k) (hcompat k) (representative k))
    (hcoset : ∀ k, ∃ d : D k,
      d • (returnElement k • representative k) = representative k)
    (hcoordinate : ∀ i,
      propagatedComponent n X transport representative i ∈
        MulAction.orbit (D i.1) (base i)) :
    (∀ k, returnElement k • representative k = representative k) ∧
      ∃ theta : (i : ComponentIndex n) → X i.1,
        theta ∈ MulAction.orbit ((i : ComponentIndex n) → D i.1) base ∧
        (∀ k, theta ⟨k, ⟨0, hn k⟩⟩ = representative k) ∧
        (∀ k j (hj : j + 1 < n k),
          theta ⟨k, ⟨j + 1, hj⟩⟩ =
            transport k (theta ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩)) ∧
        (∀ k,
          transport k
              (theta ⟨k, ⟨n k - 1, Nat.sub_lt (hn k) Nat.zero_lt_one⟩⟩) =
            theta ⟨k, ⟨0, hn k⟩⟩) := by
  have hfixed : ∀ k, returnElement k • representative k = representative k := by
    intro k
    exact fixed_return_of_semidirect_factorization
      (phi k) (hcompat k) (representative k) (returnElement k)
      (hfactor k) (hcoset k)
  have hreturn : ∀ k,
      (transport k)^[n k] (representative k) = representative k := by
    intro k
    rw [htransport, hfixed]
  let theta := propagatedComponent n X transport representative
  refine ⟨hfixed, theta, ?_, ?_, ?_, ?_⟩
  · apply tuple_mem_pi_orbit
      (fun i : ComponentIndex n ↦ D i.1)
      (fun i : ComponentIndex n ↦ X i.1)
    intro i
    simpa [theta] using hcoordinate i
  · exact propagatedComponent_zero n hn X transport representative
  · exact propagatedComponent_succ n X transport representative
  · exact propagatedComponent_wrap n hn X transport representative hreturn

end AssemblyInOrbit

section ReturnPower

variable {A I : Type*} [Group A] [MulAction A I]

/-- If `tau ^ t` and `F ^ k` send a component to the same component, then the corrected
return `F⁻¹ ^ k * tau ^ t` fixes it.  This is written for left actions; it is the left-action
translation of the manuscript's right-action calculation. -/
theorem corrected_return_fixes_component (F tau : A) (k t : Nat) (i : I)
    (hsame : tau ^ t • i = F ^ k • i) :
    ((F⁻¹) ^ k * tau ^ t) • i = i := by
  rw [mul_smul, hsame, ← mul_smul]
  simp

/-- If both the Frobenius element and the transport element belong to one cyclic group, so
does the corrected return. -/
theorem corrected_return_mem_zpowers (F tau generator : A) (k t : Nat)
    (hF : F ∈ Subgroup.zpowers generator)
    (htau : tau ∈ Subgroup.zpowers generator) :
    (F⁻¹) ^ k * tau ^ t ∈ Subgroup.zpowers generator := by
  exact (Subgroup.zpowers generator).mul_mem
    ((Subgroup.zpowers generator).pow_mem
      ((Subgroup.zpowers generator).inv_mem hF) k)
    ((Subgroup.zpowers generator).pow_mem htau t)

end ReturnPower

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
