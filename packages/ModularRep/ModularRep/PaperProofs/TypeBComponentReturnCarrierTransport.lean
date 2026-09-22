import ModularRep.PaperProofs.TypeBRightActionOrientation
import ModularRep.IrreducibleBrauerCharacterEquiv

/-!
# Returning a component calculation to its original carriers

Orbit membership and the actual setwise stabiliser are preserved by an
equivalence intertwining the actions, including an equivalence of the
diagonal groups.  The final section supplies this intertwining for literal
Brauer characters using the canonical transported root embedding.  These
are carrier-transport deductions, not source certificates or selectors.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBComponentReturnCarrierTransport

open TypeBRightActionOrientation EvenFieldAssumption53Relative

section Actions

variable {D D' E X Y : Type*} [Group D] [Group D'] [Group E]
variable [MulAction D X] [MulAction D' Y] [MulAction E X] [MulAction E Y]
variable (beta : X ≃ Y) (delta : D ≃* D')
variable (diagonal : ∀ (d : D) x, beta (d • x) = delta d • beta x)
variable (outer : ∀ (e : E) x, beta (e • x) = e • beta x)

/-- The actual stabiliser of the orbit as a subset of the set of characters. -/
def orbitStabilizer (base : X) : Subgroup E := by
  letI : MulAction E (Set X) := imageSetMulAction
  exact MulAction.stabilizer E (MulAction.orbit D base)

include delta diagonal

theorem mem_orbit_iff (base x : X) :
    beta x ∈ MulAction.orbit D' (beta base) ↔ x ∈ MulAction.orbit D base := by
  constructor
  · rintro ⟨d', hd'⟩
    refine ⟨delta.symm d', beta.injective ?_⟩
    rw [diagonal, delta.apply_symm_apply]
    exact hd'
  · rintro ⟨d, rfl⟩
    exact ⟨delta d, (diagonal d base).symm⟩

theorem image_orbit (base : X) :
    beta '' MulAction.orbit D base = MulAction.orbit D' (beta base) := by
  ext y
  obtain ⟨x, rfl⟩ := beta.surjective y
  rw [Set.mem_image_equiv, mem_orbit_iff beta delta diagonal]
  simp

include outer

/-- The same subgroup of E stabilises the orbit in either presentation. -/
theorem orbitStabilizer_eq (base : X) :
    orbitStabilizer (D := D) (E := E) base =
      orbitStabilizer (D := D') (E := E) (beta base) := by
  ext e
  change (fun x : X ↦ e • x) '' MulAction.orbit D base =
      MulAction.orbit D base ↔
    (fun y : Y ↦ e • y) '' MulAction.orbit D' (beta base) =
      MulAction.orbit D' (beta base)
  have hcomm : beta '' ((fun x : X ↦ e • x) '' MulAction.orbit D base) =
      (fun y : Y ↦ e • y) '' (beta '' MulAction.orbit D base) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    exact outer e x
  constructor
  · intro h
    rw [← image_orbit beta delta diagonal base, ← hcomm, h]
  · intro h
    apply Set.image_injective.mpr beta.injective
    rw [hcomm, image_orbit beta delta diagonal base, h]

/-- An already constructed fixed representative returns to the original
orbit and the original setwise stabiliser. -/
theorem fixed_representative_transport (base : X)
    (constructed : ∃ y ∈ MulAction.orbit D' (beta base),
      ∀ e : orbitStabilizer (D := D') (E := E) (beta base), e.1 • y = y) :
    ∃ x ∈ MulAction.orbit D base,
      ∀ e : orbitStabilizer (D := D) (E := E) base, e.1 • x = x := by
  obtain ⟨y, hy, hfixed⟩ := constructed
  refine ⟨beta.symm y, ?_, ?_⟩
  · apply (mem_orbit_iff beta delta diagonal base _).mp
    simpa using hy
  · intro e
    have he : e.1 ∈ orbitStabilizer (D := D') (E := E) (beta base) := by
      rw [← orbitStabilizer_eq beta delta diagonal outer base]
      exact e.2
    apply beta.injective
    rw [outer, beta.apply_symm_apply]
    exact hfixed ⟨e.1, he⟩

end Actions

section BrauerCharacters

variable {p : ℕ} {k K G G' A : Type*}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group G'] [Finite G'] [Group A]
variable (iota : PrimeRegularRootEmbedding p k K G) (groupEquiv : G ≃* G')

/-- Conjugate the actual automorphism action through the group equivalence. -/
def transportedAut (rho : A →* MulAut G) : A →* MulAut G' :=
  (MulAut.congr groupEquiv).toMonoidHom.comp rho

/-- Literal function-valued Brauer-character naturality; the target root
embedding is constructed by transport, not supplied independently. -/
theorem brauerAction_transport (rho : A →* MulAut G) (a : A) (psi : IBr iota) :
    let _ := rightAutomorphismAction iota rho
    let _ := rightAutomorphismAction (iota.alongMulEquiv groupEquiv)
      (transportedAut groupEquiv rho)
    IrreducibleBrauerCharacter.equivAlongMulEquiv iota groupEquiv (a • psi) =
      a • IrreducibleBrauerCharacter.equivAlongMulEquiv iota groupEquiv psi := by
  exact IrreducibleBrauerCharacter.equivAlongMulEquiv_twist
    iota groupEquiv psi (rho a⁻¹)

/-- The same literal character transport when the acting group is also
changed. The premise is a square of group automorphisms, with no character,
orbit or stabiliser predicate. -/
theorem brauerAction_transport_of_square {B : Type*} [Group B]
    (actor : A →* B) (rho : A →* MulAut G) (rho' : B →* MulAut G')
    (square : ∀ a, rho' (actor a) = MulAut.congr groupEquiv (rho a))
    (a : A) (psi : IBr iota) :
    let _ := rightAutomorphismAction iota rho
    let _ := rightAutomorphismAction (iota.alongMulEquiv groupEquiv) rho'
    IrreducibleBrauerCharacter.equivAlongMulEquiv iota groupEquiv (a • psi) =
      actor a • IrreducibleBrauerCharacter.equivAlongMulEquiv iota groupEquiv psi := by
  change IrreducibleBrauerCharacter.equivAlongMulEquiv iota groupEquiv
      (IrreducibleBrauerCharacter.twist iota psi (rho a⁻¹)) =
    IrreducibleBrauerCharacter.twist (iota.alongMulEquiv groupEquiv)
      (IrreducibleBrauerCharacter.equivAlongMulEquiv iota groupEquiv psi)
      (rho' (actor a)⁻¹)
  rw [← map_inv actor, square]
  exact IrreducibleBrauerCharacter.equivAlongMulEquiv_twist
    iota groupEquiv psi (rho a⁻¹)

end BrauerCharacters

end ModularRep.PaperProofs.TypeBComponentReturnCarrierTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
