import ModularRep.PaperProofs.TypeBFiniteProductNaturality
import ModularRep.IrreducibleBrauerCharacterEquiv

/-!
# Literal character orbits for the regular-Levi carrier join

This is the character part of current Lemma 4.5. The original group is
identified with the actual rational factor product by a group equivalence;
the global root is transported canonically. The four-field external-product
source supplies only the standard character theorem and values. Character
action equations and orbit transport are deductions from the group square.

The surjectivity hypothesis of the final helper is to be discharged by the
separately checked geometric supported-lift deduction. It is not an external
certificate for the source-instantiated regular-Levi endpoint.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviCharacterOrbit

open TypeBRegularLeviCharacterActionAdapter EvenFieldAssumption53Relative

variable {p : ℕ} {I k K G M : Type} [Fintype I]
variable (H D : I → Type) [∀ i, Group (H i)] [∀ i, Finite (H i)]
variable [∀ i, Group (D i)] [Group G] [Finite G] [Group M]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (decomposition : G ≃* ((i : I) → H i))
variable (factorRoot : ∀ i, PrimeRegularRootEmbedding p k K (H i))
variable (source : TypeBFiniteProductNaturality.ExternalProductData H
  (iota.alongMulEquiv decomposition) factorRoot)
variable (factorAut : ∀ i, D i →* MulAut (H i))
variable (action : M →* MulAut G) (rho : M →* ((i : I) → D i))

/-- The tuple equivalence uses the prescribed original root, its canonical
transport, and the actual standard external product. -/
def tupleEquiv : IBr iota ≃ ((i : I) → IBr (factorRoot i)) :=
  (IrreducibleBrauerCharacter.equivAlongMulEquiv iota decomposition).trans
    source.characters

variable (groupSquare : ∀ m,
  MulAut.congr decomposition (action m) = coordinateMulAut H D factorAut (rho m))

include groupSquare in
/-- Group-level conjugation coordinates imply the action on actual Brauer
characters. The equality is not part of the external-product source. -/
theorem tupleEquiv_action (m : M) (psi : IBr iota) :
    let _ := rightAutomorphismAction iota action
    let _ := coordinateIBrRightAction H D factorRoot factorAut
    tupleEquiv H iota decomposition factorRoot source (m • psi) =
      rho m • tupleEquiv H iota decomposition factorRoot source psi := by
  change source.characters (IrreducibleBrauerCharacter.equivAlongMulEquiv
    iota decomposition (IrreducibleBrauerCharacter.twist iota psi (action m⁻¹))) = _
  rw [IrreducibleBrauerCharacter.equivAlongMulEquiv_twist, groupSquare]
  change _ = fun i ↦ IrreducibleBrauerCharacter.twist (factorRoot i)
    (tupleEquiv H iota decomposition factorRoot source psi i)
    (factorAut i ((rho m i)⁻¹))
  have h := TypeBFiniteProductNaturality.coordinate_naturality H
    (iota.alongMulEquiv decomposition) factorRoot source D factorAut
    (rho m⁻¹) (IrreducibleBrauerCharacter.equivAlongMulEquiv iota decomposition psi)
  simpa only [map_inv, tupleEquiv, Equiv.trans_apply, Pi.inv_apply] using h

include groupSquare in
/-- A literal Cartesian-orbit helper, with surjectivity supplied by the
geometric correction proof. The original character orbit is retained as
the image of an explicit equivalence, not identified with an arbitrary set. -/
theorem image_original_orbit_eq_coordinate_orbits
    (rho_surjective : Function.Surjective rho) (base : IBr iota) :
    let _ := rightAutomorphismAction iota action
    (tupleEquiv H iota decomposition factorRoot source) '' MulAction.orbit M base =
      {theta | ∀ i,
        let _ := rightAutomorphismAction (factorRoot i) (factorAut i)
        theta i ∈ MulAction.orbit (D i)
          (tupleEquiv H iota decomposition factorRoot source base i)} := by
  classical
  letI : MulAction M (IBr iota) := rightAutomorphismAction iota action
  letI factorAction (i : I) : MulAction (D i) (IBr (factorRoot i)) :=
    rightAutomorphismAction (factorRoot i) (factorAut i)
  have haction : ∀ (m : M) psi,
      tupleEquiv H iota decomposition factorRoot source (m • psi) =
        rho m • tupleEquiv H iota decomposition factorRoot source psi := by
    intro m psi
    exact tupleEquiv_action H D iota decomposition factorRoot source
      factorAut action rho groupSquare m psi
  ext theta
  constructor
  · rintro ⟨psi, ⟨m, rfl⟩, rfl⟩ i
    rw [haction]
    exact MulAction.mem_orbit _ (rho m i)
  · intro htheta
    have hprod := (TypeBRegularLeviOrbitLemma46Relative.mem_pi_orbit_iff D
      (fun i ↦ IBr (factorRoot i))
      (tupleEquiv H iota decomposition factorRoot source base) theta).mpr htheta
    obtain ⟨d, hd⟩ := hprod
    obtain ⟨m, hm⟩ := rho_surjective d
    refine ⟨m • base, MulAction.mem_orbit base m, ?_⟩
    rw [haction, hm]
    exact hd

end ModularRep.PaperProofs.TypeBRegularLeviCharacterOrbit


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
