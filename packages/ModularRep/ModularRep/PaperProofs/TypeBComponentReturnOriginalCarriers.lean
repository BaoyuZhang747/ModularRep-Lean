import ModularRep.PaperProofs.TypeBComponentCycleNormalization
import ModularRep.PaperProofs.TypeBComponentReturnCarrierTransport
import ModularRep.PaperProofs.TypeBNormalizedProductNaturality

/-!
# Original finite-product carriers for the component-return window

The original factors may be different groups at different positions in a
cycle. Their simultaneous H/Delta coordinate equivalences are the computed
ones in TypeBComponentCycleNormalization. The Brauer root is transported
canonically, and the actual orbit stabiliser remains the SAME subgroup of
the original external group E. No character or orbit matching is sourced.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBComponentReturnOriginalCarriers

open TypeBComponentCycleNormalization TypeBRegularLeviCharacterActionAdapter
open TypeBComponentReturnCarrierTransport EvenFieldAssumption53Relative

variable {p : ℕ} {C k K E : Type} [Fintype C]
variable (m : C → ℕ) (H D : Index m → Type)
variable [∀ i, Group (H i)] [∀ i, Finite (H i)] [∀ i, Group (D i)]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group E] [Finite E] [IsCyclic E]
variable (SH : CycleCoordinates m H) (SD : CycleCoordinates m D)
variable (diagonal : ∀ i, D i →* MulAut (H i))
variable (iota : PrimeRegularRootEmbedding p k K (Original m H))
variable (outer : E →* MulAut (Original m H))

/-- The normalized root is computed from the original root and the actual
group equivalence; no second independent modular system is introduced. -/
abbrev normalizedRoot := iota.alongMulEquiv (productEquiv m H SH)

abbrev characterEquiv := IrreducibleBrauerCharacter.equivAlongMulEquiv
  iota (productEquiv m H SH)

def originalStabilizer (base : IBr iota) : Subgroup E := by
  letI := rightAutomorphismAction iota (coordinateMulAut H D diagonal)
  letI := rightAutomorphismAction iota outer
  exact orbitStabilizer (D := Original m D) (E := E) base

abbrev normalizedStabilizer (base : IBr iota) : Subgroup E :=
  TypeBComponentReturnSourceInstantiation.orbitSetwiseStabilizer
    (fun c ↦ m c + 1) (Base m H) (Base m D)
    (normalizedRoot m H SH iota) (fun c ↦ diagonal (first m c))
    (normalizedAction m H SH outer) (characterEquiv m H SH iota base)

variable (pairs : PairEdges m H D SH SD diagonal)

include pairs in
/-- Canonical Brauer-character transport intertwines the actual original
diagonal action with the computed diagonal group equivalence. -/
theorem characterEquiv_diagonal (d : Original m D) (psi : IBr iota) :
    let _ := rightAutomorphismAction iota (coordinateMulAut H D diagonal)
    let _ := rightAutomorphismAction (normalizedRoot m H SH iota)
      (coordinateMulAut (fun i : Index m ↦ Base m H i.1)
        (fun i : Index m ↦ Base m D i.1) (fun i ↦ diagonal (first m i.1)))
    characterEquiv m H SH iota (d • psi) =
      productEquiv m D SD d • characterEquiv m H SH iota psi := by
  exact brauerAction_transport_of_square iota (productEquiv m H SH)
    (productEquiv m D SD).toMonoidHom
    (coordinateMulAut H D diagonal)
    (coordinateMulAut (fun i : Index m ↦ Base m H i.1)
      (fun i : Index m ↦ Base m D i.1) (fun i ↦ diagonal (first m i.1)))
    (fun d ↦ (normalized_diagonal m H D SH SD diagonal pairs d).symm) d psi

include pairs in
/-- The actual original and normalized character orbits have exactly the
same setwise stabiliser inside E. -/
theorem originalStabilizer_eq_normalized (base : IBr iota) :
    originalStabilizer m H D diagonal iota outer base =
      normalizedStabilizer m H D SH diagonal iota outer base := by
  letI := rightAutomorphismAction iota (coordinateMulAut H D diagonal)
  letI := rightAutomorphismAction iota outer
  letI := rightAutomorphismAction (normalizedRoot m H SH iota)
    (coordinateMulAut (fun i : Index m ↦ Base m H i.1)
      (fun i : Index m ↦ Base m D i.1) (fun i ↦ diagonal (first m i.1)))
  letI := rightAutomorphismAction (normalizedRoot m H SH iota)
    (normalizedAction m H SH outer)
  have hdiag : ∀ (d : Original m D) psi,
      characterEquiv m H SH iota (d • psi) =
        productEquiv m D SD d • characterEquiv m H SH iota psi := by
    intro d psi
    exact characterEquiv_diagonal m H D SH SD diagonal iota pairs d psi
  have houter : ∀ (e : E) psi,
      characterEquiv m H SH iota (e • psi) =
        e • characterEquiv m H SH iota psi := by
    intro e psi
    exact brauerAction_transport iota (productEquiv m H SH) outer e psi
  exact orbitStabilizer_eq (characterEquiv m H SH iota) (productEquiv m D SD)
    hdiag houter base

/-- The same orbit-stabiliser elements viewed in the normalized
presentation. This is the canonical equivalence of equal subgroups. -/
def stabilizerEquiv (base : IBr iota) :
    originalStabilizer m H D diagonal iota outer base ≃*
      normalizedStabilizer m H D SH diagonal iota outer base :=
  MulEquiv.subgroupCongr
    (originalStabilizer_eq_normalized m H D SH SD diagonal iota outer pairs base)

@[simp]
theorem stabilizerEquiv_value (base : IBr iota)
    (e : originalStabilizer m H D diagonal iota outer base) :
    (stabilizerEquiv m H D SH SD diagonal iota outer pairs base e).1 = e.1 := rfl

/-- Changing subgroup presentation preserves the selected generator. -/
theorem stabilizerEquiv_generator (base : IBr iota)
    (tau : originalStabilizer m H D diagonal iota outer base)
    (htau : Subgroup.zpowers tau = ⊤) :
    Subgroup.zpowers
      (stabilizerEquiv m H D SH SD diagonal iota outer pairs base tau) = ⊤ := by
  let e := stabilizerEquiv m H D SH SD diagonal iota outer pairs base
  have h := congrArg (Subgroup.map e.toMonoidHom) htau
  rw [MonoidHom.map_zpowers, Subgroup.map_top_of_surjective _ e.surjective] at h
  exact h

end ModularRep.PaperProofs.TypeBComponentReturnOriginalCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
