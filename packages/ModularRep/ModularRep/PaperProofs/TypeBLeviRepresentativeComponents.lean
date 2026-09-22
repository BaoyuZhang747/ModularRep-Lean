import ModularRep.PaperProofs.TypeBComponentReturnActual
import ModularRep.PaperProofs.TypeBLemma47LeviApplication

/-!
# The component selector on the actual normal Levi subgroup

The accepted component-return deduction is applied once, then its actual
character is transported back to the prescribed root on N <= Gamma. The
diagonal quotient need not be faithful: surjectivity and a point-level
conjugation square identify the orbits. The same field action identifies
their setwise stabilizers, and fixation lifts the factorization to Gamma.

The product presentation, surjective diagonal map and its conjugation
square are intermediate outputs of the regular-Levi application. The
per-cycle representatives and their local factorization are intermediate
outputs of the factor selector application. They are not new external
sources for the final Levi representative theorem. No arbitrary-index
adapter is built here; the existing cycle presentation includes m = 0.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeComponents

open Formalisation
open TypeBComponentCycleNormalization TypeBRegularLeviCharacterActionAdapter
open TypeBComponentReturnOriginalCarriers TypeBComponentReturnCarrierTransport
open TypeBLemma47LeviApplication EvenFieldAssumption53Relative

section SurjectiveOrbitTransport

variable {A B E X Y : Type*} [Group A] [Group B] [Group E]
variable [MulAction A X] [MulAction B Y] [MulAction E X] [MulAction E Y]
variable (beta : X ≃ Y) (q : A →* B) (hq : Function.Surjective q)
variable (diagonal : ∀ a x, beta (a • x) = q a • beta x)

include hq diagonal in
theorem mem_orbit_iff_of_surjective (base x : X) :
    beta x ∈ MulAction.orbit B (beta base) ↔ x ∈ MulAction.orbit A base := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := hq b
    refine ⟨a, beta.injective ?_⟩
    rw [diagonal]
    exact hb
  · rintro ⟨a, rfl⟩
    exact ⟨q a, (diagonal a base).symm⟩

include hq diagonal in
theorem image_orbit_of_surjective (base : X) :
    beta '' MulAction.orbit A base = MulAction.orbit B (beta base) := by
  ext y
  obtain ⟨x, rfl⟩ := beta.surjective y
  rw [Set.mem_image_equiv, mem_orbit_iff_of_surjective beta q hq diagonal]
  simp

include hq diagonal in
theorem orbitStabilizer_eq_of_surjective
    (outer : ∀ (e : E) (x : X), beta (e • x) = e • beta x) (base : X) :
    orbitStabilizer (D := A) (E := E) base =
      orbitStabilizer (D := B) (E := E) (beta base) := by
  ext e
  change (fun x : X ↦ e • x) '' MulAction.orbit A base =
      MulAction.orbit A base ↔
    (fun y : Y ↦ e • y) '' MulAction.orbit B (beta base) =
      MulAction.orbit B (beta base)
  have hcomm : beta '' ((fun x : X ↦ e • x) '' MulAction.orbit A base) =
      (fun y : Y ↦ e • y) '' (beta '' MulAction.orbit A base) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    exact outer e x
  constructor
  · intro h
    rw [← image_orbit_of_surjective beta q hq diagonal base, ← hcomm, h]
  · intro h
    apply Set.image_injective.mpr beta.injective
    rw [hcomm, image_orbit_of_surjective beta q hq diagonal base, h]

end SurjectiveOrbitTransport

section CharacterTransport

variable {k K G P : Type}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group P] [Finite P]

abbrev productRoot (root : PrimeRegularRootEmbedding 2 k K G) (equiv : G ≃* P) :=
  root.alongMulEquiv equiv

abbrev toProductCharacter (root : PrimeRegularRootEmbedding 2 k K G) (equiv : G ≃* P) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv root equiv

end CharacterTransport

section ActualCarriers

variable {Gamma E k K : Type}
variable [Group Gamma] [Finite Gamma] [Group E] [Finite E] [IsCyclic E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (N : Subgroup Gamma) [N.Normal]
variable (iotaN : PrimeRegularRootEmbedding 2 k K N)
variable (field : E →* MulAut Gamma)
variable (hNstable : ∀ e : E, ∀ g : Gamma, g ∈ N ↔ field e g ∈ N)

/-- The setwise stabilizer of the actual Gamma-orbit in the prescribed N
set of characters. It is a subgroup of the original field group E. -/
def actualOrbitStabilizer (theta0 : IBr iotaN) : Subgroup E := by
  letI := ambientBrauerAction N iotaN
  letI := fieldBrauerAction N iotaN field hNstable
  exact orbitStabilizer (D := Gamma) (E := E) theta0

/-- The product action is defined from the same ambient field action. -/
def productField {P : Type} [Group P] [Finite P] (equiv : N ≃* P) : E →* MulAut P :=
  transportedAut equiv (restrictAutomorphismHom N field hNstable)

variable {C : Type} [Fintype C]
variable (m : C → ℕ) (H D : Index m → Type)
variable [∀ i, Group (H i)] [∀ i, Finite (H i)] [∀ i, Group (D i)]
variable (e : N ≃* Original m H)

variable (diagonal : ∀ i, D i →* MulAut (H i))
variable (q : Gamma →* Original m D) (hq : Function.Surjective q)
variable (groupSquare : ∀ g : Gamma,
  MulAut.congr e (MulAut.conjNormal (H := N) g) = coordinateMulAut H D diagonal (q g))

include groupSquare in
theorem diagonal_transport (g : Gamma) (theta : IBr iotaN) :
    let _ := ambientBrauerAction N iotaN
    let _ := rightAutomorphismAction (productRoot iotaN e) (coordinateMulAut H D diagonal)
    toProductCharacter iotaN e (g • theta) = q g • toProductCharacter iotaN e theta := by
  exact brauerAction_transport_of_square iotaN e q
    (MulAut.conjNormal (H := N)) (coordinateMulAut H D diagonal)
    (fun g ↦ (groupSquare g).symm) g theta

theorem field_transport (a : E) (theta : IBr iotaN) :
    let _ := fieldBrauerAction N iotaN field hNstable
    let _ := rightAutomorphismAction (productRoot iotaN e) (productField N field hNstable e)
    toProductCharacter iotaN e (a • theta) = a • toProductCharacter iotaN e theta := by
  exact brauerAction_transport iotaN e (restrictAutomorphismHom N field hNstable) a theta

include hq groupSquare in
theorem actual_mem_orbit_iff (theta0 theta : IBr iotaN) :
    let _ := ambientBrauerAction N iotaN
    let _ := rightAutomorphismAction (productRoot iotaN e) (coordinateMulAut H D diagonal)
    toProductCharacter iotaN e theta ∈ MulAction.orbit (Original m D)
      (toProductCharacter iotaN e theta0) ↔ theta ∈ MulAction.orbit Gamma theta0 := by
  letI := ambientBrauerAction N iotaN
  letI := rightAutomorphismAction (productRoot iotaN e) (coordinateMulAut H D diagonal)
  exact mem_orbit_iff_of_surjective (toProductCharacter iotaN e) q hq
    (diagonal_transport N iotaN m H D e diagonal q groupSquare) theta0 theta

include hq groupSquare in
theorem actualOrbitStabilizer_eq (theta0 : IBr iotaN) :
    actualOrbitStabilizer N iotaN field hNstable theta0 =
      originalStabilizer m H D diagonal (productRoot iotaN e)
        (productField N field hNstable e) (toProductCharacter iotaN e theta0) := by
  letI := ambientBrauerAction N iotaN
  letI := fieldBrauerAction N iotaN field hNstable
  letI := rightAutomorphismAction (productRoot iotaN e) (coordinateMulAut H D diagonal)
  letI := rightAutomorphismAction (productRoot iotaN e) (productField N field hNstable e)
  exact orbitStabilizer_eq_of_surjective (toProductCharacter iotaN e) q hq
    (diagonal_transport N iotaN m H D e diagonal q groupSquare)
    (field_transport N iotaN field hNstable m H e) theta0

variable (SH : CycleCoordinates m H) (SD : CycleCoordinates m D)
variable (pairs : PairEdges m H D SH SD diagonal)
variable (factorRoot : ∀ c, PrimeRegularRootEmbedding 2 k K (Base m H c))
variable (source : TypeBFiniteProductNaturality.ExternalProductData
  (fun i : Index m ↦ Base m H i.1) (normalizedRoot m H SH (productRoot iotaN e))
  (fun i ↦ factorRoot i.1))
variable (phi : E →* MulAut (Original m D))
variable (normalises : AutomorphismSemidirectCompatible
  (coordinateMulAut H D diagonal) (productField N field hNstable e) phi)
variable (theta0 : IBr iotaN)

abbrev productOrbitStabilizer :=
  originalStabilizer m H D diagonal (productRoot iotaN e)
    (productField N field hNstable e) (toProductCharacter iotaN e theta0)

variable (tau : productOrbitStabilizer N iotaN field hNstable m H D e diagonal theta0)
variable (hH : MonomialAction m H SH
  (((productField N field hNstable e).comp
    (productOrbitStabilizer N iotaN field hNstable m H D e diagonal theta0).subtype) tau⁻¹))
variable (hD : MonomialAction m D SD
  ((phi.comp (productOrbitStabilizer N iotaN field hNstable m H D e diagonal theta0).subtype) tau⁻¹))

abbrev localH (c : C) :=
  TypeBComponentReturnRestriction.returnAction m H SH
    ((productField N field hNstable e).comp
      (productOrbitStabilizer N iotaN field hNstable m H D e diagonal theta0).subtype) tau hH c

abbrev localD (c : C) :=
  TypeBComponentReturnRestriction.returnAction m D SD
    (phi.comp (productOrbitStabilizer N iotaN field hNstable m H D e diagonal theta0).subtype) tau hD c

include hq groupSquare pairs in
/-- The accepted component selector, on the original N character and the
actual Gamma and field actions. All global orbit/fixation/factorization
conclusions are derived; only the per-cycle selector is supplied here. -/
theorem exists_actual_fixed_constituent
    (htau : Subgroup.zpowers tau = ⊤)
    (representative : ∀ c, IBr (factorRoot c))
    (representative_orbit : ∀ c,
      let _ := rightAutomorphismAction (factorRoot c) (diagonal (first m c))
      representative c ∈ MulAction.orbit (Base m D c)
        (source.characters (characterEquiv m H SH (productRoot iotaN e)
          (toProductCharacter iotaN e theta0)) (first m c)))
    (local_factorisation : ∀ c,
      let _ := rightAutomorphismAction (factorRoot c) (diagonal (first m c))
      let _ := rightAutomorphismAction (factorRoot c)
        (localH N iotaN field hNstable m H D e diagonal SH theta0 tau hH c)
      SemidirectStabilizerFactors
        (localD N iotaN field hNstable m H D e diagonal SD phi theta0 tau hD c)
        (brauerRightActions_semidirectCompatible (factorRoot c)
          (diagonal (first m c))
          (localH N iotaN field hNstable m H D e diagonal SH theta0 tau hH c)
          (localD N iotaN field hNstable m H D e diagonal SD phi theta0 tau hD c)
          (TypeBComponentReturnRestriction.return_actions_compatible m H D SH SD diagonal
            ((productField N field hNstable e).comp
              (productOrbitStabilizer N iotaN field hNstable m H D e diagonal theta0).subtype)
            (phi.comp (productOrbitStabilizer N iotaN field hNstable m H D e diagonal theta0).subtype)
            tau hH hD (fun a d ↦ normalises a.1 d) c)) (representative c)) :
    let _ := ambientBrauerAction N iotaN
    let EO := actualOrbitStabilizer N iotaN field hNstable theta0
    let fieldO := field.comp EO.subtype
    let stableO := fun a : EO ↦ hNstable a.1
    let _ := fieldBrauerAction N iotaN fieldO stableO
    ∃ theta : IBr iotaN,
      theta ∈ MulAction.orbit Gamma theta0 ∧
      (∀ a : EO, a • theta = theta) ∧
      SemidirectStabilizerFactors fieldO
        (field_ambient_semidirect_compatible N iotaN fieldO stableO) theta := by
  let beta := toProductCharacter iotaN e
  let EO := actualOrbitStabilizer N iotaN field hNstable theta0
  let fieldO := field.comp EO.subtype
  let stableO := fun a : EO ↦ hNstable a.1
  letI := ambientBrauerAction N iotaN
  letI := fieldBrauerAction N iotaN fieldO stableO
  letI := rightAutomorphismAction (productRoot iotaN e) (coordinateMulAut H D diagonal)
  letI := rightAutomorphismAction (productRoot iotaN e)
    ((productField N field hNstable e).comp
      (productOrbitStabilizer N iotaN field hNstable m H D e diagonal theta0).subtype)
  obtain ⟨y, hy, hfixed, _⟩ :=
    TypeBComponentReturnActual.component_return_actual m H D SH SD diagonal pairs
      (productRoot iotaN e) factorRoot source (productField N field hNstable e)
      phi normalises (beta theta0) tau hH hD htau representative
      representative_orbit local_factorisation
  have horbit : beta.symm y ∈ MulAction.orbit Gamma theta0 := by
    apply (actual_mem_orbit_iff N iotaN m H D e diagonal q hq groupSquare theta0 _).mp
    simpa only [beta, Equiv.apply_symm_apply] using hy
  have hthetaFixed : ∀ a : EO, a • beta.symm y = beta.symm y := by
    intro a
    have ha : a.1 ∈ productOrbitStabilizer N iotaN field hNstable m H D e diagonal theta0 := by
      unfold productOrbitStabilizer
      rw [← actualOrbitStabilizer_eq N iotaN field hNstable m H D e diagonal q hq groupSquare theta0]
      exact a.2
    let a' : productOrbitStabilizer N iotaN field hNstable m H D e diagonal theta0 := ⟨a.1, ha⟩
    apply beta.injective
    have htransport := field_transport N iotaN field hNstable m H e a.1 (beta.symm y)
    change beta (a • beta.symm y) = a' • beta (beta.symm y) at htransport
    rw [htransport, beta.apply_symm_apply]
    exact hfixed a'
  refine ⟨beta.symm y, horbit, hthetaFixed, ?_⟩
  exact mem_semidirect_stabilizer_iff fieldO
    (field_ambient_semidirect_compatible N iotaN fieldO stableO)
    (beta.symm y) hthetaFixed

end ActualCarriers

end ModularRep.PaperProofs.TypeBLeviRepresentativeComponents


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
