import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ProjectorNorm
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ProjectorActions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntegralProjector
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters
import ModularRep.BlockCentralCharacters
import ModularRep.CentralIdempotentBlockExpansion

/-! Ordinary selected values and uniform integral scalar descent identify
the actual role-two modular block idempotent. The descent law is deliberately
uniform in characters and integral central elements; it remains an external
ordinary/modular realization principle. All selected projector facts are proved. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
open scoped BigOperators MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ProjectorCoefficients
open ModularRep
open SporadicFi24P3Definition44NamedCarrierP3OrdinaryProjector
open SporadicFi24P3Definition44NamedCarrierP3ProjectorNorm
open SporadicFi24P3Definition44NamedCarrierP3ProjectorActions
open SporadicFi24P3Definition44NamedCarrierP3IntegralCoefficients
open SporadicFi24P3Definition44NamedCarrierP3IntegralProjector
open SporadicFi24P3Definition44NamedCarrierP3IdempotentData
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData

theorem centralIdempotent_eq_block_of_catalogue_values
    {k G B : Type*} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [Fintype B] [DecidableEq B]
    {e : B → k[G]} (blocks : BlockIdempotentDecomposition e)
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (c : GroupAlgebraCenter k G) (hc : IsIdempotentElem (c : k[G])) (b : B)
    (hvalue : ∀ j, catalogue.centralCharacter j c = if j = b then 1 else 0) :
    (c : k[G]) = e b := by
  classical
  have hcentral : IsMulCentral (c : k[G]) :=
    Set.mem_center_iff.mp
      (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp c.property))
  have hprod (j : B) : e j * (c : k[G]) = if j = b then e j else 0 := by
    rcases (blocks.primitive j).mul_eq_zero_or_eq_self_of_central_idempotent hc hcentral with hz | he
    · by_cases hj : j = b
      · subst j
        exfalso
        have hzc : blocks.blockIdempotentInCenter b * c = 0 := Subtype.ext hz
        have h := congrArg (catalogue.centralCharacter b) hzc
        have hv : catalogue.centralCharacter b c = 1 := by simpa using hvalue b
        rw [map_mul, map_zero, catalogue.centralCharacter_own, hv, one_mul] at h
        exact one_ne_zero h
      · simpa [hj] using hz
    · by_cases hj : j = b
      · simpa [hj] using he
      · exfalso
        have hec : blocks.blockIdempotentInCenter j * c = blocks.blockIdempotentInCenter j :=
          Subtype.ext he
        have h := congrArg (catalogue.centralCharacter j) hec
        have hv : catalogue.centralCharacter j c = 0 := by simpa [hj] using hvalue j
        rw [map_mul, catalogue.centralCharacter_own, hv, one_mul] at h
        exact zero_ne_one h
  calc
    (c : k[G]) = (∑ j : B, e j) * (c : k[G]) := by rw [blocks.complete.complete, one_mul]
    _ = ∑ j : B, e j * (c : k[G]) := by rw [Finset.sum_mul]
    _ = e b := by simp_rw [hprod]; simp

universe u
variable {k K G : Type u} {B : Type*}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype B]
variable {e : B → k[G]} (blocks : BlockIdempotentDecomposition e)
variable (catalogue : BlockCentralCharacterCatalogue blocks)

def IntegralScalarDescent
    (ordinaryBlock : OrdinaryIrreducibleCharacter.Irr K G → B) : Prop :=
  ∀ (chi : OrdinaryIrreducibleCharacter.Irr K G)
    (W : OrdinaryIrreducibleCharacter.Realisation K G chi.val)
    (a : GroupAlgebraCenter CoefficientRing G) (s : CoefficientRing),
    W.representation.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (toOrdinary (K := K)) a.val) =
      toOrdinary (K := K) s • (1 : Module.End K (Fin W.dimension → K)) →
    catalogue.centralCharacter (ordinaryBlock chi)
      (centerMap (toResidue (k := k)) a) = toResidue (k := k) s

theorem block_coefficients_of_selected_values
    (ordinaryBlock : OrdinaryIrreducibleCharacter.Irr K G → B)
    (roles : Fin 3 ≃ B) (C : FullOrdinaryDegreeTable K G)
    (allocation : ∀ r, ordinaryBlock (C.character r) = roles (blockLabels r))
    (rep : Fin 108 → G) (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (orders : ∀ c, Nat.card (Subgroup.centralizer ({rep c} : Set G)) = centralizerOrders c)
    (selectedForwardValues : ∀ c, (C.character 93).val (rep c) = (inverseCharacterValues c : K))
    (selectedInverseValues : ∀ c, (C.character 93).val ((rep c)⁻¹) = (inverseCharacterValues c : K))
    (scalarDescent : IntegralScalarDescent blocks catalogue ordinaryBlock) :
    ∀ c, (e (roles 2)).coeff (rep c) =
      (inverseCharacterValues c : k) / (7031383654400 : k) := by
  classical
  obtain ⟨W0⟩ := (C.character 0).property
  obtain ⟨W58⟩ := (C.character 58).property
  obtain ⟨W93⟩ := (C.character 93).property
  let : W0.representation.IsIrreducible := W0.irreducible
  let : W58.representation.IsIrreducible := W58.irreducible
  let : W93.representation.IsIrreducible := W93.irreducible
  have hdim (r : Fin 108)
      (W : OrdinaryIrreducibleCharacter.Realisation K G (C.character r).val) :
      Module.finrank K (Fin W.dimension → K) = degrees r := by
    apply Nat.cast_injective (R := K)
    exact (Representation.char_one W.representation).symm.trans
      ((congrFun W.character_eq 1).trans (C.degree r))
  have hforward : ∀ c, W93.representation.character (rep c) = (inverseCharacterValues c : K) := by
    intro c
    rw [W93.character_eq]
    exact selectedForwardValues c
  have hinverse : ∀ c, W93.representation.character ((rep c)⁻¹) = (inverseCharacterValues c : K) := by
    intro c
    rw [W93.character_eq]
    exact selectedInverseValues c
  have hnorm := selected_character_norm W93.representation rep cover orders C.groupOrder
    hforward hinverse
  obtain ⟨h93, he93⟩ := ordinaryProjector_action_one_and_idempotent_of_norm W93.representation hnorm
  have h0 := ordinaryProjector_action_zero_of_finrank_ne W93.representation W0.representation
    he93 (by rw [hdim 93 W93, hdim 0 W0]; decide)
  have h58 := ordinaryProjector_action_zero_of_finrank_ne W93.representation W58.representation
    he93 (by rw [hdim 93 W93, hdim 58 W58]; decide)
  have himage := integralProjector_map_eq W93.representation rep cover hinverse
    (hdim 93 W93) C.groupOrder (toOrdinary (K := K))
  have hz : integralProjector rep cover ∈ GroupAlgebraCenter CoefficientRing G :=
    mem_center_of_coeffMap_mem_center toOrdinary toOrdinary_injective _
      (by rw [himage]; exact (ordinaryProjectorInCenter W93.representation).property)
  let zO : GroupAlgebraCenter CoefficientRing G := ⟨integralProjector rep cover, hz⟩
  have heO : IsIdempotentElem zO.val :=
    idempotent_of_coeffMap_idempotent toOrdinary toOrdinary_injective _
      (by rw [himage]; exact he93)
  let c : GroupAlgebraCenter k G := centerMap toResidue zO
  have hec : IsIdempotentElem c.val := heO.map (MonoidAlgebra.mapRingHom G toResidue)
  have hv0 := scalarDescent (C.character 0) W0 zO 0 (by
    simpa only [map_zero, zero_smul, zO, himage] using h0)
  have hv58 := scalarDescent (C.character 58) W58 zO 0 (by
    simpa only [map_zero, zero_smul, zO, himage] using h58)
  have hv93 := scalarDescent (C.character 93) W93 zO 1 (by
    simpa only [map_one, one_smul, zO, himage] using h93)
  have ha0 : ordinaryBlock (C.character 0) = roles 0 := allocation 0
  have ha58 : ordinaryBlock (C.character 58) = roles 1 := allocation 58
  have ha93 : ordinaryBlock (C.character 93) = roles 2 := allocation 93
  rw [ha0, map_zero (toResidue (k := k))] at hv0
  rw [ha58, map_zero (toResidue (k := k))] at hv58
  rw [ha93, map_one (toResidue (k := k))] at hv93
  have hn0 : roles 0 ≠ roles 2 := fun h =>
    (show (0 : Fin 3) ≠ 2 from by decide) (roles.injective h)
  have hn1 : roles 1 ≠ roles 2 := fun h =>
    (show (1 : Fin 3) ≠ 2 from by decide) (roles.injective h)
  have hblock : c.val = e (roles 2) := by
    apply centralIdempotent_eq_block_of_catalogue_values blocks catalogue c hec (roles 2)
    intro b
    obtain ⟨j, rfl⟩ := roles.surjective b
    fin_cases j
    · change catalogue.centralCharacter (roles 0) c = if roles 0 = roles 2 then 1 else 0
      simpa only [if_neg hn0] using hv0
    · change catalogue.centralCharacter (roles 1) c = if roles 1 = roles 2 then 1 else 0
      simpa only [if_neg hn1] using hv58
    · change catalogue.centralCharacter (roles 2) c = if roles 2 = roles 2 then 1 else 0
      rw [if_pos rfl]
      exact hv93
  intro j
  rw [← hblock]
  exact integralProjector_map_coeff_at_rep W93.representation rep cover hinverse toResidue j

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ProjectorCoefficients


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
