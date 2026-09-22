import ModularRep.PaperProofs.OddTwoActualStabilizerTriple

/-!
# Actual coordinates between selected automorphism images

Selection of a representative from an ambient weight class is not equivariant.
The two quotient relations instead produce an actual inner conjugator. The
resulting holomorph element retains both that conjugator and the specified
automorphism, and transports the actual raw and Brauer stabilizers.

All results here are K. No relation covariance, independent root equality,
character extension or block-triple conclusion is an input or output.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple

universe u

section GroupCoordinates

variable {H : Type u} [Group H]

/-- The actual holomorph with its identity automorphism action. -/
abbrev CoordinateHolomorph (H : Type u) [Group H] :=
  H ⋊[MonoidHom.id (MulAut H)] MulAut H

/-- The inner correction followed by the given actual automorphism. -/
def coordinateAutomorphism (g : H) (a : MulAut H) : MulAut H :=
  MulAut.conj g * a

@[simp] theorem coordinateAutomorphism_apply (g : H) (a : MulAut H) (x : H) :
    coordinateAutomorphism g a x = g * a x * g⁻¹ := rfl

/-- The same two coordinates in the actual holomorph. -/
def coordinateElement (g : H) (a : MulAut H) : CoordinateHolomorph H :=
  SemidirectProduct.inl g * SemidirectProduct.inr a

@[simp] theorem coordinateElement_left (g : H) (a : MulAut H) :
    (coordinateElement g a).left = g := by
  simp [coordinateElement]

@[simp] theorem coordinateElement_right (g : H) (a : MulAut H) :
    (coordinateElement g a).right = a := by
  simp [coordinateElement]

theorem coordinateElement_automorphism (g : H) (a : MulAut H) :
    semidirectToMulAut (MonoidHom.id (MulAut H)) (coordinateElement g a) =
      coordinateAutomorphism g a := by
  simp [coordinateElement, coordinateAutomorphism]

/-- The ambient map is actual conjugation by the constructed element. -/
def coordinateHolomorphEquiv (g : H) (a : MulAut H) :
    CoordinateHolomorph H ≃* CoordinateHolomorph H :=
  MulAut.conj (coordinateElement g a)

/-- Its base restriction is exactly x -> g*a(x)*g^-1. -/
theorem coordinateHolomorphEquiv_inl (g : H) (a : MulAut H) (x : H) :
    coordinateHolomorphEquiv g a (SemidirectProduct.inl x) =
      SemidirectProduct.inl (g * a x * g⁻¹) := by
  change coordinateElement g a * SemidirectProduct.inl x * (coordinateElement g a)⁻¹ = _
  apply SemidirectProduct.ext
  · simp [coordinateElement, mul_assoc]
  · simp [coordinateElement]

end GroupCoordinates

section RawCoordinates

variable {p : ℕ} {K H : Type u}
variable [Field K] [CharZero K] [Group H] [Fintype H]

/-- The two actual quotient maps defining an ambient weight class. -/
def weightClass (W : CharacterWeight p K H) :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H) :=
  Quotient.mk'' (Quotient.mk'' W)

/-- An equality of the actual classes supplies an inner conjugator and
equality of the entire raw pair, including its OWN ordinary character. -/
theorem exists_coordinate_of_class_eq (W V : CharacterWeight p K H)
    (a : MulAut H)
    (hclass : weightClass V =
      rightTwistConjugacyClass a⁻¹ (weightClass W)) :
    ∃ g : H, W.rightTwist (coordinateAutomorphism g a)⁻¹ = V := by
  have horbit :
      (Quotient.mk'' (Quotient.mk'' V) :
        CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H)) =
      Quotient.mk'' (Quotient.mk'' (W.rightTwist a⁻¹)) := hclass
  rcases Quotient.exact horbit with ⟨g, hg⟩
  have hraw : (W.rightTwist a⁻¹).rightTwist (MulAut.conj g⁻¹) = V := by
    apply CharacterWeight.eq_of_isomorphic
    exact Quotient.exact hg
  have hcombine := CharacterWeight.eq_of_isomorphic
    (rightTwist_mul_isomorphic W a⁻¹ (MulAut.conj g⁻¹))
  have hproduct : a⁻¹ * MulAut.conj g⁻¹ = (coordinateAutomorphism g a)⁻¹ := by
    simp [coordinateAutomorphism]
  refine ⟨g, ?_⟩
  rw [← hproduct, ← hcombine]
  exact hraw

/-- A witness chosen only from the proved equality of actual quotient classes. -/
def classConjugator (W V : CharacterWeight p K H) (a : MulAut H)
    (hclass : weightClass V = rightTwistConjugacyClass a⁻¹ (weightClass W)) : H :=
  Classical.choose (exists_coordinate_of_class_eq W V a hclass)

theorem classConjugator_spec (W V : CharacterWeight p K H) (a : MulAut H)
    (hclass : weightClass V = rightTwistConjugacyClass a⁻¹ (weightClass W)) :
    W.rightTwist (coordinateAutomorphism (classConjugator W V a hclass) a)⁻¹ = V :=
  Classical.choose_spec (exists_coordinate_of_class_eq W V a hclass)

/-- The literal subgroup map follows from the equality of raw pairs. -/
theorem coordinate_subgroup (W V : CharacterWeight p K H) (g : H) (a : MulAut H)
    (hpair : W.rightTwist (coordinateAutomorphism g a)⁻¹ = V) :
    W.subgroup.map (coordinateAutomorphism g a).toMonoidHom = V.subgroup := by
  rw [← hpair]
  exact Subgroup.map_equiv_eq_comap_symm' (coordinateAutomorphism g a) W.subgroup

/-- The canonical raw action is the same inverse automorphism transport. -/
theorem coordinateElement_raw_smul (W : CharacterWeight p K H) (g : H) (a : MulAut H) :
    letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut H))
    coordinateElement g a • (Quotient.mk'' W : RawWeightClass (p := p) (K := K) (H := H)) =
      Quotient.mk'' (W.rightTwist (coordinateAutomorphism g a)⁻¹) := by
  letI := canonicalRawHAction (p := p) (K := K) (H := H)
  letI := canonicalRawEAction (p := p) (K := K) (MonoidHom.id (MulAut H))
  letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut H))
  rw [coordinateElement, mul_smul, semidirect_inr_smul, semidirect_inl_smul]
  change rightTwistIsoClass (MulAut.conj g⁻¹)
    (rightTwistIsoClass a⁻¹ (Quotient.mk'' W)) = _
  rw [rightTwistIsoClass_mul]
  have hproduct : a⁻¹ * MulAut.conj g⁻¹ = (coordinateAutomorphism g a)⁻¹ := by
    simp [coordinateAutomorphism]
  rw [hproduct]
  rfl

/-- Equality of the complete raw pair gives the exact stabilizer image.
The hypothesis is supplied by classConjugator_spec for selected pairs. -/
theorem rawStabilizer_coordinate_image (W V : CharacterWeight p K H)
    (g : H) (a : MulAut H)
    (hpair : W.rightTwist (coordinateAutomorphism g a)⁻¹ = V) :
    (rawStabilizer (MonoidHom.id (MulAut H)) W).map
        (coordinateHolomorphEquiv g a).toMonoidHom =
      rawStabilizer (MonoidHom.id (MulAut H)) V := by
  letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut H))
  have hraw := coordinateElement_raw_smul W g a
  rw [hpair] at hraw
  change (MulAction.stabilizer (CoordinateHolomorph H) (Quotient.mk'' W)).map
    (MulAut.conj (coordinateElement g a)).toMonoidHom =
      MulAction.stabilizer (CoordinateHolomorph H) (Quotient.mk'' V)
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hraw]

end RawCoordinates

section SelectedFibre

variable {p : ℕ} {k K H A Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group A] [Fintype Block]
variable [MulAction (MulAut H)ᵐᵒᵖ Block]
variable (rho : A →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := Block))
variable (block : Block) (hfixed : ∀ a : A, inverseOpHom rho a • block = block)

/-- The actual fibre action supplies the class equality; selection supplies
only a representative, so the resulting inner correction is retained. -/
theorem exists_selected_coordinate (a : A) (w : WeightFibre blockSource block) :
    letI := rightWeightFibreMulAction rho blockSource block hfixed
    ∃ g : H,
      (selectedCharacterWeight blockSource block w).rightTwist
          (coordinateAutomorphism g (rho a))⁻¹ =
        selectedCharacterWeight blockSource block (a • w) := by
  letI := rightWeightFibreMulAction rho blockSource block hfixed
  apply exists_coordinate_of_class_eq
  change weightClass (selectedCharacterWeight blockSource block (a • w)) =
    rightTwistConjugacyClass (rho a)⁻¹
      (weightClass (selectedCharacterWeight blockSource block w))
  rw [show weightClass (selectedCharacterWeight blockSource block (a • w)) =
      (a • w).1 from selectedCharacterWeight_spec blockSource block (a • w),
    show weightClass (selectedCharacterWeight blockSource block w) = w.1 from
      selectedCharacterWeight_spec blockSource block w]
  have h := rightWeightFibre_smul_val rho blockSource block hfixed a w
  dsimp only at h
  change (a • w).1 = rightTwistConjugacyClass (rho a⁻¹) w.1 at h
  simpa only [map_inv] using h

end SelectedFibre

section BrauerCoordinates

variable {p : ℕ} {k K H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H]
variable (iota : PrimeRegularRootEmbedding p k K H)

/-- The correction by an inner element leaves the global character action
equal to the given automorphism's inverse/op action. -/
theorem coordinateElement_brauer_smul (g : H) (a : MulAut H) (psi : IBr iota) :
    letI := actualBrauerAction iota (MonoidHom.id (MulAut H))
    coordinateElement g a • psi = MulOpposite.op a⁻¹ • psi := by
  letI := rightAutomorphismAction (X := IBr iota) (MulAut.conj : H →* MulAut H)
  letI := rightAutomorphismAction (X := IBr iota) (MonoidHom.id (MulAut H))
  letI := actualBrauerAction iota (MonoidHom.id (MulAut H))
  rw [coordinateElement, mul_smul, semidirect_inr_smul, semidirect_inl_smul]
  exact inner_fixes_ibr iota g (MulOpposite.op a⁻¹ • psi)

/-- The SAME conjugation map transports the actual global stabilizer. -/
theorem globalStabilizer_coordinate_image (g : H) (a : MulAut H) (psi : IBr iota) :
    (globalStabilizer iota (MonoidHom.id (MulAut H)) psi).map
        (coordinateHolomorphEquiv g a).toMonoidHom =
      globalStabilizer iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) := by
  letI := actualBrauerAction iota (MonoidHom.id (MulAut H))
  change (MulAction.stabilizer (CoordinateHolomorph H) psi).map
    (MulAut.conj (coordinateElement g a)).toMonoidHom =
      MulAction.stabilizer (CoordinateHolomorph H) (MulOpposite.op a⁻¹ • psi)
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [coordinateElement_brauer_smul]

end BrauerCoordinates

end ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
