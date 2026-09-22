import ModularRep.IntegralBasicSetBridge
import ModularRep.RepresentationScalarChange
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Paper proofs: Conlon marks and integral basic sets

This file states the permutation-lattice argument in the form used in
Corollary 2.7 and Lemma 2.8 of the accompanying manuscript.

The two published inputs are kept separate.  `PadicConlonMarkDetection` is
the forward implication of Conlon's theorem for permutation lattices over the
`p`-adic integers, and `PublishedBurnsideMarkInjectivity` is injectivity of
the global mark map on isomorphism classes of all finite `A`-sets in the
chosen universe.  Neither input contains the desired equivariant equivalence
of the two finite sets.
-/

open scoped MonoidAlgebra TensorProduct

namespace ModularRep.PaperProofs.ConlonBasicSet

open ModularRep.IntegralBasicSetBridge

universe uR uS uA uV uW uX uY

section ScalarExtension

variable {R : Type uR} {S : Type uS} {A : Type uA}
variable {V : Type uV} {W : Type uW}
variable [CommSemiring R] [Semiring S] [Algebra R S] [Monoid A]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]

/-- Extension of scalars preserves an equivalence of representations. -/
noncomputable def representationEquivBaseChange
    {rho : Representation R A V} {sigma : Representation R A W}
    (e : rho.Equiv sigma) :
    (rho.baseChange S).Equiv (sigma.baseChange S) :=
  Representation.Equiv.mk (e.toLinearEquiv.baseChange R S) (by
    intro a
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s v =>
        change s ⊗ₜ[R] e.toLinearEquiv (rho a v) =
          s ⊗ₜ[R] sigma a (e.toLinearEquiv v)
        exact congrArg (fun w : W => s ⊗ₜ[R] w)
          (DFunLike.congr_fun (e.toIntertwiningMap.isIntertwining' a) v)
    | add x y hx hy => simp only [map_add, hx, hy])

variable {X : Type uX} [MulAction A X]

/-- The scalar extension of a permutation module is canonically the
permutation module over the larger coefficient ring. -/
noncomputable def permutationModuleBaseChangeEquiv :
    ((Representation.ofMulAction R A X).baseChange S).Equiv
      (Representation.ofMulAction S A X) :=
  by
    classical
    let coeffR : MonoidAlgebra R X ≃ₗ[R] (X →₀ R) :=
      MonoidAlgebra.coeffLinearEquiv R
    let canonical :
        S ⊗[R] MonoidAlgebra R X ≃ₗ[S] MonoidAlgebra S X :=
      (coeffR.baseChange R S) ≪≫ₗ
        TensorProduct.finsuppScalarRight R S S X ≪≫ₗ
        (MonoidAlgebra.coeffLinearEquiv S).symm
    exact Representation.Equiv.mk
      canonical (by
      intro a
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s v =>
          induction v using MonoidAlgebra.induction_linear with
          | zero => simp
          | add v w hv hw =>
              simp only [TensorProduct.tmul_add, map_add, hv, hw]
          | single x r =>
              have hcanonical (z : X) (t : R) :
                  canonical (s ⊗ₜ[R] MonoidAlgebra.single z t) =
                    MonoidAlgebra.single z (t • s) := by
                ext y
                simp [canonical, coeffR,
                  TensorProduct.finsuppScalarRight_apply_tmul_apply,
                  Finsupp.single_apply]
              change
                canonical
                    (s ⊗ₜ[R]
                      (Representation.ofMulAction R A X) a
                        (MonoidAlgebra.single x r)) =
                  (Representation.ofMulAction S A X) a
                    (canonical (s ⊗ₜ[R] MonoidAlgebra.single x r))
              rw [Representation.ofMulAction_single,
                hcanonical, hcanonical, Representation.ofMulAction_single]
      | add x y hx hy => simp only [map_add, hx, hy])

variable {Y : Type uY} [MulAction A Y]

/-- An equivalence of integral permutation lattices remains an equivalence
after any extension of the coefficient ring. -/
noncomputable def permutationLatticeEquivBaseChange
    (e : (Representation.ofMulAction R A X).Equiv
      (Representation.ofMulAction R A Y)) :
    (Representation.ofMulAction S A X).Equiv
      (Representation.ofMulAction S A Y) :=
  (permutationModuleBaseChangeEquiv
      (R := R) (S := S) (A := A) (X := X)).symm |>.trans
    ((representationEquivBaseChange (S := S) e).trans
      (permutationModuleBaseChangeEquiv
        (R := R) (S := S) (A := A) (X := Y)))

end ScalarExtension

section PublishedMarks

variable {A : Type uA} [Group A]

/-- A finite `A`-set with its action stored as data.  Storing the action
allows the global Burnside mark map below to range over all finite actions,
including distinct actions on the same carrier type. -/
structure FiniteActionSet (A : Type uA) [Group A] where
  Carrier : Type uX
  action : MulAction A Carrier
  finite : Finite Carrier

namespace FiniteActionSet

/-- Bundle an existing finite type with its existing `A`-action. -/
def of (X : Type uX) [MulAction A X] [Finite X] : FiniteActionSet A where
  Carrier := X
  action := inferInstance
  finite := inferInstance

/-- The stored action, used without installing a global typeclass instance. -/
def smul (P : FiniteActionSet A) (a : A) (x : P.Carrier) : P.Carrier :=
  let _ : MulAction A P.Carrier := P.action
  a • x

/-- The permutation representation attached to a bundled finite `A`-set. -/
noncomputable def permutationRepresentation (R : Type uR) [Semiring R]
    (P : FiniteActionSet A) :
    Representation R A (MonoidAlgebra R P.Carrier) :=
  let _ : MulAction A P.Carrier := P.action
  Representation.ofMulAction R A P.Carrier

/-- Fixed points for the explicitly stored action. -/
def FixedPoints (P : FiniteActionSet A) (U : Subgroup A) :=
  {x : P.Carrier // ∀ u : U, P.smul (u : A) x = x}

/-- The mark of a bundled finite `A`-set at a subgroup. -/
noncomputable def mark (P : FiniteActionSet A) (U : Subgroup A) : ℕ :=
  let _ : Finite P.Carrier := P.finite
  Nat.card (P.FixedPoints U)

/-- Equivariant equivalence for two explicitly stored actions. -/
def IsEquivariantlyEquivalent (P Q : FiniteActionSet A) : Prop :=
  ∃ e : P.Carrier ≃ Q.Carrier,
    ∀ (a : A) (x : P.Carrier), e (P.smul a x) = Q.smul a (e x)

/-- The inverse of an equivariant equivalence for stored actions is
equivariant. -/
theorem equivariant_symm {P Q : FiniteActionSet A}
    (e : P.Carrier ≃ Q.Carrier)
    (he : ∀ (a : A) (x : P.Carrier),
      e (P.smul a x) = Q.smul a (e x)) :
    ∀ (a : A) (y : Q.Carrier),
      e.symm (Q.smul a y) = P.smul a (e.symm y) := by
  intro a y
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- Equivariant equivalence of stored finite actions is an equivalence
relation. -/
def setoid : Setoid (FiniteActionSet A) where
  r := IsEquivariantlyEquivalent
  iseqv := by
    constructor
    · intro P
      exact ⟨Equiv.refl _, fun _ _ ↦ rfl⟩
    · intro P Q h
      obtain ⟨e, he⟩ := h
      exact ⟨e.symm, equivariant_symm e he⟩
    · intro P Q T hPQ hQT
      obtain ⟨e, he⟩ := hPQ
      obtain ⟨f, hf⟩ := hQT
      refine ⟨e.trans f, ?_⟩
      intro a x
      exact (congrArg f (he a x)).trans (hf a (e x))

/-- An equivariant equivalence restricts to an equivalence of fixed-point
types for every subgroup. -/
noncomputable def fixedPointsEquiv {P Q : FiniteActionSet A}
    (e : P.Carrier ≃ Q.Carrier)
    (he : ∀ (a : A) (x : P.Carrier),
      e (P.smul a x) = Q.smul a (e x))
    (U : Subgroup A) : P.FixedPoints U ≃ Q.FixedPoints U where
  toFun x := ⟨e x.1, by
    intro u
    calc
      Q.smul (u : A) (e x.1) = e (P.smul (u : A) x.1) :=
        (he (u : A) x.1).symm
      _ = e x.1 := congrArg e (x.property u)⟩
  invFun y := ⟨e.symm y.1, by
    intro u
    calc
      P.smul (u : A) (e.symm y.1) = e.symm (Q.smul (u : A) y.1) :=
        (equivariant_symm e he (u : A) y.1).symm
      _ = e.symm y.1 := congrArg e.symm (y.property u)⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1

/-- Equivariantly equivalent bundled finite actions have equal marks. -/
theorem mark_eq_of_equivariant {P Q : FiniteActionSet A}
    (h : IsEquivariantlyEquivalent P Q) (U : Subgroup A) :
    P.mark U = Q.mark U := by
  obtain ⟨e, he⟩ := h
  exact Nat.card_congr (fixedPointsEquiv e he U)

/-- The global Burnside mark map on equivariant isomorphism classes of all
finite `A`-sets in the chosen universe. -/
noncomputable def markMap :
    Quotient (setoid (A := A)) → Subgroup A → ℕ :=
  Quotient.lift (fun P ↦ P.mark) (by
    intro P Q h
    funext U
    exact mark_eq_of_equivariant h U)

end FiniteActionSet

/-- Source-shaped global form of Conlon mark detection (Conlon 1968, in the
form of Bouc 2000, Theorem 3.5.5).  It is quantified over arbitrary finite
`A`-sets rather than specialised to the pair in the manuscript conclusion. -/
def PadicConlonMarkDetection (p : ℕ) [Fact p.Prime] [Finite A] : Prop :=
  ∀ P Q : FiniteActionSet.{uA, uX} A,
    Nonempty
        ((P.permutationRepresentation ℤ_[p]).Equiv
          (Q.permutationRepresentation ℤ_[p])) →
      ∀ U : Subgroup A, IsPHypoelementary p U →
        P.mark U = Q.mark U

/-- Source-shaped global injectivity of the Burnside mark homomorphism (Bouc
2000, Theorem 2.3.2 and Section 3.2).  Its domain contains all finite `A`-sets
in the chosen universe, not just the two actions appearing in the desired
conclusion. -/
def PublishedBurnsideMarkInjectivity [Finite A] : Prop :=
  Function.Injective (FiniteActionSet.markMap.{uA, uX} (A := A))

end PublishedMarks

section Marks

variable {p : ℕ} {A : Type uA} {X Y : Type uX}
variable [Group A] [MulAction A X] [MulAction A Y]

/-- Corollary 2.7 (`cor:conlon-mark`) of the current manuscript: for a finite
`p`-hypoelementary group, an isomorphism of the two `p`-adic permutation
lattices implies an isomorphism of the underlying finite `A`-sets.

The two theorem parameters are precisely the published Conlon detection and
Burnside mark-injectivity inputs used by the paper. -/
theorem corollary_2_4_conlonMark [Fact p.Prime]
    [Finite A] [Finite X] [Finite Y]
    (ambientHypoelementary : IsPHypoelementary p A)
    (latticeEquiv : Nonempty
      ((Representation.ofMulAction ℤ_[p] A X).Equiv
        (Representation.ofMulAction ℤ_[p] A Y)))
    (conlon : PadicConlonMarkDetection.{uA, uX} (p := p) (A := A))
    (burnside : PublishedBurnsideMarkInjectivity.{uA, uX} (A := A)) :
    ∃ e : X ≃ Y, IsEquivariantSetEquiv (A := A) e := by
  let setX : FiniteActionSet A := FiniteActionSet.of (A := A) X
  let setY : FiniteActionSet A := FiniteActionSet.of (A := A) Y
  have latticeEquiv' : Nonempty
      ((setX.permutationRepresentation ℤ_[p]).Equiv
        (setY.permutationRepresentation ℤ_[p])) := by
    exact latticeEquiv
  have allMarks : ∀ U : Subgroup A, setX.mark U = setY.mark U := by
    intro U
    exact conlon setX setY latticeEquiv' U
      (isPHypoelementary_subgroup p ambientHypoelementary U)
  have marksEqual :
      FiniteActionSet.markMap
          (Quotient.mk (FiniteActionSet.setoid (A := A)) setX) =
        FiniteActionSet.markMap
          (Quotient.mk (FiniteActionSet.setoid (A := A)) setY) := by
    funext U
    exact allMarks U
  have classesEqual := burnside marksEqual
  have related : FiniteActionSet.IsEquivariantlyEquivalent setX setY :=
    Quotient.exact classesEqual
  obtain ⟨e, he⟩ := related
  let eXY : X ≃ Y := e
  refine ⟨eXY, ?_⟩
  intro a x
  have h := he a x
  change eXY (a • x) = a • eXY x at h
  exact h

/-- Lemma 2.8 (`lem:basicset-bridge`) of the current manuscript in its exact
permutation-lattice form.  The restricted decomposition map is an integral
linear equivalence and is assumed to commute with the stated actions.  Lean
then constructs the isomorphism of integral permutation lattices.  When `A`
is `2`-hypoelementary, Lean extends that isomorphism to the `2`-adic integers
and applies Corollary 2.7.

No equivariant equivalence of `X` and `Y` is supplied as an input. -/
theorem lemma_2_5_basicSetBridge
    [Finite A] [Finite X] [Finite Y]
    (restrictedDecomposition :
      MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (decompositionEquivariant : ∀ a : A,
      restrictedDecomposition.toLinearMap.comp
          (Representation.ofMulAction ℤ A X a) =
        (Representation.ofMulAction ℤ A Y a).comp
          restrictedDecomposition.toLinearMap)
    (conlon : PadicConlonMarkDetection.{uA, uX} (p := 2) (A := A))
    (burnside : PublishedBurnsideMarkInjectivity.{uA, uX} (A := A)) :
    Nonempty
        ((Representation.ofMulAction ℤ A X).Equiv
          (Representation.ofMulAction ℤ A Y)) ∧
      (IsPHypoelementary 2 A →
        ∃ e : X ≃ Y, IsEquivariantSetEquiv (A := A) e) := by
  let integralLatticeEquiv :
      (Representation.ofMulAction ℤ A X).Equiv
        (Representation.ofMulAction ℤ A Y) :=
    permutationLatticeEquivOfIntertwining
      restrictedDecomposition decompositionEquivariant
  constructor
  · exact ⟨integralLatticeEquiv⟩
  · intro ambientHypoelementary
    apply corollary_2_4_conlonMark ambientHypoelementary
      ⟨permutationLatticeEquivBaseChange
        (S := ℤ_[2]) integralLatticeEquiv⟩ conlon burnside

end Marks

end ModularRep.PaperProofs.ConlonBasicSet


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
