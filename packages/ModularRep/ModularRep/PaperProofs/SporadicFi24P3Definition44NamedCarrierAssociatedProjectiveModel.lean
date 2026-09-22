import ModularRep.CyclicExtension

/-!
# Associated ambient projective models from actual extensions

Navarro (1998), Theorem 8.14, p. 165, uses operators on the ambient group
whose restriction is the specified base representation. Their scalar
multiplier is a factor set on the quotient (pp. 166--167, Theorem 8.15).
An extension gives these operators with multiplier one after conjugating
by its restriction equivalence. The ambient representation is never
asserted to descend through the base quotient.

The selected-character applications must retain irreducibility and the
affording equation for `rho`; this generic operator construction requires
neither as an assumption. It does not assert any character-triple relation.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel

universe u

structure ScalarFactorSet (k H : Type u) [Field k] [Group H] where
  toFun : H → H → kˣ
  one_left : ∀ h, toFun 1 h = 1
  one_right : ∀ h, toFun h 1 = 1
  cocycle : ∀ g h j, toFun g h * toFun (g * h) j =
    toFun h j * toFun g (h * j)

namespace ScalarFactorSet

variable {k H J : Type u} [Field k] [Group H] [Group J]

instance : CoeFun (ScalarFactorSet k H) (fun _ ↦ H → H → kˣ) := ⟨toFun⟩

def trivial : ScalarFactorSet k H where
  toFun _ _ := 1
  one_left _ := rfl
  one_right _ := rfl
  cocycle _ _ _ := by simp

def pullback (e : H ≃* J) (a : ScalarFactorSet k J) : ScalarFactorSet k H where
  toFun g h := a (e g) (e h)
  one_left g := by simp [a.one_left]
  one_right g := by simp [a.one_right]
  cocycle g h j := by simpa using a.cocycle (e g) (e h) (e j)

/-- Equality of classes expressed by the actual scalar coboundary equation. -/
def Cohomologous (a b : ScalarFactorSet k H) : Prop :=
  ∃ c : H → kˣ, c 1 = 1 ∧
    ∀ g h, b g h = c g * c h * (c (g * h))⁻¹ * a g h

theorem trivial_cohomologous_pullback_trivial (e : H ≃* J) :
    Cohomologous (trivial : ScalarFactorSet k H)
      (pullback e (trivial : ScalarFactorSet k J)) := by
  refine ⟨fun _ ↦ 1, rfl, ?_⟩
  intro g h
  simp [pullback, trivial]

end ScalarFactorSet

variable {k G V : Type u} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable (N : Subgroup G) [N.Normal] (rho : Representation k N V)

/-- Fixed Navarro 8.14 operator semantics associated to the specified `rho`.
The selected irreducible applications also ensure a nonzero carrier. -/
structure AssociatedProjectiveModel where
  operator : G → Module.End k V
  operator_bijective : ∀ g, Function.Bijective (operator g)
  operator_one : operator 1 = 1
  restriction : ∀ n : N, operator n = rho n
  factorSet : ScalarFactorSet k (G ⧸ N)
  operator_mul : ∀ g h, operator g * operator h =
    (factorSet (QuotientGroup.mk' N g) (QuotientGroup.mk' N h) : k) •
      operator (g * h)

namespace AssociatedProjectiveModel

variable {N rho}

/-- Conjugating by the stored intertwiner makes restriction literal. -/
def normalizedExtension (E : Representation.Extension N rho) : Representation k G V :=
  E.restrictionEquiv.toLinearEquiv.conjRingEquiv.toMonoidHom.comp E.representation

omit [N.Normal] in
theorem normalizedExtension_restriction (E : Representation.Extension N rho) (n : N) :
    normalizedExtension E n = rho n := by
  ext v
  change E.restrictionEquiv (E.representation n (E.restrictionEquiv.symm v)) = rho n v
  rw [E.map_restriction]
  simp

/-- An actual extension supplies its associated model and quotient factor one. -/
def ofExtension (E : Representation.Extension N rho) : AssociatedProjectiveModel N rho where
  operator := normalizedExtension E
  operator_bijective := (normalizedExtension E).apply_bijective
  operator_one := map_one _
  restriction := normalizedExtension_restriction E
  factorSet := ScalarFactorSet.trivial
  operator_mul g h := by simp [ScalarFactorSet.trivial, map_mul]

theorem ofExtension_factorSet (E : Representation.Extension N rho) :
    (ofExtension E).factorSet = ScalarFactorSet.trivial := rfl

variable (M : AssociatedProjectiveModel N rho)

/-- Navarro 8.14(b) follows from the normalized quotient multiplier. -/
theorem base_mul (n : N) (g : G) :
    M.operator ((n : G) * g) = rho n * M.operator g := by
  have hq : QuotientGroup.mk' N (n : G) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr n.2
  have h := M.operator_mul n g
  rw [hq, M.factorSet.one_left, Units.val_one, one_smul, M.restriction] at h
  exact h.symm

/-- Navarro 8.14(c) follows from the normalized quotient multiplier. -/
theorem mul_base (g : G) (n : N) :
    M.operator (g * (n : G)) = M.operator g * rho n := by
  have hq : QuotientGroup.mk' N (n : G) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr n.2
  have h := M.operator_mul g n
  rw [hq, M.factorSet.one_right, Units.val_one, one_smul, M.restriction] at h
  exact h.symm

end AssociatedProjectiveModel

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
