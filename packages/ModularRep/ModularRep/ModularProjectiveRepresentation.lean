import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Projective representations and homomorphism pullback

The operators below are actual linear automorphisms of a nonzero finite
dimensional vector space.  Their multiplication law has values in the units
of the coefficient field.  Normalisation of the multiplier and its cocycle
identity are derived from the normalised identity operator, associativity,
and faithfulness of scalar multiplication on a nonzero vector space.

The field may have any characteristic; modular applications specialise it
to the chosen characteristic.  The groups need not be finite for these
algebraic constructions.  Nonzero dimension is essential for recovering
the multiplier from the operators.

This is standard representation theoretic infrastructure.  It defines no
Brauer-character association, modular block-triple relation, intermediate
tensor correspondence, or manuscript-specific source certificate.
-/

namespace ModularRep

universe uK uG uH uL uV

section ScalarAutomorphisms

variable {k : Type uK} {V : Type uV}
variable [Field k] [AddCommGroup V] [Module k V]

/-- Multiplication by a nonzero scalar, as an actual linear automorphism. -/
def scalarLinearAut (a : kˣ) : V ≃ₗ[k] V := LinearEquiv.smulOfUnit a

@[simp] theorem scalarLinearAut_apply (a : kˣ) (v : V) :
    scalarLinearAut (V := V) a v = (a : k) • v := rfl

@[simp] theorem scalarLinearAut_one :
    scalarLinearAut (k := k) (V := V) 1 = 1 := by
  ext v
  exact one_smul k v

theorem scalarLinearAut_mul (a b : kˣ) :
    scalarLinearAut (V := V) (a * b) =
      scalarLinearAut a * scalarLinearAut b := by
  ext v
  exact mul_smul (a : k) (b : k) v

/-- Scalar automorphisms commute with every linear automorphism. -/
theorem scalarLinearAut_commute (a : kˣ) (e : V ≃ₗ[k] V) :
    scalarLinearAut a * e = e * scalarLinearAut a := by
  ext v
  exact (e.map_smul (a : k) v).symm

theorem scalarLinearAut_injective [Nontrivial V] :
    Function.Injective (scalarLinearAut (k := k) (V := V)) := by
  intro a b h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply Units.ext
  apply smul_left_injective k hv
  exact congrArg (fun e : V ≃ₗ[k] V => e v) h

end ScalarAutomorphisms

/-- A normalised scalar two-cocycle with the convention
`P(g) P(h) = alpha(g,h) P(gh)`. -/
structure NormalizedFactorSet (k : Type uK) (G : Type uG)
    [Field k] [Group G] where
  toFun : G → G → kˣ
  one_left : ∀ g, toFun 1 g = 1
  one_right : ∀ g, toFun g 1 = 1
  cocycle : ∀ g h j,
    toFun g h * toFun (g * h) j = toFun h j * toFun g (h * j)

namespace NormalizedFactorSet

variable {k : Type uK} {G : Type uG} {H : Type uH} {L : Type uL}
variable [Field k] [Group G] [Group H] [Group L]

instance : CoeFun (NormalizedFactorSet k G) (fun _ => G → G → kˣ) :=
  ⟨NormalizedFactorSet.toFun⟩

@[ext] theorem ext {alpha beta : NormalizedFactorSet k G}
    (h : ∀ g j, alpha g j = beta g j) : alpha = beta := by
  cases alpha with
  | mk alpha hleft hright hcocycle =>
    cases beta with
    | mk beta kleft kright kcocycle =>
      have hfun : alpha = beta := funext (fun g => funext (h g))
      cases hfun
      rfl

/-- Pullback needs a homomorphism, without an injectivity or surjectivity
assumption.  The quotient maps needed for inflation are included. -/
def pullback (alpha : NormalizedFactorSet k G) (f : H →* G) :
    NormalizedFactorSet k H where
  toFun h j := alpha (f h) (f j)
  one_left h := by simpa only [map_one] using alpha.one_left (f h)
  one_right h := by simpa only [map_one] using alpha.one_right (f h)
  cocycle h j t := by
    simpa only [map_mul] using alpha.cocycle (f h) (f j) (f t)

@[simp] theorem pullback_apply (alpha : NormalizedFactorSet k G)
    (f : H →* G) (h j : H) :
    alpha.pullback f h j = alpha (f h) (f j) := rfl

@[simp] theorem pullback_id (alpha : NormalizedFactorSet k G) :
    alpha.pullback (MonoidHom.id G) = alpha := by
  ext g h
  rfl

@[simp] theorem pullback_comp (alpha : NormalizedFactorSet k G)
    (f : H →* G) (e : L →* H) :
    (alpha.pullback f).pullback e = alpha.pullback (f.comp e) := by
  ext g h
  rfl

def restrict (alpha : NormalizedFactorSet k G) (N : Subgroup G) :
    NormalizedFactorSet k N := alpha.pullback N.subtype

@[simp] theorem restrict_apply (alpha : NormalizedFactorSet k G)
    (N : Subgroup G) (g h : N) :
    alpha.restrict N g h = alpha g h := rfl

end NormalizedFactorSet

/-- A projective representation on a fixed nonzero finite dimensional
vector space.  The operator law determines the multiplier; its normalised
factor-set laws are proved below, rather than assumed as an unrelated
cocycle certificate. -/
structure ModularProjectiveRepresentation
    (k : Type uK) (G : Type uG) (V : Type uV)
    [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] where
  operator : G → V ≃ₗ[k] V
  multiplier : G → G → kˣ
  operator_one : operator 1 = 1
  operator_mul : ∀ g h,
    operator g * operator h =
      scalarLinearAut (multiplier g h) * operator (g * h)

namespace ModularProjectiveRepresentation

variable {k : Type uK} {G : Type uG} {H : Type uH} {L : Type uL} {V : Type uV}
variable [Field k] [Group G] [Group H] [Group L]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]

variable (P : ModularProjectiveRepresentation k G V)

@[simp] theorem multiplier_one_left (g : G) : P.multiplier 1 g = 1 := by
  apply scalarLinearAut_injective (V := V)
  rw [scalarLinearAut_one]
  have h : scalarLinearAut (V := V) (P.multiplier 1 g) * P.operator g =
      (1 : V ≃ₗ[k] V) * P.operator g := by
    simpa only [P.operator_one, one_mul] using (P.operator_mul 1 g).symm
  exact mul_right_cancel h

@[simp] theorem multiplier_one_right (g : G) : P.multiplier g 1 = 1 := by
  apply scalarLinearAut_injective (V := V)
  rw [scalarLinearAut_one]
  have h : scalarLinearAut (V := V) (P.multiplier g 1) * P.operator g =
      (1 : V ≃ₗ[k] V) * P.operator g := by
    simpa only [P.operator_one, mul_one, one_mul] using (P.operator_mul g 1).symm
  exact mul_right_cancel h

/-- Associativity of the actual operators forces the scalar cocycle law. -/
theorem multiplier_cocycle (g h j : G) :
    P.multiplier g h * P.multiplier (g * h) j =
      P.multiplier h j * P.multiplier g (h * j) := by
  apply scalarLinearAut_injective (V := V)
  have hoperators :
      scalarLinearAut (V := V) (P.multiplier g h * P.multiplier (g * h) j) *
          P.operator ((g * h) * j) =
        scalarLinearAut (P.multiplier h j * P.multiplier g (h * j)) *
          P.operator ((g * h) * j) := by
    calc
      _ = scalarLinearAut (P.multiplier g h) *
          (scalarLinearAut (P.multiplier (g * h) j) * P.operator ((g * h) * j)) := by
            rw [scalarLinearAut_mul, mul_assoc]
      _ = scalarLinearAut (P.multiplier g h) * (P.operator (g * h) * P.operator j) := by
            rw [P.operator_mul (g * h) j]
      _ = (scalarLinearAut (P.multiplier g h) * P.operator (g * h)) * P.operator j := by
            rw [mul_assoc]
      _ = (P.operator g * P.operator h) * P.operator j := by
            rw [P.operator_mul g h]
      _ = P.operator g * (P.operator h * P.operator j) := mul_assoc _ _ _
      _ = P.operator g *
          (scalarLinearAut (P.multiplier h j) * P.operator (h * j)) := by
            rw [P.operator_mul h j]
      _ = (P.operator g * scalarLinearAut (P.multiplier h j)) * P.operator (h * j) := by
            rw [mul_assoc]
      _ = (scalarLinearAut (P.multiplier h j) * P.operator g) * P.operator (h * j) := by
            rw [scalarLinearAut_commute (P.multiplier h j) (P.operator g)]
      _ = scalarLinearAut (P.multiplier h j) * (P.operator g * P.operator (h * j)) := by
            rw [mul_assoc]
      _ = scalarLinearAut (P.multiplier h j) *
          (scalarLinearAut (P.multiplier g (h * j)) * P.operator (g * (h * j))) := by
            rw [P.operator_mul g (h * j)]
      _ = _ := by rw [scalarLinearAut_mul, mul_assoc, mul_assoc]
  exact mul_right_cancel hoperators

/-- The normalized factor set attached to the actual operators. -/
def factorSet : NormalizedFactorSet k G where
  toFun := P.multiplier
  one_left := P.multiplier_one_left
  one_right := P.multiplier_one_right
  cocycle := P.multiplier_cocycle

@[simp] theorem factorSet_apply (g h : G) : P.factorSet g h = P.multiplier g h := rfl

theorem operator_mul_apply (g h : G) (v : V) :
    P.operator g (P.operator h v) =
      (P.multiplier g h : k) • P.operator (g * h) v :=
  congrArg (fun e : V ≃ₗ[k] V => e v) (P.operator_mul g h)

/-- Equality of the two operator and multiplier functions determines the
projective representation; all remaining components are proofs. -/
@[ext] theorem ext {P Q : ModularProjectiveRepresentation k G V}
    (hop : ∀ g, P.operator g = Q.operator g)
    (hmul : ∀ g h, P.multiplier g h = Q.multiplier g h) : P = Q := by
  cases P with
  | mk pop pmul pone plaw =>
    cases Q with
    | mk qop qmul qone qlaw =>
      have hoperator : pop = qop := funext hop
      have hmultiplier : pmul = qmul := funext (fun g => funext (hmul g))
      cases hoperator
      cases hmultiplier
      rfl

/-- Homomorphism pullback keeps the vector space and every operator
unchanged except for precomposition on the group. -/
def pullback (f : H →* G) : ModularProjectiveRepresentation k H V where
  operator h := P.operator (f h)
  multiplier h j := P.multiplier (f h) (f j)
  operator_one := by simpa only [map_one] using P.operator_one
  operator_mul h j := by
    simpa only [map_mul] using P.operator_mul (f h) (f j)

@[simp] theorem pullback_operator (f : H →* G) (h : H) :
    (P.pullback f).operator h = P.operator (f h) := rfl

@[simp] theorem pullback_multiplier (f : H →* G) (h j : H) :
    (P.pullback f).multiplier h j = P.multiplier (f h) (f j) := rfl

/-- The factor-set construction commutes with homomorphism pullback. -/
@[simp] theorem pullback_factorSet (f : H →* G) :
    (P.pullback f).factorSet = P.factorSet.pullback f := by
  ext h j
  rfl

@[simp] theorem pullback_id : P.pullback (MonoidHom.id G) = P := by
  apply ext <;> intros <;> rfl

@[simp] theorem pullback_comp (f : H →* G) (e : L →* H) :
    (P.pullback f).pullback e = P.pullback (f.comp e) := by
  apply ext <;> intros <;> rfl

/-- Restriction to an actual subgroup is the same homomorphism pullback. -/
def restrict (N : Subgroup G) : ModularProjectiveRepresentation k N V :=
  P.pullback N.subtype

@[simp] theorem restrict_operator (N : Subgroup G) (g : N) :
    (P.restrict N).operator g = P.operator g := rfl

@[simp] theorem restrict_multiplier (N : Subgroup G) (g h : N) :
    (P.restrict N).multiplier g h = P.multiplier g h := rfl

@[simp] theorem restrict_factorSet (N : Subgroup G) :
    (P.restrict N).factorSet = P.factorSet.restrict N := by
  ext g h
  rfl

theorem restrict_pullback (f : H →* G) (M : Subgroup H) :
    (P.pullback f).restrict M = P.pullback (f.comp M.subtype) := by
  apply ext <;> intros <;> rfl

/-- The restriction of a homomorphism to the inverse image of a subgroup. -/
def comapHom (f : H →* G) (N : Subgroup G) : N.comap f →* N where
  toFun h := ⟨f h, h.property⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' h j := Subtype.ext (map_mul f h.1 j.1)

/-- Restriction commutes with pullback on the literal inverse-image
subgroup, using its actual induced homomorphism to the original subgroup. -/
theorem restrict_pullback_comap (f : H →* G) (N : Subgroup G) :
    (P.pullback f).restrict (N.comap f) =
      (P.restrict N).pullback (comapHom f N) := by
  apply ext <;> intros <;> rfl

/-- An honest representation by linear automorphisms is a projective
representation with trivial multiplier. -/
def ofLinearHom (rho : G →* V ≃ₗ[k] V) : ModularProjectiveRepresentation k G V where
  operator := rho
  multiplier _ _ := 1
  operator_one := map_one rho
  operator_mul g h := by
    rw [scalarLinearAut_one, one_mul]
    exact (map_mul rho g h).symm

@[simp] theorem ofLinearHom_multiplier (rho : G →* V ≃ₗ[k] V) (g h : G) :
    (ofLinearHom rho).multiplier g h = 1 := rfl

end ModularProjectiveRepresentation

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
