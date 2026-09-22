import ModularRep.IrreducibleBrauerCharacter
import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413Relative

/-!
# Actual-character instance for Corollary 4.10

This file instantiates the field-fixation argument with literal character
carriers.  Irreducible Brauer characters are the function-valued `IBr`
objects of the library.  Principal-block projective characters lie in a
specified submodule of the literal function space `G → K`, and the field
action is pullback along the specified automorphisms of `G`.

The standard projective--Brauer theory enters through its defining
decomposition-number formula, separation of projective characters by their
ordinary scalar products, and linear independence of the decomposition
columns.  Lean derives both injectivity and field equivariance of the
projective-indecomposable indexing from those inputs.  It then applies the
basis-fixed argument already checked for Corollary 4.10.  No Brauer-character
fixedness, weight correspondence, BAW condition, or iBAW condition is an
input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413SourceInstantiation

open Module
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413Relative

universe u

variable {p : Nat} {k K G E I : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group E]

/-! ## Literal field actions -/

/-- Pullback of literal `K`-valued functions along a group automorphism. -/
def functionTwistLinearEquiv (alpha : MulAut G) :
    (G → K) ≃ₗ[K] (G → K) where
  toFun f := fun g ↦ f (alpha g)
  invFun f := fun g ↦ f (alpha.symm g)
  left_inv f := by
    funext g
    simp
  right_inv f := by
    funext g
    simp
  map_add' f q := rfl
  map_smul' c f := rfl

@[simp]
theorem functionTwistLinearEquiv_apply
    (alpha : MulAut G) (f : G → K) (g : G) :
    functionTwistLinearEquiv (K := K) alpha f g = f (alpha g) :=
  rfl

/-- The literal linear action obtained from the manuscript's right action of
automorphisms.  A right action is encoded as a left action through the
opposite automorphism group. -/
def functionFieldRepresentation
    (field : E →* (MulAut G)ᵐᵒᵖ) : E →* ((G → K) ≃ₗ[K] (G → K)) where
  toFun e := functionTwistLinearEquiv (K := K) (field e).unop
  map_one' := by
    ext f g
    simp [functionTwistLinearEquiv]
  map_mul' e d := by
    ext f g
    rw [map_mul, MulOpposite.unop_mul]
    rfl

/-- Restrict a linear action to a stable submodule. -/
def restrictLinearRepresentation
    {V : Type u} [AddCommGroup V] [Module K V]
    (rho : E →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (stable : ∀ e : E, ∀ v : V, v ∈ W → rho e v ∈ W) :
    E →* (W ≃ₗ[K] W) where
  toFun e :=
    { toFun := fun v ↦ ⟨rho e v.1, stable e v.1 v.2⟩
      invFun := fun v ↦ ⟨rho e⁻¹ v.1, stable e⁻¹ v.1 v.2⟩
      left_inv := by
        intro v
        apply Subtype.ext
        have h := congrArg (fun T : V ≃ₗ[K] V ↦ T v.1) (rho.map_mul e⁻¹ e)
        simpa using h
      right_inv := by
        intro v
        apply Subtype.ext
        have h := congrArg (fun T : V ≃ₗ[K] V ↦ T v.1) (rho.map_mul e e⁻¹)
        simpa using h
      map_add' := by
        intro v w
        apply Subtype.ext
        exact (rho e).map_add v.1 w.1
      map_smul' := by
        intro c v
        apply Subtype.ext
        exact (rho e).map_smul c v.1 }
  map_one' := by
    ext v
    have h := congrArg (fun T : V ≃ₗ[K] V ↦ T v.1) rho.map_one
    simpa using h
  map_mul' e d := by
    ext v
    have h := congrArg (fun T : V ≃ₗ[K] V ↦ T v.1) (rho.map_mul e d)
    simpa using h

/-- Literal principal-block projective-character space with its pullback
field action. -/
def projectiveFieldRepresentation
    (field : E →* (MulAut G)ᵐᵒᵖ)
    (projectiveSpace : Submodule K (G → K))
    (stable : ∀ e : E, ∀ f : G → K, f ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) (field e).unop f ∈ projectiveSpace) :
    E →* (projectiveSpace ≃ₗ[K] projectiveSpace) :=
  restrictLinearRepresentation
    (functionFieldRepresentation (K := K) field) projectiveSpace stable

@[simp]
theorem projectiveFieldRepresentation_apply
    (field : E →* (MulAut G)ᵐᵒᵖ)
    (projectiveSpace : Submodule K (G → K))
    (stable : ∀ e : E, ∀ f : G → K, f ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) (field e).unop f ∈ projectiveSpace)
    (e : E) (P : projectiveSpace) (g : G) :
    (projectiveFieldRepresentation field projectiveSpace stable e P).1 g =
      P.1 ((field e).unop g) :=
  rfl

/-- Pullback action on actual function-valued ordinary irreducible
characters. -/
@[instance_reducible] def ordinaryIrrFieldAction
    (field : E →* (MulAut G)ᵐᵒᵖ) : MulAction E (Irr K G) where
  smul e chi := twist K G chi (field e).unop
  one_smul chi := by
    apply OrdinaryIrreducibleCharacter.ext
    intro g
    change chi ((field 1).unop g) = chi g
    rw [map_one, MulOpposite.unop_one]
    rfl
  mul_smul e d chi := by
    apply OrdinaryIrreducibleCharacter.ext
    intro g
    change chi ((field (e * d)).unop g) =
      chi ((field d).unop ((field e).unop g))
    rw [map_mul, MulOpposite.unop_mul]
    rfl

/-- The actual set of Brauer characters in the principal block. -/
abbrev PrincipalBrauerCarrier
    (iota : PrimeRegularRootEmbedding p k K G)
    (inPrincipalBlock : IBr iota → Prop) :=
  {phi : IBr iota // inPrincipalBlock phi}

/-- Restriction of the literal Brauer-character pullback action to the
principal block.  Stability of the principal block under automorphisms is a
standard source input. -/
@[instance_reducible] def principalBrauerFieldAction
    (field : E →* (MulAut G)ᵐᵒᵖ)
    (iota : PrimeRegularRootEmbedding p k K G)
    (inPrincipalBlock : IBr iota → Prop)
    (stable : ∀ e : E, ∀ phi : IBr iota, inPrincipalBlock phi →
      inPrincipalBlock
        (IrreducibleBrauerCharacter.twist iota phi (field e).unop)) :
    MulAction E (PrincipalBrauerCarrier iota inPrincipalBlock) where
  smul e phi :=
    ⟨IrreducibleBrauerCharacter.twist iota phi.1 (field e).unop,
      stable e phi.1 phi.2⟩
  one_smul phi := by
    apply Subtype.ext
    change IrreducibleBrauerCharacter.twist iota phi.1 (field 1).unop = phi.1
    rw [map_one, MulOpposite.unop_one]
    exact IrreducibleBrauerCharacter.twist_refl iota phi.1
  mul_smul e d phi := by
    apply Subtype.ext
    change IrreducibleBrauerCharacter.twist iota phi.1 (field (e * d)).unop =
      IrreducibleBrauerCharacter.twist iota
        (IrreducibleBrauerCharacter.twist iota phi.1 (field d).unop)
        (field e).unop
    rw [map_mul, MulOpposite.unop_mul,
      IrreducibleBrauerCharacter.twist_mul]

/-! ## Source-shaped projective--Brauer formula -/

/-- Exact standard character-theoretic inputs used to identify the
projective indecomposable character indexed by a Brauer character.

`coefficient P chi` is the ordinary scalar product of the projective
character `P` with `chi`, and `decompositionNumber chi phi` is the
corresponding decomposition number.  The final two naturality fields are the
standard automorphism invariance of those two quantities.  Neither
injectivity nor equivariance of `projectiveIndecomposable` is a field. -/
structure ProjectiveBrauerFormulaSource
    (field : E →* (MulAut G)ᵐᵒᵖ)
    (iota : PrimeRegularRootEmbedding p k K G)
    (inPrincipalBlock : IBr iota → Prop)
    (brauerStable : ∀ e : E, ∀ phi : IBr iota, inPrincipalBlock phi →
      inPrincipalBlock
        (IrreducibleBrauerCharacter.twist iota phi (field e).unop))
    (projectiveSpace : Submodule K (G → K))
    (projectiveStable : ∀ e : E, ∀ f : G → K, f ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) (field e).unop f ∈ projectiveSpace) where
  projectiveIndecomposable :
    PrincipalBrauerCarrier iota inPrincipalBlock → projectiveSpace
  coefficient : projectiveSpace → Irr K G → K
  decompositionNumber :
    Irr K G → PrincipalBrauerCarrier iota inPrincipalBlock → K
  coefficient_projectiveIndecomposable : ∀ phi chi,
    coefficient (projectiveIndecomposable phi) chi =
      decompositionNumber chi phi
  coefficient_separates : ∀ P Q : projectiveSpace,
    (∀ chi : Irr K G, coefficient P chi = coefficient Q chi) → P = Q
  decompositionColumns_linearIndependent :
    LinearIndependent K (fun phi : PrincipalBrauerCarrier iota inPrincipalBlock ↦
      fun chi : Irr K G ↦ decompositionNumber chi phi)
  coefficient_natural :
    let _ := ordinaryIrrFieldAction (K := K) field
    ∀ e : E, ∀ P : projectiveSpace, ∀ chi : Irr K G,
      coefficient
          (projectiveFieldRepresentation field projectiveSpace
            projectiveStable e P)
          (e • chi) =
        coefficient P chi
  decompositionNumber_natural :
    let _ := ordinaryIrrFieldAction (K := K) field
    let _ := principalBrauerFieldAction field iota inPrincipalBlock brauerStable
    ∀ e : E, ∀ chi : Irr K G,
      ∀ phi : PrincipalBrauerCarrier iota inPrincipalBlock,
      decompositionNumber (e • chi) (e • phi) =
        decompositionNumber chi phi

namespace ProjectiveBrauerFormulaSource

variable {field : E →* (MulAut G)ᵐᵒᵖ}
variable {iota : PrimeRegularRootEmbedding p k K G}
variable {inPrincipalBlock : IBr iota → Prop}
variable {brauerStable : ∀ e : E, ∀ phi : IBr iota,
  inPrincipalBlock phi →
    inPrincipalBlock
      (IrreducibleBrauerCharacter.twist iota phi (field e).unop)}
variable {projectiveSpace : Submodule K (G → K)}
variable {projectiveStable : ∀ e : E, ∀ f : G → K,
  f ∈ projectiveSpace →
    functionTwistLinearEquiv (K := K) (field e).unop f ∈ projectiveSpace}

/-- The defining decomposition-number formula and independence of its
columns force distinct Brauer characters to index distinct projective
indecomposable characters. -/
theorem projectiveIndecomposable_injective
    (S : ProjectiveBrauerFormulaSource field iota inPrincipalBlock
      brauerStable projectiveSpace projectiveStable) :
    Function.Injective S.projectiveIndecomposable := by
  intro phi psi hP
  apply S.decompositionColumns_linearIndependent.injective
  funext chi
  calc
    S.decompositionNumber chi phi =
        S.coefficient (S.projectiveIndecomposable phi) chi :=
      (S.coefficient_projectiveIndecomposable phi chi).symm
    _ = S.coefficient (S.projectiveIndecomposable psi) chi := by rw [hP]
    _ = S.decompositionNumber chi psi :=
      S.coefficient_projectiveIndecomposable psi chi

/-- The defining decomposition-number formula and its standard
automorphism invariance force the projective-indecomposable indexing to be
equivariant for the literal pullback actions. -/
theorem projectiveIndecomposable_equivariant
    (S : ProjectiveBrauerFormulaSource field iota inPrincipalBlock
      brauerStable projectiveSpace projectiveStable) :
    let _ := ordinaryIrrFieldAction (K := K) field
    let _ := principalBrauerFieldAction field iota inPrincipalBlock brauerStable
    ∀ e : E, ∀ phi : PrincipalBrauerCarrier iota inPrincipalBlock,
      S.projectiveIndecomposable (e • phi) =
        projectiveFieldRepresentation field projectiveSpace
          projectiveStable e (S.projectiveIndecomposable phi) := by
  dsimp only
  letI ordinaryAction : MulAction E (Irr K G) :=
    ordinaryIrrFieldAction (K := K) field
  letI brauerAction : MulAction E
      (PrincipalBrauerCarrier iota inPrincipalBlock) :=
    principalBrauerFieldAction field iota inPrincipalBlock brauerStable
  intro e phi
  apply S.coefficient_separates
  intro chi
  let chi0 : Irr K G := e⁻¹ • chi
  have hchi : e • chi0 = chi := by
    simp [chi0]
  calc
    S.coefficient (S.projectiveIndecomposable (e • phi)) chi =
        S.decompositionNumber chi (e • phi) :=
      S.coefficient_projectiveIndecomposable (e • phi) chi
    _ = S.decompositionNumber (e • chi0) (e • phi) := by rw [hchi]
    _ = S.decompositionNumber chi0 phi :=
      S.decompositionNumber_natural e chi0 phi
    _ = S.coefficient (S.projectiveIndecomposable phi) chi0 :=
      (S.coefficient_projectiveIndecomposable phi chi0).symm
    _ = S.coefficient
          (projectiveFieldRepresentation field projectiveSpace
            projectiveStable e (S.projectiveIndecomposable phi))
          (e • chi0) :=
      (S.coefficient_natural e (S.projectiveIndecomposable phi) chi0).symm
    _ = S.coefficient
          (projectiveFieldRepresentation field projectiveSpace
            projectiveStable e (S.projectiveIndecomposable phi)) chi := by
      rw [hchi]

/-- Corollary 4.10 on the literal principal-block sets of characters.

The GGGR components are supplied as the basis obtained in Proposition 4.9,
and their pointwise field fixation is the output of Lemma 4.7.  Lean proves
triviality on the projective space, derives equivariance and injectivity of
the actual PIM indexing from `S`, and concludes that every actual
principal-block Brauer character is fixed. -/
theorem corollary_4_13_brauer_fixed_source_instantiated
    (S : ProjectiveBrauerFormulaSource field iota inPrincipalBlock
      brauerStable projectiveSpace projectiveStable)
    (gggrBasis : Basis I K projectiveSpace)
    (gggrBasis_fixed : ∀ e : E, ∀ u : I,
      projectiveFieldRepresentation field projectiveSpace
          projectiveStable e (gggrBasis u) = gggrBasis u) :
    let _ := principalBrauerFieldAction field iota inPrincipalBlock brauerStable
    ∀ e : E, ∀ phi : PrincipalBrauerCarrier iota inPrincipalBlock,
      e • phi = phi := by
  dsimp only
  letI brauerAction : MulAction E
      (PrincipalBrauerCarrier iota inPrincipalBlock) :=
    principalBrauerFieldAction field iota inPrincipalBlock brauerStable
  have projective_fixed : ∀ e : E, ∀ P : projectiveSpace,
      projectiveFieldRepresentation field projectiveSpace
          projectiveStable e P = P :=
    linear_action_fixed_of_basis_fixed
      (projectiveFieldRepresentation field projectiveSpace projectiveStable)
      gggrBasis gggrBasis_fixed
  intro e phi
  apply S.projectiveIndecomposable_injective
  rw [S.projectiveIndecomposable_equivariant]
  exact projective_fixed e (S.projectiveIndecomposable phi)

end ProjectiveBrauerFormulaSource

end ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413SourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
