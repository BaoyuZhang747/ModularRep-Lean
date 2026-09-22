import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Span.Basic
import ModularRep.BrauerCharacterLinearIndependence
import ModularRep.PaperProofs.SporadicFi24ThreeBlockCarrierActual

/-!
# Literal B1 restriction-span binding

BrauerRestrictionSpaceBinding is a narrow E1/E3 interface: it takes one
equality between a six-row ordinary restriction span and the literal B1
Brauer-function span. Conditional on that equality, the basis and linear
action are constructed in Lean. It contains no rank, fixed-count, census,
weight, fibre-equivalence, named-row permutation, or cancellation input.

The downstream SporadicFi24P3OrdinarySpanFromDecomposition adapter proves this
equality from global decomposition data, Brauer-character linear independence,
six-row coverage, and literal row identification. Thus literal span equality
is an input to this binding interface, but not an additional unresolved input
to that adapter.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction

open Formalisation
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-! ## One generic stable-span helper -/

/-- Restrict a linear map to the span of a family when its action on every
generator stays in that span.  This constructs a linear operator; it is not a
source-supplied equivariant map. -/
noncomputable def restrictToGeneratedSpan
    {W I : Type u} [AddCommGroup W] [Module K W]
    (f : W →ₗ[K] W) (v : I → W)
    (hstable : ∀ i, f (v i) ∈ Submodule.span K (Set.range v)) :
    Submodule.span K (Set.range v) →ₗ[K] Submodule.span K (Set.range v) :=
  (f.domRestrict _).codRestrict _ (by
    intro x
    have hmap :
        (Submodule.span K (Set.range v)).map f ≤
          Submodule.span K (Set.range v) :=
      (LinearMap.map_span_le f (Set.range v)
        (Submodule.span K (Set.range v))).2 (by
          rintro y ⟨i, rfl⟩
          exact hstable i)
    exact hmap ⟨x, x.property, rfl⟩)

/-! ## Literal B1 functions, basis, and canonical outer action -/

abbrev b1BrauerFunction
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    BrauerFibre iota hinj blocks S.nonprincipalBlock →
      PrimeRegularFunction K X 3 :=
  fun phi => phi.1.1.toFun

abbrev literalB1BrauerSpan
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Submodule K (PrimeRegularFunction K X 3) :=
  Submodule.span K (Set.range (b1BrauerFunction iota hinj blocks S))

/-- The sole public rank-bridge interface. It receives, rather than proves,
the equality of already literal function spaces; it supplies neither an
evaluation injection, action equation, basis, nor character-fibre equivalence.
-/
structure BrauerRestrictionSpaceBinding
    (S : Fi24ThreeBlockSource (k := k) (X := X)) : Type u where
  rows : Fin 6 → PrimeRegularFunction K X 3
  span_eq_literal :
    Submodule.span K (Set.range rows) =
      literalB1BrauerSpan iota hinj blocks S

abbrev ordinaryRestrictionSpan
    {S : Fi24ThreeBlockSource (k := k) (X := X)}
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S) :=
  Submodule.span K (Set.range D.rows)

/-- The literal B1 subfamily inherits linear independence from the standard
linear independence theorem for all function-valued irreducible Brauer
characters. -/
theorem b1BrauerFunction_linearIndependent
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    LinearIndependent K (b1BrauerFunction iota hinj blocks S) := by
  change LinearIndependent K
    ((fun phi : IBr iota => phi.1.toFun) ∘
      (fun phi : BrauerFibre iota hinj blocks S.nonprincipalBlock => phi.1))
  exact
    (FDRepSimpleClassKZero.irreducibleBrauerCharacters_linearIndependent iota).comp
      (fun phi : BrauerFibre iota hinj blocks S.nonprincipalBlock => phi.1)
      Subtype.val_injective

/-- This basis is kernel-constructed from linear independence, not supplied
by a Fischer source record. -/
noncomputable def literalB1BrauerBasis
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Module.Basis (BrauerFibre iota hinj blocks S.nonprincipalBlock) K
      (literalB1BrauerSpan iota hinj blocks S) :=
  Module.Basis.span (b1BrauerFunction_linearIndependent iota hinj blocks S)

@[simp]
theorem coe_literalB1BrauerBasis_apply
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (phi : BrauerFibre iota hinj blocks S.nonprincipalBlock) :
    ((literalB1BrauerBasis iota hinj blocks S phi :
      literalB1BrauerSpan iota hinj blocks S) : PrimeRegularFunction K X 3) =
      b1BrauerFunction iota hinj blocks S phi := by
  simp [literalB1BrauerBasis]

/-- The literal outer action on a B1 Brauer character, with block membership
obtained from the existing canonical block-transport theorem. -/
def outerOnB1Brauer
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (phi : BrauerFibre iota hinj blocks S.nonprincipalBlock) :
    BrauerFibre iota hinj blocks S.nonprincipalBlock :=
  ⟨S.outer • phi.1, by
    rw [brauerBlock_transport iota hinj blocks S.outer phi.1,
      phi.2, S.nonprincipal_fixed]⟩

/-- Pullback by the canonical right outer automorphism, represented as the
repository's left action of the opposite group. -/
def canonicalOuterPullbackLinear
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    PrimeRegularFunction K X 3 →ₗ[K] PrimeRegularFunction K X 3 where
  toFun f := f.pullback S.outer.unop.toMonoidHom
  map_add' f g := rfl
  map_smul' a f := rfl

theorem canonicalOuterPullbackLinear_b1BrauerFunction
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (phi : BrauerFibre iota hinj blocks S.nonprincipalBlock) :
    canonicalOuterPullbackLinear iota hinj blocks S
        (b1BrauerFunction iota hinj blocks S phi) =
      b1BrauerFunction iota hinj blocks S
        (outerOnB1Brauer iota hinj blocks S phi) := by
  change phi.1.1.toFun.pullback S.outer.unop.toMonoidHom =
    (S.outer • phi.1).1.toFun
  rw [IrreducibleBrauerCharacter.op_smul_val]
  rfl

/-- The canonical pullback restricts to the literal B1 Brauer-function span.
This is constructed from `brauerBlock_transport` and block fixedness, rather
than being supplied as an action or intertwining source field. -/
noncomputable def canonicalOuterOnLiteralB1Span
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    literalB1BrauerSpan iota hinj blocks S →ₗ[K]
      literalB1BrauerSpan iota hinj blocks S :=
  restrictToGeneratedSpan (K := K)
    (canonicalOuterPullbackLinear iota hinj blocks S)
    (b1BrauerFunction iota hinj blocks S) (by
      intro phi
      rw [canonicalOuterPullbackLinear_b1BrauerFunction iota hinj blocks S phi]
      exact Submodule.subset_span ⟨outerOnB1Brauer iota hinj blocks S phi, rfl⟩)

theorem canonicalOuterOnLiteralB1Span_apply_basis
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (phi : BrauerFibre iota hinj blocks S.nonprincipalBlock) :
    canonicalOuterOnLiteralB1Span iota hinj blocks S
        (literalB1BrauerBasis iota hinj blocks S phi) =
      literalB1BrauerBasis iota hinj blocks S
        (outerOnB1Brauer iota hinj blocks S phi) := by
  apply Subtype.ext
  change canonicalOuterPullbackLinear iota hinj blocks S
      ((literalB1BrauerBasis iota hinj blocks S phi :
        literalB1BrauerSpan iota hinj blocks S) : PrimeRegularFunction K X 3) =
    ((literalB1BrauerBasis iota hinj blocks S
      (outerOnB1Brauer iota hinj blocks S phi) :
        literalB1BrauerSpan iota hinj blocks S) : PrimeRegularFunction K X 3)
  simpa only [coe_literalB1BrauerBasis_apply] using
    canonicalOuterPullbackLinear_b1BrauerFunction iota hinj blocks S phi

/-! ## Transport along the one admitted span equality -/

/-- Equality of submodules transports a basis without a source-supplied
linear equivalence. -/
noncomputable def transportBasisAlongSubmoduleEq
    {W I : Type u} [AddCommGroup W] [Module K W]
    {P Q : Submodule K W} (h : P = Q) (b : Module.Basis I K Q) : Module.Basis I K P := by
  subst Q
  exact b

/-- Equality of submodules transports the canonical operator without a
source-supplied equivariant map. -/
noncomputable def transportActionAlongSubmoduleEq
    {W : Type u} [AddCommGroup W] [Module K W]
    {P Q : Submodule K W} (h : P = Q) (T : Q →ₗ[K] Q) : P →ₗ[K] P := by
  subst Q
  exact T

private theorem coe_transportBasisAlongSubmoduleEq
    {W I : Type u} [AddCommGroup W] [Module K W]
    {P Q : Submodule K W} (h : P = Q) (b : Module.Basis I K Q) (i : I) :
    ((transportBasisAlongSubmoduleEq h b i : P) : W) = (b i : W) := by
  subst Q
  rfl

private theorem transportActionAlongSubmoduleEq_value
    {W : Type u} [AddCommGroup W] [Module K W]
    {P Q : Submodule K W} (h : P = Q) (T : Q →ₗ[K] Q) (f : W → W)
    (hT : ∀ v : Q, (T v : W) = f (v : W)) (v : P) :
    ((transportActionAlongSubmoduleEq h T v : P) : W) = f (v : W) := by
  subst Q
  exact hT v

noncomputable def ordinaryRestrictionBrauerBasis
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S) :
    Module.Basis (BrauerFibre iota hinj blocks S.nonprincipalBlock) K
      (ordinaryRestrictionSpan iota hinj blocks D) :=
  transportBasisAlongSubmoduleEq D.span_eq_literal
    (literalB1BrauerBasis iota hinj blocks S)

noncomputable def canonicalOuterOnOrdinaryRestrictionSpan
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S) :
    ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
      ordinaryRestrictionSpan iota hinj blocks D :=
  transportActionAlongSubmoduleEq D.span_eq_literal
    (canonicalOuterOnLiteralB1Span iota hinj blocks S)

/-! ## Derived API from the sole source record -/

theorem ordinaryRestrictionBrauerBasis_value
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (phi : BrauerFibre iota hinj blocks S.nonprincipalBlock) :
    ((ordinaryRestrictionBrauerBasis iota hinj blocks S D phi :
      ordinaryRestrictionSpan iota hinj blocks D) : PrimeRegularFunction K X 3) =
      phi.1.1.toFun := by
  exact
    (coe_transportBasisAlongSubmoduleEq D.span_eq_literal
      (literalB1BrauerBasis iota hinj blocks S) phi).trans
      (coe_literalB1BrauerBasis_apply iota hinj blocks S phi)

theorem canonicalOuterOnOrdinaryRestrictionSpan_value
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (v : ordinaryRestrictionSpan iota hinj blocks D) :
    ((canonicalOuterOnOrdinaryRestrictionSpan iota hinj blocks S D v :
      ordinaryRestrictionSpan iota hinj blocks D) : PrimeRegularFunction K X 3) =
      (v.1).pullback S.outer.unop.toMonoidHom := by
  exact transportActionAlongSubmoduleEq_value D.span_eq_literal
    (canonicalOuterOnLiteralB1Span iota hinj blocks S)
    (fun f => f.pullback S.outer.unop.toMonoidHom) (fun _ => rfl) v

namespace BrauerRestrictionSpaceBinding

/-- Kernel-constructed basis on the row span.  This is a definition, not a
field that a future source record may fill. -/
noncomputable def brauerBasis
    {S : Fi24ThreeBlockSource (k := k) (X := X)}
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S) :
    Module.Basis (BrauerFibre iota hinj blocks S.nonprincipalBlock) K
      (ordinaryRestrictionSpan iota hinj blocks D) :=
  ordinaryRestrictionBrauerBasis iota hinj blocks S D

/-- Kernel-constructed canonical outer operator on the row span.  This is
not a source-supplied table action or an equivariant map. -/
noncomputable def outerAction
    {S : Fi24ThreeBlockSource (k := k) (X := X)}
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S) :
    ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
      ordinaryRestrictionSpan iota hinj blocks D :=
  canonicalOuterOnOrdinaryRestrictionSpan iota hinj blocks S D

theorem brauerBasis_value
    {S : Fi24ThreeBlockSource (k := k) (X := X)}
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (phi : BrauerFibre iota hinj blocks S.nonprincipalBlock) :
    ((BrauerRestrictionSpaceBinding.brauerBasis iota hinj blocks D phi :
      ordinaryRestrictionSpan iota hinj blocks D) :
      PrimeRegularFunction K X 3) = phi.1.1.toFun :=
  ordinaryRestrictionBrauerBasis_value iota hinj blocks S D phi

theorem outerAction_value
    {S : Fi24ThreeBlockSource (k := k) (X := X)}
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (v : ordinaryRestrictionSpan iota hinj blocks D) :
    ((BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D v :
      ordinaryRestrictionSpan iota hinj blocks D) :
      PrimeRegularFunction K X 3) = (v.1).pullback S.outer.unop.toMonoidHom :=
  canonicalOuterOnOrdinaryRestrictionSpan_value iota hinj blocks S D v

/-- The existing canonical fibre permutation is recovered from the
kernel-constructed span action.  It is a theorem, never a source field. -/
theorem basis_action
    {S : Fi24ThreeBlockSource (k := k) (X := X)}
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (phi : BrauerFibre iota hinj blocks S.nonprincipalBlock) :
    BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D
      (BrauerRestrictionSpaceBinding.brauerBasis iota hinj blocks D phi) =
      BrauerRestrictionSpaceBinding.brauerBasis iota hinj blocks D
        (nonprincipalBrauerPerm iota hinj blocks E1 S phi) := by
  have hperm :
      nonprincipalBrauerPerm iota hinj blocks E1 S phi =
        outerOnB1Brauer iota hinj blocks S phi := by
    apply Subtype.ext
    simp only [nonprincipalBrauerPerm, brauerFibrePerm,
      Formalisation.stabilizerFibreEquiv_coe, outerOnB1Brauer]
  apply Subtype.ext
  calc
    ((outerAction iota hinj blocks D
        (brauerBasis iota hinj blocks D phi) :
        ordinaryRestrictionSpan iota hinj blocks D) :
        PrimeRegularFunction K X 3) =
        ((brauerBasis iota hinj blocks D phi :
          ordinaryRestrictionSpan iota hinj blocks D) :
          PrimeRegularFunction K X 3).pullback S.outer.unop.toMonoidHom :=
      outerAction_value iota hinj blocks D (brauerBasis iota hinj blocks D phi)
    _ = phi.1.1.toFun.pullback S.outer.unop.toMonoidHom :=
      congrArg (fun f : PrimeRegularFunction K X 3 =>
        f.pullback S.outer.unop.toMonoidHom)
        (brauerBasis_value iota hinj blocks D phi)
    _ = (outerOnB1Brauer iota hinj blocks S phi).1.1.toFun :=
      canonicalOuterPullbackLinear_b1BrauerFunction iota hinj blocks S phi
    _ = (nonprincipalBrauerPerm iota hinj blocks E1 S phi).1.1.toFun :=
      congrArg
        (fun theta : BrauerFibre iota hinj blocks S.nonprincipalBlock =>
          theta.1.1.toFun) hperm.symm
    _ = ((brauerBasis iota hinj blocks D
        (nonprincipalBrauerPerm iota hinj blocks E1 S phi) :
        ordinaryRestrictionSpan iota hinj blocks D) :
        PrimeRegularFunction K X 3) :=
      (brauerBasis_value iota hinj blocks D
        (nonprincipalBrauerPerm iota hinj blocks E1 S phi)).symm

end BrauerRestrictionSpaceBinding

end ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
