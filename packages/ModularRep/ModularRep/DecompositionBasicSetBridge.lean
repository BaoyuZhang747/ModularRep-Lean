import ModularRep.BrauerDecompositionMap
import ModularRep.IntegralBasicSetBridge
import ModularRep.PaperProofs.ConlonBasicSet
import Mathlib.Algebra.FreeAbelianGroup.Finsupp

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.DecompositionBasicSetBridge

open ExactGrothendieckGroup
open FDRepSimpleClassKZero
open IntegralBasicSetBridge
open PaperProofs.ConlonBasicSet

universe u v

variable {p : ℕ} {K O k G : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [Group G] [Finite G]

/-- The homomorphism from the free integral module on a labelled family of
simple modules to the exact Grothendieck group. -/
noncomputable def labelledSimpleClassKZero
    {F X : Type u} [Field F]
    (label : X → SimpleModuleClass F[G]) :
    MonoidAlgebra ℤ X →+ FDRepKZero F G :=
  (simpleClassToFDRepKZero (k := F) (G := G)).comp
    ((FreeAbelianGroup.map label).comp
      ((Finsupp.toFreeAbelianGroup (X := X)).comp
        MonoidAlgebra.coeffAddEquiv.toAddMonoidHom))

@[simp]
theorem labelledSimpleClassKZero_single
    {F X : Type u} [Field F]
    (label : X → SimpleModuleClass F[G]) (x : X) :
    labelledSimpleClassKZero label (MonoidAlgebra.single x 1) =
      simpleClassToFDRepKZeroGenerator (label x) := by
  change
    simpleClassToFDRepKZero
        (FreeAbelianGroup.map label
          (Finsupp.toFreeAbelianGroup
            (MonoidAlgebra.single x 1).coeff)) =
      simpleClassToFDRepKZeroGenerator (label x)
  rw [MonoidAlgebra.coeff_single,
    Finsupp.toFreeAbelianGroup_single,
    one_zsmul, FreeAbelianGroup.map_of_apply,
    simpleClassToFDRepKZero, FreeAbelianGroup.lift_apply_of]

/-- Mapping generators of a free abelian group along an injective function is
injective. -/
theorem freeAbelianGroup_map_injective
    {X Y : Type*} {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (FreeAbelianGroup.map f) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      let _ : IsEmpty X := hX
      intro x y _
      exact Subsingleton.elim x y
  | inr hX =>
      let _ : Nonempty X := hX
      let g : Y → X := Function.invFun f
      have hgf : Function.LeftInverse g f := Function.leftInverse_invFun hf
      intro x y hxy
      have h := congrArg (FreeAbelianGroup.map g) hxy
      rw [← FreeAbelianGroup.map_comp_apply,
        ← FreeAbelianGroup.map_comp_apply, hgf.id,
        FreeAbelianGroup.map_id_apply,
        FreeAbelianGroup.map_id_apply] at h
      exact h

/-- Distinct simple-module labels give an injective map from their free
integral module into exact `K₀`. -/
theorem labelledSimpleClassKZero_injective
    {F X : Type u} [Field F]
    (label : X → SimpleModuleClass F[G])
    (hlabel : Function.Injective label) :
    Function.Injective (labelledSimpleClassKZero label) := by
  intro x y hxy
  change
    simpleClassToFDRepKZero
        (FreeAbelianGroup.map label
          (Finsupp.toFreeAbelianGroup x.coeff)) =
      simpleClassToFDRepKZero
        (FreeAbelianGroup.map label
          (Finsupp.toFreeAbelianGroup y.coeff)) at hxy
  have hxy := Function.LeftInverse.injective
    (fdRepSimpleJordanHolderHom_simpleClassToFDRepKZero
      (k := F) (G := G)) hxy
  have hxy := freeAbelianGroup_map_injective hlabel hxy
  have hxy := Function.LeftInverse.injective
    FreeAbelianGroup.toFinsupp_toFreeAbelianGroup hxy
  exact MonoidAlgebra.coeff_injective hxy

variable {Basic Brauer A : Type u}
variable [Group A] [MulAction A Basic] [MulAction A Brauer]
variable {decomposition : FDRepKZero K G →+ FDRepKZero k G}

/-- A source-shaped formulation of an integral basic set for a specified
exact decomposition map.

It supplies distinct ordinary and modular simple-module labels, an integral
linear equivalence between their free modules, and the assertion that this
linear equivalence is literally the restriction of the specified
decomposition homomorphism.  It contains no equivariance or bijection between
the two label sets. -/
structure RestrictedIntegralBasicSet
    (decomposition : FDRepKZero K G →+ FDRepKZero k G) where
  ordinaryLabel : Basic → SimpleModuleClass K[G]
  ordinaryLabel_injective : Function.Injective ordinaryLabel
  modularLabel : Brauer → SimpleModuleClass k[G]
  modularLabel_injective : Function.Injective modularLabel
  linearEquiv :
    MonoidAlgebra ℤ Basic ≃ₗ[ℤ] MonoidAlgebra ℤ Brauer
  restricts_decomposition : ∀ v : MonoidAlgebra ℤ Basic,
    labelledSimpleClassKZero modularLabel (linearEquiv v) =
      decomposition (labelledSimpleClassKZero ordinaryLabel v)

/-- Source-shaped compatibility between the actions on the two label sets
and automorphism twisting of the represented simple modules. -/
structure TwistCompatibleLabels
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := Basic) (Brauer := Brauer)
      decomposition)
    (automorphism : A →* (MulAut G)ᵐᵒᵖ) : Prop where
  ordinary_single : ∀ (a : A) (x : Basic),
    labelledSimpleClassKZero D.ordinaryLabel
        (MonoidAlgebra.single (a • x) 1) =
      twistKZero (k := K) (automorphism a).unop
        (labelledSimpleClassKZero D.ordinaryLabel
          (MonoidAlgebra.single x 1))
  modular_single : ∀ (a : A) (y : Brauer),
    labelledSimpleClassKZero D.modularLabel
        (MonoidAlgebra.single (a • y) 1) =
      twistKZero (k := k) (automorphism a).unop
        (labelledSimpleClassKZero D.modularLabel
          (MonoidAlgebra.single y 1))

/-- Additive maps on the two exact Grothendieck groups which realise the
given actions on the ordinary and modular labels.

This data does not assume that the restricted decomposition matrix is
equivariant.  For the tensor and field action in the conformal-group
application, the two representations are induced by tensoring and twisting
on exact `K₀`.  For a pure automorphism action they are restrictions of
`twistKZeroRepresentation`. -/
structure LabelledKZeroActionData
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := Basic) (Brauer := Brauer)
      decomposition) where
  ordinaryAction : Representation ℤ A (FDRepKZero K G)
  modularAction : Representation ℤ A (FDRepKZero k G)
  ordinary_single : ∀ (a : A) (x : Basic),
    labelledSimpleClassKZero D.ordinaryLabel
        (MonoidAlgebra.single (a • x) 1) =
      ordinaryAction a
        (labelledSimpleClassKZero D.ordinaryLabel
          (MonoidAlgebra.single x 1))
  modular_single : ∀ (a : A) (y : Brauer),
    labelledSimpleClassKZero D.modularLabel
        (MonoidAlgebra.single (a • y) 1) =
      modularAction a
        (labelledSimpleClassKZero D.modularLabel
          (MonoidAlgebra.single y 1))

/-- Naturality of a decomposition homomorphism with respect to specified
actions on its source and target exact Grothendieck groups. -/
def DecompositionNatural
    (decomposition : FDRepKZero K G →+ FDRepKZero k G)
    (ordinaryAction : Representation ℤ A (FDRepKZero K G))
    (modularAction : Representation ℤ A (FDRepKZero k G)) : Prop :=
  ∀ (a : A) (x : FDRepKZero K G),
    decomposition (ordinaryAction a x) =
      modularAction a (decomposition x)

/-- Compatibility on the labelled generators determines compatibility on
their entire integral permutation module. -/
theorem labelledSimpleClassKZero_actionOf
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := Basic) (Brauer := Brauer)
      decomposition)
    (h : LabelledKZeroActionData D)
    (a : A) (v : MonoidAlgebra ℤ Basic) :
    labelledSimpleClassKZero D.ordinaryLabel
        (Representation.ofMulAction ℤ A Basic a v) =
      h.ordinaryAction a (labelledSimpleClassKZero D.ordinaryLabel v) := by
  let lhs : MonoidAlgebra ℤ Basic →ₗ[ℤ] FDRepKZero K G :=
    (labelledSimpleClassKZero D.ordinaryLabel).toIntLinearMap.comp
      (Representation.ofMulAction ℤ A Basic a)
  let rhs : MonoidAlgebra ℤ Basic →ₗ[ℤ] FDRepKZero K G :=
    (h.ordinaryAction a).comp
      (labelledSimpleClassKZero D.ordinaryLabel).toIntLinearMap
  have hlr : lhs = rhs := by
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simpa [lhs, rhs] using h.ordinary_single a x
  exact DFunLike.congr_fun hlr v

/-- The analogous generator argument for the modular labels. -/
theorem labelledModularSimpleClassKZero_actionOf
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := Basic) (Brauer := Brauer)
      decomposition)
    (h : LabelledKZeroActionData D)
    (a : A) (v : MonoidAlgebra ℤ Brauer) :
    labelledSimpleClassKZero D.modularLabel
        (Representation.ofMulAction ℤ A Brauer a v) =
      h.modularAction a (labelledSimpleClassKZero D.modularLabel v) := by
  let lhs : MonoidAlgebra ℤ Brauer →ₗ[ℤ] FDRepKZero k G :=
    (labelledSimpleClassKZero D.modularLabel).toIntLinearMap.comp
      (Representation.ofMulAction ℤ A Brauer a)
  let rhs : MonoidAlgebra ℤ Brauer →ₗ[ℤ] FDRepKZero k G :=
    (h.modularAction a).comp
      (labelledSimpleClassKZero D.modularLabel).toIntLinearMap
  have hlr : lhs = rhs := by
    apply MonoidAlgebra.lhom_ext'
    intro y
    apply LinearMap.ext_ring
    simpa [lhs, rhs] using h.modular_single a y
  exact DFunLike.congr_fun hlr v

/-- Naturality of the exact decomposition homomorphism with respect to
source-shaped `K₀` actions forces equivariance of its restricted matrix. -/
theorem matrixEquivariant_of_kZero_naturality
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := Basic) (Brauer := Brauer)
      decomposition)
    (hact : LabelledKZeroActionData (A := A) D)
    (hnatural : DecompositionNatural (A := A) decomposition
      hact.ordinaryAction hact.modularAction) :
    MatrixEquivariant (A := A) D.linearEquiv.toLinearMap := by
  apply (matrixEquivariant_iff_intertwining D.linearEquiv.toLinearMap).2
  intro a
  apply LinearMap.ext
  intro v
  apply labelledSimpleClassKZero_injective
    D.modularLabel D.modularLabel_injective
  calc
    labelledSimpleClassKZero D.modularLabel
        (D.linearEquiv
          (Representation.ofMulAction ℤ A Basic a v)) =
        decomposition
          (labelledSimpleClassKZero D.ordinaryLabel
            (Representation.ofMulAction ℤ A Basic a v)) :=
      D.restricts_decomposition _
    _ = decomposition
        (hact.ordinaryAction a
          (labelledSimpleClassKZero D.ordinaryLabel v)) := by
      rw [labelledSimpleClassKZero_actionOf D hact a v]
    _ = hact.modularAction a
        (decomposition
          (labelledSimpleClassKZero D.ordinaryLabel v)) :=
      hnatural a _
    _ = hact.modularAction a
        (labelledSimpleClassKZero D.modularLabel (D.linearEquiv v)) := by
      rw [D.restricts_decomposition]
    _ = labelledSimpleClassKZero D.modularLabel
        (Representation.ofMulAction ℤ A Brauer a (D.linearEquiv v)) :=
      (labelledModularSimpleClassKZero_actionOf
        D hact a (D.linearEquiv v)).symm

/-- Automorphism twisting realises compatible actions on the labelled
simple-module classes. -/
noncomputable def twistLabelledKZeroActionData
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := Basic) (Brauer := Brauer)
      decomposition)
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hlabels : TwistCompatibleLabels D automorphism) :
    LabelledKZeroActionData (A := A) D where
  ordinaryAction :=
    (twistKZeroRepresentation (k := K) (G := G)).pullback automorphism
  modularAction :=
    (twistKZeroRepresentation (k := k) (G := G)).pullback automorphism
  ordinary_single := hlabels.ordinary_single
  modular_single := hlabels.modular_single

/-- For stable reduction and a pure automorphism action, matrix equivariance
is a kernel deduction from twist naturality. -/
theorem matrixEquivariant_of_stableReduction
    [IsAlgClosed k]
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := Basic) (Brauer := Brauer)
      (decompositionMapOfStableReduction Msys iota hcompat))
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hlabels : TwistCompatibleLabels D automorphism) :
    MatrixEquivariant (A := A) D.linearEquiv.toLinearMap :=
  matrixEquivariant_of_kZero_naturality D
    (twistLabelledKZeroActionData (A := A) D automorphism hlabels)
    (fun a x ↦ decompositionMapOfStableReduction_twist
      Msys iota hcompat (automorphism a).unop x)

/-- Exact `K₀` naturality, Conlon mark detection, and injectivity of the
Burnside mark map imply an equivariant bijection of the ordinary basic-set
labels with the modular labels. -/
theorem equivariantSetEquiv_of_kZero_naturality
    {conlonPrime : ℕ} [Fact conlonPrime.Prime]
    [Finite A] [Finite Basic] [Finite Brauer]
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := Basic) (Brauer := Brauer)
      decomposition)
    (hact : LabelledKZeroActionData (A := A) D)
    (hnatural : DecompositionNatural (A := A) decomposition
      hact.ordinaryAction hact.modularAction)
    (ambientHypoelementary : IsPHypoelementary conlonPrime A)
    (conlon : PadicConlonMarkDetection.{u, u}
      (p := conlonPrime) (A := A))
    (burnside : PublishedBurnsideMarkInjectivity.{u, u} (A := A)) :
    ∃ e : Basic ≃ Brauer, ∀ (a : A) (x : Basic), e (a • x) = a • e x := by
  have hmatrix := matrixEquivariant_of_kZero_naturality D hact hnatural
  let integralLatticeEquiv := permutationLatticeEquiv D.linearEquiv hmatrix
  exact corollary_2_4_conlonMark ambientHypoelementary
    ⟨permutationLatticeEquivBaseChange
      (S := ℤ_[conlonPrime]) integralLatticeEquiv⟩ conlon burnside

/-- In the pure automorphism case, stable-lattice compatibility supplies
the naturality input, so the complete integral-basic-set argument follows. -/
theorem equivariantSetEquiv_of_stableReduction
    {conlonPrime : ℕ} [Fact conlonPrime.Prime]
    [Finite A] [Finite Basic] [Finite Brauer]
    [IsAlgClosed k]
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := Basic) (Brauer := Brauer)
      (decompositionMapOfStableReduction Msys iota hcompat))
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hlabels : TwistCompatibleLabels D automorphism)
    (ambientHypoelementary : IsPHypoelementary conlonPrime A)
    (conlon : PadicConlonMarkDetection.{u, u}
      (p := conlonPrime) (A := A))
    (burnside : PublishedBurnsideMarkInjectivity.{u, u} (A := A)) :
    ∃ e : Basic ≃ Brauer, ∀ (a : A) (x : Basic), e (a • x) = a • e x := by
  have hmatrix := matrixEquivariant_of_stableReduction
    Msys iota hcompat D automorphism hlabels
  let integralLatticeEquiv := permutationLatticeEquiv D.linearEquiv hmatrix
  exact corollary_2_4_conlonMark ambientHypoelementary
    ⟨permutationLatticeEquivBaseChange
      (S := ℤ_[conlonPrime]) integralLatticeEquiv⟩ conlon burnside

end ModularRep.DecompositionBasicSetBridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
