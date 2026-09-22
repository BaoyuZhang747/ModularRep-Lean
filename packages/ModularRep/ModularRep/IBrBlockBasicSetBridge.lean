import ModularRep.DecompositionBasicSetBridge
import ModularRep.IBrBlock

/-!
# Integral basic sets with the actual `IBr` block fibre

`DecompositionBasicSetBridge` deliberately permits an abstract modular label
set.  This file specialises that construction to the function-valued set of
irreducible Brauer characters belonging to one supplied block-idempotent
fibre.  Thus an application no longer has to postulate an injective map from
an arbitrary set of "Brauer labels" to simple module classes: the inverse of
the kernel-checked simple-module/`IBr` equivalence supplies that map.

The existence of the block-idempotent decomposition, the compatible root
embedding, the ordinary basic set, and equivariance of the resulting exact
decomposition matrix remain explicit inputs.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.IBrBlockBasicSetBridge

open DecompositionBasicSetBridge
open ExactGrothendieckGroup
open FDRepSimpleClassKZero
open IntegralBasicSetBridge

universe u w

variable {p : ℕ} {K O k G : Type u} {ι : Type w}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K]
variable [Group G] [Finite G] [Fintype ι]
variable [CharP k p] [IsAlgClosed k]

/-- The simple-module class afforded by a function-valued irreducible Brauer
character in a fixed block fibre. -/
def ibrBlockSimpleLabel
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι) :
    IBrBlock iota hinj blocks block → SimpleModuleClass k[G] :=
  fun phi =>
    ((simpleModuleClassBlockEquivIBrBlock iota hinj blocks block).symm phi).1

/-- The actual `IBr` block labels are distinct as simple-module classes. -/
theorem ibrBlockSimpleLabel_injective
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι) :
    Function.Injective (ibrBlockSimpleLabel iota hinj blocks block) := by
  intro phi psi h
  apply (simpleModuleClassBlockEquivIBrBlock
    iota hinj blocks block).symm.injective
  apply Subtype.ext
  exact h

/-- The simple-module label attached to a member of `IBr(b)` affords its
underlying function-valued Brauer character. -/
@[simp]
theorem brauerCharacter_ibrBlockSimpleLabel
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι) (phi : IBrBlock iota hinj blocks block) :
    Representation.brauerCharacterOfRootEmbedding
        (simpleClassFDRep
          (ibrBlockSimpleLabel iota hinj blocks block phi)).ρ iota =
      phi.1.1 := by
  change
    (simpleClassToIBr iota
      ((simpleModuleClassEquivIBr iota hinj).symm phi.1)).1 = phi.1.1
  exact congrArg Subtype.val
    ((simpleModuleClassEquivIBr iota hinj).apply_symm_apply phi.1)

/-- A source-shaped integral basic set whose modular side is literally the
function-valued set `IBr(b)` determined by a supplied block-idempotent
decomposition.

The restriction equation says that the displayed integral equivalence is the
restriction of the exact decomposition homomorphism.  It contains no action,
equivariance assumption, or separately chosen modular labelling map. -/
structure RestrictedIntegralBasicSetOnIBrBlock
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι)
    (Basic : Type u)
    (decomposition : FDRepKZero K G →+ FDRepKZero k G) where
  ordinaryLabel : Basic → SimpleModuleClass K[G]
  ordinaryLabel_injective : Function.Injective ordinaryLabel
  linearEquiv :
    MonoidAlgebra ℤ Basic ≃ₗ[ℤ]
      MonoidAlgebra ℤ (IBrBlock iota hinj blocks block)
  restricts_decomposition : ∀ v : MonoidAlgebra ℤ Basic,
    labelledSimpleClassKZero
        (ibrBlockSimpleLabel iota hinj blocks block) (linearEquiv v) =
      decomposition (labelledSimpleClassKZero ordinaryLabel v)

namespace RestrictedIntegralBasicSetOnIBrBlock

variable {Basic : Type u}
variable {decomposition : FDRepKZero K G →+ FDRepKZero k G}
variable {blockIdempotent : ι → k[G]}
variable {iota : PrimeRegularRootEmbedding p k K G}
variable {hinj : IrreducibleBrauerCharacterInjectivity iota}
variable {blocks : BlockIdempotentDecomposition blockIdempotent}
variable {block : ι}

/-- Forgetting that the modular labels are actual Brauer characters gives the
general exact-`K₀` basic-set interface.  Its modular-label injectivity is a
kernel theorem, not an application hypothesis. -/
def toRestrictedIntegralBasicSet
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic decomposition) :
    RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G)
      (Basic := Basic) (Brauer := IBrBlock iota hinj blocks block)
      decomposition where
  ordinaryLabel := D.ordinaryLabel
  ordinaryLabel_injective := D.ordinaryLabel_injective
  modularLabel := ibrBlockSimpleLabel iota hinj blocks block
  modularLabel_injective :=
    ibrBlockSimpleLabel_injective iota hinj blocks block
  linearEquiv := D.linearEquiv
  restricts_decomposition := D.restricts_decomposition

@[simp]
theorem toRestrictedIntegralBasicSet_linearEquiv
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic decomposition) :
    D.toRestrictedIntegralBasicSet.linearEquiv = D.linearEquiv := rfl

section AutomorphismBlockAction

variable {A : Type u} [Group A]

/-- Exact stability of one Brauer-character block fibre under a supplied
group of automorphisms.  This is the block-theoretic input needed to restrict
the already constructed action on `IBr(G)`; it does not contain a chosen
action on the fibre or any character bijection. -/
def IsAutomorphismStableIBrBlock
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι) : Prop :=
  ∀ (a : A) (phi : IBr iota),
    irreducibleBrauerCharacterBlock iota hinj blocks phi = block →
      irreducibleBrauerCharacterBlock iota hinj blocks
        (automorphism a • phi) = block

/-- Equivariance of the block-index map under the action induced by group
automorphisms.  In applications this is the precise consequence supplied by
automorphism invariance of the block-idempotent decomposition. -/
def IsEquivariantIBrBlockIndex
    [MulAction A ι]
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent) : Prop :=
  ∀ (a : A) (phi : IBr iota),
    irreducibleBrauerCharacterBlock iota hinj blocks
        (automorphism a • phi) =
      a • irreducibleBrauerCharacterBlock iota hinj blocks phi

/-- Equivariance of the block-index map and fixation of one block imply
stability of its `IBr` fibre. -/
theorem isAutomorphismStableIBrBlock_of_equivariantBlockIndex
    [MulAction A ι]
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι)
    (hindex : IsEquivariantIBrBlockIndex automorphism iota hinj blocks)
    (hfixed : ∀ a : A, a • block = block) :
    IsAutomorphismStableIBrBlock automorphism iota hinj blocks block := by
  intro a phi hphi
  rw [hindex a phi, hphi, hfixed a]

/-- Restrict the actual automorphism action on function-valued irreducible
Brauer characters to an invariant block fibre. -/
def automorphismIBrBlockSmul
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (a : A) (phi : IBrBlock iota hinj blocks block) :
    IBrBlock iota hinj blocks block :=
  ⟨automorphism a • phi.1, hstable a phi.1 phi.2⟩

@[simp]
theorem automorphismIBrBlockSmul_val
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (a : A) (phi : IBrBlock iota hinj blocks block) :
    (automorphismIBrBlockSmul automorphism hstable a phi).1 =
      automorphism a • phi.1 :=
  rfl

/-- On character functions, the restricted action is exactly pullback by the
supplied group automorphism and uses the same root embedding `iota`. -/
@[simp]
theorem automorphismIBrBlockSmul_character
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (a : A) (phi : IBrBlock iota hinj blocks block) :
    (automorphismIBrBlockSmul automorphism hstable a phi).1.1 =
      phi.1.1.twist (automorphism a).unop :=
  rfl

/-- The canonical action on an invariant function-valued `IBr` block fibre.
Its action law is inherited from the opposite-automorphism action on
`IBr(G)`. -/
@[instance_reducible]
def automorphismIBrBlockMulAction
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block) :
    MulAction A (IBrBlock iota hinj blocks block) where
  smul := automorphismIBrBlockSmul automorphism hstable
  one_smul phi := by
    apply Subtype.ext
    change automorphism 1 • phi.1 = phi.1
    rw [map_one, one_smul]
  mul_smul a c phi := by
    apply Subtype.ext
    change automorphism (a * c) • phi.1 =
      automorphism a • (automorphism c • phi.1)
    rw [map_mul, mul_smul]

/-- The canonical action on `IBr(b)` is realised on exact `K₀` by twisting
the corresponding simple modular representation.  This removes the modular
half of `TwistCompatibleLabels` as an application hypothesis. -/
theorem labelledSimpleClassKZero_automorphismIBrBlockSmul
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (a : A) (phi : IBrBlock iota hinj blocks block) :
    labelledSimpleClassKZero (ibrBlockSimpleLabel iota hinj blocks block)
        (MonoidAlgebra.single
          (automorphismIBrBlockSmul automorphism hstable a phi) 1) =
      twistKZero (k := k) (automorphism a).unop
        (labelledSimpleClassKZero
          (ibrBlockSimpleLabel iota hinj blocks block)
          (MonoidAlgebra.single phi 1)) := by
  apply brauerCharacterKZeroHom_injective iota
  rw [labelledSimpleClassKZero_single,
    labelledSimpleClassKZero_single]
  have htwist := DFunLike.congr_fun
    (brauerCharacterKZeroHom_twist
      (k := k) iota (automorphism a).unop)
    (simpleClassToFDRepKZeroGenerator
      (ibrBlockSimpleLabel iota hinj blocks block phi))
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at htwist
  rw [simpleClassToFDRepKZeroGenerator,
    brauerCharacterKZeroHom_classOf]
  rw [brauerCharacter_ibrBlockSimpleLabel]
  rw [htwist]
  rw [simpleClassToFDRepKZeroGenerator,
    brauerCharacterKZeroHom_classOf,
    brauerCharacter_ibrBlockSimpleLabel]
  change
    (automorphismIBrBlockSmul automorphism hstable a phi).1.1 =
      phi.1.1.twist (automorphism a).unop
  exact automorphismIBrBlockSmul_character automorphism hstable a phi

end AutomorphismBlockAction

section Equivariance

variable {A : Type u} [Group A]
variable [MulAction A Basic]
variable [MulAction A (IBrBlock iota hinj blocks block)]

/-- Exact `K₀` naturality and the two standard mark theorems produce an
equivariant bijection from the ordinary basic-set labels to the actual
function-valued Brauer characters in the fixed block. -/
theorem equivariantIBrBlockEquiv_of_kZero_naturality
    {conlonPrime : ℕ} [Fact conlonPrime.Prime]
    [Finite A] [Finite Basic]
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic decomposition)
    (hact : LabelledKZeroActionData (A := A)
      D.toRestrictedIntegralBasicSet)
    (hnatural : DecompositionNatural (A := A) decomposition
      hact.ordinaryAction hact.modularAction)
    (ambientHypoelementary : IsPHypoelementary conlonPrime A)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := conlonPrime) (A := A))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := A)) :
    ∃ e : Basic ≃ IBrBlock iota hinj blocks block,
      ∀ (a : A) (x : Basic), e (a • x) = a • e x :=
  DecompositionBasicSetBridge.equivariantSetEquiv_of_kZero_naturality
    D.toRestrictedIntegralBasicSet hact hnatural
    ambientHypoelementary conlon burnside

/-- Stable-reduction specialisation of the preceding theorem.  The modular
endpoint is still the literal `IBr` block fibre. -/
theorem equivariantIBrBlockEquiv_of_stableReduction
    {conlonPrime : ℕ} [Fact conlonPrime.Prime]
    [Finite A] [Finite Basic]
    (Msys : ModularSystem p K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic
        (decompositionMapOfStableReduction Msys iota hcompat))
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hlabels : TwistCompatibleLabels
      D.toRestrictedIntegralBasicSet automorphism)
    (ambientHypoelementary : IsPHypoelementary conlonPrime A)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := conlonPrime) (A := A))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := A)) :
    ∃ e : Basic ≃ IBrBlock iota hinj blocks block,
      ∀ (a : A) (x : Basic), e (a • x) = a • e x :=
  DecompositionBasicSetBridge.equivariantSetEquiv_of_stableReduction
    Msys iota hcompat D.toRestrictedIntegralBasicSet automorphism hlabels
    ambientHypoelementary conlon burnside

end Equivariance

section CanonicalAutomorphismEquivariance

variable {A : Type u} [Group A] [MulAction A Basic]

/-- Compatibility of the ordinary basic-set labels with automorphism
twisting.  For the canonical action on `IBr(b)`, the corresponding modular
compatibility is proved by the kernel and is therefore absent from this
input. -/
structure OrdinaryTwistCompatibleLabels
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic decomposition)
    (automorphism : A →* (MulAut G)ᵐᵒᵖ) : Prop where
  ordinary_single : ∀ (a : A) (x : Basic),
    labelledSimpleClassKZero D.ordinaryLabel
        (MonoidAlgebra.single (a • x) 1) =
      twistKZero (k := K) (automorphism a).unop
        (labelledSimpleClassKZero D.ordinaryLabel
          (MonoidAlgebra.single x 1))

/-- Complete twist compatibility obtained from ordinary-label compatibility
and the canonical action on the invariant `IBr` block fibre. -/
theorem twistCompatibleLabelsOfAutomorphismStableBlock
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic decomposition)
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (hordinary : OrdinaryTwistCompatibleLabels D automorphism) :
    let _ : MulAction A (IBrBlock iota hinj blocks block) :=
      automorphismIBrBlockMulAction automorphism hstable
    TwistCompatibleLabels D.toRestrictedIntegralBasicSet automorphism := by
  dsimp only
  let _ : MulAction A (IBrBlock iota hinj blocks block) :=
    automorphismIBrBlockMulAction automorphism hstable
  refine ⟨hordinary.ordinary_single, ?_⟩
  intro a phi
  change
    labelledSimpleClassKZero (ibrBlockSimpleLabel iota hinj blocks block)
        (MonoidAlgebra.single
          (automorphismIBrBlockSmul automorphism hstable a phi) 1) =
      twistKZero (k := k) (automorphism a).unop
        (labelledSimpleClassKZero
          (ibrBlockSimpleLabel iota hinj blocks block)
          (MonoidAlgebra.single phi 1))
  exact labelledSimpleClassKZero_automorphismIBrBlockSmul
    automorphism hstable a phi

/-- For a general exact decomposition map natural under automorphism twists,
the ordinary basic-set compatibility and exact stability of the block are
the only action-related inputs.  The action on `IBr(b)` and its modular
`K₀` compatibility are constructed by the kernel. -/
theorem equivariantIBrBlockEquiv_of_automorphism_naturality
    {conlonPrime : ℕ} [Fact conlonPrime.Prime]
    [Finite A] [Finite Basic]
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic decomposition)
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (hordinary : OrdinaryTwistCompatibleLabels D automorphism)
    (hnatural : DecompositionNatural (A := A) decomposition
      ((twistKZeroRepresentation (k := K) (G := G)).pullback automorphism)
      ((twistKZeroRepresentation (k := k) (G := G)).pullback automorphism)) :
    let _ : MulAction A (IBrBlock iota hinj blocks block) :=
      automorphismIBrBlockMulAction automorphism hstable
    ∀ (_ambientHypoelementary : IsPHypoelementary conlonPrime A)
      (_conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
        (p := conlonPrime) (A := A))
      (_burnside :
        PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
          (A := A)),
      ∃ e : Basic ≃ IBrBlock iota hinj blocks block,
        ∀ (a : A) (x : Basic), e (a • x) = a • e x := by
  dsimp only
  let _ : MulAction A (IBrBlock iota hinj blocks block) :=
    automorphismIBrBlockMulAction automorphism hstable
  intro ambientHypoelementary conlon burnside
  let hlabels : TwistCompatibleLabels
      D.toRestrictedIntegralBasicSet automorphism :=
    twistCompatibleLabelsOfAutomorphismStableBlock
      D automorphism hstable hordinary
  exact equivariantIBrBlockEquiv_of_kZero_naturality D
    (twistLabelledKZeroActionData
      D.toRestrictedIntegralBasicSet automorphism hlabels)
    hnatural ambientHypoelementary conlon burnside

/-- Stable reduction supplies automorphism naturality, so an invariant block,
ordinary-label compatibility, and the two standard mark theorems produce the
equivariant bijection with the literal function-valued set `IBr(b)`. -/
theorem equivariantIBrBlockEquiv_of_stableReduction_canonical
    {conlonPrime : ℕ} [Fact conlonPrime.Prime]
    [Finite A] [Finite Basic]
    (Msys : ModularSystem p K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic
        (decompositionMapOfStableReduction Msys iota hcompat))
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (hordinary : OrdinaryTwistCompatibleLabels D automorphism) :
    let _ : MulAction A (IBrBlock iota hinj blocks block) :=
      automorphismIBrBlockMulAction automorphism hstable
    ∀ (_ambientHypoelementary : IsPHypoelementary conlonPrime A)
      (_conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
        (p := conlonPrime) (A := A))
      (_burnside :
        PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
          (A := A)),
      ∃ e : Basic ≃ IBrBlock iota hinj blocks block,
        ∀ (a : A) (x : Basic), e (a • x) = a • e x := by
  dsimp only
  let _ : MulAction A (IBrBlock iota hinj blocks block) :=
    automorphismIBrBlockMulAction automorphism hstable
  intro ambientHypoelementary conlon burnside
  exact equivariantIBrBlockEquiv_of_stableReduction
    Msys hcompat D automorphism
    (twistCompatibleLabelsOfAutomorphismStableBlock
      D automorphism hstable hordinary)
    ambientHypoelementary conlon burnside

end CanonicalAutomorphismEquivariance

end RestrictedIntegralBasicSetOnIBrBlock

end ModularRep.IBrBlockBasicSetBridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
