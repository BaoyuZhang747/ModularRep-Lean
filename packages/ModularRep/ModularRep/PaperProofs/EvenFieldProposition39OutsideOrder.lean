import ModularRep.PrimeOutsideOrder
import ModularRep.SemisimpleBlockSimpleClass
import ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
import Mathlib.RepresentationTheory.Maschke

/-!
# The prime-outside-order branch of even-field Proposition 3.9

This module replaces the former conclusion-shaped input for the branch in
which the coefficient prime `ell` does not divide the order of the presented
finite group.  The elementary and quotient-level consequences are proved in
the kernel:

* Maschke semisimplicity of the modular group algebra;
* uniqueness of the simple-module class supported by each primitive block;
* triviality of every radical subgroup and radical conjugacy class;
* construction of the unique block weight from a defect-zero character at
  the trivial radical;
* transport of the kernel-derived simple-module class to the literal Brauer
  fibre;
* the equivalence of the two singleton fibres and its equivariance.

The project still has no coprime ordinary/Brauer block correspondence on the
literal carriers and no formalisation of the modular-character-triple
relation `>=_b`.  `OutsideOrderSource` therefore retains the order exclusion,
one defect-zero local ordinary character with its block assignment and
uniqueness, and the fixed Definition 3.5 block-isomorphism relation for the
resulting selected pair.  It contains no simple-module singleton data,
Brauer--weight equivalence, equivariance field, iBAW predicate, or
`Definition35IBAWBijection` conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldProposition39OutsideOrder

open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-! ## Kernel consequences of coprimality -/

/-- Maschke's theorem in the exact characteristic-`p` form used here.

The coprimality hypothesis supplies the nonzero scalar required by the
Mathlib group algebra instance. -/
theorem monoidAlgebra_isSemisimpleRing_of_not_dvd_card
    {p : ℕ} {k G : Type*} [Field k] [Group G] [Finite G]
    [CharP k p] (hpG : ¬ p ∣ Nat.card G) :
    IsSemisimpleRing k[G] := by
  letI : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hpG
  infer_instance

/-- Every literal character weight has trivial radical when `p` is outside
the ambient group order. -/
theorem characterWeight_subgroup_eq_bot_of_not_dvd_card
    {p : ℕ} {K G : Type u} [Field K] [CharZero K]
    [Group G] [Finite G] (hp : p.Prime) (hpG : ¬ p ∣ Nat.card G)
    (W : CharacterWeight p K G) : W.subgroup = ⊥ :=
  (isRadicalSubgroup_iff_eq_bot_of_not_dvd_card hp hpG W.subgroup).mp
    W.radical

/-- Every literal conjugacy class of radical subgroups is the class of the
trivial subgroup.  This is the quotient-level form of the object theorem in
`PrimeOutsideOrder`. -/
theorem radicalConjugacyClass_eq_trivialClass_of_not_dvd_card
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hpG : ¬ p ∣ Nat.card G)
    (q : RadicalConjugacyClass (p := p) (G := G)) :
    q = RadicalConjugacyClass.trivialClass
      (bot_isRadicalSubgroup_of_not_dvd_card hp hpG) := by
  refine Quotient.inductionOn q ?_
  intro Q
  have hQ : Q.1 = (⊥ : Subgroup G) :=
    (isRadicalSubgroup_iff_eq_bot_of_not_dvd_card hp hpG Q.1).mp Q.2
  have hSubtype : Q =
      (⟨⊥, bot_isRadicalSubgroup_of_not_dvd_card hp hpG⟩ :
        RadicalSubgroup (p := p) (G := G)) := by
    apply Subtype.ext
    exact hQ
  exact congrArg
    (fun R : RadicalSubgroup (p := p) (G := G) ↦
      (Quotient.mk'' R : RadicalConjugacyClass (p := p) (G := G)))
    hSubtype

/-! ## Literal singleton representatives -/

/-- The raw weight `(1, chi)` constructed from the kernel-proved trivial
radical and a supplied defect-zero local ordinary character. -/
def outsideOrderRawWeight {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (notDvdCard : ¬ ell ∣ Nat.card family.H)
    (chi : OrdinaryIrreducibleCharacter.Irr family.K
      (NormalizerQuotient (⊥ : Subgroup family.H)))
    (chiDefectZero : IsDefectZeroOrdinaryCharacter ell chi) :
    CharacterWeight ell family.K family.H where
  prime := family.ellPrime
  subgroup := ⊥
  radical := bot_isRadicalSubgroup_of_not_dvd_card
    family.ellPrime notDvdCard
  localCharacter := chi
  defectZero := chiDefectZero

/-- Restrict the constructed trivial-radical weight to a selected literal
block once the exact local block-induction equality has been supplied. -/
def outsideOrderWeight {ell : ℕ}
    (family : Definition35Family.{u} ell) (block : family.Block)
    (notDvdCard : ¬ ell ∣ Nat.card family.H)
    (chi : OrdinaryIrreducibleCharacter.Irr family.K
      (NormalizerQuotient (⊥ : Subgroup family.H)))
    (chiDefectZero : IsDefectZeroOrdinaryCharacter ell chi)
    (chiBlock : family.blockSource.operations.rawWeightBlock
      (outsideOrderRawWeight family notDvdCard chi chiDefectZero) = block) :
    Definition35Weight (family.problem block) := by
  refine ⟨Quotient.mk'' (Quotient.mk''
    (outsideOrderRawWeight family notDvdCard chi chiDefectZero)), ?_⟩
  exact chiBlock

/-- Transport one simple-module class in the selected block to the literal
function-valued Brauer-character fibre. -/
def outsideOrderBrauer {ell : ℕ}
    (family : Definition35Family.{u} ell) (block : family.Block)
    (X : SimpleModuleClass family.k[family.H])
    (hX : simpleModuleClassBlock family.blocks X = block) :
    Definition35Brauer (family.problem block) :=
  simpleModuleClassBlockEquivIBrBlock family.iota
    family.irreducibleBrauerInjective family.blocks block ⟨X, hX⟩

/-- The canonical representative of the unique simple-module class in an
outside-order block.  Its existence and uniqueness are kernel consequences
of Maschke semisimplicity and the supplied primitive block-idempotent
decomposition. -/
noncomputable def outsideOrderSimpleModuleClassBlock {ell : ℕ}
    (family : Definition35Family.{u} ell) (block : family.Block)
    (notDvdCard : ¬ ell ∣ Nat.card family.H) :
    SimpleModuleClassBlock family.blocks block := by
  let hss : IsSemisimpleRing family.k[family.H] :=
    monoidAlgebra_isSemisimpleRing_of_not_dvd_card notDvdCard
  let hUnique :=
    FDRepSimpleClassKZero.existsUnique_simpleModuleClassBlock_of_isSemisimpleRing
      hss family.blocks block
  exact ⟨Classical.choose hUnique.exists,
    Classical.choose_spec hUnique.exists⟩

/-- The literal Brauer character obtained from the kernel-selected
simple-module class in an outside-order block. -/
def outsideOrderSelectedBrauer {ell : ℕ}
    (family : Definition35Family.{u} ell) (block : family.Block)
    (notDvdCard : ¬ ell ∣ Nat.card family.H) :
    Definition35Brauer (family.problem block) :=
  let X :=
    outsideOrderSimpleModuleClassBlock family block notDvdCard
  outsideOrderBrauer family block X.1 X.2

/-- The radical-class projection of every weight in the selected Definition
3.5 fibre is the literal class of the trivial subgroup. -/
theorem definition35Weight_radicalClass_eq_trivial_of_not_dvd_card
    {ell : ℕ} (family : Definition35Family.{u} ell)
    (notDvdCard : ¬ ell ∣ Nat.card family.H)
    (block : family.Block) (w : Definition35Weight (family.problem block)) :
    CharacterWeight.radicalClass w.1 =
      RadicalConjugacyClass.trivialClass
        (bot_isRadicalSubgroup_of_not_dvd_card
          family.ellPrime notDvdCard) :=
  radicalConjugacyClass_eq_trivialClass_of_not_dvd_card
    family.ellPrime notDvdCard _

/-! ## The narrow representation theoretic source -/

/-- The exact facts still unavailable for one outside-order block.

The local-character fields state the corresponding fact on the literal raw
set of weights and the exact local block-induction operation.  The final
field is one value of the fixed FLZ semantic relation, not an arbitrary
relation or an iBAW conclusion. -/
structure OutsideOrderSource {ell : ℕ}
    (family : Definition35Family.{u} ell) (block : family.Block)
    (automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block))
    (source : FLZSourceSemantics (family.problem block) automorphisms) where
  notDvdCard : ¬ ell ∣ Nat.card family.H
  localCharacter : OrdinaryIrreducibleCharacter.Irr family.K
    (NormalizerQuotient (⊥ : Subgroup family.H))
  localCharacter_defectZero :
    IsDefectZeroOrdinaryCharacter ell localCharacter
  localCharacter_block : family.blockSource.operations.rawWeightBlock
    (outsideOrderRawWeight family notDvdCard localCharacter
      localCharacter_defectZero) = block
  localCharacter_unique : ∀ (W : CharacterWeight ell family.K family.H),
    family.blockSource.operations.rawWeightBlock W = block →
      ∀ hQ : W.subgroup = (⊥ : Subgroup family.H),
        CharacterWeight.castLocalCharacter hQ W.localCharacter =
          localCharacter
  blockIsomorphism :
    source.definition35BlockIsomorphic
      (outsideOrderSelectedBrauer family block notDvdCard)
      (outsideOrderWeight family block notDvdCard localCharacter
        localCharacter_defectZero localCharacter_block)

namespace OutsideOrderSource

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable {block : family.Block}
variable {automorphisms : Definition35AutomorphismStabilizerAdapter
  (family.problem block)}
variable {source : FLZSourceSemantics (family.problem block) automorphisms}
variable (S : OutsideOrderSource family block automorphisms source)

/-- The selected literal Brauer character, constructed from the
kernel-derived simple-module class by the existing block-fibre equivalence. -/
def brauer : Definition35Brauer (family.problem block) :=
  outsideOrderSelectedBrauer family block S.notDvdCard

/-- The selected literal weight, constructed at the kernel-proved trivial
radical. -/
def weight : Definition35Weight (family.problem block) :=
  outsideOrderWeight family block S.notDvdCard S.localCharacter
    S.localCharacter_defectZero S.localCharacter_block

include S in
/-- The outside-order source proves Maschke semisimplicity rather than
requiring it as another representation theoretic field. -/
theorem semisimpleGroupAlgebra : IsSemisimpleRing family.k[family.H] :=
  monoidAlgebra_isSemisimpleRing_of_not_dvd_card S.notDvdCard

/-- Primitive-block uniqueness makes the literal Brauer block fibre a
singleton through `simpleModuleClassBlockEquivIBrBlock`. -/
theorem brauer_unique (psi : Definition35Brauer (family.problem block)) :
    psi = S.brauer := by
  let e := simpleModuleClassBlockEquivIBrBlock family.iota
    family.irreducibleBrauerInjective family.blocks block
  let X₀ :=
    outsideOrderSimpleModuleClassBlock family block S.notDvdCard
  have hUnique :=
    FDRepSimpleClassKZero.existsUnique_simpleModuleClassBlock_of_isSemisimpleRing
      S.semisimpleGroupAlgebra family.blocks block
  have hpreimage : e.symm psi = X₀ := by
    apply Subtype.ext
    exact hUnique.unique (e.symm psi).2 X₀.2
  have hbrauer : e X₀ = S.brauer := rfl
  exact (e.apply_symm_apply psi).symm |>.trans <|
    (congrArg e hpreimage).trans hbrauer

/-- The kernel radical collapse and sourced local-character uniqueness make
the literal weight block fibre a singleton. -/
theorem weight_unique (w : Definition35Weight (family.problem block)) :
    w = S.weight := by
  let W := selectedCharacterWeight family.blockSource block w
  have hQ : W.subgroup = (⊥ : Subgroup family.H) :=
    characterWeight_subgroup_eq_bot_of_not_dvd_card family.ellPrime
      S.notDvdCard W
  have hWBlock : family.blockSource.operations.rawWeightBlock W = block :=
    selectedCharacterWeight_block family.blockSource block w
  have hIso : CharacterWeight.Isomorphic W
      (outsideOrderRawWeight family S.notDvdCard S.localCharacter
        S.localCharacter_defectZero) :=
    ⟨hQ, S.localCharacter_unique W hWBlock hQ⟩
  have hconjugacyClass :
      (Quotient.mk'' (Quotient.mk'' W) :
        CharacterWeight.ConjugacyClass
          (p := ell) (K := family.K) (G := family.H)) =
      (Quotient.mk'' (Quotient.mk''
        (outsideOrderRawWeight family S.notDvdCard S.localCharacter
          S.localCharacter_defectZero)) :
        CharacterWeight.ConjugacyClass
          (p := ell) (K := family.K) (G := family.H)) :=
    congrArg
      (fun x : CharacterWeight.IsoClass
          (p := ell) (K := family.K) (G := family.H) ↦
        (Quotient.mk'' x : CharacterWeight.ConjugacyClass
          (p := ell) (K := family.K) (G := family.H)))
      (Quotient.sound hIso)
  apply Subtype.ext
  exact (selectedCharacterWeight_spec family.blockSource block w).symm |>.trans <|
    hconjugacyClass.trans (by rfl)

/-- The canonical equivalence between the two kernel-proved singleton
fibres. -/
def omega : Definition35Brauer (family.problem block) ≃
    Definition35Weight (family.problem block) where
  toFun := fun _ ↦ S.weight
  invFun := fun _ ↦ S.brauer
  left_inv := fun psi ↦ (S.brauer_unique psi).symm
  right_inv := fun w ↦ (S.weight_unique w).symm

@[simp]
theorem omega_apply (psi : Definition35Brauer (family.problem block)) :
    S.omega psi = S.weight :=
  rfl

/-- Equivariance is forced by singletonness of the target fibre; it is not
an external source field. -/
theorem omega_equivariant :
    Definition35Equivariant (family.problem block) S.omega := by
  letI : MulAction (family.problem block).Gamma
      (Definition35Brauer (family.problem block)) :=
    definition35BrauerAction (family.problem block)
  letI : MulAction (family.problem block).Gamma
      (Definition35Weight (family.problem block)) :=
    definition35WeightAction (family.problem block)
  intro a psi
  calc
    S.omega (a • psi) = S.weight := S.omega_apply (a • psi)
    _ = a • S.omega psi := (S.weight_unique (a • S.omega psi)).symm

/-- One sourced relation at the selected pair extends to every Brauer
character because the two fibres are singletons. -/
theorem blockIsomorphism_all
    (psi : Definition35Brauer (family.problem block)) :
    source.definition35BlockIsomorphic psi (S.omega psi) := by
  rw [S.brauer_unique psi, S.omega_apply]
  exact S.blockIsomorphism

/-- Kernel construction of the fixed Definition 3.5 carrier from the narrow
outside-order source. -/
def toDefinition35IBAWBijection : Definition35IBAWBijection
    (family.problem block) automorphisms source where
  omega := S.omega
  equivariant := S.omega_equivariant
  blockIsomorphism := S.blockIsomorphism_all

include S in
/-- Nonempty form used by the Proposition 3.9 strict-block router. -/
theorem hasDefinition35IBAWBijection : Nonempty (Definition35IBAWBijection
    (family.problem block) automorphisms source) :=
  ⟨S.toDefinition35IBAWBijection⟩

end OutsideOrderSource

end ModularRep.PaperProofs.EvenFieldProposition39OutsideOrder


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
