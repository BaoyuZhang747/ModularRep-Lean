import ModularRep.PaperProofs.TypeCConformalActionAdapter
import ModularRep.WeightCharacterBridge
import ModularRep.KZeroLinearCharacterTensor

/-!
# Tensor and field actions on the actual set of weights defined by characters

This file constructs the action used on weights in manuscript Proposition
3.14.  A tensor character is first restricted to each local normaliser and
then descended to the normaliser quotient.  Tensoring the local defect-zero
ordinary character with that quotient character preserves the radical
subgroup and defect.  The construction descends through weight isomorphism
and ambient conjugacy.

The chosen ordinary lift of a modular quotient character must be trivial on
every radical subgroup.  This exact lift property is kept in
`RadicalKernelLiftInput`; no weight correspondence, block assignment, or
inductive condition is included in that input.  Lean proves the tensor group
law, the right automorphism law, their semidirect compatibility, and the
orientation of the resulting action.
-/

noncomputable section

open CategoryTheory

namespace ModularRep.PaperProofs.TypeCWeightTensorFieldAction

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.TypeCConformalActionAdapter

universe u

variable {p : Nat}
variable {K k G E : Type u}
variable [Field K] [CharZero K] [Field k] [CharP k p] [IsAlgClosed k]
variable [Group G] [Finite G] [Group E]

/-- Ordinary linear characters which are trivial on every `p`-radical
subgroup.  This is the precise domain on which tensoring a character weight
can be defined by descent to every local normaliser quotient. -/
def radicalTrivialLinearCharacters : Subgroup (G →* Kˣ) where
  carrier lambda := ∀ (Q : Subgroup G), IsRadicalSubgroup p Q → Q ≤ lambda.ker
  one_mem' := by
    intro Q hQ q hq
    simp
  mul_mem' := by
    intro lambda mu hlambda hmu Q hQ q hq
    change lambda q * mu q = 1
    rw [hlambda Q hQ hq, hmu Q hQ hq, one_mul]
  inv_mem' := by
    intro lambda hlambda Q hQ q hq
    change (lambda q)⁻¹ = 1
    rw [hlambda Q hQ hq, inv_one]

abbrev RadicalTensorCharacter :=
  radicalTrivialLinearCharacters (p := p) (K := K) (G := G)

/-- Restriction of a radical-trivial linear character to a normaliser,
descended to the local quotient. -/
def localQuotientCharacter
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (Q : Subgroup G) (hQ : IsRadicalSubgroup p Q) :
    NormalizerQuotient Q →* Kˣ :=
  QuotientGroup.lift
    (Q.subgroupOf (Subgroup.normalizer (Q : Set G)))
    (lambda.1.comp (Subgroup.normalizer (Q : Set G)).subtype)
    (by
      intro x hx
      exact lambda.2 Q hQ hx)

@[simp]
theorem localQuotientCharacter_mk
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (Q : Subgroup G) (hQ : IsRadicalSubgroup p Q)
    (x : Subgroup.normalizer (Q : Set G)) :
    localQuotientCharacter lambda Q hQ (QuotientGroup.mk x) = lambda.1 x :=
  rfl

theorem localQuotientCharacter_one
    (Q : Subgroup G) (hQ : IsRadicalSubgroup p Q) :
    localQuotientCharacter
      (1 : RadicalTensorCharacter (p := p) (K := K) (G := G)) Q hQ = 1 := by
  ext x
  rfl

theorem localQuotientCharacter_mul
    (lambda mu : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (Q : Subgroup G) (hQ : IsRadicalSubgroup p Q) :
    localQuotientCharacter (lambda * mu) Q hQ =
      localQuotientCharacter lambda Q hQ *
        localQuotientCharacter mu Q hQ := by
  ext x
  rfl

/-- Pullback of a radical-trivial linear character by an automorphism. -/
def precomp
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (alpha : MulAut G) :
    RadicalTensorCharacter (p := p) (K := K) (G := G) :=
  ⟨lambda.1.comp alpha.toMonoidHom, by
    intro Q hQ q hq
    apply lambda.2 (Q.map alpha.toMonoidHom) (hQ.map_equiv alpha)
    exact ⟨q, hq, rfl⟩⟩

@[simp]
theorem precomp_apply
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (alpha : MulAut G) (g : G) :
    (precomp lambda alpha).1 g = lambda.1 (alpha g) :=
  rfl

theorem precomp_one
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G)) :
    precomp lambda (1 : MulAut G) = lambda := by
  apply Subtype.ext
  ext g
  simp [precomp]

theorem precomp_mul
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (alpha beta : MulAut G) :
    precomp (precomp lambda alpha) beta = precomp lambda (alpha * beta) := by
  apply Subtype.ext
  ext g
  rfl

theorem precomp_mul_character
    (lambda mu : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (alpha : MulAut G) :
    precomp (lambda * mu) alpha = precomp lambda alpha * precomp mu alpha := by
  apply Subtype.ext
  ext g
  rfl

theorem precomp_inv
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (alpha : MulAut G) :
    precomp lambda⁻¹ alpha = (precomp lambda alpha)⁻¹ := by
  apply Subtype.ext
  ext g
  rfl

theorem precomp_conj
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (g : G) :
    precomp lambda (MulAut.conj g) = lambda := by
  apply Subtype.ext
  ext x
  simp [precomp]

/-- Tensoring a defect-zero ordinary character with a linear character does
not change its degree and therefore preserves defect zero. -/
theorem defectZero_linearTwist
    {H : Type u} [Group H] [Finite H]
    {chi : Irr K H} (hchi : IsDefectZeroOrdinaryCharacter p chi)
    (lambda : H →* Kˣ) :
    IsDefectZeroOrdinaryCharacter p (linearTwist chi lambda) := by
  rcases hchi with ⟨V, hV, hcharacter, hdefect⟩
  let V' : FDRep K H :=
    FDRep.of (Representation.linearCharacterTwist V.ρ lambda)
  have hV' : Simple V' := by
    let _ : Simple V := hV
    change Simple ((FDRep.linearCharacterTwistEquivalence lambda).functor.obj V)
    exact CategoryTheory.simple_obj
      (FDRep.linearCharacterTwistEquivalence lambda).functor V
  refine ⟨V', hV', ?_, ?_⟩
  · funext h
    change (Representation.linearCharacterTwist V.ρ lambda).character h =
      (lambda h : K) * chi h
    rw [Representation.character_linearCharacterTwist,
      show Representation.character V.ρ h = chi.1 h from
        congrFun hcharacter h]
  · simpa [V', IsDefectZeroRepresentation] using hdefect

namespace CharacterWeight

theorem castLocalCharacter_linearTwist
    {Q R : Subgroup G} (hQ : Q = R)
    (hQrad : IsRadicalSubgroup p Q) (hRrad : IsRadicalSubgroup p R)
    {chi : Irr K (NormalizerQuotient Q)}
    {psi : Irr K (NormalizerQuotient R)}
    (hchi : ModularRep.CharacterWeight.castLocalCharacter hQ chi = psi)
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G)) :
    ModularRep.CharacterWeight.castLocalCharacter hQ
        (OrdinaryIrreducibleCharacter.linearTwist chi
          (localQuotientCharacter lambda Q hQrad)) =
      OrdinaryIrreducibleCharacter.linearTwist psi
        (localQuotientCharacter lambda R hRrad) := by
  subst R
  change OrdinaryIrreducibleCharacter.linearTwist chi _ =
    OrdinaryIrreducibleCharacter.linearTwist psi _
  change chi = psi at hchi
  subst psi
  rfl

/-- Tensor a character weight by a radical-trivial ordinary linear
character.  The radical subgroup is unchanged and the local character is
twisted by the descended quotient character. -/
def linearTwist
    (W : ModularRep.CharacterWeight p K G)
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G)) :
    ModularRep.CharacterWeight p K G where
  prime := W.prime
  subgroup := W.subgroup
  radical := W.radical
  localCharacter := OrdinaryIrreducibleCharacter.linearTwist W.localCharacter
    (localQuotientCharacter lambda W.subgroup W.radical)
  defectZero := defectZero_linearTwist W.defectZero
    (localQuotientCharacter lambda W.subgroup W.radical)

@[simp]
theorem linearTwist_subgroup
    (W : ModularRep.CharacterWeight p K G)
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G)) :
    (linearTwist W lambda).subgroup = W.subgroup :=
  rfl

theorem linearTwist_isomorphic
    {W W' : ModularRep.CharacterWeight p K G}
    (h : ModularRep.CharacterWeight.Isomorphic W W')
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G)) :
    ModularRep.CharacterWeight.Isomorphic
      (linearTwist W lambda) (linearTwist W' lambda) := by
  rcases h with ⟨hQ, hchi⟩
  refine ⟨hQ, ?_⟩
  exact castLocalCharacter_linearTwist hQ W.radical W'.radical hchi lambda

/-- Tensoring descends to character-weight isomorphism classes. -/
def linearTwistIsoClass
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G)) :
    ModularRep.CharacterWeight.IsoClass (p := p) (K := K) (G := G) →
      ModularRep.CharacterWeight.IsoClass (p := p) (K := K) (G := G) :=
  Quotient.map (fun W ↦ linearTwist W lambda)
    (fun _ _ h ↦ linearTwist_isomorphic h lambda)

theorem linearTwist_one_isomorphic
    (W : ModularRep.CharacterWeight p K G) :
    ModularRep.CharacterWeight.Isomorphic
      (linearTwist W
        (1 : RadicalTensorCharacter (p := p) (K := K) (G := G))) W := by
  refine ⟨rfl, ?_⟩
  change OrdinaryIrreducibleCharacter.linearTwist W.localCharacter _ =
    W.localCharacter
  rw [localQuotientCharacter_one,
    OrdinaryIrreducibleCharacter.linearTwist_one]

@[simp]
theorem linearTwistIsoClass_one
    (x : ModularRep.CharacterWeight.IsoClass
      (p := p) (K := K) (G := G)) :
    linearTwistIsoClass
        (1 : RadicalTensorCharacter (p := p) (K := K) (G := G)) x = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound (linearTwist_one_isomorphic W)

theorem linearTwist_mul_isomorphic
    (W : ModularRep.CharacterWeight p K G)
    (lambda mu : RadicalTensorCharacter (p := p) (K := K) (G := G)) :
    ModularRep.CharacterWeight.Isomorphic
      (linearTwist (linearTwist W lambda) mu)
      (linearTwist W (lambda * mu)) := by
  refine ⟨rfl, ?_⟩
  dsimp only [linearTwist]
  change OrdinaryIrreducibleCharacter.linearTwist
      (OrdinaryIrreducibleCharacter.linearTwist W.localCharacter _) _ =
    OrdinaryIrreducibleCharacter.linearTwist W.localCharacter _
  rw [OrdinaryIrreducibleCharacter.linearTwist_mul,
    localQuotientCharacter_mul]

theorem linearTwistIsoClass_mul
    (x : ModularRep.CharacterWeight.IsoClass
      (p := p) (K := K) (G := G))
    (lambda mu : RadicalTensorCharacter (p := p) (K := K) (G := G)) :
    linearTwistIsoClass mu (linearTwistIsoClass lambda x) =
      linearTwistIsoClass (lambda * mu) x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound (linearTwist_mul_isomorphic W lambda mu)

/-- Automorphism transport commutes with local tensoring after the linear
character is pulled back by the same automorphism.  This theorem fixes the
right-action orientation used in the semidirect product below. -/
theorem rightTwist_linearTwist_isomorphic
    (W : ModularRep.CharacterWeight p K G)
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (alpha : MulAut G) :
    ModularRep.CharacterWeight.Isomorphic
      ((linearTwist W lambda).rightTwist alpha)
      (linearTwist (W.rightTwist alpha) (precomp lambda alpha)) := by
  refine ⟨rfl, ?_⟩
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  rfl

theorem rightTwistIsoClass_linearTwistIsoClass
    (x : ModularRep.CharacterWeight.IsoClass
      (p := p) (K := K) (G := G))
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (alpha : MulAut G) :
    ModularRep.CharacterWeight.rightTwistIsoClass alpha
        (linearTwistIsoClass lambda x) =
      linearTwistIsoClass (precomp lambda alpha)
        (ModularRep.CharacterWeight.rightTwistIsoClass alpha x) := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound (rightTwist_linearTwist_isomorphic W lambda alpha)

theorem linearTwistIsoClass_conjugation
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (g : G)
    (x : ModularRep.CharacterWeight.IsoClass
      (p := p) (K := K) (G := G)) :
    linearTwistIsoClass lambda (g • x) =
      g • linearTwistIsoClass lambda x := by
  change linearTwistIsoClass lambda
      (ModularRep.CharacterWeight.rightTwistIsoClass
        (MulAut.conj g⁻¹) x) =
    ModularRep.CharacterWeight.rightTwistIsoClass
      (MulAut.conj g⁻¹) (linearTwistIsoClass lambda x)
  rw [rightTwistIsoClass_linearTwistIsoClass,
    precomp_conj]

/-- Tensoring descends through ambient conjugacy to the manuscript's actual
set of weights. -/
def linearTwistConjugacyClass
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G)) :
    ModularRep.CharacterWeight.ConjugacyClass
        (p := p) (K := K) (G := G) →
      ModularRep.CharacterWeight.ConjugacyClass
        (p := p) (K := K) (G := G) :=
  Quotient.map (linearTwistIsoClass lambda) (by
    intro x y hxy
    rcases hxy with ⟨g, rfl⟩
    exact ⟨g, (linearTwistIsoClass_conjugation lambda g y).symm⟩)

@[simp]
theorem linearTwistConjugacyClass_one
    (x : ModularRep.CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G)) :
    linearTwistConjugacyClass
        (1 : RadicalTensorCharacter (p := p) (K := K) (G := G)) x = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg Quotient.mk'' (linearTwistIsoClass_one W)

theorem linearTwistConjugacyClass_mul
    (x : ModularRep.CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G))
    (lambda mu : RadicalTensorCharacter (p := p) (K := K) (G := G)) :
    linearTwistConjugacyClass mu (linearTwistConjugacyClass lambda x) =
      linearTwistConjugacyClass (lambda * mu) x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg Quotient.mk'' (linearTwistIsoClass_mul W lambda mu)

theorem rightTwistConjugacyClass_linearTwistConjugacyClass
    (x : ModularRep.CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G))
    (lambda : RadicalTensorCharacter (p := p) (K := K) (G := G))
    (alpha : MulAut G) :
    ModularRep.CharacterWeight.rightTwistConjugacyClass alpha
        (linearTwistConjugacyClass lambda x) =
      linearTwistConjugacyClass (precomp lambda alpha)
        (ModularRep.CharacterWeight.rightTwistConjugacyClass alpha x) := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg Quotient.mk''
    (rightTwistIsoClass_linearTwistIsoClass W lambda alpha)

end CharacterWeight

section SourceLift

variable (G0 : Subgroup G) [G0.Normal]
variable (field : E →* MulAut G)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
variable (D : OrdinaryReductionEquiv (k := k) (K := K)
  G0 field hinvariant)

/-- Exact source input for the ordinary lift selected in Proposition 3.14:
each lifted quotient character is trivial on every radical subgroup.  This
contains no action, weight correspondence, block map, or equivariance
conclusion. -/
structure RadicalKernelLiftInput : Prop where
  lift_trivial : ∀
    (lambda : TensorCharacters (k := k) G0) (Q : Subgroup G),
    IsRadicalSubgroup p Q →
      Q ≤ (OrdinaryReductionEquiv.lift
        (G0 := G0) (field := field) (hinvariant := hinvariant) D lambda).ker

variable (kernelInput : RadicalKernelLiftInput
  (p := p) G0 field hinvariant D)

/-- The actual lifted tensor characters, now regarded as characters which
descend to every radical normaliser quotient. -/
def radicalLift :
    TensorCharacters (k := k) G0 →*
      RadicalTensorCharacter (p := p) (K := K) (G := G) where
  toFun lambda :=
    ⟨OrdinaryReductionEquiv.lift
      (G0 := G0) (field := field) (hinvariant := hinvariant) D lambda,
      kernelInput.lift_trivial lambda⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' lambda mu := by
    apply Subtype.ext
    exact map_mul _ lambda mu

@[simp]
theorem radicalLift_apply
    (lambda : TensorCharacters (k := k) G0) (g : G) :
    (radicalLift G0 field hinvariant D kernelInput lambda).1 g =
      OrdinaryReductionEquiv.lift
        (G0 := G0) (field := field) (hinvariant := hinvariant) D lambda g :=
  rfl

/-- The actual lift intertwines the modular field action with pullback of
the ordinary radical-trivial character. -/
theorem radicalLift_field
    (e : E) (lambda : TensorCharacters (k := k) G0) :
    radicalLift G0 field hinvariant D kernelInput
        (LinearCharactersTrivialOn.fieldAction (k := k)
          field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)
          e lambda) =
      precomp (radicalLift G0 field hinvariant D kernelInput lambda)
        (field e⁻¹) := by
  apply Subtype.ext
  exact OrdinaryReductionEquiv.lift_field_equivariant
    (G0 := G0) (field := field) (hinvariant := hinvariant) D e lambda

abbrev WeightClass :=
  ModularRep.CharacterWeight.ConjugacyClass
    (p := p) (K := K) (G := G)

/-- The opposite automorphism homomorphism which converts the manuscript's
right action into Lean's left-action interface. -/
def inverseOpHom (rho : E →* MulAut G) : E →* (MulAut G)ᵐᵒᵖ where
  toFun e := MulOpposite.op (rho e⁻¹)
  map_one' := by simp
  map_mul' e f := by simp

/-- Inverse tensoring is the left action encoding the manuscript's right
tensor convention. -/
@[instance_reducible]
def inverseTensorAction :
    MulAction (TensorCharacters (k := k) G0)
      (WeightClass (p := p) (K := K) (G := G)) where
  smul lambda W := CharacterWeight.linearTwistConjugacyClass
    (radicalLift G0 field hinvariant D kernelInput lambda)⁻¹ W
  one_smul W := by
    change CharacterWeight.linearTwistConjugacyClass
      (radicalLift G0 field hinvariant D kernelInput 1)⁻¹ W = W
    rw [map_one, inv_one,
      CharacterWeight.linearTwistConjugacyClass_one]
  mul_smul lambda mu W := by
    change CharacterWeight.linearTwistConjugacyClass
        (radicalLift G0 field hinvariant D kernelInput (lambda * mu))⁻¹ W =
      CharacterWeight.linearTwistConjugacyClass
        (radicalLift G0 field hinvariant D kernelInput lambda)⁻¹
        (CharacterWeight.linearTwistConjugacyClass
          (radicalLift G0 field hinvariant D kernelInput mu)⁻¹ W)
    rw [map_mul, mul_inv_rev,
      CharacterWeight.linearTwistConjugacyClass_mul]

/-- Field automorphisms act through the actual right automorphism transport
on character-weight conjugacy classes. -/
@[instance_reducible]
def inverseFieldAction (field : E →* MulAut G) : MulAction E
    (WeightClass (p := p) (K := K) (G := G)) :=
  MulAction.compHom _
    (inverseOpHom field)

/-- The actual tensor and field actions on character weights satisfy the
semidirect compatibility identity with the same orientation as the ordinary
and Brauer character actions. -/
theorem tensorField_semidirectCompatible :
    @Formalisation.SemidirectActionCompatible
      (TensorCharacters (k := k) G0) E
      (WeightClass (p := p) (K := K) (G := G)) _ _
      (inverseTensorAction G0 field hinvariant D kernelInput)
      (inverseFieldAction (p := p) (K := K) field)
      (LinearCharactersTrivialOn.fieldAction (k := k)
        field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)) := by
  intro e lambda W
  change ModularRep.CharacterWeight.rightTwistConjugacyClass
      (field e⁻¹)
      (CharacterWeight.linearTwistConjugacyClass
        (radicalLift G0 field hinvariant D kernelInput lambda)⁻¹ W) =
    CharacterWeight.linearTwistConjugacyClass
      (radicalLift G0 field hinvariant D kernelInput
        (LinearCharactersTrivialOn.fieldAction (k := k)
          field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)
          e lambda))⁻¹
      (ModularRep.CharacterWeight.rightTwistConjugacyClass (field e⁻¹) W)
  rw [CharacterWeight.rightTwistConjugacyClass_linearTwistConjugacyClass,
    precomp_inv, radicalLift_field]

/-- The literal tensor-and-field semidirect action on conjugacy classes of
character weights. -/
@[instance_reducible]
def tensorFieldSemidirectAction :
    MulAction (ActingGroup (k := k) G0 field hinvariant)
      (WeightClass (p := p) (K := K) (G := G)) := by
  exact @Formalisation.semidirectMulAction
    (TensorCharacters (k := k) G0) E
    (WeightClass (p := p) (K := K) (G := G)) _ _
    (inverseTensorAction G0 field hinvariant D kernelInput)
    (inverseFieldAction (p := p) (K := K) field)
    (LinearCharactersTrivialOn.fieldAction (k := k)
      field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant))
    (tensorField_semidirectCompatible G0 field hinvariant D kernelInput)

/-- Elementwise formula for the actual combined weight action.  The field
transport by `e⁻¹` is performed first and the local character is then
tensored by the inverse lifted quotient character. -/
theorem tensorFieldSemidirectAction_apply
    (a : ActingGroup (k := k) G0 field hinvariant)
    (W : WeightClass (p := p) (K := K) (G := G)) :
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant)
        (WeightClass (p := p) (K := K) (G := G)) :=
      tensorFieldSemidirectAction G0 field hinvariant D kernelInput
    a • W = CharacterWeight.linearTwistConjugacyClass
      (radicalLift G0 field hinvariant D kernelInput a.left)⁻¹
      (ModularRep.CharacterWeight.rightTwistConjugacyClass
        (field a.right⁻¹) W) := by
  rfl

end SourceLift

end ModularRep.PaperProofs.TypeCWeightTensorFieldAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
