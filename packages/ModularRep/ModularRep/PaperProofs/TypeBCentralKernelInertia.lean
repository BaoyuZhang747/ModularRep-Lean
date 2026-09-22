import ModularRep.PaperProofs.TypeBCentralKernelCarriers
import ModularRep.PaperProofs.TypeBCentralKernelWeightTransport
import ModularRep.PaperProofs.TypeBCentralKernelBlockSource
import ModularRep.PaperProofs.CyclicOuterLemma37Concrete

/-!
# Actual character and raw-weight inertias for central-kernel transport

All stabilizers are comaps of the canonical opposite-automorphism action.
The original action is literal conjugation on G normal in A, and the
quotient action is the already constructed conjugation action of A/P on G/P.

An injective equivariant map from ONE supported Brauer fibre to weight
classes supplies the elementary joins U <= T and T = G U for a chosen raw
representative. It is not required to be a bijection on all Brauer characters
or on all weights. The representative adjustment, normalizer intersection,
and quotient stabilizer comparisons are deductions, not source fields.

This file does not identify the raw ordinary-weight stabilizer with the
stabilizer of an inflated local Brauer reduction. That separate join must
retain the same ordinary character, defect-zero reduction and root lift.
-/

noncomputable section
set_option autoImplicit false

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBCentralKernelInertia

open ModularRep
open CyclicOuterLemma37Concrete
open TypeBCentralKernelCarriers TypeBCentralKernelBlockSource

universe u

variable {p : ℕ} {k K A H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Group H] [Finite H]

def isoOf (W : CharacterWeight p K H) :
    CharacterWeight.IsoClass (p := p) (K := K) (G := H) := Quotient.mk'' W

def classOf (W : CharacterWeight p K H) :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H) :=
  Quotient.mk'' (isoOf W)

abbrev BrauerFibre (iota : PrimeRegularRootEmbedding p k K H)
    (b : LiteralPrimitiveBlock k H) :=
  {theta : IBr iota // Supported iota b theta}

def brauerStabilizer (action : A →* MulAut H)
    (iota : PrimeRegularRootEmbedding p k K H) (theta : IBr iota) : Subgroup A :=
  (MulAction.stabilizer (MulAut H)ᵐᵒᵖ theta).comap (inverseOpHom action)

def rawStabilizer (action : A →* MulAut H) (W : CharacterWeight p K H) : Subgroup A :=
  (MulAction.stabilizer (MulAut H)ᵐᵒᵖ (isoOf W)).comap (inverseOpHom action)

@[simp] theorem mem_brauerStabilizer (action : A →* MulAut H)
    (iota : PrimeRegularRootEmbedding p k K H) (theta : IBr iota) (a : A) :
    a ∈ brauerStabilizer action iota theta ↔
      IrreducibleBrauerCharacter.twist iota theta (action a⁻¹) = theta := Iff.rfl

@[simp] theorem mem_rawStabilizer (action : A →* MulAut H)
    (W : CharacterWeight p K H) (a : A) :
    a ∈ rawStabilizer action W ↔ W.rightTwist (action a⁻¹) = W := by
  change (Quotient.mk'' (W.rightTwist (action a⁻¹)) :
    CharacterWeight.IsoClass (p := p) (K := K) (G := H)) = Quotient.mk'' W ↔ _
  constructor
  · intro h
    exact CharacterWeight.eq_of_isomorphic (Quotient.exact h)
  · intro h
    rw [h]

theorem classOf_action (action : A →* MulAut H) (a : A)
    (W : CharacterWeight p K H) :
    (Quotient.mk'' (inverseOpHom action a • isoOf W) :
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H)) =
        inverseOpHom action a • classOf W := rfl

section Original

variable [Finite A] (G : Subgroup A) [G.Normal]

abbrev conjugationOp : A →* (MulAut G)ᵐᵒᵖ := inverseOpHom (originalAction G)

abbrev T (iota : PrimeRegularRootEmbedding p k K G) (theta : IBr iota) : Subgroup A :=
  brauerStabilizer (originalAction G) iota theta

abbrev U (W : CharacterWeight p K G) : Subgroup A := rawStabilizer (originalAction G) W

theorem conjugation_inner (g : G) : originalAction G (g : A) = MulAut.conj g := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

theorem iso_action_inner (g : G)
    (w : CharacterWeight.IsoClass (p := p) (K := K) (G := G)) :
    conjugationOp G (g : A) • w = g • w := by
  change CharacterWeight.rightTwistIsoClass (originalAction G (g : A)⁻¹) w =
    CharacterWeight.rightTwistIsoClass (MulAut.conj g⁻¹) w
  rw [← Subgroup.coe_inv, conjugation_inner]

theorem G_le_T (iota : PrimeRegularRootEmbedding p k K G) (theta : IBr iota) :
    G ≤ T G iota theta := by
  intro a ha
  rw [mem_brauerStabilizer]
  let g : G := ⟨a, ha⟩
  have heq : originalAction G a⁻¹ = MulAut.conj g⁻¹ := conjugation_inner G g⁻¹
  rw [heq]
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  exact PrimeRegularClassFunction.twist_conj theta.val g⁻¹

/-- Raw inertia inside the base is exactly the normalizer of its radical.
The local-character invariance is checked inner conjugacy, not a source. -/
theorem U_comap_base (W : CharacterWeight p K G) :
    (U G W).comap G.subtype = Subgroup.normalizer (W.subgroup : Set G) := by
  ext g
  have hi : conjugationOp G (g : A) • isoOf W = g • isoOf W :=
    iso_action_inner G g (isoOf W)
  change (conjugationOp G (g : A) • isoOf W = isoOf W) ↔ _
  rw [hi]
  constructor
  · intro h
    have hraw : W.rightTwist (MulAut.conj g⁻¹) = W :=
      CharacterWeight.eq_of_isomorphic (Quotient.exact h)
    have hs : W.subgroup.comap (MulAut.conj g⁻¹).toMonoidHom = W.subgroup :=
      congrArg CharacterWeight.subgroup hraw
    have hconj : (MulAut.conj g).symm = MulAut.conj g⁻¹ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_equiv_eq_comap_symm, hconj]
    exact hs
  · intro h
    exact normalizer_fixes_rawWeight canonicalRawNormalizerQuotientInput
      g (isoOf W) h

theorem base_inf_U (W : CharacterWeight p K G) :
    G ⊓ U G W = (Subgroup.normalizer (W.subgroup : Set G)).map G.subtype := by
  ext a
  constructor
  · rintro ⟨haG, haU⟩
    refine ⟨⟨a, haG⟩, ?_, rfl⟩
    rw [← U_comap_base G W]
    exact haU
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g.property, ?_⟩
    change g ∈ (U G W).comap G.subtype
    rw [U_comap_base]
    exact hg

variable (iota : PrimeRegularRootEmbedding p k K G) (b : LiteralPrimitiveBlock k G)

variable (stable : ∀ (a : A) (theta : BrauerFibre iota b),
  Supported iota b (conjugationOp G a • theta.val))

def fibreAction (a : A) (theta : BrauerFibre iota b) : BrauerFibre iota b :=
  ⟨conjugationOp G a • theta.val, stable a theta⟩

variable (omega : BrauerFibre iota b →
  CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G))
variable (injective : Function.Injective omega)
variable (equivariant : ∀ (a : A) (theta : BrauerFibre iota b),
  omega (fibreAction G iota b stable a theta) = conjugationOp G a • omega theta)
variable (theta : BrauerFibre iota b) (W : CharacterWeight p K G)
variable (representative : omega theta = classOf W)

include injective equivariant representative in
theorem U_le_T : U G W ≤ T G iota theta.val := by
  intro a ha
  have hw : conjugationOp G a • isoOf W = isoOf W := ha
  have hc : conjugationOp G a • classOf W = classOf W :=
    congrArg (fun w : CharacterWeight.IsoClass (p := p) (K := K) (G := G) =>
      (Quotient.mk'' w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G))) hw
  have htheta : fibreAction G iota b stable a theta = theta := by
    apply injective
    rw [equivariant, representative, hc]
  exact congrArg Subtype.val htheta

include equivariant representative in
theorem class_fixed_of_mem_T {a : A} (ha : a ∈ T G iota theta.val) :
    conjugationOp G a • classOf W = classOf W := by
  have ht : fibreAction G iota b stable a theta = theta := Subtype.ext ha
  rw [← representative, ← equivariant, ht]

include equivariant representative in
/-- The adjustment is an actual element of G taking one raw representative
to the other; its residual ambient element lies in the actual raw inertia. -/
theorem representative_adjustment {a : A} (ha : a ∈ T G iota theta.val) :
    ∃ g : G, (g : A)⁻¹ * a ∈ U G W := by
  have hc := class_fixed_of_mem_T G iota b stable omega equivariant theta W representative ha
  have hiso :
      (Quotient.mk'' (conjugationOp G a • isoOf W) :
        CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) =
      Quotient.mk'' (isoOf W) := hc
  obtain ⟨g, hg⟩ := Quotient.exact hiso
  change g • isoOf W = conjugationOp G a • isoOf W at hg
  refine ⟨g, ?_⟩
  change conjugationOp G ((g : A)⁻¹ * a) • isoOf W = isoOf W
  rw [map_mul, mul_smul, ← hg, ← iso_action_inner G g]
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

include injective equivariant representative in
theorem T_eq_base_mul_U :
    (T G iota theta.val : Set A) = (G : Set A) * (U G W : Set A) := by
  ext a
  constructor
  · intro ha
    obtain ⟨g, hg⟩ := representative_adjustment
      G iota b stable omega equivariant theta W representative ha
    exact ⟨g.val, g.property, g.val⁻¹ * a, hg, by simp⟩
  · rintro ⟨g, hg, u, hu, rfl⟩
    exact (T G iota theta.val).mul_mem (G_le_T G iota theta.val hg)
      (U_le_T G iota b stable omega injective equivariant theta W representative hu)

end Original

section Quotient

variable [Finite A] (G P : Subgroup A) [G.Normal] [P.Normal]
variable (hP : IsPGroup p (kernelInG G P))
variable (iotaDown : PrimeRegularRootEmbedding p k K (QuotientG G P))
variable (kernel : TypeBCentralKernelBrauerInflation.Navarro232Principle p k)
variable (regular : TypeBCentralKernelBrauerInflation.PrimeRegularQuotientLiftPrinciple.{u} p)

/-- The character inertia is the full preimage of the actual quotient
character inertia under A -> A/P. -/
theorem brauerStabilizer_quotient (phi : IBr iotaDown) :
    T G (TypeBCentralKernelBrauerInflation.upRoot (kernelInG G P) hP iotaDown)
        (TypeBCentralKernelBrauerInflation.brauerEquiv
          (kernelInG G P) hP iotaDown kernel regular phi) =
      (brauerStabilizer (quotientAction G P) iotaDown phi).comap (qA P) := by
  ext a
  simp only [mem_brauerStabilizer, Subgroup.mem_comap]
  have natural := TypeBCentralKernelBrauerInflation.brauerEquiv_twist
    (kernelInG G P) hP iotaDown kernel regular
    (originalAction G a⁻¹) (quotientAction G P (qA P a)⁻¹)
    (fun g => by
      change qG G P (originalAction G a⁻¹ g) =
        quotientAction G P ((qA P a)⁻¹) (qG G P g)
      rw [← map_inv]
      exact (quotientAction_mk G P a⁻¹ g).symm) phi
  constructor
  · intro h
    apply (TypeBCentralKernelBrauerInflation.brauerEquiv
      (kernelInG G P) hP iotaDown kernel regular).injective
    exact natural.trans h
  · intro h
    rw [← natural, h]

include hP in
theorem quotientKernelIsPGroup : IsPGroup p (qG G P).ker := by
  rw [qG_ker]
  exact hP

include hP in
/-- The same equality holds for the raw ordinary-character weight inertia;
this uses the proved raw transport, not a source-supplied class matching. -/
theorem rawStabilizer_quotient (W : CharacterWeight p K G) :
    U G W =
      (rawStabilizer (quotientAction G P)
        (TypeBCentralKernelWeightTransport.descend (qG G P) (qG_surjective G P)
          (quotientKernelIsPGroup G P hP) W)).comap (qA P) := by
  ext a
  simp only [mem_rawStabilizer, Subgroup.mem_comap]
  have natural := TypeBCentralKernelWeightTransport.descend_rightTwist
    (qG G P) (qG_surjective G P) (quotientKernelIsPGroup G P hP)
    (originalAction G a⁻¹) (quotientAction G P (qA P a)⁻¹)
    (fun g => by simpa only [map_inv] using (quotientAction_mk G P a⁻¹ g).symm) W
  constructor
  · intro h
    rw [← natural, h]
  · intro h
    apply TypeBCentralKernelWeightTransport.descend_injective
      (qG G P) (qG_surjective G P) (quotientKernelIsPGroup G P hP)
    exact natural.trans h

end Quotient

end ModularRep.PaperProofs.TypeBCentralKernelInertia


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
