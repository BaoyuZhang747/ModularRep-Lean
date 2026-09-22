import ModularRep.BrauerCharacterHomPullback
import ModularRep.CyclicOuterBAW

/-!
# Brauer character extensions for cyclic outer actions

This module contains the character-theoretic core of the cyclic outer action
argument.  It constructs an extension of an invariant irreducible Brauer
character to its stabiliser from the cyclic quotient extension principle.
There are no weights, blocks, or inductive-condition conclusions here.
-/

noncomputable section

namespace ModularRep.PaperProofs.CyclicOuterLemma37Concrete

open Formalisation
open ModularRep.ManuscriptVerification.CyclicOuterBAW

universe u

section GenericRightAction

variable {H E X : Type u} [Group H] [Group E]
variable [MulAction (MulAut H)ᵐᵒᵖ X]

/-- Convert a homomorphism to automorphisms into the opposite-group
homomorphism encoding a right action. -/
def inverseOpHom (rho : E →* MulAut H) : E →* (MulAut H)ᵐᵒᵖ where
  toFun e := MulOpposite.op (rho e⁻¹)
  map_one' := by simp
  map_mul' e f := by simp

/-- The left action that encodes a right automorphism action. -/
@[instance_reducible] def rightAutomorphismAction
    (rho : E →* MulAut H) : MulAction E X :=
  MulAction.compHom X (inverseOpHom rho)

/-- Right automorphism actions satisfy the semidirect compatibility
identity. -/
theorem rightAutomorphismSemidirectCompatible
    (phi : E →* MulAut H) :
    let _ : MulAction H X :=
      rightAutomorphismAction (X := X) (MulAut.conj : H →* MulAut H)
    let _ : MulAction E X := rightAutomorphismAction (X := X) phi
    SemidirectActionCompatible (X := X) phi := by
  dsimp only
  intro e h x
  change MulOpposite.op (phi e⁻¹) •
      (MulOpposite.op (MulAut.conj h⁻¹) • x) =
    MulOpposite.op (MulAut.conj ((phi e) h)⁻¹) •
      (MulOpposite.op (phi e⁻¹) • x)
  rw [← mul_smul, ← mul_smul]
  congr 1
  apply MulOpposite.unop_injective
  ext y
  simp [mul_assoc]

end GenericRightAction

section ActualBrauerCarriers

variable {p : ℕ} {k K H E : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H] [Group E] [Finite E] [IsCyclic E]

/-- Inner automorphisms fix every function-valued irreducible Brauer
character. -/
theorem inner_fixes_ibr
    (iota : PrimeRegularRootEmbedding p k K H)
    (h : H) (psi : IBr iota) :
    let _ : MulAction H (IBr iota) :=
      rightAutomorphismAction (X := IBr iota)
        (MulAut.conj : H →* MulAut H)
    h • psi = psi := by
  dsimp only [rightAutomorphismAction, inverseOpHom]
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  exact PrimeRegularClassFunction.twist_conj psi.1 h⁻¹

/-- The full semidirect action on an irreducible Brauer character is
twisting by the inverse of the corresponding automorphism. -/
theorem semidirect_smul_ibr_eq_twist_inverse
    (iota : PrimeRegularRootEmbedding p k K H)
    (phi : E →* MulAut H) (g : H ⋊[phi] E) (psi : IBr iota) :
    let _ : MulAction H (IBr iota) :=
      rightAutomorphismAction (X := IBr iota)
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (IBr iota) :=
      rightAutomorphismAction (X := IBr iota) phi
    let hcompat := rightAutomorphismSemidirectCompatible
      (X := IBr iota) phi
    let _ : MulAction (H ⋊[phi] E) (IBr iota) :=
      semidirectMulAction phi hcompat
    g • psi = IrreducibleBrauerCharacter.twist iota psi
      (semidirectToMulAut phi g⁻¹) := by
  dsimp only
  letI : MulAction H (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (IBr iota) :=
    rightAutomorphismAction (X := IBr iota) phi
  let hcompat := rightAutomorphismSemidirectCompatible
    (X := IBr iota) phi
  letI : MulAction (H ⋊[phi] E) (IBr iota) :=
    semidirectMulAction phi hcompat
  change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi (phi g.right⁻¹))
        (MulAut.conj g.left⁻¹) = _
  rw [IrreducibleBrauerCharacter.twist_mul]
  congr 1
  have hg : semidirectToMulAut phi g =
      MulAut.conj g.left * phi g.right := by
    calc
      semidirectToMulAut phi g =
          semidirectToMulAut phi
            (SemidirectProduct.inl g.left *
              SemidirectProduct.inr g.right) :=
        congrArg (semidirectToMulAut phi)
          (SemidirectProduct.inl_left_mul_inr_right g).symm
      _ = MulAut.conj g.left * phi g.right := by
        rw [map_mul, semidirectToMulAut_inl, semidirectToMulAut_inr]
  calc
    phi g.right⁻¹ * MulAut.conj g.left⁻¹ =
        (phi g.right)⁻¹ * (MulAut.conj g.left)⁻¹ := by
      congr 1
      · rw [map_inv]
      · change innerAutomorphismHom g.left⁻¹ =
          (innerAutomorphismHom g.left)⁻¹
        rw [map_inv]
    _ = (MulAut.conj g.left * phi g.right)⁻¹ := by
      rw [mul_inv_rev]
    _ = (semidirectToMulAut phi g)⁻¹ := congrArg Inv.inv hg.symm
    _ = semidirectToMulAut phi g⁻¹ := (map_inv _ g).symm

end ActualBrauerCarriers

section CanonicalEmbeddedCopy

variable {H E X : Type u} [Group H] [Group E]
variable {phi : E →* MulAut H} [MulAction (H ⋊[phi] E) X]

/-- The canonical equivalence from `H` to its embedded copy in a
semidirect-product stabiliser when the normal factor fixes the point. -/
def canonicalHToEmbeddedEquiv (x : X)
    (hfixed : ∀ h : H, (SemidirectProduct.inl h : H ⋊[phi] E) • x = x) :
    H ≃* embeddedHStabilizer (phi := phi) x where
  toFun h :=
    ⟨⟨SemidirectProduct.inl h, hfixed h⟩,
      ⟨⟨h, hfixed h⟩, rfl⟩⟩
  invFun y := (y.1.1 : H ⋊[phi] E).left
  left_inv h := rfl
  right_inv y := by
    rcases y with ⟨y, ⟨h, rfl⟩⟩
    rfl
  map_mul' h g := by
    apply Subtype.ext
    apply Subtype.ext
    simp

@[simp]
theorem canonicalHToEmbeddedEquiv_apply_coe (x : X)
    (hfixed : ∀ h : H, (SemidirectProduct.inl h : H ⋊[phi] E) • x = x)
    (h : H) :
    (((canonicalHToEmbeddedEquiv x hfixed h :
      embeddedHStabilizer (phi := phi) x) :
      semidirectStabilizer (phi := phi) x) : H ⋊[phi] E) =
        SemidirectProduct.inl h :=
  rfl

end CanonicalEmbeddedCopy

section ActualGlobalExtension

variable {p : ℕ} {k K H E : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H] [Group E] [Finite E] [IsCyclic E]

/-- Pull a prime regular class function back along a group equivalence. -/
def pullbackPrimeRegularAlongEquiv
    {N : Type u} [Group N]
    (e : H ≃* N) (chi : PrimeRegularClassFunction K H p) :
    PrimeRegularClassFunction K N p :=
  PrimeRegularClassFunction.pullback e.symm.toMonoidHom chi

@[simp]
theorem pullbackPrimeRegularAlongEquiv_apply
    {N : Type u} [Group N]
    (e : H ≃* N) (chi : PrimeRegularClassFunction K H p)
    (x : PrimeRegularElement (G := N) p) :
    pullbackPrimeRegularAlongEquiv e chi x =
      chi (PrimeRegularElement.map e.symm.toMonoidHom x) :=
  rfl

/-- Extend a function-valued irreducible Brauer character to its stabiliser
and transport the base character along the canonical embedded copy. -/
theorem global_extension_actual
    (iota : PrimeRegularRootEmbedding p k K H)
    (phi : E →* MulAut H)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (psi : IBr iota) :
    let _ : MulAction H (IBr iota) :=
      rightAutomorphismAction (X := IBr iota)
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (IBr iota) :=
      rightAutomorphismAction (X := IBr iota) phi
    let hcompat := rightAutomorphismSemidirectCompatible
      (X := IBr iota) phi
    let _ : MulAction (H ⋊[phi] E) (IBr iota) :=
      semidirectMulAction phi hcompat
    let hinner : ∀ h : H,
        (SemidirectProduct.inl h : H ⋊[phi] E) • psi = psi := fun h ↦ by
      rw [semidirect_inl_smul]
      exact inner_fixes_ibr iota h psi
    let eH := canonicalHToEmbeddedEquiv psi hinner
    ∀ (iotaEmbedded : PrimeRegularRootEmbedding p k K
        (embeddedHStabilizer (phi := phi) psi))
      (pullbackIrreducible : IsIrreducibleBrauerCharacter iotaEmbedded
        (pullbackPrimeRegularAlongEquiv eH psi.1))
      (conjugationSquare :
        ∀ (d : semidirectStabilizer (phi := phi) psi)
          (x : PrimeRegularElement
            (G := embeddedHStabilizer (phi := phi) psi) p),
          PrimeRegularElement.map eH.symm.toMonoidHom
              (PrimeRegularElement.map (MulAut.conjNormal d).toMonoidHom x) =
            PrimeRegularElement.map
              (semidirectToMulAut phi (d : H ⋊[phi] E)).toMonoidHom
              (PrimeRegularElement.map eH.symm.toMonoidHom x)),
      ∃ W : FDRep k (embeddedHStabilizer (phi := phi) psi),
        Representation.IsIrreducible W.ρ ∧
        pullbackPrimeRegularAlongEquiv eH psi.1 =
          Representation.brauerCharacterOfRootEmbedding W.ρ iotaEmbedded ∧
        Nonempty (Representation.Extension
          (embeddedHStabilizer (phi := phi) psi) W.ρ) := by
  dsimp only
  letI : MulAction H (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (IBr iota) :=
    rightAutomorphismAction (X := IBr iota) phi
  let hcompat := rightAutomorphismSemidirectCompatible
    (X := IBr iota) phi
  letI : MulAction (H ⋊[phi] E) (IBr iota) :=
    semidirectMulAction phi hcompat
  have hinner : ∀ h : H,
      (SemidirectProduct.inl h : H ⋊[phi] E) • psi = psi := by
    intro h
    rw [semidirect_inl_smul]
    exact inner_fixes_ibr iota h psi
  let eH := canonicalHToEmbeddedEquiv psi hinner
  intro iotaEmbedded pullbackIrreducible conjugationSquare
  let psiEmbedded : IBr iotaEmbedded :=
    ⟨pullbackPrimeRegularAlongEquiv eH psi.1, pullbackIrreducible⟩
  have hfixed : ∀ d : semidirectStabilizer (phi := phi) psi,
      IrreducibleBrauerCharacter.twist iotaEmbedded psiEmbedded
        (MulAut.conjNormal d) = psiEmbedded := by
    intro d
    have hdInv : ((d⁻¹ : semidirectStabilizer (phi := phi) psi) :
        H ⋊[phi] E) • psi = psi := (d⁻¹).property
    have hpsi : IrreducibleBrauerCharacter.twist iota psi
        (semidirectToMulAut phi (d : H ⋊[phi] E)) = psi := by
      rw [semidirect_smul_ibr_eq_twist_inverse] at hdInv
      simpa using hdInv
    apply Subtype.ext
    apply PrimeRegularClassFunction.ext
    intro x
    change psi.1
        (PrimeRegularElement.map eH.symm.toMonoidHom
          (PrimeRegularElement.map (MulAut.conjNormal d).toMonoidHom x)) =
      psi.1 (PrimeRegularElement.map eH.symm.toMonoidHom x)
    rw [conjugationSquare]
    exact congrArg
      (fun chi : IBr iota ↦ chi.1
        (PrimeRegularElement.map eH.symm.toMonoidHom x)) hpsi
  exact Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
    principle iotaEmbedded psiEmbedded
      (isCyclic_stabilizer_quotient (phi := phi) psi) hfixed

end ActualGlobalExtension

end ModularRep.PaperProofs.CyclicOuterLemma37Concrete


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
