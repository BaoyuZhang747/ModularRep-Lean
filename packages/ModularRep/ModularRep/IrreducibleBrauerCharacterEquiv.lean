import ModularRep.BrauerCharacterHomPullback

/-!
# Equivalence of irreducible Brauer characters under a group equivalence

The one-way transport in `BrauerCharacterEquivTransport` is an equivalence.
This file constructs its inverse explicitly by pulling back the underlying
class function and an affording irreducible representation.  The proof uses
only the kernel-checked compatibility of Brauer-character formation with
pullback and the equality of the transported root-lift functions.
-/

noncomputable section

namespace ModularRep

universe u v w x

namespace PrimeRegularClassFunction

variable {R : Type v} {G : Type w} {H : Type x} {p : ℕ}
variable [Group G] [Group H]

/-- Pullback along a group equivalence gives an equivalence of prime regular
class functions. -/
def equivAlongMulEquiv (e : G ≃* H) :
    PrimeRegularClassFunction R G p ≃
      PrimeRegularClassFunction R H p where
  toFun := pullback e.symm.toMonoidHom
  invFun := pullback e.toMonoidHom
  left_inv chi := by
    apply PrimeRegularClassFunction.ext
    intro g
    change chi (PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map e.toMonoidHom g)) = chi g
    congr 1
    apply Subtype.ext
    exact e.symm_apply_apply g.1
  right_inv psi := by
    apply PrimeRegularClassFunction.ext
    intro h
    change psi (PrimeRegularElement.map e.toMonoidHom
      (PrimeRegularElement.map e.symm.toMonoidHom h)) = psi h
    congr 1
    apply Subtype.ext
    exact e.apply_symm_apply h.1

@[simp]
theorem equivAlongMulEquiv_apply (e : G ≃* H)
    (chi : PrimeRegularClassFunction R G p) :
    equivAlongMulEquiv e chi = pullback e.symm.toMonoidHom chi :=
  rfl

@[simp]
theorem equivAlongMulEquiv_symm_apply (e : G ≃* H)
    (psi : PrimeRegularClassFunction R H p) :
    (equivAlongMulEquiv e).symm psi = pullback e.toMonoidHom psi :=
  rfl

@[simp]
theorem equivAlongMulEquiv_apply_eval (e : G ≃* H)
    (chi : PrimeRegularClassFunction R G p)
    (h : PrimeRegularElement (G := H) p) :
    equivAlongMulEquiv e chi h =
      chi (PrimeRegularElement.map e.symm.toMonoidHom h) :=
  rfl

@[simp]
theorem equivAlongMulEquiv_symm_apply_eval (e : G ≃* H)
    (psi : PrimeRegularClassFunction R H p)
    (g : PrimeRegularElement (G := G) p) :
    (equivAlongMulEquiv e).symm psi g =
      psi (PrimeRegularElement.map e.toMonoidHom g) :=
  rfl

/-- Pullback transport intertwines twisting by an automorphism with twisting
by the conjugate automorphism on the equivalent group. -/
theorem equivAlongMulEquiv_twist (e : G ≃* H)
    (chi : PrimeRegularClassFunction R G p) (alpha : MulAut G) :
    equivAlongMulEquiv e (chi.twist alpha) =
      (equivAlongMulEquiv e chi).twist (MulAut.congr e alpha) := by
  apply PrimeRegularClassFunction.ext
  intro h
  change chi (PrimeRegularElement.map alpha.toMonoidHom
      (PrimeRegularElement.map e.symm.toMonoidHom h)) =
    chi (PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map (MulAut.congr e alpha).toMonoidHom h))
  congr 1
  apply Subtype.ext
  simp [MulAut.congr]

end PrimeRegularClassFunction

variable {p : ℕ} {k : Type u} {K : Type v} {G : Type w} {H : Type x}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H]

namespace IrreducibleBrauerCharacter

/-- The explicit inverse to transport of an irreducible Brauer character
along a group equivalence. -/
def alongMulEquivInverse (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (psi : IBr (iota.alongMulEquiv e)) : IBr iota := by
  refine ⟨PrimeRegularClassFunction.pullback e.toMonoidHom psi.1, ?_⟩
  rcases psi.2 with ⟨V, hV, hpsi⟩
  refine ⟨FDRep.of (Representation.pullback V.ρ e.toMonoidHom),
    hV.pullback e.toMonoidHom e.surjective, ?_⟩
  rw [FDRep.of_ρ', hpsi]
  exact (Representation.brauerCharacterOfRootEmbedding_pullback_of_lift_eq
    V.ρ (iota.alongMulEquiv e) iota e.toMonoidHom
      (funext fun z ↦ (iota.alongMulEquiv_lift e z).symm)).symm

@[simp]
theorem alongMulEquivInverse_val
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (psi : IBr (iota.alongMulEquiv e)) :
    (alongMulEquivInverse iota e psi).1 =
      PrimeRegularClassFunction.pullback e.toMonoidHom psi.1 :=
  rfl

/-- Transport along a finite group equivalence is an equivalence on the
function-valued irreducible Brauer characters. -/
def equivAlongMulEquiv (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) : IBr iota ≃ IBr (iota.alongMulEquiv e) where
  toFun := alongMulEquiv iota e
  invFun := alongMulEquivInverse iota e
  left_inv phi := by
    apply Subtype.ext
    apply PrimeRegularClassFunction.ext
    intro g
    change phi.1 (PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map e.toMonoidHom g)) = phi.1 g
    congr 1
    apply Subtype.ext
    exact e.symm_apply_apply g.1
  right_inv psi := by
    apply Subtype.ext
    apply PrimeRegularClassFunction.ext
    intro h
    change psi.1 (PrimeRegularElement.map e.toMonoidHom
      (PrimeRegularElement.map e.symm.toMonoidHom h)) = psi.1 h
    congr 1
    apply Subtype.ext
    exact e.apply_symm_apply h.1

@[simp]
theorem equivAlongMulEquiv_apply
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (phi : IBr iota) :
    equivAlongMulEquiv iota e phi = alongMulEquiv iota e phi :=
  rfl

@[simp]
theorem equivAlongMulEquiv_symm_apply
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (psi : IBr (iota.alongMulEquiv e)) :
    (equivAlongMulEquiv iota e).symm psi =
      alongMulEquivInverse iota e psi :=
  rfl

@[simp]
theorem equivAlongMulEquiv_val
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (phi : IBr iota) :
    (equivAlongMulEquiv iota e phi).1 =
      PrimeRegularClassFunction.equivAlongMulEquiv e phi.1 :=
  rfl

@[simp]
theorem equivAlongMulEquiv_symm_val
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (psi : IBr (iota.alongMulEquiv e)) :
    ((equivAlongMulEquiv iota e).symm psi).1 =
      (PrimeRegularClassFunction.equivAlongMulEquiv e).symm psi.1 :=
  rfl

@[simp]
theorem equivAlongMulEquiv_apply_eval
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (phi : IBr iota)
    (h : PrimeRegularElement (G := H) p) :
    (equivAlongMulEquiv iota e phi).1 h =
      phi.1 (PrimeRegularElement.map e.symm.toMonoidHom h) :=
  rfl

@[simp]
theorem equivAlongMulEquiv_symm_apply_eval
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (psi : IBr (iota.alongMulEquiv e))
    (g : PrimeRegularElement (G := G) p) :
    ((equivAlongMulEquiv iota e).symm psi).1 g =
      psi.1 (PrimeRegularElement.map e.toMonoidHom g) :=
  rfl

@[simp]
theorem alongMulEquivInverse_alongMulEquiv
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (phi : IBr iota) :
    alongMulEquivInverse iota e (alongMulEquiv iota e phi) = phi :=
  (equivAlongMulEquiv iota e).left_inv phi

@[simp]
theorem alongMulEquiv_alongMulEquivInverse
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (psi : IBr (iota.alongMulEquiv e)) :
    alongMulEquiv iota e (alongMulEquivInverse iota e psi) = psi :=
  (equivAlongMulEquiv iota e).right_inv psi

/-- The character equivalence intertwines the right automorphism convention
with conjugation of automorphisms by the group equivalence. -/
theorem equivAlongMulEquiv_twist
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (phi : IBr iota) (alpha : MulAut G) :
    equivAlongMulEquiv iota e (twist iota phi alpha) =
      twist (iota.alongMulEquiv e) (equivAlongMulEquiv iota e phi)
        (MulAut.congr e alpha) := by
  apply Subtype.ext
  exact PrimeRegularClassFunction.equivAlongMulEquiv_twist e phi.1 alpha

/-- Equivariance in the opposite-group encoding of the manuscript's right
automorphism action. -/
theorem equivAlongMulEquiv_op_smul
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (phi : IBr iota) (alpha : (MulAut G)ᵐᵒᵖ) :
    equivAlongMulEquiv iota e (alpha • phi) =
      MulOpposite.op (MulAut.congr e alpha.unop) •
        equivAlongMulEquiv iota e phi :=
  equivAlongMulEquiv_twist iota e phi alpha.unop

end IrreducibleBrauerCharacter

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
