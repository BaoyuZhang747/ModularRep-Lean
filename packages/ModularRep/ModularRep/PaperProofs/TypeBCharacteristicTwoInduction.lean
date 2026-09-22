import ModularRep.PaperProofs.CharacterInductionEquivariance
import ModularRep.IrreducibleBrauerCharacter

/-!
# Literal induction for the characteristic-two Clifford window

The induction relation is the actual finite-sum class-function formula on
prime regular elements, using zero extension on the inducing subgroup.
Navarro Definition 8.1, p. 151, and Theorem 8.2, pp. 151--155, identify this
formula with Brauer induction. Theorem 8.9, p. 160, supplies existence and
injectivity only on the literal Clifford fibre in a separate source packet.

This file proves naturality under actual subgroup/ambient automorphism
squares and uniqueness of the induced character by equality of functions.
No Clifford relation, action compatibility, correspondence bijection,
stabilizer factorization or source theorem is assumed here. Root agreement
is required when attaching the representation theoretic source; the
function-level identities below hold for the displayed character functions.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoInduction

open CharacterInductionEquivariance

universe u v

section ZeroExtension

variable {p : ℕ} {R : Type v} {G : Type u} [Zero R] [Group G]

/-- The standard zero extension of a prime regular class function. -/
def zeroExtend (chi : PrimeRegularClassFunction R G p) (g : G) : R := by
  classical
  exact if h : IsPrimeRegular p g then chi ⟨g, h⟩ else 0

@[simp] theorem zeroExtend_regular (chi : PrimeRegularClassFunction R G p)
    (g : PrimeRegularElement (G := G) p) : zeroExtend chi g.1 = chi g := by
  classical
  simp only [zeroExtend, dif_pos g.2]
  rfl

/-- Zero extension commutes with the actual automorphism pullback. -/
theorem zeroExtend_twist (chi : PrimeRegularClassFunction R G p) (tau : MulAut G) :
    zeroExtend (chi.twist tau) = fun g ↦ zeroExtend chi (tau g) := by
  classical
  funext g
  by_cases hg : IsPrimeRegular p g
  · have htg : IsPrimeRegular p (tau g) := hg.map tau.toMonoidHom
    simp only [zeroExtend, dif_pos hg, dif_pos htg]
    rfl
  · have htg : ¬ IsPrimeRegular p (tau g) := by
      intro h
      exact hg ((isPrimeRegular_map_mulEquiv tau g).mp h)
    simp only [zeroExtend, dif_neg hg, dif_neg htg]

end ZeroExtension

section Functions

variable {p : ℕ} {H K : Type u} [Group H] [Fintype H] [Field K]

/-- The literal induction sum, restricted to prime regular elements of H. -/
def inducedValue (I : Subgroup H) (chi : PrimeRegularClassFunction K I p) :
    PrimeRegularFunction K H p :=
  fun g ↦ inducedCharacter I (zeroExtend chi) g.1

/-- The fixed induction relation on actual class functions. -/
def Induces (I : Subgroup H) (chi : PrimeRegularClassFunction K I p)
    (psi : PrimeRegularClassFunction K H p) : Prop :=
  ∀ g : PrimeRegularElement (G := H) p, inducedValue I chi g = psi g

/-- The existing finite-sum naturality theorem applies to zero-extended
Brauer class functions without assuming ordinary Frobenius reciprocity. -/
theorem inducedValue_twist (I : Subgroup H) (tau : MulAut H)
    (stable : ∀ x : H, x ∈ I ↔ tau x ∈ I)
    (chi : PrimeRegularClassFunction K I p)
    (g : PrimeRegularElement (G := H) p) :
    inducedValue I (chi.twist (restrictAut I tau stable)) g =
      inducedValue I chi (PrimeRegularElement.map tau.toMonoidHom g) := by
  change inducedCharacter I (zeroExtend (chi.twist (restrictAut I tau stable))) g.1 =
    inducedCharacter I (zeroExtend chi) (tau g.1)
  rw [zeroExtend_twist]
  exact inducedCharacter_natural I tau stable (zeroExtend chi) g.1

theorem Induces.twist (I : Subgroup H) (tau : MulAut H)
    (stable : ∀ x : H, x ∈ I ↔ tau x ∈ I)
    {chi : PrimeRegularClassFunction K I p} {psi : PrimeRegularClassFunction K H p}
    (h : Induces I chi psi) :
    Induces I (chi.twist (restrictAut I tau stable)) (psi.twist tau) := by
  intro g
  change inducedValue I (chi.twist (restrictAut I tau stable)) g =
    psi (PrimeRegularElement.map tau.toMonoidHom g)
  rw [inducedValue_twist]
  exact h (PrimeRegularElement.map tau.toMonoidHom g)

/-- The target of the literal induction relation is unique on all class
functions. Fibre injectivity is a separate Clifford source statement. -/
theorem Induces.unique (I : Subgroup H)
    {chi : PrimeRegularClassFunction K I p} {psi psi' : PrimeRegularClassFunction K H p}
    (h : Induces I chi psi) (h' : Induces I chi psi') : psi = psi' := by
  apply PrimeRegularClassFunction.ext
  intro g
  exact (h g).symm.trans (h' g)

/-- An actual commuting inclusion square already proves subgroup stability. -/
theorem stable_of_square (I : Subgroup H) (tau : MulAut H) (tauI : MulAut I)
    (square : ∀ x : I, ((tauI x : I) : H) = tau (x : H)) :
    ∀ x : H, x ∈ I ↔ tau x ∈ I := by
  intro x
  constructor
  · intro hx
    have h := (tauI ⟨x, hx⟩).property
    rw [square] at h
    exact h
  · intro hx
    let y : I := tauI.symm ⟨tau x, hx⟩
    have hty : tau (y : H) = tau x := by
      rw [← square y]
      exact congrArg (fun z : I ↦ (z : H)) (tauI.apply_symm_apply ⟨tau x, hx⟩)
    have hy : (y : H) = x := tau.injective hty
    exact hy ▸ y.property

/-- The automorphism in a commuting inclusion square is precisely the
canonical restriction, so no separate local action identification is needed. -/
theorem restrictAut_eq_of_square (I : Subgroup H) (tau : MulAut H) (tauI : MulAut I)
    (square : ∀ x : I, ((tauI x : I) : H) = tau (x : H)) :
    restrictAut I tau (stable_of_square I tau tauI square) = tauI := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact (square x).symm

/-- Naturality for the displayed subgroup and ambient automorphisms,
requiring only their original pointwise inclusion square. -/
theorem Induces.twist_of_square (I : Subgroup H) (tau : MulAut H) (tauI : MulAut I)
    (square : ∀ x : I, ((tauI x : I) : H) = tau (x : H))
    {chi : PrimeRegularClassFunction K I p} {psi : PrimeRegularClassFunction K H p}
    (h : Induces I chi psi) : Induces I (chi.twist tauI) (psi.twist tau) := by
  have ht := Induces.twist I tau (stable_of_square I tau tauI square) h
  rw [restrictAut_eq_of_square I tau tauI square] at ht
  exact ht

end Functions

section BrauerCharacters

variable {p : ℕ} {H K : Type u} {k : Type v}
variable [Group H] [Fintype H] [Field k] [Field K]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable (I : Subgroup H)
variable (iotaI : PrimeRegularRootEmbedding p k K I)
variable (iotaH : PrimeRegularRootEmbedding p k K H)

/-- The literal Brauer induction relation, with no arbitrary relation field. -/
def BrauerInduces (eta : IBr iotaI) (psi : IBr iotaH) : Prop :=
  Induces I eta.1 psi.1

theorem BrauerInduces.unique {eta : IBr iotaI} {psi psi' : IBr iotaH}
    (h : BrauerInduces I iotaI iotaH eta psi)
    (h' : BrauerInduces I iotaI iotaH eta psi') : psi = psi' := by
  apply Subtype.ext
  exact Induces.unique I h h'

/-- Naturality on actual irreducible Brauer characters under an automorphism
preserving the inducing subgroup. -/
theorem BrauerInduces.twist (tau : MulAut H)
    (stable : ∀ x : H, x ∈ I ↔ tau x ∈ I)
    {eta : IBr iotaI} {psi : IBr iotaH}
    (h : BrauerInduces I iotaI iotaH eta psi) :
    BrauerInduces I iotaI iotaH
      (IrreducibleBrauerCharacter.twist iotaI eta (restrictAut I tau stable))
      (IrreducibleBrauerCharacter.twist iotaH psi tau) :=
  Induces.twist I tau stable h

/-- Naturality under the actual inertia/ambient automorphism square.
Passing inverse automorphisms gives the manuscript right-action convention. -/
theorem BrauerInduces.twist_of_square (tau : MulAut H) (tauI : MulAut I)
    (square : ∀ x : I, ((tauI x : I) : H) = tau (x : H))
    {eta : IBr iotaI} {psi : IBr iotaH}
    (h : BrauerInduces I iotaI iotaH eta psi) :
    BrauerInduces I iotaI iotaH (IrreducibleBrauerCharacter.twist iotaI eta tauI)
      (IrreducibleBrauerCharacter.twist iotaH psi tau) :=
  Induces.twist_of_square I tau tauI square h

end BrauerCharacters

end ModularRep.PaperProofs.TypeBCharacteristicTwoInduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
