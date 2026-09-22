import ModularRep.PaperProofs.TypeBLemma47LeviApplication
import ModularRep.NavarroCoveringBrauerExtension
import ModularRep.IrreducibleBrauerCharacterEquiv
import ModularRep.BrauerCharacterCommonRootCompatibility

/-!
# Literal restriction constituents in the characteristic-two Clifford window

The base group is the actual `N.subgroupOf H`. Its root convention and
characters are transported along the canonical equivalence from `N`.
`Occurs` is the existing nonnegative finite restriction expansion, not an
uninterpreted relation. Root agreement is retained in the published-source
domain, and representation pullback compatibility is proved from it.

The only external principle here is Navarro, Corollary 8.7, pp. 158--159:
the actual restriction constituents of an irreducible Brauer character
form one inner orbit. This is an E1/U source identification on the displayed
fields and roots. All automorphism naturality is proved by reindexing the
literal expansion. No induction, Gallagher, or stabilizer conclusion is an
input to this module.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoConstituentSource

open ModularRep
open NavarroCoveringBrauerExtension
open TypeBLemma47LeviApplication
open ModularRep.ManuscriptVerification.CharacteristicTwoClifford

universe u

variable {Gamma E k K : Type u}
variable [Group Gamma] [Finite Gamma] [Group E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- Literal finite nonnegative restriction support along a displayed group
homomorphism. Applications to inertia groups supply the actual base embedding;
no abstract lies-over relation or implicit carrier change occurs here. -/
def OccursAlong {A B : Type u} [Group A] [Finite A] [Group B] [Finite B]
    (f : B →* A)
    (iotaA : PrimeRegularRootEmbedding 2 k K A)
    (iotaB : PrimeRegularRootEmbedding 2 k K B)
    (psi : IBr iotaA) (theta : IBr iotaB) : Prop :=
  ∃ multiplicity : IBr iotaB →₀ ℕ,
    multiplicity theta ≠ 0 ∧
      ∀ x : PrimeRegularElement (G := B) 2,
        psi.1 (PrimeRegularElement.map f x) =
          multiplicity.sum (fun eta n => (n : K) * eta.1 x)

/-- Changing from an actual base group to its isomorphic subgroup copy
preserves constituent support, by an explicit reindexing of multiplicities. -/
theorem occursAlong_iff_occursInRestriction
    {A B : Type u} [Group A] [Finite A] [Group B] [Finite B]
    (U : Subgroup A) (e : B ≃* U)
    (iotaA : PrimeRegularRootEmbedding 2 k K A)
    (iotaB : PrimeRegularRootEmbedding 2 k K B)
    (psi : IBr iotaA) (theta : IBr iotaB) :
    OccursAlong (U.subtype.comp e.toMonoidHom) iotaA iotaB psi theta ↔
      BrauerOccursInRestriction U iotaA (iotaB.alongMulEquiv e) psi
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iotaB e theta) := by
  classical
  let t := IrreducibleBrauerCharacter.equivAlongMulEquiv iotaB e
  constructor
  · rintro ⟨m, hm, hvalue⟩
    refine ⟨Finsupp.equivMapDomain t m, ?_, ?_⟩
    · change Finsupp.equivMapDomain t m (t theta) ≠ 0
      simpa only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] using hm
    · intro x
      rw [Finsupp.sum_equivMapDomain]
      change psi.1 (PrimeRegularElement.map U.subtype x) =
        m.sum (fun eta n => (n : K) *
          eta.1 (PrimeRegularElement.map e.symm.toMonoidHom x))
      have hmap : PrimeRegularElement.map (U.subtype.comp e.toMonoidHom)
          (PrimeRegularElement.map e.symm.toMonoidHom x) =
          PrimeRegularElement.map U.subtype x := by
        apply Subtype.ext
        exact congrArg (fun y : U => (y : A)) (e.apply_symm_apply x.1)
      simpa only [hmap] using hvalue (PrimeRegularElement.map e.symm.toMonoidHom x)
  · rintro ⟨m, hm, hvalue⟩
    refine ⟨Finsupp.equivMapDomain t.symm m, ?_, ?_⟩
    · simpa only [Finsupp.equivMapDomain_apply, Equiv.symm_symm] using hm
    · intro x
      rw [Finsupp.sum_equivMapDomain]
      exact hvalue (PrimeRegularElement.map e.toMonoidHom x)

/-- The canonical identification of the base group with its literal copy
inside `H`. Both directions preserve the underlying ambient element. -/
def baseEquiv (H N : Subgroup Gamma) (hNH : N ≤ H) :
    N ≃* N.subgroupOf H where
  toFun x := ⟨⟨x.1, hNH x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def embeddedRoot (H N : Subgroup Gamma) (hNH : N ≤ H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N) :
    PrimeRegularRootEmbedding 2 k K (N.subgroupOf H) :=
  iotaN.alongMulEquiv (baseEquiv H N hNH)

def embeddedCharacter (H N : Subgroup Gamma) (hNH : N ≤ H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN) :
    IBr (embeddedRoot H N hNH iotaN) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv iotaN (baseEquiv H N hNH) theta

/-- The literal, already defined nonnegative restriction support. -/
def Occurs (H N : Subgroup Gamma) (hNH : N ≤ H)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (psi : IBr iotaH) (theta : IBr iotaN) : Prop :=
  BrauerOccursInRestriction (N.subgroupOf H) iotaH
    (embeddedRoot H N hNH iotaN) psi (embeddedCharacter H N hNH iotaN theta)

/-- On the original base carrier, `Occurs` is exactly restriction along the
canonical subgroup inclusion. -/
theorem occurs_iff_occursAlong (H N : Subgroup Gamma) (hNH : N ≤ H)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (psi : IBr iotaH) (theta : IBr iotaN) :
    Occurs H N hNH iotaH iotaN psi theta ↔
      OccursAlong (Subgroup.inclusion hNH) iotaH iotaN psi theta :=
  (occursAlong_iff_occursInRestriction (N.subgroupOf H)
    (baseEquiv H N hNH) iotaH iotaN psi theta).symm

/-- The prescribed roots for `H` and `N` use the same lift on all roots
needed by `N`; no equality of the zero-extended lifts is required. -/
def RootAgreement (H N : Subgroup Gamma)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N) : Prop :=
  ∀ z : rootsOfUnity (primeRegularExponent 2 N) k,
    iotaN.lift (((z : kˣ) : k)) = iotaH.lift (((z : kˣ) : k))

theorem embeddedRoot_agrees (H N : Subgroup Gamma) (hNH : N ≤ H)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (roots : RootAgreement H N iotaH iotaN)
    (z : rootsOfUnity (primeRegularExponent 2 (N.subgroupOf H)) k) :
    (embeddedRoot H N hNH iotaN).lift (((z : kˣ) : k)) =
      iotaH.lift (((z : kˣ) : k)) := by
  have hexp : primeRegularExponent 2 (N.subgroupOf H) =
      primeRegularExponent 2 N :=
    congrArg (fun n : ℕ => ordCompl[2] n)
      (Nat.card_congr (baseEquiv H N hNH).symm.toEquiv)
  let zN : rootsOfUnity (primeRegularExponent 2 N) k :=
    ⟨z.1, by simpa only [hexp] using z.2⟩
  rw [show (embeddedRoot H N hNH iotaN).lift (((z : kˣ) : k)) =
    iotaN.lift (((z : kˣ) : k)) from
      iotaN.alongMulEquiv_lift (baseEquiv H N hNH) _]
  exact roots zN

/-- The source root guard is sufficient for the actual representation
restriction to realize exactly the class-function restriction used above. -/
theorem embedded_brauer_pullback (H N : Subgroup Gamma) (hNH : N ≤ H)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (roots : RootAgreement H N iotaH iotaN) (V : FDRep k H) :
    Representation.brauerCharacterOfRootEmbedding
        (Representation.pullback V.ρ (N.subgroupOf H).subtype)
        (embeddedRoot H N hNH iotaN) =
      PrimeRegularClassFunction.pullback (N.subgroupOf H).subtype
        (Representation.brauerCharacterOfRootEmbedding V.ρ iotaH) :=
  Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
    V.ρ iotaH (embeddedRoot H N hNH iotaN) (N.subgroupOf H).subtype
    (Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
      V.ρ iotaH (embeddedRoot H N hNH iotaN) (N.subgroupOf H).subtype
      (embeddedRoot_agrees H N hNH iotaH iotaN roots))

section ExpansionNaturality

variable {A : Type u} [Group A] [Finite A]

/-- The actual twist is a permutation of the irreducible Brauer characters. -/
def twistEquiv (iota : PrimeRegularRootEmbedding 2 k K A) (alpha : MulAut A) :
    IBr iota ≃ IBr iota where
  toFun phi := IrreducibleBrauerCharacter.twist iota phi alpha
  invFun phi := IrreducibleBrauerCharacter.twist iota phi alpha⁻¹
  left_inv phi := by
    change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota phi alpha) alpha⁻¹ = phi
    rw [IrreducibleBrauerCharacter.twist_mul, mul_inv_cancel]
    exact IrreducibleBrauerCharacter.twist_refl iota phi
  right_inv phi := by
    change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota phi alpha⁻¹) alpha = phi
    rw [IrreducibleBrauerCharacter.twist_mul, inv_mul_cancel]
    exact IrreducibleBrauerCharacter.twist_refl iota phi

/-- Literal restriction support is natural along any commuting square of
group homomorphisms and automorphisms. In particular this applies directly
to the actual base embedding in each inertia group. -/
theorem occursAlong_twist
    {B : Type u} [Group B] [Finite B]
    (f : B →* A)
    (iotaA : PrimeRegularRootEmbedding 2 k K A)
    (iotaB : PrimeRegularRootEmbedding 2 k K B)
    (alpha : MulAut A) (beta : MulAut B)
    (square : ∀ x : B, alpha (f x) = f (beta x))
    (psi : IBr iotaA) (theta : IBr iotaB)
    (occurs : OccursAlong f iotaA iotaB psi theta) :
    OccursAlong f iotaA iotaB
      (IrreducibleBrauerCharacter.twist iotaA psi alpha)
      (IrreducibleBrauerCharacter.twist iotaB theta beta) := by
  classical
  obtain ⟨m, hm, hvalue⟩ := occurs
  refine ⟨Finsupp.equivMapDomain (twistEquiv iotaB beta) m, ?_, ?_⟩
  · change Finsupp.equivMapDomain (twistEquiv iotaB beta) m
      ((twistEquiv iotaB beta) theta) ≠ 0
    simpa only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] using hm
  · intro x
    rw [Finsupp.sum_equivMapDomain]
    change psi.1 (PrimeRegularElement.map alpha.toMonoidHom
        (PrimeRegularElement.map f x)) =
      m.sum (fun t n => (n : K) * t.1 (PrimeRegularElement.map beta.toMonoidHom x))
    have hmap : PrimeRegularElement.map alpha.toMonoidHom
        (PrimeRegularElement.map f x) =
        PrimeRegularElement.map f (PrimeRegularElement.map beta.toMonoidHom x) := by
      apply Subtype.ext
      exact square x.1
    rw [hmap]
    exact hvalue (PrimeRegularElement.map beta.toMonoidHom x)

/-- A commuting group square transports actual constituent support.
The new multiplicity is the old multiplicity reindexed by the twist. -/
theorem occursInRestriction_twist
    (U : Subgroup A)
    (iotaA : PrimeRegularRootEmbedding 2 k K A)
    (iotaU : PrimeRegularRootEmbedding 2 k K U)
    (alpha : MulAut A) (beta : MulAut U)
    (square : ∀ x : U, alpha (x : A) = (beta x : A))
    (psi : IBr iotaA) (theta : IBr iotaU)
    (occurs : BrauerOccursInRestriction U iotaA iotaU psi theta) :
    BrauerOccursInRestriction U iotaA iotaU
      (IrreducibleBrauerCharacter.twist iotaA psi alpha)
      (IrreducibleBrauerCharacter.twist iotaU theta beta) := by
  classical
  obtain ⟨m, hm, hvalue⟩ := occurs
  refine ⟨Finsupp.equivMapDomain (twistEquiv iotaU beta) m, ?_, ?_⟩
  · change Finsupp.equivMapDomain (twistEquiv iotaU beta) m
      ((twistEquiv iotaU beta) theta) ≠ 0
    simpa only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] using hm
  · intro x
    rw [Finsupp.sum_equivMapDomain]
    change psi.1 (PrimeRegularElement.map alpha.toMonoidHom
        (PrimeRegularElement.map U.subtype x)) =
      m.sum (fun t n => (n : K) * t.1 (PrimeRegularElement.map beta.toMonoidHom x))
    have hmap : PrimeRegularElement.map alpha.toMonoidHom
        (PrimeRegularElement.map U.subtype x) =
        PrimeRegularElement.map U.subtype (PrimeRegularElement.map beta.toMonoidHom x) := by
      apply Subtype.ext
      exact square x.1
    rw [hmap]
    exact hvalue (PrimeRegularElement.map beta.toMonoidHom x)

end ExpansionNaturality

/-- Naturality on the original `N` carrier, transported through its actual
subgroup copy. The input is just a square of group automorphisms. -/
theorem occurs_twist (H N : Subgroup Gamma) (hNH : N ≤ H)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (alphaH : MulAut H) (alphaN : MulAut N)
    (square : ∀ x : N,
      alphaH (Subgroup.inclusion hNH x) = Subgroup.inclusion hNH (alphaN x))
    (psi : IBr iotaH) (theta : IBr iotaN)
    (occurs : Occurs H N hNH iotaH iotaN psi theta) :
    Occurs H N hNH iotaH iotaN
      (IrreducibleBrauerCharacter.twist iotaH psi alphaH)
      (IrreducibleBrauerCharacter.twist iotaN theta alphaN) := by
  unfold Occurs embeddedCharacter embeddedRoot at occurs ⊢
  rw [IrreducibleBrauerCharacter.equivAlongMulEquiv_twist]
  apply occursInRestriction_twist _ _ _ _ _ _ _ _ occurs
  intro x
  exact square ((baseEquiv H N hNH).symm x)

section CanonicalActions

variable (H N : Subgroup Gamma) [H.Normal] [N.Normal] (hNH : N ≤ H)
variable (iotaH : PrimeRegularRootEmbedding 2 k K H)
variable (iotaN : PrimeRegularRootEmbedding 2 k K N)
variable (field : E →* MulAut Gamma)
variable (hH : ∀ e : E, ∀ g : Gamma, g ∈ H ↔ field e g ∈ H)
variable (hN : ∀ e : E, ∀ g : Gamma, g ∈ N ↔ field e g ∈ N)

theorem occurs_ambient (a : Gamma) (psi : IBr iotaH) (theta : IBr iotaN)
    (occurs : Occurs H N hNH iotaH iotaN psi theta) :
    let _ := ambientBrauerAction H iotaH
    let _ := ambientBrauerAction N iotaN
    Occurs H N hNH iotaH iotaN (a • psi) (a • theta) := by
  dsimp only
  apply occurs_twist H N hNH iotaH iotaN
    (MulAut.conjNormal (H := H) a⁻¹) (MulAut.conjNormal (H := N) a⁻¹)
    _ psi theta occurs
  intro x
  rfl

theorem occurs_field (e : E) (psi : IBr iotaH) (theta : IBr iotaN)
    (occurs : Occurs H N hNH iotaH iotaN psi theta) :
    let _ := fieldBrauerAction H iotaH field hH
    let _ := fieldBrauerAction N iotaN field hN
    Occurs H N hNH iotaH iotaN (e • psi) (e • theta) := by
  dsimp only
  apply occurs_twist H N hNH iotaH iotaN
    (restrictAutomorphismHom H field hH e⁻¹)
    (restrictAutomorphismHom N field hN e⁻¹) _ psi theta occurs
  intro x
  rfl

end CanonicalActions

/-- Uniform E1/U reading of Navarro, Corollary 8.7, pp. 158--159,
on the actual constituent-support definition. Common roots authenticate the
representation restriction. Its character-theoretic output is only the
single inner orbit; it has no action-factorization or Clifford-correspondent
conclusion. The use of inverse conjugation matches the checked right action.
-/
def Navarro87Principle (k K : Type u)
    [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K] : Prop :=
  ∀ {Gamma : Type u} [Group Gamma] [Finite Gamma]
    (H N : Subgroup Gamma) [H.Normal] [N.Normal] (hNH : N ≤ H)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N),
    RootAgreement H N iotaH iotaN →
    ∀ (psi : IBr iotaH) (theta₁ theta₂ : IBr iotaN),
      Occurs H N hNH iotaH iotaN psi theta₁ →
      Occurs H N hNH iotaH iotaN psi theta₂ →
      ∃ h : H, IrreducibleBrauerCharacter.twist iotaN theta₁
        (MulAut.conjNormal (H := N) (h : Gamma)⁻¹) = theta₂

/-- The existing Clifford-orbit interface with its relation fixed to actual
restriction support and both equivariance fields proved in Lean. -/
def constituentOrbit
    (H N : Subgroup Gamma) [H.Normal] [N.Normal] (hNH : N ≤ H)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (roots : RootAgreement H N iotaH iotaN)
    (field : E →* MulAut Gamma)
    (hH : ∀ e : E, ∀ g : Gamma, g ∈ H ↔ field e g ∈ H)
    (hN : ∀ e : E, ∀ g : Gamma, g ∈ N ↔ field e g ∈ N)
    (source : Navarro87Principle k K)
    (psi : IBr iotaH) (theta : IBr iotaN)
    (chosen : Occurs H N hNH iotaH iotaN psi theta) :
    let _ := ambientBrauerAction H iotaH
    let _ := ambientBrauerAction N iotaN
    let _ := fieldBrauerAction H iotaH field hH
    let _ := fieldBrauerAction N iotaN field hN
    CliffordConstituentOrbit (E := E) H.subtype psi theta := by
  letI : MulAction Gamma (IBr iotaH) := ambientBrauerAction H iotaH
  letI : MulAction Gamma (IBr iotaN) := ambientBrauerAction N iotaN
  letI : MulAction E (IBr iotaH) := fieldBrauerAction H iotaH field hH
  letI : MulAction E (IBr iotaN) := fieldBrauerAction N iotaN field hN
  dsimp only
  refine {
    Constituent := Occurs H N hNH iotaH iotaN
    chosen := chosen
    equivariant_A := ?_
    equivariant_E := ?_
    single_inner_orbit := ?_ }
  · exact occurs_ambient H N hNH iotaH iotaN
  · exact occurs_field H N hNH iotaH iotaN field hH hN
  · exact source H N hNH iotaH iotaN roots psi

end ModularRep.PaperProofs.TypeBCharacteristicTwoConstituentSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
