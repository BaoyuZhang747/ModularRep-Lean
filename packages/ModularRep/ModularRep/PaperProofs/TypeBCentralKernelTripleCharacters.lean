import ModularRep.PaperProofs.TypeBCentralKernelNormalizerInertia
import ModularRep.PaperProofs.TypeBCentralKernelTripleCarriers

/-!
# Literal characters on the central-kernel triple carriers

The base is G viewed inside its actual Brauer inertia T. The local base is
the actual intersection inside the raw inertia U viewed inside T. Its
character is the inflation of the reduction of the same local ordinary
character, transported through the displayed normalizer equivalence.

Only the established local reduction sources are used for invariance.
The U <= T argument is internal construction data. No upstairs triple
witness, character-matching principle or inductive-condition input occurs.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelTripleCharacters

open ModularRep CharacterWeight TypeBCentralKernelCarriers
open TypeBCentralKernelInertia TypeBCentralKernelLocalReduction
open TypeBCentralKernelNormalizerInertia TypeBCentralKernelBrauerInflation
open TypeBCentralKernelTripleCarriers TypeBCentralKernelTripleCertificate
open TypeBCentralKernelWeightTransport

universe u

section FunctionTransport

variable {p : ℕ} {k K X Y X' Y' : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Finite X] [Group Y] [Finite Y]
variable [Group X'] [Finite X'] [Group Y'] [Finite Y']

/-- Function-valued inflation commutes with actual group equivalences and
a literal square of group homomorphisms. No character existence is assumed. -/
theorem pullback_equiv_square (eX : X ≃* X') (eY : Y ≃* Y')
    (f : X →* Y) (f' : X' →* Y')
    (square : ∀ x, f' (eX x) = eY (f x))
    (phi : PrimeRegularClassFunction K Y p) :
    PrimeRegularClassFunction.equivAlongMulEquiv eX
        (PrimeRegularClassFunction.pullback f phi) =
      PrimeRegularClassFunction.pullback f'
        (PrimeRegularClassFunction.equivAlongMulEquiv eY phi) := by
  ext x
  change phi (PrimeRegularElement.map f (PrimeRegularElement.map eX.symm.toMonoidHom x)) =
    phi (PrimeRegularElement.map eY.symm.toMonoidHom (PrimeRegularElement.map f' x))
  congr 1
  apply Subtype.ext
  apply eY.injective
  change eY (f (eX.symm x.val)) = eY (eY.symm (f' x.val))
  rw [eY.apply_symm_apply]
  have h := square (eX.symm x.val)
  rw [eX.apply_symm_apply] at h
  exact h.symm

/-- A previously established literal inflation equation is transported
through the preceding square. The equation is proof data, not a source. -/
theorem brauer_inflation_transport
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (eX : X ≃* X') (eY : Y ≃* Y') (f : X →* Y) (f' : X' →* Y')
    (square : ∀ x, f' (eX x) = eY (f x))
    (psi : IBr iotaX) (phi : IBr iotaY)
    (inflation : psi.val = PrimeRegularClassFunction.pullback f phi.val) :
    (IrreducibleBrauerCharacter.equivAlongMulEquiv iotaX eX psi).val =
      PrimeRegularClassFunction.pullback f'
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iotaY eY phi).val := by
  change PrimeRegularClassFunction.equivAlongMulEquiv eX psi.val = _
  rw [inflation]
  exact pullback_equiv_square eX eY f f' square phi.val

/-- Invariance is transported using the pointwise automorphism square. -/
theorem brauer_fixed_of_square
    (iota : PrimeRegularRootEmbedding p k K X) (e : X ≃* Y)
    (psi : IBr iota) (alpha : MulAut X) (beta : MulAut Y)
    (square : ∀ x, e (alpha x) = beta (e x))
    (fixed : IrreducibleBrauerCharacter.twist iota psi alpha = psi) :
    IrreducibleBrauerCharacter.twist (iota.alongMulEquiv e)
      (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi) beta =
        IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi := by
  have conjugation : MulAut.congr e alpha = beta := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    change e (alpha (e.symm (e x))) = _
    rw [e.symm_apply_apply]
    exact square x
  have natural := IrreducibleBrauerCharacter.equivAlongMulEquiv_twist iota e psi alpha
  rw [fixed, conjugation] at natural
  exact natural.symm

end FunctionTransport

section ActualTriple

variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Finite A] (G : Subgroup A) [G.Normal]
variable (iota : PrimeRegularRootEmbedding p k K G) (theta : IBr iota)

abbrev inertia := T G iota theta
abbrev base := inside G (inertia G iota theta)

def baseEquiv : G ≃* base G iota theta :=
  insideEquiv G (inertia G iota theta) (G_le_T G iota theta)

@[simp] theorem baseEquiv_ambient (x : G) :
    (baseEquiv G iota theta x).val.val = x.val := rfl

theorem baseEquiv_conjugation (a : inertia G iota theta) (x : G) :
    baseEquiv G iota theta (originalAction G (a : A) x) =
      MulAut.conjNormal (H := base G iota theta) a (baseEquiv G iota theta x) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

def baseRoot : PrimeRegularRootEmbedding p k K (base G iota theta) :=
  iota.alongMulEquiv (baseEquiv G iota theta)

theorem baseRoot_lift (z : k) : (baseRoot G iota theta).lift z = iota.lift z :=
  iota.alongMulEquiv_lift (baseEquiv G iota theta) z

def baseBrauer : IBr (baseRoot G iota theta) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv iota (baseEquiv G iota theta) theta

theorem baseBrauer_value (x : PrimeRegularElement (G := base G iota theta) p) :
    (baseBrauer G iota theta).val x =
      theta.val (PrimeRegularElement.map (baseEquiv G iota theta).symm.toMonoidHom x) := rfl

theorem baseBrauer_fixed (a : inertia G iota theta) :
    IrreducibleBrauerCharacter.twist (baseRoot G iota theta) (baseBrauer G iota theta)
      (MulAut.conjNormal (H := base G iota theta) a) = baseBrauer G iota theta := by
  have fixed : IrreducibleBrauerCharacter.twist iota theta
      (originalAction G (a : A)) = theta := by
    have hi := (mem_brauerStabilizer (originalAction G) iota theta ((a : A)⁻¹)).mp a⁻¹.property
    simpa only [inv_inv] using hi
  exact brauer_fixed_of_square iota (baseEquiv G iota theta) theta
    (originalAction G (a : A)) (MulAut.conjNormal (H := base G iota theta) a)
    (baseEquiv_conjugation G iota theta a) fixed

variable (W : CharacterWeight p K G)
variable (hUT : U G W ≤ inertia G iota theta)

abbrev localAmbient := inside (U G W) (inertia G iota theta)
abbrev tripleLocal := localBase (base G iota theta) (localAmbient G iota theta W)

def localActorEquiv : U G W ≃* localAmbient G iota theta W :=
  insideEquiv (U G W) (inertia G iota theta) hUT

/-- The complete normalizer-to-M map is the composition of the two checked
literal subgroup equivalences. -/
def localEquiv : Subgroup.normalizer (W.subgroup : Set G) ≃* tripleLocal G iota theta W :=
  (normalizerEquivLocalBase G W).trans
    (nestedLocalEquiv G (inertia G iota theta) (U G W) hUT)

@[simp] theorem localEquiv_ambient (x : Subgroup.normalizer (W.subgroup : Set G)) :
    (localEquiv G iota theta W hUT x).val.val.val = ((x : G) : A) := rfl

theorem localEquiv_conjugation (a : U G W)
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    localEquiv G iota theta W hUT
      (normalizerAction G W.subgroup (rawNormalizerMap G W a) x) =
      MulAut.conjNormal (H := tripleLocal G iota theta W)
        (localActorEquiv G iota theta W hUT a) (localEquiv G iota theta W hUT x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ((normalizerAction G W.subgroup (rawNormalizerMap G W a) x : G) : A) =
    (a : A) * ((x : G) : A) * (a : A)⁻¹
  rw [normalizerAction_coe, originalAction_val]
  rfl

variable (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))

def localRoot : PrimeRegularRootEmbedding p k K (tripleLocal G iota theta W) :=
  (normalizerRoot W iotaQ).alongMulEquiv (localEquiv G iota theta W hUT)

theorem localRoot_lift (z : k) :
    (localRoot G iota theta W hUT iotaQ).lift z = (normalizerRoot W iotaQ).lift z :=
  (normalizerRoot W iotaQ).alongMulEquiv_lift (localEquiv G iota theta W hUT) z

def localBrauer (phiQ : IBr iotaQ) : IBr (localRoot G iota theta W hUT iotaQ) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (normalizerRoot W iotaQ)
    (localEquiv G iota theta W hUT) (inflatedReduction W iotaQ phiQ)

theorem localBrauer_value (phiQ : IBr iotaQ)
    (x : PrimeRegularElement (G := tripleLocal G iota theta W) p) :
    (localBrauer G iota theta W hUT iotaQ phiQ).val x =
      (inflatedReduction W iotaQ phiQ).val
        (PrimeRegularElement.map (localEquiv G iota theta W hUT).symm.toMonoidHom x) := rfl

theorem localBrauer_reduction (phiQ : IBr iotaQ)
    (reduction : Reduces iotaQ W.localCharacter phiQ)
    (x : PrimeRegularElement (G := tripleLocal G iota theta W) p) :
    W.localCharacter (localMk W.subgroup ((localEquiv G iota theta W hUT).symm x.val)) =
      (localBrauer G iota theta W hUT iotaQ phiQ).val x :=
  inflatedReduction_value W iotaQ phiQ reduction
    (PrimeRegularElement.map (localEquiv G iota theta W hUT).symm.toMonoidHom x)

theorem localBrauer_fixed [IsAlgClosed K]
    (source : Navarro318Certificate p k K)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
    (phiQ : IBr iotaQ) (reduction : Reduces iotaQ W.localCharacter phiQ)
    (a : localAmbient G iota theta W) :
    IrreducibleBrauerCharacter.twist (localRoot G iota theta W hUT iotaQ)
      (localBrauer G iota theta W hUT iotaQ phiQ)
      (MulAut.conjNormal (H := tripleLocal G iota theta W) a) =
        localBrauer G iota theta W hUT iotaQ phiQ := by
  obtain ⟨a, rfl⟩ := (localActorEquiv G iota theta W hUT).surjective a
  have hraw : W.rightTwist (originalAction G (a : A)) = W := by
    have hi := (mem_rawStabilizer (originalAction G) W ((a : A)⁻¹)).mp a⁻¹.property
    simpa only [inv_inv] using hi
  have fixed : IrreducibleBrauerCharacter.twist (normalizerRoot W iotaQ)
      (inflatedReduction W iotaQ phiQ)
      (normalizerAction G W.subgroup (rawNormalizerMap G W a)) =
        inflatedReduction W iotaQ phiQ :=
    (rightTwist_eq_iff_brauer_fixed source regular W iotaQ phiQ reduction
      (originalAction G (a : A))
      (normalizer_stable G W.subgroup (rawNormalizerMap G W a))).mp hraw
  exact brauer_fixed_of_square (normalizerRoot W iotaQ) (localEquiv G iota theta W hUT)
    (inflatedReduction W iotaQ phiQ)
    (normalizerAction G W.subgroup (rawNormalizerMap G W a))
    (MulAut.conjNormal (H := tripleLocal G iota theta W) (localActorEquiv G iota theta W hUT a))
    (localEquiv_conjugation G iota theta W hUT a) fixed

end ActualTriple

end ModularRep.PaperProofs.TypeBCentralKernelTripleCharacters


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
