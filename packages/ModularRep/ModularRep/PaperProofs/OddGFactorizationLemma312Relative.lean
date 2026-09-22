import ModularRep.PaperProofs.OddConformalProposition311Relative
import ModularRep.PaperProofs.EvenFieldAssumption53Relative
import ModularRep.PaperProofs.OddConlonOrbitAssembly
import ModularRep.PaperProofs.TypeBRightActionOrientation
import ModularRep.StabilizerFactorizationTransport
import ModularRep.OrdinaryIrreducibleCharacter
import Formalisation.FibreTransport

/-!
# Relative proof surface for manuscript Lemma 3.12

This file checks the two deductions made in Lemma 3.12 after the integral
basic set has been supplied:

* the action of a block stabiliser descends through its subgroup of inner
  automorphisms, and the resulting equivariant basic-set bijection transfers
  Li's ordinary-character stabiliser factorisation to actual function-valued
  irreducible Brauer characters;
* the stabiliser in the cyclic field group is cyclic, so Navarro's cyclic
  extension theorem applies after the concrete copy of the base group and
  its Brauer characters have been identified.

The ordinary factorisation itself is the statement used before
unitriangularity in the proof of Li, Lemma 5.4.  It remains an explicit
published input.  The global integral basic set and its exact `K₀` action
are likewise explicit inputs from Feng--Li--Zhang, Theorem 2.14, together
with standard naturality of reduction.  No Brauer stabiliser factorisation,
extension, BAW-goodness, or iBAW conclusion is assumed.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddGFactorizationLemma312Relative

open scoped MonoidAlgebra
open Formalisation
open FDRepSimpleClassKZero
open ExactGrothendieckGroup
open DecompositionBasicSetBridge
open BlockFibreRestriction
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport
open ModularRep.PaperProofs.OddConformalProposition311Relative
open ModularRep.PaperProofs.EvenFieldAssumption53Relative
open ModularRep.PaperProofs.OddConlonOrbitAssembly

universe u

/-! ## Actual ordinary and Brauer character actions -/

namespace OrdinaryAction

variable {K G A : Type u}
variable [Field K] [CharZero K] [Group G] [Group A]

/-- Successive twists of ordinary characters obey the manuscript's right
action convention. -/
@[simp]
theorem twist_mul
    (chi : OrdinaryIrreducibleCharacter.Irr K G)
    (alpha beta : MulAut G) :
    OrdinaryIrreducibleCharacter.twist K G
        (OrdinaryIrreducibleCharacter.twist K G chi alpha) beta =
      OrdinaryIrreducibleCharacter.twist K G chi (alpha * beta) := by
  apply OrdinaryIrreducibleCharacter.ext
  intro g
  rfl

/-- The canonical right automorphism action on function-valued ordinary
irreducible characters, encoded as a left action of the opposite group. -/
@[instance_reducible]
def oppositeAutomorphismAction :
    MulAction (MulAut G)ᵐᵒᵖ
      (OrdinaryIrreducibleCharacter.Irr K G) where
  smul alpha chi :=
    OrdinaryIrreducibleCharacter.twist K G chi alpha.unop
  one_smul chi := OrdinaryIrreducibleCharacter.twist_refl K G chi
  mul_smul alpha beta chi := by
    change OrdinaryIrreducibleCharacter.twist K G chi
        (MulOpposite.unop (alpha * beta)) =
      OrdinaryIrreducibleCharacter.twist K G
        (OrdinaryIrreducibleCharacter.twist K G chi beta.unop) alpha.unop
    rw [MulOpposite.unop_mul]
    exact (twist_mul chi beta.unop alpha.unop).symm

/-- Pull the right automorphism action back along a concrete automorphism
homomorphism. -/
@[instance_reducible]
def rightAutomorphismAction
    (rho : A →* MulAut G) :
    MulAction A (OrdinaryIrreducibleCharacter.Irr K G) := by
  letI : MulAction (MulAut G)ᵐᵒᵖ
      (OrdinaryIrreducibleCharacter.Irr K G) :=
    oppositeAutomorphismAction
  exact MulAction.compHom _
    (EvenFieldAssumption53Relative.inverseOpHom rho)

/-- The manuscript orbit of an ordinary irreducible character is the orbit
for the inverse left action used in this module. -/
theorem manuscriptRightOrbit_eq_leanOrbit
    (rho : A →* MulAut G)
    (chi : OrdinaryIrreducibleCharacter.Irr K G) :
    let _ : MulAction (MulAut G)ᵐᵒᵖ
        (OrdinaryIrreducibleCharacter.Irr K G) :=
      oppositeAutomorphismAction
    let _ : MulAction A (OrdinaryIrreducibleCharacter.Irr K G) :=
      rightAutomorphismAction rho
    TypeBRightActionOrientation.manuscriptRightOrbit rho chi =
      MulAction.orbit A chi := by
  let _ : MulAction (MulAut G)ᵐᵒᵖ
      (OrdinaryIrreducibleCharacter.Irr K G) :=
    oppositeAutomorphismAction
  exact TypeBRightActionOrientation.manuscriptRightOrbit_eq_leanOrbit rho chi

/-- The manuscript and Lean stabilisers of an ordinary irreducible character
agree under the inverse left action used in this module. -/
theorem manuscriptRightStabilizer_eq_leanStabilizer
    (rho : A →* MulAut G)
    (chi : OrdinaryIrreducibleCharacter.Irr K G) :
    let _ : MulAction (MulAut G)ᵐᵒᵖ
        (OrdinaryIrreducibleCharacter.Irr K G) :=
      oppositeAutomorphismAction
    let _ : MulAction A (OrdinaryIrreducibleCharacter.Irr K G) :=
      rightAutomorphismAction rho
    TypeBRightActionOrientation.manuscriptRightStabilizer rho chi =
      MulAction.stabilizer A chi := by
  let _ : MulAction (MulAut G)ᵐᵒᵖ
      (OrdinaryIrreducibleCharacter.Irr K G) :=
    oppositeAutomorphismAction
  exact
    TypeBRightActionOrientation.manuscriptRightStabilizer_eq_leanStabilizer
      rho chi

/-- Inner automorphisms fix actual ordinary character functions. -/
theorem twist_conj
    (chi : OrdinaryIrreducibleCharacter.Irr K G) (g : G) :
    OrdinaryIrreducibleCharacter.twist K G chi (MulAut.conj g) = chi := by
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  rcases chi.2 with ⟨R⟩
  change chi (g * x * g⁻¹) = chi x
  calc
    chi (g * x * g⁻¹) =
        R.representation.character (g * x * g⁻¹) :=
      (congrFun R.character_eq (g * x * g⁻¹)).symm
    _ = R.representation.character x := R.representation.char_conj x g
    _ = chi x := congrFun R.character_eq x

/-- A subgroup represented by inner automorphisms acts trivially on actual
ordinary irreducible characters. -/
theorem subgroup_acts_trivially_of_inner
    (rho : A →* MulAut G) (N : Subgroup A)
    (hinner : ∀ n : N, ∃ g : G, rho n = MulAut.conj g) :
    let _ : MulAction A (OrdinaryIrreducibleCharacter.Irr K G) :=
      rightAutomorphismAction rho
    ∀ (n : N) (chi : OrdinaryIrreducibleCharacter.Irr K G),
      (n : A) • chi = chi := by
  dsimp only
  letI : MulAction A (OrdinaryIrreducibleCharacter.Irr K G) :=
    rightAutomorphismAction rho
  intro n chi
  obtain ⟨g, hg⟩ := hinner n
  change OrdinaryIrreducibleCharacter.twist K G chi (rho (n : A)⁻¹) = chi
  rw [map_inv, hg]
  simpa only [map_inv] using (twist_conj chi g⁻¹)

end OrdinaryAction

/-- The actual ordinary-character action written as a function, so that
source interfaces can mention it without relying on a local typeclass
instance. -/
def ordinaryAutomorphismAct
    {K G A : Type u} [Field K] [CharZero K] [Group G] [Group A]
    (rho : A →* MulAut G) (a : A)
    (chi : OrdinaryIrreducibleCharacter.Irr K G) :
    OrdinaryIrreducibleCharacter.Irr K G :=
  OrdinaryIrreducibleCharacter.twist K G chi (rho a⁻¹)

/-- A source-shaped ordinary basic set: an actual predicate on actual
ordinary irreducible character functions, stable under the supplied
automorphism group. -/
structure OrdinaryBasicData
    {K G A BlockIndex : Type u}
    [Field K] [CharZero K] [Group G] [Group A]
    [MulAction A BlockIndex]
    (rho : A →* MulAut G) where
  predicate : OrdinaryIrreducibleCharacter.Irr K G → Prop
  predicate_stable : ∀ (a : A)
    (chi : OrdinaryIrreducibleCharacter.Irr K G),
    predicate chi → predicate (ordinaryAutomorphismAct rho a chi)
  blockOf : {chi : OrdinaryIrreducibleCharacter.Irr K G // predicate chi} →
    BlockIndex
  block_equivariant : ∀ (a : A)
    (chi : {chi : OrdinaryIrreducibleCharacter.Irr K G // predicate chi}),
    blockOf ⟨ordinaryAutomorphismAct rho a chi.1,
      predicate_stable a chi.1 chi.2⟩ = a • blockOf chi

namespace OrdinaryBasicData

/-- The induced action on the literal basic-set subtype. -/
@[instance_reducible]
def mulAction
    {K G A BlockIndex : Type u}
    [Field K] [CharZero K] [Group G] [Group A]
    [MulAction A BlockIndex]
    (rho : A →* MulAut G)
    (B : OrdinaryBasicData (BlockIndex := BlockIndex) rho) :
    MulAction A {chi : OrdinaryIrreducibleCharacter.Irr K G // B.predicate chi} where
  smul a chi := ⟨ordinaryAutomorphismAct rho a chi.1,
    B.predicate_stable a chi.1 chi.2⟩
  one_smul chi := by
    apply Subtype.ext
    exact show ordinaryAutomorphismAct rho (1 : A) chi.1 = chi.1 by
      unfold ordinaryAutomorphismAct
      rw [inv_one, map_one]
      convert OrdinaryIrreducibleCharacter.twist_refl K G chi.1 using 1
      ext x
      rfl
  mul_smul a b chi := by
    apply Subtype.ext
    change OrdinaryIrreducibleCharacter.twist K G chi.1 (rho (a * b)⁻¹) =
      OrdinaryIrreducibleCharacter.twist K G
        (OrdinaryIrreducibleCharacter.twist K G chi.1 (rho b⁻¹))
          (rho a⁻¹)
    rw [mul_inv_rev, map_mul, OrdinaryAction.twist_mul]

@[simp]
theorem smul_val
    {K G A BlockIndex : Type u}
    [Field K] [CharZero K] [Group G] [Group A]
    [MulAction A BlockIndex]
    (rho : A →* MulAut G)
    (B : OrdinaryBasicData (BlockIndex := BlockIndex) rho)
    (a : A)
    (chi : {chi : OrdinaryIrreducibleCharacter.Irr K G // B.predicate chi}) :
    let _ : MulAction A
        {chi : OrdinaryIrreducibleCharacter.Irr K G // B.predicate chi} :=
      B.mulAction rho
    (a • chi).1 = ordinaryAutomorphismAct rho a chi.1 := by
  rfl

end OrdinaryBasicData

/-- A subgroup represented by inner automorphisms acts trivially on actual
function-valued irreducible Brauer characters. -/
theorem brauer_subgroup_acts_trivially_of_inner
    {p : ℕ} {k K G A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group A]
    (iota : PrimeRegularRootEmbedding p k K G)
    (rho : A →* MulAut G) (N : Subgroup A)
    (hinner : ∀ n : N, ∃ g : G, rho n = MulAut.conj g) :
    let _ : MulAction A (IBr iota) :=
      EvenFieldAssumption53Relative.rightAutomorphismAction iota rho
    ∀ (n : N) (phi : IBr iota), (n : A) • phi = phi := by
  dsimp only
  letI : MulAction A (IBr iota) :=
    EvenFieldAssumption53Relative.rightAutomorphismAction iota rho
  intro n phi
  obtain ⟨g, hg⟩ := hinner n
  change IrreducibleBrauerCharacter.twist iota phi (rho (n : A)⁻¹) = phi
  rw [map_inv, hg]
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  simpa only [map_inv] using PrimeRegularClassFunction.twist_conj phi.1 g⁻¹

/-! ## The conformal-field semidirect action -/

/-- Source-shaped compatibility of the conformal and field automorphisms of
the base group. -/
def AutomorphismSemidirectCompatible
    {G D E : Type u} [Group G] [Group D] [Group E]
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G) : Prop :=
  ∀ e : E,
    rhoD.comp (action e).toMonoidHom =
      (MulAut.conj (rhoE e)).toMonoidHom.comp rhoD

/-- The actual automorphism homomorphism from the conformal-field
semidirect product to the automorphism group of the base group. -/
def semidirectAutomorphismHom
    {G D E : Type u} [Group G] [Group D] [Group E]
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G)
    (hcompat : AutomorphismSemidirectCompatible action rhoD rhoE) :
    D ⋊[action] E →* MulAut G :=
  SemidirectProduct.lift rhoD rhoE hcompat

/-- The separate right actions of the conformal and field groups on actual
Brauer characters satisfy the semidirect compatibility equation. -/
theorem brauer_semidirect_compatible
    {p : ℕ} {k K G D E : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group D] [Group E]
    (iota : PrimeRegularRootEmbedding p k K G)
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G)
    (hcompat : AutomorphismSemidirectCompatible action rhoD rhoE) :
    let _ : MulAction D (IBr iota) :=
      EvenFieldAssumption53Relative.rightAutomorphismAction iota rhoD
    let _ : MulAction E (IBr iota) :=
      EvenFieldAssumption53Relative.rightAutomorphismAction iota rhoE
    SemidirectActionCompatible (X := IBr iota) action := by
  dsimp only
  intro e d psi
  change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi (rhoD d⁻¹))
        (rhoE e⁻¹) =
    IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi (rhoE e⁻¹))
        (rhoD ((action e) d)⁻¹)
  rw [IrreducibleBrauerCharacter.twist_mul,
    IrreducibleBrauerCharacter.twist_mul]
  congr 1
  simp only [map_inv]
  have h := DFunLike.ext_iff.mp (hcompat e) d
  change rhoD ((action e) d) = rhoE e * rhoD d * (rhoE e)⁻¹ at h
  have hinv := congrArg Inv.inv h
  simp only [mul_inv_rev, inv_inv] at hinv
  rw [hinv]
  simp

/-- The separate right actions on actual ordinary characters satisfy the
same semidirect compatibility equation. -/
theorem ordinary_semidirect_compatible
    {K G D E : Type u}
    [Field K] [CharZero K] [Group G] [Group D] [Group E]
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G)
    (hcompat : AutomorphismSemidirectCompatible action rhoD rhoE) :
    let _ : MulAction D (OrdinaryIrreducibleCharacter.Irr K G) :=
      OrdinaryAction.rightAutomorphismAction rhoD
    let _ : MulAction E (OrdinaryIrreducibleCharacter.Irr K G) :=
      OrdinaryAction.rightAutomorphismAction rhoE
    SemidirectActionCompatible
      (X := OrdinaryIrreducibleCharacter.Irr K G) action := by
  dsimp only
  intro e d chi
  change OrdinaryIrreducibleCharacter.twist K G
      (OrdinaryIrreducibleCharacter.twist K G chi (rhoD d⁻¹))
        (rhoE e⁻¹) =
    OrdinaryIrreducibleCharacter.twist K G
      (OrdinaryIrreducibleCharacter.twist K G chi (rhoE e⁻¹))
        (rhoD ((action e) d)⁻¹)
  rw [OrdinaryAction.twist_mul, OrdinaryAction.twist_mul]
  congr 1
  simp only [map_inv]
  have h := DFunLike.ext_iff.mp (hcompat e) d
  change rhoD ((action e) d) = rhoE e * rhoD d * (rhoE e)⁻¹ at h
  have hinv := congrArg Inv.inv h
  simp only [mul_inv_rev, inv_inv] at hinv
  rw [hinv]
  simp

/-- Evaluate the compatible semidirect action on an actual Brauer
character.  Naming this operation prevents instance shadowing in the
comparison below. -/
def brauerSemidirectAct
    {p : ℕ} {k K G D E : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group D] [Group E]
    (iota : PrimeRegularRootEmbedding p k K G)
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G)
    (_hcompat : AutomorphismSemidirectCompatible action rhoD rhoE)
    (a : D ⋊[action] E) (psi : IBr iota) : IBr iota :=
  IrreducibleBrauerCharacter.twist iota
    (IrreducibleBrauerCharacter.twist iota psi (rhoE a.right⁻¹))
      (rhoD a.left⁻¹)

/-- Evaluate the action obtained from the actual semidirect automorphism
homomorphism. -/
def brauerSemidirectAutomorphismAct
    {p : ℕ} {k K G D E : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group D] [Group E]
    (iota : PrimeRegularRootEmbedding p k K G)
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G)
    (hcompat : AutomorphismSemidirectCompatible action rhoD rhoE)
    (a : D ⋊[action] E) (psi : IBr iota) : IBr iota :=
  IrreducibleBrauerCharacter.twist iota psi
    ((semidirectAutomorphismHom action rhoD rhoE hcompat) a⁻¹)

/-- Acting through the semidirect automorphism homomorphism is the same as
the compatible semidirect action on actual Brauer characters. -/
theorem brauer_semidirect_smul_eq_automorphism_smul
    {p : ℕ} {k K G D E : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group D] [Group E]
    (iota : PrimeRegularRootEmbedding p k K G)
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G)
    (hcompat : AutomorphismSemidirectCompatible action rhoD rhoE)
    (a : D ⋊[action] E) (psi : IBr iota) :
    brauerSemidirectAct iota action rhoD rhoE hcompat a psi =
      brauerSemidirectAutomorphismAct iota action rhoD rhoE hcompat a psi := by
  unfold brauerSemidirectAct brauerSemidirectAutomorphismAct
  rw [show
    (semidirectAutomorphismHom action rhoD rhoE hcompat) a⁻¹ =
      ((semidirectAutomorphismHom action rhoD rhoE hcompat) a)⁻¹ by
        exact map_inv _ a]
  rw [show
    (semidirectAutomorphismHom action rhoD rhoE hcompat) a =
      rhoD a.left * rhoE a.right by rfl]
  simp only [map_inv]
  change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi ((rhoE a.right)⁻¹))
        ((rhoD a.left)⁻¹) =
    IrreducibleBrauerCharacter.twist iota psi
      ((rhoD a.left * rhoE a.right)⁻¹)
  rw [IrreducibleBrauerCharacter.twist_mul]
  simp only [mul_inv_rev]

/-- Explicit compatible semidirect action on actual ordinary characters. -/
def ordinarySemidirectAct
    {K G D E : Type u}
    [Field K] [CharZero K] [Group G] [Group D] [Group E]
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G)
    (_hcompat : AutomorphismSemidirectCompatible action rhoD rhoE)
    (a : D ⋊[action] E)
    (chi : OrdinaryIrreducibleCharacter.Irr K G) :
    OrdinaryIrreducibleCharacter.Irr K G :=
  OrdinaryIrreducibleCharacter.twist K G
    (OrdinaryIrreducibleCharacter.twist K G chi (rhoE a.right⁻¹))
      (rhoD a.left⁻¹)

/-- Explicit action of the semidirect automorphism homomorphism on actual
ordinary characters. -/
def ordinarySemidirectAutomorphismAct
    {K G D E : Type u}
    [Field K] [CharZero K] [Group G] [Group D] [Group E]
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G)
    (hcompat : AutomorphismSemidirectCompatible action rhoD rhoE)
    (a : D ⋊[action] E)
    (chi : OrdinaryIrreducibleCharacter.Irr K G) :
    OrdinaryIrreducibleCharacter.Irr K G :=
  OrdinaryIrreducibleCharacter.twist K G chi
    ((semidirectAutomorphismHom action rhoD rhoE hcompat) a⁻¹)

/-- The two explicitly named ordinary-character actions agree.  Unlike an
instance-shadowed statement `a • chi = a • chi`, the theorem type retains the
two distinct action functions. -/
theorem ordinary_semidirect_smul_eq_automorphism_smul
    {K G D E : Type u}
    [Field K] [CharZero K] [Group G] [Group D] [Group E]
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G)
    (hcompat : AutomorphismSemidirectCompatible action rhoD rhoE)
    (a : D ⋊[action] E)
    (chi : OrdinaryIrreducibleCharacter.Irr K G) :
    ordinarySemidirectAct action rhoD rhoE hcompat a chi =
      ordinarySemidirectAutomorphismAct action rhoD rhoE hcompat a chi := by
  unfold ordinarySemidirectAct ordinarySemidirectAutomorphismAct
  rw [show
    (semidirectAutomorphismHom action rhoD rhoE hcompat) a⁻¹ =
      ((semidirectAutomorphismHom action rhoD rhoE hcompat) a)⁻¹ by
        exact map_inv _ a]
  rw [show
    (semidirectAutomorphismHom action rhoD rhoE hcompat) a =
      rhoD a.left * rhoE a.right by rfl]
  simp only [map_inv]
  rw [OrdinaryAction.twist_mul]
  simp only [mul_inv_rev]

/-- The left-factor action obtained by restricting a literal semidirect
product action. -/
@[instance_reducible]
def semidirectLeftRestrictedAction
    {D E X : Type u} [Group D] [Group E]
    (action : E →* MulAut D) [MulAction (D ⋊[action] E) X] :
    MulAction D X :=
  MulAction.compHom X (SemidirectProduct.inl : D →* D ⋊[action] E)

/-- The right-factor action obtained from the same ambient action. -/
@[instance_reducible]
def semidirectRightRestrictedAction
    {D E X : Type u} [Group D] [Group E]
    (action : E →* MulAut D) [MulAction (D ⋊[action] E) X] :
    MulAction E X :=
  MulAction.compHom X (SemidirectProduct.inr : E →* D ⋊[action] E)

/-- Every ambient semidirect action decomposes into its literal left and
right restrictions. -/
theorem semidirectRestrictedAction_eq
    {D E X : Type u} [Group D] [Group E]
    (action : E →* MulAut D) [MulAction (D ⋊[action] E) X] :
    let _ : MulAction D X := semidirectLeftRestrictedAction action
    let _ : MulAction E X := semidirectRightRestrictedAction action
    ∀ (a : D ⋊[action] E) (x : X),
      a • x = a.left • (a.right • x) := by
  dsimp only
  intro a x
  change a • x =
    (SemidirectProduct.inl a.left : D ⋊[action] E) •
      ((SemidirectProduct.inr a.right : D ⋊[action] E) • x)
  rw [← mul_smul]
  congr 1
  ext <;> simp

/-! ## Quotienting an action by a subgroup acting trivially -/

/-- A group action descends to a quotient when the normal subgroup acts
trivially.  This is the precise action-theoretic meaning of quotienting the
block stabiliser by inner automorphisms. -/
@[instance_reducible]
def quotientMulActionOfTrivialSubgroup
    {A X : Type u} [Group A] [MulAction A X]
    (N : Subgroup A) [N.Normal]
    (hN : ∀ (n : N) (x : X), (n : A) • x = x) :
    MulAction (A ⧸ N) X :=
  MulAction.compHom X <|
    QuotientGroup.lift N (MulAction.toPermHom A X) <| by
      intro a ha
      apply Equiv.ext
      intro x
      exact hN ⟨a, ha⟩ x

@[simp]
theorem quotientMulActionOfTrivialSubgroup_mk_smul
    {A X : Type u} [Group A] [MulAction A X]
    (N : Subgroup A) [N.Normal]
    (hN : ∀ (n : N) (x : X), (n : A) • x = x)
    (a : A) (x : X) :
    let _ : MulAction (A ⧸ N) X :=
      quotientMulActionOfTrivialSubgroup N hN
    QuotientGroup.mk' N a • x = a • x := by
  dsimp only [quotientMulActionOfTrivialSubgroup]
  rfl

/-- Restrict an ambient action to the literal stabiliser of a block. -/
@[instance_reducible]
def blockStabilizerMulAction
    {A X BlockIndex : Type u} [Group A]
    [MulAction A X] [MulAction A BlockIndex]
    (block : BlockIndex) :
    MulAction (MulAction.stabilizer A block) X :=
  MulAction.compHom X (MulAction.stabilizer A block).subtype

/-- Descend the block-stabiliser action through a normal subgroup which acts
trivially on the relevant character set. -/
@[instance_reducible]
def blockStabilizerQuotientMulAction
    {A X BlockIndex : Type u} [Group A]
    [MulAction A X] [MulAction A BlockIndex]
    (block : BlockIndex)
    (N : Subgroup (MulAction.stabilizer A block)) [N.Normal]
    (hN : ∀ (n : N) (x : X),
      (((n : MulAction.stabilizer A block) : A) • x) = x) :
    MulAction ((MulAction.stabilizer A block) ⧸ N) X := by
  letI : MulAction (MulAction.stabilizer A block) X :=
    blockStabilizerMulAction block
  exact quotientMulActionOfTrivialSubgroup N hN

@[simp]
theorem blockStabilizerQuotientMulAction_mk_smul
    {A X BlockIndex : Type u} [Group A]
    [MulAction A X] [MulAction A BlockIndex]
    (block : BlockIndex)
    (N : Subgroup (MulAction.stabilizer A block)) [N.Normal]
    (hN : ∀ (n : N) (x : X),
      (((n : MulAction.stabilizer A block) : A) • x) = x)
    (a : MulAction.stabilizer A block) (x : X) :
    let _ : MulAction ((MulAction.stabilizer A block) ⧸ N) X :=
      blockStabilizerQuotientMulAction block N hN
    QuotientGroup.mk' N a • x = (a : A) • x := by
  dsimp only [blockStabilizerQuotientMulAction]
  exact quotientMulActionOfTrivialSubgroup_mk_smul N hN a x

/-- The descended action preserves the selected block fibre. -/
theorem blockStabilizerQuotient_blockStable
    {A X BlockIndex : Type u} [Group A]
    [MulAction A X] [MulAction A BlockIndex]
    (blockOf : X → BlockIndex)
    (blockOf_equivariant : ∀ (a : A) (x : X),
      blockOf (a • x) = a • blockOf x)
    (block : BlockIndex)
    (N : Subgroup (MulAction.stabilizer A block)) [N.Normal]
    (hN : ∀ (n : N) (x : X),
      (((n : MulAction.stabilizer A block) : A) • x) = x) :
    let _ : MulAction ((MulAction.stabilizer A block) ⧸ N) X :=
      blockStabilizerQuotientMulAction block N hN
    ∀ (q : (MulAction.stabilizer A block) ⧸ N) (x : X),
      blockOf x = block → blockOf (q • x) = block := by
  dsimp only
  letI : MulAction ((MulAction.stabilizer A block) ⧸ N) X :=
    blockStabilizerQuotientMulAction block N hN
  intro q x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N q
  rw [blockStabilizerQuotientMulAction_mk_smul]
  calc
    blockOf ((a : A) • x) = (a : A) • blockOf x :=
      blockOf_equivariant a x
    _ = (a : A) • block := congrArg ((a : A) • ·) hx
    _ = block := a.property

/-- Equivariance for the quotient of a literal block stabiliser gives the
usual stabiliser-equivariance on the block fibre.  Thus the notation
`Aut(G)_B / Inn(G)` is not treated as an unrelated abstract group action. -/
theorem stabilizerFibreEquivariant_of_quotientEquivariant
    {A X Y BlockIndex : Type u} [Group A]
    [MulAction A X] [MulAction A Y] [MulAction A BlockIndex]
    (blockX : X → BlockIndex) (blockY : Y → BlockIndex)
    (blockX_equivariant : ∀ (a : A) (x : X),
      blockX (a • x) = a • blockX x)
    (blockY_equivariant : ∀ (a : A) (y : Y),
      blockY (a • y) = a • blockY y)
    (block : BlockIndex)
    (N : Subgroup (MulAction.stabilizer A block)) [N.Normal]
    (hNX : ∀ (n : N) (x : X),
      (((n : MulAction.stabilizer A block) : A) • x) = x)
    (hNY : ∀ (n : N) (y : Y),
      (((n : MulAction.stabilizer A block) : A) • y) = y)
    (beta : Fibre blockX block ≃ Fibre blockY block) :
    let _ : MulAction ((MulAction.stabilizer A block) ⧸ N) X :=
      blockStabilizerQuotientMulAction block N hNX
    let _ : MulAction ((MulAction.stabilizer A block) ⧸ N) Y :=
      blockStabilizerQuotientMulAction block N hNY
    let _ : MulAction ((MulAction.stabilizer A block) ⧸ N)
        (Fibre blockX block) :=
      stableBlockFibreMulAction blockX block
        (blockStabilizerQuotient_blockStable
          blockX blockX_equivariant block N hNX)
    let _ : MulAction ((MulAction.stabilizer A block) ⧸ N)
        (Fibre blockY block) :=
      stableBlockFibreMulAction blockY block
        (blockStabilizerQuotient_blockStable
          blockY blockY_equivariant block N hNY)
    (∀ (q : (MulAction.stabilizer A block) ⧸ N)
      (x : Fibre blockX block), beta (q • x) = q • beta x) →
    ∀ (a : A) (ha : a • block = block) (x : Fibre blockX block),
      beta (stabilizerFibreEquiv blockX blockX_equivariant
        block a ha x) =
        stabilizerFibreEquiv blockY blockY_equivariant
          block a ha (beta x) := by
  dsimp only
  letI : MulAction ((MulAction.stabilizer A block) ⧸ N) X :=
    blockStabilizerQuotientMulAction block N hNX
  letI : MulAction ((MulAction.stabilizer A block) ⧸ N) Y :=
    blockStabilizerQuotientMulAction block N hNY
  let hstableX := blockStabilizerQuotient_blockStable
    blockX blockX_equivariant block N hNX
  let hstableY := blockStabilizerQuotient_blockStable
    blockY blockY_equivariant block N hNY
  letI : MulAction ((MulAction.stabilizer A block) ⧸ N)
      (Fibre blockX block) :=
    stableBlockFibreMulAction blockX block hstableX
  letI : MulAction ((MulAction.stabilizer A block) ⧸ N)
      (Fibre blockY block) :=
    stableBlockFibreMulAction blockY block hstableY
  intro hbeta a ha x
  let astab : MulAction.stabilizer A block := ⟨a, ha⟩
  let q : (MulAction.stabilizer A block) ⧸ N := QuotientGroup.mk' N astab
  calc
    beta (stabilizerFibreEquiv blockX blockX_equivariant block a ha x) =
        beta (q • x) := by
      apply congrArg beta
      apply Subtype.ext
      change a • x.1 = q • x.1
      rw [show q = QuotientGroup.mk' N astab from rfl,
        blockStabilizerQuotientMulAction_mk_smul]
    _ = q • beta x := hbeta q x
    _ = stabilizerFibreEquiv blockY blockY_equivariant
        block a ha (beta x) := by
      apply Subtype.ext
      change q • (beta x).1 = a • (beta x).1
      rw [show q = QuotientGroup.mk' N astab from rfl,
        blockStabilizerQuotientMulAction_mk_smul]

/-! ## The exact basic-set bridge on a literal block stabiliser -/

/-- The quotient action on the ordinary basic set, obtained from the literal
block stabiliser after deriving triviality of its inner subgroup. -/
@[instance_reducible]
def ordinaryBasicBlockQuotientAction
    {K G A BlockIndex : Type u}
    [Field K] [CharZero K] [Group G] [Group A]
    [MulAction A BlockIndex]
    (rho : A →* MulAut G)
    (B : OrdinaryBasicData (BlockIndex := BlockIndex) rho)
    (block : BlockIndex)
    (N : Subgroup (MulAction.stabilizer A block)) [N.Normal]
    (hinner : ∀ n : N, ∃ g : G,
      rho (((n : MulAction.stabilizer A block) : A)) = MulAut.conj g) :
    MulAction ((MulAction.stabilizer A block) ⧸ N)
      {chi : OrdinaryIrreducibleCharacter.Irr K G // B.predicate chi} := by
  letI : MulAction A
      {chi : OrdinaryIrreducibleCharacter.Irr K G // B.predicate chi} :=
    B.mulAction rho
  apply blockStabilizerQuotientMulAction block N
  intro n chi
  obtain ⟨g, hg⟩ := hinner n
  have hfixed : ordinaryAutomorphismAct rho
      (((n : MulAction.stabilizer A block) : A)) chi.1 = chi.1 := by
    unfold ordinaryAutomorphismAct
    rw [map_inv, hg]
    simpa only [map_inv] using OrdinaryAction.twist_conj chi.1 g⁻¹
  exact Subtype.ext hfixed

/-- The corresponding quotient action on actual function-valued Brauer
characters. -/
@[instance_reducible]
def brauerBlockQuotientAction
    {p : ℕ} {k K G A BlockIndex : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group A] [MulAction A BlockIndex]
    [Fintype BlockIndex]
    (iota : PrimeRegularRootEmbedding p k K G)
    (rho : A →* MulAut G)
    (block : BlockIndex)
    (N : Subgroup (MulAction.stabilizer A block)) [N.Normal]
    (hinner : ∀ n : N, ∃ g : G,
      rho (((n : MulAction.stabilizer A block) : A)) = MulAut.conj g) :
    MulAction ((MulAction.stabilizer A block) ⧸ N) (IBr iota) := by
  letI : MulAction A (IBr iota) :=
    EvenFieldAssumption53Relative.rightAutomorphismAction iota rho
  apply blockStabilizerQuotientMulAction block N
  intro n phi
  obtain ⟨g, hg⟩ := hinner n
  have hfixed : IrreducibleBrauerCharacter.twist iota phi
      (rho (((n : MulAction.stabilizer A block) : A))⁻¹) = phi := by
    rw [map_inv, hg]
    apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
    simpa only [map_inv] using
      PrimeRegularClassFunction.twist_conj phi.1 g⁻¹
  exact hfixed

set_option maxHeartbeats 800000 in

/-- Proposition 3.11's exact integral-basic-set argument, applied to the
quotient of the *literal* block stabiliser by its inner subgroup.

The theorem constructs the block-fibre bijection from exact `K₀` data.  The
only representation theoretic premises are the published integral basic set,
its block diagonal support and natural actions on exact `K₀`.  In
particular, no set-level bijection or Brauer stabiliser statement is an
input. -/
theorem actual_block_basic_set_bijection_relative
    {p : ℕ}
    {k K G A BlockIndex CyclicTarget : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group A] [Finite A]
    [MulAction A BlockIndex] [Fintype BlockIndex]
    [Group CyclicTarget] [IsCyclic CyclicTarget]
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (rho : A →* MulAut G)
    (ordinary : OrdinaryBasicData (BlockIndex := BlockIndex) rho)
    [Finite {chi : OrdinaryIrreducibleCharacter.Irr K G //
      ordinary.predicate chi}]
    {blockIdempotent : BlockIndex → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : BlockIndex)
    {decomposition : FDRepKZero K G →+ FDRepKZero k G}
    (basicSet : RestrictedIntegralBasicSetOnIBr iota hinj
      {chi : OrdinaryIrreducibleCharacter.Irr K G // ordinary.predicate chi}
      decomposition)
    (hblockDiagonal : BlockDiagonalLinearEquiv ordinary.blockOf
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      basicSet.linearEquiv)
    (hBrauerBlockEquivariant : ∀ (a : A) (phi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks
          (IrreducibleBrauerCharacter.twist iota phi (rho a⁻¹)) =
        a • irreducibleBrauerCharacterBlock iota hinj blocks phi)
    (innerSubgroup : Subgroup (MulAction.stabilizer A block))
    [innerSubgroup.Normal]
    (hinner : ∀ n : innerSubgroup, ∃ g : G,
      rho (((n : MulAction.stabilizer A block) : A)) = MulAut.conj g)
    (smallNormal :
      Subgroup (MulAction.stabilizer A block ⧸ innerSubgroup))
    [smallNormal.Normal]
    (hsmall : Nat.card smallNormal ≤ 2)
    (quotientEmbedding :
      ((MulAction.stabilizer A block ⧸ innerSubgroup) ⧸ smallNormal) →*
        CyclicTarget)
    (quotientEmbedding_injective : Function.Injective quotientEmbedding)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := 2)
      (A := MulAction.stabilizer A block ⧸ innerSubgroup))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := MulAction.stabilizer A block ⧸ innerSubgroup)) :
    let _ : MulAction A
        {chi : OrdinaryIrreducibleCharacter.Irr K G //
          ordinary.predicate chi} := ordinary.mulAction rho
    let _ : MulAction A (IBr iota) :=
      EvenFieldAssumption53Relative.rightAutomorphismAction iota rho
    let _ : MulAction (MulAction.stabilizer A block ⧸ innerSubgroup)
        {chi : OrdinaryIrreducibleCharacter.Irr K G //
          ordinary.predicate chi} :=
      ordinaryBasicBlockQuotientAction rho ordinary block innerSubgroup hinner
    let _ : MulAction (MulAction.stabilizer A block ⧸ innerSubgroup)
        (IBr iota) :=
      brauerBlockQuotientAction iota rho block innerSubgroup hinner
    ∀ (tensorFieldActions : LabelledKZeroActionData
        (A := MulAction.stabilizer A block ⧸ innerSubgroup)
        basicSet.toRestrictedIntegralBasicSet),
      DecompositionNatural
          (A := MulAction.stabilizer A block ⧸ innerSubgroup)
          decomposition tensorFieldActions.ordinaryAction
            tensorFieldActions.modularAction →
      ∃ beta : Fibre
          (irreducibleBrauerCharacterBlock iota hinj blocks) block ≃
          Fibre ordinary.blockOf block,
        ∀ (a : A) (ha : a • block = block)
          (phi : Fibre
            (irreducibleBrauerCharacterBlock iota hinj blocks) block),
          beta (stabilizerFibreEquiv
            (irreducibleBrauerCharacterBlock iota hinj blocks)
              hBrauerBlockEquivariant block a ha phi) =
            stabilizerFibreEquiv ordinary.blockOf ordinary.block_equivariant
              block a ha (beta phi) := by
  dsimp only
  letI : MulAction A
      {chi : OrdinaryIrreducibleCharacter.Irr K G //
        ordinary.predicate chi} := ordinary.mulAction rho
  letI : MulAction A (IBr iota) :=
    EvenFieldAssumption53Relative.rightAutomorphismAction iota rho
  have hOrdinaryInner : ∀ (n : innerSubgroup)
      (chi : {chi : OrdinaryIrreducibleCharacter.Irr K G //
        ordinary.predicate chi}),
      (((n : MulAction.stabilizer A block) : A) • chi) = chi := by
    intro n chi
    obtain ⟨g, hg⟩ := hinner n
    have hfixed : ordinaryAutomorphismAct rho
        (((n : MulAction.stabilizer A block) : A)) chi.1 = chi.1 := by
      unfold ordinaryAutomorphismAct
      rw [map_inv, hg]
      simpa only [map_inv] using OrdinaryAction.twist_conj chi.1 g⁻¹
    exact Subtype.ext hfixed
  have hBrauerInner : ∀ (n : innerSubgroup) (phi : IBr iota),
      (((n : MulAction.stabilizer A block) : A) • phi) = phi := by
    intro n phi
    obtain ⟨g, hg⟩ := hinner n
    have hfixed : IrreducibleBrauerCharacter.twist iota phi
        (rho (((n : MulAction.stabilizer A block) : A))⁻¹) = phi := by
      rw [map_inv, hg]
      apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
      simpa only [map_inv] using
        PrimeRegularClassFunction.twist_conj phi.1 g⁻¹
    exact hfixed
  letI : MulAction (MulAction.stabilizer A block ⧸ innerSubgroup)
      {chi : OrdinaryIrreducibleCharacter.Irr K G //
        ordinary.predicate chi} :=
    ordinaryBasicBlockQuotientAction rho ordinary block innerSubgroup hinner
  letI : MulAction (MulAction.stabilizer A block ⧸ innerSubgroup)
      (IBr iota) :=
    brauerBlockQuotientAction iota rho block innerSubgroup hinner
  intro tensorFieldActions reductionNatural
  have hOrdinaryStable := blockStabilizerQuotient_blockStable
    ordinary.blockOf ordinary.block_equivariant block innerSubgroup
      hOrdinaryInner
  have hBrauerStable := blockStabilizerQuotient_blockStable
    (irreducibleBrauerCharacterBlock iota hinj blocks)
      hBrauerBlockEquivariant block innerSubgroup hBrauerInner
  obtain ⟨beta, hbeta⟩ := proposition_3_11_relative
    iota hinj blocks block basicSet ordinary.blockOf hblockDiagonal
      tensorFieldActions reductionNatural hOrdinaryStable hBrauerStable
      smallNormal hsmall quotientEmbedding quotientEmbedding_injective
        conlon burnside
  refine ⟨beta, ?_⟩
  exact stabilizerFibreEquivariant_of_quotientEquivariant
    (irreducibleBrauerCharacterBlock iota hinj blocks) ordinary.blockOf
      hBrauerBlockEquivariant ordinary.block_equivariant block innerSubgroup
      hBrauerInner hOrdinaryInner beta hbeta

/-- Combine the bijections constructed on one block in each orbit into the
global equivariant bijection asserted in Lemma 3.12.  The input consists of
the representative-fibre family, not a global equivalence. -/
theorem actual_global_bijection_of_orbit_representatives
    {p : ℕ} {k K G A BlockIndex : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group A] [MulAction A BlockIndex]
    [Fintype BlockIndex]
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (rho : A →* MulAut G)
    (ordinary : OrdinaryBasicData (BlockIndex := BlockIndex) rho)
    {blockIdempotent : BlockIndex → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (hBrauerBlockEquivariant : ∀ (a : A) (phi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks
          (IrreducibleBrauerCharacter.twist iota phi (rho a⁻¹)) =
        a • irreducibleBrauerCharacterBlock iota hinj blocks phi) :
    let _ : MulAction A
        {chi : OrdinaryIrreducibleCharacter.Irr K G //
          ordinary.predicate chi} := ordinary.mulAction rho
    let _ : MulAction A (IBr iota) :=
      EvenFieldAssumption53Relative.rightAutomorphismAction iota rho
    ∀ F : RepresentativeEquivFamily
        (A := A)
        (irreducibleBrauerCharacterBlock iota hinj blocks)
        ordinary.blockOf hBrauerBlockEquivariant,
      ∃ beta : IBr iota ≃
          {chi : OrdinaryIrreducibleCharacter.Irr K G //
            ordinary.predicate chi},
        (∀ (a : A) (phi : IBr iota), beta (a • phi) = a • beta phi) ∧
        (∀ phi : IBr iota,
          ordinary.blockOf (beta phi) =
            irreducibleBrauerCharacterBlock iota hinj blocks phi) := by
  dsimp only
  letI : MulAction A
      {chi : OrdinaryIrreducibleCharacter.Irr K G //
        ordinary.predicate chi} := ordinary.mulAction rho
  letI : MulAction A (IBr iota) :=
    EvenFieldAssumption53Relative.rightAutomorphismAction iota rho
  intro F
  let beta := RepresentativeEquivFamily.globalEquiv
    (A := A)
    (blockX := irreducibleBrauerCharacterBlock iota hinj blocks)
    (blockY := ordinary.blockOf)
    (hblockX := hBrauerBlockEquivariant)
    (hblockY := ordinary.block_equivariant) F
  refine ⟨beta, ?_, ?_⟩
  · exact RepresentativeEquivFamily.globalEquiv_equivariant
      (A := A)
      (blockX := irreducibleBrauerCharacterBlock iota hinj blocks)
      (blockY := ordinary.blockOf)
      (hblockX := hBrauerBlockEquivariant)
      (hblockY := ordinary.block_equivariant) F
  · exact RepresentativeEquivFamily.globalEquiv_block_preserving
      (A := A)
      (blockX := irreducibleBrauerCharacterBlock iota hinj blocks)
      (blockY := ordinary.blockOf)
      (hblockX := hBrauerBlockEquivariant)
      (hblockY := ordinary.block_equivariant) F

/-! ## Transfer from the ordinary block fibre -/

/-- A bijection on one block fibre, equivariant under the stabiliser of that
block, suffices to transfer a stabiliser factorisation for the corresponding
ordinary character.  A global bijection is not needed: if a product fixes
the Brauer character, then that product stabilises its block, and the same
argument applies separately after the ordinary factorisation shows that
each factor fixes the ordinary character. -/
theorem blockFibre_factorization_of_stabilizer_equiv
    {D E X Y BlockIndex : Type u}
    [Group D] [Group E]
    [MulAction D X] [MulAction E X]
    [MulAction D Y] [MulAction E Y]
    (action : E →* MulAut D)
    [MulAction (D ⋊[action] E) X]
    [MulAction (D ⋊[action] E) Y]
    [MulAction (D ⋊[action] E) BlockIndex]
    (semidirectActionX : ∀ (a : D ⋊[action] E) (x : X),
      a • x = a.left • (a.right • x))
    (semidirectActionY : ∀ (a : D ⋊[action] E) (y : Y),
      a • y = a.left • (a.right • y))
    (blockX : X → BlockIndex) (blockY : Y → BlockIndex)
    (blockX_equivariant : ∀ (a : D ⋊[action] E) (x : X),
      blockX (a • x) = a • blockX x)
    (blockY_equivariant : ∀ (a : D ⋊[action] E) (y : Y),
      blockY (a • y) = a • blockY y)
    (block : BlockIndex)
    (beta : Fibre blockX block ≃ Fibre blockY block)
    (beta_stabilizer_equivariant :
      ∀ (a : D ⋊[action] E) (ha : a • block = block)
        (x : Fibre blockX block),
        beta (stabilizerFibreEquiv blockX blockX_equivariant
          block a ha x) =
          stabilizerFibreEquiv blockY blockY_equivariant
            block a ha (beta x))
    (x : Fibre blockX block)
    (ordinaryFactorization :
      ProductStabilizerFactorization (D := D) (E := E) (beta x).1) :
    ProductStabilizerFactorization (D := D) (E := E) x.1 := by
  intro d e
  constructor
  · intro hcombined
    let a : D ⋊[action] E := ⟨d, e⟩
    have hax : a • x.1 = x.1 := by
      rw [semidirectActionX]
      exact hcombined
    have hab : a • block = block := by
      calc
        a • block = a • blockX x.1 := congrArg (a • ·) x.2.symm
        _ = blockX (a • x.1) := (blockX_equivariant a x.1).symm
        _ = blockX x.1 := congrArg blockX hax
        _ = block := x.2
    have hbetaA := beta_stabilizer_equivariant a hab x
    have hordinaryCombined : a • (beta x).1 = (beta x).1 := by
      calc
        a • (beta x).1 =
            (stabilizerFibreEquiv blockY blockY_equivariant
              block a hab (beta x)).1 := rfl
        _ = (beta (stabilizerFibreEquiv blockX blockX_equivariant
              block a hab x)).1 := congrArg Subtype.val hbetaA.symm
        _ = (beta x).1 := by
          rw [show stabilizerFibreEquiv blockX blockX_equivariant
            block a hab x = x from Subtype.ext hax]
    have hordinaryProduct :
        d • (e • (beta x).1) = (beta x).1 := by
      rw [← semidirectActionY a]
      exact hordinaryCombined
    obtain ⟨hdOrdinary, heOrdinary⟩ :=
      (ordinaryFactorization d e).mp hordinaryProduct
    have hdb : (SemidirectProduct.inl d : D ⋊[action] E) • block = block := by
      calc
        (SemidirectProduct.inl d : D ⋊[action] E) • block =
            (SemidirectProduct.inl d : D ⋊[action] E) •
              blockY (beta x).1 := congrArg _ (beta x).2.symm
        _ = blockY ((SemidirectProduct.inl d : D ⋊[action] E) •
              (beta x).1) :=
          (blockY_equivariant (SemidirectProduct.inl d) (beta x).1).symm
        _ = blockY (beta x).1 := by
          rw [semidirectActionY]
          simpa using congrArg blockY hdOrdinary
        _ = block := (beta x).2
    have heb : (SemidirectProduct.inr e : D ⋊[action] E) • block = block := by
      calc
        (SemidirectProduct.inr e : D ⋊[action] E) • block =
            (SemidirectProduct.inr e : D ⋊[action] E) •
              blockY (beta x).1 := congrArg _ (beta x).2.symm
        _ = blockY ((SemidirectProduct.inr e : D ⋊[action] E) •
              (beta x).1) :=
          (blockY_equivariant (SemidirectProduct.inr e) (beta x).1).symm
        _ = blockY (beta x).1 := by
          rw [semidirectActionY]
          simpa using congrArg blockY heOrdinary
        _ = block := (beta x).2
    constructor
    · have hfibre :
          stabilizerFibreEquiv blockX blockX_equivariant block
              (SemidirectProduct.inl d) hdb x = x := by
        apply beta.injective
        calc
          beta (stabilizerFibreEquiv blockX blockX_equivariant block
              (SemidirectProduct.inl d) hdb x) =
              stabilizerFibreEquiv blockY blockY_equivariant block
                (SemidirectProduct.inl d) hdb (beta x) :=
            beta_stabilizer_equivariant (SemidirectProduct.inl d) hdb x
          _ = beta x := by
            apply Subtype.ext
            change (SemidirectProduct.inl d : D ⋊[action] E) •
              (beta x).1 = (beta x).1
            rw [semidirectActionY]
            simpa using hdOrdinary
      have hfull := congrArg Subtype.val hfibre
      change (SemidirectProduct.inl d : D ⋊[action] E) • x.1 = x.1 at hfull
      rw [semidirectActionX] at hfull
      simpa using hfull
    · have hfibre :
          stabilizerFibreEquiv blockX blockX_equivariant block
              (SemidirectProduct.inr e) heb x = x := by
        apply beta.injective
        calc
          beta (stabilizerFibreEquiv blockX blockX_equivariant block
              (SemidirectProduct.inr e) heb x) =
              stabilizerFibreEquiv blockY blockY_equivariant block
                (SemidirectProduct.inr e) heb (beta x) :=
            beta_stabilizer_equivariant (SemidirectProduct.inr e) heb x
          _ = beta x := by
            apply Subtype.ext
            change (SemidirectProduct.inr e : D ⋊[action] E) •
              (beta x).1 = (beta x).1
            rw [semidirectActionY]
            simpa using heOrdinary
      have hfull := congrArg Subtype.val hfibre
      change (SemidirectProduct.inr e : D ⋊[action] E) • x.1 = x.1 at hfull
      rw [semidirectActionX] at hfull
      simpa using hfull
  · rintro ⟨hd, he⟩
    rw [he, hd]

/-! ## Manuscript-specific composition -/

/-- The Lemma 3.12 stabiliser factorisation, relative to the cited integral
basic set and Li's ordinary-character factorisation.

Lean first constructs `beta` from the exact `K₀` bridge above.  It then
transfers the ordinary factorisation through that constructed bijection.
There is no Brauer factorisation or arbitrary set equivalence among the
premises. -/
theorem lemma_3_12_factorization_relative
    {p : ℕ}
    {k K G D E BlockIndex CyclicTarget : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G]
    [Group D] [Finite D] [Group E] [Finite E]
    [Fintype BlockIndex]
    [Group CyclicTarget] [IsCyclic CyclicTarget]
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (action : E →* MulAut D)
    (rhoD : D →* MulAut G) (rhoE : E →* MulAut G)
    (hcompat : AutomorphismSemidirectCompatible action rhoD rhoE)
    [MulAction (D ⋊[action] E) BlockIndex]
    (ordinary : OrdinaryBasicData (BlockIndex := BlockIndex)
      (semidirectAutomorphismHom action rhoD rhoE hcompat))
    [Finite {chi : OrdinaryIrreducibleCharacter.Irr K G //
      ordinary.predicate chi}]
    {blockIdempotent : BlockIndex → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : BlockIndex)
    {decomposition : FDRepKZero K G →+ FDRepKZero k G}
    (basicSet : RestrictedIntegralBasicSetOnIBr iota hinj
      {chi : OrdinaryIrreducibleCharacter.Irr K G // ordinary.predicate chi}
      decomposition)
    (hblockDiagonal : BlockDiagonalLinearEquiv ordinary.blockOf
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      basicSet.linearEquiv)
    (hBrauerBlockEquivariant : ∀ (a : D ⋊[action] E)
        (phi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks
          (IrreducibleBrauerCharacter.twist iota phi
            ((semidirectAutomorphismHom action rhoD rhoE hcompat) a⁻¹)) =
        a • irreducibleBrauerCharacterBlock iota hinj blocks phi)
    (innerSubgroup : Subgroup
      (MulAction.stabilizer (D ⋊[action] E) block))
    [innerSubgroup.Normal]
    (hinner : ∀ n : innerSubgroup, ∃ g : G,
      (semidirectAutomorphismHom action rhoD rhoE hcompat)
        (((n : MulAction.stabilizer (D ⋊[action] E) block) :
          D ⋊[action] E)) = MulAut.conj g)
    (smallNormal : Subgroup
      (MulAction.stabilizer (D ⋊[action] E) block ⧸ innerSubgroup))
    [smallNormal.Normal]
    (hsmall : Nat.card smallNormal ≤ 2)
    (quotientEmbedding :
      ((MulAction.stabilizer (D ⋊[action] E) block ⧸ innerSubgroup) ⧸
          smallNormal) →* CyclicTarget)
    (quotientEmbedding_injective : Function.Injective quotientEmbedding)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := 2)
      (A := MulAction.stabilizer (D ⋊[action] E) block ⧸
        innerSubgroup))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := MulAction.stabilizer (D ⋊[action] E) block ⧸
          innerSubgroup)) :
    let rhoA := semidirectAutomorphismHom action rhoD rhoE hcompat
    let _ : MulAction (D ⋊[action] E)
        {chi : OrdinaryIrreducibleCharacter.Irr K G //
          ordinary.predicate chi} := ordinary.mulAction rhoA
    let _ : MulAction (D ⋊[action] E) (IBr iota) :=
      EvenFieldAssumption53Relative.rightAutomorphismAction iota rhoA
    let _ : MulAction D
        {chi : OrdinaryIrreducibleCharacter.Irr K G //
          ordinary.predicate chi} := semidirectLeftRestrictedAction action
    let _ : MulAction E
        {chi : OrdinaryIrreducibleCharacter.Irr K G //
          ordinary.predicate chi} := semidirectRightRestrictedAction action
    let _ : MulAction D (IBr iota) := semidirectLeftRestrictedAction action
    let _ : MulAction E (IBr iota) := semidirectRightRestrictedAction action
    let _ : MulAction
        (MulAction.stabilizer (D ⋊[action] E) block ⧸ innerSubgroup)
        {chi : OrdinaryIrreducibleCharacter.Irr K G //
          ordinary.predicate chi} :=
      ordinaryBasicBlockQuotientAction rhoA ordinary block innerSubgroup hinner
    let _ : MulAction
        (MulAction.stabilizer (D ⋊[action] E) block ⧸ innerSubgroup)
        (IBr iota) :=
      brauerBlockQuotientAction iota rhoA block innerSubgroup hinner
    ∀ (tensorFieldActions : LabelledKZeroActionData
        (A := MulAction.stabilizer (D ⋊[action] E) block ⧸
          innerSubgroup)
        basicSet.toRestrictedIntegralBasicSet),
      DecompositionNatural
          (A := MulAction.stabilizer (D ⋊[action] E) block ⧸
            innerSubgroup)
          decomposition tensorFieldActions.ordinaryAction
            tensorFieldActions.modularAction →
      (∀ chi : Fibre ordinary.blockOf block,
        ProductStabilizerFactorization (D := D) (E := E) chi.1) →
      ∃ beta : Fibre
          (irreducibleBrauerCharacterBlock iota hinj blocks) block ≃
          Fibre ordinary.blockOf block,
        (∀ (a : D ⋊[action] E) (ha : a • block = block)
          (phi : Fibre
            (irreducibleBrauerCharacterBlock iota hinj blocks) block),
          beta (stabilizerFibreEquiv
            (irreducibleBrauerCharacterBlock iota hinj blocks)
              hBrauerBlockEquivariant block a ha phi) =
            stabilizerFibreEquiv ordinary.blockOf ordinary.block_equivariant
              block a ha (beta phi)) ∧
        ∀ phi : Fibre
          (irreducibleBrauerCharacterBlock iota hinj blocks) block,
          ProductStabilizerFactorization (D := D) (E := E) phi.1 := by
  dsimp only
  let rhoA := semidirectAutomorphismHom action rhoD rhoE hcompat
  letI : MulAction (D ⋊[action] E)
      {chi : OrdinaryIrreducibleCharacter.Irr K G //
        ordinary.predicate chi} := ordinary.mulAction rhoA
  letI : MulAction (D ⋊[action] E) (IBr iota) :=
    EvenFieldAssumption53Relative.rightAutomorphismAction iota rhoA
  letI : MulAction D
      {chi : OrdinaryIrreducibleCharacter.Irr K G //
        ordinary.predicate chi} := semidirectLeftRestrictedAction action
  letI : MulAction E
      {chi : OrdinaryIrreducibleCharacter.Irr K G //
        ordinary.predicate chi} := semidirectRightRestrictedAction action
  letI : MulAction D (IBr iota) := semidirectLeftRestrictedAction action
  letI : MulAction E (IBr iota) := semidirectRightRestrictedAction action
  letI : MulAction
      (MulAction.stabilizer (D ⋊[action] E) block ⧸ innerSubgroup)
      {chi : OrdinaryIrreducibleCharacter.Irr K G //
        ordinary.predicate chi} :=
    ordinaryBasicBlockQuotientAction rhoA ordinary block innerSubgroup hinner
  letI : MulAction
      (MulAction.stabilizer (D ⋊[action] E) block ⧸ innerSubgroup)
      (IBr iota) :=
    brauerBlockQuotientAction iota rhoA block innerSubgroup hinner
  intro tensorFieldActions reductionNatural ordinaryFactorization
  obtain ⟨beta, hbeta⟩ := actual_block_basic_set_bijection_relative
    iota hinj rhoA ordinary blocks block basicSet hblockDiagonal
      hBrauerBlockEquivariant innerSubgroup hinner smallNormal hsmall
      quotientEmbedding quotientEmbedding_injective conlon burnside
      tensorFieldActions reductionNatural
  refine ⟨beta, hbeta, ?_⟩
  intro phi
  exact blockFibre_factorization_of_stabilizer_equiv action
    (semidirectRestrictedAction_eq (X := IBr iota) action)
    (semidirectRestrictedAction_eq
      (X := {chi : OrdinaryIrreducibleCharacter.Irr K G //
        ordinary.predicate chi}) action)
    (irreducibleBrauerCharacterBlock iota hinj blocks) ordinary.blockOf
    hBrauerBlockEquivariant ordinary.block_equivariant block beta hbeta phi
    (ordinaryFactorization (beta phi))

/-- The final extension clause of Lemma 3.12.  The cyclicity of the relevant
stabiliser quotient and the extension are conclusions of the reused
Navarro bridge, not premises.  The remaining arguments identify the actual
copy of `G` and its function-valued Brauer character inside the stabiliser. -/
theorem lemma_3_12_cyclic_extension_relative
    {p : ℕ} {D E k K : Type u}
    [Group D] [Finite D] [Group E] [Finite E] [IsCyclic E]
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (iota : PrimeRegularRootEmbedding p k K D)
    (phi : E →* MulAut D)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u}
      p k)
    (psi : IBr iota) :
    let _ : MulAction D (IBr iota) :=
      EvenFieldAssumption53Relative.rightAutomorphismAction iota
        (MulAut.conj : D →* MulAut D)
    let _ : MulAction E (IBr iota) :=
      EvenFieldAssumption53Relative.rightAutomorphismAction iota phi
    let hsemidirect : SemidirectActionCompatible (X := IBr iota) phi :=
      EvenFieldAssumption53Relative.rightAutomorphismSemidirectCompatible
        iota phi
    let _ : MulAction (D ⋊[phi] E) (IBr iota) :=
      semidirectMulAction phi hsemidirect
    ∀ (iotaEmbedded : PrimeRegularRootEmbedding p k K
        (embeddedHStabilizer (phi := phi) psi))
      (groupEquiv : D ≃* embeddedHStabilizer (phi := phi) psi)
      (groupEquiv_canonical : ∀ d : D,
        (((groupEquiv d : embeddedHStabilizer (phi := phi) psi) :
          D ⋊[phi] E)) = SemidirectProduct.inl d)
      (transport : IBr iota ≃ IBr iotaEmbedded)
      (characterCompatible : ∀ (chi : IBr iota)
          (d : PrimeRegularElement (G := D) p),
        (transport chi).1 (PrimeRegularElement.equiv groupEquiv d) = chi.1 d),
      (∀ g : semidirectStabilizer (phi := phi) psi,
        IrreducibleBrauerCharacter.twist iotaEmbedded
            (transport psi) (MulAut.conjNormal g) =
          transport ((g : D ⋊[phi] E) • psi)) →
      ∃ W : FDRep k (embeddedHStabilizer (phi := phi) psi),
        Representation.IsIrreducible W.ρ ∧
        (transport psi).1 =
          Representation.brauerCharacterOfRootEmbedding W.ρ iotaEmbedded ∧
        Nonempty (Representation.Extension
          (embeddedHStabilizer (phi := phi) psi) W.ρ) := by
  exact EvenFieldAssumption53Relative.field_stabilizer_extension_relative
    iota phi principle psi

end ModularRep.PaperProofs.OddGFactorizationLemma312Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
