import ModularRep.PaperProofs.TypeBCharacteristicTwoScalarConjugation
import ModularRep.PaperProofs.TypeBCharacteristicTwoInduction
import ModularRep.PaperProofs.TypeBGreenPrincipalConstituentSource
import ModularRep.StabilizerFactorizationTransport

/-!
# The current all-prime Clifford stabilizer lemma

Current Lemma 4.6 assumes that theta extends to its full ambient inertia.
For every prime, modular Clifford theory and Gallagher's product formula
then imply that this inertia fixes the Clifford correspondent and its
induction. The finite constituent-orbit adjustment transfers the selected
constituent's stabilizer factorization. No characteristic-two twist-order
or effective-conjugation quotient hypothesis occurs below.

The external statements are the explicit Navarro restriction-orbit,
Clifford-induction and abelian Gallagher formulas (8.7, 8.9, 8.20), on the
same finite groups and prime regular roots. Their realization remains E2/U.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCurrentCliffordStabilizer

open ModularRep
open TypeBCharacteristicTwoCliffordKernel TypeBCharacteristicTwoCliffordApplication
open TypeBCharacteristicTwoInduction TypeBCharacteristicTwoScalarConjugation
open ModularRep.ManuscriptVerification.CharacteristicTwoClifford


universe u
variable {ell : ℕ} {G E k K : Type u}
variable [Group G] [Finite G] [Group E] [Finite E]
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]

/-- Every intermediate subgroup above the kernel of an abelian quotient
is normal; this is not an additional hypothesis of the current lemma. -/
theorem intermediate_normal (H N : Subgroup G) [N.Normal]
    [IsMulCommutative (G ⧸ N)] (hNH : N ≤ H) : H.Normal :=
  Subgroup.Normal.of_commutator_le G
    ((Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance).trans hNH)

@[instance_reducible] def ambientAction (H : Subgroup G) [H.Normal]
    (root : PrimeRegularRootEmbedding ell k K H) : MulAction G (IBr root) :=
  MulAction.compHom _ (inverseOppositeHom (MulAut.conjNormal (H := H)))

@[instance_reducible] def automorphismAction (H : Subgroup G)
    (root : PrimeRegularRootEmbedding ell k K H) (field : E →* MulAut G)
    (stable : ∀ e : E, ∀ x : G, x ∈ H ↔ field e x ∈ H) :
    MulAction E (IBr root) :=
  MulAction.compHom _ (inverseOppositeHom
    (TypeBLemma47LeviApplication.restrictAutomorphismHom H field stable))

theorem inner_fixes (H : Subgroup G) [H.Normal]
    (root : PrimeRegularRootEmbedding ell k K H) (h : H) (psi : IBr root) :
    letI := ambientAction H root; (h : G) • psi = psi := by
  change IrreducibleBrauerCharacter.twist root psi
    (MulAut.conjNormal (H := H) (h : G)⁻¹) = psi
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  have eq : MulAut.conjNormal (H := H) (h : G)⁻¹ = MulAut.conj h⁻¹ := by
    ext x
    rfl
  rw [eq]
  exact PrimeRegularClassFunction.twist_conj psi.1 h⁻¹

/-- The same finite nonnegative restriction expansion as the accepted
Brauer-occurrence predicate, along the actual base embedding. -/
def OccursAlong {A B : Type u} [Group A] [Finite A] [Group B] [Finite B]
    (j : B →* A) (rootA : PrimeRegularRootEmbedding ell k K A)
    (rootB : PrimeRegularRootEmbedding ell k K B)
    (psi : IBr rootA) (theta : IBr rootB) : Prop :=
  ∃ multiplicity : IBr rootB →₀ ℕ, multiplicity theta ≠ 0 ∧
    ∀ x : PrimeRegularElement (G := B) ell,
      psi.1 (PrimeRegularElement.map j x) =
        multiplicity.sum (fun eta m => (m : K) * eta.1 x)

def twistEquiv {A : Type u} [Group A] [Finite A]
    (root : PrimeRegularRootEmbedding ell k K A) (a : MulAut A) :
    IBr root ≃ IBr root where
  toFun psi := IrreducibleBrauerCharacter.twist root psi a
  invFun psi := IrreducibleBrauerCharacter.twist root psi a⁻¹
  left_inv psi := by
    change IrreducibleBrauerCharacter.twist root
      (IrreducibleBrauerCharacter.twist root psi a) a⁻¹ = psi
    rw [IrreducibleBrauerCharacter.twist_mul, mul_inv_cancel]
    exact IrreducibleBrauerCharacter.twist_refl root psi
  right_inv psi := by
    change IrreducibleBrauerCharacter.twist root
      (IrreducibleBrauerCharacter.twist root psi a⁻¹) a = psi
    rw [IrreducibleBrauerCharacter.twist_mul, inv_mul_cancel]
    exact IrreducibleBrauerCharacter.twist_refl root psi

/-- Reindexing the explicit multiplicities proves restriction naturality. -/
theorem occurs_twist {A B : Type u} [Group A] [Finite A] [Group B] [Finite B]
    (j : B →* A) (rootA : PrimeRegularRootEmbedding ell k K A)
    (rootB : PrimeRegularRootEmbedding ell k K B) (a : MulAut A) (b : MulAut B)
    (square : ∀ x : B, a (j x) = j (b x))
    {psi : IBr rootA} {theta : IBr rootB} (occurs : OccursAlong j rootA rootB psi theta) :
    OccursAlong j rootA rootB (IrreducibleBrauerCharacter.twist rootA psi a)
      (IrreducibleBrauerCharacter.twist rootB theta b) := by
  classical
  obtain ⟨m, hm, hvalue⟩ := occurs
  refine ⟨Finsupp.equivMapDomain (twistEquiv rootB b) m, ?_, ?_⟩
  · change Finsupp.equivMapDomain (twistEquiv rootB b) m ((twistEquiv rootB b) theta) ≠ 0
    simpa only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] using hm
  · intro x
    rw [Finsupp.sum_equivMapDomain]
    change psi.1 (PrimeRegularElement.map a.toMonoidHom (PrimeRegularElement.map j x)) =
      m.sum (fun t n => (n : K) * t.1 (PrimeRegularElement.map b.toMonoidHom x))
    have eq : PrimeRegularElement.map a.toMonoidHom (PrimeRegularElement.map j x) =
        PrimeRegularElement.map j (PrimeRegularElement.map b.toMonoidHom x) := by
      apply Subtype.ext
      exact square x.1
    rw [eq]
    exact hvalue (PrimeRegularElement.map b.toMonoidHom x)

/-- The actual actions, with the manuscript inverse convention, define
the stated semidirect action for every prime. -/
theorem semidirect_compatible (H : Subgroup G) [H.Normal]
    (root : PrimeRegularRootEmbedding ell k K H) (field : E →* MulAut G)
    (stable : ∀ e : E, ∀ x : G, x ∈ H ↔ field e x ∈ H) :
    letI := ambientAction H root;
    letI := automorphismAction H root field stable;
    Formalisation.SemidirectActionCompatible (X := IBr root) field := by
  intro e g psi
  change IrreducibleBrauerCharacter.twist root
      (IrreducibleBrauerCharacter.twist root psi (MulAut.conjNormal (H := H) g⁻¹))
      (TypeBLemma47LeviApplication.restrictAutomorphismHom H field stable e⁻¹) =
    IrreducibleBrauerCharacter.twist root
      (IrreducibleBrauerCharacter.twist root psi
        (TypeBLemma47LeviApplication.restrictAutomorphismHom H field stable e⁻¹))
      (MulAut.conjNormal (H := H) (field e g)⁻¹)
  rw [IrreducibleBrauerCharacter.twist_mul, IrreducibleBrauerCharacter.twist_mul]
  congr 1
  ext x
  simp [TypeBLemma47LeviApplication.restrictAutomorphismHom,
    TypeBLemma47LeviApplication.restrictAutomorphism]

section Main

variable (H N : Subgroup G) [H.Normal] [N.Normal] [IsMulCommutative (G ⧸ N)] (hNH : N ≤ H)

local instance fintypeH : Fintype H := Fintype.ofFinite _

variable (rootN : PrimeRegularRootEmbedding ell k K N) (theta : IBr rootN)
local instance actionN : MulAction G (IBr rootN) := ambientAction N rootN

abbrev AmbientInertia := MulAction.stabilizer G theta
abbrev Inertia := inertiaSubgroup H theta

def baseToH : N →* H := Subgroup.inclusion hNH

def baseToAmbient : N →* AmbientInertia N rootN theta where
  toFun x := ⟨x.1, inner_fixes N rootN x theta⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def inertiaToAmbient : Inertia H N rootN theta →* AmbientInertia N rootN theta where
  toFun x := ⟨x.1.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def baseToInertia : N →* Inertia H N rootN theta where
  toFun x := ⟨⟨x.1, hNH x.2⟩, inner_fixes N rootN x theta⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable (rootH : PrimeRegularRootEmbedding ell k K H)
variable (rootI : PrimeRegularRootEmbedding ell k K (Inertia H N rootN theta))
variable (rootA : PrimeRegularRootEmbedding ell k K (AmbientInertia N rootN theta))

/-- The exact current manuscript extension hypothesis. -/
structure AmbientExtension where
  character : IBr rootA
  restriction : PrimeRegularClassFunction.pullback (baseToAmbient N rootN theta)
    character.1 = theta.1

/-- Root agreement on just the roots used by the smaller group. -/
def RootsAgree {A B : Type u} [Group A] [Finite A] [Group B] [Finite B]
    (rA : PrimeRegularRootEmbedding ell k K A) (rB : PrimeRegularRootEmbedding ell k K B) : Prop :=
  ∀ z : rootsOfUnity (primeRegularExponent ell B) k,
    rB.lift (((z : kˣ) : k)) = rA.lift (((z : kˣ) : k))

/-- Exact E2/U specializations of Navarro 8.7, 8.9 and 8.20. The sources
supply only literal restriction, induction and quotient-linear product
formulas, not any invariant character or stabilizer conclusion. -/
structure Sources
    (rootsHN : RootsAgree rootH rootN) (rootsIN : RootsAgree rootI rootN)
    (rootsAN : RootsAgree rootA rootN) (rootsAI : RootsAgree rootA rootI)
    (rootsHI : RootsAgree rootH rootI)
    (coefficient : SpathCoefficientField ell k rootH.prime) : Prop where
  orbit : ∀ (psi : IBr rootH) (t u : IBr rootN),
    OccursAlong (baseToH H N hNH) rootH rootN psi t →
    OccursAlong (baseToH H N hNH) rootH rootN psi u →
      ∃ h : H, (h : G) • t = u
  correspondent : ∀ (psi : IBr rootH),
    OccursAlong (baseToH H N hNH) rootH rootN psi theta →
      ∃ eta : IBr rootI,
        OccursAlong (baseToInertia H N hNH rootN theta) rootI rootN eta theta ∧
        BrauerInduces (Inertia H N rootN theta) rootI rootH eta psi
  gallagher : ∀ (extension : AmbientExtension N rootN theta rootA) (eta : IBr rootI),
    OccursAlong (baseToInertia H N hNH rootN theta) rootI rootN eta theta →
      ∃ lambda : linearCharactersTrivialOn (k := k)
        (N.comap (H.subtype.comp (Inertia H N rootN theta).subtype)),
      eta.1 = PrimeRegularClassFunction.pointwiseMul (rootI.liftedLinearCharacter lambda.1)
        (PrimeRegularClassFunction.pullback (inertiaToAmbient H N rootN theta) extension.character.1)

/-- The Gallagher formula is fixed by the actual ambient inertia: its
first factor is quotient-linear, and its second is a restricted class
function from that same ambient inertia. -/
theorem gallagher_fixed (extension : AmbientExtension N rootN theta rootA)
    (eta : IBr rootI)
    (product : ∃ lambda : linearCharactersTrivialOn (k := k)
        (N.comap (H.subtype.comp (Inertia H N rootN theta).subtype)),
      eta.1 = PrimeRegularClassFunction.pointwiseMul (rootI.liftedLinearCharacter lambda.1)
        (PrimeRegularClassFunction.pullback (inertiaToAmbient H N rootN theta) extension.character.1))
    (a : AmbientInertia N rootN theta) :
    IrreducibleBrauerCharacter.twist rootI eta (conjugationOnInertiaSubgroupHom H theta a) = eta := by
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  obtain ⟨lambda, product⟩ := product
  have scalar : lambda.1.comp (conjugationOnInertiaSubgroupHom H theta a).toMonoidHom = lambda.1 := by
    apply linearCharacter_comp_eq_of_conjugation N
      (H.subtype.comp (Inertia H N rootN theta).subtype) (a : G)
      (conjugationOnInertiaSubgroupHom H theta a) (fun _ => rfl) lambda
  rw [product]
  have restricted : (PrimeRegularClassFunction.pullback (inertiaToAmbient H N rootN theta)
      extension.character.1).twist (conjugationOnInertiaSubgroupHom H theta a) =
      PrimeRegularClassFunction.pullback (inertiaToAmbient H N rootN theta) extension.character.1 := by
    apply PrimeRegularClassFunction.ext
    intro x
    exact extension.character.1.map_conj a
      (PrimeRegularElement.map (inertiaToAmbient H N rootN theta) x)
  calc
    _ = PrimeRegularClassFunction.pointwiseMul
        ((rootI.liftedLinearCharacter lambda.1).twist (conjugationOnInertiaSubgroupHom H theta a))
        ((PrimeRegularClassFunction.pullback (inertiaToAmbient H N rootN theta)
          extension.character.1).twist (conjugationOnInertiaSubgroupHom H theta a)) := by ext x; rfl
    _ = _ := by rw [PrimeRegularRootEmbedding.liftedLinearCharacter_twist, scalar, restricted]

variable {rootsHN : RootsAgree rootH rootN} {rootsIN : RootsAgree rootI rootN}
variable {rootsAN : RootsAgree rootA rootN} {rootsAI : RootsAgree rootA rootI}
variable {rootsHI : RootsAgree rootH rootI}
variable {coefficient : SpathCoefficientField ell k rootH.prime}
variable (sources : Sources H N hNH rootN theta rootH rootI rootA
  rootsHN rootsIN rootsAN rootsAI rootsHI coefficient)
variable (extension : AmbientExtension N rootN theta rootA)
variable (psi : IBr rootH)
variable (occurs : OccursAlong (baseToH H N hNH) rootH rootN psi theta)

include sources extension occurs

/-- Ambient-inertia fixation follows by the existing all-prime finite-sum
induction naturality, applied to the same selected Clifford correspondent. -/
theorem ambient_inertia_fixes (a : AmbientInertia N rootN theta) :
    letI := ambientAction H rootH; (a : G) • psi = psi := by
  obtain ⟨eta, above, induction⟩ := sources.correspondent psi occurs
  have fixed := gallagher_fixed H N rootN theta rootI rootA extension eta
    (sources.gallagher extension eta above) a⁻¹
  have natural := BrauerInduces.twist_of_square (Inertia H N rootN theta) rootI rootH
    (MulAut.conjNormal (H := H) (a : G)⁻¹)
    (conjugationOnInertiaSubgroupHom H theta a⁻¹) (fun _ => rfl) induction
  rw [fixed] at natural
  exact BrauerInduces.unique (Inertia H N rootN theta) rootI rootH natural induction

variable (field : E →* MulAut G)
variable (stableH : ∀ e : E, ∀ x : G, x ∈ H ↔ field e x ∈ H)
variable (stableN : ∀ e : E, ∀ x : G, x ∈ N ↔ field e x ∈ N)

local instance actionH : MulAction G (IBr rootH) := ambientAction H rootH



/-- Current Lemma 4.6, for every prime and arbitrary finite E. The only
stabilizer-factorization input is the one stated for the chosen theta. -/
theorem stabilizer_factorization
    (thetaFactor :
      letI := automorphismAction N rootN field stableN;
      ProductStabilizerFactorization (A := G) (E := E) theta) :
    letI := automorphismAction H rootH field stableH;
    ProductStabilizerFactorization (A := G) (E := E) psi := by
  letI := automorphismAction H rootH field stableH
  letI := automorphismAction N rootN field stableN
  have constituents : CliffordConstituentOrbit (E := E) H.subtype psi theta := by
    refine ⟨OccursAlong (baseToH H N hNH) rootH rootN, occurs, ?_, ?_, sources.orbit psi⟩
    · intro a chi t h
      exact occurs_twist (baseToH H N hNH) rootH rootN
        (MulAut.conjNormal (H := H) a⁻¹) (MulAut.conjNormal (H := N) a⁻¹)
        (fun _ => rfl) h
    · intro e chi t h
      exact occurs_twist (baseToH H N hNH) rootH rootN
        (TypeBLemma47LeviApplication.restrictAutomorphismHom H field stableH e⁻¹)
        (TypeBLemma47LeviApplication.restrictAutomorphismHom N field stableN e⁻¹)
        (fun _ => rfl) h
  intro g e
  constructor
  · intro fixed
    obtain ⟨h, adjusted⟩ := adjust_to_fix_constituent H.subtype psi theta constituents fixed
    have factors := (thetaFactor ((h : G) * g) e).mp adjusted
    have fixedAdjusted := ambient_inertia_fixes H N hNH rootN theta rootH rootI rootA
      sources extension psi occurs ⟨(h : G) * g, factors.1⟩
    have fixedG : g • psi = psi := by
      simpa only [mul_smul, inner_fixes H rootH] using fixedAdjusted
    have fixedE : e • psi = psi := (MulAction.injective g) (fixed.trans fixedG.symm)
    exact ⟨fixedG, fixedE⟩
  · rintro ⟨hg, he⟩
    rw [he, hg]

end Main

/-- Exact current Lemma 4.6 in its semidirect-stabilizer form. Normality
of H is derived before the literal source packet is instantiated; the
finite group E is arbitrary. Every prime is the actual root prime ell. -/
theorem lemma46 (H N : Subgroup G) [N.Normal]
    [IsMulCommutative (G ⧸ N)] (hNH : N ≤ H) :
    letI := intermediate_normal H N hNH;
    ∀ (rootN : PrimeRegularRootEmbedding ell k K N) (theta : IBr rootN)
      (rootH : PrimeRegularRootEmbedding ell k K H)
      (rootI : PrimeRegularRootEmbedding ell k K (Inertia H N rootN theta))
      (rootA : PrimeRegularRootEmbedding ell k K (AmbientInertia N rootN theta))
      (rootsHN : RootsAgree rootH rootN) (rootsIN : RootsAgree rootI rootN)
      (rootsAN : RootsAgree rootA rootN) (rootsAI : RootsAgree rootA rootI)
      (rootsHI : RootsAgree rootH rootI)
      (coefficient : SpathCoefficientField ell k rootH.prime)
      (sources : Sources H N hNH rootN theta rootH rootI rootA
        rootsHN rootsIN rootsAN rootsAI rootsHI coefficient)
      (extension : AmbientExtension N rootN theta rootA)
      (psi : IBr rootH)
      (occurs : OccursAlong (baseToH H N hNH) rootH rootN psi theta)
      (field : E →* MulAut G)
      (stableH : ∀ e : E, ∀ x : G, x ∈ H ↔ field e x ∈ H)
      (stableN : ∀ e : E, ∀ x : G, x ∈ N ↔ field e x ∈ N),
    letI := ambientAction N rootN;
    letI := ambientAction H rootH;
    letI := automorphismAction N rootN field stableN;
    letI := automorphismAction H rootH field stableH;
    Formalisation.SemidirectStabilizerFactors field
      (semidirect_compatible N rootN field stableN) theta →
    Formalisation.SemidirectStabilizerFactors field
      (semidirect_compatible H rootH field stableH) psi := by
  letI := intermediate_normal H N hNH
  intro rootN theta rootH rootI rootA rootsHN rootsIN rootsAN rootsAI rootsHI
    coefficient sources extension psi occurs field stableH stableN
  letI := ambientAction N rootN
  letI := ambientAction H rootH
  letI := automorphismAction N rootN field stableN
  letI := automorphismAction H rootH field stableH
  intro thetaFactor
  have product : ProductStabilizerFactorization (A := G) (E := E) theta :=
    fun g e => thetaFactor ⟨g, e⟩
  have result := stabilizer_factorization H N hNH rootN theta rootH rootI rootA
    sources extension psi occurs field stableH stableN product
  intro a
  exact result a.left a.right

end ModularRep.PaperProofs.TypeBCurrentCliffordStabilizer




/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
