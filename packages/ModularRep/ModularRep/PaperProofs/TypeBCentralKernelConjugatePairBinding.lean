import ModularRep.PaperProofs.TypeBCentralKernelConjugateInertia
import ModularRep.PaperProofs.TypeBCentralKernelConjugateTripleTransport
import ModularRep.PaperProofs.TypeBCentralKernelConjugateCharacters
import ModularRep.PaperProofs.TypeBCentralKernelTripleCharacters
import ModularRep.PaperProofs.TypeBCentralKernelTripleRootFamily

/-!
# Actual pair data for simultaneous conjugation of block triples

The triple's ambient is the actual character inertia, its base is the
embedded normal group, and its local ambient is the actual raw-weight
inertia inside it. Both characters are constructed: the base character
is the original Brauer character on the embedded base; the local
character is the inflation of the reduction of the weight's own ordinary
local character. Only independently prescribed roots, their domain guards,
and literal specified block catalogues are data.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelConjugatePairBinding

open ModularRep CharacterWeight TypeBCentralKernelCarriers
open TypeBCentralKernelInertia TypeBCentralKernelTripleCarriers
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleRootFamily
open TypeBCentralKernelLocalReduction

universe u

variable {p : ℕ} {k K A : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A] (G : Subgroup A) [G.Normal]
  (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root)
  (W : CharacterWeight p K G)

/-- This package has no correspondence, projective representation or
block-triple field. All block allocations are literal primitive idempotents. -/
structure PairData (hUT : U G W ≤ T G root theta) where
  quotientRoot : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup)
  ambientRoot : PrimeRegularRootEmbedding p k K (T G root theta)
  blocks : PhysicalBlockFamily (k := k)
    (inside G (T G root theta)) (inside (U G W) (T G root theta))
  baseAgree : ∀ z : rootsOfUnity (primeRegularExponent p (inside G (T G root theta))) k,
    (TypeBCentralKernelTripleCharacters.baseRoot G root theta).lift ((z : kˣ) : k) =
      ambientRoot.lift ((z : kˣ) : k)
  localAgree : ∀ z : rootsOfUnity
      (primeRegularExponent p
        (localBase (inside G (T G root theta)) (inside (U G W) (T G root theta)))) k,
    (TypeBCentralKernelTripleCharacters.localRoot G root theta W hUT quotientRoot).lift
        ((z : kˣ) : k) = ambientRoot.lift ((z : kˣ) : k)

variable (hUT : U G W ≤ T G root theta) (D : PairData G root theta W hUT)

def tripleData : TripleData (p := p) (k := k) (K := K)
    (inside G (T G root theta)) (inside (U G W) (T G root theta)) :=
  withPrescribedRoots _ _ D.ambientRoot
    (TypeBCentralKernelTripleCharacters.baseRoot G root theta)
    (TypeBCentralKernelTripleCharacters.localRoot G root theta W hUT D.quotientRoot)
    D.baseAgree D.localAgree D.blocks

@[simp] theorem tripleData_ambientRoot :
    (tripleData G root theta W hUT D).ambientRoot = D.ambientRoot := rfl

@[simp] theorem tripleData_baseRoot :
    (tripleData G root theta W hUT D).base.iota =
      TypeBCentralKernelTripleCharacters.baseRoot G root theta := rfl

@[simp] theorem tripleData_localRoot :
    (tripleData G root theta W hUT D).localData.iota =
      TypeBCentralKernelTripleCharacters.localRoot G root theta W hUT D.quotientRoot := rfl

def baseCharacter : IBr (tripleData G root theta W hUT D).base.iota :=
  TypeBCentralKernelTripleCharacters.baseBrauer G root theta

theorem baseCharacter_value
    (x : PrimeRegularElement (G := inside G (T G root theta)) p) :
    (baseCharacter G root theta W hUT D).val x =
      theta.val (PrimeRegularElement.map
        (TypeBCentralKernelTripleCharacters.baseEquiv G root theta).symm.toMonoidHom x) := rfl

variable [IsAlgClosed K] (navarro : Navarro318Certificate p k K)

def localCharacter : IBr (tripleData G root theta W hUT D).localData.iota :=
  TypeBCentralKernelTripleCharacters.localBrauer G root theta W hUT D.quotientRoot
    (quotientReduction W D.quotientRoot navarro)

theorem localCharacter_reduction
    (x : PrimeRegularElement
      (G := localBase (inside G (T G root theta)) (inside (U G W) (T G root theta))) p) :
    W.localCharacter
        (TypeBCentralKernelWeightTransport.localMk W.subgroup
          ((TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT).symm x.val)) =
      (localCharacter G root theta W hUT D navarro).val x :=
  TypeBCentralKernelTripleCharacters.localBrauer_reduction G root theta W hUT D.quotientRoot
    (quotientReduction W D.quotientRoot navarro)
    (quotientReduction_value W D.quotientRoot navarro) x

/-- This abbreviation has a fixed literal meaning. Its characters are the
constructed functions above, not caller-selected predicate arguments. -/
abbrev PairWitness := BlockTripleWitness (tripleData G root theta W hUT D)
  (baseCharacter G root theta W hUT D) (localCharacter G root theta W hUT D navarro)

variable (a : A)

local notation "thetaA" => conjugationOp G a • theta
local notation "WA" => TypeBCentralKernelConjugateInertia.conjugateWeight G a W
local notation "hUTA" =>
  TypeBCentralKernelConjugateInertia.conjugate_raw_le_character G root theta W a hUT

/-- Simultaneously conjugate the actual pair, transporting the complete
literal witness. Only ambient/quotient root lift compatibility remains a
guard: both character comparisons and the actual local image are proved.
Every specified target block is fixed by the prescribed target catalogue. -/
theorem transfer_conjugate
    (DA : PairData G root thetaA WA hUTA)
    (ambientLifts : D.ambientRoot.lift = DA.ambientRoot.lift)
    (quotientLifts : DA.quotientRoot.lift = D.quotientRoot.lift)
    (certificate : TypeBCentralKernelButterflyCertificate.ButterflyCertificate p k K)
    (witness : PairWitness G root theta W hUT D navarro) :
    Nonempty (PairWitness G root thetaA WA hUTA DA navarro) := by
  refine TypeBCentralKernelConjugateTripleTransport.transfer_to_image
    (inside G (T G root theta)) (inside G (T G root thetaA))
    (inside (U G W) (T G root theta)) (inside (U G WA) (T G root thetaA))
    (TypeBCentralKernelConjugateInertia.characterInertiaEquiv G root theta a)
    (TypeBCentralKernelConjugateInertia.baseEquiv G root theta a)
    (TypeBCentralKernelConjugateInertia.base_anchor G root theta a)
    (TypeBCentralKernelConjugateInertia.localAmbient_image G root theta W a)
    (tripleData G root theta W hUT D) (tripleData G root thetaA WA hUTA DA)
    (baseCharacter G root theta W hUT D) (localCharacter G root theta W hUT D navarro)
    (baseCharacter G root thetaA WA hUTA DA) (localCharacter G root thetaA WA hUTA DA navarro)
    witness ?_ ?_ ?_ ?_ ?_ certificate
  · intro z _ _
    exact congrFun ambientLifts (z : k)
  · exact TypeBCentralKernelConjugateCharacters.baseRoot_lift_eq G root theta a
  · exact TypeBCentralKernelConjugateCharacters.localRoot_lift_eq G root theta a
      W hUT D.quotientRoot hUTA DA.quotientRoot quotientLifts
  · exact TypeBCentralKernelConjugateCharacters.baseBrauer_pullback G root theta a
  · intro x y hxy
    exact (TypeBCentralKernelConjugateCharacters.localBrauer_value_of_ambient
      G root theta a W hUT D.quotientRoot hUTA DA.quotientRoot
      (quotientReduction W D.quotientRoot navarro)
      (quotientReduction WA DA.quotientRoot navarro)
      (quotientReduction_value W D.quotientRoot navarro)
      (quotientReduction_value WA DA.quotientRoot navarro)
      x y (congrArg Subtype.val hxy).symm).symm

end ModularRep.PaperProofs.TypeBCentralKernelConjugatePairBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
