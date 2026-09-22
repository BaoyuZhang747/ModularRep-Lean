import ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverExplicitHypotheses
import ModularRep.PaperProofs.EvenFieldFLZSourceConditions
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource

/-!
# Fixed source gate for Feng--Li--Zhang, Theorem 3.18

This module is the first application boundary for Feng--Li--Zhang, Theorem
3.18, in the centreless self-cover case used in manuscript Lemma 2.10.  It
does not prove the cited theorem.  Instead, it gives that E2 input a fixed
source-shaped domain and codomain.

The literal Definition 3.5 problem uses
`Gamma = H ⋊ E` and the homomorphism `semidirectToMulAut field`.  Thus the
acting group is the full semidirect automorphism carrier from clause (i), not
the outer factor `E`.  Kernel lemmas identify its canonical right action with
the semidirect actions in clause (ii).  From the bijectivity field in
`StructuralSource`, Lean constructs an actual equivalence from `Gamma` to the
stabiliser of the selected block in `Aut(H)`.

`SelfCoverSourceIdentification` owns the one concrete universal `p'`-cover
used in the ambient application.  Its remaining source assumptions say that
`H` is a finite nonabelian simple group at a prime dividing its order and is
its own full universal central cover.  The full and `p'`-cover conditions are
deliberately distinct.  Centrelessness, bijectivity of the `p'`-cover quotient,
the inverse quotient equivalence, and its compatibility with the quotient map
are then kernel consequences.  Primality of `p` is derived from `CharP k p`
and divisibility by the nonzero order of `H`.  The Definition 3.5 semantics
and output remain cover-free.  Matching `FLZSourceSemantics` with the
modular-character-triple relation in the paper remains U/E2.

The sole theorem-application field is `FLZ318Source.applyTheorem318`.  One
`FLZ318Source` owns the typed clause-(iii) source operations and their
self-cover adapters.  Its theorem operation consumes a completed hypothesis
package indexed by those operations, their adapters, and the structural
source.  The package stores only the genuine root inputs, and its full theorem
hypotheses are computed by the canonical cyclic-endgame builder.  The
operation then returns the fixed `Definition35IBAWBijection`
carrier.  This is the composite source consequence: Theorem 3.18 concludes
BAW-goodness, and the discussion following equation (3.17) passes
BAW-goodness to the existence of an iBAW-bijection.  Lean does not define or
prove BAW-goodness here.

The published theorem does not imply equation (3.17), whose converse to
Definition 3.5(ii) is explicitly said to fail in general.  Accordingly no
declaration in this module constructs an `Equation317Witness` from Theorem
3.18.  `definition35IBAWBijection_of_theorem318` exposes only the accurate
Definition 3.5 endpoint.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate

open ModularRep
open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverExplicitHypotheses
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (field : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)

omit [Fintype H] [Finite E] [IsCyclic E] in
theorem semidirectRightAction_smul_eq
    {X : Type u} [MulAction (MulAut H)ᵐᵒᵖ X]
    (g : H ⋊[field] E) (x : X) :
    let _ : MulAction H X :=
      rightAutomorphismAction (MulAut.conj : H →* MulAut H)
    let _ : MulAction E X := rightAutomorphismAction field
    let _ : MulAction (H ⋊[field] E) X :=
      semidirectMulAction field
        (rightAutomorphismSemidirectCompatible (X := X) field)
    g • x = inverseOpHom (semidirectToMulAut field) g • x := by
  dsimp only
  let _ : MulAction H X :=
    rightAutomorphismAction (MulAut.conj : H →* MulAut H)
  let _ : MulAction E X := rightAutomorphismAction field
  change inverseOpHom (MulAut.conj : H →* MulAut H) g.left •
      (inverseOpHom field g.right • x) = _
  have hop :
      inverseOpHom (semidirectToMulAut field) g =
        inverseOpHom (MulAut.conj : H →* MulAut H) g.left *
          inverseOpHom field g.right := by
    rw [← SemidirectProduct.inl_left_mul_inr_right g, map_mul]
    simp [inverseOpHom]
  rw [← mul_smul, hop]

omit [Fintype H] [Finite E] [IsCyclic E] [Fintype ι] in
theorem selfCoverBlockSemidirect_smul_eq (g : H ⋊[field] E) :
    let _ : MulAction H ι := SelfCoverBlockHAction
    let _ : MulAction E ι := SelfCoverBlockEAction field
    let _ : MulAction (H ⋊[field] E) ι :=
      semidirectMulAction field
        (rightAutomorphismSemidirectCompatible (X := ι) field)
    g • block =
      inverseOpHom (semidirectToMulAut field) g • block := by
  exact semidirectRightAction_smul_eq field g block

variable (T : FibreTransportSource iota hinj blocks field block)
variable (localReduction : ∀ w : LiteralWeightFibre blockSource block,
  SelectedLocalReductionSource blockSource block w)
variable (structural : StructuralSource field)
variable (endgame : CyclicEndgameData
  (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
  (blockSource := blockSource) (block := block) T
  (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
  localReduction)

abbrev ExplicitPackage
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block) :=
  ExplicitSelfCoverHypotheses iota hinj blocks field blockSource block T
    localReduction operations endgame

/-- The root inputs from which the complete Theorem 3.18 hypothesis package is
canonically combined.  The type is indexed by the exact structural source,
clause-(iii) operations, and adapters owned by the theorem source.

It deliberately does not store a raw `ExplicitSelfCoverHypotheses`.  Its
constructor is private for ordinary API use, and even a client with access to
private declarations can provide only the two source root families.
`CompletedExplicitPackage.hypotheses` below always runs the canonical
construction. -/
structure CompletedExplicitPackage
    (structural : StructuralSource field)
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (operationAdapters : ClauseIIISelfCoverAdapters
      iota hinj blocks blockSource block operations) where
  private mk ::
  globalRootInputs : ∀ psi : BrauerFibre iota hinj blocks block,
    ClauseIVAGlobalRootInput
      iota hinj blocks field blockSource block T psi
  localRootInputs : ∀ psi : BrauerFibre iota hinj blocks block,
    ClauseIVBLocalRootInput
      (field := field) (blockSource := blockSource) (block := block)
      (localReduction := localReduction)
        (endgame.omega.toEquiv psi)

/-- Canonically combine the full hypotheses from a completed root package. -/
def CompletedExplicitPackage.hypotheses
    {structural : StructuralSource field}
    {operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block}
    {operationAdapters : ClauseIIISelfCoverAdapters
      iota hinj blocks blockSource block operations}
    (package : CompletedExplicitPackage iota hinj blocks field blockSource
      block T localReduction endgame structural operations operationAdapters) :
    ExplicitPackage iota hinj blocks field blockSource block T localReduction
      endgame operations :=
  explicitSelfCoverHypotheses_of_cyclicEndgame
    iota hinj blocks field blockSource block T localReduction structural
      operations operationAdapters endgame package.globalRootInputs
        package.localRootInputs

/-- Package the two root-input families for canonical hypothesis construction. -/
def completedExplicitPackage_of_cyclicEndgame
    (structural : StructuralSource field)
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (operationAdapters : ClauseIIISelfCoverAdapters
      iota hinj blocks blockSource block operations)
    (cyclicEndgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction)
    (globalRootInputs : ∀ psi : BrauerFibre iota hinj blocks block,
      ClauseIVAGlobalRootInput
        iota hinj blocks field blockSource block T psi)
    (localRootInputs : ∀ psi : BrauerFibre iota hinj blocks block,
      ClauseIVBLocalRootInput
        (field := field) (blockSource := blockSource) (block := block)
        (localReduction := localReduction)
          (cyclicEndgame.omega.toEquiv psi)) :
    CompletedExplicitPackage iota hinj blocks field blockSource block T
      localReduction cyclicEndgame structural operations operationAdapters :=
  { globalRootInputs := globalRootInputs
    localRootInputs := localRootInputs }

include iota hinj blocks blockSource T in
theorem canonicalGammaBlock_fixed (g : H ⋊[field] E) :
    inverseOpHom (semidirectToMulAut field) g • block = block := by
  rw [← selfCoverBlockSemidirect_smul_eq field block g]
  exact singletonBlock_fixed iota hinj blocks field blockSource block T g

include iota hinj blocks field blockSource block T localReduction in
def selfCoverDefinition35Problem : Definition35Problem where
  p := p
  k := k
  K := K
  H := H
  Gamma := H ⋊[field] E
  Block := ι
  blockIdempotent := blockIdempotent
  iota := iota
  irreducibleBrauerInjective := hinj
  blocks := blocks
  blockSource := blockSource
  block := block
  gamma := semidirectToMulAut field
  gammaBlock_fixed := canonicalGammaBlock_fixed
    (iota := iota) (hinj := hinj) (blocks := blocks) (field := field)
    (blockSource := blockSource) (block := block) (T := T)
  brauerBlock_transport := T.brauerBlock_transport
  localReduction := localReduction

omit [Fintype H] [Fintype ι] in
theorem rightBlockStabilizer_bijective
    {A : Type u} [Group A]
    (rho : A →* MulAut H) (hbij : Function.Bijective rho)
    (hfixed : ∀ a : A, inverseOpHom rho a • block = block) :
    Function.Bijective (rightBlockStabilizer rho block hfixed) := by
  constructor
  · intro a b hab
    apply inv_injective
    apply hbij.1
    have hop := congrArg Subtype.val hab
    have hunop := congrArg MulOpposite.unop hop
    simpa [rightBlockStabilizer, inverseOpHom] using hunop
  · intro alpha
    obtain ⟨a, ha⟩ := hbij.2 ((MulOpposite.unop alpha.1)⁻¹)
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change inverseOpHom rho a = alpha.1
    apply MulOpposite.unop_injective
    simp [inverseOpHom, ha]

def selfCoverAutomorphismStabilizerAdapter
    :
    Definition35AutomorphismStabilizerAdapter
      (selfCoverDefinition35Problem iota hinj blocks field blockSource block T
        localReduction) := by
  let P := selfCoverDefinition35Problem iota hinj blocks field blockSource block T
    localReduction
  exact {
    equiv := MulEquiv.ofBijective
      (rightBlockStabilizer P.gamma P.block P.gammaBlock_fixed)
      (rightBlockStabilizer_bijective
        (rho := P.gamma) (block := P.block)
        (hbij := structural.automorphismMap_bijective)
        (hfixed := P.gammaBlock_fixed))
    equiv_coe := fun _ ↦ rfl }

@[instance_reducible]
def selfCoverBrauerSemidirectAction :
    MulAction (H ⋊[field] E) (BrauerFibre iota hinj blocks block) := by
  let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (FibreTransportSource.innerBlock_fixed
        (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks field block
      T.outerBlock_fixed T.brauerBlock_transport
  exact semidirectMulAction field
    (FibreTransportSource.brauerFibre_compatible
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) (T := T))

@[instance_reducible]
def selfCoverWeightSemidirectAction :
    MulAction (H ⋊[field] E) (WeightFibre blockSource block) := by
  let _ : MulAction H (WeightFibre blockSource block) :=
    rightWeightFibreMulAction
      (MulAut.conj : H →* MulAut H) blockSource block
      (FibreTransportSource.innerBlock_fixed
        (blockSource := blockSource) (block := block))
  let _ : MulAction E (WeightFibre blockSource block) :=
    rightWeightFibreMulAction field blockSource block T.outerBlock_fixed
  exact semidirectMulAction field
    (FibreTransportSource.weightFibre_compatible
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) (T := T))

theorem definition35BrauerAction_smul_eq_clauseII
    (g : H ⋊[field] E) (psi : BrauerFibre iota hinj blocks block) :
    (definition35BrauerAction
      (selfCoverDefinition35Problem iota hinj blocks field blockSource block T
        localReduction)).smul g psi =
      (selfCoverBrauerSemidirectAction iota hinj blocks field blockSource
        block T).smul g psi := by
  apply Subtype.ext
  change inverseOpHom (semidirectToMulAut field) g • psi.1 =
    inverseOpHom (MulAut.conj : H →* MulAut H) g.left •
      (inverseOpHom field g.right • psi.1)
  exact (semidirectRightAction_smul_eq field g psi.1).symm

theorem definition35WeightAction_smul_eq_clauseII
    (g : H ⋊[field] E) (w : WeightFibre blockSource block) :
    (definition35WeightAction
      (selfCoverDefinition35Problem iota hinj blocks field blockSource block T
        localReduction)).smul g w =
      (selfCoverWeightSemidirectAction iota hinj blocks field blockSource
        block T).smul g w := by
  apply Subtype.ext
  change inverseOpHom (semidirectToMulAut field) g • w.1 =
    inverseOpHom (MulAut.conj : H →* MulAut H) g.left •
      (inverseOpHom field g.right • w.1)
  exact (semidirectRightAction_smul_eq field g w.1).symm

abbrev SelfCoverProblem :=
  selfCoverDefinition35Problem iota hinj blocks field blockSource block T
    localReduction

abbrev SelfCoverAutomorphisms :=
  selfCoverAutomorphismStabilizerAdapter iota hinj blocks field blockSource
    block T localReduction structural

omit [IsAlgClosed k] in
include k in
theorem coefficientPrime_of_divides_card
    (hdiv : p ∣ Fintype.card H) : Nat.Prime p := by
  apply CharP.char_prime_of_ne_zero k
  intro hp
  subst p
  exact Fintype.card_ne_zero (zero_dvd_iff.mp hdiv)

/-- The ambient cover and source identifications used in the self-cover
application of the cited theorem. -/
structure SelfCoverSourceIdentification where
  ellPrimeCover : EllPrimeCoverSource p H
  simple : IsSimpleGroup H
  nonabelian : ¬ IsMulCommutative H
  coefficientPrime_divides_card : p ∣ Fintype.card H
  ownUniversalCover : IsOwnUniversalCover H

omit [IsAlgClosed k] in
include k in
theorem SelfCoverSourceIdentification.coefficientPrime
    (identification : SelfCoverSourceIdentification (p := p) (H := H)) :
    Nat.Prime p :=
  coefficientPrime_of_divides_card
    (k := k) identification.coefficientPrime_divides_card

theorem SelfCoverSourceIdentification.center_eq_bot
    (identification : SelfCoverSourceIdentification (p := p) (H := H)) :
    Subgroup.center H = ⊥ := by
  letI : IsSimpleGroup H := identification.simple
  have hnormal : (Subgroup.center H).Normal := inferInstance
  rcases hnormal.eq_bot_or_eq_top with hcenter | hcenter
  · exact hcenter
  · exact (identification.nonabelian
      (Subgroup.center_eq_top_iff.mp hcenter)).elim

theorem SelfCoverSourceIdentification.ellPrimeCover_quotient_bijective
    (identification : SelfCoverSourceIdentification (p := p) (H := H)) :
    Function.Bijective identification.ellPrimeCover.quotient := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_,
    identification.ellPrimeCover.quotient_surjective⟩
  rw [identification.ellPrimeCover.quotient_kernel,
    identification.center_eq_bot]

/-- The inverse of the centreless `p'`-cover quotient. -/
def SelfCoverSourceIdentification.coverToSelf
    (identification : SelfCoverSourceIdentification (p := p) (H := H)) :
    identification.ellPrimeCover.S ≃* H :=
  (MulEquiv.ofBijective identification.ellPrimeCover.quotient
    identification.ellPrimeCover_quotient_bijective).symm

theorem SelfCoverSourceIdentification.coverToSelf_comp
    (identification : SelfCoverSourceIdentification (p := p) (H := H)) :
    identification.coverToSelf.toMonoidHom.comp
        identification.ellPrimeCover.quotient =
      MonoidHom.id H := by
  ext h
  change identification.coverToSelf
      (identification.ellPrimeCover.quotient h) = h
  exact (MulEquiv.ofBijective identification.ellPrimeCover.quotient
    identification.ellPrimeCover_quotient_bijective).symm_apply_apply h

/-- The sole E2 interface for Feng--Li--Zhang, Theorem 3.18, in the
centreless self-cover specialisation.

One source owns the clause-(iii) operation model and its self-cover adapters.
The theorem operation consumes the complete explicit hypothesis package built
from that same model and the narrow source identification.  Its fixed output
is only the Definition 3.5 iBAW-bijection consequence of the theorem's
BAW-good conclusion; it contains no equation-(3.17) relation. -/
structure FLZ318Source
    (source : FLZSourceSemantics
      (SelfCoverProblem iota hinj blocks field blockSource block T
        localReduction)
      (SelfCoverAutomorphisms iota hinj blocks field blockSource block T
        localReduction structural)) where
  operations : ClauseIIISourceOperations
    iota hinj blocks blockSource block
  operationAdapters : ClauseIIISelfCoverAdapters
    iota hinj blocks blockSource block operations
  applyTheorem318 :
    CompletedExplicitPackage iota hinj blocks field blockSource block T
        localReduction endgame structural operations operationAdapters →
      SelfCoverSourceIdentification (p := p) (H := H) →
        Nonempty (Definition35IBAWBijection
          (SelfCoverProblem iota hinj blocks field blockSource block T
            localReduction)
          (SelfCoverAutomorphisms iota hinj blocks field blockSource block T
            localReduction structural)
          source)

/-- Apply the fixed E2 theorem interface and expose only its Definition 3.5
iBAW-bijection consequence. -/
theorem definition35IBAWBijection_of_theorem318
    (source : FLZSourceSemantics
      (SelfCoverProblem iota hinj blocks field blockSource block T
        localReduction)
      (SelfCoverAutomorphisms iota hinj blocks field blockSource block T
        localReduction structural))
    (theorem318 : FLZ318Source iota hinj blocks field blockSource block T
      localReduction structural endgame source)
    (hypotheses : CompletedExplicitPackage iota hinj blocks field blockSource
      block T localReduction endgame structural theorem318.operations
        theorem318.operationAdapters)
    (identification : SelfCoverSourceIdentification (p := p) (H := H)) :
    Nonempty (Definition35IBAWBijection
      (SelfCoverProblem iota hinj blocks field blockSource block T
        localReduction)
      (SelfCoverAutomorphisms iota hinj blocks field blockSource block T
        localReduction structural)
      source) :=
  theorem318.applyTheorem318 hypotheses identification

end ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
