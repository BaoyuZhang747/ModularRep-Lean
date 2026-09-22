import ModularRep.EvenUnipotentIBAW
import ModularRep.IBrBlockBasicSetBridge

/-!
# Exact-`K₀` construction of the even-field unipotent block witness

This file connects the actual function-valued `IBr` block fibre constructed
in `IBrBlockBasicSetBridge` to the block witness used for manuscript
Proposition 3.8.  In particular, equivariance of the decomposition matrix is
not an input here: it is derived from stable-reduction naturality, the exact
integral-basic-set restriction, and the two mark theorems.

The remaining hypotheses identify the canonical automorphism action with the
action in the manuscript context.  They also supply the final extension,
intermediate-block, character-triple, and normalisation clauses separately.
Although no single hypothesis is named BAW-good or iBAW, these supplied final
clauses receive no kernel-proof credit.  The theorem's genuine deduction is
the construction and equivariance of the literal block-fibre equivalence.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.ManuscriptVerification.EvenUnipotentIBrBlockAssembly

open Formalisation
open Formalisation.IBAW
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.IntegralBasicSetBridge
open ModularRep.ManuscriptVerification.EvenUnipotentAssembly
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.ManuscriptVerification.EvenUnipotentIBAW

universe u

variable {p : ℕ}
variable {K O k H E ι R S Weight DZ Basic GenericWeight : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k p] [IsAlgClosed k]
variable [Group H] [Finite H]
variable [Group E] [Finite E]
variable [Fintype ι]

/-- Identify the block fibre in an abstract iBAW context with the literal
function-valued `IBr` fibre obtained from the block idempotents. -/
def contextBrauerFibreEquiv
    (iota : PrimeRegularRootEmbedding p k K H)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[H]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    [MulAction E ι] [MulAction E R] [MulAction E S]
    [MulAction E (IBr iota)] [MulAction E Weight] [MulAction E DZ]
    (C : Context E ι R S (IBr iota) Weight DZ)
    (block : ι)
    (hblock : C.brauerBlock =
      irreducibleBrauerCharacterBlock iota hinj blocks) :
    Fibre C.brauerBlock block ≃ IBrBlock iota hinj blocks block where
  toFun phi := ⟨phi.1, by
    rw [← hblock]
    exact phi.2⟩
  invFun phi := ⟨phi.1, by
    rw [hblock]
    exact phi.2⟩
  left_inv phi := by
    apply Subtype.ext
    rfl
  right_inv phi := by
    apply Subtype.ext
    rfl

/-- The basic-set equivalence produced from the stable-reduction and exact
`K₀` bridge, with the modular endpoint equal to the literal `IBr` block
fibre. -/
noncomputable def basicToIBrBlockOfStableReduction
    (iota : PrimeRegularRootEmbedding p k K H)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[H]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι)
    [MulAction E Basic] [Finite Basic]
    (Msys : ModularSystem p K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic
        (decompositionMapOfStableReduction Msys iota hcompat))
    (automorphism : E →* (MulAut H)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (hordinary : OrdinaryTwistCompatibleLabels D automorphism)
    (outerGroupTwoHypoelementary : IsPHypoelementary 2 E)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := 2) (A := E))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := E)) :
    Basic ≃ IBrBlock iota hinj blocks block := by
  let _ : MulAction E (IBrBlock iota hinj blocks block) :=
    automorphismIBrBlockMulAction automorphism hstable
  exact Classical.choose
    (equivariantIBrBlockEquiv_of_stableReduction_canonical
      Msys hcompat D automorphism hstable hordinary
      outerGroupTwoHypoelementary conlon burnside)

/-- The basic-set equivalence selected above is equivariant for the canonical
automorphism action on the function-valued `IBr` block fibre. -/
theorem basicToIBrBlockOfStableReduction_equivariant
    (iota : PrimeRegularRootEmbedding p k K H)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[H]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι)
    [MulAction E Basic] [Finite Basic]
    (Msys : ModularSystem p K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic
        (decompositionMapOfStableReduction Msys iota hcompat))
    (automorphism : E →* (MulAut H)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (hordinary : OrdinaryTwistCompatibleLabels D automorphism)
    (outerGroupTwoHypoelementary : IsPHypoelementary 2 E)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := 2) (A := E))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := E))
    (a : E) (x : Basic) :
    let _ : MulAction E (IBrBlock iota hinj blocks block) :=
      automorphismIBrBlockMulAction automorphism hstable
    basicToIBrBlockOfStableReduction iota hinj blocks block Msys hcompat D
        automorphism hstable hordinary outerGroupTwoHypoelementary conlon
        burnside (a • x) =
      a • basicToIBrBlockOfStableReduction iota hinj blocks block Msys
        hcompat D automorphism hstable hordinary
        outerGroupTwoHypoelementary conlon burnside x := by
  dsimp only
  let _ : MulAction E (IBrBlock iota hinj blocks block) :=
    automorphismIBrBlockMulAction automorphism hstable
  exact Classical.choose_spec
    (equivariantIBrBlockEquiv_of_stableReduction_canonical
      Msys hcompat D automorphism hstable hordinary
      outerGroupTwoHypoelementary conlon burnside) a x

variable [MulAction E ι] [MulAction E R] [MulAction E S]
variable [MulAction E Weight] [MulAction E DZ]
variable [MulAction E Basic] [MulAction E GenericWeight]
variable [Finite Basic]

/-- The substantive finite set conclusion in Proposition 3.8, before the
cyclic-outer extension and character-triple criterion is applied.

The source is the literal function-valued Brauer-character fibre and the
target is the Alperin-weight fibre over the same block.  The integral
basic-set equivalence is derived from exact stable reduction, and the two
remaining arrows are the supplied generic-weight correspondences.  No
extension, intermediate-block, character-triple, normalisation, BAW-good, or
iBAW conclusion is an input. -/
theorem exists_equivariant_blockEquiv_of_stableReduction
    (iota : PrimeRegularRootEmbedding p k K H)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[H]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι)
    (Msys : ModularSystem p K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic
        (decompositionMapOfStableReduction Msys iota hcompat))
    (automorphism : E →* (MulAut H)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (hordinary : OrdinaryTwistCompatibleLabels D automorphism)
    (outerGroupTwoHypoelementary : IsPHypoelementary 2 E)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := 2) (A := E))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := E))
    [MulAction E (IBr iota)]
    (C : Context E ι R S (IBr iota) Weight DZ)
    (hblock : C.brauerBlock =
      irreducibleBrauerCharacterBlock iota hinj blocks)
    [MulAction E (Fibre C.brauerBlock block)]
    [MulAction E (Fibre C.weightBlock block)]
    (hSourceAction : ∀ (a : E) (x : Fibre C.brauerBlock block),
      contextBrauerFibreEquiv iota hinj blocks C block hblock (a • x) =
        automorphismIBrBlockSmul automorphism hstable a
          (contextBrauerFibreEquiv iota hinj blocks C block hblock x))
    (basicToGeneric : EquivariantEquiv E Basic GenericWeight (· • ·) (· • ·))
    (genericToAlperin : EquivariantEquiv E GenericWeight
      (Fibre C.weightBlock block) (· • ·) (· • ·)) :
    Nonempty (EquivariantEquiv E
      (Fibre C.brauerBlock block) (Fibre C.weightBlock block)
      (· • ·) (· • ·)) := by
  let _ : MulAction E (IBrBlock iota hinj blocks block) :=
    automorphismIBrBlockMulAction automorphism hstable
  let e : Basic ≃ IBrBlock iota hinj blocks block :=
    basicToIBrBlockOfStableReduction iota hinj blocks block Msys hcompat D
      automorphism hstable hordinary outerGroupTwoHypoelementary conlon burnside
  have he : ∀ (a : E) (x : Basic), e (a • x) = a • e x :=
    basicToIBrBlockOfStableReduction_equivariant iota hinj blocks block Msys
      hcompat D automorphism hstable hordinary outerGroupTwoHypoelementary
      conlon burnside
  let first : EquivariantEquiv E (IBrBlock iota hinj blocks block) Basic
      (· • ·) (· • ·) :=
    equivariantEquivSymm
      (show EquivariantEquiv E Basic (IBrBlock iota hinj blocks block)
          (· • ·) (· • ·) from ⟨e, he⟩)
  let tail : EquivariantEquiv E Basic (Fibre C.weightBlock block)
      (· • ·) (· • ·) :=
    equivariantEquivTrans basicToGeneric genericToAlperin
  let omega : Fibre C.brauerBlock block ≃ Fibre C.weightBlock block :=
    (contextBrauerFibreEquiv iota hinj blocks C block hblock).trans
      (first.toEquiv.trans tail.toEquiv)
  refine ⟨⟨omega, ?_⟩⟩
  intro a x
  change tail.toEquiv
      (first.toEquiv
        (contextBrauerFibreEquiv iota hinj blocks C block hblock (a • x))) =
    a • tail.toEquiv
      (first.toEquiv
        (contextBrauerFibreEquiv iota hinj blocks C block hblock x))
  rw [hSourceAction]
  change tail.toEquiv
      (first.toEquiv
        (a • contextBrauerFibreEquiv iota hinj blocks C block hblock x)) =
    a • tail.toEquiv
      (first.toEquiv
        (contextBrauerFibreEquiv iota hinj blocks C block hblock x))
  rw [first.equivariant, tail.equivariant]

/-- The strongest current blockwise construction theorem for the even-field
unipotent argument.

The integral basic-set/`IBr` equivalence is derived internally from exact
stable-reduction data.  `hSourceAction` is the still-uninstantiated semantic
identification between the manuscript action on its block fibre and the
canonical action obtained from the actual group automorphisms. -/
theorem exists_blockWitness_of_stableReduction
    (iota : PrimeRegularRootEmbedding p k K H)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[H]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι)
    (Msys : ModularSystem p K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (D : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block Basic
        (decompositionMapOfStableReduction Msys iota hcompat))
    (automorphism : E →* (MulAut H)ᵐᵒᵖ)
    (hstable : IsAutomorphismStableIBrBlock
      automorphism iota hinj blocks block)
    (hordinary : OrdinaryTwistCompatibleLabels D automorphism)
    (outerGroupTwoHypoelementary : IsPHypoelementary 2 E)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := 2) (A := E))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := E))
    [MulAction E (IBr iota)]
    (C : Context E ι R S (IBr iota) Weight DZ)
    (hblock : C.brauerBlock =
      irreducibleBrauerCharacterBlock iota hinj blocks)
    [MulAction E (Fibre C.brauerBlock block)]
    [MulAction E (Fibre C.weightBlock block)]
    (hSourceAction : ∀ (a : E) (x : Fibre C.brauerBlock block),
      contextBrauerFibreEquiv iota hinj blocks C block hblock (a • x) =
        automorphismIBrBlockSmul automorphism hstable a
          (contextBrauerFibreEquiv iota hinj blocks C block hblock x))
    (hBrauerAction : FibreActionCompatible (E := E) C.brauerBlock block)
    (hWeightAction : FibreActionCompatible (E := E) C.weightBlock block)
    (basicToGeneric : EquivariantEquiv E Basic GenericWeight (· • ·) (· • ·))
    (genericToAlperin : EquivariantEquiv E GenericWeight
      (Fibre C.weightBlock block) (· • ·) (· • ·))
    (T : CyclicOuterSourceInputs iota C block)
    (hnormalisation : ∀ (d : DZ)
      (hd : C.brauerBlock (C.reduce d) = block),
        ((contextBrauerFibreEquiv iota hinj blocks C block hblock).trans
          ((basicToIBrBlockOfStableReduction iota hinj blocks block Msys
              hcompat D automorphism hstable hordinary
              outerGroupTwoHypoelementary conlon burnside).symm.trans
            (basicToGeneric.toEquiv.trans genericToAlperin.toEquiv)))
            ⟨C.reduce d, hd⟩ =
          ⟨C.atOne d, (C.atOne_block d).trans hd⟩) :
    Nonempty (BlockWitness C block) := by
  let _ : MulAction E (IBrBlock iota hinj blocks block) :=
    automorphismIBrBlockMulAction automorphism hstable
  let e : Basic ≃ IBrBlock iota hinj blocks block :=
    basicToIBrBlockOfStableReduction iota hinj blocks block Msys hcompat D
      automorphism hstable hordinary outerGroupTwoHypoelementary conlon burnside
  have he : ∀ (a : E) (x : Basic), e (a • x) = a • e x :=
    basicToIBrBlockOfStableReduction_equivariant iota hinj blocks block Msys
      hcompat D automorphism hstable hordinary outerGroupTwoHypoelementary
      conlon burnside
  let first : EquivariantEquiv E (IBrBlock iota hinj blocks block) Basic
      (· • ·) (· • ·) :=
    equivariantEquivSymm
      (show EquivariantEquiv E Basic (IBrBlock iota hinj blocks block)
          (· • ·) (· • ·) from ⟨e, he⟩)
  let tail : EquivariantEquiv E Basic (Fibre C.weightBlock block)
      (· • ·) (· • ·) :=
    equivariantEquivTrans basicToGeneric genericToAlperin
  let omega : Fibre C.brauerBlock block ≃ Fibre C.weightBlock block :=
    (contextBrauerFibreEquiv iota hinj blocks C block hblock).trans
      (first.toEquiv.trans tail.toEquiv)
  refine ⟨{
    equiv := omega
    stabilizer_equivariant := ?_
    intermediateBlockEqualities := ?_
    extensions := ?_
    characterTriple := ?_
    normalisation := ?_
  }⟩
  · intro a ha x
    have hsource :
        contextBrauerFibreEquiv iota hinj blocks C block hblock
            (stabilizerFibreEquiv C.brauerBlock
              C.brauerBlock_equivariant block a ha x) =
          a • contextBrauerFibreEquiv iota hinj blocks C block hblock x := by
      calc
        _ = contextBrauerFibreEquiv iota hinj blocks C block hblock
              (a • x) := by
            apply congrArg
              (contextBrauerFibreEquiv iota hinj blocks C block hblock)
            apply Subtype.ext
            exact (hBrauerAction a x).symm
        _ = automorphismIBrBlockSmul automorphism hstable a
              (contextBrauerFibreEquiv iota hinj blocks C block hblock x) :=
            hSourceAction a x
        _ = a • contextBrauerFibreEquiv iota hinj blocks C block hblock x :=
            rfl
    have htarget :
        stabilizerFibreEquiv C.weightBlock
            C.weightBlock_equivariant block a ha (omega x) =
          a • omega x := by
      apply Subtype.ext
      exact (hWeightAction a (omega x)).symm
    change omega
        (stabilizerFibreEquiv C.brauerBlock
          C.brauerBlock_equivariant block a ha x) =
      stabilizerFibreEquiv C.weightBlock
        C.weightBlock_equivariant block a ha (omega x)
    rw [htarget]
    change tail.toEquiv
        (first.toEquiv
          (contextBrauerFibreEquiv iota hinj blocks C block hblock
            (stabilizerFibreEquiv C.brauerBlock
              C.brauerBlock_equivariant block a ha x))) =
      a • tail.toEquiv
        (first.toEquiv
          (contextBrauerFibreEquiv iota hinj blocks C block hblock x))
    rw [hsource, first.equivariant, tail.equivariant]
  · intro x
    exact T.intermediateBlockEqualities_of_sameBlock x (omega x)
  · intro x
    exact T.extensions_of_global_and_local x (omega x)
      (T.globalExtension_available x)
      (T.localExtension_available (omega x))
  · intro x
    exact T.characterTriple_of_global_and_local x (omega x)
      (T.globalExtension_available x)
      (T.localExtension_available (omega x))
  · exact hnormalisation

end ModularRep.ManuscriptVerification.EvenUnipotentIBrBlockAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
