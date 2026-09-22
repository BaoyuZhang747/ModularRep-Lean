import ModularRep.EvenUnipotentAssembly
import ModularRep.IBrSimpleModuleClass
import Formalisation.IBAWBlockWitness

/-!
# Blockwise iBAW construction for the even-field unipotent argument

This file closes the typed gap between the finite set bijection constructed in
`EvenUnipotentAssembly` and the blockwise object required by manuscript
Proposition 3.8.  The source fibre consists of the actual function-valued
irreducible Brauer characters `IBr iota` in one block.

The representation theoretic content of Feng--Li--Zhang, Theorem 3.18, is not
hidden in the construction.  It is supplied through `CyclicOuterSourceInputs`
as separate global-extension, local-extension, intermediate-block, and
character-triple clauses.  Although no single input is named BAW-good or iBAW,
these final clauses receive no kernel-proof credit.  The `Q = 1`
normalisation is also supplied separately because it does not follow from an
arbitrary equivariant equivalence of the two finite sets.
-/

noncomputable section

namespace ModularRep.ManuscriptVerification.EvenUnipotentIBAW

open ModularRep.ManuscriptVerification.EvenUnipotentAssembly
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open Formalisation
open Formalisation.IBAW

universe u

variable {p : ℕ}
variable {k K H E B R S Weight DZ Basic GenericWeight : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H]
variable [Group E] [Finite E]
variable [MulAction E B] [MulAction E R] [MulAction E S]
variable [MulAction E Weight] [MulAction E DZ]
variable (iota : PrimeRegularRootEmbedding p k K H)
variable [MulAction E (IBr iota)]

/-- Compatibility of a supplied action on a block fibre with the ambient
action.  This prevents an artificial action on the subtype from being used to
manufacture equivariance of the blockwise bijection. -/
def FibreActionCompatible {X I : Type*} [MulAction E X]
    (blockOf : X → I) (b : I) [MulAction E (Fibre blockOf b)] : Prop :=
  ∀ (a : E) (x : Fibre blockOf b), (a • x).1 = a • x.1

variable (C : Context E B R S (IBr iota) Weight DZ) (b : B)
variable [MulAction E (Fibre C.brauerBlock b)]
variable [MulAction E (Fibre C.weightBlock b)]

/-- The source-shaped clauses used after the blockwise equivariant bijection
has been constructed.

`GlobalExtensionOK` and `LocalExtensionOK` are to be instantiated by the
actual extension predicates for the global Brauer character and the Brauer
reduction of the local defect-zero character.  The two `available` fields are
the cyclic-extension applications.  The remaining fields are the collapsed
intermediate-block and modular-character-triple clauses in the specialization
of Feng--Li--Zhang, Theorem 3.18, to `G = G_tilde = H` and one centreless
block.  This structure contains no equivalence and no iBAW or BAW-good
conclusion. -/
structure CyclicOuterSourceInputs where
  GlobalExtensionOK : Fibre C.brauerBlock b → Prop
  LocalExtensionOK : Fibre C.weightBlock b → Prop
  globalExtension_available : ∀ x, GlobalExtensionOK x
  localExtension_available : ∀ y, LocalExtensionOK y
  intermediateBlockEqualities_of_sameBlock :
    ∀ (x : Fibre C.brauerBlock b) (y : Fibre C.weightBlock b),
      C.intermediateBlockEqualitiesOK x.1 y.1
  extensions_of_global_and_local :
    ∀ (x : Fibre C.brauerBlock b) (y : Fibre C.weightBlock b),
      GlobalExtensionOK x → LocalExtensionOK y →
        C.extensionsOK x.1 y.1
  characterTriple_of_global_and_local :
    ∀ (x : Fibre C.brauerBlock b) (y : Fibre C.weightBlock b),
      GlobalExtensionOK x → LocalExtensionOK y →
        C.characterTripleOK x.1 y.1

variable [MulAction E Basic] [MulAction E GenericWeight]
variable [Finite Basic]

/-- A fixed choice of the blockwise equivalence constructed by the integral
basic-set, generic-weight, and Alperin-weight chain. -/
noncomputable def assembledBlockEquiv
    (D : AssemblyData
      (E := E) (IBr := Fibre C.brauerBlock b) (Basic := Basic)
      (GenericWeight := GenericWeight)
      (AlperinWeight := Fibre C.weightBlock b)) :
    Fibre C.brauerBlock b ≃ Fibre C.weightBlock b :=
  Classical.choose
    (exists_equivariant_alperin_equiv
      (E := E) (IBr := Fibre C.brauerBlock b) (Basic := Basic)
      (GenericWeight := GenericWeight)
      (AlperinWeight := Fibre C.weightBlock b) D)

/-- The selected block equivalence is equivariant. -/
theorem assembledBlockEquiv_equivariant
    (D : AssemblyData
      (E := E) (IBr := Fibre C.brauerBlock b) (Basic := Basic)
      (GenericWeight := GenericWeight)
      (AlperinWeight := Fibre C.weightBlock b))
    (a : E) (x : Fibre C.brauerBlock b) :
    assembledBlockEquiv iota C b D (a • x) =
      a • assembledBlockEquiv iota C b D x :=
  (Classical.choose_spec
    (exists_equivariant_alperin_equiv
      (E := E) (IBr := Fibre C.brauerBlock b) (Basic := Basic)
      (GenericWeight := GenericWeight)
      (AlperinWeight := Fibre C.weightBlock b) D)) a x

/-- The complete block witness combined in Proposition 3.8.

Lean constructs the equivalence from the basic-set and weight data, proves
its stabiliser equivariance from the two fibre-action compatibility
identities, and attaches each representation theoretic clause separately.
Block preservation is not assumed: it follows from the fact that the source
and target are the fibres over the same block `b`. -/
noncomputable def blockWitnessOfAssembly
    (D : AssemblyData
      (E := E) (IBr := Fibre C.brauerBlock b) (Basic := Basic)
      (GenericWeight := GenericWeight)
      (AlperinWeight := Fibre C.weightBlock b))
    (hBrauerAction : FibreActionCompatible (E := E) C.brauerBlock b)
    (hWeightAction : FibreActionCompatible (E := E) C.weightBlock b)
    (T : CyclicOuterSourceInputs iota C b)
    (hnormalisation : ∀ (d : DZ) (hd : C.brauerBlock (C.reduce d) = b),
      assembledBlockEquiv iota C b D ⟨C.reduce d, hd⟩ =
        ⟨C.atOne d, (C.atOne_block d).trans hd⟩) :
    BlockWitness C b where
  equiv := assembledBlockEquiv iota C b D
  stabilizer_equivariant a ha x := by
    have hsource :
        stabilizerFibreEquiv C.brauerBlock
            C.brauerBlock_equivariant b a ha x = a • x := by
      apply Subtype.ext
      exact (hBrauerAction a x).symm
    have htarget :
        stabilizerFibreEquiv C.weightBlock
            C.weightBlock_equivariant b a ha
              (assembledBlockEquiv iota C b D x) =
          a • assembledBlockEquiv iota C b D x := by
      apply Subtype.ext
      exact (hWeightAction a (assembledBlockEquiv iota C b D x)).symm
    rw [hsource, assembledBlockEquiv_equivariant, htarget]
  intermediateBlockEqualities x :=
    T.intermediateBlockEqualities_of_sameBlock x
      (assembledBlockEquiv iota C b D x)
  extensions x :=
    T.extensions_of_global_and_local x
      (assembledBlockEquiv iota C b D x)
      (T.globalExtension_available x)
      (T.localExtension_available (assembledBlockEquiv iota C b D x))
  characterTriple x :=
    T.characterTriple_of_global_and_local x
      (assembledBlockEquiv iota C b D x)
      (T.globalExtension_available x)
      (T.localExtension_available (assembledBlockEquiv iota C b D x))
  normalisation := hnormalisation

/-- Existential form of `blockWitnessOfAssembly`, matching the manuscript's
existence claim. -/
theorem exists_blockWitness_of_assembly
    (D : AssemblyData
      (E := E) (IBr := Fibre C.brauerBlock b) (Basic := Basic)
      (GenericWeight := GenericWeight)
      (AlperinWeight := Fibre C.weightBlock b))
    (hBrauerAction : FibreActionCompatible (E := E) C.brauerBlock b)
    (hWeightAction : FibreActionCompatible (E := E) C.weightBlock b)
    (T : CyclicOuterSourceInputs iota C b)
    (hnormalisation : ∀ (d : DZ) (hd : C.brauerBlock (C.reduce d) = b),
      assembledBlockEquiv iota C b D ⟨C.reduce d, hd⟩ =
        ⟨C.atOne d, (C.atOne_block d).trans hd⟩) :
    Nonempty (BlockWitness C b) :=
  ⟨blockWitnessOfAssembly iota C b D hBrauerAction hWeightAction T
    hnormalisation⟩

end ModularRep.ManuscriptVerification.EvenUnipotentIBAW


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
