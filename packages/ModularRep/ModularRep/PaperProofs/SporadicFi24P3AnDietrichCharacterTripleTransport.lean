import ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate
import ModularRep.PaperProofs.SporadicFi24Definition35Operations

/-!
# Retaining the An--Dietrich character-triple witness after block replacement

The An--Dietrich source certificate used for the prime-three cancellation
contains the published total equivariant bijection, but it deliberately does
not contain the local Definition 4.4 character-triple data.  Cancellation
then constructs a generally noncanonical principal-block bijection and
combines it with two independently constructed block maps.  Consequently a
character-triple witness attached to the published matched pair cannot be
transported merely from equality of sectors or stabilisers.

This file isolates the missing source fact without postulating a global
retention principle or the final Definition 3.5 relation.  On one fixed
literal block, the source must say that the replacement map is pointwise the
same as the transported An--Dietrich map and must supply source-native
Definition 4.4 witness data for that exact published pair.  Lean then returns
that same witness together with the equality identifying the replacement
image.

In particular, the source below does not mention `FLZSourceSemantics`, a
modular-character-triple predicate on the literal carriers, compatible
extensions, intermediate block equalities, BAW, or iBAW.  Turning the retained
source witness into the final Definition 3.5 assertion remains a separate
external theorem.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3AnDietrichCharacterTripleTransport

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24Definition35Operations
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate.AnDietrichFi24P3SourceCertificate

universe u

/-! ## Restriction of a replacement to one Definition 3.5 block -/

/-- Restrict a block-preserving global equivalence to the selected literal
block of a `Definition35Problem`.

This is a kernel construction.  In the Fischer application `Omega` is the
three-block equivalence combined after cancellation, and `hblock` is its
already proved block-preservation equality. -/
def restrictGlobalEquivToDefinition35Block
    (P : Definition35Problem.{u})
    (Omega : IBr P.iota ≃
      WeightClass (p := P.p) (K := P.K) (X := P.H))
    (hblock : ∀ psi : IBr P.iota,
      P.blockSource.weightBlock (Omega psi) =
        irreducibleBrauerCharacterBlock P.iota
          P.irreducibleBrauerInjective P.blocks psi) :
    Definition35Brauer P ≃ Definition35Weight P where
  toFun psi := ⟨Omega psi.1, (hblock psi.1).trans psi.2⟩
  invFun weight := ⟨Omega.symm weight.1, by
    calc
      irreducibleBrauerCharacterBlock P.iota
          P.irreducibleBrauerInjective P.blocks (Omega.symm weight.1) =
          P.blockSource.weightBlock
            (Omega (Omega.symm weight.1)) :=
        (hblock (Omega.symm weight.1)).symm
      _ = P.blockSource.weightBlock weight.1 := by
        rw [Omega.apply_symm_apply]
      _ = P.block := weight.2⟩
  left_inv psi := by
    apply Subtype.ext
    exact Omega.symm_apply_apply psi.1
  right_inv weight := by
    apply Subtype.ext
    exact Omega.apply_symm_apply weight.1

@[simp]
theorem restrictGlobalEquivToDefinition35Block_apply_val
    (P : Definition35Problem.{u})
    (Omega : IBr P.iota ≃
      WeightClass (p := P.p) (K := P.K) (X := P.H))
    (hblock : ∀ psi : IBr P.iota,
      P.blockSource.weightBlock (Omega psi) =
        irreducibleBrauerCharacterBlock P.iota
          P.irreducibleBrauerInjective P.blocks psi)
    (psi : Definition35Brauer P) :
    (restrictGlobalEquivToDefinition35Block P Omega hblock psi).1 =
      Omega psi.1 :=
  rfl

/-! ## The exact missing An--Dietrich same-map source -/

variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction]
variable [MulAction SourceAction SourceBrauer]
variable [MulAction SourceAction SourceWeight]

variable {k K X Gamma : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable [Group Gamma] [Finite Gamma]

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
variable (block : ActualBlock (k := k) (X := X))
variable (gamma : Gamma →* MulAut X)
variable (gammaBlock_fixed : ∀ a : Gamma,
  inverseOpHom gamma a • block = block)
variable (localReduction : ∀ w : LiteralWeightFibre R.1 block,
  SelectedLocalReductionSource R.1 block w)

/-- The precise Definition 3.5 problem on which the prime-three
An--Dietrich same-map statement is made. -/
abbrev fi24P3Definition35Problem : Definition35Problem.{u} :=
  literalDefinition35Problem iota hinj R block gamma gammaBlock_fixed
    localReduction

variable
  (AD : AnDietrichFi24P3SourceCertificate
    (SourceAction := SourceAction)
    (SourceBrauer := SourceBrauer)
    (SourceWeight := SourceWeight))
  (Bridge : AnDietrichFi24P3LiteralCarrierBridge
    (SourceAction := SourceAction)
    (SourceBrauer := SourceBrauer)
    (SourceWeight := SourceWeight) (k := k) (K := K) (X := X) iota)

/-- The missing E2/U binding between An--Dietrich Definition 4.4 and one
replacement block map.

`CharacterTripleWitness` is a source-carrier type of witness data, rather
than a truth-valued relation on the literal Definition 3.5 carriers.  The
record supplies it only for pairs selected by the published
`AD.sourceEquiv`, and only for source Brauer objects lying over this literal
block.  `sameMap` then identifies those exact published images with the
replacement images.  Neither field can be recovered from the global
equivariant-bijection certificate or from finite set cancellation. -/
structure AnDietrichDefinition44SameMapBinding
    (replacement : Definition35Brauer
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction) ≃
      Definition35Weight
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction))
    : Type (u + 1) where
  CharacterTripleWitness : SourceBrauer → SourceWeight → Type u
  witnessAtPublishedPair : ∀ psi : Definition35Brauer
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction),
    CharacterTripleWitness (Bridge.brauerIdentification psi.1)
      (AD.sourceEquiv (Bridge.brauerIdentification psi.1))
  sameMap : ∀ psi : Definition35Brauer
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction),
    (replacement psi).1 = literalEquiv iota AD Bridge psi.1

/-- A replacement local equivalence retains the source-native An--Dietrich
Definition 4.4 witness when it is pointwise the same local map.

The conclusion deliberately exposes the exact map equality and the witness
at the corresponding published source pair.  It does not claim the final
Definition 3.5 modular-character-triple relation. -/
theorem replacement_retains_definition44_witness
    (replacement : Definition35Brauer
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction) ≃
      Definition35Weight
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction))
    (binding : AnDietrichDefinition44SameMapBinding
      iota hinj R block gamma gammaBlock_fixed localReduction AD Bridge
      replacement)
    (psi : Definition35Brauer
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction)) :
    (replacement psi).1 = literalEquiv iota AD Bridge psi.1 ∧
    Nonempty (binding.CharacterTripleWitness
      (Bridge.brauerIdentification psi.1)
      (AD.sourceEquiv (Bridge.brauerIdentification psi.1))) :=
  ⟨binding.sameMap psi, ⟨binding.witnessAtPublishedPair psi⟩⟩

/-- Apply the same-map transport directly to the selected-block restriction
of a block-preserving global replacement `Omega`.  This is the form used by
the three-block cancellation/construction route. -/
theorem restrictedOmega_retains_definition44_witness
    (Omega : IBr
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction).iota ≃
      WeightClass
        (p := (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction).p)
        (K := (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction).K)
        (X := (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction).H))
    (hblock : ∀ psi : IBr
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction).iota,
      (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction).blockSource.weightBlock
          (Omega psi) =
        irreducibleBrauerCharacterBlock
          (fi24P3Definition35Problem iota hinj R block gamma
            gammaBlock_fixed localReduction).iota
          (fi24P3Definition35Problem iota hinj R block gamma
            gammaBlock_fixed localReduction).irreducibleBrauerInjective
          (fi24P3Definition35Problem iota hinj R block gamma
            gammaBlock_fixed localReduction).blocks psi)
    (binding : AnDietrichDefinition44SameMapBinding
      iota hinj R block gamma gammaBlock_fixed localReduction AD Bridge
      (restrictGlobalEquivToDefinition35Block
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction) Omega hblock))
    (psi : Definition35Brauer
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction)) :
    (restrictGlobalEquivToDefinition35Block
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction) Omega hblock psi).1 =
        literalEquiv iota AD Bridge psi.1 ∧
    Nonempty (binding.CharacterTripleWitness
      (Bridge.brauerIdentification psi.1)
      (AD.sourceEquiv (Bridge.brauerIdentification psi.1))) :=
  replacement_retains_definition44_witness
    iota hinj R block gamma gammaBlock_fixed localReduction AD Bridge
    (restrictGlobalEquivToDefinition35Block
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction) Omega hblock)
    binding psi

end ModularRep.PaperProofs.SporadicFi24P3AnDietrichCharacterTripleTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
