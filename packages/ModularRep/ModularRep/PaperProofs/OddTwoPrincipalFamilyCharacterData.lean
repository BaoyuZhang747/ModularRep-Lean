import ModularRep.PaperProofs.OddTwoGroupEquivBrauerBlocks
import ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
import ModularRep.PaperProofs.OddTwoTypeASourceJoin
import ModularRep.BrauerCharacterSeparation

/-!
# Literal principal character data from a routed family

The coefficient fields and block labels are those of the SAME selected
Definition 3.5 family. The root on Sp is the actual transport of family.iota
along the routed carrier's group equivalence. The primitive dictionary and
the existing family-catalogue equation first identify the actual target
ambient idempotents. Brauer block transport then proves support covariance,
and the transported constant-one character computes the selected principal
block. Both fibre maps restrict the existing actual group-equivalence maps.

No support law, principal-block equality, fibre map, character choice,
selected-root compatibility or relation is an additional source field.
The supplied target operations still require the exact existing primitive
dictionary; they are not treated as authenticated arbitrary operations.
This module stops before selected roots, representative correction and the
Full-HG Definition 3.5 interpretation.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks

universe u

private def reindexFibre {A B : Type u} (f : A → B) {b c : B}
    (h : b = c) : {x // f x = b} ≃ {x // f x = c} where
  toFun x := ⟨x.1, x.2.trans h⟩
  invFun x := ⟨x.1, x.2.trans h.symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

variable (family : Definition35Family.{u} 2) (block : family.Block)
variable {rank : ℕ} {F : Type u} [Field F] [Fintype F]
variable (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F)

local instance familyCharacterSpFintype : Fintype (Sp rank F) := Fintype.ofFinite _

/-- Exactly the routed group coordinates, with the family group displayed. -/
abbrev groupEquiv : family.H ≃* Sp rank F := carrier.symplecticEquiv

/-- The literal target root uses the SAME family root convention. -/
def symplecticRoot : PrimeRegularRootEmbedding 2 family.k family.K (Sp rank F) :=
  family.iota.alongMulEquiv (groupEquiv family block carrier)

/-- Injectivity follows from the explicit root embedding in K. -/
theorem symplecticInjective :
    IrreducibleBrauerCharacterInjectivity (symplecticRoot family block carrier) :=
  irreducibleBrauerCharacterInjectivity_of_rootEmbedding _

variable (input : TypeAInputSemantics family)
variable (OH : LocalBlockInductionOperations
  (p := 2) (k := family.k) (K := family.K) (G := Sp rank F) (Block := family.Block))
variable (dictionary : PrimitiveDictionary family.blockSource.operations OH
  (groupEquiv family block carrier))

include input dictionary in
/-- The family decomposition and its operations catalogue are not assumed
definitionally identical. The existing source equation bridges them before
the actual target primitive equation is obtained. -/
theorem target_primitive (b : family.Block) :
    OH.ambientBlockData.blockIdempotent b =
      MonoidAlgebra.domCongr family.k family.k (groupEquiv family block carrier)
        (family.blockIdempotent b) := by
  calc
    OH.ambientBlockData.blockIdempotent b =
        MonoidAlgebra.domCongr family.k family.k (groupEquiv family block carrier)
          (family.blockSource.operations.ambientBlockData.blockIdempotent b) :=
      (dictionary.ambient_primitive b).symm
    _ = _ := congrArg
      (MonoidAlgebra.domCongr family.k family.k (groupEquiv family block carrier))
      (input.catalogue_idempotent b)

/-- The target block function retains the indexing instance stored in OH. -/
def symplecticBrauerBlock (psi : IBr (symplecticRoot family block carrier)) :
    family.Block :=
  letI := OH.ambientBlockData.fintypeBlock
  irreducibleBrauerCharacterBlock (symplecticRoot family block carrier)
    (symplecticInjective family block carrier) OH.ambientBlockData.blocks psi

include input dictionary in
/-- Actual Brauer block transport through the primitive dictionary. -/
theorem block_transport (psi : IBr family.iota) :
    symplecticBrauerBlock family block carrier OH
        (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
          (groupEquiv family block carrier) psi) =
      irreducibleBrauerCharacterBlock family.iota family.irreducibleBrauerInjective
        family.blocks psi :=
  OddTwoGroupEquivBrauerBlocks.block_alongMulEquiv family.iota
    family.irreducibleBrauerInjective (groupEquiv family block carrier)
    (symplecticInjective family block carrier) family.blocks OH.ambientBlockData
    (target_primitive family block carrier input OH dictionary) psi

include input dictionary in
/-- Support covariance is proved for every target character and actual
automorphism, using the constructed pullback action on the same labels. -/
theorem support_transport :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    OperationsBrauerSupport (symplecticRoot family block carrier)
      (symplecticInjective family block carrier) OH := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  intro alpha psi
  obtain ⟨phi, rfl⟩ :=
    (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
      (groupEquiv family block carrier)).surjective psi
  have action := IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul family.iota
    (groupEquiv family block carrier) phi
    (MulOpposite.op (MulAut.congr (groupEquiv family block carrier).symm alpha.unop))
  simp only [MulOpposite.unop_op, congr_symm_congr, MulOpposite.op_unop] at action
  change symplecticBrauerBlock family block carrier OH
      (alpha • IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
        (groupEquiv family block carrier) phi) =
    alpha • symplecticBrauerBlock family block carrier OH
      (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
        (groupEquiv family block carrier) phi)
  rw [← action, block_transport family block carrier input OH dictionary,
    block_transport family block carrier input OH dictionary]
  exact family.brauerBlock_transport
    (MulOpposite.op (MulAut.congr (groupEquiv family block carrier).symm alpha.unop)) phi

/-- The actual intrinsic data are constructed; constant-one membership and
support covariance are theorem outputs, not additional supplied fields. -/
def data :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    PrincipalCharacterData (n := rank) (F := F)
      (k := family.k) (K := family.K) (Block := family.Block) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact
    { ordinarySplitting := input.ordinarySplitting
      iota := symplecticRoot family block carrier
      injective := symplecticInjective family block carrier
      blockSource := transportedSource OH (groupEquiv family block carrier)
        family.blockSource dictionary
      trivialCharacter := IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
        (groupEquiv family block carrier) (carrier.principalCharacter.1 : IBr family.iota)
      trivial_value := fun x => carrier.principalCharacter_value_one
        (PrimeRegularElement.map (groupEquiv family block carrier).symm.toMonoidHom x)
      support_transport := support_transport family block carrier input OH dictionary }

@[simp] theorem data_iota :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    (data family block carrier input OH dictionary).iota =
      family.iota.alongMulEquiv (groupEquiv family block carrier) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  rfl

@[simp] theorem data_operations :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    (data family block carrier input OH dictionary).blockSource.operations = OH := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  rfl

/-- The block is computed from the transported constant-one character and
is the SAME selected family block. -/
theorem data_principalBlock :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    (data family block carrier input OH dictionary).principalBlock = block := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact (block_transport family block carrier input OH dictionary
    (carrier.principalCharacter.1 : IBr family.iota)).trans carrier.principalCharacter.2

/-- Restrict the computed Brauer equivalence, then reindex by the proved
principal-block equality. No new character or map is selected. -/
def brauerEquiv :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    Definition35Brauer (family.problem block) ≃
      (data family block carrier input OH dictionary).PrincipalBrauer := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact (OddTwoGroupEquivBrauerBlocks.brauerFibreEquiv family.iota
    family.irreducibleBrauerInjective (groupEquiv family block carrier)
    (symplecticInjective family block carrier) family.blocks OH.ambientBlockData
    (target_primitive family block carrier input OH dictionary) block).trans
      (reindexFibre (symplecticBrauerBlock family block carrier OH)
        (data_principalBlock family block carrier input OH dictionary).symm)

@[simp] theorem brauerEquiv_character (psi : Definition35Brauer (family.problem block)) :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    (brauerEquiv family block carrier input OH dictionary psi).1 =
      IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
        (groupEquiv family block carrier) (psi.1 : IBr family.iota) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  rfl

/-- Literal pullback values on the same coefficient field. -/
@[simp] theorem brauerEquiv_value (psi : Definition35Brauer (family.problem block))
    (x : PrimeRegularElement (G := Sp rank F) 2) :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    (brauerEquiv family block carrier input OH dictionary psi).1.1 x =
      psi.1.1 (PrimeRegularElement.map
        (groupEquiv family block carrier).symm.toMonoidHom x) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  rfl

/-- Restrict the computed own-character conjugacy class equivalence and
reindex by the SAME proved principal-block equality. -/
def weightEquiv :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    Definition35Weight (family.problem block) ≃
      (data family block carrier input OH dictionary).PrincipalWeight := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact (fibreEquiv OH (groupEquiv family block carrier) family.blockSource dictionary block).trans
    (reindexFibre
      (transportedSource OH (groupEquiv family block carrier)
        family.blockSource dictionary).weightBlock
      (data_principalBlock family block carrier input OH dictionary).symm)

@[simp] theorem weightEquiv_class (w : Definition35Weight (family.problem block)) :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    (weightEquiv family block carrier input OH dictionary w).1 =
      CharacterWeight.conjugacyClassGroupEquiv (groupEquiv family block carrier) w.1 := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  rfl

end ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
