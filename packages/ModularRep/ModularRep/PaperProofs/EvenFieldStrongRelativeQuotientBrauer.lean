import ModularRep.PaperProofs.EvenFieldStrongRelativeQuotientWeight
import ModularRep.PaperProofs.EvenFieldFLZ57ChosenRootMetadata

/-!
# The actual quotient Brauer fibre of a strong centreless witness

The SAME W and its selected scalar metadata determine the root comparison.
Its literal inflation equation then identifies each stored quotient Brauer
character with canonical transport through the actual quotient equivalence.
No character equality is inferred solely from root agreement.

The two actual complete primitive catalogues determine the specified label.
W's existing membership at W.reference identifies its stored label with that
computed label. The reverse fibre follows from the canonical equivalence;
it is constructed as the old reverse-source interface, never assumed.

No W, selected own pair, extension or intermediate packet is replaced.
Specified corresponding weight dictionaries, global construction and Q=1 remain separate.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldStrongRelativeQuotientBrauer

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37ActualBlockFibres
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre
open EvenFieldFLZ57ChosenRootMetadata EvenFieldStrongRelativeQuotientWeight
open TypeBFullBlockCondition TypeCCoherentFiniteRootConvention

universe u

section RootFibre

variable {p : ℕ} {k K G B : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Fintype B]
variable {idempotent : B → k[G]}

local instance rootFibreFintype : Fintype G := Fintype.ofFinite _

/-- Root transport changes neither the character values nor its specified
support. Both roots and their literal equality are fixed arguments. -/
private def rootFibreEquiv
    (iota j : PrimeRegularRootEmbedding p k K G) (h : iota = j)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (hinjJ : IrreducibleBrauerCharacterInjectivity j)
    (D : BlockIdempotentDecomposition idempotent) (b : B) :
    BrauerFibre iota hinj D b ≃ BrauerFibre j hinjJ D b where
  toFun psi := ⟨transportIBrRoot h psi.1,
    (irreducibleBrauerCharacterBlock_transportIBrRoot h hinj hinjJ D psi.1).trans psi.2⟩
  invFun psi := ⟨transportIBrRoot h.symm psi.1,
    (irreducibleBrauerCharacterBlock_transportIBrRoot h.symm hinjJ hinj D psi.1).trans psi.2⟩
  left_inv psi := by cases h; rfl
  right_inv psi := by cases h; rfl

end RootFibre

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H} {block : family.Block}
variable (W : RelativeBlockConditionWitness family cover block)
variable (hcenter : Subgroup.center family.H = ⊥)
variable (C : Convention ell family.k family.K)
variable (admissible : FamilyRootAdmissibility family C)
variable (metadata : RelativeRootMetadata C W)

local instance quotientFintype : Fintype (QuotientCarrier W) := Fintype.ofFinite _

include C admissible metadata in
/-- The same convention identifies canonical ambient-root transport with
the root actually stored at W.reference. No new root equality is supplied. -/
theorem transportedRoot_eq_fixed :
    family.iota.alongMulEquiv (quotientEquiv W hcenter) = fixedQuotientRoot W := by
  have h := congrArg
    (fun root : PrimeRegularRootEmbedding ell family.k family.K family.H =>
      root.alongMulEquiv (quotientEquiv W hcenter)) admissible.ambient_eq
  exact h.trans ((C.rootAt_alongMulEquiv (quotientEquiv W hcenter)).trans
    (metadata.matched W.reference).quotient_eq.symm)

/-- Actual quotient inflation, evaluated through the inverse group map,
determines the stored character on every prime regular quotient element. -/
theorem fixedDescendedBrauer_eq_canonical
    (psi : Definition35Brauer (family.problem block)) :
    fixedDescendedBrauer W metadata.fixedQuotientRootSource psi =
      transportIBrRoot (transportedRoot_eq_fixed W hcenter C admissible metadata)
        (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
          (quotientEquiv W hcenter) psi.1) := by
  apply Subtype.ext
  have hvalues :
      (fixedDescendedBrauer W metadata.fixedQuotientRootSource psi).1 =
        (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
          (quotientEquiv W hcenter) psi.1).1 := by
    apply PrimeRegularClassFunction.ext
    intro x
    have h := congrArg
      (fun f : PrimeRegularClassFunction family.K family.H ell =>
        f (PrimeRegularElement.map (quotientEquiv W hcenter).symm.toMonoidHom x))
      (fixedDescendedBrauer_inflation W metadata.fixedQuotientRootSource psi)
    change (fixedDescendedBrauer W metadata.fixedQuotientRootSource psi).1
        (PrimeRegularElement.map (quotientEquiv W hcenter).toMonoidHom
          (PrimeRegularElement.map (quotientEquiv W hcenter).symm.toMonoidHom x)) =
      psi.1.1 (PrimeRegularElement.map (quotientEquiv W hcenter).symm.toMonoidHom x) at h
    have hx : PrimeRegularElement.map (quotientEquiv W hcenter).toMonoidHom
        (PrimeRegularElement.map (quotientEquiv W hcenter).symm.toMonoidHom x) = x := by
      apply Subtype.ext
      exact (quotientEquiv W hcenter).apply_symm_apply x.1
    exact (congrArg
      (fun z : PrimeRegularElement (G := QuotientCarrier W) ell =>
        (fixedDescendedBrauer W metadata.fixedQuotientRootSource psi).1 z) hx).symm.trans h
  exact hvalues.trans (transportIBrRoot_val
    (transportedRoot_eq_fixed W hcenter C admissible metadata)
    (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
      (quotientEquiv W hcenter) psi.1)).symm

/-- Compute the specified fibre map first at the canonical transported root,
then transport that same fibre to the actual fixed quotient root. -/
def physicalBrauerEquiv :
    Definition35Brauer (family.problem block) ≃
      BrauerFibre (fixedQuotientRoot W) (fixedQuotientBrauerInjective W)
        W.quotientBlocks (physicalLabel W hcenter) :=
  (EvenFieldPhysicalBlockFibreReindexing.brauerEquiv family.blocks W.quotientBlocks
    (quotientEquiv W hcenter) family.iota family.irreducibleBrauerInjective
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
      (family.iota.alongMulEquiv (quotientEquiv W hcenter))) block).trans
    (rootFibreEquiv (family.iota.alongMulEquiv (quotientEquiv W hcenter))
      (fixedQuotientRoot W) (transportedRoot_eq_fixed W hcenter C admissible metadata)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
        (family.iota.alongMulEquiv (quotientEquiv W hcenter)))
      (fixedQuotientBrauerInjective W) W.quotientBlocks (physicalLabel W hcenter))

/-- The computed fibre map is exactly the stored descent, with its existing
root transport. It is not a second matching chosen to force surjectivity. -/
theorem physicalBrauerEquiv_value (psi : Definition35Brauer (family.problem block)) :
    (physicalBrauerEquiv W hcenter C admissible metadata psi).1 =
      fixedDescendedBrauer W metadata.fixedQuotientRootSource psi :=
  (fixedDescendedBrauer_eq_canonical W hcenter C admissible metadata psi).symm

include C admissible metadata in
/-- The existing member W.reference lies in both the stored and computed
specified block. Its actual block assignment gives equality of those labels. -/
theorem storedLabel_eq_physical : W.quotientBlock = physicalLabel W hcenter := by
  have hvalue := congrArg
    (fun psi : IBr (fixedQuotientRoot W) =>
      irreducibleBrauerCharacterBlock (fixedQuotientRoot W)
        (fixedQuotientBrauerInjective W) W.quotientBlocks psi)
    (physicalBrauerEquiv_value W hcenter C admissible metadata W.reference)
  exact (fixedDescendedBrauer_liesInQuotientBlock W metadata.fixedQuotientRootSource
    W.reference).symm.trans (hvalue.symm.trans
      (physicalBrauerEquiv W hcenter C admissible metadata W.reference).2)

/-- Construct the old reverse interface using the inverse of the actual
specified fibre equivalence. No reverse-source premise is assumed. -/
def reverseSource : QuotientBlockFibreReverseSource W metadata.fixedQuotientRootSource where
  of_quotientBlock phi hphi := by
    let v : BrauerFibre (fixedQuotientRoot W) (fixedQuotientBrauerInjective W)
        W.quotientBlocks (physicalLabel W hcenter) :=
      ⟨phi, hphi.trans (storedLabel_eq_physical W hcenter C admissible metadata)⟩
    let E := physicalBrauerEquiv W hcenter C admissible metadata
    refine ⟨E.symm v, ?_⟩
    exact (physicalBrauerEquiv_value W hcenter C admissible metadata (E.symm v)).symm.trans
      (congrArg Subtype.val (E.apply_symm_apply v))

/-- The complete original-to-STORED-quotient-block Brauer equivalence now
uses only the actual canonical maps and the supplied selected metadata. -/
def brauerFibreEquiv :
    Definition35Brauer (family.problem block) ≃ FixedQuotientBrauerFibre W :=
  originalBrauerFibreEquivFixedQuotientBrauerFibre W metadata.fixedQuotientRootSource
    (reverseSource W hcenter C admissible metadata)

/-- Its forward map retains the exact old fixed descent on the same W. -/
theorem brauerFibreEquiv_value (psi : Definition35Brauer (family.problem block)) :
    (brauerFibreEquiv W hcenter C admissible metadata psi).1 =
      fixedDescendedBrauer W metadata.fixedQuotientRootSource psi := rfl

end ModularRep.PaperProofs.EvenFieldStrongRelativeQuotientBrauer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
