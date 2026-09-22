import ModularRep.PaperProofs.EvenFieldStrongRelativeQuotientBrauer
import Mathlib.Algebra.Group.Action.TransferInstance

/-!
# Actual quotient action and the same strong correspondence

The canonical centreless quotient equivalence and the two complete primitive
catalogues compute the quotient block action. The whole Brauer equivalence
uses the already proved equality with the selected reference root.

Graph equivariance is proved for the SAME W. A quotient automorphism is
pulled back to the original group; fixation of the original specified block
follows from the supplied equality of the two descended characters. Only
then is the actual block-stabilizer adapter used to invoke W.equivariant.
There is no assumption that the family's Gamma is the full automorphism
group and no new graph, action, relation or specified support source.

The separate specified local-block interpretation, complete-block construction,
global choices and Q=1 normalization remain outside this module.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldStrongRelativeQuotientAction

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37ActualBlockFibres CyclicOuterLemma37Concrete
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre
open EvenFieldFLZ57ChosenRootMetadata EvenFieldStrongRelativeQuotientWeight
open EvenFieldStrongRelativeQuotientBrauer EvenFieldBlockGroupEquivCoordinates
open TypeBFullBlockCondition TypeCCoherentFiniteRootConvention

universe u

section RootTransport

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G]
variable {iota j : PrimeRegularRootEmbedding p k K G}

private def rootEquiv (h : iota = j) : IBr iota ≃ IBr j where
  toFun := transportIBrRoot h
  invFun := transportIBrRoot h.symm
  left_inv phi := by cases h; rfl
  right_inv phi := by cases h; rfl

private theorem rootEquiv_smul (h : iota = j)
    (alpha : (MulAut G)ᵐᵒᵖ) (phi : IBr iota) :
    rootEquiv h (alpha • phi) = alpha • rootEquiv h phi := by
  cases h
  rfl

end RootTransport

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H} {block : family.Block}
variable (W : RelativeBlockConditionWitness family cover block)
variable (hcenter : Subgroup.center family.H = ⊥)

local instance quotientFintype : Fintype (QuotientCarrier W) := Fintype.ofFinite _

/-- The actual opposite-automorphism equivalence of the canonical quotient. -/
abbrev quotientAutomorphisms :
    (MulAut family.H)ᵐᵒᵖ ≃* (MulAut (QuotientCarrier W))ᵐᵒᵖ :=
  oppositeAutEquiv (quotientEquiv W hcenter)

/-- The two complete primitive catalogues determine every target label. -/
abbrev quotientLabels : family.Block ≃ W.QuotientBlock :=
  EvenFieldPhysicalBlockFibreReindexing.blockLabelEquiv
    family.blocks W.quotientBlocks (quotientEquiv W hcenter)

/-- Transport the actual family action through its computed label map and
the inverse actual automorphism equivalence. -/
@[instance_reducible]
def quotientBlockAction : MulAction (MulAut (QuotientCarrier W))ᵐᵒᵖ W.QuotientBlock := by
  letI : MulAction (MulAut (QuotientCarrier W))ᵐᵒᵖ family.Block :=
    MulAction.compHom family.Block (quotientAutomorphisms W hcenter).symm.toMonoidHom
  exact (quotientLabels W hcenter).symm.mulAction _

theorem quotientBlockAction_smul
    (alpha : (MulAut (QuotientCarrier W))ᵐᵒᵖ) (b : W.QuotientBlock) :
    letI := quotientBlockAction W hcenter
    alpha • b = quotientLabels W hcenter
      ((quotientAutomorphisms W hcenter).symm alpha •
        (quotientLabels W hcenter).symm b) := rfl

variable (C : Convention ell family.k family.K)
variable (admissible : FamilyRootAdmissibility family C)
variable (metadata : RelativeRootMetadata C W)

/-- The whole actual IBr equivalence at the SAME selected reference root. -/
def wholeBrauerEquiv : IBr family.iota ≃ IBr (fixedQuotientRoot W) :=
  (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
    (quotientEquiv W hcenter)).trans
      (rootEquiv (transportedRoot_eq_fixed W hcenter C admissible metadata))

theorem wholeBrauerEquiv_value (phi : IBr family.iota)
    (x : PrimeRegularElement (G := QuotientCarrier W) ell) :
    (wholeBrauerEquiv W hcenter C admissible metadata phi).1 x =
      phi.1 (PrimeRegularElement.map (quotientEquiv W hcenter).symm.toMonoidHom x) := by
  exact congrArg (fun f : PrimeRegularClassFunction family.K (QuotientCarrier W) ell => f x)
    (transportIBrRoot_val (transportedRoot_eq_fixed W hcenter C admissible metadata)
      (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
        (quotientEquiv W hcenter) phi))

/-- Whole-carrier naturality retains the exact opposite action. -/
theorem wholeBrauerEquiv_smul (beta : (MulAut family.H)ᵐᵒᵖ) (phi : IBr family.iota) :
    wholeBrauerEquiv W hcenter C admissible metadata (beta • phi) =
      quotientAutomorphisms W hcenter beta •
        wholeBrauerEquiv W hcenter C admissible metadata phi := by
  have h := IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul family.iota
    (quotientEquiv W hcenter) phi beta
  exact (congrArg
    (rootEquiv (transportedRoot_eq_fixed W hcenter C admissible metadata)) h).trans
      (rootEquiv_smul (transportedRoot_eq_fixed W hcenter C admissible metadata)
        (quotientAutomorphisms W hcenter beta)
        (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
          (quotientEquiv W hcenter) phi))

theorem wholeBrauerEquiv_pullback_smul
    (alpha : (MulAut (QuotientCarrier W))ᵐᵒᵖ) (phi : IBr family.iota) :
    wholeBrauerEquiv W hcenter C admissible metadata
        ((quotientAutomorphisms W hcenter).symm alpha • phi) =
      alpha • wholeBrauerEquiv W hcenter C admissible metadata phi :=
  (wholeBrauerEquiv_smul W hcenter C admissible metadata
    ((quotientAutomorphisms W hcenter).symm alpha) phi).trans
      (congrArg (fun a : (MulAut (QuotientCarrier W))ᵐᵒᵖ =>
        a • wholeBrauerEquiv W hcenter C admissible metadata phi)
        ((quotientAutomorphisms W hcenter).apply_symm_apply alpha))

/-- Specified support for every character follows from the actual catalogues
and root transport, not from a chosen-block action assumption. -/
theorem wholeBrauerEquiv_block (phi : IBr family.iota) :
    irreducibleBrauerCharacterBlock (fixedQuotientRoot W)
        (fixedQuotientBrauerInjective W) W.quotientBlocks
        (wholeBrauerEquiv W hcenter C admissible metadata phi) =
      quotientLabels W hcenter
        (irreducibleBrauerCharacterBlock family.iota family.irreducibleBrauerInjective
          family.blocks phi) := by
  exact (irreducibleBrauerCharacterBlock_transportIBrRoot
    (transportedRoot_eq_fixed W hcenter C admissible metadata)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
      (family.iota.alongMulEquiv (quotientEquiv W hcenter)))
    (fixedQuotientBrauerInjective W) W.quotientBlocks
    (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
      (quotientEquiv W hcenter) phi)).trans
        (EvenFieldPhysicalBlockFibreReindexing.brauerBlock_map family.blocks
          W.quotientBlocks (quotientEquiv W hcenter) family.iota
          family.irreducibleBrauerInjective
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
            (family.iota.alongMulEquiv (quotientEquiv W hcenter))) phi)

include C admissible metadata in
/-- The computed action is the actual quotient Brauer-block action on the
entire fixed-root carrier. -/
theorem quotientBrauerBlock_transport
    (alpha : (MulAut (QuotientCarrier W))ᵐᵒᵖ) (phi : IBr (fixedQuotientRoot W)) :
    letI := quotientBlockAction W hcenter
    irreducibleBrauerCharacterBlock (fixedQuotientRoot W)
        (fixedQuotientBrauerInjective W) W.quotientBlocks (alpha • phi) =
      alpha • irreducibleBrauerCharacterBlock (fixedQuotientRoot W)
        (fixedQuotientBrauerInjective W) W.quotientBlocks phi := by
  letI := quotientBlockAction W hcenter
  obtain ⟨chi, rfl⟩ := (wholeBrauerEquiv W hcenter C admissible metadata).surjective phi
  rw [← wholeBrauerEquiv_pullback_smul W hcenter C admissible metadata alpha chi,
    wholeBrauerEquiv_block W hcenter C admissible metadata,
    family.brauerBlock_transport]
  rw [wholeBrauerEquiv_block W hcenter C admissible metadata,
    quotientBlockAction_smul, Equiv.symm_apply_apply]

/-- The map just constructed retains the SAME stored descent on this fibre. -/
theorem fixedDescendedBrauer_eq_whole
    (psi : Definition35Brauer (family.problem block)) :
    fixedDescendedBrauer W metadata.fixedQuotientRootSource psi =
      wholeBrauerEquiv W hcenter C admissible metadata psi.1 :=
  fixedDescendedBrauer_eq_canonical W hcenter C admissible metadata psi

/-- Support recovers exactly the original block stabilizer; the actual
adapter then turns W's Gamma equivariance into this whole-carrier equation. -/
theorem omega_graph_equivariant
    (beta : (MulAut family.H)ᵐᵒᵖ)
    (psi chi : Definition35Brauer (family.problem block))
    (h : (chi.1 : IBr family.iota) =
      IrreducibleBrauerCharacter.twist family.iota (psi.1 : IBr family.iota) beta.unop) :
    ((W.omega chi).1 : ConjugacyClass (p := ell) (K := family.K) (G := family.H)) =
      @CharacterWeight.rightTwistConjugacyClass ell family.K family.H
        family.fieldK family.charZeroK family.groupH
        (@Finite.of_fintype family.H family.fintypeH) beta.unop (W.omega psi).1 := by
  letI := definition35BrauerAction (family.problem block)
  letI := definition35WeightAction (family.problem block)
  have hfixed : beta • block = block := by
    have hb := congrArg
      (fun phi : IBr family.iota => irreducibleBrauerCharacterBlock family.iota
        family.irreducibleBrauerInjective family.blocks phi) h
    exact ((congrArg (fun b : family.Block => beta • b) psi.2).symm.trans
      ((family.brauerBlock_transport beta psi.1).symm.trans (hb.symm.trans chi.2)))
  let s : MulAction.stabilizer (MulAut family.H)ᵐᵒᵖ block := ⟨beta, hfixed⟩
  let g := W.automorphismStabilizer.equiv.symm s
  have hg : inverseOpHom (family.problem block).gamma g = beta :=
    (W.automorphismStabilizer.equiv_coe g).symm.trans
      (congrArg Subtype.val (W.automorphismStabilizer.equiv.apply_symm_apply s))
  have hpsi : g • psi = chi := by
    apply Subtype.ext
    change IrreducibleBrauerCharacter.twist family.iota (psi.1 : IBr family.iota)
      (inverseOpHom (family.problem block).gamma g).unop = (chi.1 : IBr family.iota)
    exact (congrArg (fun a : (MulAut family.H)ᵐᵒᵖ =>
      IrreducibleBrauerCharacter.twist family.iota (psi.1 : IBr family.iota) a.unop)
      hg).trans h.symm
  have hW := W.equivariant g psi
  have hv := congrArg (fun w : Definition35Weight (family.problem block) => w.1) hW
  change (W.omega (g • psi)).1 =
    @CharacterWeight.rightTwistConjugacyClass ell family.K family.H
      family.fieldK family.charZeroK family.groupH
      (@Finite.of_fintype family.H family.fintypeH)
      (inverseOpHom (family.problem block).gamma g).unop
      (W.omega psi).1 at hv
  exact (congrArg (fun p : Definition35Brauer (family.problem block) => (W.omega p).1)
    hpsi).symm.trans (hv.trans
      (congrArg (fun a : (MulAut family.H)ᵐᵒᵖ =>
        @CharacterWeight.rightTwistConjugacyClass ell family.K family.H
          family.fieldK family.charZeroK family.groupH
          (@Finite.of_fintype family.H family.fintypeH) a.unop (W.omega psi).1) hg))

include hcenter admissible in
/-- The exact quotient graph required by the complete single-block target.
Neither the correspondence nor any matched packet is replaced. -/
theorem quotient_graph_equivariant
    (alpha : (MulAut (QuotientCarrier W))ᵐᵒᵖ)
    (psi chi : Definition35Brauer (family.problem block))
    (h : fixedDescendedBrauer W metadata.fixedQuotientRootSource chi =
      alpha • fixedDescendedBrauer W metadata.fixedQuotientRootSource psi) :
    quotientWeightClass W chi = alpha • quotientWeightClass W psi := by
  let beta := (quotientAutomorphisms W hcenter).symm alpha
  have hc : wholeBrauerEquiv W hcenter C admissible metadata chi.1 =
      alpha • wholeBrauerEquiv W hcenter C admissible metadata psi.1 :=
    (fixedDescendedBrauer_eq_whole W hcenter C admissible metadata chi).symm.trans
      (h.trans (congrArg (fun phi : IBr (fixedQuotientRoot W) => alpha • phi)
        (fixedDescendedBrauer_eq_whole W hcenter C admissible metadata psi)))
  have hpair : (chi.1 : IBr family.iota) =
      IrreducibleBrauerCharacter.twist family.iota (psi.1 : IBr family.iota) beta.unop :=
    (wholeBrauerEquiv W hcenter C admissible metadata).injective
      (hc.trans (wholeBrauerEquiv_pullback_smul W hcenter C admissible metadata
        alpha psi.1).symm)
  have hw := omega_graph_equivariant W beta psi chi hpair
  have hmap := congrArg (conjugacyClassGroupEquiv (quotientEquiv W hcenter)) hw
  have htwist := quotientClassMap_twist W hcenter beta (W.omega psi).1
  have hcancel : quotientAutomorphisms W hcenter beta = alpha :=
    (quotientAutomorphisms W hcenter).apply_symm_apply alpha
  exact (quotientWeightClass_eq_map W hcenter chi).trans (hmap.trans
    (htwist.trans ((congrArg (fun a : (MulAut (QuotientCarrier W))ᵐᵒᵖ =>
      a • conjugacyClassGroupEquiv (quotientEquiv W hcenter) (W.omega psi).1)
      hcancel).trans (congrArg (fun w : ConjugacyClass
        (p := ell) (K := family.K) (G := QuotientCarrier W) => alpha • w)
        (quotientWeightClass_eq_map W hcenter psi).symm))))

end ModularRep.PaperProofs.EvenFieldStrongRelativeQuotientAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
