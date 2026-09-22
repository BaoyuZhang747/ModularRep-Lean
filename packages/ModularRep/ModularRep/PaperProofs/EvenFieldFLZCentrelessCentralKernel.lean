import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

/-!
# The central character quotient in the centreless FLZ specialisation

For a centreless literal `Definition35Problem`, the subgroup used in the
Brough--Späth central character quotient is forced to be `bot`: it is the
intersection of `Z(H)` with the kernel of a chosen affording representation.
Consequently the common-central-kernel field used by the general relative
block-condition carrier is redundant in the centreless case, and the
quotient map is canonically an isomorphism.  The quotient operation collapses;
the quotient group is isomorphic to `H`, not to the trivial group.

This also constructs the central quotient of an `ell'`-cover from the fixed
cover itself.  No quotient-cover source field is needed once centrelessness
is available.

Centrelessness does not eliminate the predicate stored in
`Equation317SourceSemantics`: it remains the unformalised modular character
triple relation from equation (3.17).  That semantics and its witness are
indexed upstream by one concrete cover.  The final source carrier below
therefore removes only the kernel and quotient-cover fields that are proved
here.  It retains the fixed quotient-block, matched-character, extension,
and intermediate-block data, including the one-way equation-(3.17) premise.
It is not a BAW-good or iBAW statement.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-! ## Kernel and quotient collapse -/

/-- Centrelessness forces the central character kernel of every literal
Brauer character to be trivial.  This proof is independent of the chosen
affording representation. -/
theorem centralCharacterKernel_eq_bot_of_centerless
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P) :
    centralCharacterKernel P psi = ⊥ := by
  simp [centralCharacterKernel, hcenter]

/-- Hence every two characters in the literal block fibre have the same
central character kernel; no representation theoretic kernel comparison is
left in the centreless specialisation. -/
theorem centralCharacterKernel_eq_of_centerless
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi reference : Definition35Brauer P) :
    centralCharacterKernel P psi =
      centralCharacterKernel P reference := by
  rw [centralCharacterKernel_eq_bot_of_centerless P hcenter psi,
    centralCharacterKernel_eq_bot_of_centerless P hcenter reference]

/-- The canonical central character quotient is the quotient by `bot`, hence
is canonically isomorphic to the original centreless group. -/
def centerlessCentralCharacterQuotientEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P) :
    CentralCharacterQuotient P psi ≃* P.H :=
  (QuotientGroup.quotientMulEquivOfEq
      (centralCharacterKernel_eq_bot_of_centerless P hcenter psi)).trans
    QuotientGroup.quotientBot

@[simp]
theorem centerlessCentralCharacterQuotientEquiv_mk
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P) (h : P.H) :
    centerlessCentralCharacterQuotientEquiv P hcenter psi
        (centralCharacterQuotientMap P psi h) = h := by
  change QuotientGroup.quotientBot
    (QuotientGroup.quotientMulEquivOfEq
      (centralCharacterKernel_eq_bot_of_centerless P hcenter psi)
      (QuotientGroup.mk h)) = h
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- In the centreless case the canonical quotient map itself is bijective. -/
theorem centralCharacterQuotientMap_bijective_of_centerless
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P) :
    Function.Bijective (centralCharacterQuotientMap P psi) := by
  constructor
  · intro x y hxy
    have := congrArg
      (centerlessCentralCharacterQuotientEquiv P hcenter psi) hxy
    simpa only [centerlessCentralCharacterQuotientEquiv_mk] using this
  · exact QuotientGroup.mk'_surjective (centralCharacterKernel P psi)

/-- A quotient by a trivial central character kernel is again centreless. -/
theorem center_centralCharacterQuotient_eq_bot_of_centerless
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P) :
    Subgroup.center (CentralCharacterQuotient P psi) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro z hz
  have hz' : centerlessCentralCharacterQuotientEquiv P hcenter psi z ∈
      Subgroup.center P.H := by
    have hzSet : z ∈ Set.center (CentralCharacterQuotient P psi) := by
      rw [← Subgroup.coe_center]
      exact hz
    have hmapped := MulEquivClass.apply_mem_center
      (centerlessCentralCharacterQuotientEquiv P hcenter psi) hzSet
    rw [← Subgroup.coe_center] at hmapped
    exact hmapped
  rw [hcenter, Subgroup.mem_bot] at hz'
  exact (centerlessCentralCharacterQuotientEquiv P hcenter psi).injective
    (hz'.trans (map_one _).symm)

/-! ## Canonical quotient character and cover data -/

/-- In the centreless case the quotient Brauer character is obtained by
transport across the canonical quotient equivalence.  Thus its existence,
inflation formula, and central faithfulness are kernel consequences rather
than additional quotient-character source data. -/
def centerlessCentralQuotientBrauerSource
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P) :
    CentralQuotientBrauerSource P psi psi := by
  let quotientEquiv : P.H ≃* CentralCharacterQuotient P psi :=
    (centerlessCentralCharacterQuotientEquiv P hcenter psi).symm
  let quotientRoot := P.iota.alongMulEquiv quotientEquiv
  let quotientBrauer :=
    IrreducibleBrauerCharacter.alongMulEquiv P.iota quotientEquiv psi.1
  refine {
    iota := quotientRoot
    brauer := quotientBrauer
    irreducibleBrauerInjective :=
      irreducibleBrauerCharacterInjectivity_of_rootEmbedding quotientRoot
    centralFaithful := ?_
    inflation := ?_ }
  · simp [center_centralCharacterQuotient_eq_bot_of_centerless
      P hcenter psi]
  · apply PrimeRegularClassFunction.ext
    intro x
    change psi.1.1
        (PrimeRegularElement.map
          (centerlessCentralCharacterQuotientEquiv P hcenter psi).toMonoidHom
          (PrimeRegularElement.map
            (centralCharacterQuotientMap P psi) x)) = psi.1.1 x
    congr 1

/-- Centrelessness also forces the central quotient attached to every other
literal Brauer character to use the same (trivial) reference kernel.  Its
quotient character is again canonical transport of that character. -/
def centerlessCentralQuotientBrauerSourceFromReference
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P) :
    CentralQuotientBrauerSource P reference psi := by
  let referenceEquiv : P.H ≃* CentralCharacterQuotient P reference :=
    (centerlessCentralCharacterQuotientEquiv P hcenter reference).symm
  let quotientRoot := P.iota.alongMulEquiv referenceEquiv
  let quotientBrauer :=
    IrreducibleBrauerCharacter.alongMulEquiv P.iota referenceEquiv psi.1
  refine {
    iota := quotientRoot
    brauer := quotientBrauer
    irreducibleBrauerInjective :=
      irreducibleBrauerCharacterInjectivity_of_rootEmbedding quotientRoot
    centralFaithful := ?_
    inflation := ?_ }
  · simp [center_centralCharacterQuotient_eq_bot_of_centerless
      P hcenter reference]
  · apply PrimeRegularClassFunction.ext
    intro x
    change psi.1.1
        (PrimeRegularElement.map
          (centerlessCentralCharacterQuotientEquiv
            P hcenter reference).toMonoidHom
          (PrimeRegularElement.map
            (centralCharacterQuotientMap P reference) x)) = psi.1.1 x
    congr 1

/-- The root embedding in the centreless quotient packet has the same lift
as the original root embedding. -/
theorem centerlessCentralQuotientBrauerSourceFromReference_iota_lift
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P) :
    (centerlessCentralQuotientBrauerSourceFromReference
      P hcenter reference psi).iota.lift = P.iota.lift := by
  change
    (P.iota.alongMulEquiv
      (centerlessCentralCharacterQuotientEquiv
        P hcenter reference).symm).lift = P.iota.lift
  funext z
  exact P.iota.alongMulEquiv_lift
    (centerlessCentralCharacterQuotientEquiv
      P hcenter reference).symm z

/-- The central quotient of the fixed maximal `ell'`-cover is forced by
centrelessness.  The map to the simple quotient is the fixed covering map
after the canonical equivalence back to the family group. -/
def centerlessCentralQuotientCoverSource
    {ell : ℕ} (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (hcenter : Subgroup.center family.H = ⊥)
    (block : family.Block)
    (reference : Definition35Brauer (family.problem block)) :
    CentralQuotientCoverSource family cover block reference := by
  let P := family.problem block
  let quotientEquiv :
      CentralCharacterQuotient P reference ≃* family.H :=
    centerlessCentralCharacterQuotientEquiv P hcenter reference
  let quotientToSimple :
      CentralCharacterQuotient P reference →* cover.S :=
    cover.quotient.comp quotientEquiv.toMonoidHom
  have hcoverKer : cover.quotient.ker = ⊥ :=
    cover.quotient_kernel.trans hcenter
  have hcoverInjective : Function.Injective cover.quotient :=
    (MonoidHom.ker_eq_bot_iff cover.quotient).mp hcoverKer
  have hquotientToSimpleInjective : Function.Injective quotientToSimple :=
    hcoverInjective.comp quotientEquiv.injective
  have hquotientCenter :
      Subgroup.center (CentralCharacterQuotient P reference) = ⊥ :=
    center_centralCharacterQuotient_eq_bot_of_centerless
      P hcenter reference
  letI : Group.IsPerfect family.H := ⟨cover.perfect⟩
  letI : Group.IsPerfect (CentralCharacterQuotient P reference) :=
    Group.IsPerfect.ofSurjective
      (f := quotientEquiv.symm.toMonoidHom) quotientEquiv.symm.surjective
  refine {
    quotientToSimple := quotientToSimple
    quotientToSimple_comp := ?_
    quotientToSimple_surjective := ?_
    quotient_kernel := ?_
    perfect := ?_
    centerPrimeTo := ?_ }
  · ext h
    exact congrArg cover.quotient
      (centerlessCentralCharacterQuotientEquiv_mk
        P hcenter reference h)
  · intro s
    obtain ⟨h, rfl⟩ := cover.quotient_surjective s
    exact ⟨quotientEquiv.symm h, by simp [quotientToSimple]⟩
  · calc
      quotientToSimple.ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff quotientToSimple).mpr
          hquotientToSimpleInjective
      _ = Subgroup.center (CentralCharacterQuotient P reference) :=
        hquotientCenter.symm
  · exact Group.IsPerfect.commutator_eq_top
  · rw [hquotientCenter, Subgroup.card_bot]
    exact family.ellPrime.not_dvd_one

/-! ## The exact remaining centreless equation-(3.17) boundary -/

/-- The genuinely remaining one-way equation-(3.17) source after
centrelessness has removed the common-kernel and quotient-cover fields.

The quotient-block presentation, construction of the matched Brough--Späth
data, and one-way descended block membership are still representation-
theoretic E1/E2/U inputs.  In particular, the conditional `matched` field is
not replaced by a caller-selected proposition. -/
structure CentrelessEquation317ToRelativeBlockConditionSource
    {ell : ℕ} (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (block : family.Block)
    (automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block))
    (source : Equation317SourceSemantics
      (family.problem block) automorphisms
      cover)
    (hcenter : Subgroup.center family.H = ⊥) where
  reference : Definition35Brauer (family.problem block)
  QuotientBlock : Type u
  [fintypeQuotientBlock : Fintype QuotientBlock]
  quotientBlockIdempotent : QuotientBlock →
    family.k[CentralCharacterQuotient
      (family.problem block) reference]
  quotientBlocks :
    BlockIdempotentDecomposition quotientBlockIdempotent
  quotientBlock : QuotientBlock
  matched : ∀ (psi : Definition35Brauer (family.problem block))
      (w : Definition35Weight (family.problem block)),
    source.equation317BlockIsomorphic psi w →
      SpathMatchedBlockConditionTail
        (family.problem block) reference psi w
        (centerlessCentralQuotientBrauerSourceFromReference
          (family.problem block) hcenter reference psi)
  descendedBrauer_liesInQuotientBlock :
    ∀ (psi : Definition35Brauer (family.problem block))
      (w : Definition35Weight (family.problem block))
      (hrelation : source.equation317BlockIsomorphic psi w),
      irreducibleBrauerCharacterBlock
          (centerlessCentralQuotientBrauerSourceFromReference
            (family.problem block) hcenter reference psi).iota
          (centerlessCentralQuotientBrauerSourceFromReference
            (family.problem block) hcenter reference
              psi).irreducibleBrauerInjective
          quotientBlocks
          (centerlessCentralQuotientBrauerSourceFromReference
            (family.problem block) hcenter reference psi).brauer =
        quotientBlock

attribute [instance]
  CentrelessEquation317ToRelativeBlockConditionSource.fintypeQuotientBlock

/-- Reconstruct the older general conversion source.  Its common-kernel and
central-quotient-cover fields are filled by kernel proofs, and its cover is
definitionally the same concrete parameter indexing the source relation. -/
def CentrelessEquation317ToRelativeBlockConditionSource.toGeneral
    {ell : ℕ} {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {block : family.Block}
    {automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block)}
    {source : Equation317SourceSemantics
      (family.problem block) automorphisms cover}
    {hcenter : Subgroup.center family.H = ⊥}
    (conversion : CentrelessEquation317ToRelativeBlockConditionSource
      family cover block automorphisms source hcenter) :
    Equation317ToRelativeBlockConditionSource
      family cover block automorphisms source where
  reference := conversion.reference
  commonCentralKernel := fun psi ↦
    centralCharacterKernel_eq_of_centerless
      (family.problem block) hcenter psi conversion.reference
  quotientCover := centerlessCentralQuotientCoverSource
    family cover hcenter block conversion.reference
  QuotientBlock := conversion.QuotientBlock
  fintypeQuotientBlock := conversion.fintypeQuotientBlock
  quotientBlockIdempotent := conversion.quotientBlockIdempotent
  quotientBlocks := conversion.quotientBlocks
  quotientBlock := conversion.quotientBlock
  matched := fun psi w hrelation ↦
    { quotient := centerlessCentralQuotientBrauerSourceFromReference
        (family.problem block) hcenter conversion.reference psi
      tail := conversion.matched psi w hrelation }
  descendedBrauer_liesInQuotientBlock :=
    conversion.descendedBrauer_liesInQuotientBlock

/-- Cover-bound centreless form of the existing one-way conversion.  The
centreless proof carried by the equation-(3.17) witness discharges every
common central kernel, while the output is indexed by exactly the same
concrete cover as the source semantics and witness. -/
def Equation317Witness.toCoverBoundRelativeBlockCondition
    {ell : ℕ} {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {block : family.Block}
    {automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block)}
    {source : Equation317SourceSemantics
      (family.problem block) automorphisms cover}
    (witness : Equation317Witness
      (family.problem block) automorphisms cover source)
    (conversion : CentrelessEquation317ToRelativeBlockConditionSource
      family cover block automorphisms source witness.centerless) :
    RelativeBlockConditionWitness
      family cover block :=
  Equation317Witness.toRelativeBlockCondition
    conversion.toGeneral witness

end ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
