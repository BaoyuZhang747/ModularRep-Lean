import ManuscriptIBAW.TypeC.OddRationalSeries
import ModularRep.PaperProofs.TypeCCurrentConstituentFactorization

/-!
# A global bijection between ordinary and Brauer characters and stabiliser transfer

Conlon's argument constructs a bijection on each block orbit representative.
Transport along block orbits constructs a global equivariant bijection.
Surjectivity of the conformal and field action then gives equivariance under
every automorphism of Sp. The ordinary Cabanes–Späth theorem is applied
after this global bijection has been constructed.

Restriction supplies a constituent after the factorisation is known for
every Brauer character. Integral basic sets, Conlon's theorem, Burnside mark
injectivity and the ordinary Cabanes–Späth implication remain separate
source assumptions.
-/

noncomputable section
open scoped MonoidAlgebra Pointwise
namespace ManuscriptIBAW.TypeC.OddGlobalFactorization
open ModularRep ModularRep.PaperProofs Formalisation
open FDRepSimpleClassKZero ExactGrothendieckGroup DecompositionBasicSetBridge
open BlockFibreRestriction OrdinaryIrreducibleCharacter
open OddConformalProposition311Relative OddGFactorizationLemma312Relative
open OddConlonOrbitAssembly TypeBCriterionHypotheses
open TypeCCurrentConstituentFactorization (combinedAut combinedAut_eq actualBrauerAct
  BrauerProductFormula brauerFactorization_of_productFormula RestrictionExpansionSource exists_constituent)
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

section BasicSetApplication

variable {ell : ℕ} {K O k M E : Type}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)

local instance subgroupFintype : Fintype G := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k G)]
variable [MulAction (Ambient field) (LiteralPrimitiveBlock k G)]
variable (iotaG : PrimeRegularRootEmbedding ell k K G)
variable (hinjG : IrreducibleBrauerCharacterInjectivity iotaG)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k G => b.1))

/-- The exact global basic set inputs. Both the ordinary simple module labels
and decomposition map are fixed constructions. No ordinary or Brauer
stabiliser assertion is a field of this record. -/
structure BasicSetSource where
  modularSystem : ModularSystem ell K O k
  reductionCompatible : StableReductionBrauerCharacterCompatibility modularSystem iotaG
  ordinary : OrdinaryBasicData (K := K) (BlockIndex := LiteralPrimitiveBlock k G)
    (combinedAut G field action)
  [finiteOrdinary : Finite {chi : Irr K G // ordinary.predicate chi}]
  linearEquiv : MonoidAlgebra ℤ {chi : Irr K G // ordinary.predicate chi} ≃ₗ[ℤ]
    MonoidAlgebra ℤ (IBr iotaG)
  decomposition : ∀ v : MonoidAlgebra ℤ {chi : Irr K G // ordinary.predicate chi},
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iotaG hinjG).symm
        (linearEquiv v) =
      decompositionMapOfStableReduction modularSystem iotaG reductionCompatible
        (labelledSimpleClassKZero
          (TypeBOrdinaryLabelSplitting.ordinarySeriesLabel
            (K := K) ordinary.predicate) v)
  blockDiagonal : BlockDiagonalLinearEquiv ordinary.blockOf
    (irreducibleBrauerCharacterBlock iotaG hinjG blocks) linearEquiv
  brauerBlockEquivariant : ∀ (a : Ambient field) (phi : IBr iotaG),
    irreducibleBrauerCharacterBlock iotaG hinjG blocks
        (IrreducibleBrauerCharacter.twist iotaG phi
          ((combinedAut G field action) a⁻¹)) =
      a • irreducibleBrauerCharacterBlock iotaG hinjG blocks phi

attribute [instance] BasicSetSource.finiteOrdinary

variable (S : BasicSetSource (O := O) G field action iotaG hinjG blocks)

/-- Combine the integral source with the specified ordinary and Brauer simple
module labels and stable reduction decomposition map. -/
def BasicSetSource.basicSet : RestrictedIntegralBasicSetOnIBr iotaG hinjG
    {chi : Irr K G // S.ordinary.predicate chi}
    (decompositionMapOfStableReduction S.modularSystem iotaG S.reductionCompatible) :=
  { ordinaryLabel := TypeBOrdinaryLabelSplitting.ordinarySeriesLabel S.ordinary.predicate
    ordinaryLabel_injective :=
      TypeBOrdinaryLabelSplitting.ordinarySeriesLabel_injective S.ordinary.predicate
    linearEquiv := S.linearEquiv
    restricts_decomposition := S.decomposition }

variable {CyclicTarget : Type} [Group CyclicTarget] [IsCyclic CyclicTarget]

/-- Source data on one specified block stabiliser. The actions descend through
its actual inner subgroup. None of the fields is a bijection on the
characters belonging to a block or a Brauer character stabiliser assertion. -/
structure BlockSourceInputs (block : LiteralPrimitiveBlock k G) where
  innerSubgroup : Subgroup (MulAction.stabilizer (Ambient field) block)
  [innerNormal : innerSubgroup.Normal]
  inner : ∀ n : innerSubgroup, ∃ g : G,
    combinedAut G field action
      (((n : MulAction.stabilizer (Ambient field) block) : Ambient field)) = MulAut.conj g
  smallNormal : Subgroup (MulAction.stabilizer (Ambient field) block ⧸ innerSubgroup)
  [smallNormal_normal : smallNormal.Normal]
  small_card : Nat.card smallNormal ≤ 2
  quotientEmbedding :
    ((MulAction.stabilizer (Ambient field) block ⧸ innerSubgroup) ⧸ smallNormal) →*
      CyclicTarget
  quotientEmbedding_injective : Function.Injective quotientEmbedding
  conlon : ConlonBasicSet.PadicConlonMarkDetection.{0, 0} (p := 2)
    (A := MulAction.stabilizer (Ambient field) block ⧸ innerSubgroup)
  burnside : ConlonBasicSet.PublishedBurnsideMarkInjectivity.{0, 0}
    (A := MulAction.stabilizer (Ambient field) block ⧸ innerSubgroup)
  actions :
    letI := ordinaryBasicBlockQuotientAction (combinedAut G field action)
      S.ordinary block innerSubgroup inner
    letI := brauerBlockQuotientAction iotaG (combinedAut G field action)
      block innerSubgroup inner
    LabelledKZeroActionData
      (A := MulAction.stabilizer (Ambient field) block ⧸ innerSubgroup)
      (BasicSetSource.basicSet G field action iotaG hinjG blocks S).toRestrictedIntegralBasicSet
  reductionNatural :
    letI := ordinaryBasicBlockQuotientAction (combinedAut G field action)
      S.ordinary block innerSubgroup inner
    letI := brauerBlockQuotientAction iotaG (combinedAut G field action)
      block innerSubgroup inner
    DecompositionNatural
      (A := MulAction.stabilizer (Ambient field) block ⧸ innerSubgroup)
      (decompositionMapOfStableReduction S.modularSystem iotaG S.reductionCompatible)
      actions.ordinaryAction actions.modularAction

attribute [instance] BlockSourceInputs.innerNormal BlockSourceInputs.smallNormal_normal

variable (blockInputs : ∀ block : LiteralPrimitiveBlock k G,
  BlockSourceInputs G field action iotaG hinjG blocks S
    (CyclicTarget := CyclicTarget) block)

/-- A constructed global bijection with exact character actions and blocks. -/
structure GlobalBijection where
  beta : IBr iotaG ≃ {chi : Irr K G // S.ordinary.predicate chi}
  equivariant : ∀ (a : Ambient field) (phi : IBr iotaG),
    beta (IrreducibleBrauerCharacter.twist iotaG phi
        ((combinedAut G field action) a⁻¹)) =
      ⟨ordinaryAutomorphismAct (combinedAut G field action) a (beta phi).1,
        S.ordinary.predicate_stable a (beta phi).1 (beta phi).2⟩
  block_preserving : ∀ phi,
    S.ordinary.blockOf (beta phi) = irreducibleBrauerCharacterBlock iotaG hinjG blocks phi

/-- Construct the global bijection in the order of the proof: apply the block
basic set theorem, choose orbit representatives, and transport their
bijections. No stabiliser separation is used here. -/
def globalBijection : GlobalBijection G field action iotaG hinjG blocks S := by
  let rho := combinedAut G field action
  letI : MulAction (Ambient field) {chi : Irr K G // S.ordinary.predicate chi} :=
    S.ordinary.mulAction rho
  letI : MulAction (Ambient field) (IBr iotaG) :=
    EvenFieldAssumption53Relative.rightAutomorphismAction iotaG rho
  have localExists : RepresentativeEquivExists
      (A := Ambient field) (irreducibleBrauerCharacterBlock iotaG hinjG blocks)
      S.ordinary.blockOf S.brauerBlockEquivariant := by
    intro orbit
    let b := orbitRepresentative orbit
    let B := blockInputs b
    obtain ⟨beta, equivariant⟩ := actual_block_basic_set_bijection_relative
      iotaG hinjG rho S.ordinary blocks b
      (BasicSetSource.basicSet G field action iotaG hinjG blocks S)
      S.blockDiagonal S.brauerBlockEquivariant B.innerSubgroup B.inner
      B.smallNormal B.small_card B.quotientEmbedding B.quotientEmbedding_injective
      B.conlon B.burnside B.actions B.reductionNatural
    refine ⟨beta, ?_⟩
    intro a ha phi
    exact congrArg Subtype.val (equivariant a ha phi)
  let R := RepresentativeEquivFamily.ofExists
    (A := Ambient field) (irreducibleBrauerCharacterBlock iotaG hinjG blocks)
    S.ordinary.blockOf S.brauerBlockEquivariant localExists
  exact {
    beta := RepresentativeEquivFamily.globalEquiv
      (A := Ambient field) _ _ S.brauerBlockEquivariant S.ordinary.block_equivariant R
    equivariant := RepresentativeEquivFamily.globalEquiv_equivariant
      (A := Ambient field) _ _ S.brauerBlockEquivariant S.ordinary.block_equivariant R
    block_preserving := RepresentativeEquivFamily.globalEquiv_block_preserving
      (A := Ambient field) _ _ S.brauerBlockEquivariant S.ordinary.block_equivariant R }

variable (B : GlobalBijection G field action iotaG hinjG blocks S)

omit [Finite E] in
/-- The actual ambient action is onto Aut(G), so the constructed map is
equivariant for every automorphism, on the original character functions. -/
theorem GlobalBijection.automorphism_equivariant
    (surjective : Function.Surjective action.hom)
    (alpha : MulAut G) (phi : IBr iotaG) :
    (B.beta (IrreducibleBrauerCharacter.twist iotaG phi alpha)).1 =
      OrdinaryIrreducibleCharacter.twist K G (B.beta phi).1 alpha := by
  obtain ⟨a, ha⟩ := surjective alpha⁻¹
  have h : combinedAut G field action a⁻¹ = alpha := by
    rw [combinedAut_eq, map_inv, ha, inv_inv]
  simpa only [ordinaryAutomorphismAct, h] using
    congrArg Subtype.val (B.equivariant a phi)

include B in
/-- The direct global equivariant transfer used by the proof. The only
separation input concerns ordinary characters. -/
theorem GlobalBijection.allBrauerFactorization
    (ordinarySeparation : ∀ (chi : Irr K G) (m : M) (e : E),
      ordinaryAutomorphismAct (combinedAut G field action) (SemidirectProduct.inl m)
          (ordinaryAutomorphismAct (combinedAut G field action)
            (SemidirectProduct.inr e) chi) = chi ↔
        ordinaryAutomorphismAct (combinedAut G field action)
            (SemidirectProduct.inl m) chi = chi ∧
          ordinaryAutomorphismAct (combinedAut G field action)
            (SemidirectProduct.inr e) chi = chi)
    (phi : IBr iotaG) : BrauerFactorization G field action iotaG phi := by
  let rho := combinedAut G field action
  let : MulAction (Ambient field) {chi : Irr K G // S.ordinary.predicate chi} :=
    S.ordinary.mulAction rho
  let : MulAction (Ambient field) (IBr iotaG) :=
    EvenFieldAssumption53Relative.rightAutomorphismAction iotaG rho
  let : MulAction M {chi : Irr K G // S.ordinary.predicate chi} :=
    semidirectLeftRestrictedAction field
  let : MulAction E {chi : Irr K G // S.ordinary.predicate chi} :=
    semidirectRightRestrictedAction field
  let : MulAction M (IBr iotaG) := semidirectLeftRestrictedAction field
  let : MulAction E (IBr iotaG) := semidirectRightRestrictedAction field
  have hOrdinary : ProductStabilizerFactorization (D := M) (E := E) (B.beta phi) := by
    intro m e
    constructor
    · intro h
      obtain ⟨hm, he⟩ := (ordinarySeparation (B.beta phi).1 m e).mp
        (congrArg Subtype.val h)
      exact ⟨Subtype.ext hm, Subtype.ext he⟩
    · rintro ⟨hm, he⟩
      rw [he, hm]
  have h := brauerFactorization_of_ordinaryFactorization B.beta
    (fun m phi => B.equivariant (SemidirectProduct.inl m) phi)
    (fun e phi => B.equivariant (SemidirectProduct.inr e) phi) phi hOrdinary
  apply brauerFactorization_of_productFormula G field action iotaG phi
  intro m e
  have hf := h m e
  change
    IrreducibleBrauerCharacter.twist iotaG
        (IrreducibleBrauerCharacter.twist iotaG phi
          ((combinedAut G field action) (SemidirectProduct.inr e)⁻¹))
        ((combinedAut G field action) (SemidirectProduct.inl m)⁻¹) = phi ↔
      IrreducibleBrauerCharacter.twist iotaG phi
          ((combinedAut G field action) (SemidirectProduct.inl m)⁻¹) = phi ∧
        IrreducibleBrauerCharacter.twist iotaG phi
          ((combinedAut G field action) (SemidirectProduct.inr e)⁻¹) = phi at hf
  simpa only [combinedAut_eq, actualBrauerAct] using hf

end BasicSetApplication

section OrdinarySource

open TypeCOddPrimeConformalCriterionCarriers

/-- Cabanes–Späth (2017), Theorem 3.1, pp.63–64, on ordinary complex characters
of the actual matrix group. Inverse field and diagonal elements range over
the same groups as in the printed equality. No modular prime, Brauer
character, basic set or unitriangularity hypothesis occurs. -/
structure CabanesSpath31Certificate : Prop where
  separates : ∀ (n : ℕ) (F : Type) [Field F] [Finite F]
      [(SpSubgroup n F).Normal],
    0 < n → Odd (Nat.card F) → ∀ (chi : Irr ℂ (SpSubgroup n F))
      (m : OddTwoConformalProjectiveRealisation.CSp n F) (e : F ≃+* F),
    ordinaryAutomorphismAct (naturalAction n F).hom (SemidirectProduct.inr e) chi =
        ordinaryAutomorphismAct (naturalAction n F).hom (SemidirectProduct.inl m) chi →
      ordinaryAutomorphismAct (naturalAction n F).hom (SemidirectProduct.inr e) chi = chi ∧
        ordinaryAutomorphismAct (naturalAction n F).hom (SemidirectProduct.inl m) chi = chi

variable (n : ℕ) (F : Type) [Field F] [Finite F] [(SpSubgroup n F).Normal]
variable (source : CabanesSpath31Certificate) (structural : StructuralSource n F)

include source structural in
/-- The equality in Theorem 3.1 gives the product form used in the proof. -/
theorem complexOrdinarySeparation (chi : Irr ℂ (SpSubgroup n F))
    (m : OddTwoConformalProjectiveRealisation.CSp n F) (e : F ≃+* F) :
    ordinaryAutomorphismAct (naturalAction n F).hom (SemidirectProduct.inl m)
        (ordinaryAutomorphismAct (naturalAction n F).hom
          (SemidirectProduct.inr e) chi) = chi ↔
      ordinaryAutomorphismAct (naturalAction n F).hom (SemidirectProduct.inl m) chi = chi ∧
        ordinaryAutomorphismAct (naturalAction n F).hom (SemidirectProduct.inr e) chi = chi := by
  let : MulAction (Ambient (fieldAction n F)) (Irr ℂ (SpSubgroup n F)) :=
    OrdinaryAction.rightAutomorphismAction (naturalAction n F).hom
  let : MulAction (OddTwoConformalProjectiveRealisation.CSp n F)
      (Irr ℂ (SpSubgroup n F)) := semidirectLeftRestrictedAction (fieldAction n F)
  let : MulAction (F ≃+* F) (Irr ℂ (SpSubgroup n F)) :=
    semidirectRightRestrictedAction (fieldAction n F)
  change m • (e • chi) = chi ↔ m • chi = chi ∧ e • chi = chi
  constructor
  · intro h
    have hf : e • chi = m⁻¹ • chi := by
      simpa only [inv_smul_smul] using congrArg (fun psi => m⁻¹ • psi) h
    have hn := structural.rank
    obtain ⟨he, hm⟩ := source.separates n F (by omega) structural.field_odd chi m⁻¹ e hf
    change e • chi = chi at he
    change m⁻¹ • chi = chi at hm
    have hm' := congrArg (fun psi => m • psi) hm
    exact ⟨by simpa only [smul_inv_smul] using hm'.symm, he⟩
  · rintro ⟨hm, he⟩
    rw [he, hm]

variable {K : Type} [Field K] [CharZero K]

include source structural in
/-- The character identities over the common field transport the ordinary
theorem to K. -/
theorem ordinarySeparation (R : OddRationalSeries.Symplectic n F K)
    (chi : Irr K (SpSubgroup n F))
    (m : OddTwoConformalProjectiveRealisation.CSp n F) (e : F ≃+* F) :
    ordinaryAutomorphismAct (combinedAut (SpSubgroup n F) (fieldAction n F)
        (naturalAction n F)) (SemidirectProduct.inl m)
        (ordinaryAutomorphismAct (combinedAut (SpSubgroup n F) (fieldAction n F)
          (naturalAction n F)) (SemidirectProduct.inr e) chi) = chi ↔
      ordinaryAutomorphismAct (combinedAut (SpSubgroup n F) (fieldAction n F)
          (naturalAction n F)) (SemidirectProduct.inl m) chi = chi ∧
        ordinaryAutomorphismAct (combinedAut (SpSubgroup n F) (fieldAction n F)
          (naturalAction n F)) (SemidirectProduct.inr e) chi = chi := by
  simp only [combinedAut_eq]
  have transport (a : Ambient (fieldAction n F)) (theta : Irr K (SpSubgroup n F)) :
      R.complexCharacter (ordinaryAutomorphismAct (naturalAction n F).hom a theta) =
        ordinaryAutomorphismAct (naturalAction n F).hom a (R.complexCharacter theta) :=
    R.complexCharacter_twist theta ((naturalAction n F).hom a⁻¹)
  constructor
  · intro h
    have hc := congrArg R.complexCharacter h
    rw [transport, transport] at hc
    obtain ⟨hm, he⟩ := (complexOrdinarySeparation n F source structural
      (R.complexCharacter chi) m e).mp hc
    exact ⟨R.complexCharacter_injective ((transport _ _).trans hm),
      R.complexCharacter_injective ((transport _ _).trans he)⟩
  · rintro ⟨hm, he⟩
    rw [he, hm]

end OrdinarySource

end ManuscriptIBAW.TypeC.OddGlobalFactorization


/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
`docs/manuals/formalisation-companion.tex` and `audit/current/source-crosswalk.json`.
-/
