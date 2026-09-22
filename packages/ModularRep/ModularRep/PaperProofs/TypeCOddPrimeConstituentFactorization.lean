import ModularRep.PaperProofs.OddGFactorizationLemma312Relative
import ModularRep.PaperProofs.TypeBCriterionHypotheses

/-!
# Type C: the actual restriction constituent and Lemma 3.12 factorization

This module applies the existing Lemma 3.12 to the criterion's SAME natural
action, actual Brauer characters and specified primitive blocks. The exact
decomposition map and ordinary simple-module labels are constructed from
the displayed modular system. Only Li's ORDINARY stabilizer separation is
a source input; the conditional Brauer conclusion of Li 5.4 is not used.

A separate Navarro 2.2(d)/2.3 source supplies a nonzero nonnegative expansion
of literal restriction, with one explicit root agreement. K selects a
nonzero coefficient and combines it with the derived all-character Brauer
factorization. No constituent-with-factorization, Brauer bijection, final
criterion packet, Spin-specific source or iBAW conclusion is a premise.
-/

noncomputable section

open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeCOddPrimeConstituentFactorization

open ModularRep Formalisation
open FDRepSimpleClassKZero ExactGrothendieckGroup DecompositionBasicSetBridge
open BlockFibreRestriction OrdinaryIrreducibleCharacter
open OddConformalProposition311Relative OddGFactorizationLemma312Relative
open TypeBCriterionHypotheses NavarroCoveringBrauerExtension
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

section ActualAction

variable {M E : Type} [Group M] [Group E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)

/-- The conformal and field maps are restrictions of the given natural
homomorphism, not additional automorphism sources. -/
def conformalAut : M →* MulAut G := action.hom.comp SemidirectProduct.inl

def fieldAut : E →* MulAut G := action.hom.comp SemidirectProduct.inr

theorem naturalSemidirectCompatible : AutomorphismSemidirectCompatible field
    (conformalAut G field action) (fieldAut G field action) := by
  intro e
  apply MonoidHom.ext
  intro m
  change action.hom (SemidirectProduct.inl (field e m)) =
    action.hom (SemidirectProduct.inr e) *
      action.hom (SemidirectProduct.inl m) *
        (action.hom (SemidirectProduct.inr e))⁻¹
  rw [SemidirectProduct.inl_aut, map_mul, map_mul, map_inv, map_inv]

/-- The homomorphism used by Lemma 3.12 is combined from those exact two
restrictions. -/
def combinedAut : Ambient field →* MulAut G :=
  semidirectAutomorphismHom field (conformalAut G field action)
    (fieldAut G field action) (naturalSemidirectCompatible G field action)

theorem combinedAut_eq : combinedAut G field action = action.hom := by
  apply MonoidHom.ext
  intro a
  change action.hom (SemidirectProduct.inl a.left) *
      action.hom (SemidirectProduct.inr a.right) = action.hom a
  rw [← map_mul, SemidirectProduct.inl_left_mul_inr_right]

end ActualAction

section ActualBrauer

variable {ell : ℕ} {k K M E : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)
variable (iotaG : PrimeRegularRootEmbedding ell k K G)

/-- Actual inverse/right character action, written as a function to keep
the two source and criterion conventions independently inspectable. -/
def actualBrauerAct (a : Ambient field) (phi : IBr iotaG) : IBr iotaG :=
  IrreducibleBrauerCharacter.twist iotaG phi (action.hom a⁻¹)

def BrauerProductFormula (phi : IBr iotaG) : Prop :=
  ∀ (m : M) (e : E),
    actualBrauerAct G field action iotaG (SemidirectProduct.inl m)
        (actualBrauerAct G field action iotaG (SemidirectProduct.inr e) phi) = phi ↔
      actualBrauerAct G field action iotaG (SemidirectProduct.inl m) phi = phi ∧
        actualBrauerAct G field action iotaG (SemidirectProduct.inr e) phi = phi

/-- Elementwise separation gives the criterion's product of intersections
with the actual embedded M and E, with no image/factorization dictionary
left as a source premise. -/
theorem brauerFactorization_of_productFormula (phi : IBr iotaG)
    (product : BrauerProductFormula G field action iotaG phi) :
    BrauerFactorization G field action iotaG phi := by
  letI : MulAction (Ambient field) (IBr iotaG) :=
    EvenFieldAssumption53Relative.rightAutomorphismAction iotaG action.hom
  letI : MulAction M (IBr iotaG) := semidirectLeftRestrictedAction field
  letI : MulAction E (IBr iotaG) := semidirectRightRestrictedAction field
  have hproduct : ProductStabilizerFactorization (D := M) (E := E) phi := product
  let I := brauerInertia G field action iotaG phi
  change (I : Set (Ambient field)) =
    (↑(I ⊓ embeddedM field) : Set (Ambient field)) *
      (↑(I ⊓ embeddedE field) : Set (Ambient field))
  apply Set.Subset.antisymm
  · intro a ha
    have hfixed : a • phi = phi := ha
    rw [semidirectRestrictedAction_eq (X := IBr iotaG) field] at hfixed
    obtain ⟨hm, he⟩ := (hproduct a.left a.right).mp hfixed
    refine ⟨SemidirectProduct.inl a.left, ⟨hm, ⟨a.left, rfl⟩⟩,
      SemidirectProduct.inr a.right, ⟨he, ⟨a.right, rfl⟩⟩,
      SemidirectProduct.inl_left_mul_inr_right a⟩
  · rintro a ⟨m, hm, e, he, rfl⟩
    exact I.mul_mem hm.1 he.1

end ActualBrauer

section BasicSetApplication

variable {ell : ℕ} {K O k M E : Type}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
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

/-- The exact global basic-set inputs. Both the ordinary simple-module
labels and decomposition map are fixed constructions. The only stabilizer
source concerns ORDINARY characters, as in the first sentence of Li 5.4's
proof before unitriangularity enters. -/
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
          (TypeBSpecialCliffordActionAdapter.ordinarySeriesLabel
            (K := K) ordinary.predicate) v)
  blockDiagonal : BlockDiagonalLinearEquiv ordinary.blockOf
    (irreducibleBrauerCharacterBlock iotaG hinjG blocks) linearEquiv
  brauerBlockEquivariant : ∀ (a : Ambient field) (phi : IBr iotaG),
    irreducibleBrauerCharacterBlock iotaG hinjG blocks
        (IrreducibleBrauerCharacter.twist iotaG phi
          ((combinedAut G field action) a⁻¹)) =
      a • irreducibleBrauerCharacterBlock iotaG hinjG blocks phi
  ordinarySeparation : ∀ (chi : Irr K G) (m : M) (e : E),
    ordinaryAutomorphismAct (combinedAut G field action) (SemidirectProduct.inl m)
        (ordinaryAutomorphismAct (combinedAut G field action)
          (SemidirectProduct.inr e) chi) = chi ↔
      ordinaryAutomorphismAct (combinedAut G field action)
          (SemidirectProduct.inl m) chi = chi ∧
        ordinaryAutomorphismAct (combinedAut G field action)
          (SemidirectProduct.inr e) chi = chi

attribute [instance] BasicSetSource.finiteOrdinary

variable (S : BasicSetSource (O := O) G field action iotaG hinjG blocks)

/-- Package the integral source with its canonical ordinary and Brauer
simple-module labels and its actual stable-reduction decomposition map. -/
def BasicSetSource.basicSet : RestrictedIntegralBasicSetOnIBr iotaG hinjG
    {chi : Irr K G // S.ordinary.predicate chi}
    (decompositionMapOfStableReduction S.modularSystem iotaG S.reductionCompatible) :=
  TypeBSpecialCliffordActionAdapter.ordinarySeriesBasicSet
    S.modularSystem iotaG S.reductionCompatible hinjG S.ordinary.predicate
    S.linearEquiv S.decomposition

variable {CyclicTarget : Type} [Group CyclicTarget] [IsCyclic CyclicTarget]

/-- Source data on one specified block stabilizer. The actions descend
through its actual inner subgroup. None of the fields is a block-fibre
bijection or a Brauer-character stabilizer assertion. -/
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

/-- Invoke the protected Lemma 3.12 at this literal specified block. The
result is written in the SAME natural action used by the criterion. -/
theorem brauerProductFormula_at
    (block : LiteralPrimitiveBlock k G)
    (B : BlockSourceInputs G field action iotaG hinjG blocks S
      (CyclicTarget := CyclicTarget) block)
    (phi : IBr iotaG)
    (hphi : irreducibleBrauerCharacterBlock iotaG hinjG blocks phi = block) :
    BrauerProductFormula G field action iotaG phi := by
  let rhoA := combinedAut G field action
  letI : MulAction (Ambient field) {chi : Irr K G // S.ordinary.predicate chi} :=
    S.ordinary.mulAction rhoA
  letI : MulAction (Ambient field) (IBr iotaG) :=
    EvenFieldAssumption53Relative.rightAutomorphismAction iotaG rhoA
  letI : MulAction M {chi : Irr K G // S.ordinary.predicate chi} :=
    semidirectLeftRestrictedAction field
  letI : MulAction E {chi : Irr K G // S.ordinary.predicate chi} :=
    semidirectRightRestrictedAction field
  letI : MulAction M (IBr iotaG) := semidirectLeftRestrictedAction field
  letI : MulAction E (IBr iotaG) := semidirectRightRestrictedAction field
  letI : MulAction (MulAction.stabilizer (Ambient field) block ⧸ B.innerSubgroup)
      {chi : Irr K G // S.ordinary.predicate chi} :=
    ordinaryBasicBlockQuotientAction rhoA S.ordinary block B.innerSubgroup B.inner
  letI : MulAction (MulAction.stabilizer (Ambient field) block ⧸ B.innerSubgroup)
      (IBr iotaG) :=
    brauerBlockQuotientAction iotaG rhoA block B.innerSubgroup B.inner
  have hordinary : ∀ chi : Fibre S.ordinary.blockOf block,
      ProductStabilizerFactorization (D := M) (E := E) chi.1 := by
    intro chi m e
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      obtain ⟨hm, he⟩ := (S.ordinarySeparation chi.1.1 m e).mp hv
      exact ⟨Subtype.ext hm, Subtype.ext he⟩
    · rintro ⟨hm, he⟩
      rw [he, hm]
  obtain ⟨_beta, _equivariant, factorization⟩ :=
    lemma_3_12_factorization_relative iotaG hinjG field
      (conformalAut G field action) (fieldAut G field action)
      (naturalSemidirectCompatible G field action) S.ordinary blocks block
      (BasicSetSource.basicSet G field action iotaG hinjG blocks S) S.blockDiagonal
      S.brauerBlockEquivariant B.innerSubgroup B.inner B.smallNormal B.small_card
      B.quotientEmbedding B.quotientEmbedding_injective B.conlon B.burnside
      B.actions B.reductionNatural hordinary
  intro m e
  have h := factorization ⟨phi, hphi⟩ m e
  change
    IrreducibleBrauerCharacter.twist iotaG
        (IrreducibleBrauerCharacter.twist iotaG phi
          ((combinedAut G field action) (SemidirectProduct.inr e)⁻¹))
        ((combinedAut G field action) (SemidirectProduct.inl m)⁻¹) = phi ↔
      IrreducibleBrauerCharacter.twist iotaG phi
          ((combinedAut G field action) (SemidirectProduct.inl m)⁻¹) = phi ∧
        IrreducibleBrauerCharacter.twist iotaG phi
          ((combinedAut G field action) (SemidirectProduct.inr e)⁻¹) = phi at h
  simpa only [combinedAut_eq, actualBrauerAct] using h

/-- Every actual Brauer character is put in its own specified block before
applying Lemma 3.12. No representative-character family is supplied. -/
theorem allBrauerFactorization
    (blockInputs : ∀ block : LiteralPrimitiveBlock k G,
      BlockSourceInputs G field action iotaG hinjG blocks S
        (CyclicTarget := CyclicTarget) block)
    (phi : IBr iotaG) : BrauerFactorization G field action iotaG phi :=
  brauerFactorization_of_productFormula G field action iotaG phi
    (brauerProductFormula_at G field action iotaG hinjG blocks S
      (irreducibleBrauerCharacterBlock iotaG hinjG blocks phi)
      (blockInputs _) phi rfl)

end BasicSetApplication

section Restriction

variable {ell : ℕ} {k K M : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Group M] [Finite M]
variable (G : Subgroup M) [G.Normal]
variable (iotaM : PrimeRegularRootEmbedding ell k K M)
variable (iotaG : PrimeRegularRootEmbedding ell k K G)

/-- Navarro 2.2(d), 2.3 on literal restriction, with a single compatible
root convention. The source provides no chosen constituent and no inertia
condition. The nonzero vector expresses the nonzero restricted module. -/
structure RestrictionExpansionSource where
  roots : RootAgreement G iotaM iotaG
  multiplicity : IBr iotaM → IBr iotaG →₀ ℕ
  nonzero : ∀ Phi, multiplicity Phi ≠ 0
  value : ∀ (Phi : IBr iotaM) (x : PrimeRegularElement (G := G) ell),
    Phi.1 (PrimeRegularElement.map G.subtype x) =
      (multiplicity Phi).sum (fun phi m => (m : K) * phi.1 x)

/-- The same root agreement really identifies representation restriction
with class-function pullback along the actual subgroup inclusion. -/
theorem RestrictionExpansionSource.brauer_pullback
    (R : RestrictionExpansionSource G iotaM iotaG) (V : FDRep k M) :
    Representation.brauerCharacterOfRootEmbedding
        (Representation.pullback V.ρ G.subtype) iotaG =
      PrimeRegularClassFunction.pullback G.subtype
        (Representation.brauerCharacterOfRootEmbedding V.ρ iotaM) :=
  Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
    V.ρ iotaM iotaG G.subtype
    (Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
      V.ρ iotaM iotaG G.subtype R.roots)

/-- Select a nonzero coefficient of the actual finite nonnegative
restriction expansion and use the existing occurrence definition. -/
theorem exists_constituent (R : RestrictionExpansionSource G iotaM iotaG)
    (Phi : IBr iotaM) : ∃ phi : IBr iotaG,
      BrauerOccursInRestriction G iotaM iotaG Phi phi := by
  classical
  have hexists : ∃ phi, R.multiplicity Phi phi ≠ 0 := by
    by_contra h
    apply R.nonzero Phi
    ext phi
    exact not_not.mp (fun hphi => h ⟨phi, hphi⟩)
  obtain ⟨phi, hphi⟩ := hexists
  exact ⟨phi, R.multiplicity Phi, hphi, R.value Phi⟩

end Restriction

section CriterionConsumer

variable {ell : ℕ} {K O k M E CyclicTarget : Type}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
variable [Group M] [Finite M] [Group E] [Finite E]
variable [Group CyclicTarget] [IsCyclic CyclicTarget]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)

local instance consumerSubgroupFintype : Fintype G := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k G)]
variable [MulAction (Ambient field) (LiteralPrimitiveBlock k G)]
variable (iotaM : PrimeRegularRootEmbedding ell k K M)
variable (iotaG : PrimeRegularRootEmbedding ell k K G)
variable (hinjG : IrreducibleBrauerCharacterInjectivity iotaG)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k G => b.1))

/-- The complete constituent clause is derived from the exact basic-set,
ordinary, quotient-action and restriction inputs. Both outputs refer to the
SAME selected literal constituent and SAME natural action. -/
theorem constituentClause_of_lemma312
    (S : BasicSetSource (O := O) G field action iotaG hinjG blocks)
    (blockInputs : ∀ block : LiteralPrimitiveBlock k G,
      BlockSourceInputs G field action iotaG hinjG blocks S
        (CyclicTarget := CyclicTarget) block)
    (restriction : RestrictionExpansionSource G iotaM iotaG) :
    ConstituentClause G field action iotaM iotaG := by
  intro Phi
  obtain ⟨phi, hphi⟩ := exists_constituent G iotaM iotaG restriction Phi
  exact ⟨phi, hphi,
    allBrauerFactorization G field action iotaG hinjG blocks S blockInputs phi⟩

end CriterionConsumer

end ModularRep.PaperProofs.TypeCOddPrimeConstituentFactorization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
