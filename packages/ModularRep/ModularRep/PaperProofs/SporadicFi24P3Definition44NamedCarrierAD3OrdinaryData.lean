import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda

/-! Ordinary central restriction and the same canonical local reduction,
with the actual normalizer-equivalence argument displayed. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAD3OrdinaryData

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [CharZero K] [Group G] [Fintype G]

def OrdinaryRowData (iota : PrimeRegularRootEmbedding p k K G)
    (nu mu : Subgroup.center G →* kˣ) (V : CharacterWeight p K G) : Prop :=
  (Nat.card (Subgroup.center G)).Coprime p ∧
  Function.Injective (ordinaryCentralLambda iota nu) ∧
  ordinaryCentralLambda iota mu = ordinaryCentralLambda iota nu ∧
  ∀ z : Subgroup.center G,
    centralRestriction V z = V.localCharacter 1 * ordinaryCentralLambda iota nu z

theorem ordinary_row_data [Fintype (Subgroup.center G)]
    [Invertible (Fintype.card (Subgroup.center G) : k)]
    (iota : PrimeRegularRootEmbedding p k K G) (nu mu : Subgroup.center G →* kˣ)
    (hnu : Function.Injective nu) (hmu : mu = nu)
    (Q : RadicalSubgroup (p := p) (G := G)) (theta : RootSectorLocal iota nu Q) :
    OrdinaryRowData iota nu mu (characterWeightAt iota.prime Q theta.val) :=
  ⟨center_order_coprime iota, ordinaryCentralLambda_faithful iota nu hnu,
    congrArg (ordinaryCentralLambda iota) hmu,
    rootSectorLocal_over_ordinaryCentralLambda iota nu Q theta⟩

variable [IsAlgClosed k]

def LocalOrdinaryRealization {L : Type u} [Group L] [Finite L]
    (iota : PrimeRegularRootEmbedding p k K G) (V : CharacterWeight p K G)
    (source : CanonicalRawReduction iota V)
    (eN : Subgroup.normalizer (V.subgroup : Set G) ≃* L) : Prop :=
  ∀ n : PrimeRegularElement (G := L) p,
    V.localCharacter (QuotientGroup.mk'
      (V.subgroup.subgroupOf (Subgroup.normalizer (V.subgroup : Set G))) (eN.symm n.val)) =
      (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer).val n

theorem local_ordinary_realization {L : Type u} [Group L] [Finite L]
    (iota : PrimeRegularRootEmbedding p k K G) (V : CharacterWeight p K G)
    (source : CanonicalRawReduction iota V)
    (eN : Subgroup.normalizer (V.subgroup : Set G) ≃* L) :
    LocalOrdinaryRealization iota V source eN :=
  along_localBrauer_reduction iota V source eN

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAD3OrdinaryData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
