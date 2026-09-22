import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSurjectiveRoot

/-!
# Canonical roots at the two fixed-quotient normalizers

Both normalizer roots restrict the original ambient root table. The local
surjection gives the source of restriction without a root-matching premise.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralNormalizerRoot

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierSurjectiveRoot

universe u

private theorem root_eq_of_table_eq
    {p : ℕ} {k K H : Type*} [Field k] [Field K] [Group H] [Finite H]
    (i j : PrimeRegularRootEmbedding p k K H) (h : i.toMulEquiv = j.toMulEquiv) :
    i = j := by
  cases i
  cases j
  cases h
  rfl

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]

local instance quotientFintype (Z : Subgroup G) [Z.Normal] : Fintype (G ⧸ Z) :=
  Fintype.ofFinite _

omit [CharP k p] [IsAlgClosed k] in
theorem fixedZ_normalizerRoot_eq
    (iota : PrimeRegularRootEmbedding p k K G) (Z : Subgroup G) [Z.Normal]
    (W : CharacterWeight p K G) (Wbar : CharacterWeight p K (G ⧸ Z))
    (fN : Subgroup.normalizer (W.subgroup : Set G) →*
      Subgroup.normalizer (Wbar.subgroup : Set (G ⧸ Z)))
    (hfN : Function.Surjective fN) :
    surjectiveRoot (normalizerRootAt iota W) fN hfN =
      normalizerRootAt (quotientRoot iota Z) Wbar := by
  rw [normalizerRootAt_eq_subgroupRoot, normalizerRootAt_eq_subgroupRoot]
  apply root_eq_of_table_eq
  apply MulEquiv.ext
  intro z
  apply Subtype.ext
  rfl

theorem fixedZ_sourceNormalizerRoot_eq
    (iota : PrimeRegularRootEmbedding p k K G) (Z : Subgroup G) [Z.Normal]
    (W : CharacterWeight p K G) (Wbar : CharacterWeight p K (G ⧸ Z))
    (source : CanonicalRawReduction iota W)
    (sourceBar : CanonicalRawReduction (quotientRoot iota Z) Wbar)
    (fN : Subgroup.normalizer (W.subgroup : Set G) →*
      Subgroup.normalizer (Wbar.subgroup : Set (G ⧸ Z)))
    (hfN : Function.Surjective fN) :
    surjectiveRoot source.normalizerRoot fN hfN = sourceBar.normalizerRoot := by
  rw [source.normalizerRoot_eq, sourceBar.normalizerRoot_eq]
  exact fixedZ_normalizerRoot_eq iota Z W Wbar fN hfN

theorem fixedZ_sourceNormalizerRoot_compatible
    (iota : PrimeRegularRootEmbedding p k K G) (Z : Subgroup G) [Z.Normal]
    (W : CharacterWeight p K G) (Wbar : CharacterWeight p K (G ⧸ Z))
    (source : CanonicalRawReduction iota W)
    (sourceBar : CanonicalRawReduction (quotientRoot iota Z) Wbar)
    (fN : Subgroup.normalizer (W.subgroup : Set G) →*
      Subgroup.normalizer (Wbar.subgroup : Set (G ⧸ Z)))
    (hfN : Function.Surjective fN)
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k (Subgroup.normalizer (Wbar.subgroup : Set (G ⧸ Z))) V) :
    Representation.BrauerRootLiftCompatibleAlong rho
      sourceBar.normalizerRoot source.normalizerRoot fN := by
  rw [← fixedZ_sourceNormalizerRoot_eq iota Z W Wbar source sourceBar fN hfN]
  exact surjectiveRoot_compatible source.normalizerRoot fN hfN rho

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralNormalizerRoot


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
