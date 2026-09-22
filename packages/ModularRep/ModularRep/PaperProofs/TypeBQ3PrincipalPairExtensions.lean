import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualLocalInvariance
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions

/-!
# Two character extensions for the same principal matched pair

The finite group remains a parameter for the elementary constructions;
the principal consumer fixes the literal matrix Omega group over ZMod 3.
The actual Brauer stabilizer contains its inner copy, and the local ambient
is the normalizer of the image of the specified raw weight's radical.
Pair-class invariance proves invariance of that weight's local character.
The quotient bound and cyclic extension principle give both extensions,
retaining each transported base root and its finite-root agreement.
One ambient root seed supplies the two existence constructions.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalPairExtensions

open ModularRep CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualLocalInvariance
open SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance
open SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
open SporadicFi24P3Definition44NamedCarrierOwnNormalizerInvariance
  (stableNormalizerAut stableNormalizerAut_coe inflated_ordinary_fixed_of_isomorphic)
open Representation.Extension

variable {k K G : Type}
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

/-- The class of the specified raw weight on the unchanged finite group. -/
abbrev rawClass (W : CharacterWeight 2 K G) :
    ConjugacyClass (p := 2) (K := K) (G := G) :=
  Quotient.mk'' (Quotient.mk'' W)

variable (iota : PrimeRegularRootEmbedding 2 k K G) (phi : IBr iota)
  (W : CharacterWeight 2 K G)
  (pairFixed : ∀ alpha : MulAut G,
    MulOpposite.op alpha • phi = phi →
      MulOpposite.op alpha • rawClass W = rawClass W)

include pairFixed in
/-- Fixedness of the matched class and radical gives the same raw local data. -/
theorem raw_isomorphic_of_pair_fixed
    (alpha : MulAut G) (hfixed : MulOpposite.op alpha • phi = phi)
    (hQ : W.subgroup.comap alpha.toMonoidHom = W.subgroup) :
    CharacterWeight.Isomorphic (W.rightTwist alpha) W := by
  apply Quotient.exact (s := CharacterWeight.isomorphicSetoid)
  apply CyclicOuterRawPairNormalizer.isoClass_eq_of_conjugacyClass_eq_of_rawSubgroup_eq
  · exact pairFixed alpha hfixed
  · exact hQ

include pairFixed in
/-- The inflated ordinary character is fixed under this actual normalizer map. -/
theorem inflated_ordinary_fixed_of_pair_fixed
    (alpha : MulAut G) (hfixed : MulOpposite.op alpha • phi = phi)
    (hQ : W.subgroup.comap alpha.toMonoidHom = W.subgroup)
    (n : Subgroup.normalizer (W.subgroup : Set G)) :
    W.localCharacter (QuotientGroup.mk (stableNormalizerAut W.subgroup alpha hQ n)) =
      W.localCharacter (QuotientGroup.mk n) := by
  exact inflated_ordinary_fixed_of_isomorphic W alpha
    (raw_isomorphic_of_pair_fixed iota phi W pairFixed alpha hfixed hQ)
    n (stableNormalizerAut W.subgroup alpha hQ n)
    (stableNormalizerAut_coe W.subgroup alpha hQ n)

include pairFixed in
/-- The same canonical reduction inherits the ordinary fixedness equation. -/
theorem localBrauer_fixed_of_pair_fixed
    (source : CanonicalRawReduction iota W)
    (alpha : MulAut G) (hfixed : MulOpposite.op alpha • phi = phi)
    (hQ : W.subgroup.comap alpha.toMonoidHom = W.subgroup) :
    IrreducibleBrauerCharacter.twist source.normalizerRoot source.localBrauer
        (stableNormalizerAut W.subgroup alpha hQ) = source.localBrauer := by
  let alphaN := stableNormalizerAut W.subgroup alpha hQ
  apply Subtype.ext
  ext n
  change source.localBrauer.1 (PrimeRegularElement.map alphaN.toMonoidHom n) =
    source.localBrauer.1 n
  calc
    source.localBrauer.1 (PrimeRegularElement.map alphaN.toMonoidHom n) =
        W.localCharacter (QuotientGroup.mk (alphaN n.1)) :=
      (source.localBrauer_reduction _).symm
    _ = W.localCharacter (QuotientGroup.mk n.1) :=
      inflated_ordinary_fixed_of_pair_fixed
        iota phi W pairFixed alpha hfixed hQ n.1
    _ = source.localBrauer.1 n := source.localBrauer_reduction n

include pairFixed in
/-- The full embedded radical normalizer fixes the transported local character. -/
theorem actualLocalBrauer_fixed_of_pair_fixed
    (source : CanonicalRawReduction iota W) (hcenter : Subgroup.center G = ⊥)
    (d : embeddedNormalizer (innerEmbedding iota phi) W.subgroup) :
    let eN := normalizerBaseEquiv (innerEmbedding iota phi)
      (innerEmbedding_injective iota phi hcenter) W.subgroup
    IrreducibleBrauerCharacter.twist (source.normalizerRoot.alongMulEquiv eN)
        (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer)
        (MulAut.conjNormal d) =
      IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer := by
  let alpha := actualConjugation iota phi d.1
  let hQ := embedded_radical_stable iota phi hcenter W.subgroup d
  let alphaN := stableNormalizerAut W.subgroup alpha hQ
  let eN := normalizerBaseEquiv (innerEmbedding iota phi)
    (innerEmbedding_injective iota phi hcenter) W.subgroup
  change IrreducibleBrauerCharacter.twist (source.normalizerRoot.alongMulEquiv eN)
      (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer)
      (MulAut.conjNormal d) =
    IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer
  have hlocal : IrreducibleBrauerCharacter.twist source.normalizerRoot source.localBrauer
      alphaN = source.localBrauer :=
    localBrauer_fixed_of_pair_fixed iota phi W pairFixed source alpha
      (actualConjugation_brauer_fixed iota phi d.1) hQ
  have hconj : MulAut.congr eN alphaN = MulAut.conjNormal d :=
    normalizerBaseEquiv_congr_conjugation iota phi hcenter W.subgroup d
  have ht := IrreducibleBrauerCharacter.equivAlongMulEquiv_twist
    source.normalizerRoot eN source.localBrauer alphaN
  rw [hlocal, hconj] at ht
  exact ht.symm

/-- The literal inertia quotient bound gives the needed cyclicity. -/
theorem actual_quotient_cyclic_of_card_le_two
    (hquotientCard : Nat.card (ActualAutAmbient iota phi ⧸ actualBase iota phi) ≤ 2) :
    IsCyclic (ActualAutAmbient iota phi ⧸ actualBase iota phi) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < Nat.card (ActualAutAmbient iota phi ⧸ actualBase iota phi) :=
    Nat.card_pos
  have hcases : Nat.card (ActualAutAmbient iota phi ⧸ actualBase iota phi) = 1 ∨
      Nat.card (ActualAutAmbient iota phi ⧸ actualBase iota phi) = 2 := by
    omega
  apply isCyclic_of_card_dvd_prime (p := 2)
  rcases hcases with hone | htwo
  · simp only [hone, one_dvd]
  · simp only [htwo, dvd_refl]

variable (source : CanonicalRawReduction iota W)
  (hcenter : Subgroup.center G = ⊥)

local notation "A" => ActualAutAmbient iota phi
local notation "B" => actualBase iota phi
local notation "D" => embeddedNormalizer (innerEmbedding iota phi) W.subgroup
local notation "L" => embeddedLocalBase (innerEmbedding iota phi) W.subgroup
local notation "eG" => actualBaseEquiv iota phi hcenter
local notation "eN" => normalizerBaseEquiv (innerEmbedding iota phi)
  (innerEmbedding_injective iota phi hcenter) W.subgroup
local notation "rG" => iota.alongMulEquiv eG
local notation "phiG" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi
local notation "rL" => source.normalizerRoot.alongMulEquiv eN
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv
  source.normalizerRoot eN source.localBrauer

include pairFixed in
/-- Both actual characters extend, with their separate finite-root agreements. -/
theorem exists_pair_extensions
    (hquotientCard : Nat.card (A ⧸ B) ≤ 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (seed : PrimeRegularRootEmbedding 2 k K A) :
    ∃ rA : PrimeRegularRootEmbedding 2 k K A,
    ∃ rD : PrimeRegularRootEmbedding 2 k K D,
    ∃ globalExtension : BrauerCharacterExtensionWitness rA rG phiG,
    ∃ localExtension : BrauerCharacterExtensionWitness rD rL phiL,
      (∀ zeta : rootsOfUnity (primeRegularExponent 2 B) k,
        (rG).lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
      (∀ zeta : rootsOfUnity (primeRegularExponent 2 L) k,
        (rL).lift (((zeta : kˣ) : k)) = rD.lift (((zeta : kˣ) : k))) := by
  have hcyclicG : IsCyclic (A ⧸ B) :=
    actual_quotient_cyclic_of_card_le_two iota phi hquotientCard
  have hcyclicL : IsCyclic (D ⧸ L) :=
    local_quotient_isCyclic B D hcyclicG
  obtain ⟨rA, agreementG, ⟨globalExtension⟩⟩ :=
    exists_extensionWitness_with_retained_agreement (p := 2) (k := k) (K := K) («A» := A)
      B principle rG phiG hcyclicG
      (actualGlobalBaseFixed iota phi hcenter) seed
  obtain ⟨rD, agreementL, ⟨localExtension⟩⟩ :=
    exists_extensionWitness_with_retained_agreement (p := 2) (k := k) (K := K) («A» := D)
      L principle rL phiL hcyclicL
      (actualLocalBrauer_fixed_of_pair_fixed iota phi W pairFixed source hcenter)
      (seedOnSubgroup seed D)
  exact ⟨rA, rD, globalExtension, localExtension, agreementG, agreementL⟩

end ModularRep.PaperProofs.TypeBQ3PrincipalPairExtensions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
