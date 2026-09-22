import ModularRep.PaperProofs.TypeBCentralKernelBrauerInflation
import ModularRep.PaperProofs.TypeBCentralKernelWeightTransport
import ModularRep.BrauerReduction

/-!
# The actual local Brauer character of a transported weight

Navarro 3.18, pp. 61--62, supplies reduction of the actual ordinary
defect-zero character and its vanishing off the prime regular elements.
The coefficient fields are splitting fields and the root convention is
displayed. This is a routine E1/U source, with no block selector or matching.

Inflation to the normalizer and the quotient character square are proved
on actual normalizer representatives. Vanishing proves that Brauer reduction
reflects ordinary-character stabilizers, rather than assuming this reflection.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCentralKernelLocalReduction

open CharacterWeight TypeBCentralKernelBrauerInflation
open TypeBCentralKernelWeightTransport IrreducibleBrauerCharacterSurjectiveDescent

universe u

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G]

/-- Exact ordinary-to-Brauer character equality, with no block labels. -/
def Reduces {X : Type u} [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (chi : OrdinaryIrreducibleCharacter.Irr K X) (phi : IBr iota) : Prop :=
  ∀ x : PrimeRegularElement (G := X) p, chi x.val = phi.val x

/-- Uniform splitting-field form of Navarro 3.18. The fixed root determines
the actual modular function; no specified ordinary block selector occurs. -/
structure Navarro318Certificate (p : ℕ) (k K : Type u)
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [IsAlgClosed K] where
  reduction : ∀ (X : Type u) [Group X] [Finite X]
      (iota : PrimeRegularRootEmbedding p k K X)
      (chi : OrdinaryIrreducibleCharacter.Irr K X),
    IsDefectZeroOrdinaryCharacter p chi → ∃ phi : IBr iota, Reduces iota chi phi
  vanishes : ∀ (X : Type u) [Group X] [Finite X]
      (chi : OrdinaryIrreducibleCharacter.Irr K X),
    p.Prime → IsDefectZeroOrdinaryCharacter p chi →
      ∀ x : X, ¬ IsPrimeRegular p x → chi x = 0

theorem reduction_twist_reflects [IsAlgClosed K]
    (source : Navarro318Certificate p k K)
    (iota : PrimeRegularRootEmbedding p k K G)
    (chi : OrdinaryIrreducibleCharacter.Irr K G)
    (hchi : IsDefectZeroOrdinaryCharacter p chi) (phi : IBr iota)
    (reduction : Reduces iota chi phi) (alpha : MulAut G) :
    OrdinaryIrreducibleCharacter.twist K G chi alpha = chi ↔
      IrreducibleBrauerCharacter.twist iota phi alpha = phi := by
  constructor
  · intro h
    apply Subtype.ext
    ext x
    change phi.val (PrimeRegularElement.map alpha.toMonoidHom x) = phi.val x
    rw [← reduction, ← reduction]
    exact congrArg (fun c : OrdinaryIrreducibleCharacter.Irr K G => c x.val) h
  · intro h
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    change chi (alpha x) = chi x
    by_cases hx : IsPrimeRegular p x
    · have heq := congrArg (fun c : IBr iota => c.val ⟨x, hx⟩) h
      change phi.val (PrimeRegularElement.map alpha.toMonoidHom ⟨x, hx⟩) =
        phi.val ⟨x, hx⟩ at heq
      exact (reduction (PrimeRegularElement.map alpha.toMonoidHom ⟨x, hx⟩)).trans
        (heq.trans (reduction ⟨x, hx⟩).symm)
    · rw [source.vanishes G chi iota.prime hchi x hx,
        source.vanishes G chi iota.prime hchi (alpha x)
          (by simpa only [isPrimeRegular_map_mulEquiv] using hx)]

variable (W : CharacterWeight p K G)

abbrev normalizerKernel : Subgroup (Subgroup.normalizer (W.subgroup : Set G)) :=
  W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set G))

theorem normalizerKernel_isPGroup : IsPGroup p (normalizerKernel W) :=
  W.radical.isPGroup.comap_subtype

variable (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))

abbrev normalizerRoot : PrimeRegularRootEmbedding p k K
    (Subgroup.normalizer (W.subgroup : Set G)) :=
  upRoot (normalizerKernel W) (normalizerKernel_isPGroup W) iotaQ

/-- A specified quotient reduction is inflated by the literal quotient map. -/
def inflatedReduction (phiQ : IBr iotaQ) : IBr (normalizerRoot W iotaQ) :=
  (inflateToKernelTrivialIBrAlong (QuotientGroup.mk' (normalizerKernel W))
    (QuotientGroup.mk'_surjective _) (normalizerRoot W iotaQ) iotaQ
    (root_compatible (normalizerKernel W) (normalizerKernel_isPGroup W) iotaQ) phiQ).val

theorem inflatedReduction_value (phiQ : IBr iotaQ)
    (reduction : Reduces iotaQ W.localCharacter phiQ) :
    NormalizerInflatedReduction W.subgroup W.localCharacter (normalizerRoot W iotaQ)
      (inflatedReduction W iotaQ phiQ) := by
  intro x
  exact reduction (PrimeRegularElement.map (QuotientGroup.mk' (normalizerKernel W)) x)

def quotientReduction [IsAlgClosed K] (source : Navarro318Certificate p k K) : IBr iotaQ :=
  Classical.choose (source.reduction _ iotaQ W.localCharacter W.defectZero)

theorem quotientReduction_value [IsAlgClosed K] (source : Navarro318Certificate p k K) :
    Reduces iotaQ W.localCharacter (quotientReduction W iotaQ source) :=
  Classical.choose_spec (source.reduction _ iotaQ W.localCharacter W.defectZero)

/-- The actual normalizer Brauer character is constructed from the same
ordinary local character, with its exact inflation/reduction equation. -/
theorem exists_normalizer_reduction [IsAlgClosed K]
    (source : Navarro318Certificate p k K) :
    ∃ phi : IBr (normalizerRoot W iotaQ),
      NormalizerInflatedReduction W.subgroup W.localCharacter (normalizerRoot W iotaQ) phi :=
  ⟨inflatedReduction W iotaQ (quotientReduction W iotaQ source),
    inflatedReduction_value W iotaQ _ (quotientReduction_value W iotaQ source)⟩

/-- The actual quotient character equation follows from the local quotient
equivalence and the two reduction equations, without a naturality source. -/
theorem normalizer_reduction_quotient_square {H : Type u} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hker : IsPGroup p f.ker)
    (iotaUp : PrimeRegularRootEmbedding p k K (Subgroup.normalizer (W.subgroup : Set G)))
    (iotaDown : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer ((descend f hf hker W).subgroup : Set H)))
    (phiUp : IBr iotaUp) (phiDown : IBr iotaDown)
    (hUp : NormalizerInflatedReduction W.subgroup W.localCharacter iotaUp phiUp)
    (hDown : NormalizerInflatedReduction (descend f hf hker W).subgroup
      (descend f hf hker W).localCharacter iotaDown phiDown)
    (x : PrimeRegularElement (G := Subgroup.normalizer (W.subgroup : Set G)) p) :
    phiUp.val x = phiDown.val (PrimeRegularElement.map (normalizerMap f W.subgroup) x) := by
  rw [← hUp x, ← hDown (PrimeRegularElement.map (normalizerMap f W.subgroup) x)]
  exact (descend_localCharacter f hf hker W x.val (normalizerMap f W.subgroup x.val) rfl).symm

end ModularRep.PaperProofs.TypeBCentralKernelLocalReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
