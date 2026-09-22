import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralRestrictionFormula
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly

/-!
# Ordinary rows over one retained-root central character combine its weights

The catalogue enumerates only ordinary local characters satisfying the
central restriction formula. Canonical reductions are available on all
local defect-zero characters, so the reverse implication applies to any
original weight. No global weight map is supplied.
-/

noncomputable section
open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralRestrictionFormula
open SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly

universe u v w
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharZero K] [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _

abbrev RootSectorLocal (iota : PrimeRegularRootEmbedding p k K X)
    (nu : CentralSector (k := k) (X := X))
    (Q : CharacterWeight.RadicalSubgroup (p := p) (G := X)) :=
  {theta : LocalDefectZeroCharacter (K := K) Q //
    ∀ z : Subgroup.center X,
      centralRestriction (characterWeightAt iota.prime Q theta) z =
        theta.1 1 * iota.lift (nu z : k)}

structure SectorCatalogue (iota : PrimeRegularRootEmbedding p k K X)
    (nu : CentralSector (k := k) (X := X)) (I : Type v) (Row : I → Type w) where
  representative : I → CharacterWeight.RadicalSubgroup (p := p) (G := X)
  radical_bijective : Function.Bijective (fun i =>
    (Quotient.mk'' (representative i) : RadicalConjugacyClass (p := p) (G := X)))
  ordinary : ∀ i, Row i → RootSectorLocal iota nu (representative i)
  ordinary_bijective : ∀ i, Function.Bijective (ordinary i)

namespace SectorCatalogue

variable {iota : PrimeRegularRootEmbedding p k K X}
variable {nu : CentralSector (k := k) (X := X)}
variable {I : Type v} {Row : I → Type w}

def localEquiv (C : SectorCatalogue iota nu I Row) (i : I) :
    Row i ≃ RootSectorLocal iota nu (C.representative i) :=
  Equiv.ofBijective (C.ordinary i) (C.ordinary_bijective i)

end SectorCatalogue

variable [CharP k p] [IsAlgClosed k]
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

abbrev WeightSectorRadicalFibre
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (nu : CentralSector (k := k) (X := X))
    (Q : CharacterWeight.RadicalSubgroup (p := p) (G := X)) :=
  {weight : WeightRadicalFibre (K := K) Q // weightSector (R := R) weight.1 = nu}

def rootSectorLocalToWeight
    (iota : PrimeRegularRootEmbedding p k K X)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (nu : CentralSector (k := k) (X := X))
    (Q : CharacterWeight.RadicalSubgroup (p := p) (G := X))
    (CU : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
      CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations) :
    RootSectorLocal iota nu Q ≃ WeightSectorRadicalFibre R nu Q :=
  (localDefectZeroEquivWeightRadicalFibre iota.prime Q).subtypeEquiv (fun theta => by
    rw [localDefectZeroEquivWeightRadicalFibre_apply_val]
    change (∀ z : Subgroup.center X,
        centralRestriction (characterWeightAt iota.prime Q theta) z =
          theta.1 1 * iota.lift (nu z : k)) ↔
      blockSector (R.1.operations.rawWeightBlock (characterWeightAt iota.prime Q theta)) = nu
    exact centralRestriction_eq_degree_mul_lift_iff_rawWeightSector_eq
      iota R (characterWeightAt iota.prime Q theta) (CU theta) compatibility nu)

def weightSectorRadicalUnionEquiv
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (nu : CentralSector (k := k) (X := X)) {I : Type v}
    (Q : I → CharacterWeight.RadicalSubgroup (p := p) (G := X))
    (hQ : Function.Bijective (fun i =>
      (Quotient.mk'' (Q i) : RadicalConjugacyClass (p := p) (G := X)))) :
    (Σ i : I, WeightSectorRadicalFibre R nu (Q i)) ≃
      {weight : WeightClass (p := p) (K := K) (X := X) // weightSector (R := R) weight = nu} := by
  let eQ : I ≃ RadicalConjugacyClass (p := p) (G := X) := Equiv.ofBijective _ hQ
  let F := {weight : WeightClass (p := p) (K := K) (X := X) //
    weightSector (R := R) weight = nu}
  let projection : F → RadicalConjugacyClass (p := p) (G := X) :=
    fun weight => radicalClass weight.1
  let E : (Σ i : I, WeightSectorRadicalFibre R nu (Q i)) ≃
      (Σ c : RadicalConjugacyClass (p := p) (G := X), {weight : F // projection weight = c}) :=
    Equiv.sigmaCongr eQ (fun i => swapNestedSubtype
      (fun weight : WeightClass (p := p) (K := K) (X := X) =>
        radicalClass weight = (Quotient.mk'' (Q i) : RadicalConjugacyClass (p := p) (G := X)))
      (fun weight : WeightClass (p := p) (K := K) (X := X) =>
        weightSector (R := R) weight = nu))
  exact E.trans (Equiv.sigmaFiberEquiv projection)

namespace SectorCatalogue

variable {iota : PrimeRegularRootEmbedding p k K X}
variable {nu : CentralSector (k := k) (X := X)}
variable {I : Type v} {Row : I → Type w}
variable (C : SectorCatalogue iota nu I Row)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (CU : ∀ i (theta : LocalDefectZeroCharacter (K := K) (C.representative i)),
  CanonicalRawReduction iota (characterWeightAt iota.prime (C.representative i) theta))
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)

def weightEquiv : (Σ i : I, Row i) ≃
    {weight : WeightClass (p := p) (K := K) (X := X) // weightSector (R := R) weight = nu} :=
  (Equiv.sigmaCongrRight (fun i => (C.localEquiv i).trans
    (rootSectorLocalToWeight iota R nu (C.representative i) (CU i) compatibility))).trans
      (weightSectorRadicalUnionEquiv R nu C.representative C.radical_bijective)

theorem weightEquiv_apply (x : Σ i : I, Row i) :
    (C.weightEquiv R CU compatibility x).1 =
      (Quotient.mk'' (Quotient.mk''
        (characterWeightAt iota.prime (C.representative x.1) (C.ordinary x.1 x.2).1) :
          CharacterWeight.IsoClass (p := p) (K := K) (G := X)) :
        CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X)) := by
  change (localDefectZeroEquivWeightRadicalFibre iota.prime
    (C.representative x.1) (C.ordinary x.1 x.2).1).1 = _
  exact localDefectZeroEquivWeightRadicalFibre_apply_val iota.prime
    (C.representative x.1) (C.ordinary x.1 x.2).1

include C CU compatibility in
theorem weightSector_finite [Finite I] [∀ i, Finite (Row i)] :
    Finite {weight : WeightClass (p := p) (K := K) (X := X) //
      weightSector (R := R) weight = nu} :=
  (C.weightEquiv R CU compatibility).finite_iff.mp inferInstance

include C CU compatibility in
theorem weightSector_card [Fintype I] [∀ i, Finite (Row i)] :
    Nat.card {weight : WeightClass (p := p) (K := K) (X := X) //
      weightSector (R := R) weight = nu} = ∑ i : I, Nat.card (Row i) :=
  (Nat.card_congr (C.weightEquiv R CU compatibility).symm).trans Nat.card_sigma

end SectorCatalogue
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
