import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Basic

/-!
# Exhaustive ordinary rows determine total and fixed weight classes

Only radical and ordinary character catalogues are supplied. The global
weight map, representative corrections and finite disjoint unions are
constructed internally. Empty local catalogues remain permitted.
-/

noncomputable section
open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
open TypeBCentralKernelNormalizerInertia

universe u v w

structure Catalogue (p : ℕ) (K G : Type u)
    [Field K] [CharZero K] [Group G] [Fintype G]
    (I : Type v) (Row : I → Type w) where
  prime : p.Prime
  representative : I → RadicalSubgroup (p := p) (G := G)
  radical_bijective : Function.Bijective
    (fun i => (Quotient.mk'' (representative i) : RadicalConjugacyClass (p := p) (G := G)))
  ordinary : ∀ i, Row i → LocalDefectZeroCharacter (K := K) (representative i)
  ordinary_bijective : ∀ i, Function.Bijective (ordinary i)

def swapNestedSubtype {A : Type*} (P R : A → Prop) :
    {a : {a : A // P a} // R a.1} ≃ {a : {a : A // R a} // P a.1} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter P R).trans
    ((Equiv.subtypeEquivRight (fun _ => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter R P).symm)

namespace Catalogue

variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Fintype G]
variable {I : Type v} {Row : I → Type w} (C : Catalogue p K G I Row)

def radicalEquiv : I ≃ RadicalConjugacyClass (p := p) (G := G) :=
  Equiv.ofBijective
    (fun i => (Quotient.mk'' (C.representative i) : RadicalConjugacyClass (p := p) (G := G)))
    C.radical_bijective

def localEquiv (i : I) : Row i ≃ LocalDefectZeroCharacter (K := K) (C.representative i) :=
  Equiv.ofBijective (C.ordinary i) (C.ordinary_bijective i)

def globalEquiv : (Σ i : I, Row i) ≃ ConjugacyClass (p := p) (K := K) (G := G) := by
  let E : (Σ i : I, Row i) ≃
      (Σ c : RadicalConjugacyClass (p := p) (G := G),
        {weight : ConjugacyClass (p := p) (K := K) (G := G) // radicalClass weight = c}) :=
    Equiv.sigmaCongr C.radicalEquiv (fun i => (C.localEquiv i).trans
      (localDefectZeroEquivWeightRadicalFibre C.prime (C.representative i)))
  exact E.trans (Equiv.sigmaFiberEquiv (radicalClass (p := p) (K := K) (G := G)))

theorem globalEquiv_apply (x : Σ i : I, Row i) :
    C.globalEquiv x = classAt C.prime (C.representative x.1) (C.ordinary x.1 x.2) := by
  change (localDefectZeroEquivWeightRadicalFibre C.prime
    (C.representative x.1) (C.ordinary x.1 x.2)).1 = _
  exact localDefectZeroEquivWeightRadicalFibre_apply_val
    C.prime (C.representative x.1) (C.ordinary x.1 x.2)

include C in
theorem weightClass_finite [Finite I] [∀ i, Finite (Row i)] :
    Finite (ConjugacyClass (p := p) (K := K) (G := G)) :=
  (C.globalEquiv).finite_iff.mp inferInstance

include C in
theorem weightClass_card [Fintype I] [∀ i, Finite (Row i)] :
    Nat.card (ConjugacyClass (p := p) (K := K) (G := G)) = ∑ i : I, Nat.card (Row i) :=
  (Nat.card_congr (C.globalEquiv).symm).trans Nat.card_sigma

abbrev FixedIndex (tau : MulAut G) :=
  {i : I // MulOpposite.op tau •
      (Quotient.mk'' (C.representative i) : RadicalConjugacyClass (p := p) (G := G)) =
    Quotient.mk'' (C.representative i)}

def correctionElement (tau : MulAut G) (i : C.FixedIndex tau) : G :=
  Classical.choose (exists_innerCorrection_of_fixed_radicalClass (C.representative i.1) tau i.2)

def correctedAut (tau : MulAut G) (i : C.FixedIndex tau) : MulAut G :=
  tau * MulAut.conj (C.correctionElement tau i)

theorem correctedStable (tau : MulAut G) (i : C.FixedIndex tau) :
    (C.representative i.1).1.comap (C.correctedAut tau i).toMonoidHom = (C.representative i.1).1 :=
  Classical.choose_spec
    (exists_innerCorrection_of_fixed_radicalClass (C.representative i.1) tau i.2)

abbrev FixedLocalRow (tau : MulAut G) (i : C.FixedIndex tau) :=
  {r : Row i.1 // OrdinaryIrreducibleCharacter.twist K _ (C.ordinary i.1 r).1
    (localAut (C.representative i.1).1 (C.correctedAut tau i) (C.correctedStable tau i)) =
      (C.ordinary i.1 r).1}

def fixedRowEquiv (tau : MulAut G) (i : C.FixedIndex tau) :
    C.FixedLocalRow tau i ≃
      {weight : WeightRadicalFibre (K := K) (C.representative i.1) //
        MulOpposite.op tau • weight.1 = weight.1} := by
  let E := (C.localEquiv i.1).trans
    (localDefectZeroEquivWeightRadicalFibre C.prime (C.representative i.1))
  refine E.subtypeEquiv ?_
  intro r
  change OrdinaryIrreducibleCharacter.twist K _ (C.ordinary i.1 r).1
      (localAut (C.representative i.1).1 (C.correctedAut tau i) (C.correctedStable tau i)) =
      (C.ordinary i.1 r).1 ↔
    MulOpposite.op tau • (localDefectZeroEquivWeightRadicalFibre C.prime
      (C.representative i.1) (C.ordinary i.1 r)).1 =
      (localDefectZeroEquivWeightRadicalFibre C.prime (C.representative i.1) (C.ordinary i.1 r)).1
  simpa only [localDefectZeroEquivWeightRadicalFibre_apply_val, classAt, correctedAut,
    innerCorrection_weight_smul] using
      (classAt_fixed_iff_local_fixed C.prime (C.representative i.1)
        (C.correctedAut tau i) (C.correctedStable tau i) (C.ordinary i.1 r)).symm

def fixedGlobalEquiv (tau : MulAut G) :
    (Σ i : C.FixedIndex tau, C.FixedLocalRow tau i) ≃
      {weight : ConjugacyClass (p := p) (K := K) (G := G) //
        MulOpposite.op tau • weight = weight} := by
  let W := ConjugacyClass (p := p) (K := K) (G := G)
  let F := {weight : W // MulOpposite.op tau • weight = weight}
  let J := {c : RadicalConjugacyClass (p := p) (G := G) // MulOpposite.op tau • c = c}
  let projection : F → RadicalConjugacyClass (p := p) (G := G) := fun weight => radicalClass weight.1
  have projection_fixed (weight : F) :
      MulOpposite.op tau • projection weight = projection weight := by
    change MulOpposite.op tau • radicalClass weight.1 = radicalClass weight.1
    rw [← radicalClass_equivariant (MulOpposite.op tau) weight.1, weight.2]
  let eIndex : C.FixedIndex tau ≃ J := C.radicalEquiv.subtypeEquiv (fun _ => Iff.rfl)
  let E : (Σ i : C.FixedIndex tau, C.FixedLocalRow tau i) ≃
      (Σ c : J, {weight : F // projection weight = c.1}) :=
    Equiv.sigmaCongr eIndex (fun i => (C.fixedRowEquiv tau i).trans
      (swapNestedSubtype
        (fun weight : W => radicalClass weight =
          (Quotient.mk'' (C.representative i.1) : RadicalConjugacyClass (p := p) (G := G)))
        (fun weight : W => MulOpposite.op tau • weight = weight)))
  exact E.trans (Equiv.sigmaSubtypeFiberEquiv projection
    (fun c : RadicalConjugacyClass (p := p) (G := G) => MulOpposite.op tau • c = c) projection_fixed)

local instance fixedIndexFintype [Finite I] (tau : MulAut G) : Fintype (C.FixedIndex tau) :=
  Fintype.ofFinite _

theorem fixedWeightClass_card [Fintype I] [∀ i, Finite (Row i)] (tau : MulAut G) :
    Nat.card {weight : ConjugacyClass (p := p) (K := K) (G := G) //
      MulOpposite.op tau • weight = weight} =
      ∑ i : C.FixedIndex tau, Nat.card (C.FixedLocalRow tau i) :=
  (Nat.card_congr (C.fixedGlobalEquiv tau).symm).trans Nat.card_sigma

end Catalogue
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
