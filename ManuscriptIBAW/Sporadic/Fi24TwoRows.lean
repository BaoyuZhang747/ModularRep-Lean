import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence

/-!
The Table 8 rows with the stated corrections on the actual weight conjugacy
classes. The central quotient and the fixed local characters use the same
classification, root restrictions, block operations, and automorphism square.
-/

noncomputable section
namespace ManuscriptIBAW.Sporadic.Fi24TwoRows
open ModularRep ModularRep.CharacterWeight ModularRep.PaperProofs
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedRadical
open SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo
open SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierLiftedRadicalIndex
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre

universe u v
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance subFinite (H : Subgroup X) : Fintype H := Fintype.ofFinite _
local instance quotientFinite : Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {iota : PrimeRegularRootEmbedding 2 k K X} {tau : MulAut X}
variable {Row : Fin 34 → Type v} {BlockD : Type u}
variable [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]

abbrev representative (T : TrivialOrdinaryTableData iota tau Row BlockD) (i : Fin 34) :=
  liftedRepresentative iota (Subgroup.center X) le_rfl T.primeToCenter T.catalogue i

def classOf (T : TrivialOrdinaryTableData iota tau Row BlockD) (i : Fin 34) :
    RadicalConjugacyClass (p := 2) (G := X) := Quotient.mk'' (representative T i)

def row (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
    (c : RadicalConjugacyClass (p := 2) (G := X))
    (w : WeightClass (p := 2) (K := K) (X := X)) : Prop :=
  weightSector (R := R) w = 1 ∧ radicalClass w = c

def fibreEquiv (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
    (Q : CharacterWeight.RadicalSubgroup (p := 2) (G := X)) :
    SectorWeightRadicalFibre R (Subgroup.center X) Q ≃
      {w // row R (Quotient.mk'' Q) w} where
  toFun w := ⟨w.1.1, (center_support_iff_weightSector_one R w.1.1).mp w.2, w.1.2⟩
  invFun w := ⟨⟨w.1, w.2.2⟩, (center_support_iff_weightSector_one R w.1).mpr w.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (T : TrivialOrdinaryTableData iota tau Row BlockD)
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)

def localRowEquiv (i : Fin 34) : Row i ≃ {w // row R (classOf T i) w} :=
  (catalogueSectorRowEquiv (R := R) (Z := Subgroup.center X) (iota := iota)
    (hcentral := le_rfl) (hprimeTo := T.primeToCenter) (C := T.catalogue)
    (OD := T.operationsD) (CU := T.reductionU) (CD := T.reductionD)
    (compatU := compatibility) (compatD := T.compatibilityD)
    (Sglobal := T.primitiveGlobal) (Slocal := T.primitiveLocal) i).trans
      (fibreEquiv R (representative T i))

include compatibility in
theorem row_total (i : Fin 34) :
    Nat.card {w // row R (classOf T i) w} = (T.entry i).total :=
  (Nat.card_congr (localRowEquiv R T compatibility i).symm).trans
    ((Nat.card_congr (T.catalogue.localEquiv i)).trans (T.total i))

include compatibility in
theorem row_finite (i : Fin 34) [Finite (Row i)] :
    Finite {w // row R (classOf T i) w} :=
  (localRowEquiv R T compatibility i).finite_iff.mp inferInstance

def fixedRowEquiv (i : Fin 34) :
    {w // row R (classOf T i) w ∧ MulOpposite.op tau • w = w} ≃
      T.catalogue.FixedLocalRow T.quotientAut ⟨i, T.classesFixed i⟩ := by
  let Q := representative T i
  have himage := fixedRadicalImage_lift iota (Subgroup.center X) le_rfl
    T.primeToCenter (T.catalogue.representative i)
  let CD : ∀ eta : LocalDefectZeroCharacter (K := K)
      (fixedRadicalImage iota (Subgroup.center X) le_rfl T.primeToCenter Q),
      CanonicalRawReduction (quotientRoot iota (Subgroup.center X))
        (characterWeightAt iota.prime _ eta) := by
    rw [himage]
    exact T.reductionD i
  let E := fixedSectorRadicalEquivCatalogueRow (R := R) (Z := Subgroup.center X)
    (Q := Q) (iota := iota) (hcentral := le_rfl) (hprimeTo := T.primeToCenter)
    (OD := T.operationsD) (CU := T.reductionU i) (CD := CD)
    (compatU := compatibility) (compatD := T.compatibilityD)
    (Sglobal := T.primitiveGlobal) (Slocal := T.primitiveLocal i)
    T.catalogue tau T.quotientAut T.square ⟨i, T.classesFixed i⟩ himage
  let Erow : {w : SectorWeightRadicalFibre R (Subgroup.center X) Q //
      MulOpposite.op tau • w.1.1 = w.1.1} ≃
      {w : {w // row R (classOf T i) w} // MulOpposite.op tau • w.1 = w.1} :=
    (fibreEquiv R Q).subtypeEquiv (fun _ => Iff.rfl)
  exact ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans Erow.symm).trans E

include compatibility in
theorem row_fixed (i : Fin 34) :
    Nat.card {w // row R (classOf T i) w ∧ MulOpposite.op tau • w = w} =
      (T.entry i).fixed :=
  (Nat.card_congr (fixedRowEquiv R T compatibility i)).trans
    ((Nat.card_congr (fixedLocalRowEquivActual T.catalogue T.quotientAut
      ⟨i, T.classesFixed i⟩)).trans (T.fixed ⟨i, T.classesFixed i⟩))

theorem classOf_injective : Function.Injective (classOf T) :=
  (liftedRepresentative_bijective iota (Subgroup.center X) le_rfl
    T.primeToCenter T.catalogue).1

theorem classOf_fixed (i : Fin 34) :
    MulOpposite.op tau • classOf T i = classOf T i := by
  apply (fixedRadicalImage_class_fixed_iff iota (Subgroup.center X) le_rfl
    T.primeToCenter tau T.quotientAut T.square (representative T i)).mpr
  simpa only [representative, fixedRadicalImage_lift] using T.classesFixed i

theorem row_stable (i : Fin 34) (w : WeightClass (p := 2) (K := K) (X := X))
    (hw : row R (classOf T i) w) : row R (classOf T i) (MulOpposite.op tau • w) := by
  constructor
  · rw [weightSector, R.1.weightBlock_transport, blockSector_transport]
    change MulOpposite.op tau • weightSector (R := R) w = 1
    rw [hw.1]
    rfl
  · rw [radicalClass_equivariant, hw.2, classOf_fixed T i]

end ManuscriptIBAW.Sporadic.Fi24TwoRows

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
