import ModularRep.PaperProofs.SporadicDefectZeroWeightFibreActual
import ModularRep.PaperProofs.SporadicFi24ThreeBlockCarrierActual

/-!
# Source-shaped known fibres for the Fischer cancellation

This module derives the defect-zero member of the two known block-fibre
equivalences used in the `Fi'_{24}` cancellation.  It imports neither the
An--Dietrich sector construction nor a principal-block equivalence.

The literal identification of the published defect-zero block and the
nonprincipal cardinality and fixed-point census remain explicit source
boundaries. The complete equivalences and their equivariance are kernel
deductions from the generic defect-zero fibre theorem and the classification
of finite sets with an involution.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual

open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24QOneNormalisationActual
open SporadicFi24ThreeBlockCancellationActual

universe u

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-- Literal identification of the selected defect-zero ordinary character
with the defect-zero member of the three-block census.  It asserts no
character--weight equivalence. -/
structure Fi24DefectZeroBlockIdentification
    (D : DefectZeroReductionSource iota)
    (S : Fi24ThreeBlockSource (k := k) (X := X)) where
  character : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X)
  block_eq : S.defectZeroBlock =
    brauerBlock iota hinj blocks (D.reduce (iota := iota) character)

/-- The literal nonprincipal census used to construct an equivariant
equivalence. The two fields expose the cardinality and fixed-point signatures
that remain external; no equivalence is supplied. -/
structure Fi24NonprincipalCensusSource
    (S : Fi24ThreeBlockSource (k := k) (X := X)) where
  brauer_signature :
    (Nat.card (BrauerFibre iota hinj blocks S.nonprincipalBlock),
      Nat.card (Function.fixedPoints
        (nonprincipalBrauerPerm iota hinj blocks E1 S))) = (4, 2)
  weight_signature :
    (Nat.card (WeightFibre (R := R) S.nonprincipalBlock),
      Nat.card (Function.fixedPoints
        (nonprincipalWeightPerm (R := R) S))) = (4, 2)

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The literal nonprincipal census determines an equivariant equivalence of
the two finite sets with involution. -/
theorem exists_fi24NonprincipalFibreEquiv
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (NC : Fi24NonprincipalCensusSource iota hinj blocks E1 S) :
    ∃ equivalence :
        BrauerFibre iota hinj blocks S.nonprincipalBlock ≃
          WeightFibre (R := R) S.nonprincipalBlock,
      Formalisation.BlockCancellation.Intertwines equivalence
        (nonprincipalBrauerPerm iota hinj blocks E1 S)
        (nonprincipalWeightPerm (R := R) S) := by
  classical
  have hBrauerCardNat :
      Nat.card (BrauerFibre iota hinj blocks S.nonprincipalBlock) = 4 :=
    congrArg Prod.fst NC.brauer_signature
  have hWeightCardNat :
      Nat.card (WeightFibre (R := R) S.nonprincipalBlock) = 4 :=
    congrArg Prod.fst NC.weight_signature
  let _ : Finite (BrauerFibre iota hinj blocks S.nonprincipalBlock) :=
    Nat.finite_of_card_ne_zero (by rw [hBrauerCardNat]; decide)
  let _ : Finite (WeightFibre (R := R) S.nonprincipalBlock) :=
    Nat.finite_of_card_ne_zero (by rw [hWeightCardNat]; decide)
  let _ : Fintype (BrauerFibre iota hinj blocks S.nonprincipalBlock) :=
    Fintype.ofFinite _
  let _ : Fintype (WeightFibre (R := R) S.nonprincipalBlock) :=
    Fintype.ofFinite _
  apply Formalisation.C2Cancellation.exists_equivariantEquiv_of_card_eq_of_fixed_card_eq
  · exact brauerFibrePerm_involutive iota hinj blocks E1 S
      S.nonprincipalBlock S.nonprincipal_fixed
  · exact weightFibrePerm_involutive (R := R) S
      S.nonprincipalBlock S.nonprincipal_fixed
  · have hBrauer : Fintype.card
        (BrauerFibre iota hinj blocks S.nonprincipalBlock) = 4 := by
      simpa only [← Nat.card_eq_fintype_card] using hBrauerCardNat
    have hWeight : Fintype.card
        (WeightFibre (R := R) S.nonprincipalBlock) = 4 := by
      simpa only [← Nat.card_eq_fintype_card] using hWeightCardNat
    exact hBrauer.trans hWeight.symm
  · have hBrauer : Fintype.card (Function.fixedPoints
        (nonprincipalBrauerPerm iota hinj blocks E1 S)) = 2 := by
      simpa only [← Nat.card_eq_fintype_card] using
        congrArg Prod.snd NC.brauer_signature
    have hWeight : Fintype.card (Function.fixedPoints
        (nonprincipalWeightPerm (R := R) S)) = 2 := by
      simpa only [← Nat.card_eq_fintype_card] using
        congrArg Prod.snd NC.weight_signature
    exact hBrauer.trans hWeight.symm

/-- The nonprincipal equivalence selected from the literal census. -/
noncomputable def fi24NonprincipalFibreEquiv
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (NC : Fi24NonprincipalCensusSource iota hinj blocks E1 S) :
    BrauerFibre iota hinj blocks S.nonprincipalBlock ≃
      WeightFibre (R := R) S.nonprincipalBlock :=
  (exists_fi24NonprincipalFibreEquiv iota hinj blocks E1 S NC).choose

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The selected nonprincipal equivalence commutes with the outer
involution. -/
theorem fi24NonprincipalFibreEquiv_intertwines
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (NC : Fi24NonprincipalCensusSource iota hinj blocks E1 S) :
    Formalisation.BlockCancellation.Intertwines
      (fi24NonprincipalFibreEquiv iota hinj blocks E1 S NC)
      (nonprincipalBrauerPerm iota hinj blocks E1 S)
      (nonprincipalWeightPerm (R := R) S) :=
  (exists_fi24NonprincipalFibreEquiv iota hinj blocks E1 S NC).choose_spec

/-- The complete defect-zero block-fibre equivalence, derived from the raw
defect-group source fact and the literal block identification. -/
def fi24DefectZeroFibreEquiv
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (Z : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (F : Fi24DefectZeroBlockIdentification iota hinj blocks D S) :
    BrauerFibre iota hinj blocks S.defectZeroBlock ≃
      WeightFibre (R := R) S.defectZeroBlock := by
  rw [F.block_eq]
  exact defectZeroBlockFibreEquiv
    (iota := iota) (hinj := hinj) (blocks := blocks) (R := R)
    D T C B Z F.character

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The target defect-zero fibre is a singleton. -/
theorem fi24DefectZeroWeightFibre_subsingleton
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (Z : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (F : Fi24DefectZeroBlockIdentification iota hinj blocks D S) :
    Subsingleton (WeightFibre (R := R) S.defectZeroBlock) := by
  rw [F.block_eq]
  exact defectZeroWeightFibre_subsingleton
    (iota := iota) (hinj := hinj) (blocks := blocks) (R := R)
    D T C B Z F.character

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Any map between the two singleton defect-zero fibres commutes with the
selected outer involution. -/
theorem fi24DefectZeroFibreEquiv_intertwines
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (Z : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (F : Fi24DefectZeroBlockIdentification iota hinj blocks D S) :
    Formalisation.BlockCancellation.Intertwines
      (fi24DefectZeroFibreEquiv iota hinj blocks D T C B Z S F)
      (defectZeroBrauerPerm iota hinj blocks E1 S)
      (defectZeroWeightPerm (R := R) S) := by
  intro phi
  exact @Subsingleton.elim _
    (fi24DefectZeroWeightFibre_subsingleton
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R)
      D T C B Z S F) _ _

/-- The two known block-fibre equivalences required by cancellation. Both are
derived from source records that do not supply an equivalence. -/
def fi24ThreeKnownEquivalences
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (Z : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (F : Fi24DefectZeroBlockIdentification iota hinj blocks D S)
    (NC : Fi24NonprincipalCensusSource iota hinj blocks E1 S) :
    Fi24ThreeKnownEquivalences iota hinj blocks E1 S where
  nonprincipal := fi24NonprincipalFibreEquiv iota hinj blocks E1 S NC
  nonprincipal_intertwines :=
    fi24NonprincipalFibreEquiv_intertwines iota hinj blocks E1 S NC
  defectZero := fi24DefectZeroFibreEquiv
    (iota := iota) (hinj := hinj) (blocks := blocks) (R := R)
    D T C B Z S F
  defectZero_intertwines := fi24DefectZeroFibreEquiv_intertwines
    (iota := iota) (hinj := hinj) (blocks := blocks) (R := R) (E1 := E1)
    D T C B Z S F

end ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
