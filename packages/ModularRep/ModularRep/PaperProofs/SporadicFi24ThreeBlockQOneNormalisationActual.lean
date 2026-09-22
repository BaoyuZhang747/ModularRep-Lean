import ModularRep.PaperProofs.SporadicFi24ThreeBlockCharacterTripleRetentionActual
import ModularRep.PaperProofs.SporadicDefectZeroWeightFibreActual

/-!
# Trivial-radical normalisation for the Fischer three block equivalence

The cancellation and automorphism-promotion route constructs a literal block
preserving equivalence without using the earlier blockwise construction or its
normalisation conclusion.  This module restricts that equivalence to one block
fibre and applies defect-zero uniqueness to derive its value at the trivial
radical subgroup.

The normalisation is a kernel deduction over the existing U/E1 defect-zero
interfaces.  The combined endpoint retains the E2/U character-triple boundary
of the preceding module.  It supplies no compatible extensions, intermediate
block equalities, Proposition 5.7, BAW, or iBAW conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24ThreeBlockQOneNormalisationActual

open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCharacterTripleRetentionActual
open ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual

universe u

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R :
  LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- A block-preserving global equivalence restricts to an equivalence on each
literal block fibre. -/
def threeBlockBlockEquiv
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (hblock : ∀ phi,
      R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi)
    (b : ActualBlock (k := k) (X := X)) :
    {phi : IBr iota // brauerBlock iota hinj blocks phi = b} ≃
    {w : WeightClass (p := 3) (K := K) (X := X) //
      R.1.weightBlock w = b} where
  toFun phi := ⟨Omega phi.1, (hblock phi.1).trans phi.2⟩
  invFun w := ⟨Omega.symm w.1, by
    calc
      brauerBlock iota hinj blocks (Omega.symm w.1) =
          R.1.weightBlock (Omega (Omega.symm w.1)) :=
        (hblock (Omega.symm w.1)).symm
      _ = R.1.weightBlock w.1 := by
        rw [Omega.apply_symm_apply]
      _ = b := w.2⟩
  left_inv phi := by
    apply Subtype.ext
    exact Omega.symm_apply_apply phi.1
  right_inv w := by
    apply Subtype.ext
    exact Omega.apply_symm_apply w.1

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Literal block preservation and uniqueness in a defect-zero block force the
value of the global equivalence at every canonical defect-zero reduction. -/
theorem threeBlock_literal_qOne_normalisation
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (hblock : ∀ phi,
      R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X)) :
    Omega (D.reduce (iota := iota) d) = T.atOne d := by
  let b := brauerBlock iota hinj blocks (D.reduce (iota := iota) d)
  let e := threeBlockBlockEquiv iota hinj blocks Omega hblock b
  change (e ⟨D.reduce (iota := iota) d, rfl⟩).1 = T.atOne d
  let x : {phi : IBr iota //
      brauerBlock iota hinj blocks phi = b} :=
    ⟨D.reduce (iota := iota) d, rfl⟩
  let y : {w : WeightClass (p := 3) (K := K) (X := X) //
      R.1.weightBlock w = b} :=
    ⟨T.atOne d, C.block_atOne d⟩
  have hpre : e.symm y = x := by
    apply Subtype.ext
    exact DefectZeroOrdinaryBlockSource.uniqueBrauer
      (iota := iota) (hinj := hinj) (blocks := blocks)
      D B d (e.symm y).1 (e.symm y).2
  have hxy : e x = y := by
    rw [← hpre, e.apply_symm_apply]
  exact congrArg Subtype.val hxy

/-- The fully automorphism-equivariant three block equivalence retains the
character-triple clause and satisfies the literal `Q = 1` normalisation after
the exact external and defect-zero sources have been supplied. -/
theorem exists_threeBlockAutEquivariantEquiv_retaining_characterTriples_and_qOne
    (ModularCharacterTriple :
      IBr iota → WeightClass (p := 3) (K := K) (X := X) → Prop)
    (hCenter : Subgroup.center X = ⊥)
    (TripleSource : CharacterTripleRetentionSource
      (R := R) iota hinj blocks hCenter ModularCharacterTriple)
    (F : RawSectorFamily iota hinj blocks E1)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S)
    (OuterSource : C2OuterActionSource iota S)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
        Omega (alpha • phi) = alpha • Omega phi) ∧
      (∀ phi,
        R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi) ∧
      (∀ phi,
        weightSector (R := R) (Omega phi) =
          brauerSector iota hinj blocks phi) ∧
      (∀ phi,
        MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi =
          MulAction.stabilizer (MulAut X)ᵐᵒᵖ (Omega phi)) ∧
      (∀ phi, ModularCharacterTriple phi (Omega phi)) ∧
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        Omega (D.reduce (iota := iota) d) = T.atOne d) ∧
      (∀ phi : BrauerFibre iota hinj blocks S.nonprincipalBlock,
        Omega phi.1 = (Known.nonprincipal phi).1) ∧
      (∀ phi : BrauerFibre iota hinj blocks S.defectZeroBlock,
        Omega phi.1 = (Known.defectZero phi).1) := by
  obtain ⟨Omega, hOmega, hblock, hsector, hstabilizer, htriple,
      hnonprincipal, hdefectZero⟩ :=
    exists_threeBlockAutEquivariantEquiv_retaining_characterTriples
      (R := R) iota hinj blocks E1 ModularCharacterTriple hCenter
        TripleSource F S Known OuterSource
  have hqOne : ∀ d :
      GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d :=
    threeBlock_literal_qOne_normalisation
      (R := R) iota hinj blocks Omega hblock D T C B
  exact ⟨Omega, hOmega, hblock, hsector, hstabilizer, htriple,
    hqOne, hnonprincipal, hdefectZero⟩

end ModularRep.PaperProofs.SporadicFi24ThreeBlockQOneNormalisationActual



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
