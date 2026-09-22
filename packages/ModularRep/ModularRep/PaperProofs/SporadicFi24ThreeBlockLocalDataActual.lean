import ModularRep.PaperProofs.SporadicFi24ThreeBlockQOneNormalisationActual
import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre

/-!
# Radical-indexed local data for the Fischer three block equivalence

This module derives the radical partition and simultaneous block/radical
restrictions of an arbitrary literal character--weight equivalence.  For the
three block map constructed in the preceding modules, full automorphism
equivariance makes the partition equivariant, and the independently proved
`Q = 1` normalisation identifies its trivial-radical part.

These are kernel deductions.  They identify each block and radical fibre with
the corresponding representative-level local defect-zero set.  They do not
prove compatible extensions, intermediate block equalities, Proposition 5.7,
BAW, or iBAW.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24ThreeBlockLocalDataActual

open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCharacterTripleRetentionActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockQOneNormalisationActual
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

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Radical class of the weight matched with a Brauer character by the given
global equivalence. -/
def threeBlockPart
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (phi : IBr iota) : RadicalClass (p := 3) (X := X) :=
  weightRadical (Omega phi)

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Full automorphism equivariance of the global equivalence transports to
the radical partition. -/
theorem threeBlockPart_equivariant
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (alpha • phi) = alpha • Omega phi)
    (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    threeBlockPart iota Omega (alpha • phi) =
      alpha • threeBlockPart iota Omega phi := by
  unfold threeBlockPart
  rw [hOmega alpha phi, weightRadical_equivariant]

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The fibres of the transported radical map form a partition of the Brauer
characters. -/
def threeBlockPartitionEquiv
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X)) :
    IBr iota ≃ Sigma fun radical : RadicalClass (p := 3) (X := X) =>
      {phi : IBr iota // threeBlockPart iota Omega phi = radical} :=
  (Equiv.sigmaFiberEquiv (threeBlockPart iota Omega)).symm

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Restriction of a block-preserving equivalence simultaneously to one
literal block and one literal radical class. -/
def threeBlockLocalEquiv
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (hblock : ∀ phi,
      R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi)
    (b : ActualBlock (k := k) (X := X))
    (radical : RadicalClass (p := 3) (X := X)) :
    {phi : IBr iota //
      brauerBlock iota hinj blocks phi = b ∧
        weightRadical (Omega phi) = radical} ≃
    {w : WeightClass (p := 3) (K := K) (X := X) //
      R.1.weightBlock w = b ∧ weightRadical w = radical} where
  toFun phi := ⟨Omega phi.1, by
    exact ⟨(hblock phi.1).trans phi.2.1, phi.2.2⟩⟩
  invFun w := ⟨Omega.symm w.1, by
    constructor
    · calc
        brauerBlock iota hinj blocks (Omega.symm w.1) =
            R.1.weightBlock (Omega (Omega.symm w.1)) :=
          (hblock (Omega.symm w.1)).symm
        _ = R.1.weightBlock w.1 := by
          rw [Omega.apply_symm_apply]
        _ = b := w.2.1
    · rw [Omega.apply_symm_apply]
      exact w.2.2⟩
  left_inv phi := by
    apply Subtype.ext
    exact Omega.symm_apply_apply phi.1
  right_inv w := by
    apply Subtype.ext
    exact Omega.apply_symm_apply w.1

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Every canonical defect-zero reduction lies in the part indexed by the
literal trivial radical class. -/
theorem threeBlock_literal_qOne_part
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (hblock : ∀ phi,
      R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X)) :
    weightRadical (Omega (D.reduce (iota := iota) d)) =
      CharacterWeight.RadicalConjugacyClass.trivialClass
        T.trivialRadical := by
  calc
    weightRadical (Omega (D.reduce (iota := iota) d)) =
        CharacterWeight.radicalClass (T.atOne d) :=
      congrArg CharacterWeight.radicalClass
        (threeBlock_literal_qOne_normalisation
          (R := R) iota hinj blocks Omega hblock D T C B d)
    _ = CharacterWeight.RadicalConjugacyClass.trivialClass
          T.trivialRadical :=
      T.radicalClass_atOne d

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The part indexed by the trivial radical class consists exactly of the
canonical reductions of defect-zero ordinary characters. -/
theorem threeBlock_weightRadical_eq_trivial_iff
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (hblock : ∀ phi,
      R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (phi : IBr iota) :
    weightRadical (Omega phi) =
        CharacterWeight.RadicalConjugacyClass.trivialClass
          T.trivialRadical ↔
      ∃ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        D.reduce (iota := iota) d = phi := by
  constructor
  · intro hphi
    obtain ⟨d, hd⟩ :=
      T.exists_atOne_of_radicalClass_eq_trivial (Omega phi) hphi
    refine ⟨d, Omega.injective ?_⟩
    calc
      Omega (D.reduce (iota := iota) d) = T.atOne d :=
        threeBlock_literal_qOne_normalisation
          (R := R) iota hinj blocks Omega hblock D T C B d
      _ = Omega phi := hd
  · rintro ⟨d, rfl⟩
    exact threeBlock_literal_qOne_part
      (R := R) iota hinj blocks Omega hblock D T C B d

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Radical-fibre consequences attached to one retained global equivalence.
The canonical methods below return fibres of global weight classes, not
representative-level local defect-zero character sets. -/
structure ThreeBlockRadicalFibreData
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X) where
  omegaEquivariant :
    ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (alpha • phi) = alpha • Omega phi
  blockPreserving :
    ∀ phi, R.1.weightBlock (Omega phi) =
      brauerBlock iota hinj blocks phi
  qOneNormalisation :
    ∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d

namespace ThreeBlockRadicalFibreData

variable {Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X)}
variable {D : DefectZeroReductionSource iota}
variable {T : TrivialWeightSource 3 X}

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The canonical radical partition induced by the retained map. -/
def partition
    (_L : ThreeBlockRadicalFibreData
      (R := R) iota hinj blocks Omega D T) :
    IBr iota ≃ Sigma fun radical : RadicalClass (p := 3) (X := X) =>
      {phi : IBr iota // threeBlockPart iota Omega phi = radical} :=
  threeBlockPartitionEquiv iota Omega

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Equivariance of the induced radical partition. -/
theorem partEquivariant
    (L : ThreeBlockRadicalFibreData
      (R := R) iota hinj blocks Omega D T)
    (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    threeBlockPart iota Omega (alpha • phi) =
      alpha • threeBlockPart iota Omega phi :=
  threeBlockPart_equivariant iota Omega L.omegaEquivariant alpha phi

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Every canonical defect-zero reduction belongs to the part indexed by the
literal trivial radical class. -/
theorem qOnePart
    (L : ThreeBlockRadicalFibreData
      (R := R) iota hinj blocks Omega D T)
    (d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X)) :
    weightRadical (Omega (D.reduce (iota := iota) d)) =
      CharacterWeight.RadicalConjugacyClass.trivialClass
        T.trivialRadical := by
  calc
    weightRadical (Omega (D.reduce (iota := iota) d)) =
        CharacterWeight.radicalClass (T.atOne d) :=
      congrArg CharacterWeight.radicalClass (L.qOneNormalisation d)
    _ = CharacterWeight.RadicalConjugacyClass.trivialClass
          T.trivialRadical := T.radicalClass_atOne d

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The part indexed by the trivial radical class consists exactly of the
canonical reductions of defect-zero ordinary characters. -/
theorem trivialPartIff
    (L : ThreeBlockRadicalFibreData
      (R := R) iota hinj blocks Omega D T)
    (phi : IBr iota) :
    weightRadical (Omega phi) =
        CharacterWeight.RadicalConjugacyClass.trivialClass
          T.trivialRadical ↔
      ∃ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        D.reduce (iota := iota) d = phi := by
  constructor
  · intro hphi
    obtain ⟨d, hd⟩ :=
      T.exists_atOne_of_radicalClass_eq_trivial (Omega phi) hphi
    refine ⟨d, Omega.injective ?_⟩
    exact (L.qOneNormalisation d).trans hd
  · rintro ⟨d, rfl⟩
    exact qOnePart (R := R) iota hinj blocks L d

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Canonical simultaneous restriction by one block and radical class. -/
def blockRadicalRestriction
    (L : ThreeBlockRadicalFibreData
      (R := R) iota hinj blocks Omega D T)
    (b : ActualBlock (k := k) (X := X))
    (radical : RadicalClass (p := 3) (X := X)) :
    {phi : IBr iota //
      brauerBlock iota hinj blocks phi = b ∧
        weightRadical (Omega phi) = radical} ≃
    {w : WeightClass (p := 3) (K := K) (X := X) //
      R.1.weightBlock w = b ∧ weightRadical w = radical} :=
  threeBlockLocalEquiv (R := R) iota hinj blocks
    Omega L.blockPreserving b radical

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Restriction of the retained global equivalence to a block and a chosen
radical representative, followed by the kernel-derived identification with
the defect-zero characters of the representative normaliser quotient. -/
def representativeLocalEquiv
    (L : ThreeBlockRadicalFibreData
      (R := R) iota hinj blocks Omega D T)
    (b : ActualBlock (k := k) (X := X))
    (Q : RadicalSubgroup (p := 3) (X := X)) :
    {phi : IBr iota //
      brauerBlock iota hinj blocks phi = b ∧
        weightRadical (Omega phi) =
          (Quotient.mk'' Q : RadicalClass (p := 3) (X := X))} ≃
    CharacterWeight.RepresentativeDZ Nat.prime_three R.1 Q b :=
  (blockRadicalRestriction (R := R) iota hinj blocks L b
      (Quotient.mk'' Q : RadicalClass (p := 3) (X := X))).trans
    (CharacterWeight.representativeDZEquivWeightBlockRadicalFibre
      Nat.prime_three R.1 Q b).symm

end ThreeBlockRadicalFibreData

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Construct the exact radical-fibre package for the retained global map. -/
theorem threeBlockRadicalFibreData_of_retainedOmega
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (alpha • phi) = alpha • Omega phi)
    (hblock : ∀ phi,
      R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (hqOne : ∀ d : GlobalDefectZeroCharacter
        (p := 3) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d) :
    ThreeBlockRadicalFibreData
      (R := R) iota hinj blocks Omega D T where
  omegaEquivariant := hOmega
  blockPreserving := hblock
  qOneNormalisation := hqOne

/-- Combine the retained global equivalence, its `Q = 1` normalisation, and
the local radical-fibre package without assuming the character-triple
conclusion.  This does not remove the documented provenance of the supplied
raw fibre data. -/
theorem exists_threeBlockEquiv_retaining_qOne_localData_noTriple
    (E1 : RoutineTransportInput iota hinj blocks R)
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
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        Omega (D.reduce (iota := iota) d) = T.atOne d) ∧
      (∀ phi : BrauerFibre iota hinj blocks S.nonprincipalBlock,
        Omega phi.1 = (Known.nonprincipal phi).1) ∧
      (∀ phi : BrauerFibre iota hinj blocks S.defectZeroBlock,
        Omega phi.1 = (Known.defectZero phi).1) ∧
      ThreeBlockRadicalFibreData
        (R := R) iota hinj blocks Omega D T := by
  obtain ⟨Omega, hOmega, hblock, hnonprincipal, hdefectZero⟩ :=
    exists_threeBlockAutEquivariantEquiv
      (R := R) iota hinj blocks E1 F S Known OuterSource
  have hsector := same_sector_of_block_preserving
    (R := R) iota hinj blocks Omega hblock
  have hstabilizer := matched_stabilizers iota Omega hOmega
  have hqOne := threeBlock_literal_qOne_normalisation
    (R := R) iota hinj blocks Omega hblock D T C B
  have hlocal := threeBlockRadicalFibreData_of_retainedOmega
    (R := R) iota hinj blocks Omega hOmega hblock D T hqOne
  exact ⟨Omega, hOmega, hblock, hsector, hstabilizer, hqOne,
    hnonprincipal, hdefectZero, hlocal⟩

/-- The same global equivalence retains the character-triple and `Q = 1`
clauses and carries the canonically derived radical-fibre data. The final
conjunct concerns global weight classes, not representative-level local
`dz` sets. -/
theorem exists_threeBlockEquiv_retaining_localData
    (E1 : RoutineTransportInput iota hinj blocks R)
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
        Omega phi.1 = (Known.defectZero phi).1) ∧
      ThreeBlockRadicalFibreData
        (R := R) iota hinj blocks Omega D T := by
  obtain ⟨Omega, hOmega, hblock, hsector, hstabilizer, htriple,
      hqOne, hnonprincipal, hdefectZero⟩ :=
    exists_threeBlockAutEquivariantEquiv_retaining_characterTriples_and_qOne
      (R := R) iota hinj blocks E1 ModularCharacterTriple hCenter
        TripleSource F S Known OuterSource D T C B
  have hlocal : ThreeBlockRadicalFibreData
      (R := R) iota hinj blocks Omega D T :=
    threeBlockRadicalFibreData_of_retainedOmega
      (R := R) iota hinj blocks Omega hOmega hblock D T hqOne
  exact ⟨Omega, hOmega, hblock, hsector, hstabilizer, htriple,
    hqOne, hnonprincipal, hdefectZero, hlocal⟩

end ModularRep.PaperProofs.SporadicFi24ThreeBlockLocalDataActual



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
