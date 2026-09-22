import ModularRep.CharacterWeightBlockAssignment
import ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Relative
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# Equivariant transport on sets of characters and weights

This file constructs transport over an orbit of central sectors on the
library's function-valued irreducible Brauer characters and literal character
weights.  Blocks are primitive central idempotents, sectors are linear
characters of the centre, and radical labels are conjugacy classes of literal
radical subgroups.

Only the source-shaped data on one faithful sector, the classification of the
orbit of faithful sectors, and the character-triple predicate are supplied.
Lean constructs the transported equivalence and proves its independence of
transporters, full automorphism equivariance, preservation of sectors and
blocks, equivariance of the induced radical parts, and equality of matched
stabilisers.  The cyclic extension and factor-set implications are not
claimed as kernel deductions here.

The ambient block of a weight is the block obtained from the three literal
operations in `CharacterWeight.LocalBlockInductionSource`.  Thus the former
uninterpreted weight-block selector is not used by this instantiation.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Actual

open Formalisation
open Formalisation.IBAW
open ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Relative
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable {BlockIndex : Type u} [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

/- The actual source operations assigning an induced ambient block to a
literal character weight. -/
variable (blockSource : LiteralCarrierAdapter
  (p := p) (k := k) (K := K) (X := X))
variable (E1 : RoutineTransportInput iota hinj blocks blockSource)

private abbrev R := blockSource

/-- Literal faithful central characters of the centre. -/
abbrev FaithfulSector :=
  {nu : CentralSector (k := k) (X := X) // Function.Injective nu}

private theorem faithfulSector_smul
    (a : (MulAut X)ᵐᵒᵖ) (nu : FaithfulSector (k := k) (X := X)) :
    Function.Injective (a • (nu.1 : CentralSector (k := k) (X := X))) := by
  intro x y hxy
  apply (Representation.centerAutomorphism a.unop).injective
  apply nu.2
  exact hxy

/-- The automorphism action restricts to faithful central characters. -/
instance faithfulSectorMulAction :
    MulAction (MulAut X)ᵐᵒᵖ (FaithfulSector (k := k) (X := X)) where
  smul a nu := ⟨a • nu.1, faithfulSector_smul a nu⟩
  one_smul nu := by
    apply Subtype.ext
    exact one_smul _ _
  mul_smul a b nu := by
    apply Subtype.ext
    exact mul_smul a b nu.1

/-- Function-valued irreducible Brauer characters in faithful sectors.  The
transport record is a type parameter so that its action is inferable. -/
structure FaithfulIBr
    (E1 : RoutineTransportInput iota hinj blocks blockSource) where
  val : IBr iota
  faithful : Function.Injective (brauerSector iota hinj blocks val)

/-- Literal character-weight conjugacy classes in faithful sectors.  The
source and transport record occur in the type so that its action is
inferable. -/
structure FaithfulWeight
    (E1 : RoutineTransportInput iota hinj blocks blockSource) where
  val : WeightClass (p := p) (K := K) (X := X)
  faithful : Function.Injective (weightSector (R := R blockSource) val)

/-- The automorphism action restricts to the function-valued Brauer
characters in faithful sectors. -/
instance faithfulIBrMulAction :
    MulAction (MulAut X)ᵐᵒᵖ
      (FaithfulIBr iota hinj blocks blockSource E1) where
  smul a phi := ⟨a • phi.val, by
    rw [brauerSector_equivariant iota hinj blocks E1]
    exact faithfulSector_smul a
      ⟨brauerSector iota hinj blocks phi.val, phi.faithful⟩⟩
  one_smul phi := by
    cases phi
    rw [FaithfulIBr.mk.injEq]
    exact one_smul _ _
  mul_smul a b phi := by
    cases phi
    rw [FaithfulIBr.mk.injEq]
    exact mul_smul a b _

/-- The automorphism action restricts to literal weights in faithful
sectors. -/
instance faithfulWeightMulAction :
    MulAction (MulAut X)ᵐᵒᵖ
      (FaithfulWeight iota hinj blocks blockSource E1) where
  smul a w := ⟨a • w.val, by
    rw [weightSector_equivariant_actual
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := blockSource) E1]
    exact faithfulSector_smul a
      ⟨weightSector (R := blockSource) w.val, w.faithful⟩⟩
  one_smul w := by
    cases w
    rw [FaithfulWeight.mk.injEq]
    exact one_smul _ _
  mul_smul a b w := by
    cases w
    rw [FaithfulWeight.mk.injEq]
    exact mul_smul a b _

/-- Equality under the restricted action is exactly equality of the
underlying function-valued Brauer characters. -/
theorem faithfulIBr_smul_eq_iff (a : (MulAut X)ᵐᵒᵖ)
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    a • phi = phi ↔ a • phi.val = phi.val := by
  constructor
  · intro h
    exact congrArg (fun z => z.val) h
  · intro h
    cases phi
    rw [FaithfulIBr.mk.injEq]
    exact h

/-- Equality under the restricted action is exactly equality of the
underlying literal weight conjugacy classes. -/
theorem faithfulWeight_smul_eq_iff (a : (MulAut X)ᵐᵒᵖ)
    (w : FaithfulWeight iota hinj blocks blockSource E1) :
    a • w = w ↔ a • w.val = w.val := by
  constructor
  · intro h
    exact congrArg (fun z => z.val) h
  · intro h
    cases w
    rw [FaithfulWeight.mk.injEq]
    exact h

/-- Literal sector label on the faithful Brauer carrier. -/
def faithfulBrauerSector
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    FaithfulSector (k := k) (X := X) :=
  ⟨brauerSector iota hinj blocks phi.val, phi.faithful⟩

/-- Literal sector label on the faithful set of weights. -/
def faithfulWeightSector
    (w : FaithfulWeight iota hinj blocks blockSource E1) :
    FaithfulSector (k := k) (X := X) :=
  ⟨weightSector (R := R blockSource) w.val, w.faithful⟩

/-- Literal block label on the faithful Brauer carrier. -/
def faithfulBrauerBlock
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    ActualBlock (k := k) (X := X) :=
  brauerBlock iota hinj blocks phi.val

/-- Literal induced block label on the faithful set of weights. -/
def faithfulWeightBlock
    (w : FaithfulWeight iota hinj blocks blockSource E1) :
    ActualBlock (k := k) (X := X) :=
  blockSource.1.weightBlock w.val

/-- Literal radical conjugacy class of a faithful weight. -/
def faithfulWeightRadical
    (w : FaithfulWeight iota hinj blocks blockSource E1) :
    RadicalClass (p := p) (X := X) :=
  weightRadical w.val

variable (CharacterTripleOK :
  FaithfulIBr iota hinj blocks blockSource E1 →
    FaithfulWeight iota hinj blocks blockSource E1 → Prop)

/- Exact automorphism naturality of the source's character-triple
predicate. -/
variable (characterTriple_equivariant :
  Formalisation.IBAW.PairPropertyEquivariant
    (A := (MulAut X)ᵐᵒᵖ)
    (X := FaithfulIBr iota hinj blocks blockSource E1)
    (Y := FaithfulWeight iota hinj blocks blockSource E1) CharacterTripleOK)

/-- The abstract replacement context instantiated on literal manuscript
carriers. -/
def actualReplacementContext : ReplacementContext
    (A := (MulAut X)ᵐᵒᵖ)
    (Sector := FaithfulSector (k := k) (X := X))
    (Block := ActualBlock (k := k) (X := X))
    (Radical := RadicalClass (p := p) (X := X))
    (Brauer := FaithfulIBr iota hinj blocks blockSource E1)
    (Weight := FaithfulWeight iota hinj blocks blockSource E1) where
  brauerSector := faithfulBrauerSector iota hinj blocks blockSource E1
  weightSector := faithfulWeightSector iota hinj blocks blockSource E1
  brauerBlock := faithfulBrauerBlock iota hinj blocks blockSource E1
  weightBlock := faithfulWeightBlock iota hinj blocks blockSource E1
  weightRadical := faithfulWeightRadical iota hinj blocks blockSource E1
  brauerSector_equivariant a phi := by
    apply Subtype.ext
    exact brauerSector_equivariant iota hinj blocks
      E1 a phi.val
  weightSector_equivariant a w := by
    apply Subtype.ext
    exact weightSector_equivariant_actual
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R blockSource) E1 a w.val
  brauerBlock_equivariant a phi :=
    brauerBlock_transport iota hinj blocks a phi.val
  weightBlock_equivariant a w :=
    blockSource.1.weightBlock_transport a w.val
  weightRadical_equivariant a w :=
    weightRadical_equivariant a w.val
  characterTripleOK := CharacterTripleOK
  characterTriple_equivariant := characterTriple_equivariant

private abbrev C := actualReplacementContext iota hinj blocks blockSource E1
  CharacterTripleOK characterTriple_equivariant

/-- The exact source data used from An--Dietrich on one faithful sector.
There is no global equivalence or combined family in this structure. -/
structure AnDietrichFaithfulSectorSource where
  baseSector : FaithfulSector (k := k) (X := X)
  transporter : FaithfulSector (k := k) (X := X) → (MulAut X)ᵐᵒᵖ
  transporter_spec : ∀ sector,
    transporter sector • baseSector = sector
  baseEquiv :
    Fibre (faithfulBrauerSector iota hinj blocks blockSource E1) baseSector ≃
      Fibre (faithfulWeightSector iota hinj blocks blockSource E1) baseSector
  baseEquivariant : ∀ (a : (MulAut X)ᵐᵒᵖ)
      (ha : a • baseSector = baseSector)
      (phi : Fibre
        (faithfulBrauerSector iota hinj blocks blockSource E1) baseSector),
    baseEquiv
        (stabilizerFibreEquiv
          (faithfulBrauerSector iota hinj blocks blockSource E1)
          (C iota hinj blocks blockSource E1 CharacterTripleOK
            characterTriple_equivariant).brauerSector_equivariant
          baseSector a ha phi) =
      stabilizerFibreEquiv
        (faithfulWeightSector iota hinj blocks blockSource E1)
        (C iota hinj blocks blockSource E1 CharacterTripleOK
          characterTriple_equivariant).weightSector_equivariant
        baseSector a ha (baseEquiv phi)
  baseBlockInduction : ∀ phi :
      Fibre (faithfulBrauerSector iota hinj blocks blockSource E1) baseSector,
    faithfulWeightBlock iota hinj blocks blockSource E1 (baseEquiv phi) =
      faithfulBrauerBlock iota hinj blocks blockSource E1 phi
  characterTriple_of_stabilizer_eq : ∀
      (phi : FaithfulIBr iota hinj blocks blockSource E1)
      (w : FaithfulWeight iota hinj blocks blockSource E1),
    faithfulWeightSector iota hinj blocks blockSource E1 w =
        faithfulBrauerSector iota hinj blocks blockSource E1 phi →
    MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi.val =
        MulAction.stabilizer (MulAut X)ᵐᵒᵖ w.val →
      CharacterTripleOK phi w

variable (AD : AnDietrichFaithfulSectorSource iota hinj blocks blockSource E1
  CharacterTripleOK characterTriple_equivariant)

/-- The transported equivalence on all literal faithful-sector carriers. -/
def transportedCandidate : Candidate
    (C iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant) :=
  equivariantReplacement
    (C iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant)
    AD.baseSector AD.transporter AD.transporter_spec
    AD.baseEquiv AD.baseEquivariant AD.baseBlockInduction

/-- The transported map is fully automorphism equivariant. -/
theorem transported_equivariant (a : (MulAut X)ᵐᵒᵖ)
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    (transportedCandidate iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant AD).equiv (a • phi) =
      a • (transportedCandidate iota hinj blocks blockSource E1
        CharacterTripleOK characterTriple_equivariant AD).equiv phi :=
  (transportedCandidate iota hinj blocks blockSource E1 CharacterTripleOK
    characterTriple_equivariant AD).equiv_equivariant a phi

/-- The transported map preserves the literal central character sector. -/
theorem transported_preserves_sector
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    faithfulWeightSector iota hinj blocks blockSource E1
        ((transportedCandidate iota hinj blocks blockSource E1
          CharacterTripleOK characterTriple_equivariant AD).equiv phi) =
      faithfulBrauerSector iota hinj blocks blockSource E1 phi :=
  (transportedCandidate iota hinj blocks blockSource E1 CharacterTripleOK
    characterTriple_equivariant AD).sector_preserving phi

/-- The transported map preserves the literal block induced from the local
defect-zero character. -/
theorem transported_preserves_block
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    faithfulWeightBlock iota hinj blocks blockSource E1
        ((transportedCandidate iota hinj blocks blockSource E1
          CharacterTripleOK characterTriple_equivariant AD).equiv phi) =
      faithfulBrauerBlock iota hinj blocks blockSource E1 phi :=
  (transportedCandidate iota hinj blocks blockSource E1 CharacterTripleOK
    characterTriple_equivariant AD).block_preserving phi

/-- Radical class of the literal weight matched with a faithful Brauer
character. -/
def transportedPart (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    RadicalClass (p := p) (X := X) :=
  faithfulWeightRadical iota hinj blocks blockSource E1
    ((transportedCandidate iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant AD).equiv phi)

/-- The radical class pulled back from the literal weight is equivariant. -/
theorem transported_part_equivariant (a : (MulAut X)ᵐᵒᵖ)
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    transportedPart iota hinj blocks blockSource E1 CharacterTripleOK
        characterTriple_equivariant AD (a • phi) =
      a • transportedPart iota hinj blocks blockSource E1 CharacterTripleOK
        characterTriple_equivariant AD phi :=
  Candidate.part_equivariant
    (C iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant)
    (transportedCandidate iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant AD) a phi

/-- Every matched literal Brauer character and weight class have equal full
automorphism stabilisers. -/
theorem transported_stabilizer_eq
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi =
      MulAction.stabilizer (MulAut X)ᵐᵒᵖ
        ((transportedCandidate iota hinj blocks blockSource E1
          CharacterTripleOK characterTriple_equivariant AD).equiv phi) :=
  Candidate.stabilizer_eq
    (C iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant)
    (transportedCandidate iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant AD) phi

/-- The same stabiliser equality holds on the underlying function-valued
Brauer character and literal character-weight conjugacy class. -/
theorem transported_underlying_stabilizer_eq
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi.val =
      MulAction.stabilizer (MulAut X)ᵐᵒᵖ
        ((transportedCandidate iota hinj blocks blockSource E1
          CharacterTripleOK characterTriple_equivariant AD).equiv phi).val := by
  ext a
  simp only [MulAction.mem_stabilizer_iff]
  calc
    a • phi.val = phi.val ↔ a • phi = phi :=
      (faithfulIBr_smul_eq_iff iota hinj blocks blockSource E1 a phi).symm
    _ ↔ a • (transportedCandidate iota hinj blocks blockSource E1
          CharacterTripleOK characterTriple_equivariant AD).equiv phi =
        (transportedCandidate iota hinj blocks blockSource E1
          CharacterTripleOK characterTriple_equivariant AD).equiv phi :=
      Candidate.fixed_iff
        (C iota hinj blocks blockSource E1 CharacterTripleOK
          characterTriple_equivariant)
        (transportedCandidate iota hinj blocks blockSource E1
          CharacterTripleOK characterTriple_equivariant AD) a phi
    _ ↔ a • ((transportedCandidate iota hinj blocks blockSource E1
          CharacterTripleOK characterTriple_equivariant AD).equiv phi).val =
        ((transportedCandidate iota hinj blocks blockSource E1
          CharacterTripleOK characterTriple_equivariant AD).equiv phi).val :=
      faithfulWeight_smul_eq_iff iota hinj blocks blockSource E1 a
        ((transportedCandidate iota hinj blocks blockSource E1
          CharacterTripleOK characterTriple_equivariant AD).equiv phi)

/-- Apply the exact source factor-set and character-triple implication after
Lean has proved equality of the literal stabilisers.  The implication itself
is E2 and receives no kernel credit. -/
theorem transported_characterTriple_actual
    (phi : FaithfulIBr iota hinj blocks blockSource E1) :
    CharacterTripleOK phi
      ((transportedCandidate iota hinj blocks blockSource E1
        CharacterTripleOK characterTriple_equivariant AD).equiv phi) :=
  AD.characterTriple_of_stabilizer_eq phi
    ((transportedCandidate iota hinj blocks blockSource E1
      CharacterTripleOK characterTriple_equivariant AD).equiv phi)
    (transported_preserves_sector iota hinj blocks blockSource E1
      CharacterTripleOK characterTriple_equivariant AD phi)
    (transported_underlying_stabilizer_eq iota hinj blocks blockSource E1
      CharacterTripleOK characterTriple_equivariant AD phi)

/-- Independence of the literal transported equivalence from the chosen
sector transporters. -/
theorem transported_equiv_independent
    (transporter' : FaithfulSector (k := k) (X := X) → (MulAut X)ᵐᵒᵖ)
    (htransporter' : ∀ sector, transporter' sector • AD.baseSector = sector) :
    (equivariantReplacement
      (C iota hinj blocks blockSource E1 CharacterTripleOK
        characterTriple_equivariant)
      AD.baseSector AD.transporter AD.transporter_spec
      AD.baseEquiv AD.baseEquivariant AD.baseBlockInduction).equiv =
    (equivariantReplacement
      (C iota hinj blocks blockSource E1 CharacterTripleOK
        characterTriple_equivariant)
      AD.baseSector transporter' htransporter'
      AD.baseEquiv AD.baseEquivariant AD.baseBlockInduction).equiv :=
  equivariantReplacement_equiv_independent
    (C iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant)
    AD.baseSector AD.transporter transporter'
    AD.transporter_spec htransporter'
    AD.baseEquiv AD.baseEquivariant AD.baseBlockInduction

/-- Literal local restriction by sector, primitive block, and radical class. -/
def transportedLocalEquiv
    (sector : FaithfulSector (k := k) (X := X))
    (block : ActualBlock (k := k) (X := X))
    (radical : RadicalClass (p := p) (X := X)) :
    {phi : FaithfulIBr iota hinj blocks blockSource E1 //
      faithfulBrauerSector iota hinj blocks blockSource E1 phi = sector ∧
      faithfulBrauerBlock iota hinj blocks blockSource E1 phi = block ∧
      transportedPart iota hinj blocks blockSource E1 CharacterTripleOK
        characterTriple_equivariant AD phi = radical} ≃
    {w : FaithfulWeight iota hinj blocks blockSource E1 //
      faithfulWeightSector iota hinj blocks blockSource E1 w = sector ∧
      faithfulWeightBlock iota hinj blocks blockSource E1 w = block ∧
      faithfulWeightRadical iota hinj blocks blockSource E1 w = radical} :=
  Candidate.localEquiv
    (C iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant)
    (transportedCandidate iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant AD) sector block radical

/-- Conclusion of the transport construction on the actual carriers.  The record contains
the map constructed from one sector rather than receiving a global map as an
input. -/
structure ActualLemma55Clauses where
  equiv : FaithfulIBr iota hinj blocks blockSource E1 ≃
    FaithfulWeight iota hinj blocks blockSource E1
  automorphismTransport : ∀ (a : (MulAut X)ᵐᵒᵖ)
      (phi : FaithfulIBr iota hinj blocks blockSource E1),
    equiv (a • phi) = a • equiv phi
  sectorPreservation : ∀ phi,
    faithfulWeightSector iota hinj blocks blockSource E1 (equiv phi) =
      faithfulBrauerSector iota hinj blocks blockSource E1 phi
  blockPreservation : ∀ phi,
    faithfulWeightBlock iota hinj blocks blockSource E1 (equiv phi) =
      faithfulBrauerBlock iota hinj blocks blockSource E1 phi
  radicalPart : FaithfulIBr iota hinj blocks blockSource E1 →
    RadicalClass (p := p) (X := X)
  radicalPart_eq : ∀ phi,
    radicalPart phi =
      faithfulWeightRadical iota hinj blocks blockSource E1 (equiv phi)
  radicalTransport : ∀ (a : (MulAut X)ᵐᵒᵖ)
      (phi : FaithfulIBr iota hinj blocks blockSource E1),
    radicalPart (a • phi) = a • radicalPart phi
  localRestriction : ∀
      (sector : FaithfulSector (k := k) (X := X))
      (block : ActualBlock (k := k) (X := X))
      (radical : RadicalClass (p := p) (X := X)), Nonempty
    ({phi : FaithfulIBr iota hinj blocks blockSource E1 //
      faithfulBrauerSector iota hinj blocks blockSource E1 phi = sector ∧
      faithfulBrauerBlock iota hinj blocks blockSource E1 phi = block ∧
      radicalPart phi = radical} ≃
    {w : FaithfulWeight iota hinj blocks blockSource E1 //
      faithfulWeightSector iota hinj blocks blockSource E1 w = sector ∧
      faithfulWeightBlock iota hinj blocks blockSource E1 w = block ∧
      faithfulWeightRadical iota hinj blocks blockSource E1 w = radical})
  stabilizers : ∀ phi,
    MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi.val =
      MulAction.stabilizer (MulAut X)ᵐᵒᵖ (equiv phi).val
  characterTriple : ∀ phi, CharacterTripleOK phi (equiv phi)

/-- Combine the conclusions of transport on the actual carriers.  The final
character-triple field applies the separately supplied E2 factor-set bridge;
the transport, local restriction, and stabiliser statements are constructed
in Lean. -/
def lemma_5_5_actual : ActualLemma55Clauses iota hinj blocks blockSource E1
    CharacterTripleOK where
  equiv := (transportedCandidate iota hinj blocks blockSource E1
    CharacterTripleOK characterTriple_equivariant AD).equiv
  automorphismTransport := transported_equivariant iota hinj blocks
    blockSource E1 CharacterTripleOK characterTriple_equivariant AD
  sectorPreservation := transported_preserves_sector iota hinj blocks
    blockSource E1 CharacterTripleOK characterTriple_equivariant AD
  blockPreservation := transported_preserves_block iota hinj blocks
    blockSource E1 CharacterTripleOK characterTriple_equivariant AD
  radicalPart := transportedPart iota hinj blocks blockSource E1
    CharacterTripleOK characterTriple_equivariant AD
  radicalPart_eq _ := rfl
  radicalTransport := transported_part_equivariant iota hinj blocks
    blockSource E1 CharacterTripleOK characterTriple_equivariant AD
  localRestriction sector block radical :=
    ⟨transportedLocalEquiv iota hinj blocks blockSource E1 CharacterTripleOK
      characterTriple_equivariant AD sector block radical⟩
  stabilizers := transported_underlying_stabilizer_eq iota hinj blocks
    blockSource E1 CharacterTripleOK characterTriple_equivariant AD
  characterTriple := transported_characterTriple_actual iota hinj blocks
    blockSource E1 CharacterTripleOK characterTriple_equivariant AD

end ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
