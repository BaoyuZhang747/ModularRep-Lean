import Formalisation.IBAWBlockWitness
import ModularRep.PaperProofs.OddConlonOrbitAssembly
import ModularRep.CharacterWeightBlockAssignment
import ModularRep.IBrBlock
import ModularRep.PrimitiveBlockAutomorphism
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Construction from orbit representatives and literal Feng--Malle hypotheses for Proposition 3.3

The kernel first transports complete block components around automorphism
orbits and combines their global data. It then proves the fixedness
transport in Feng--Malle, Remark 3.5, from the actual equivariant bijection.

The source-facing endpoint uses literal symplectic matrices over one finite
field, their central quotient, function-valued Brauer characters, intrinsic
character-weight classes, primitive block idempotents, and canonical
automorphism actions. The field order is its cardinality. Matrix
realizations bind the field and diagonal automorphisms to the source.

**K:** construction from orbit representatives, transport of full component clauses, and Remark 3.5.
**E1/E2:** coefficient conventions, actual local block operations, the
matrix realization of source automorphisms, and Corollary 4.6.
**U:** principal/Jordan component realization, the original iBAW target and
its universal prime-to-two cover, and the final Proposition 3.4 application.

The old arbitrary-target descent gate has been removed. This file does not
assert the manuscript proposition or silently identify abstract Context
predicates with the original iBAW condition.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow

open Formalisation
open Formalisation.IBAW
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.OddConlonOrbitAssembly


universe u

variable {A Block Radical Sector Brauer Weight DefectZero : Type u}
variable [Group A]
variable [MulAction A Block] [MulAction A Radical] [MulAction A Sector]
variable [MulAction A Brauer] [MulAction A Weight]
variable [MulAction A DefectZero]

variable (C : Context A Block Radical Sector Brauer Weight DefectZero)

/-! ## One explicit component on every selected block-orbit representative -/

/-- Component-level input on the representatives selected by
`OddConlonOrbitAssembly.orbitRepresentative`.

Every representation theoretic clause is pointwise on the displayed fibre.
In particular, this is not an all-block BAW-goodness predicate and does not
contain a global equivalence. -/
structure RepresentativeBlockComponents where
  equiv : ∀ orbit : BlockOrbit A Block,
    Fibre C.brauerBlock (orbitRepresentative orbit) ≃
      Fibre C.weightBlock (orbitRepresentative orbit)
  stabilizer_equivariant : ∀ (orbit : BlockOrbit A Block) (a : A)
      (ha : a • orbitRepresentative orbit = orbitRepresentative orbit)
      (x : Fibre C.brauerBlock (orbitRepresentative orbit)),
    equiv orbit
        (stabilizerFibreEquiv C.brauerBlock C.brauerBlock_equivariant
          (orbitRepresentative orbit) a ha x) =
      stabilizerFibreEquiv C.weightBlock C.weightBlock_equivariant
        (orbitRepresentative orbit) a ha (equiv orbit x)
  intermediateBlockEqualities : ∀ (orbit : BlockOrbit A Block)
      (x : Fibre C.brauerBlock (orbitRepresentative orbit)),
    C.intermediateBlockEqualitiesOK x (equiv orbit x)
  compatibleExtensions : ∀ (orbit : BlockOrbit A Block)
      (x : Fibre C.brauerBlock (orbitRepresentative orbit)),
    C.extensionsOK x (equiv orbit x)
  modularCharacterTriples : ∀ (orbit : BlockOrbit A Block)
      (x : Fibre C.brauerBlock (orbitRepresentative orbit)),
    C.characterTripleOK x (equiv orbit x)
  normalisation : ∀ (orbit : BlockOrbit A Block) (d : DefectZero)
      (hd : C.brauerBlock (C.reduce d) = orbitRepresentative orbit),
    equiv orbit ⟨C.reduce d, hd⟩ =
      ⟨C.atOne d, (C.atOne_block d).trans hd⟩

namespace RepresentativeBlockComponents

variable (D : RepresentativeBlockComponents C)

/-- Forget the extra component clauses and expose exactly the representative
fibre family consumed by the generic orbit-construction kernel. -/
def toRepresentativeEquivFamily :
    RepresentativeEquivFamily C.brauerBlock C.weightBlock
      C.brauerBlock_equivariant where
  equiv := D.equiv
  equivariant orbit a ha x := by
    have h := D.stabilizer_equivariant orbit a ha x
    exact congrArg Subtype.val h

/-- The cover-side equivalence obtained by transporting the supplied
component equivalences through every block orbit. -/
def assembledEquiv : Brauer ≃ Weight :=
  (D.toRepresentativeEquivFamily).globalEquiv
    C.brauerBlock C.weightBlock C.brauerBlock_equivariant
      C.weightBlock_equivariant

theorem assembledEquiv_equivariant (a : A) (x : Brauer) :
    D.assembledEquiv C (a • x) = a • D.assembledEquiv C x :=
  (D.toRepresentativeEquivFamily).globalEquiv_equivariant
    C.brauerBlock C.weightBlock C.brauerBlock_equivariant
      C.weightBlock_equivariant a x

theorem assembledEquiv_block_preserving (x : Brauer) :
    C.weightBlock (D.assembledEquiv C x) = C.brauerBlock x :=
  (D.toRepresentativeEquivFamily).globalEquiv_block_preserving
    C.brauerBlock C.weightBlock C.brauerBlock_equivariant
      C.weightBlock_equivariant x

/-- Any equivariant matched-pair property known on the selected component of
each block orbit holds for the combined global correspondence. -/
theorem assembledEquiv_pairProperty
    (P : Brauer → Weight → Prop)
    (hP : PairPropertyEquivariant (A := A) P)
    (hRepresentative : ∀ (orbit : BlockOrbit A Block)
      (x : Fibre C.brauerBlock (orbitRepresentative orbit)),
      P x (D.equiv orbit x))
    (x : Brauer) :
    P x (D.assembledEquiv C x) := by
  let orbit : BlockOrbit A Block := Quotient.mk'' (C.brauerBlock x)
  let t : A := orbitTransporter (A := A) (C.brauerBlock x)
  let xRep : Fibre C.brauerBlock (orbitRepresentative orbit) :=
    toRepresentativeX C.brauerBlock C.brauerBlock_equivariant x
  have hbase : P xRep (D.equiv orbit xRep) :=
    hRepresentative orbit xRep
  have htransport : P (t • (xRep : Brauer))
      (t • ((D.equiv orbit xRep :
        Fibre C.weightBlock (orbitRepresentative orbit)) : Weight)) :=
    (hP t xRep (D.equiv orbit xRep)).mp hbase
  rw [assembledEquiv,
    RepresentativeEquivFamily.globalEquiv_apply]
  change P x (t • (D.equiv orbit xRep).1)
  simpa [xRep, t, orbit, toRepresentativeX] using htransport

/-- The componentwise `Q = 1` equations propagate through the same orbit
transport used to build the global equivalence. -/
theorem assembledEquiv_normalisation (d : DefectZero) :
    D.assembledEquiv C (C.reduce d) = C.atOne d := by
  let orbit : BlockOrbit A Block :=
    Quotient.mk'' (C.brauerBlock (C.reduce d))
  let t : A := orbitTransporter (A := A) (C.brauerBlock (C.reduce d))
  let dRep : DefectZero := t⁻¹ • d
  have ht : t • orbitRepresentative orbit =
      C.brauerBlock (C.reduce d) := by
    simp [orbit, t, orbitTransporter_smul_representative]
  have hdRep : C.brauerBlock (C.reduce dRep) =
      orbitRepresentative orbit := by
    calc
      C.brauerBlock (C.reduce dRep) =
          C.brauerBlock (t⁻¹ • C.reduce d) := by
        rw [C.reduce_equivariant]
      _ = t⁻¹ • C.brauerBlock (C.reduce d) :=
        C.brauerBlock_equivariant _ _
      _ = orbitRepresentative orbit := by
        rw [← ht]
        exact inv_smul_smul t _
  let xRep : Fibre C.brauerBlock (orbitRepresentative orbit) :=
    toRepresentativeX C.brauerBlock C.brauerBlock_equivariant (C.reduce d)
  have hxRep : xRep = ⟨C.reduce dRep, hdRep⟩ := by
    apply Subtype.ext
    exact (C.reduce_equivariant t⁻¹ d).symm
  have hbase := D.normalisation orbit dRep hdRep
  have hbaseValue : (D.equiv orbit ⟨C.reduce dRep, hdRep⟩).1 =
      C.atOne dRep := congrArg Subtype.val hbase
  rw [assembledEquiv,
    RepresentativeEquivFamily.globalEquiv_apply]
  change t • (D.equiv orbit xRep).1 = C.atOne d
  rw [hxRep, hbaseValue]
  calc
    t • C.atOne dRep = C.atOne (t • dRep) :=
      (C.atOne_equivariant t dRep).symm
    _ = C.atOne d := by simp [dRep]

/-- The resulting equivalence, equivariance, and block equality packaged as
the generic `IBAW.Candidate`. -/
def assembledCandidate : Candidate C where
  equiv := D.assembledEquiv C
  equiv_equivariant := D.assembledEquiv_equivariant C
  block_preserving := D.assembledEquiv_block_preserving C

/-- Restrict the resulting map and its transported clauses to one literal
block. -/
def assembledBlockWitness (b : Block) : BlockWitness C b where
  equiv := (D.assembledCandidate C).blockEquiv b
  stabilizer_equivariant a ha x := by
    apply Subtype.ext
    exact D.assembledEquiv_equivariant C a x
  intermediateBlockEqualities x :=
    D.assembledEquiv_pairProperty C C.intermediateBlockEqualitiesOK
      C.intermediateBlockEqualities_equivariant
      D.intermediateBlockEqualities x
  extensions x :=
    D.assembledEquiv_pairProperty C C.extensionsOK
      C.extensions_equivariant D.compatibleExtensions x
  characterTriple x :=
    D.assembledEquiv_pairProperty C C.characterTripleOK
      C.characterTriple_equivariant D.modularCharacterTriples x
  normalisation d _hd := by
    apply Subtype.ext
    exact D.assembledEquiv_normalisation C d

/-- Cross-block coherence is no longer an input: it follows from global
equivariance of the orbit-transported map. -/
theorem assembledBlockWitnessFamilyEquivariant :
    BlockWitnessFamilyEquivariant (D.assembledBlockWitness C) := by
  intro a _b x
  apply Subtype.ext
  exact D.assembledEquiv_equivariant C a x

/-- Kernel construction of full cover-side data from the component family.

The final step deliberately reuses the generic block-witness aggregation
kernel.  The three representation theoretic predicates remain exactly the
pointwise component fields supplied upstream. -/
def assembledData : Data C :=
  dataOfBlockWitnesses (D.assembledBlockWitness C)
    (D.assembledBlockWitnessFamilyEquivariant C)

end RepresentativeBlockComponents

/-! ## The kernel content of Feng--Malle, Remark 3.5 -/

variable {FieldAutomorphism : Type u} [Group FieldAutomorphism]

/-- A displayed diagonal element and a displayed field-automorphism
embedding. The literal realization below binds these to matrix operations;
this generic record alone is not a source identification. -/
structure DiagonalFieldAutomorphisms where
  diagonal : A
  field : FieldAutomorphism →* A
  field_injective : Function.Injective field

/-- The common logical shape of Feng--Malle, Proposition 3.4(2)--(3). -/
def DiagonalFieldFixedness
    {X : Type u} [MulAction A X]
    (outer : DiagonalFieldAutomorphisms
      (A := A) (FieldAutomorphism := FieldAutomorphism)) : Prop :=
  ∀ (x : X) (sigma : FieldAutomorphism),
    outer.diagonal • x = outer.field sigma • x →
      outer.diagonal • x = x ∧ outer.field sigma • x = x

/-- Fixedness transfers through the actual equivariant bijection. This is
the used direction of Feng--Malle, Remark 3.5, proved in the kernel rather
than imported as a representation theoretic certificate. -/
theorem diagonalFieldFixedness_of_equivariantEquiv
    {X Y : Type u} [MulAction A X] [MulAction A Y]
    (outer : DiagonalFieldAutomorphisms
      (A := A) (FieldAutomorphism := FieldAutomorphism))
    (omega : X ≃ Y)
    (hequivariant : ∀ (a : A) (x : X), omega (a • x) = a • omega x)
    (hfixed : DiagonalFieldFixedness (X := X) outer) :
    DiagonalFieldFixedness (X := Y) outer := by
  intro y sigma hy
  obtain ⟨x, rfl⟩ := omega.surjective y
  have hx : outer.diagonal • x = outer.field sigma • x := by
    apply omega.injective
    rw [hequivariant, hequivariant]
    exact hy
  obtain ⟨hdelta, hfield⟩ := hfixed x sigma hx
  constructor
  · rw [← hequivariant, hdelta]
  · rw [← hequivariant, hfield]

/-- The weight fixedness clause for the map obtained from orbit representatives uses that exact
map, with no independent Remark 3.5 certificate or candidate choice. -/
theorem assembled_conditionThree
    (D : RepresentativeBlockComponents C)
    (outer : DiagonalFieldAutomorphisms
      (A := A) (FieldAutomorphism := FieldAutomorphism))
    (conditionTwo : DiagonalFieldFixedness (X := Brauer) outer) :
    DiagonalFieldFixedness (X := Weight) outer :=
  diagonalFieldFixedness_of_equivariantEquiv outer
    (D.assembledEquiv C) (D.assembledEquiv_equivariant C) conditionTwo

/-! ## One literal odd-field type-C source problem -/

/-- The finite matrix carrier of Sp_(2n)(F). The rank occurs in the matrix
indices, and the field is the actual coefficient field. -/
abbrev LiteralSp (n : ℕ) (F : Type u) [Field F] :=
  Matrix.symplecticGroup (Fin n) F

/-- The displayed projective symplectic group, not a caller-selected group. -/
abbrev LiteralPSp (n : ℕ) (F : Type u) [Field F] :=
  LiteralSp n F ⧸ Subgroup.center (LiteralSp n F)

/-- The actual central quotient map. -/
def literalProjection (n : ℕ) (F : Type u) [Field F] :
    LiteralSp n F →* LiteralPSp n F :=
  QuotientGroup.mk' (Subgroup.center (LiteralSp n F))

/-- The source range of Feng--Malle, Proposition 3.4. The field order is
Nat.card F, not an unrelated natural-number parameter. -/
structure OddFieldParameters (n : ℕ) (F : Type u) [Field F] [Finite F] : Prop where
  rank_ge_two : 2 ≤ n
  field_odd : Odd (Nat.card F)

noncomputable instance literalSpFintype
    (n : ℕ) (F : Type u) [Field F] [Finite F] :
    Fintype (LiteralSp n F) :=
  Fintype.ofFinite _

/-- The literal carrier of two-weight classes for the symplectic group. -/
abbrev LiteralWeight (n : ℕ) (F K : Type u)
    [Field F] [Finite F] [Field K] [CharZero K] :=
  CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := LiteralSp n F)

/-- Literal group, coefficient, character, block, and local-block-operation
data for the global Feng--Malle map.

All block labels are actual primitive central idempotents. The catalogue
identity rules out reinterpreting those labels by an unrelated idempotent
function. No map, fixedness condition, universal-cover assertion, or iBAW
conclusion is stored here. Standard coefficient and local block-operation
semantics remain E1/E2 source inputs. -/
structure LiteralFengMalleProblem
    (n : ℕ) (F : Type u) [Field F] [Finite F] where
  parameters : OddFieldParameters n F
  k : Type u
  K : Type u
  [fieldk : Field k]
  [fieldK : Field K]
  [charPk : CharP k 2]
  [algClosedk : IsAlgClosed k]
  [charZeroK : CharZero K]
  [algClosedK : IsAlgClosed K]
  iota : PrimeRegularRootEmbedding 2 k K (LiteralSp n F)
  irreducibleBrauerInjective : IrreducibleBrauerCharacterInjectivity iota
  blockSource : CharacterWeight.LocalBlockInductionSource
    (p := 2) (k := k) (K := K) (G := LiteralSp n F)
    (Block := LiteralPrimitiveBlock k (LiteralSp n F))
  catalogue_idempotent : ∀ b : LiteralPrimitiveBlock k (LiteralSp n F),
    blockSource.operations.ambientBlockData.blockIdempotent b = b.1

attribute [instance]
  LiteralFengMalleProblem.fieldk LiteralFengMalleProblem.fieldK
  LiteralFengMalleProblem.charPk LiteralFengMalleProblem.algClosedk
  LiteralFengMalleProblem.charZeroK LiteralFengMalleProblem.algClosedK

namespace LiteralFengMalleProblem

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable (P : LiteralFengMalleProblem n F)

/-- The actual primitive block supporting the Brauer character. -/
def brauerBlock (psi : IBr P.iota) :
    LiteralPrimitiveBlock P.k (LiteralSp n F) := by
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  exact FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock P.iota
    P.irreducibleBrauerInjective
    P.blockSource.operations.ambientBlockData.blocks psi

end LiteralFengMalleProblem

/-- The exact condition-(1) map on intrinsic Brauer characters and weight
classes of the literal symplectic group. Equivariance uses the repository's
canonical right actions, encoded by the opposite automorphism group. -/
structure LiteralGlobalMap
    {n : ℕ} {F : Type u} [Field F] [Finite F]
    (P : LiteralFengMalleProblem n F) where
  equiv : IBr P.iota ≃ LiteralWeight n F P.K
  equivariant : ∀ (a : (MulAut (LiteralSp n F))ᵐᵒᵖ) (psi : IBr P.iota),
    equiv (a • psi) = a • equiv psi
  block_preserving : ∀ psi : IBr P.iota,
    P.blockSource.weightBlock (equiv psi) = P.brauerBlock psi

/-- A matrix-level realization of the automorphisms in Feng--Malle,
Section 3, p. 4. The diagonal automorphism is conjugation by a displayed
similitude of nonsquare multiplier. Field automorphisms act entrywise.

The finite field's ring automorphism group is the intrinsic form of the
source cyclic group generated by prime-field Frobenius; identifying those
two presentations is the standard finite-field E1 fact. No character or
weight action may be freely selected. -/
structure LiteralDiagonalFieldRealisation
    (n : ℕ) (F : Type u) [Field F] [Finite F] where
  outer : DiagonalFieldAutomorphisms
    (A := (MulAut (LiteralSp n F))ᵐᵒᵖ)
    (FieldAutomorphism := (F ≃+* F)ᵐᵒᵖ)
  diagonalMatrix : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F
  diagonalInverse : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F
  inverse_mul : diagonalInverse * diagonalMatrix = 1
  mul_inverse : diagonalMatrix * diagonalInverse = 1
  multiplier : Fˣ
  multiplier_nonsquare : ¬ IsSquare (multiplier : F)
  similitude : diagonalMatrix * Matrix.J (Fin n) F * diagonalMatrix.transpose =
    (multiplier : F) • Matrix.J (Fin n) F
  diagonal_apply : ∀ g : LiteralSp n F,
    ((outer.diagonal.unop g : LiteralSp n F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        diagonalMatrix * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          diagonalInverse
  field_apply : ∀ (sigma : (F ≃+* F)ᵐᵒᵖ) (g : LiteralSp n F),
    (((outer.field sigma).unop g : LiteralSp n F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map sigma.unop

/-- Feng--Malle, Corollary 4.6, p. 10, on this fixed literal Brauer carrier
and the displayed matrix automorphisms. Its field is only condition (2). -/
structure LiteralFengMalleCorollary46Certificate
    {n : ℕ} {F : Type u} [Field F] [Finite F]
    (P : LiteralFengMalleProblem n F)
    (O : LiteralDiagonalFieldRealisation n F) : Prop where
  conditionTwo : DiagonalFieldFixedness (X := IBr P.iota) O.outer

/-- All three displayed hypotheses of Feng--Malle, Proposition 3.4,
pp. 5--6, indexed by the same literal problem and the same global map.

This is a source-hypothesis endpoint, not the iBAW conclusion. In
particular, it does not reinterpret a generic predicate as iBAW. -/
structure LiteralFengMalleHypotheses
    {n : ℕ} {F : Type u} [Field F] [Finite F]
    (P : LiteralFengMalleProblem n F)
    (O : LiteralDiagonalFieldRealisation n F)
    (omega : LiteralGlobalMap P) : Prop where
  conditionTwo : DiagonalFieldFixedness (X := IBr P.iota) O.outer
  conditionThree : DiagonalFieldFixedness (X := LiteralWeight n F P.K) O.outer

/-- Once condition (1) is supplied on the literal carriers, Corollary 4.6
and the kernel proof of Remark 3.5 discharge conditions (2) and (3). -/
theorem literalFengMalleHypotheses
    {n : ℕ} {F : Type u} [Field F] [Finite F]
    (P : LiteralFengMalleProblem n F)
    (O : LiteralDiagonalFieldRealisation n F)
    (omega : LiteralGlobalMap P)
    (corollary46 : LiteralFengMalleCorollary46Certificate P O) :
    LiteralFengMalleHypotheses P O omega where
  conditionTwo := corollary46.conditionTwo
  conditionThree := diagonalFieldFixedness_of_equivariantEquiv
    O.outer omega.equiv omega.equivariant corollary46.conditionTwo

/-! ## Bind the map obtained from orbit representatives to the literal global carrier -/

section LiteralOrbitAssembly

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable (P : LiteralFengMalleProblem n F)
variable {R S DZ : Type u}
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ R]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ S]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ DZ]
variable
  (literalContext : Context (MulAut (LiteralSp n F))ᵐᵒᵖ
    (LiteralPrimitiveBlock P.k (LiteralSp n F)) R S
    (IBr P.iota) (LiteralWeight n F P.K) DZ)

/-- The orbit construction produces the literal condition-(1) map after
the two Context block operations are identified with their actual operations.
The character, weight, block, group, and automorphism carriers already agree
definitionally. No independent global equivalence is accepted. -/
def literalGlobalMapOfRepresentativeComponents
    (D : RepresentativeBlockComponents literalContext)
    (brauerBlock_eq : literalContext.brauerBlock = P.brauerBlock)
    (weightBlock_eq :
      literalContext.weightBlock = P.blockSource.weightBlock) :
    LiteralGlobalMap P where
  equiv := D.assembledEquiv literalContext
  equivariant := D.assembledEquiv_equivariant literalContext
  block_preserving psi := by
    rw [← weightBlock_eq, ← brauerBlock_eq]
    exact D.assembledEquiv_block_preserving literalContext psi

/-- The strongest source-facing endpoint of this window: all three literal
hypotheses of Feng--Malle, Proposition 3.4, for the map obtained from orbit representatives. -/
theorem literalFengMalleHypothesesOfRepresentativeComponents
    (D : RepresentativeBlockComponents literalContext)
    (brauerBlock_eq : literalContext.brauerBlock = P.brauerBlock)
    (weightBlock_eq :
      literalContext.weightBlock = P.blockSource.weightBlock)
    (O : LiteralDiagonalFieldRealisation n F)
    (corollary46 : LiteralFengMalleCorollary46Certificate P O) :
    LiteralFengMalleHypotheses P O
      (literalGlobalMapOfRepresentativeComponents P literalContext D
        brauerBlock_eq weightBlock_eq) :=
  literalFengMalleHypotheses P O
    (literalGlobalMapOfRepresentativeComponents P literalContext D
      brauerBlock_eq weightBlock_eq) corollary46

end LiteralOrbitAssembly

/-!
The previous unused CentralCoverCarrierTransport, phantom-parameter
TypeCUniversalCoverIdentification, arbitrary-target
FengMalleProposition34Certificate, and
ibawAtTwo_of_representativeBlockComponents endpoint were removed.

Feng--Malle, Proposition 3.4, already includes the central-cover passage in
its proof. Reconstructing a bare quotient bijection does not discharge its
extension, local-character, block, or original iBAW semantics. A future
forward E2 gate must return one independently defined literal original iBAW
target on X_2(LiteralPSp n F), with its cover identified with
LiteralPSp n F. No such fully matched target is available here. That join,
and the principal/Jordan inputs to the representative components, remain U;
this file proves neither Proposition prop:odd-two nor the manuscript.
-/

end ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
