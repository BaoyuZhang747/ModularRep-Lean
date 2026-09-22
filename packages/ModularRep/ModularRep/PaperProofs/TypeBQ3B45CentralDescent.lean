import ModularRep.PaperProofs.TypeBQ3B2CentralQuotient
import ModularRep.PaperProofs.TypeBQ3B2RootDescent
import ModularRep.PaperProofs.TypeBQ3FaithfulFibreBinding
import ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual
import ModularRep.PaperProofs.TypeBLiteralBlockReindex
import ModularRep.BrauerCharacterSeparation

/-!
# Named B4/B5 central descent to the same matrix G3

This is supporting work for `prop:type-b-q3`, the B4/B5 defect-zero branch,
not a standalone acceptance of that branch.  The literal group is the
retained X = FullCover / centralTwoSubgroup and the quotient is the same
q : X -> G3.  No universal-cover assertion is made for X.

External inputs used here are the actual nine-block idempotent decomposition,
the literal Brauer-row dictionary with completeness and specified block
membership, the trivial central sector of the selected named block, and the
generic guarded primitive-image theorem for q.  The rows L16 and L17 are
fixed before descent; no reference character, descended block, fibre
equivalence, outer-action equation, defect-zero theorem, or criterion is
supplied as an input.  Dictionary injectivity is unnecessary for these
singleton fibres and is not assumed.

K: the finite row routing and dictionary completeness give the complete
singleton Brauer fibre on each named idempotent.  The already checked generic
B2 central-descent deductions then give the actual primitive image, complete
deflation, every supported character's central kernel and own quotient,
with exact character-value pullback equations.  These providers are generic
in the block: no B2 cardinality-two, dihedral, outer-action or criterion
hypothesis is used.  Root restriction and residue calibration retain the
same modular system.  The downstream literal decomposition DB is to be
constructed from the SAME weight operations in the final application.

Source boundary: table positions 16/17 and their trivial sectors in the
canonical q3 block table / o7blocks.out require the existing E3 specified
dictionary and sector identification.  Guarded primitive image is the
standard E1 Navarro central prime-to-two quotient statement, pp. 198--199,
9.9(c).  None of these semantic source inhabitants is authenticated by this
conditional Lean deduction.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B45CentralDescent

open ModularRep FDRepSimpleClassKZero
open Formalisation.ComputationArithmetic
open ManuscriptVerification.ExceptionalQ3OutputCertificate
open TypeBExceptionalQ3Proposition416Actual
open TypeBQ3TripleCoverCarrier TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3PrincipalCriterionDominatedBlock
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

/-- Exactly the two named blocks in the manuscript defect-zero branch. -/
abbrev Block45 := { b : Q3Block // b = .B4 ∨ b = .B5 }

def four : Block45 := ⟨.B4, Or.inl rfl⟩
def five : Block45 := ⟨.B5, Or.inr rfl⟩

/-- The existing one-based CTblLib row, not a newly chosen character. -/
def row (i : Block45) : BrauerLabel :=
  match i.val with
  | .B4 => .L16
  | _ => .L17

@[simp] theorem row_four : row four = .L16 := rfl
@[simp] theorem row_five : row five = .L17 := rfl
@[simp] theorem row_four_position : (row four).position = 16 := rfl
@[simp] theorem row_five_position : (row five).position = 17 := rfl

theorem row_block (i : Block45) : blockOfBrauerLabel (row i) = i.val := by
  rcases i with ⟨i, hi⟩
  rcases hi with rfl | rfl <;> rfl

/-- The printed fibre has exactly its named row, before any specified map. -/
theorem label_eq_row (i : Block45) (label : BrauerLabel)
    (h : blockOfBrauerLabel label = i.val) : label = row i := by
  rcases i with ⟨i, hi⟩
  rcases hi with rfl | rfl <;>
    cases label <;> simp_all [blockOfBrauerLabel, row]

variable [Finite X]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]
  (root : PrimeRegularRootEmbedding 2 k K X)
  {d : Q3Block → k[X]} (blocks : BlockIdempotentDecomposition d)

/-- The literal primitive idempotent of the selected named block. -/
abbrev upBlock (i : Block45) : LiteralPrimitiveBlock k X :=
  primitiveBlockOfLabel blocks i.val

variable (dictionary : LiteralBrauerOutputMap root)
  (compatible : BrauerBlockFibreCompatible root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks dictionary)

/-- The actual supported reference is exactly the specified image of row
16 or 17.  Its existence uses membership, with no arbitrary reference input. -/
def upReference (i : Block45) : BrauerFibre root (upBlock blocks i) :=
  ⟨dictionary.character (row i),
    (TypeBQ3FaithfulFibreBinding.supported_iff_namedBlock root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks i.val _).mpr
      ((compatible (row i)).trans (row_block i))⟩

@[simp] theorem upReference_val (i : Block45) :
    (upReference root blocks dictionary compatible i).val = dictionary.character (row i) := rfl

include compatible in
/-- Completeness of the actual dictionary, rather than existence of a row,
proves that every supported character is this reference. -/
theorem upReference_unique
    (complete : Function.Surjective dictionary.character) (i : Block45)
    (phi : BrauerFibre root (upBlock blocks i)) :
    phi = upReference root blocks dictionary compatible i := by
  obtain ⟨label, hlabel⟩ := complete phi.val
  have hblock : blockOfBrauerLabel label = i.val := by
    have hnamed := (TypeBQ3FaithfulFibreBinding.supported_iff_namedBlock root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks i.val phi.val).mp
      phi.property
    rw [← compatible label, hlabel]
    exact hnamed
  apply Subtype.ext
  change phi.val = dictionary.character (row i)
  rw [← hlabel, label_eq_row i label hblock]

include compatible in
theorem upCard (complete : Function.Surjective dictionary.character) (i : Block45) :
    Nat.card (BrauerFibre root (upBlock blocks i)) = 1 :=
  Nat.card_eq_one_iff_exists.mpr
    ⟨upReference root blocks dictionary compatible i,
      upReference_unique root blocks dictionary compatible complete i⟩

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

/-- The same computed root used by actual q-descent. -/
abbrev downRoot : PrimeRegularRootEmbedding 2 k K G3 :=
  TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root

variable [Fintype (LiteralPrimitiveBlock k X)]
  [Fintype (LiteralPrimitiveBlock k G3)]
  (i : Block45)
  (sectorOne : centralSector matrixSource freeSource (upBlock blocks i) = 1)

include sectorOne in
/-- The common-sector kernel is exactly ker(q), not a caller-selected
central subgroup and not an assertion about the full representation kernel. -/
theorem sectorKernel_eq_qker :
    (centralSector matrixSource freeSource (upBlock blocks i)).ker.map
        (Subgroup.center X).subtype = (q matrixSource freeSource).ker :=
  TypeBQ3B2CentralQuotient.sectorKernel_eq_qker matrixSource freeSource
    (upBlock blocks i) sectorOne

include sectorOne in
/-- The same central kernel identity holds for every supported character. -/
theorem centralKernel_eq_qker (phi : BrauerFibre root (upBlock blocks i)) :
    TypeBBSCentralCharacterQuotient.centralKernel root phi.val =
      (q matrixSource freeSource).ker :=
  TypeBQ3B2CentralQuotient.centralKernel_eq_qker matrixSource freeSource root
    (TypeBLiteralBlockReindex.literalBlocks blocks) (upBlock blocks i) sectorOne phi

/-- Each supported character's own central quotient is the SAME G3. -/
def ownQuotientEquiv (phi : BrauerFibre root (upBlock blocks i)) :
    TypeBQ3PrincipalExtensionCentralQuotient.CentralQuotient root (upBlock blocks i) phi ≃* G3 :=
  TypeBQ3B2CentralQuotient.centralQuotientEquiv matrixSource freeSource root
    (TypeBLiteralBlockReindex.literalBlocks blocks) (upBlock blocks i) sectorOne phi

@[simp] theorem ownQuotientEquiv_mk (phi : BrauerFibre root (upBlock blocks i)) (x : X) :
    ownQuotientEquiv root blocks matrixSource freeSource i sectorOne phi
      (QuotientGroup.mk' (TypeBBSCentralCharacterQuotient.centralKernel root phi.val) x) =
        q matrixSource freeSource x := rfl

variable
  (DB : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G3 => b.val))
  (primitive : CentralPrimeToPrimitiveImageSource (k := k)
    (q matrixSource freeSource) (q_surjective matrixSource freeSource) root.prime
    (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource))

/-- The actual dominated block, obtained from the named row and literal q. -/
def downBlock : LiteralPrimitiveBlock k G3 :=
  TypeBQ3B2CentralQuotient.downBlock matrixSource freeSource root
    (TypeBLiteralBlockReindex.literalBlocks blocks) (upBlock blocks i) sectorOne DB
    (upReference root blocks dictionary compatible i) primitive

@[simp] theorem downBlock_val :
    (downBlock root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive).val =
      algebraMapOf (q matrixSource freeSource) (d i.val) := rfl

/-- Complete specified Brauer deflation on the named block and its image. -/
def downDeflation :
    BrauerFibre root (upBlock blocks i) ≃
      BrauerFibre (downRoot root matrixSource freeSource)
        (downBlock root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive) :=
  TypeBQ3B2CentralQuotient.brauerDeflation matrixSource freeSource root
    (TypeBLiteralBlockReindex.literalBlocks blocks) (upBlock blocks i) sectorOne DB
    (upReference root blocks dictionary compatible i) primitive

theorem downDeflation_pullback (phi : BrauerFibre root (upBlock blocks i)) :
    PrimeRegularClassFunction.pullback (q matrixSource freeSource)
      (downDeflation root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive
        phi).val.val = phi.val.val :=
  TypeBQ3B2CentralQuotient.brauerDeflation_pullback matrixSource freeSource root
    (TypeBLiteralBlockReindex.literalBlocks blocks) (upBlock blocks i) sectorOne DB
    (upReference root blocks dictionary compatible i) primitive phi

@[simp] theorem downDeflation_symm_pullback
    (phi : BrauerFibre (downRoot root matrixSource freeSource)
      (downBlock root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive)) :
    ((downDeflation root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive).symm
      phi).val.val = PrimeRegularClassFunction.pullback (q matrixSource freeSource) phi.val.val := rfl

/-- The downstairs supported reference is the deflation of the fixed row. -/
def downReference :
    BrauerFibre (downRoot root matrixSource freeSource)
      (downBlock root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive) :=
  downDeflation root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive
    (upReference root blocks dictionary compatible i)

/-- Its literal values inflate to row16/row17 of the same dictionary. -/
theorem downReference_pullback :
    PrimeRegularClassFunction.pullback (q matrixSource freeSource)
      (downReference root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive).val.val =
        (dictionary.character (row i)).val :=
  downDeflation_pullback root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive
    (upReference root blocks dictionary compatible i)

/-- Deflation transports completeness, so the entire downstairs fibre is
the single reference used by the later defect-zero construction. -/
theorem downReference_unique (complete : Function.Surjective dictionary.character)
    (phi : BrauerFibre (downRoot root matrixSource freeSource)
      (downBlock root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive)) :
    phi = downReference root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive := by
  let E := downDeflation root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive
  have h := upReference_unique root blocks dictionary compatible complete i (E.symm phi)
  have mapped := congrArg E h
  exact (E.apply_symm_apply phi).symm.trans mapped

theorem downCard (complete : Function.Surjective dictionary.character) :
    Nat.card (BrauerFibre (downRoot root matrixSource freeSource)
      (downBlock root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive)) = 1 :=
  (Nat.card_congr
    (downDeflation root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive).symm).trans
      (upCard root blocks dictionary compatible complete i)

/-- Every character's own quotient character is the pullback of its SAME
deflated character, using the natural equivalence already constructed. -/
theorem ownQuotientBrauer_eq_pullback (phi : BrauerFibre root (upBlock blocks i)) :
    (TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer root (upBlock blocks i) phi).val =
      PrimeRegularClassFunction.pullback
        (ownQuotientEquiv root blocks matrixSource freeSource i sectorOne phi).toMonoidHom
        (downDeflation root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive
          phi).val.val :=
  TypeBQ3B2CentralQuotient.quotientBrauer_eq_pullback_deflation matrixSource freeSource root
    (TypeBLiteralBlockReindex.literalBlocks blocks) (upBlock blocks i) sectorOne DB
    (upReference root blocks dictionary compatible i) primitive phi

section Coefficients

variable {O : Type} [CommRing O] [IsDomain O] [Algebra O K]
  (Msys : ModularSystem 2 K O k)

/-- No independent downstairs ordinary coefficient convention is chosen. -/
def downOrdinaryRoots [HasEnoughRootsOfUnity K (Nat.card X)] :
    HasEnoughRootsOfUnity K (Nat.card G3) :=
  TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource

/-- The computed downstairs root is calibrated to the SAME modular system. -/
theorem downRoot_residue
    (calibration : TypeBLocalReductionInstantiation.RootResidueCompatible Msys root) :
    TypeBLocalReductionInstantiation.RootResidueCompatible Msys
      (downRoot root matrixSource freeSource) :=
  TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration

end Coefficients

end ModularRep.PaperProofs.TypeBQ3B45CentralDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
