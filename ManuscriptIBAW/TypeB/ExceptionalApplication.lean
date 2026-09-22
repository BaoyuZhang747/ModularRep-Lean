import ManuscriptIBAW.TypeB.ExceptionalFamily
import ManuscriptIBAW.TypeB.ExceptionalSources
import ManuscriptIBAW.FamilyCertificate

/-!
# Proposition 4.11 on the specified triple cover

The proof chooses dominated blocks and weight representatives under the
stated assumptions. The finite block decompositions refer to these choices. Neither the
full criterion nor a final matching is assumed.

The resulting natural quotient criteria are interpreted on one constructed
primitive block family by an explicit external source. The separate
source passing from compatible block conditions to a full family supplies
the final inductive condition. The final
certificate uses this common family on the same triple cover.

The character table and AtlasRep identifications remain explicit
assumptions. The finite arithmetic in the GAP records is checked separately
from its interpretation on the specified groups.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.Exceptional

open ModularRep ModularRep.PaperProofs
open TypeBQ3TripleCoverCarrier TypeBCentralKernelBlockSource
open TypeBExceptionalQ3Proposition416Actual
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open Formalisation.ComputationArithmetic

local instance exceptionalApplicationFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

set_option genInjectivity false
set_option genSizeOfSpec false

/-- The subordinate source assumptions, with finiteness of the triple cover
derived from the same matrix multiplier source. The ordinary field needs
only the stated roots of unity for finite splitting, including the separate
SO condition in `raw.before.principal`. -/
structure Inputs (S : Type) [Group S] where
  k : Type
  K : Type
  O : Type
  [fieldk : Field k]
  [fieldK : Field K]
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraO : Algebra O K]
  [chark : CharP k 2]
  [closedk : IsAlgClosed k]
  [zeroK : CharZero K]
  [rootsX : HasEnoughRootsOfUnity K (Nat.card X)]
  matrixSource : MatrixExceptionalSource
  freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource
  raw :
    letI : Finite X := finite_X matrixSource
    RawInputs (k := k) (K := K) (O := O)
      (matrixSource := matrixSource) (freeSource := freeSource)
  /-- The existing block operations are interpreted by the literal
  idempotents on every primitive block of the triple cover. -/
  ambientIdempotents :
    letI : Finite X := finite_X matrixSource
    AmbientIdempotents raw.before
  /-- The natural quotient criteria imply the relative condition on the
  same constructed family, under the stated character and root interpretation. -/
  naturalQuotients :
    letI : Finite X := finite_X matrixSource
    NaturalQuotientTransport raw.before ambientIdempotents
  /-- The published passage from complete block conditions to one family. -/
  compatibleFamilySource : CurrentFiniteSplittingAssembly.Source
  base : G3 ≃* S

set_option genInjectivity true
set_option genSizeOfSpec true

attribute [instance] Inputs.fieldk Inputs.fieldK Inputs.ringO Inputs.domainO
  Inputs.algebraO Inputs.chark Inputs.closedk Inputs.zeroK Inputs.rootsX

variable {S : Type} [Group S] (D : Inputs S)

/-- Fix the covering family before proving the inductive condition. -/
def Inputs.target : Target S := by
  letI : Finite X := finite_X D.matrixSource
  exact {
    k := D.k
    K := D.K
    matrixSource := D.matrixSource
    freeSource := D.freeSource
    root := D.raw.before.root
    R := D.raw.before.R
    RX := D.raw.before.faithful.R
    base := D.base }

/-- Fix the common primitive block family independently of its condition. -/
def Inputs.family : EvenFieldFLZDefinition35Family.Definition35Family 2 := by
  letI : Finite X := finite_X D.matrixSource
  exact commonFamily D.raw.before D.ambientIdempotents

/-- The universal prime-to-two cover has its original matrix projection. -/
def Inputs.cover : EvenFieldFLZSourceConditions.EllPrimeCoverSource 2 D.family.H := by
  letI : Finite X := finite_X D.matrixSource
  exact commonCover D.raw.before D.ambientIdempotents

@[simp] theorem Inputs.family_root :
    letI : Finite X := finite_X D.matrixSource
    D.family.iota = D.raw.before.root := rfl

@[simp] theorem Inputs.cover_eq_target : D.cover = D.target.cover := rfl

/-- The classification by the nine labels exhausts the specified primitive
blocks. -/
def Inputs.blockEquiv : Q3Block ≃ LiteralPrimitiveBlock D.k X := by
  letI : Finite X := finite_X D.matrixSource
  exact primitiveBlockEquiv D.raw.before.blocks

theorem Inputs.block_count : Nat.card (LiteralPrimitiveBlock D.k X) = 9 := by
  rw [← Nat.card_congr D.blockEquiv, Nat.card_eq_fintype_card]
  decide

/-- The original root and modular system are preserved. -/
theorem Inputs.root_residue :
    letI : Finite X := finite_X D.matrixSource
    RootResidueCompatible D.raw.before.Msys D.target.root := by
  let : Finite X := finite_X D.matrixSource
  exact D.raw.before.calibration

theorem Inputs.rootDown_residue :
    letI : Finite X := finite_X D.matrixSource
    RootResidueCompatible D.raw.before.Msys D.target.rootDown := by
  let : Finite X := finite_X D.matrixSource
  exact D.raw.before.calibrationDown

/-- The result applies to the principal construction on the lower group with the
same root. The natural quotient criteria are preserved. -/
theorem Inputs.allBlocks :
    letI : Finite X := finite_X D.matrixSource
    TypeBCurrentQ3Inputs.AllBlocksCertificate D.raw.before := by
  let : Finite X := finite_X D.matrixSource
  exact D.raw.allBlocks

/-- Proposition 4.11 on the independently specified target. -/
theorem Inputs.completeNatural : D.target.Complete := by
  let : Finite X := finite_X D.matrixSource
  intro b
  rcases D.allBlocks b with lower | faithful
  · exact lower.map Sum.inl
  · exact faithful.map Sum.inr

/-- The independently proved natural criteria give the uniform family
condition under the explicit quotient transport and compatible block sources. -/
theorem Inputs.familyComplete :
    Nonempty (TypeBFullBlockCondition.FamilyWitness D.family D.cover) := by
  let : Finite X := finite_X D.matrixSource
  exact commonFamily_complete D.raw.before D.ambientIdempotents
    D.naturalQuotients D.compatibleFamilySource D.allBlocks

include D in
/-- The final certificate uses the uniform family condition on the same
cover. The natural quotient theorem remains an intermediate result. -/
theorem Inputs.complete :
    Nonempty (FamilyCertificate S 2) := by
  let : Finite X := finite_X D.matrixSource
  obtain ⟨witness⟩ := D.familyComplete
  exact ⟨⟨D.family, D.cover, D.base, witness⟩⟩

@[simp] theorem Inputs.projection :
    letI : Fintype X := fintype_X D.matrixSource
    D.target.cover.quotient = q D.matrixSource D.freeSource := rfl

end ManuscriptIBAW.TypeB.Exceptional

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
