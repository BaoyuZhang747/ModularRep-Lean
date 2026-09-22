import ModularRep.Navarro417DefectSource
import ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
import ModularRep.PaperProofs.SporadicFi24ThreeBlockCarrierActual

/-!
# Carrier alignment for the generic `Fi'_{24}` four-row packet at three

This file isolates the first carrier alignments needed before Navarro (4.17)
can be applied to the four-row `Q = 3^2` packet.  The table source is required
to use the fixed-`Q` projection of the same full operations that supply the
ambient and normaliser block catalogues.  Consequently its normaliser block
is already on the literal carrier used by those catalogues.

The minimal core has two Navarro (4.11) support criteria, one for the common
local block and one for a bare literal ambient target.  The existing source
selecting the named nonprincipal block remains as a compatibility facade.
The corresponding defect-representative statements are kernel deductions
from those fields and the radicality supplied by the table source.

This remains generic in `X` and `Q`.  It does not construct `Fi'_{24}`, match
`Q` or any table row with an external computation, assert uniqueness or
coverage, invoke First Main, or prove block induction, cancellation, BAW, or
iBAW.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3QSquaredCarrierAlignment

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance primeThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

local instance fi24QSquaredCarrierAlignmentNormalizerFintype
    {Q : Subgroup X} : Fintype (defectNormalizer Q) :=
  Fintype.ofFinite _

/-! ## Catalogue-specific support predicates -/

/-- Navarro (4.11) support for a literal normaliser block in the full
fixed-`Q` catalogue stored by the Fischer operations. -/
def LocalSupport411
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X)
    (b : InflatedNormalizerBlock (k := k) Q) : Prop :=
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  Navarro411CentralBrauerSource localData.blocks b
    (defectSubgroupInNormalizer Q)

/-- Navarro (4.11) support for a literal ambient block in the full Fischer
ambient catalogue. -/
def AmbientSupport411
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X)
    (B : ActualBlock (k := k) (X := X)) : Prop :=
  let O := R.1.operations
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  Navarro411CentralBrauerSource O.ambientBlockData.blocks B Q

/-- The common table block has the copy of `Q` in its normaliser as the
nominated Navarro (4.11) defect representative. -/
def TableLocalHasDefect
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X)
    (b : InflatedNormalizerBlock (k := k) Q) : Prop :=
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  navarro417LocalHasDefect (p := 3) localData.blocks b
    (defectSubgroupInNormalizer Q)

/-- A literal ambient block has `Q` as the nominated Navarro (4.11) defect
representative in the full Fischer catalogue. -/
def AmbientHasDefect
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X)
    (B : ActualBlock (k := k) (X := X)) : Prop :=
  let O := R.1.operations
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  navarro417AmbientHasDefect (p := 3) O.ambientBlockData.blocks B Q

/-! ## The bare-target alignment boundary -/

/-- The two E1/U support identifications for the common local block and a
bare literal ambient target `B`.

The type of `table` forces the fixed-`Q` operations to be exactly the
projection of `R.1.operations`.  The source therefore introduces no second
local or ambient catalogue and no equality between parallel catalogues.

Although `R` inherits the full weight operations package, this source and
its K consequences below use only its displayed local and ambient catalogue
projections.  They do not inspect `blockInductionDefined`,
`automorphism_transport`, or `inner_blocks_fixed`, and there is no
three-block coverage input. -/
structure CoreSource
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X)
    (table :
      SporadicFi24P3QSquaredLocalTableSource.Source Q
        (R.1.operations.toLocalNormalizerBlockOperations Q))
    (B : ActualBlock (k := k) (X := X)) : Prop where
  local_support411 : LocalSupport411 R Q table.normalizerBlock
  ambient_support411 : AmbientSupport411 R Q B

namespace CoreSource

variable
  {R : LiteralCarrierAdapter
    (p := 3) (k := k) (K := K) (X := X)}
  {Q : Subgroup X}
  {table :
    SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)}
  {B : ActualBlock (k := k) (X := X)}

/-- The local defect-representative package follows from the local (4.11)
support input and the `3`-group property of the radical subgroup. -/
theorem tableLocalHasDefect
    (S : CoreSource R Q table B) :
    TableLocalHasDefect R Q table.normalizerBlock := by
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  let _ : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  change Navarro411DefectRepresentative localData.blocks
    table.normalizerBlock (defectSubgroupInNormalizer Q)
  refine ⟨defectSubgroupInNormalizer_isPGroup
    table.q_radical.isPGroup, ?_⟩
  simpa only [LocalSupport411] using S.local_support411

/-- The bare ambient target has `Q` as the nominated defect representative,
using only its ambient (4.11) support field and the table radicality. -/
theorem ambientHasDefect
    (S : CoreSource R Q table B) :
    AmbientHasDefect R Q B := by
  let O := R.1.operations
  let _ : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  change Navarro411DefectRepresentative O.ambientBlockData.blocks B Q
  refine ⟨table.q_radical.isPGroup, ?_⟩
  simpa only [AmbientSupport411] using S.ambient_support411

end CoreSource

/-! ## Compatibility with the specified three blocks -/

/-- The two E1/U support identifications still needed after the table source
has been placed on the literal Fischer operations carrier.

The type of `table` forces the fixed-`Q` operations to be exactly the
projection of `R.1.operations`.  The record therefore does not contain a
separate equality between parallel local catalogues. -/
structure Source
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (three : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table :
      SporadicFi24P3QSquaredLocalTableSource.Source Q
        (R.1.operations.toLocalNormalizerBlockOperations Q)) : Prop where
  local_support411 : LocalSupport411 R Q table.normalizerBlock
  ambient_support411 :
    AmbientSupport411 R Q three.nonprincipalBlock

namespace Source

variable
  {R : LiteralCarrierAdapter
    (p := 3) (k := k) (K := K) (X := X)}
  {three : Fi24ThreeBlockSource (k := k) (X := X)}
  {Q : Subgroup X}
  {table :
    SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)}

/-- Forget the inherited three-block package and retain only its selected
nonprincipal target and the two support fields.  This conversion does not
inspect the selected outer action, either other block, or `three.all_blocks`.
It also does not inspect any all-weight operation inherited through `R`. -/
theorem toCore
    (S : Source R three Q table) :
    CoreSource R Q table three.nonprincipalBlock :=
  ⟨S.local_support411, S.ambient_support411⟩

/-- The local defect-representative package follows from the local (4.11)
support input and the `3`-group property of the radical subgroup. -/
theorem tableLocalHasDefect
    (S : Source R three Q table) :
    TableLocalHasDefect R Q table.normalizerBlock := by
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  let _ : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  change Navarro411DefectRepresentative localData.blocks
    table.normalizerBlock (defectSubgroupInNormalizer Q)
  refine ⟨defectSubgroupInNormalizer_isPGroup
    table.q_radical.isPGroup, ?_⟩
  simpa only [LocalSupport411] using S.local_support411

/-- The ambient defect-representative package follows from the ambient
(4.11) support input and the `3`-group property of the radical subgroup. -/
theorem nonprincipalAmbientHasDefect
    (S : Source R three Q table) :
    AmbientHasDefect R Q three.nonprincipalBlock := by
  let O := R.1.operations
  let _ : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  change Navarro411DefectRepresentative O.ambientBlockData.blocks
    three.nonprincipalBlock Q
  refine ⟨table.q_radical.isPGroup, ?_⟩
  simpa only [AmbientSupport411] using S.ambient_support411

end Source

end ModularRep.PaperProofs.SporadicFi24P3QSquaredCarrierAlignment


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
