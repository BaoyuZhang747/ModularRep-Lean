import ModularRep.Navarro414IntervalCentralCharacterSource

/-!
# Kernel consequences of the Navarro (4.14) interval equality

Relative to the one-field E1 source and independently supplied local and
ambient block catalogues, this file proves definedness and uses the existing
kernel selector for the unique ambient induced block.  It proves no coverage,
defect, idempotent-image, First Main, or bijection statement.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

variable {p : Nat} {k G LocalBlock AmbientBlock : Type*}
variable [Field k] [CharP k p] [IsAlgClosed k]
variable [Group G] [Fintype G]
variable [Fintype LocalBlock] [Fintype AmbientBlock] [Fact p.Prime]
variable {P H : Subgroup G}

local instance : Fintype H := Fintype.ofFinite H

variable {localBlockIdempotent : LocalBlock → k[H]}
variable {ambientBlockIdempotent : AmbientBlock → k[G]}
variable {localBlocks : BlockIdempotentDecomposition localBlockIdempotent}
variable {ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent}
variable {I : CentralBrauerInterval (p := p) P H}
variable {localCatalogue : BlockCentralCharacterCatalogue localBlocks}

/-- Navarro's interval equality makes the induced central function
multiplicative. -/
theorem Navarro414IntervalCentralCharacterSource.isBlockInductionDefined
    (S : Navarro414IntervalCentralCharacterSource I localBlocks localCatalogue)
    (b : LocalBlock) :
    IsBlockInductionDefined H (localCatalogue.centralCharacter b) := by
  intro x y
  have hxy := LinearMap.congr_fun
    (S.inducedCentralFunction_eq_intervalBrauer b) (x * y)
  have hx := LinearMap.congr_fun
    (S.inducedCentralFunction_eq_intervalBrauer b) x
  have hy := LinearMap.congr_fun
    (S.inducedCentralFunction_eq_intervalBrauer b) y
  calc
    inducedCentralFunction H (localCatalogue.centralCharacter b) (x * y) =
        ((localCatalogue.centralCharacter b).comp
          (centralBrauerMapTo (k := k) (p := p) P H
            I.isPGroup I.centralizer_le I.le_normalizer)) (x * y) := hxy
    _ = ((localCatalogue.centralCharacter b).comp
          (centralBrauerMapTo (k := k) (p := p) P H
            I.isPGroup I.centralizer_le I.le_normalizer)) x *
        ((localCatalogue.centralCharacter b).comp
          (centralBrauerMapTo (k := k) (p := p) P H
            I.isPGroup I.centralizer_le I.le_normalizer)) y := by
      exact map_mul _ x y
    _ = inducedCentralFunction H (localCatalogue.centralCharacter b) x *
        inducedCentralFunction H (localCatalogue.centralCharacter b) y := by
      exact congrArg₂ (fun a b : k => a * b) hx.symm hy.symm

/-- The ambient block selected by the existing kernel uniqueness theorem. -/
noncomputable def navarro414InducedBlock
    (S : Navarro414IntervalCentralCharacterSource I localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (b : LocalBlock) : AmbientBlock :=
  inducedBlock H localCatalogue ambientCatalogue b
    (S.isBlockInductionDefined b)

/-- The selected ambient block is induced from the local block. -/
theorem navarro414InducedBlock_inducesTo
    (S : Navarro414IntervalCentralCharacterSource I localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (b : LocalBlock) :
    BlockInducesTo H localCatalogue ambientCatalogue b
      (navarro414InducedBlock S ambientCatalogue b) :=
  inducedBlock_spec H localCatalogue ambientCatalogue b
    (S.isBlockInductionDefined b)

/-- The selected ambient block central character is the Navarro interval
composite. -/
theorem navarro414InducedBlock_centralCharacter
    (S : Navarro414IntervalCentralCharacterSource I localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (b : LocalBlock) :
    ambientCatalogue.centralCharacter
        (navarro414InducedBlock S ambientCatalogue b) =
      (localCatalogue.centralCharacter b).comp
        (centralBrauerMapTo (k := k) (p := p) P H
          I.isPGroup I.centralizer_le I.le_normalizer) := by
  change ambientCatalogue.centralCharacter
      (inducedBlock H localCatalogue ambientCatalogue b
        (S.isBlockInductionDefined b)) = _
  calc
    ambientCatalogue.centralCharacter
        (inducedBlock H localCatalogue ambientCatalogue b
          (S.isBlockInductionDefined b)) =
      inducedCentralCharacter H (localCatalogue.centralCharacter b)
        (S.isBlockInductionDefined b) :=
      inducedBlock_centralCharacter H localCatalogue ambientCatalogue b
        (S.isBlockInductionDefined b)
    _ = (localCatalogue.centralCharacter b).comp
        (centralBrauerMapTo (k := k) (p := p) P H
          I.isPGroup I.centralizer_le I.le_normalizer) := by
      apply AlgHom.ext
      intro z
      change inducedCentralFunction H (localCatalogue.centralCharacter b) z = _
      exact LinearMap.congr_fun
        (S.inducedCentralFunction_eq_intervalBrauer b) z

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
