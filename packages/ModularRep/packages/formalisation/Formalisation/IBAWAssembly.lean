import Formalisation.IBAWCore
import Formalisation.IndexedAssembly

/-!
# Construction of manuscript-level iBAW data

This file turns coherent bijections on block or sector fibres into one global
candidate or fully certified datum.  It proves the set-theoretic content of
blockwise and central-sector construction.  The existence of the fibrewise
bijections and the representation theoretic compatibility predicates remain
explicit hypotheses.
-/

namespace Formalisation.IBAW

variable {A B R S X Y DZ I : Type*} [Group A]
  [MulAction A B] [MulAction A R] [MulAction A S]
  [MulAction A X] [MulAction A Y] [MulAction A DZ]
  [MulAction A I]

variable {C : Context A B R S X Y DZ}

/-- Combine a coherent family of labelled fibre bijections into an iBAW
candidate.  Block preservation is checked on each fibre and is not built into
the definition of the index set. -/
def candidateOfIndexedFibres
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (F : EquivariantFibreEquiv pX pY hpX hpY)
    (hblock : ∀ (i : I) (x : Fibre pX i),
      C.weightBlock (F.fibreEquiv i x) = C.brauerBlock x) : Candidate C where
  equiv := F.assemble
  equiv_equivariant := F.assemble_equivariant
  block_preserving x := by
    simpa only [EquivariantFibreEquiv.assemble_apply] using
      hblock (pX x) ⟨x, rfl⟩

/-- Add the character-theoretic obligations and `Q=1` normalisation to an
combined candidate.  These obligations are kept as separate hypotheses so
that an arbitrary set bijection cannot be mistaken for an iBAW bijection. -/
def dataOfIndexedFibres
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (F : EquivariantFibreEquiv pX pY hpX hpY)
    (hblock : ∀ (i : I) (x : Fibre pX i),
      C.weightBlock (F.fibreEquiv i x) = C.brauerBlock x)
    (hIntermediateBlockEqualities : ∀ (i : I) (x : Fibre pX i),
      C.intermediateBlockEqualitiesOK x (F.fibreEquiv i x))
    (hextensions : ∀ (i : I) (x : Fibre pX i),
      C.extensionsOK x (F.fibreEquiv i x))
    (htriples : ∀ (i : I) (x : Fibre pX i),
      C.characterTripleOK x (F.fibreEquiv i x))
    (hnormalisation : ∀ d : DZ, F.assemble (C.reduce d) = C.atOne d) : Data C where
  toCandidate := candidateOfIndexedFibres pX pY hpX hpY F hblock
  intermediateBlockEqualities x := by
    change C.intermediateBlockEqualitiesOK x (F.assemble x)
    rw [EquivariantFibreEquiv.assemble_apply]
    exact hIntermediateBlockEqualities (pX x) ⟨x, rfl⟩
  extensions x := by
    change C.extensionsOK x (F.assemble x)
    rw [EquivariantFibreEquiv.assemble_apply]
    exact hextensions (pX x) ⟨x, rfl⟩
  characterTriple x := by
    change C.characterTripleOK x (F.assemble x)
    rw [EquivariantFibreEquiv.assemble_apply]
    exact htriples (pX x) ⟨x, rfl⟩
  normalisation := hnormalisation

/-- The sector of a Brauer object, determined by its block. -/
def brauerSector (C : Context A B R S X Y DZ) (x : X) : S :=
  C.blockSector (C.brauerBlock x)

/-- The sector of a local object, determined by its induced block. -/
def weightSector (C : Context A B R S X Y DZ) (y : Y) : S :=
  C.blockSector (C.weightBlock y)

theorem brauerSector_equivariant (a : A) (x : X) :
    brauerSector C (a • x) = a • brauerSector C x := by
  simp only [brauerSector, C.brauerBlock_equivariant,
    C.blockSector_equivariant]

theorem weightSector_equivariant (a : A) (y : Y) :
    weightSector C (a • y) = a • weightSector C y := by
  simp only [weightSector, C.weightBlock_equivariant,
    C.blockSector_equivariant]

/-- Construction over block fibres.  Since the index itself is the block, block
preservation follows from the codomain fibre of each local equivalence. -/
def dataOfBlockFibres
    (F : EquivariantFibreEquiv C.brauerBlock C.weightBlock
      C.brauerBlock_equivariant C.weightBlock_equivariant)
    (hIntermediateBlockEqualities : ∀ (b : B) (x : Fibre C.brauerBlock b),
      C.intermediateBlockEqualitiesOK x (F.fibreEquiv b x))
    (hextensions : ∀ (b : B) (x : Fibre C.brauerBlock b),
      C.extensionsOK x (F.fibreEquiv b x))
    (htriples : ∀ (b : B) (x : Fibre C.brauerBlock b),
      C.characterTripleOK x (F.fibreEquiv b x))
    (hnormalisation : ∀ d : DZ, F.assemble (C.reduce d) = C.atOne d) : Data C :=
  dataOfIndexedFibres C.brauerBlock C.weightBlock
    C.brauerBlock_equivariant C.weightBlock_equivariant F
    (fun b x => by
      calc
        C.weightBlock (F.fibreEquiv b x) = b := (F.fibreEquiv b x).property
        _ = C.brauerBlock x := x.property.symm)
    hIntermediateBlockEqualities hextensions htriples hnormalisation

/-- Construction over central character sectors.  Fibrewise block preservation is
still required because a sector may contain several blocks.  This is the pure
construction step in the manuscript's central-sector lemma. -/
def dataOfSectorFibres
    (F : EquivariantFibreEquiv (brauerSector C) (weightSector C)
      (brauerSector_equivariant (C := C))
      (weightSector_equivariant (C := C)))
    (hblock : ∀ (s : S) (x : Fibre (brauerSector C) s),
      C.weightBlock (F.fibreEquiv s x) = C.brauerBlock x)
    (hIntermediateBlockEqualities : ∀ (s : S) (x : Fibre (brauerSector C) s),
      C.intermediateBlockEqualitiesOK x (F.fibreEquiv s x))
    (hextensions : ∀ (s : S) (x : Fibre (brauerSector C) s),
      C.extensionsOK x (F.fibreEquiv s x))
    (htriples : ∀ (s : S) (x : Fibre (brauerSector C) s),
      C.characterTripleOK x (F.fibreEquiv s x))
    (hnormalisation : ∀ d : DZ, F.assemble (C.reduce d) = C.atOne d) : Data C :=
  dataOfIndexedFibres (brauerSector C) (weightSector C)
    (brauerSector_equivariant (C := C))
    (weightSector_equivariant (C := C)) F
    hblock hIntermediateBlockEqualities hextensions htriples hnormalisation

end Formalisation.IBAW


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
