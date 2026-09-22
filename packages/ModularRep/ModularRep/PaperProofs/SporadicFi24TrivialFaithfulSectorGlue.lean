import ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Actual
import ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

/-!
# Gluing the trivial and faithful Fischer central sectors

For `3.Fi'24` away from characteristic `3`, the construction uses two
different inputs. The trivial central character sector is transported through
the central `ell'`-quotient to `Fi'24`. Transport along the automorphism action
constructs the maps on both faithful sectors from a map on one of them.

This file is only the set-theoretic and equivariance adapter between those two
routes.  The quotient theorem is deliberately represented by a source record
on the single trivial fibre; it is not rebuilt here.  The faithful map is
constructed by `lemma_5_5_actual` from its one-sector source.  No global
character--weight family, Spath Lemma 6.1 input, or iBAW conclusion is a
premise.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24TrivialFaithfulSectorGlue

open Formalisation
open Formalisation.IBAW
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Actual

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
variable (blockSource : LiteralCarrierAdapter
  (p := p) (k := k) (K := K) (X := X))
variable (E1 : RoutineTransportInput iota hinj blocks blockSource)

variable (ModularCharacterTriple :
  IBr iota → WeightClass (p := p) (K := K) (X := X) → Prop)

omit [IsAlgClosed k]
  [Invertible (Fintype.card (Subgroup.center X) : k)] [Fintype X] in
/-- Every automorphism fixes the literal trivial central character. -/
@[simp]
theorem smul_trivialSector (a : (MulAut X)ᵐᵒᵖ) :
    a • (1 : CentralSector (k := k) (X := X)) = 1 := by
  ext z
  rfl

/-- The exact centre-`C3` coverage fact used by the glue.  Its concrete
Fischer instance is external: a central character is faithful exactly when it
is not the trivial character.  The fact that there are two such characters is
needed to supply the sector transporter, but is not an additional input
to this set-theoretic gluing step. -/
structure ThreeSectorCoverage : Prop where
  faithful_iff_ne_trivial : ∀ nu : CentralSector (k := k) (X := X),
    Function.Injective nu ↔ nu ≠ 1

/-- Mixed E1/E2/U interface for transport through the central `ell'`-quotient
on the trivial sector.  Its equivalence, equivariance, and block-induction
fields are E1/U transport data; its character-triple field is E2/U.  These are
precisely the equivalence and three properties consumed by
`AnDietrichSectorInput`.

In the Fischer application these fields are to be instantiated by inflation
from `Fi'24`; this record does not attempt to reconstruct quotient character,
weight, block-induction, or character-triple theory. -/
structure TrivialSectorQuotientSource where
  equiv :
    Fibre (brauerSector iota hinj blocks)
        (1 : CentralSector (k := k) (X := X)) ≃
      Fibre (weightSector (R := blockSource))
        (1 : CentralSector (k := k) (X := X))
  equivariant : ∀ (a : (MulAut X)ᵐᵒᵖ)
      (phi : Fibre (brauerSector iota hinj blocks)
        (1 : CentralSector (k := k) (X := X))),
    equiv
        (stabilizerFibreEquiv
          (brauerSector iota hinj blocks)
          (brauerSector_equivariant iota hinj blocks E1)
          (1 : CentralSector (k := k) (X := X)) a
          (smul_trivialSector (k := k) (X := X) a) phi) =
      stabilizerFibreEquiv
        (weightSector (R := blockSource))
        (weightSector_equivariant_actual
          (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := blockSource) E1)
        (1 : CentralSector (k := k) (X := X)) a
        (smul_trivialSector (k := k) (X := X) a) (equiv phi)
  blockInduction : ∀ phi :
      Fibre (brauerSector iota hinj blocks)
        (1 : CentralSector (k := k) (X := X)),
    blockSource.1.weightBlock (equiv phi) =
      brauerBlock iota hinj blocks phi
  characterTriple : ∀ phi :
      Fibre (brauerSector iota hinj blocks)
        (1 : CentralSector (k := k) (X := X)),
    ModularCharacterTriple phi (equiv phi)

/-- Restriction of the global modular character-triple predicate to the
faithful carriers used in the sector transport construction. -/
abbrev FaithfulCharacterTriple
    (phi : FaithfulIBr iota hinj blocks blockSource E1)
    (w : FaithfulWeight iota hinj blocks blockSource E1) : Prop :=
  ModularCharacterTriple phi.val w.val

namespace ThreeSectorCoverage

variable (C : ThreeSectorCoverage (k := k) (X := X))

/-- The complement of the trivial Brauer sector is exactly the faithful
Brauer carrier. -/
def brauerComplementEquivFaithful :
    {phi : IBr iota //
      brauerSector iota hinj blocks phi ≠
        (1 : CentralSector (k := k) (X := X))} ≃
      FaithfulIBr iota hinj blocks blockSource E1 where
  toFun phi :=
    ⟨phi.1, (C.faithful_iff_ne_trivial
      (brauerSector iota hinj blocks phi.1)).2 phi.2⟩
  invFun phi :=
    ⟨phi.val, (C.faithful_iff_ne_trivial
      (brauerSector iota hinj blocks phi.val)).1 phi.faithful⟩
  left_inv phi := by
    apply Subtype.ext
    rfl
  right_inv phi := by
    cases phi
    rfl

/-- The complement of the trivial weight sector is exactly the faithful
set of weights. -/
def weightComplementEquivFaithful :
    {w : WeightClass (p := p) (K := K) (X := X) //
      weightSector (R := blockSource) w ≠
        (1 : CentralSector (k := k) (X := X))} ≃
      FaithfulWeight iota hinj blocks blockSource E1 where
  toFun w :=
    ⟨w.1, (C.faithful_iff_ne_trivial
      (weightSector (R := blockSource) w.1)).2 w.2⟩
  invFun w :=
    ⟨w.val, (C.faithful_iff_ne_trivial
      (weightSector (R := blockSource) w.val)).1 w.faithful⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv w := by
    cases w
    rfl

end ThreeSectorCoverage

variable (coverage : ThreeSectorCoverage (k := k) (X := X))
variable (trivial : TrivialSectorQuotientSource iota hinj blocks blockSource E1
  ModularCharacterTriple)

variable (faithfulCharacterTriple_equivariant :
  PairPropertyEquivariant
    (A := (MulAut X)ᵐᵒᵖ)
    (X := FaithfulIBr iota hinj blocks blockSource E1)
    (Y := FaithfulWeight iota hinj blocks blockSource E1)
    (FaithfulCharacterTriple iota hinj blocks blockSource E1
      ModularCharacterTriple))

variable (faithfulSource : AnDietrichFaithfulSectorSource
  iota hinj blocks blockSource E1
  (FaithfulCharacterTriple iota hinj blocks blockSource E1
    ModularCharacterTriple)
  faithfulCharacterTriple_equivariant)

private def faithfulClauses : ActualLemma55Clauses
    iota hinj blocks blockSource E1
      (FaithfulCharacterTriple iota hinj blocks blockSource E1
        ModularCharacterTriple) :=
  lemma_5_5_actual iota hinj blocks blockSource E1
    (FaithfulCharacterTriple iota hinj blocks blockSource E1
      ModularCharacterTriple)
    faithfulCharacterTriple_equivariant faithfulSource

private def faithfulComplementEquiv :
    {phi : IBr iota //
      brauerSector iota hinj blocks phi ≠
        (1 : CentralSector (k := k) (X := X))} ≃
      {w : WeightClass (p := p) (K := K) (X := X) //
        weightSector (R := blockSource) w ≠
          (1 : CentralSector (k := k) (X := X))} :=
  (coverage.brauerComplementEquivFaithful
      iota hinj blocks blockSource E1).trans
    ((faithfulClauses iota hinj blocks blockSource E1
      ModularCharacterTriple faithfulCharacterTriple_equivariant
      faithfulSource).equiv.trans
      (coverage.weightComplementEquivFaithful
        iota hinj blocks blockSource E1).symm)

/-- Disjoint union of the quotient-transported trivial map and the faithful
map constructed by transport between faithful sectors. -/
def gluedEquiv :
    IBr iota ≃ WeightClass (p := p) (K := K) (X := X) := by
  classical
  exact
    (Equiv.sumCompl (fun phi : IBr iota =>
      brauerSector iota hinj blocks phi =
        (1 : CentralSector (k := k) (X := X)))).symm |>.trans
      ((Equiv.sumCongr trivial.equiv
        (faithfulComplementEquiv iota hinj blocks blockSource E1
          ModularCharacterTriple coverage
          faithfulCharacterTriple_equivariant faithfulSource)).trans
        (Equiv.sumCompl (fun w : WeightClass (p := p) (K := K) (X := X) =>
          weightSector (R := blockSource) w =
            (1 : CentralSector (k := k) (X := X)))))

@[simp]
theorem gluedEquiv_apply_trivial (phi : IBr iota)
    (hphi : brauerSector iota hinj blocks phi =
      (1 : CentralSector (k := k) (X := X))) :
    gluedEquiv iota hinj blocks blockSource E1 ModularCharacterTriple
        coverage trivial faithfulCharacterTriple_equivariant faithfulSource phi =
      (trivial.equiv ⟨phi, hphi⟩).1 := by
  classical
  simp [gluedEquiv, hphi]

@[simp]
theorem gluedEquiv_apply_faithful (phi : IBr iota)
    (hphi : brauerSector iota hinj blocks phi ≠
      (1 : CentralSector (k := k) (X := X))) :
    gluedEquiv iota hinj blocks blockSource E1 ModularCharacterTriple
        coverage trivial faithfulCharacterTriple_equivariant faithfulSource phi =
      ((faithfulClauses iota hinj blocks blockSource E1
        ModularCharacterTriple faithfulCharacterTriple_equivariant
        faithfulSource).equiv
        ⟨phi, (coverage.faithful_iff_ne_trivial
          (brauerSector iota hinj blocks phi)).2 hphi⟩).val := by
  classical
  simp [gluedEquiv, faithfulComplementEquiv,
    ThreeSectorCoverage.brauerComplementEquivFaithful,
    ThreeSectorCoverage.weightComplementEquivFaithful, hphi]

/-- The glued equivalence preserves the literal central character sector. -/
theorem gluedEquiv_preserves_sector (phi : IBr iota) :
    weightSector (R := blockSource)
        (gluedEquiv iota hinj blocks blockSource E1 ModularCharacterTriple
          coverage trivial faithfulCharacterTriple_equivariant faithfulSource phi) =
      brauerSector iota hinj blocks phi := by
  by_cases hphi : brauerSector iota hinj blocks phi =
      (1 : CentralSector (k := k) (X := X))
  · rw [gluedEquiv_apply_trivial iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource phi hphi]
    exact (trivial.equiv ⟨phi, hphi⟩).2.trans hphi.symm
  · rw [gluedEquiv_apply_faithful iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource phi hphi]
    let fphi : FaithfulIBr iota hinj blocks blockSource E1 :=
      ⟨phi, (coverage.faithful_iff_ne_trivial
        (brauerSector iota hinj blocks phi)).2 hphi⟩
    exact congrArg Subtype.val
      ((faithfulClauses iota hinj blocks blockSource E1
        ModularCharacterTriple faithfulCharacterTriple_equivariant
        faithfulSource).sectorPreservation fphi)

/-- The glued equivalence commutes with every automorphism.  The proof has no
cross-term: automorphisms fix the trivial character and preserve faithfulness. -/
theorem gluedEquiv_equivariant (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    gluedEquiv iota hinj blocks blockSource E1 ModularCharacterTriple
        coverage trivial faithfulCharacterTriple_equivariant faithfulSource
        (a • phi) =
      a • gluedEquiv iota hinj blocks blockSource E1 ModularCharacterTriple
        coverage trivial faithfulCharacterTriple_equivariant faithfulSource phi := by
  by_cases hphi : brauerSector iota hinj blocks phi =
      (1 : CentralSector (k := k) (X := X))
  · have hact : brauerSector iota hinj blocks (a • phi) =
        (1 : CentralSector (k := k) (X := X)) := by
      rw [brauerSector_equivariant iota hinj blocks E1, hphi,
        smul_trivialSector]
    rw [gluedEquiv_apply_trivial iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource (a • phi) hact,
      gluedEquiv_apply_trivial iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource phi hphi]
    exact congrArg Subtype.val (trivial.equivariant a ⟨phi, hphi⟩)
  · let fphi : FaithfulIBr iota hinj blocks blockSource E1 :=
      ⟨phi, (coverage.faithful_iff_ne_trivial
        (brauerSector iota hinj blocks phi)).2 hphi⟩
    have hactFaithful :
        Function.Injective (brauerSector iota hinj blocks (a • phi)) := by
      exact (a • fphi).faithful
    have hact : brauerSector iota hinj blocks (a • phi) ≠
        (1 : CentralSector (k := k) (X := X)) :=
      (coverage.faithful_iff_ne_trivial
        (brauerSector iota hinj blocks (a • phi))).1 hactFaithful
    rw [gluedEquiv_apply_faithful iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource (a • phi) hact,
      gluedEquiv_apply_faithful iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource phi hphi]
    exact congrArg (fun w : FaithfulWeight iota hinj blocks blockSource E1 => w.val)
      ((faithfulClauses iota hinj blocks blockSource E1
        ModularCharacterTriple faithfulCharacterTriple_equivariant
        faithfulSource).automorphismTransport a fphi)

/-- Block induction is checked in the unique component containing `phi`. -/
theorem gluedEquiv_preserves_blockInduction (phi : IBr iota) :
    blockSource.1.weightBlock
        (gluedEquiv iota hinj blocks blockSource E1 ModularCharacterTriple
          coverage trivial faithfulCharacterTriple_equivariant faithfulSource phi) =
      brauerBlock iota hinj blocks phi := by
  by_cases hphi : brauerSector iota hinj blocks phi =
      (1 : CentralSector (k := k) (X := X))
  · rw [gluedEquiv_apply_trivial iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource phi hphi]
    exact trivial.blockInduction ⟨phi, hphi⟩
  · rw [gluedEquiv_apply_faithful iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource phi hphi]
    exact (faithfulClauses iota hinj blocks blockSource E1
      ModularCharacterTriple faithfulCharacterTriple_equivariant
      faithfulSource).blockPreservation
        ⟨phi, (coverage.faithful_iff_ne_trivial
          (brauerSector iota hinj blocks phi)).2 hphi⟩

/-- The modular character-triple clause is inherited componentwise from the
quotient source and the faithful sector transport construction. -/
theorem gluedEquiv_characterTriple (phi : IBr iota) :
    ModularCharacterTriple phi
      (gluedEquiv iota hinj blocks blockSource E1 ModularCharacterTriple
        coverage trivial faithfulCharacterTriple_equivariant faithfulSource phi) := by
  by_cases hphi : brauerSector iota hinj blocks phi =
      (1 : CentralSector (k := k) (X := X))
  · rw [gluedEquiv_apply_trivial iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource phi hphi]
    exact trivial.characterTriple ⟨phi, hphi⟩
  · rw [gluedEquiv_apply_faithful iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource phi hphi]
    exact (faithfulClauses iota hinj blocks blockSource E1
      ModularCharacterTriple faithfulCharacterTriple_equivariant
      faithfulSource).characterTriple
        ⟨phi, (coverage.faithful_iff_ne_trivial
          (brauerSector iota hinj blocks phi)).2 hphi⟩

/-- Turn the glued global equivalence back into the fibre-family shape expected
by `AnDietrichSectorInput`.  The equivalence is itself constructed above; it is
not a premise. -/
def gluedFamily : EquivariantFibreEquiv
    (brauerSector iota hinj blocks)
    (weightSector (R := blockSource))
    (brauerSector_equivariant iota hinj blocks E1)
    (weightSector_equivariant_actual
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := blockSource) E1) where
  fibreEquiv sector :=
    { toFun := fun phi =>
        ⟨gluedEquiv iota hinj blocks blockSource E1 ModularCharacterTriple
          coverage trivial faithfulCharacterTriple_equivariant faithfulSource phi,
          (gluedEquiv_preserves_sector iota hinj blocks blockSource E1
            ModularCharacterTriple coverage trivial
            faithfulCharacterTriple_equivariant faithfulSource phi).trans phi.2⟩
      invFun := fun w =>
        ⟨(gluedEquiv iota hinj blocks blockSource E1 ModularCharacterTriple
          coverage trivial faithfulCharacterTriple_equivariant
          faithfulSource).symm w, by
          have hsector := gluedEquiv_preserves_sector iota hinj blocks
            blockSource E1 ModularCharacterTriple coverage trivial
            faithfulCharacterTriple_equivariant faithfulSource
            ((gluedEquiv iota hinj blocks blockSource E1 ModularCharacterTriple
              coverage trivial faithfulCharacterTriple_equivariant
              faithfulSource).symm w)
          rw [(gluedEquiv iota hinj blocks blockSource E1
            ModularCharacterTriple coverage trivial
            faithfulCharacterTriple_equivariant
            faithfulSource).apply_symm_apply] at hsector
          exact hsector.symm.trans w.2⟩
      left_inv := by
        intro phi
        apply Subtype.ext
        exact (gluedEquiv iota hinj blocks blockSource E1
          ModularCharacterTriple coverage trivial
          faithfulCharacterTriple_equivariant faithfulSource).symm_apply_apply phi
      right_inv := by
        intro w
        apply Subtype.ext
        exact (gluedEquiv iota hinj blocks blockSource E1
          ModularCharacterTriple coverage trivial
          faithfulCharacterTriple_equivariant faithfulSource).apply_symm_apply w }
  map_actFibre a sector phi := by
    apply Subtype.ext
    exact gluedEquiv_equivariant iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource a phi

/-- Smallest noncircular adapter for the corrected Fischer synthesis.  It
constructs the all-sector `AnDietrichSectorInput` from the one trivial-sector
quotient source, centre coverage, and the source for transport from one
faithful sector. -/
def anDietrichSectorInput : AnDietrichSectorInput
    iota hinj blocks E1 ModularCharacterTriple where
  family := gluedFamily iota hinj blocks blockSource E1 ModularCharacterTriple
    coverage trivial faithfulCharacterTriple_equivariant faithfulSource
  blockInduction _sector phi :=
    gluedEquiv_preserves_blockInduction iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource phi
  characterTriple _sector phi :=
    gluedEquiv_characterTriple iota hinj blocks blockSource E1
      ModularCharacterTriple coverage trivial
      faithfulCharacterTriple_equivariant faithfulSource phi

end ModularRep.PaperProofs.SporadicFi24TrivialFaithfulSectorGlue


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
