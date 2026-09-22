import Formalisation.IBAWAssembly
import Formalisation.FibreTransport

/-!
# Transport of manuscript-level data along an automorphism orbit

This file specialises the fibre-transport theorem to the faithful-sector and
block-orbit arguments in the manuscript.  A stabiliser-equivariant bijection
on one fibre is transported throughout a transitive orbit.  Equivariant labels
and pointwise compatibility predicates are proved to survive the transport.
-/

namespace Formalisation.IBAW

variable {A I L X Y : Type*} [Group A]
  [MulAction A I] [MulAction A L] [MulAction A X] [MulAction A Y]

/-- Any equivariant label preserved on the base fibre remains preserved after
transport throughout the orbit. -/
theorem transportedEquiv_preserves_label
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (labelX : X → L) (labelY : Y → L)
    (hlabelX : ∀ (a : A) (x : X), labelX (a • x) = a • labelX x)
    (hlabelY : ∀ (a : A) (y : Y), labelY (a • y) = a • labelY y)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i)
    (e₀ : Fibre pX i₀ ≃ Fibre pY i₀)
    (hbase : ∀ x : Fibre pX i₀, labelY (e₀ x) = labelX x)
    (x : X) :
    labelY (transportedEquiv pX pY hpX hpY i₀ t ht e₀ x) = labelX x := by
  let pull : Fibre pX i₀ :=
    (fibreFromBase pX hpX i₀ t ht (pX x)).symm ⟨x, rfl⟩
  have hpull : t (pX x) • (pull : X) = x := by
    have h := (fibreFromBase pX hpX i₀ t ht (pX x)).apply_symm_apply ⟨x, rfl⟩
    exact congrArg Subtype.val h
  rw [transportedEquiv_formula]
  calc
    labelY (t (pX x) • (e₀ pull : Y)) =
        t (pX x) • labelY (e₀ pull) := hlabelY _ _
    _ = t (pX x) • labelX pull := congrArg (t (pX x) • ·) (hbase pull)
    _ = labelX (t (pX x) • (pull : X)) := (hlabelX _ _).symm
    _ = labelX x := congrArg labelX hpull

/-- An equivariant predicate valid for every matched pair in the base fibre
remains valid for every transported pair. -/
theorem transportedEquiv_pairProperty
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i)
    (e₀ : Fibre pX i₀ ≃ Fibre pY i₀)
    (P : X → Y → Prop)
    (hP : PairPropertyEquivariant (A := A) (X := X) (Y := Y) P)
    (hbase : ∀ x : Fibre pX i₀, P x (e₀ x))
    (x : X) :
    P x (transportedEquiv pX pY hpX hpY i₀ t ht e₀ x) := by
  let pull : Fibre pX i₀ :=
    (fibreFromBase pX hpX i₀ t ht (pX x)).symm ⟨x, rfl⟩
  have hpull : t (pX x) • (pull : X) = x := by
    have h := (fibreFromBase pX hpX i₀ t ht (pX x)).apply_symm_apply ⟨x, rfl⟩
    exact congrArg Subtype.val h
  have htransported :
      P (t (pX x) • (pull : X)) (t (pX x) • (e₀ pull : Y)) :=
    (hP (t (pX x)) pull (e₀ pull)).mp (hbase pull)
  rw [transportedEquiv_formula]
  rwa [hpull] at htransported

section BlockOrbit

variable {B R S DZ : Type*}
  [MulAction A B] [MulAction A R] [MulAction A S] [MulAction A DZ]

variable {C : Context A B R S X Y DZ}

/-- Transport a stabiliser-equivariant equivalence from one block through a
transitive automorphism orbit of blocks.  Preservation of the induced block
follows from the source and target fibres. -/
def candidateOfBlockOrbit
    (b₀ : B) (t : B → A) (ht : ∀ b, t b • b₀ = b)
    (e₀ : Fibre C.brauerBlock b₀ ≃ Fibre C.weightBlock b₀)
    (he₀ : ∀ (h : A) (hh : h • b₀ = b₀)
      (x : Fibre C.brauerBlock b₀),
      e₀ (stabilizerFibreEquiv C.brauerBlock
          C.brauerBlock_equivariant b₀ h hh x) =
        stabilizerFibreEquiv C.weightBlock
          C.weightBlock_equivariant b₀ h hh (e₀ x)) : Candidate C where
  equiv := transportedEquiv C.brauerBlock C.weightBlock
    C.brauerBlock_equivariant C.weightBlock_equivariant b₀ t ht e₀
  equiv_equivariant := transportedEquiv_equivariant
    C.brauerBlock C.weightBlock C.brauerBlock_equivariant
    C.weightBlock_equivariant b₀ t ht e₀ he₀
  block_preserving := transportedEquiv_preserves_base
    C.brauerBlock C.weightBlock C.brauerBlock_equivariant
    C.weightBlock_equivariant b₀ t ht e₀

/-- The block-orbit candidate is independent of the selected transporters. -/
theorem candidateOfBlockOrbit_equiv_independent
    (b₀ : B) (t u : B → A)
    (ht : ∀ b, t b • b₀ = b) (hu : ∀ b, u b • b₀ = b)
    (e₀ : Fibre C.brauerBlock b₀ ≃ Fibre C.weightBlock b₀)
    (he₀ : ∀ (h : A) (hh : h • b₀ = b₀)
      (x : Fibre C.brauerBlock b₀),
      e₀ (stabilizerFibreEquiv C.brauerBlock
          C.brauerBlock_equivariant b₀ h hh x) =
        stabilizerFibreEquiv C.weightBlock
          C.weightBlock_equivariant b₀ h hh (e₀ x)) :
    (candidateOfBlockOrbit b₀ t ht e₀ he₀).equiv =
      (candidateOfBlockOrbit b₀ u hu e₀ he₀).equiv :=
  transportedEquiv_independent_of_transporter
    C.brauerBlock C.weightBlock C.brauerBlock_equivariant
    C.weightBlock_equivariant b₀ t u ht hu e₀ he₀

/-- On the base block, the transported candidate is the supplied fibre
equivalence itself. -/
theorem candidateOfBlockOrbit_on_base
    (b₀ : B) (t : B → A) (ht : ∀ b, t b • b₀ = b)
    (htBase : t b₀ = 1)
    (e₀ : Fibre C.brauerBlock b₀ ≃ Fibre C.weightBlock b₀)
    (he₀ : ∀ (h : A) (hh : h • b₀ = b₀)
      (x : Fibre C.brauerBlock b₀),
      e₀ (stabilizerFibreEquiv C.brauerBlock
          C.brauerBlock_equivariant b₀ h hh x) =
        stabilizerFibreEquiv C.weightBlock
          C.weightBlock_equivariant b₀ h hh (e₀ x))
    (x : Fibre C.brauerBlock b₀) :
    (candidateOfBlockOrbit b₀ t ht e₀ he₀).equiv (x : X) = (e₀ x : Y) := by
  let pulled : Fibre C.brauerBlock b₀ :=
    (fibreFromBase C.brauerBlock C.brauerBlock_equivariant
      b₀ t ht (C.brauerBlock (x : X))).symm ⟨(x : X), rfl⟩
  have hpulled : pulled = x := by
    apply Subtype.ext
    change (t (C.brauerBlock (x : X)))⁻¹ • (x : X) = x
    rw [x.property, htBase]
    simp
  change (transportedEquiv C.brauerBlock C.weightBlock
      C.brauerBlock_equivariant C.weightBlock_equivariant
      b₀ t ht e₀) (x : X) = (e₀ x : Y)
  rw [transportedEquiv_formula]
  change t (C.brauerBlock (x : X)) • (e₀ pulled).1 = (e₀ x).1
  rw [x.property, htBase, one_smul, hpulled]

/-- For a block-orbit candidate, the `Q = 1` equation on the base block
propagates to every block in the orbit. -/
theorem candidateOfBlockOrbit_normalisation
    (b₀ : B) (t : B → A) (ht : ∀ b, t b • b₀ = b)
    (htBase : t b₀ = 1)
    (e₀ : Fibre C.brauerBlock b₀ ≃ Fibre C.weightBlock b₀)
    (he₀ : ∀ (h : A) (hh : h • b₀ = b₀)
      (x : Fibre C.brauerBlock b₀),
      e₀ (stabilizerFibreEquiv C.brauerBlock
          C.brauerBlock_equivariant b₀ h hh x) =
        stabilizerFibreEquiv C.weightBlock
          C.weightBlock_equivariant b₀ h hh (e₀ x))
    (hbase : ∀ (d : DZ) (hd : C.brauerBlock (C.reduce d) = b₀),
      e₀ ⟨C.reduce d, hd⟩ =
        ⟨C.atOne d, (C.atOne_block d).trans hd⟩)
    (d : DZ) :
    (candidateOfBlockOrbit b₀ t ht e₀ he₀).equiv (C.reduce d) =
      C.atOne d := by
  let b := C.brauerBlock (C.reduce d)
  let a := t b
  let d₀ := a⁻¹ • d
  have hd₀ : C.brauerBlock (C.reduce d₀) = b₀ := by
    calc
      C.brauerBlock (C.reduce d₀) =
          C.brauerBlock (a⁻¹ • C.reduce d) := by
        rw [C.reduce_equivariant]
      _ = a⁻¹ • C.brauerBlock (C.reduce d) :=
        C.brauerBlock_equivariant _ _
      _ = a⁻¹ • b := rfl
      _ = b₀ := by
        calc
          a⁻¹ • b = a⁻¹ • (a • b₀) :=
            congrArg (a⁻¹ • ·) (ht b).symm
          _ = b₀ := inv_smul_smul a b₀
  have hrecover : a • d₀ = d := by
    simp only [d₀, smul_inv_smul]
  have hreduce : C.reduce d = a • C.reduce d₀ := by
    rw [← C.reduce_equivariant, hrecover]
  have hbaseValue :
      (candidateOfBlockOrbit b₀ t ht e₀ he₀).equiv (C.reduce d₀) =
        C.atOne d₀ := by
    calc
      (candidateOfBlockOrbit b₀ t ht e₀ he₀).equiv (C.reduce d₀) =
          (e₀ ⟨C.reduce d₀, hd₀⟩ : Fibre C.weightBlock b₀).1 :=
        candidateOfBlockOrbit_on_base b₀ t ht htBase e₀ he₀
          ⟨C.reduce d₀, hd₀⟩
      _ = C.atOne d₀ := congrArg Subtype.val (hbase d₀ hd₀)
  calc
    (candidateOfBlockOrbit b₀ t ht e₀ he₀).equiv (C.reduce d) =
        (candidateOfBlockOrbit b₀ t ht e₀ he₀).equiv
          (a • C.reduce d₀) := congrArg _ hreduce
    _ = a • (candidateOfBlockOrbit b₀ t ht e₀ he₀).equiv
          (C.reduce d₀) :=
      (candidateOfBlockOrbit b₀ t ht e₀ he₀).equiv_equivariant _ _
    _ = a • C.atOne d₀ := congrArg (a • ·) hbaseValue
    _ = C.atOne (a • d₀) := (C.atOne_equivariant _ _).symm
    _ = C.atOne d := congrArg C.atOne hrecover

/-- A certified bijection on one block gives global data when the action on
blocks is transitive.  The intermediate-block, extension, and
character-triple properties propagate by equivariance, and the base-block
normalisation propagates by `candidateOfBlockOrbit_normalisation`. -/
def dataOfBlockOrbit
    (b₀ : B) (t : B → A) (ht : ∀ b, t b • b₀ = b)
    (htBase : t b₀ = 1)
    (e₀ : Fibre C.brauerBlock b₀ ≃ Fibre C.weightBlock b₀)
    (he₀ : ∀ (h : A) (hh : h • b₀ = b₀)
      (x : Fibre C.brauerBlock b₀),
      e₀ (stabilizerFibreEquiv C.brauerBlock
          C.brauerBlock_equivariant b₀ h hh x) =
        stabilizerFibreEquiv C.weightBlock
          C.weightBlock_equivariant b₀ h hh (e₀ x))
    (hIntermediateBlockEqualities : ∀ x : Fibre C.brauerBlock b₀,
      C.intermediateBlockEqualitiesOK x (e₀ x))
    (hextensions : ∀ x : Fibre C.brauerBlock b₀,
      C.extensionsOK x (e₀ x))
    (htriples : ∀ x : Fibre C.brauerBlock b₀,
      C.characterTripleOK x (e₀ x))
    (hnormalisation : ∀ (d : DZ)
      (hd : C.brauerBlock (C.reduce d) = b₀),
      e₀ ⟨C.reduce d, hd⟩ =
        ⟨C.atOne d, (C.atOne_block d).trans hd⟩) : Data C where
  toCandidate := candidateOfBlockOrbit b₀ t ht e₀ he₀
  intermediateBlockEqualities := transportedEquiv_pairProperty
    C.brauerBlock C.weightBlock C.brauerBlock_equivariant
    C.weightBlock_equivariant b₀ t ht e₀ C.intermediateBlockEqualitiesOK
    C.intermediateBlockEqualities_equivariant hIntermediateBlockEqualities
  extensions := transportedEquiv_pairProperty
    C.brauerBlock C.weightBlock C.brauerBlock_equivariant
    C.weightBlock_equivariant b₀ t ht e₀ C.extensionsOK
    C.extensions_equivariant hextensions
  characterTriple := transportedEquiv_pairProperty
    C.brauerBlock C.weightBlock C.brauerBlock_equivariant
    C.weightBlock_equivariant b₀ t ht e₀ C.characterTripleOK
    C.characterTriple_equivariant htriples
  normalisation := candidateOfBlockOrbit_normalisation
    b₀ t ht htBase e₀ he₀ hnormalisation

end BlockOrbit

section SectorOrbit

variable {B R S DZ : Type*}
  [MulAction A B] [MulAction A R] [MulAction A S] [MulAction A DZ]

variable {C : Context A B R S X Y DZ}

/-- Transport a stabiliser-equivariant bijection from one central character
sector to a transitive orbit of sectors.  Block preservation on the base
sector propagates automatically. -/
def candidateOfSectorOrbit
    (s₀ : S) (t : S → A) (ht : ∀ s, t s • s₀ = s)
    (e₀ : Fibre (brauerSector C) s₀ ≃ Fibre (weightSector C) s₀)
    (he₀ : ∀ (h : A) (hh : h • s₀ = s₀)
      (x : Fibre (brauerSector C) s₀),
      e₀ (stabilizerFibreEquiv (brauerSector C)
          (brauerSector_equivariant (C := C)) s₀ h hh x) =
        stabilizerFibreEquiv (weightSector C)
          (weightSector_equivariant (C := C)) s₀ h hh (e₀ x))
    (hblock : ∀ x : Fibre (brauerSector C) s₀,
      C.weightBlock (e₀ x) = C.brauerBlock x) : Candidate C where
  equiv := transportedEquiv (brauerSector C) (weightSector C)
    (brauerSector_equivariant (C := C))
    (weightSector_equivariant (C := C)) s₀ t ht e₀
  equiv_equivariant := transportedEquiv_equivariant
    (brauerSector C) (weightSector C)
    (brauerSector_equivariant (C := C))
    (weightSector_equivariant (C := C)) s₀ t ht e₀ he₀
  block_preserving := transportedEquiv_preserves_label
    (brauerSector C) (weightSector C)
    (brauerSector_equivariant (C := C))
    (weightSector_equivariant (C := C))
    C.brauerBlock C.weightBlock
    C.brauerBlock_equivariant C.weightBlock_equivariant
    s₀ t ht e₀ hblock

/-- The transported sector equivalence is independent of the selected
transporters. -/
theorem candidateOfSectorOrbit_equiv_independent
    (s₀ : S) (t u : S → A)
    (ht : ∀ s, t s • s₀ = s) (hu : ∀ s, u s • s₀ = s)
    (e₀ : Fibre (brauerSector C) s₀ ≃ Fibre (weightSector C) s₀)
    (he₀ : ∀ (h : A) (hh : h • s₀ = s₀)
      (x : Fibre (brauerSector C) s₀),
      e₀ (stabilizerFibreEquiv (brauerSector C)
          (brauerSector_equivariant (C := C)) s₀ h hh x) =
        stabilizerFibreEquiv (weightSector C)
          (weightSector_equivariant (C := C)) s₀ h hh (e₀ x))
    (hblock : ∀ x : Fibre (brauerSector C) s₀,
      C.weightBlock (e₀ x) = C.brauerBlock x) :
    (candidateOfSectorOrbit s₀ t ht e₀ he₀ hblock).equiv =
      (candidateOfSectorOrbit s₀ u hu e₀ he₀ hblock).equiv :=
  transportedEquiv_independent_of_transporter
    (brauerSector C) (weightSector C)
    (brauerSector_equivariant (C := C))
    (weightSector_equivariant (C := C))
    s₀ t u ht hu e₀ he₀

/-- Upgrade sector-orbit transport to full iBAW data.  The three base-fibre
compatibility assertions propagate by equivariance.  The `Q=1`
normalisation is stated separately because defect-zero objects may lie in
several sectors. -/
def dataOfSectorOrbit
    (s₀ : S) (t : S → A) (ht : ∀ s, t s • s₀ = s)
    (e₀ : Fibre (brauerSector C) s₀ ≃ Fibre (weightSector C) s₀)
    (he₀ : ∀ (h : A) (hh : h • s₀ = s₀)
      (x : Fibre (brauerSector C) s₀),
      e₀ (stabilizerFibreEquiv (brauerSector C)
          (brauerSector_equivariant (C := C)) s₀ h hh x) =
        stabilizerFibreEquiv (weightSector C)
          (weightSector_equivariant (C := C)) s₀ h hh (e₀ x))
    (hblock : ∀ x : Fibre (brauerSector C) s₀,
      C.weightBlock (e₀ x) = C.brauerBlock x)
    (hIntermediateBlockEqualities : ∀ x : Fibre (brauerSector C) s₀,
      C.intermediateBlockEqualitiesOK x (e₀ x))
    (hextensions : ∀ x : Fibre (brauerSector C) s₀,
      C.extensionsOK x (e₀ x))
    (htriples : ∀ x : Fibre (brauerSector C) s₀,
      C.characterTripleOK x (e₀ x))
    (hnormalisation : ∀ d : DZ,
      (candidateOfSectorOrbit s₀ t ht e₀ he₀ hblock).equiv (C.reduce d) =
        C.atOne d) : Data C where
  toCandidate := candidateOfSectorOrbit s₀ t ht e₀ he₀ hblock
  intermediateBlockEqualities := transportedEquiv_pairProperty
    (brauerSector C) (weightSector C)
    (brauerSector_equivariant (C := C))
    (weightSector_equivariant (C := C))
    s₀ t ht e₀ C.intermediateBlockEqualitiesOK
      C.intermediateBlockEqualities_equivariant hIntermediateBlockEqualities
  extensions := transportedEquiv_pairProperty
    (brauerSector C) (weightSector C)
    (brauerSector_equivariant (C := C))
    (weightSector_equivariant (C := C))
    s₀ t ht e₀ C.extensionsOK C.extensions_equivariant hextensions
  characterTriple := transportedEquiv_pairProperty
    (brauerSector C) (weightSector C)
    (brauerSector_equivariant (C := C))
    (weightSector_equivariant (C := C))
    s₀ t ht e₀ C.characterTripleOK C.characterTriple_equivariant htriples
  normalisation := hnormalisation

end SectorOrbit

end Formalisation.IBAW


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
