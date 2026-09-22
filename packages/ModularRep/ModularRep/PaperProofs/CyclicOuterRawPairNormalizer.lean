import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre
import ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

/-!
# A raw character weight stabiliser as a local normaliser

For a raw character weight `r = (Q, theta)` in a semidirect product
`H semidirect E`, this module identifies its stabiliser with the intersection
of the stabiliser of the ambient `H`-class of `r` and the normaliser of the
embedded subgroup `Q`.  The converse uses the kernel proved orbit-fibre
uniqueness theorem: an ambient orbit and a literal radical subgroup determine
at most one raw representative.

No character extension, block induction relation, BAW conclusion, or iBAW
conclusion is assumed here.
-/

noncomputable section

namespace ModularRep.PaperProofs.CyclicOuterRawPairNormalizer

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {p : ℕ} {K H E : Type u}
variable [Field K] [CharZero K] [Group H] [Fintype H]
variable [Group E] [Fintype E] [IsCyclic E]

/-! ## Orbit and support uniqueness -/

/-- The support used by `radicalOrbitData` has the same underlying subgroup
as `rawSubgroup`. -/
@[simp]
theorem radicalSubgroupOfIsoClass_val_eq_rawSubgroup
    (r : RawWeightClass (p := p) (K := K) (H := H)) :
    (radicalSubgroupOfIsoClass r).1 = rawSubgroup r := by
  refine Quotient.inductionOn r ?_
  intro W
  rfl

/-- The ambient conjugacy class and the literal radical subgroup determine a
raw character weight isomorphism class uniquely. -/
theorem isoClass_eq_of_conjugacyClass_eq_of_rawSubgroup_eq
    (r s : RawWeightClass (p := p) (K := K) (H := H))
    (horbit :
      (Quotient.mk'' r : ConjugacyClass (p := p) (K := K) (G := H)) =
        Quotient.mk'' s)
    (hsupport : rawSubgroup r = rawSubgroup s) :
    r = s := by
  let D := radicalOrbitData (p := p) (K := K) (G := H)
  let support := radicalSubgroupOfIsoClass r
  let r' : D.FixedFibre support := ⟨r, by
    change radicalSubgroupOfIsoClass r = support
    rfl⟩
  let s' : D.FixedFibre support := ⟨s, by
    change radicalSubgroupOfIsoClass s = radicalSubgroupOfIsoClass r
    apply Subtype.ext
    simpa using hsupport.symm⟩
  have hfibre : D.toOrbitFibre support r' = D.toOrbitFibre support s' := by
    apply Subtype.ext
    exact horbit
  have hrs : r' = s' := D.toOrbitFibre_injective support hfibre
  exact congrArg Subtype.val hrs

/-! ## Canonical actions and the embedded radical -/

/-- The canonical inner action on ambient character-weight classes. -/
abbrev canonicalWeightHAction :
    MulAction H (ConjugacyClass (p := p) (K := K) (G := H)) :=
  rightAutomorphismAction
    (X := ConjugacyClass (p := p) (K := K) (G := H))
    (MulAut.conj : H →* MulAut H)

/-- The canonical outer action on ambient character-weight classes. -/
abbrev canonicalWeightEAction (phi : E →* MulAut H) :
    MulAction E (ConjugacyClass (p := p) (K := K) (G := H)) :=
  rightAutomorphismAction
    (X := ConjugacyClass (p := p) (K := K) (G := H)) phi

/-- The canonical semidirect action on ambient character-weight classes. -/
abbrev canonicalWeightSemidirectAction (phi : E →* MulAut H) :
    MulAction (H ⋊[phi] E)
      (ConjugacyClass (p := p) (K := K) (G := H)) := by
  letI : MulAction H (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightHAction
  letI : MulAction E (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightEAction phi
  exact semidirectMulAction phi
    (rightAutomorphismSemidirectCompatible
      (X := ConjugacyClass (p := p) (K := K) (G := H)) phi)

/-- The ambient conjugacy class of a raw character weight. -/
def rawWeightOrbit
    (r : RawWeightClass (p := p) (K := K) (H := H)) :
    ConjugacyClass (p := p) (K := K) (G := H) :=
  Quotient.mk'' r

/-- Passage from a raw representative to its ambient conjugacy class is
equivariant for the canonical semidirect actions. -/
theorem rawWeightOrbit_semidirect_smul
    (phi : E →* MulAut H) (g : H ⋊[phi] E)
    (r : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      canonicalRawSemidirectAction phi
    let _ : MulAction (H ⋊[phi] E)
        (ConjugacyClass (p := p) (K := K) (G := H)) :=
      canonicalWeightSemidirectAction phi
    rawWeightOrbit (g • r) = g • rawWeightOrbit r := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  letI : MulAction H (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightHAction
  letI : MulAction E (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightEAction phi
  letI : MulAction (H ⋊[phi] E)
      (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightSemidirectAction phi
  refine Quotient.inductionOn r ?_
  intro W
  rfl

/-- The radical subgroup of a raw character weight, embedded in the selected
semidirect product. -/
def rawAmbientRadical (phi : E →* MulAut H)
    (r : RawWeightClass (p := p) (K := K) (H := H)) :
    Subgroup (H ⋊[phi] E) :=
  (rawSubgroup r).map (SemidirectProduct.inl : H →* H ⋊[phi] E)

/-- The embedded radical transforms by conjugation under the same
semidirect element that acts on the raw character weight. -/
theorem rawAmbientRadical_conjugate
    (phi : E →* MulAut H) (g : H ⋊[phi] E)
    (r : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      canonicalRawSemidirectAction phi
    (rawAmbientRadical phi r).map (MulAut.conj g).toMonoidHom =
      rawAmbientRadical phi (g • r) := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  have hhom :
      (MulAut.conj g).toMonoidHom.comp
          (SemidirectProduct.inl : H →* H ⋊[phi] E) =
        (SemidirectProduct.inl : H →* H ⋊[phi] E).comp
          (semidirectToMulAut phi g).toMonoidHom := by
    apply MonoidHom.ext
    intro h
    exact conjugate_inl_eq_inl_semidirectToMulAut phi g h
  rw [rawAmbientRadical, rawAmbientRadical,
    rawSubgroup_semidirect]
  rw [Subgroup.map_map, Subgroup.map_map, hhom]

/-- The raw stabiliser is the intersection of the orbit stabiliser and the
normaliser of the embedded radical. -/
theorem rawWeight_stabilizer_eq_orbitStabilizer_inf_normalizer
    (phi : E →* MulAut H)
    (r : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      canonicalRawSemidirectAction phi
    let _ : MulAction (H ⋊[phi] E)
        (ConjugacyClass (p := p) (K := K) (G := H)) :=
      canonicalWeightSemidirectAction phi
    semidirectStabilizer (phi := phi) r =
      semidirectStabilizer (phi := phi) (rawWeightOrbit r) ⊓
        Subgroup.normalizer (rawAmbientRadical phi r : Set (H ⋊[phi] E)) := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  letI : MulAction H (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightHAction
  letI : MulAction E (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightEAction phi
  letI : MulAction (H ⋊[phi] E)
      (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightSemidirectAction phi
  ext g
  constructor
  · intro hg
    refine ⟨?_, ?_⟩
    · change g • rawWeightOrbit r = rawWeightOrbit r
      rw [← rawWeightOrbit_semidirect_smul, hg]
    · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      calc
        (rawAmbientRadical phi r).map (MulAut.conj g).toMonoidHom =
            rawAmbientRadical phi (g • r) :=
          rawAmbientRadical_conjugate phi g r
        _ = rawAmbientRadical phi r := congrArg (rawAmbientRadical phi) hg
  · rintro ⟨horbit, hnormal⟩
    change g • r = r
    apply isoClass_eq_of_conjugacyClass_eq_of_rawSubgroup_eq
    · change rawWeightOrbit (g • r) = rawWeightOrbit r
      exact (rawWeightOrbit_semidirect_smul phi g r).trans horbit
    · apply Subgroup.map_injective
        (f := (SemidirectProduct.inl : H →* H ⋊[phi] E))
        SemidirectProduct.inl_injective
      calc
        (rawSubgroup (g • r)).map
            (SemidirectProduct.inl : H →* H ⋊[phi] E) =
            rawAmbientRadical phi (g • r) := rfl
        _ = (rawAmbientRadical phi r).map
              (MulAut.conj g).toMonoidHom :=
          (rawAmbientRadical_conjugate phi g r).symm
        _ = rawAmbientRadical phi r :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormal
        _ = (rawSubgroup r).map
              (SemidirectProduct.inl : H →* H ⋊[phi] E) := rfl

/-! ## The local normaliser inside the orbit stabiliser -/

/-- An intersection with an ambient normaliser is canonically the normaliser
of the corresponding subgroup inside the first factor. -/
def infNormalizerEquivNormalizerSubgroupOf
    {G : Type u} [Group G] (A Q : Subgroup G) (hQ : Q ≤ A) :
    ↥(A ⊓ Subgroup.normalizer (Q : Set G)) ≃*
      Subgroup.normalizer (Q.subgroupOf A : Set A) :=
  (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
    (MulEquiv.subgroupCongr
      ((Subgroup.inf_subgroupOf_left (Subgroup.normalizer Q) A).trans
        (Subgroup.subgroupOf_normalizer_eq hQ)))

@[simp]
theorem infNormalizerEquivNormalizerSubgroupOf_apply_coe
    {G : Type u} [Group G] (A Q : Subgroup G) (hQ : Q ≤ A)
    (g : ↥(A ⊓ Subgroup.normalizer (Q : Set G))) :
    ((((infNormalizerEquivNormalizerSubgroupOf A Q hQ g :
        Subgroup.normalizer (Q.subgroupOf A : Set A)) : A) : G)) = g.1 :=
  rfl

/-- The embedded radical lies in the stabiliser of the ambient weight
class. -/
theorem rawAmbientRadical_le_orbitStabilizer
    (phi : E →* MulAut H)
    (r : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction (H ⋊[phi] E)
        (ConjugacyClass (p := p) (K := K) (G := H)) :=
      canonicalWeightSemidirectAction phi
    rawAmbientRadical phi r ≤
      semidirectStabilizer (phi := phi) (rawWeightOrbit r) := by
  dsimp only
  letI : MulAction H (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightHAction
  letI : MulAction E (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightEAction phi
  letI : MulAction (H ⋊[phi] E)
      (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightSemidirectAction phi
  intro g hg
  obtain ⟨h, _hh, rfl⟩ := hg
  change (SemidirectProduct.inl h : H ⋊[phi] E) • rawWeightOrbit r =
    rawWeightOrbit r
  rw [semidirect_inl_smul]
  exact inner_fixes_weightClass h (rawWeightOrbit r)

/-- The raw-pair stabiliser is canonically the normaliser of its radical
inside the stabiliser of its ambient weight class. -/
def rawWeightStabilizerEquivOrbitLocalNormalizer
    (phi : E →* MulAut H)
    (r : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      canonicalRawSemidirectAction phi
    let _ : MulAction (H ⋊[phi] E)
        (ConjugacyClass (p := p) (K := K) (G := H)) :=
      canonicalWeightSemidirectAction phi
    semidirectStabilizer (phi := phi) r ≃*
      Subgroup.normalizer
        ((rawAmbientRadical phi r).subgroupOf
          (semidirectStabilizer (phi := phi) (rawWeightOrbit r)) :
          Set (semidirectStabilizer (phi := phi) (rawWeightOrbit r))) := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  letI : MulAction H (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightHAction
  letI : MulAction E (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightEAction phi
  letI : MulAction (H ⋊[phi] E)
      (ConjugacyClass (p := p) (K := K) (G := H)) :=
    canonicalWeightSemidirectAction phi
  exact
    (MulEquiv.subgroupCongr
      (rawWeight_stabilizer_eq_orbitStabilizer_inf_normalizer phi r)).trans
    (infNormalizerEquivNormalizerSubgroupOf
      (semidirectStabilizer (phi := phi) (rawWeightOrbit r))
      (rawAmbientRadical phi r)
      (rawAmbientRadical_le_orbitStabilizer phi r))

@[simp]
theorem rawWeightStabilizerEquivOrbitLocalNormalizer_apply_coe
    (phi : E →* MulAut H)
    (r : RawWeightClass (p := p) (K := K) (H := H))
    (g :
      let _ : MulAction (H ⋊[phi] E)
          (RawWeightClass (p := p) (K := K) (H := H)) :=
        canonicalRawSemidirectAction phi
      semidirectStabilizer (phi := phi) r) :
    let _ : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      canonicalRawSemidirectAction phi
    let _ : MulAction (H ⋊[phi] E)
        (ConjugacyClass (p := p) (K := K) (G := H)) :=
      canonicalWeightSemidirectAction phi
    ((((rawWeightStabilizerEquivOrbitLocalNormalizer phi r g :
        Subgroup.normalizer
          ((rawAmbientRadical phi r).subgroupOf
            (semidirectStabilizer (phi := phi) (rawWeightOrbit r)) :
            Set (semidirectStabilizer (phi := phi) (rawWeightOrbit r)))) :
      semidirectStabilizer (phi := phi) (rawWeightOrbit r)) :
      H ⋊[phi] E)) = g.1 := by
  dsimp only
  simp [rawWeightStabilizerEquivOrbitLocalNormalizer]

end ModularRep.PaperProofs.CyclicOuterRawPairNormalizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
