import ModularRep.OrbitFibreEquiv
import ModularRep.CharacterWeightBlockAssignment
import ModularRep.CharacterWeightRadicalProjection
import ModularRep.PaperProofs.CyclicOuterLemma37Concrete

/-!
# Representative local characters and global weight fibres

This module identifies the representative-level defect-zero character set at
a fixed radical subgroup with the corresponding block and radical fibre of
global character-weight conjugacy classes.  The orbit-fibre passage is proved
in the kernel.  Its only representation theoretic source is the existing
local block-induction interface, which supplies the block attached to a
character weight.

No character-weight bijection, compatible extension, intermediate block
equality, BAW-goodness, or iBAW conclusion is assumed or proved here.
-/

noncomputable section

namespace ModularRep.CharacterWeight

open ModularRep.OrbitFibre
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete

universe u

variable {p : Nat} {k K G Block : Type u}
variable [Field k] [Field K] [CharZero K]
variable [Group G] [Fintype G]
variable [MulAction (MulAut G)ᵐᵒᵖ Block]

/-- Defect-zero ordinary characters of the local normaliser quotient at a
fixed radical subgroup. -/
abbrev LocalDefectZeroCharacter
    (Q : RadicalSubgroup (p := p) (G := G)) :=
  {theta : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q.1) //
    IsDefectZeroOrdinaryCharacter p theta}

/-- The character weight carried by a fixed radical subgroup and a local
defect-zero character. -/
def characterWeightAt
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G))
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    CharacterWeight p K G where
  prime := hp
  subgroup := Q.1
  radical := Q.2
  localCharacter := theta.1
  defectZero := theta.2

@[simp]
theorem characterWeightAt_subgroup
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G))
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    (characterWeightAt hp Q theta).subgroup = Q.1 :=
  rfl

@[simp]
theorem characterWeightAt_localCharacter
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G))
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    (characterWeightAt hp Q theta).localCharacter = theta.1 :=
  rfl

theorem isDefectZero_castLocalCharacter
    {Q R : Subgroup G} (h : Q = R)
    {theta : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)}
    (htheta : IsDefectZeroOrdinaryCharacter p theta) :
    IsDefectZeroOrdinaryCharacter p (castLocalCharacter h theta) := by
  subst R
  exact htheta

/-- The radical projection on weight isomorphism classes has no residual
stabiliser ambiguity: an element normalising the radical fixes the full
isomorphism class. -/
def radicalOrbitData :
    OrbitFibre.Data
      (G := G)
      (W := IsoClass (p := p) (K := K) (G := G))
      (S := RadicalSubgroup (p := p) (G := G)) where
  support := radicalSubgroupOfIsoClass
  support_smul := radicalSubgroupOfIsoClass_conjugation
  support_stabilizer_fixes := by
    intro g w hw
    have hnormal :
        g ∈ Subgroup.normalizer
          ((radicalSubgroupOfIsoClass w).1 : Set G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      have hval := congrArg Subtype.val hw
      change
        (radicalSubgroupOfIsoClass w).1.comap
            (MulAut.conj g⁻¹).toMonoidHom =
          (radicalSubgroupOfIsoClass w).1 at hval
      have hconj : (MulAut.conj g).symm = MulAut.conj g⁻¹ := by
        ext x
        simp [mul_assoc]
      calc
        (radicalSubgroupOfIsoClass w).1.map
            (MulAut.conj g).toMonoidHom =
            (radicalSubgroupOfIsoClass w).1.comap
              (MulAut.conj g).symm.toMonoidHom :=
          Subgroup.map_equiv_eq_comap_symm
            (MulAut.conj g) (radicalSubgroupOfIsoClass w).1
        _ = (radicalSubgroupOfIsoClass w).1.comap
              (MulAut.conj g⁻¹).toMonoidHom := by rw [hconj]
        _ = (radicalSubgroupOfIsoClass w).1 := hval
    change
      let _ : MulAction G (RawWeightClass (p := p) (K := K) (H := G)) :=
        rightAutomorphismAction
          (X := RawWeightClass (p := p) (K := K) (H := G))
          (MulAut.conj : G →* MulAut G)
      g • w = w
    apply normalizer_fixes_rawWeight
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := G))
        g w
    have hraw : rawSubgroup w = (radicalSubgroupOfIsoClass w).1 := by
      refine Quotient.inductionOn w ?_
      intro W
      rfl
    simpa only [hraw] using hnormal

@[simp]
theorem radicalOrbitData_orbitMap
    (w : ConjugacyClass (p := p) (K := K) (G := G)) :
    radicalOrbitData.orbitMap w = radicalClass w := by
  refine Quotient.inductionOn w ?_
  intro W
  rfl

/-- Insert a representative-level local character into the fixed radical
fibre before taking ambient conjugacy classes. -/
def localToFixedIsoClass
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G)) :
    LocalDefectZeroCharacter (K := K) Q →
      (radicalOrbitData (p := p) (K := K) (G := G)).FixedFibre Q :=
  fun theta ↦
    ⟨Quotient.mk'' (characterWeightAt hp Q theta), rfl⟩

theorem localToFixedIsoClass_injective
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G)) :
    Function.Injective (localToFixedIsoClass (K := K) hp Q) := by
  intro theta eta h
  have hquot :
      (Quotient.mk'' (characterWeightAt hp Q theta) :
          IsoClass (p := p) (K := K) (G := G)) =
        Quotient.mk'' (characterWeightAt hp Q eta) :=
    congrArg Subtype.val h
  have hiso : Isomorphic (characterWeightAt hp Q theta)
      (characterWeightAt hp Q eta) := Quotient.exact hquot
  rcases hiso with ⟨hQ, htheta⟩
  apply Subtype.ext
  rw [Subsingleton.elim hQ rfl] at htheta
  change castLocalCharacter (rfl : Q.1 = Q.1) theta.1 = eta.1 at htheta
  simpa only [castLocalCharacter_rfl] using htheta

theorem localToFixedIsoClass_surjective
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G)) :
    Function.Surjective (localToFixedIsoClass (K := K) hp Q) := by
  intro w
  let W : CharacterWeight p K G := w.1.out
  have hout :
      (Quotient.mk'' W : IsoClass (p := p) (K := K) (G := G)) = w.1 :=
    Quotient.out_eq w.1
  have hQsubtype :
      (⟨W.subgroup, W.radical⟩ : RadicalSubgroup (p := p) (G := G)) = Q := by
    calc
      (⟨W.subgroup, W.radical⟩ : RadicalSubgroup (p := p) (G := G)) =
          radicalSubgroupOfIsoClass (Quotient.mk'' W) := rfl
      _ = radicalSubgroupOfIsoClass w.1 :=
        congrArg radicalSubgroupOfIsoClass hout
      _ = Q := w.2
  have hQ : W.subgroup = Q.1 := congrArg Subtype.val hQsubtype
  let theta : LocalDefectZeroCharacter (K := K) Q :=
    ⟨castLocalCharacter hQ W.localCharacter,
      isDefectZero_castLocalCharacter hQ W.defectZero⟩
  refine ⟨theta, ?_⟩
  apply Subtype.ext
  change
    (Quotient.mk'' (characterWeightAt hp Q theta) :
        IsoClass (p := p) (K := K) (G := G)) = w.1
  calc
    (Quotient.mk'' (characterWeightAt hp Q theta) :
        IsoClass (p := p) (K := K) (G := G)) = Quotient.mk'' W := by
      apply Quotient.sound
      exact ⟨hQ.symm, castLocalCharacter_symm hQ W.localCharacter⟩
    _ = w.1 := hout

/-- Representative-level local defect-zero characters are precisely the
weight-isomorphism classes whose radical subgroup is the chosen
representative. -/
def localDefectZeroEquivFixedIsoClass
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G)) :
    LocalDefectZeroCharacter (K := K) Q ≃
      (radicalOrbitData (p := p) (K := K) (G := G)).FixedFibre Q :=
  Equiv.ofBijective (localToFixedIsoClass (K := K) hp Q)
    ⟨localToFixedIsoClass_injective (K := K) hp Q,
      localToFixedIsoClass_surjective (K := K) hp Q⟩

abbrev WeightRadicalFibre
    (Q : RadicalSubgroup (p := p) (G := G)) :=
  {w : ConjugacyClass (p := p) (K := K) (G := G) //
    radicalClass w =
      (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G))}

def orbitMapFibreEquivWeightRadicalFibre
    (Q : RadicalSubgroup (p := p) (G := G)) :
    (radicalOrbitData (p := p) (K := K) (G := G)).OrbitMapFibre Q ≃
      WeightRadicalFibre (K := K) Q where
  toFun w := ⟨w.1, by
    rw [← radicalOrbitData_orbitMap]
    exact w.2⟩
  invFun w := ⟨w.1, by
    rw [radicalOrbitData_orbitMap]
    exact w.2⟩
  left_inv w := rfl
  right_inv w := rfl

/-- Representative local defect-zero characters at `Q` are equivalent to
global character-weight classes whose radical class is represented by `Q`. -/
def localDefectZeroEquivWeightRadicalFibre
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G)) :
    LocalDefectZeroCharacter (K := K) Q ≃ WeightRadicalFibre (K := K) Q :=
  (localDefectZeroEquivFixedIsoClass (K := K) hp Q).trans
    ((radicalOrbitData.fixedEquivOrbitFibre Q).trans
      (orbitMapFibreEquivWeightRadicalFibre (K := K) Q))

@[simp]
theorem localDefectZeroEquivWeightRadicalFibre_apply_val
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G))
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    (localDefectZeroEquivWeightRadicalFibre (K := K) hp Q theta).1 =
      (Quotient.mk'' (Quotient.mk'' (characterWeightAt hp Q theta)) :
        ConjugacyClass (p := p) (K := K) (G := G)) := by
  change
    ((radicalOrbitData (p := p) (K := K) (G := G)).fixedEquivOrbitFibre Q
      (localDefectZeroEquivFixedIsoClass (K := K) hp Q theta)).1 = _
  rw [OrbitFibre.Data.fixedEquivOrbitFibre_apply_val]
  rfl

/-- Representative local defect-zero characters that induce to a fixed
ambient block. -/
abbrev RepresentativeDZ
    (hp : p.Prime)
    (S : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G)) (b : Block) :=
  {theta : LocalDefectZeroCharacter (K := K) Q //
    S.operations.rawWeightBlock (characterWeightAt hp Q theta) = b}

/-- Global weight classes lying simultaneously in a chosen ambient block and
over a chosen radical representative. -/
abbrev WeightBlockRadicalFibre
    (S : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G)) (b : Block) :=
  {w : ConjugacyClass (p := p) (K := K) (G := G) //
    S.weightBlock w = b ∧
      radicalClass w =
        (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G))}

/-- The representative local `dz` set is the simultaneous block/radical
fibre of the global set of weights. -/
def representativeDZEquivWeightBlockRadicalFibre
    (hp : p.Prime)
    (S : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G)) (b : Block) :
    RepresentativeDZ hp S Q b ≃ WeightBlockRadicalFibre S Q b where
  toFun theta :=
    let w := localDefectZeroEquivWeightRadicalFibre (K := K) hp Q theta.1
    ⟨w.1, by
      constructor
      · rw [localDefectZeroEquivWeightRadicalFibre_apply_val]
        exact theta.2
      · exact w.2⟩
  invFun w := by
    let thetaLocal : LocalDefectZeroCharacter (K := K) Q :=
      (localDefectZeroEquivWeightRadicalFibre (K := K) hp Q).symm
        ⟨w.1, w.2.2⟩
    refine ⟨thetaLocal, ?_⟩
    have hclass := congrArg Subtype.val
      ((localDefectZeroEquivWeightRadicalFibre (K := K) hp Q).apply_symm_apply
        ⟨w.1, w.2.2⟩)
    change S.operations.rawWeightBlock (characterWeightAt hp Q thetaLocal) = b
    calc
      S.operations.rawWeightBlock (characterWeightAt hp Q thetaLocal) =
          S.weightBlock
            ((localDefectZeroEquivWeightRadicalFibre
              (K := K) hp Q thetaLocal).1) := by
        rw [localDefectZeroEquivWeightRadicalFibre_apply_val]
        rfl
      _ = S.weightBlock w.1 := congrArg S.weightBlock hclass
      _ = b := w.2.1
  left_inv theta := by
    apply Subtype.ext
    exact (localDefectZeroEquivWeightRadicalFibre (K := K) hp Q).symm_apply_apply
      theta.1
  right_inv w := by
    apply Subtype.ext
    change
      ((localDefectZeroEquivWeightRadicalFibre (K := K) hp Q)
        ((localDefectZeroEquivWeightRadicalFibre (K := K) hp Q).symm
          ⟨w.1, w.2.2⟩)).1 = w.1
    exact congrArg Subtype.val
      ((localDefectZeroEquivWeightRadicalFibre (K := K) hp Q).apply_symm_apply
        ⟨w.1, w.2.2⟩)

end ModularRep.CharacterWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
