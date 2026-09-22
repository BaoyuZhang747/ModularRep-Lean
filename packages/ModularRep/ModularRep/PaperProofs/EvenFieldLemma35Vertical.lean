import ModularRep.PaperProofs.EvenFieldLemma35
import ModularRep.PaperProofs.EvenFieldWeightPair

/-!
# A vertical, class-level formalisation of manuscript Lemma 3.6

This module replaces the arbitrary whole-weight relation in the first proof
schema by an actual pair `(torus, local character)`.  A rational-Levi witness
determines the inner-twist element in the finite fixed-point group.  The torus
and local-character components are then fixed by separate deductions before
the induced action on `H`-orbit classes is considered.

Deep cited results still enter through the source contracts.  In particular,
the types of characters, Lusztig series, generic pairs, and the concrete
Clifford and Gallagher correspondences have not yet been constructed from a
general character theory library.  The public conclusion, however, is now
the exact class-level form of the manuscript lemma rather than a statement
about an arbitrary representative.
-/

namespace ModularRep.PaperProofs.EvenFieldLemma35Vertical

open ModularRep.ManuscriptVerification.EvenFieldFixed
open ModularRep.PaperProofs.EvenFieldSourceShaped
open ModularRep.PaperProofs.EvenFieldLemma35
open ModularRep.PaperProofs.EvenFieldWeightPair

universe u

variable {G Torus LocalCharacter : Type u}
    [Group G] [MulAction G Torus] [MulAction G LocalCharacter]

/-- The rational-Levi and Lang data used to construct the exact inner twist
for one field automorphism.  The resulting element of the fixed-point group
is defined from these fields; it is not chosen independently. -/
structure RationalLeviWitness
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x)) where
  langWitness : G
  rationalLeviRepresentative : G
  langEquation :
    langWitness⁻¹ * F langWitness = rationalLeviRepresentative
  rationalLeviRepresentative_fixed :
    sigma rationalLeviRepresentative = rationalLeviRepresentative

/-- The element `g sigma(g)^{-1}` as an element of `G^F`. -/
def RationalLeviWitness.innerTwist
    {F sigma : G →* G}
    {commute : ∀ x : G, F (sigma x) = sigma (F x)}
    (W : RationalLeviWitness F sigma commute) :
    frobeniusFixedSubgroup F :=
  ⟨innerTwistElement sigma W.langWitness,
    innerTwistElement_mem_frobeniusFixedSubgroup F sigma W.langWitness
      W.rationalLeviRepresentative commute W.langEquation
      W.rationalLeviRepresentative_fixed⟩

@[simp]
theorem RationalLeviWitness.innerTwist_val
    {F sigma : G →* G}
    {commute : ∀ x : G, F (sigma x) = sigma (F x)}
    (W : RationalLeviWitness F sigma commute) :
    (W.innerTwist : G) = innerTwistElement sigma W.langWitness :=
  rfl

/-- Source data for one genuine generic pair.  The `pairData` field is forced
to use the inner twist constructed from `witness`. -/
structure LocalSource
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (sigmaTorus : Torus → Torus)
    (sigmaLocal : LocalCharacter → LocalCharacter)
    (pair : Torus × LocalCharacter) where
  witness : RationalLeviWitness F sigma commute
  Levi : Type u
  pairData :
    let H := frobeniusFixedSubgroup F
    let _ : MulAction H Torus := MulAction.compHom Torus H.subtype
    let _ : MulAction H LocalCharacter :=
      MulAction.compHom LocalCharacter H.subtype
    EvenFieldWeightPair.Data H Torus LocalCharacter Levi
      sigmaTorus sigmaLocal pair.1 pair.2 witness.innerTwist

/-- One source-instantiated generic pair has a fixed orbit under the field
automorphism. -/
theorem localPair_orbit_fixed
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (sigmaTorus : Torus → Torus)
    (sigmaLocal : LocalCharacter → LocalCharacter)
    (pair : Torus × LocalCharacter)
    (D : LocalSource F sigma commute sigmaTorus sigmaLocal pair) :
    let H := frobeniusFixedSubgroup F
    let _ : MulAction H Torus := MulAction.compHom Torus H.subtype
    let _ : MulAction H LocalCharacter :=
      MulAction.compHom LocalCharacter H.subtype
    MulAction.orbit H (sigmaTorus pair.1, sigmaLocal pair.2) =
      MulAction.orbit H pair := by
  dsimp only
  exact genericWeightPair_orbit_fixed D.pairData

/-- The componentwise field transformation of a generic pair. -/
def pairMap (sigmaTorus : Torus → Torus)
    (sigmaLocal : LocalCharacter → LocalCharacter) :
    Torus × LocalCharacter → Torus × LocalCharacter :=
  fun pair ↦ (sigmaTorus pair.1, sigmaLocal pair.2)

/-- Componentwise compatibility gives compatibility of the induced map on
pairs. -/
theorem pairMap_compatible
    {H : Type u} [Group H] [MulAction H Torus]
    [MulAction H LocalCharacter]
    (groupMap : H →* H)
    (sigmaTorus : Torus → Torus)
    (sigmaLocal : LocalCharacter → LocalCharacter)
    (torusCompatible : ∀ h T,
      sigmaTorus (h • T) = groupMap h • sigmaTorus T)
    (localCompatible : ∀ h eta,
      sigmaLocal (h • eta) = groupMap h • sigmaLocal eta)
    (h : H) (pair : Torus × LocalCharacter) :
    pairMap sigmaTorus sigmaLocal (h • pair) =
      groupMap h • pairMap sigmaTorus sigmaLocal pair := by
  apply Prod.ext
  · exact torusCompatible h pair.1
  · exact localCompatible h pair.2

/-- The generic-weight half of Lemma 3.6 at the level of the actual quotient
set of `H`-classes of pairs. -/
theorem genericPairClasses_fixed
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (sigmaTorus : Torus → Torus)
    (sigmaLocal : LocalCharacter → LocalCharacter)
    (torusCompatible :
      let H := frobeniusFixedSubgroup F
      let _ : MulAction H Torus := MulAction.compHom Torus H.subtype
      ∀ h : H, ∀ T : Torus,
        sigmaTorus (h • T) =
          frobeniusFixedSubgroupHom F sigma commute h • sigmaTorus T)
    (localCompatible :
      let H := frobeniusFixedSubgroup F
      let _ : MulAction H LocalCharacter :=
        MulAction.compHom LocalCharacter H.subtype
      ∀ h : H, ∀ eta : LocalCharacter,
        sigmaLocal (h • eta) =
          frobeniusFixedSubgroupHom F sigma commute h • sigmaLocal eta)
    (Generic : Torus × LocalCharacter → Prop)
    (source : ∀ pair, Generic pair →
      LocalSource F sigma commute sigmaTorus sigmaLocal pair) :
    let H := frobeniusFixedSubgroup F
    let _ : MulAction H Torus := MulAction.compHom Torus H.subtype
    let _ : MulAction H LocalCharacter :=
      MulAction.compHom LocalCharacter H.subtype
    ∀ omega, omega ∈ orbitClassesOf Generic →
      inducedOrbitMap (frobeniusFixedSubgroupHom F sigma commute)
          (pairMap sigmaTorus sigmaLocal)
          (pairMap_compatible (frobeniusFixedSubgroupHom F sigma commute)
            sigmaTorus sigmaLocal torusCompatible localCompatible) omega =
        omega := by
  dsimp only
  intro omega
  rintro ⟨pair, hpair, rfl⟩
  change
    (Quotient.mk'' (pairMap sigmaTorus sigmaLocal pair) :
      WeightOrbit (frobeniusFixedSubgroup F)
        (Torus × LocalCharacter)) = Quotient.mk'' pair
  apply Quotient.sound
  change MulAction.orbitRel (frobeniusFixedSubgroup F)
    (Torus × LocalCharacter) (pairMap sigmaTorus sigmaLocal pair) pair
  rw [MulAction.orbitRel_apply, ← MulAction.orbit_eq_iff]
  exact localPair_orbit_fixed F sigma commute sigmaTorus sigmaLocal pair
    (source pair hpair)

section FullLemma

variable {FieldGroup DualLabel Character : Type u}
    [Group FieldGroup] [Group DualLabel]
    [MulAction FieldGroup Character]
    [MulAction FieldGroup Torus]
    [MulAction FieldGroup LocalCharacter]

/-- Exact class-level conclusion of Lemma 3.6 relative to the enumerated
published inputs.  `FieldGroup` is intended to be the opposite of
`E_H = <F_2>` so that its left actions encode the manuscript's right-action
convention. -/
theorem lemma_3_5
    (ell : ℕ) (Series : Character → DualLabel → Prop)
    (XC : Set Character)
    (F : G →* G)
    (sigmaG : FieldGroup → G →* G)
    (Generic : Torus × LocalCharacter → Prop)
    (commute : ∀ a x, F (sigmaG a x) = sigmaG a (F x))
    (torusCompatible : ∀ a,
      let H := frobeniusFixedSubgroup F
      let _ : MulAction H Torus := MulAction.compHom Torus H.subtype
      ∀ h : H, ∀ T : Torus,
        a • (h • T) =
          frobeniusFixedSubgroupHom F (sigmaG a) (commute a) h • (a • T))
    (localCompatible : ∀ a,
      let H := frobeniusFixedSubgroup F
      let _ : MulAction H LocalCharacter :=
        MulAction.compHom LocalCharacter H.subtype
      ∀ h : H, ∀ eta : LocalCharacter,
        a • (h • eta) =
          frobeniusFixedSubgroupHom F (sigmaG a) (commute a) h •
            (a • eta))
    (ordinarySource : ∀ a : FieldGroup,
      OrdinaryData ell Series (fun chi : Character ↦ a • chi) XC)
    (localSource : ∀ a : FieldGroup, ∀ pair, Generic pair →
      LocalSource F (sigmaG a) (commute a)
        (fun T : Torus ↦ a • T)
        (fun eta : LocalCharacter ↦ a • eta) pair) :
    (∀ a : FieldGroup, ∀ chi : Character, chi ∈ XC → a • chi = chi) ∧
      (let H := frobeniusFixedSubgroup F
       let _ : MulAction H Torus := MulAction.compHom Torus H.subtype
       let _ : MulAction H LocalCharacter :=
         MulAction.compHom LocalCharacter H.subtype
       ∀ a : FieldGroup, ∀ omega, omega ∈ orbitClassesOf Generic →
         inducedOrbitMap
             (frobeniusFixedSubgroupHom F (sigmaG a) (commute a))
             (pairMap (fun T : Torus ↦ a • T)
               (fun eta : LocalCharacter ↦ a • eta))
             (pairMap_compatible
               (frobeniusFixedSubgroupHom F (sigmaG a) (commute a))
               (fun T : Torus ↦ a • T)
               (fun eta : LocalCharacter ↦ a • eta)
               (torusCompatible a) (localCompatible a)) omega = omega) := by
  constructor
  · intro a chi hchi
    exact ordinary_characters_fixed ell Series (fun chi : Character ↦ a • chi) XC
      (ordinarySource a) chi hchi
  · dsimp only
    intro a
    exact genericPairClasses_fixed F (sigmaG a) (commute a)
      (fun T : Torus ↦ a • T)
      (fun eta : LocalCharacter ↦ a • eta)
      (torusCompatible a) (localCompatible a)
      Generic (localSource a)

end FullLemma

end ModularRep.PaperProofs.EvenFieldLemma35Vertical


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
