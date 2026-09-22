import ModularRep.PaperProofs.CyclicOuterRawPairNormalizer
import ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient

/-!
# The selected Fischer local carrier

This module identifies the stabiliser of a selected raw character weight with
the local normaliser inside the selected Brauer stabiliser.  The construction
uses only equivariance of the global character weight bijection, orbit and
literal support uniqueness, and the centreless ambient group constructed
upstream.  It assumes no character extension, block induction relation, BAW
conclusion, or iBAW conclusion.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37Relative
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.CyclicOuterRawPairNormalizer
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

noncomputable local instance selectedOuterFinite
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Finite (SelectedOuterGroup S) :=
  Finite.of_injective
    (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _a _b h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

noncomputable local instance selectedOuterFintype
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Fintype (SelectedOuterGroup S) :=
  Fintype.ofFinite _

abbrev GlobalWeight (P : Definition35Problem.{u}) :=
  WeightClass (p := P.p) (K := P.K) (H := P.H)

abbrev SelectedPairStabilizer
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (w : Definition35Weight P) :=
  PairStabilizer (selectedOuterField S) P.blockSource P.block w

abbrev SelectedPairBase
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (w : Definition35Weight P) :=
  EmbeddedPairHStabilizer
    (selectedOuterField S) P.blockSource P.block w

abbrev SelectedSpathAmbient
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :=
  selectedOuterSpathAmbientCore P hcenter reference psi S haut

abbrev SelectedLocalGroup
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :=
  AmbientLocalGroup P reference psi w
    (SelectedCentralQuotient P hcenter reference psi)
    (SelectedSpathAmbient P hcenter reference psi S haut)

abbrev SelectedLocalBase
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :=
  AmbientLocalBase P reference psi w
    (SelectedCentralQuotient P hcenter reference psi)
    (SelectedSpathAmbient P hcenter reference psi S haut)

/-- A fully automorphism equivariant global character weight equivalence is
equivariant for the selected semidirect presentation. -/
theorem selectedOmega_semidirect_equivariant
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ WeightClass (p := P.p) (K := P.K) (H := P.H))
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi) :
    let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
      selectedBrauerSemidirectAction P.iota S
    let _ : MulAction (SelectedOuterAmbient S)
        (WeightClass (p := P.p) (K := P.K) (H := P.H)) :=
      canonicalWeightSemidirectAction (selectedOuterField S)
    ∀ g : SelectedOuterAmbient S, ∀ chi : IBr P.iota,
      Omega (g • chi) = g • Omega chi := by
  dsimp only
  letI : MulAction P.H (IBr P.iota) :=
    rightAutomorphismAction (X := IBr P.iota)
      (MulAut.conj : P.H →* MulAut P.H)
  letI : MulAction (SelectedOuterGroup S) (IBr P.iota) :=
    rightAutomorphismAction (X := IBr P.iota) (selectedOuterField S)
  letI : MulAction P.H
      (WeightClass (p := P.p) (K := P.K) (H := P.H)) :=
    canonicalWeightHAction
  letI : MulAction (SelectedOuterGroup S)
      (WeightClass (p := P.p) (K := P.K) (H := P.H)) :=
    canonicalWeightEAction (selectedOuterField S)
  let A := actualActionData P.iota (selectedOuterField S) Omega (by
    intro e chi
    exact hOmega (inverseOpHom (selectedOuterField S) e) chi)
  exact omega_semidirect_equivariant (selectedOuterField S) A

/-- The selected raw representative has the prescribed ambient weight
class. -/
@[simp]
theorem rawWeightOrbit_selectedRawWeight
    (P : Definition35Problem.{u}) (w : Definition35Weight P) :
    rawWeightOrbit (selectedRawWeight P.blockSource P.block w) = w.1 :=
  selectedCharacterWeight_spec (blockSource := P.blockSource)
    (block := P.block) w

/-- Equivariance and injectivity identify the selected weight stabiliser
with the selected Brauer stabiliser. -/
theorem selectedWeightStabilizer_eq_brauerStabilizer
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ WeightClass (p := P.p) (K := P.K) (H := P.H))
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (psi : Definition35Brauer P) :
    let _ : MulAction (SelectedOuterAmbient S)
        (WeightClass (p := P.p) (K := P.K) (H := P.H)) :=
      canonicalWeightSemidirectAction (selectedOuterField S)
    semidirectStabilizer (phi := selectedOuterField S) (Omega psi.1) =
      SelectedBrauerAmbient P.iota S psi.1 := by
  dsimp only
  letI : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  letI : MulAction (SelectedOuterAmbient S)
      (WeightClass (p := P.p) (K := P.K) (H := P.H)) :=
    canonicalWeightSemidirectAction (selectedOuterField S)
  ext g
  change (g • Omega psi.1 = Omega psi.1) ↔ (g • psi.1 = psi.1)
  rw [← selectedOmega_semidirect_equivariant P S Omega hOmega g psi.1]
  exact Omega.injective.eq_iff

/-- The raw pair stabiliser is the intersection of the matched Brauer
stabiliser with the ambient normaliser of its literal radical. -/
theorem selectedPairStabilizer_eq_brauer_inf_normalizer
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (hmatch : w.1 = Omega psi.1) :
    SelectedPairStabilizer P S w =
      SelectedBrauerAmbient P.iota S psi.1 ⊓
        Subgroup.normalizer
          (rawAmbientRadical (selectedOuterField S)
            (selectedRawWeight P.blockSource P.block w) :
              Set (SelectedOuterAmbient S)) := by
  let _ : MulAction (SelectedOuterAmbient S)
      (RawWeightClass (p := P.p) (K := P.K) (H := P.H)) :=
    canonicalRawSemidirectAction (selectedOuterField S)
  let _ : MulAction (SelectedOuterAmbient S) (GlobalWeight P) :=
    canonicalWeightSemidirectAction (selectedOuterField S)
  calc
    SelectedPairStabilizer P S w =
        semidirectStabilizer
            (phi := selectedOuterField S)
            (rawWeightOrbit
              (selectedRawWeight P.blockSource P.block w)) ⊓
          Subgroup.normalizer
            (rawAmbientRadical (selectedOuterField S)
              (selectedRawWeight P.blockSource P.block w) :
                Set (SelectedOuterAmbient S)) :=
      rawWeight_stabilizer_eq_orbitStabilizer_inf_normalizer
        (selectedOuterField S)
        (selectedRawWeight P.blockSource P.block w)
    _ = _ := by
      rw [rawWeightOrbit_selectedRawWeight, hmatch,
        selectedWeightStabilizer_eq_brauerStabilizer
          P S Omega hOmega psi]

/-- On elements of the original group, the quotient-to-ambient composite is
the canonical embedding into the normal factor. -/
@[simp]
theorem selectedQuotientToAmbient_mk_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (x : P.H) :
    ((quotientToAmbient P reference psi
        (SelectedCentralQuotient P hcenter reference psi)
        (SelectedSpathAmbient P hcenter reference psi S haut)
        (centralCharacterQuotientMap P reference x) :
      SelectedBrauerAmbient P.iota S psi.1) :
      SelectedOuterAmbient S) =
        SemidirectProduct.inl x := by
  change ((((selectedBaseEquiv P hcenter reference psi S
      (centralCharacterQuotientMap P reference x) :
        SelectedBrauerBase P.iota S psi.1) :
      SelectedBrauerAmbient P.iota S psi.1) :
      SelectedOuterAmbient S)) = _
  rw [selectedBaseEquiv_apply_coe,
    centerlessCentralCharacterQuotientEquiv_mk]

/-- The selected ambient radical is the same literal subgroup as the radical
embedded in the semidirect product. -/
theorem selectedAmbientRadical_map_subtype
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    (ambientRadical P reference psi w
        (SelectedCentralQuotient P hcenter reference psi)
        (SelectedSpathAmbient P hcenter reference psi S haut)).map
      (SelectedBrauerAmbient P.iota S psi.1).subtype =
    rawAmbientRadical (selectedOuterField S)
      (selectedRawWeight P.blockSource P.block w) := by
  simp only [ambientRadical, quotientRadical, rawAmbientRadical,
    Subgroup.map_map, rawSubgroup_selectedRawWeight]
  congr 1

/-- The embedded radical lies in the matched Brauer stabiliser. -/
theorem rawAmbientRadical_le_selectedBrauerAmbient
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (hmatch : w.1 = Omega psi.1) :
    rawAmbientRadical (selectedOuterField S)
        (selectedRawWeight P.blockSource P.block w) ≤
      SelectedBrauerAmbient P.iota S psi.1 := by
  let _ : MulAction (SelectedOuterAmbient S)
      (RawWeightClass (p := P.p) (K := P.K) (H := P.H)) :=
    canonicalRawSemidirectAction (selectedOuterField S)
  let _ : MulAction (SelectedOuterAmbient S) (GlobalWeight P) :=
    canonicalWeightSemidirectAction (selectedOuterField S)
  calc
    rawAmbientRadical (selectedOuterField S)
        (selectedRawWeight P.blockSource P.block w) ≤
      semidirectStabilizer
        (phi := selectedOuterField S)
        (rawWeightOrbit
          (selectedRawWeight P.blockSource P.block w)) :=
      rawAmbientRadical_le_orbitStabilizer
        (selectedOuterField S)
        (selectedRawWeight P.blockSource P.block w)
    _ = SelectedBrauerAmbient P.iota S psi.1 := by
      rw [rawWeightOrbit_selectedRawWeight, hmatch,
        selectedWeightStabilizer_eq_brauerStabilizer
          P S Omega hOmega psi]

/-- Inside the matched Brauer stabiliser, the ambient radical is the
subgroup obtained from the literal raw radical. -/
theorem selectedAmbientRadical_eq_raw_subgroupOf
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    ambientRadical P reference psi w
        (SelectedCentralQuotient P hcenter reference psi)
        (SelectedSpathAmbient P hcenter reference psi S haut) =
      (rawAmbientRadical (selectedOuterField S)
        (selectedRawWeight P.blockSource P.block w)).subgroupOf
          (SelectedBrauerAmbient P.iota S psi.1) := by
  apply Subgroup.map_injective
    (f := (SelectedBrauerAmbient P.iota S psi.1).subtype)
    (SelectedBrauerAmbient P.iota S psi.1).subtype_injective
  rw [selectedAmbientRadical_map_subtype]
  rw [Subgroup.map_subgroupOf_eq_of_le
    (rawAmbientRadical_le_selectedBrauerAmbient
      P S Omega hOmega psi w hmatch)]

/-- The selected raw-pair stabiliser is canonically the ambient local
normaliser required in the Spath extension condition. -/
def selectedPairStabilizerEquivAmbientLocalGroup
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    SelectedPairStabilizer P S w ≃*
      SelectedLocalGroup P hcenter reference psi w S haut := by
  let A := SelectedBrauerAmbient P.iota S psi.1
  let Q := rawAmbientRadical (selectedOuterField S)
    (selectedRawWeight P.blockSource P.block w)
  let hQ : Q ≤ A :=
    rawAmbientRadical_le_selectedBrauerAmbient
      P S Omega hOmega psi w hmatch
  let hrad :
      Q.subgroupOf A =
        ambientRadical P reference psi w
          (SelectedCentralQuotient P hcenter reference psi)
          (SelectedSpathAmbient P hcenter reference psi S haut) :=
    (selectedAmbientRadical_eq_raw_subgroupOf
      P hcenter reference psi w S Omega hOmega hmatch haut).symm
  exact
    ((MulEquiv.subgroupCongr
        (selectedPairStabilizer_eq_brauer_inf_normalizer
          P S Omega hOmega psi w hmatch)).trans
      (infNormalizerEquivNormalizerSubgroupOf A Q hQ)).trans
    (MulEquiv.subgroupCongr
      (congrArg
        (fun T : Subgroup A ↦ Subgroup.normalizer (T : Set A))
        hrad))

@[simp]
theorem selectedPairStabilizerEquivAmbientLocalGroup_apply_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (d : SelectedPairStabilizer P S w) :
    ((((selectedPairStabilizerEquivAmbientLocalGroup
          P hcenter reference psi w S Omega hOmega hmatch haut d :
        SelectedLocalGroup P hcenter reference psi w S haut) :
      SelectedBrauerAmbient P.iota S psi.1) :
      SelectedOuterAmbient S)) = d.1 := by
  simp [selectedPairStabilizerEquivAmbientLocalGroup,
    infNormalizerEquivNormalizerSubgroupOf]

@[simp]
theorem selectedPairStabilizerEquivAmbientLocalGroup_symm_apply_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (a : SelectedLocalGroup P hcenter reference psi w S haut) :
    ((selectedPairStabilizerEquivAmbientLocalGroup
        P hcenter reference psi w S Omega hOmega hmatch haut).symm a :
      SelectedOuterAmbient S) =
    (((a : SelectedBrauerAmbient P.iota S psi.1) :
      SelectedOuterAmbient S)) := by
  simpa only [
    (selectedPairStabilizerEquivAmbientLocalGroup
      P hcenter reference psi w S Omega hOmega hmatch haut).apply_symm_apply]
    using
      (selectedPairStabilizerEquivAmbientLocalGroup_apply_coe
        P hcenter reference psi w S Omega hOmega hmatch haut
        ((selectedPairStabilizerEquivAmbientLocalGroup
          P hcenter reference psi w S Omega hOmega hmatch haut).symm a)).symm

/-- The local-group equivalence commutes with the inclusions into the
selected outer semidirect product. -/
theorem selectedPairStabilizerEquivAmbientLocalGroup_subtype_square
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    ((SelectedBrauerAmbient P.iota S psi.1).subtype.comp
      (SelectedLocalGroup P hcenter reference psi w S haut).subtype).comp
        (selectedPairStabilizerEquivAmbientLocalGroup
          P hcenter reference psi w S Omega hOmega hmatch haut).toMonoidHom =
      (SelectedPairStabilizer P S w).subtype := by
  apply MonoidHom.ext
  intro d
  exact selectedPairStabilizerEquivAmbientLocalGroup_apply_coe
    P hcenter reference psi w S Omega hOmega hmatch haut d

@[simp]
theorem mem_selectedPairBase_iff_right_eq_one
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (w : Definition35Weight P)
    (d : SelectedPairStabilizer P S w) :
    d ∈ SelectedPairBase P S w ↔ d.1.right = 1 := by
  let _ : MulAction (SelectedOuterAmbient S)
      (RawWeightClass (p := P.p) (K := P.K) (H := P.H)) :=
    canonicalRawSemidirectAction (selectedOuterField S)
  change d ∈ embeddedHStabilizer
      (phi := selectedOuterField S)
      (selectedRawWeight P.blockSource P.block w) ↔ _
  rw [embeddedHStabilizer_eq_ker]
  rfl

@[simp]
theorem mem_selectedBrauerBase_iff_right_eq_one
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (psi : Definition35Brauer P)
    (a : SelectedBrauerAmbient P.iota S psi.1) :
    a ∈ SelectedBrauerBase P.iota S psi.1 ↔ a.1.right = 1 := by
  let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  change a ∈ embeddedHStabilizer
      (phi := selectedOuterField S) psi.1 ↔ _
  rw [embeddedHStabilizer_eq_ker]
  rfl

/-- Restricting the local-group equivalence to the right-coordinate kernels
identifies the embedded pair stabiliser with the ambient local base. -/
def selectedPairBaseEquivAmbientLocalBase
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    SelectedPairBase P S w ≃*
      SelectedLocalBase P hcenter reference psi w S haut := by
  let e := selectedPairStabilizerEquivAmbientLocalGroup
    P hcenter reference psi w S Omega hOmega hmatch haut
  refine
    { toFun := fun h ↦ ⟨e h.1, ?_⟩
      invFun := fun a ↦ ⟨e.symm a.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · change (e h.1).1 ∈ SelectedBrauerBase P.iota S psi.1
    rw [mem_selectedBrauerBase_iff_right_eq_one]
    have hh :=
      (mem_selectedPairBase_iff_right_eq_one P S w h.1).mp h.2
    have he := congrArg
      (fun g : SelectedOuterAmbient S ↦ g.right)
      (selectedPairStabilizerEquivAmbientLocalGroup_apply_coe
        P hcenter reference psi w S Omega hOmega hmatch haut h.1)
    exact he.trans hh
  · change e.symm a.1 ∈ SelectedPairBase P S w
    rw [mem_selectedPairBase_iff_right_eq_one]
    have ha :=
      (mem_selectedBrauerBase_iff_right_eq_one P S psi a.1).mp a.2
    have he := congrArg
      (fun g : SelectedOuterAmbient S ↦ g.right)
      (selectedPairStabilizerEquivAmbientLocalGroup_symm_apply_coe
        P hcenter reference psi w S Omega hOmega hmatch haut a.1)
    exact he.trans ha
  · intro h
    apply Subtype.ext
    exact e.symm_apply_apply h.1
  · intro a
    apply Subtype.ext
    exact e.apply_symm_apply a.1
  · intro h₁ h₂
    apply Subtype.ext
    exact e.map_mul h₁.1 h₂.1

@[simp]
theorem selectedPairBaseEquivAmbientLocalBase_apply_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (h : SelectedPairBase P S w) :
    ((selectedPairBaseEquivAmbientLocalBase
        P hcenter reference psi w S Omega hOmega hmatch haut h :
      SelectedLocalBase P hcenter reference psi w S haut) :
      SelectedLocalGroup P hcenter reference psi w S haut) =
    selectedPairStabilizerEquivAmbientLocalGroup
      P hcenter reference psi w S Omega hOmega hmatch haut
      (h : SelectedPairStabilizer P S w) :=
  rfl

@[simp]
theorem selectedPairBaseEquivAmbientLocalBase_apply_outer_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (h : SelectedPairBase P S w) :
    (((((selectedPairBaseEquivAmbientLocalBase
          P hcenter reference psi w S Omega hOmega hmatch haut h :
        SelectedLocalBase P hcenter reference psi w S haut) :
      SelectedLocalGroup P hcenter reference psi w S haut) :
      SelectedBrauerAmbient P.iota S psi.1) :
      SelectedOuterAmbient S)) =
    (((h : SelectedPairStabilizer P S w) :
      SelectedOuterAmbient S)) := by
  exact selectedPairStabilizerEquivAmbientLocalGroup_apply_coe
    P hcenter reference psi w S Omega hOmega hmatch haut h.1

@[simp]
theorem selectedPairBaseEquivAmbientLocalBase_symm_apply_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (a : SelectedLocalBase P hcenter reference psi w S haut) :
    (((selectedPairBaseEquivAmbientLocalBase
        P hcenter reference psi w S Omega hOmega hmatch haut).symm a :
      SelectedPairBase P S w) : SelectedPairStabilizer P S w) =
    (selectedPairStabilizerEquivAmbientLocalGroup
      P hcenter reference psi w S Omega hOmega hmatch haut).symm
        (a : SelectedLocalGroup P hcenter reference psi w S haut) :=
  rfl

@[simp]
theorem selectedPairBaseEquivAmbientLocalBase_symm_apply_outer_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (a : SelectedLocalBase P hcenter reference psi w S haut) :
    (((((selectedPairBaseEquivAmbientLocalBase
          P hcenter reference psi w S Omega hOmega hmatch haut).symm a :
        SelectedPairBase P S w) : SelectedPairStabilizer P S w) :
      SelectedOuterAmbient S)) =
    ((((a : SelectedLocalGroup P hcenter reference psi w S haut) :
      SelectedBrauerAmbient P.iota S psi.1) :
      SelectedOuterAmbient S)) := by
  exact selectedPairStabilizerEquivAmbientLocalGroup_symm_apply_coe
    P hcenter reference psi w S Omega hOmega hmatch haut a.1

/-- The pair/base equivalence and the pair/local equivalence commute with
the subgroup inclusions. -/
theorem selectedPairBaseEquivAmbientLocalBase_square
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    (selectedPairStabilizerEquivAmbientLocalGroup
      P hcenter reference psi w S Omega hOmega hmatch haut).toMonoidHom.comp
        (SelectedPairBase P S w).subtype =
      (SelectedLocalBase P hcenter reference psi w S haut).subtype.comp
        (selectedPairBaseEquivAmbientLocalBase
          P hcenter reference psi w S Omega hOmega hmatch haut).toMonoidHom := by
  apply MonoidHom.ext
  intro h
  rfl

/-- The inverse equivalences also commute with the subgroup inclusions. -/
theorem selectedPairBaseEquivAmbientLocalBase_symm_square
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    (selectedPairStabilizerEquivAmbientLocalGroup
      P hcenter reference psi w S Omega hOmega hmatch haut).symm.toMonoidHom.comp
        (SelectedLocalBase P hcenter reference psi w S haut).subtype =
      (SelectedPairBase P S w).subtype.comp
        (selectedPairBaseEquivAmbientLocalBase
          P hcenter reference psi w S Omega hOmega hmatch haut).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro a
  rfl

end ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
