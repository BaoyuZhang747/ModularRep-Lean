import ModularRep.IrreducibleBrauerCharacterEquiv
import ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
import ModularRep.PaperProofs.SporadicFi24SelectedOuterC2

/-!
# The selected Fischer ambient stabiliser

This module constructs the ambient stabiliser used in the positive radical
branch for the centreless Fischer cover.  The construction transports the
selected semidirect presentation through the canonical central quotient.
All stabiliser, centre, and conjugation statements in this module are group
theoretic consequences of the displayed hypotheses.

No character extension, block induction relation, BAW conclusion, or iBAW
conclusion is assumed here.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient

open Formalisation
open ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

noncomputable local instance mulAutFinite
    {X : Type u} [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun alpha : MulAut X ↦ (alpha : X → X))
    DFunLike.coe_injective

noncomputable local instance selectedOuterFinite
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Finite (SelectedOuterGroup S) :=
  Finite.of_injective
    (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _a _b h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

noncomputable local instance selectedAmbientFinite
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Finite (SelectedOuterAmbient S) :=
  Finite.of_injective
    (fun g : SelectedOuterAmbient S ↦ (g.left, g.right)) (by
      intro a b hab
      exact SemidirectProduct.ext
        (congrArg Prod.fst hab) (congrArg Prod.snd hab))

/-- The canonical right action of the selected semidirect product on
function valued irreducible Brauer characters. -/
@[instance_reducible]
def selectedBrauerSemidirectAction
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    MulAction (SelectedOuterAmbient S) (IBr iota) := by
  letI : MulAction X (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : X →* MulAut X)
  letI : MulAction (SelectedOuterGroup S) (IBr iota) :=
    rightAutomorphismAction (X := IBr iota) (selectedOuterField S)
  exact semidirectMulAction (selectedOuterField S)
    (rightAutomorphismSemidirectCompatible
      (X := IBr iota) (selectedOuterField S))

/-- The stabiliser of one Brauer character in the selected semidirect
presentation. -/
abbrev SelectedBrauerAmbient
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (psi : IBr iota) :=
  @semidirectStabilizer X _ (SelectedOuterGroup S) (IBr iota) _
    (selectedOuterField S) (selectedBrauerSemidirectAction iota S) psi

/-- The embedded stabiliser for the normal factor. -/
def SelectedBrauerBase
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (psi : IBr iota) :
    Subgroup (SelectedBrauerAmbient iota S psi) :=
  @embeddedHStabilizer X _ (SelectedOuterGroup S) (IBr iota) _
    (selectedOuterField S) (selectedBrauerSemidirectAction iota S) psi

/-- Every element of the normal factor fixes an irreducible Brauer
character. -/
theorem selectedBrauer_inner_fixed
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (psi : IBr iota) (x : X) :
    let _ : MulAction (SelectedOuterAmbient S) (IBr iota) :=
      selectedBrauerSemidirectAction iota S
    (SemidirectProduct.inl x : SelectedOuterAmbient S) • psi = psi := by
  dsimp only
  change IrreducibleBrauerCharacter.twist iota psi (MulAut.conj x⁻¹) = psi
  exact inner_fixes_ibr iota x psi

/-- The centreless central quotient is canonically the embedded normal
factor in the selected Brauer stabiliser. -/
def selectedBaseEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :
    CentralCharacterQuotient P reference ≃*
      SelectedBrauerBase P.iota S psi.1 :=
  (centerlessCentralCharacterQuotientEquiv P hcenter reference).trans
    (@canonicalHToEmbeddedEquiv P.H (SelectedOuterGroup S) (IBr P.iota)
      _ _ (selectedOuterField S) (selectedBrauerSemidirectAction P.iota S)
      psi.1 (selectedBrauer_inner_fixed P.iota S psi.1))

/-- The selected stabiliser acts on the original group through the canonical
semidirect automorphism map. -/
def selectedAmbientToMulAut
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (psi : Definition35Brauer P) :
    SelectedBrauerAmbient P.iota S psi.1 →* MulAut P.H :=
  (semidirectToMulAut (selectedOuterField S)).comp
    (SelectedBrauerAmbient P.iota S psi.1).subtype

/-- Transport the selected stabiliser action to the centreless central
quotient. -/
def selectedQuotientConjugation
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :
    SelectedBrauerAmbient P.iota S psi.1 →*
      MulAut (CentralCharacterQuotient P reference) :=
  (MulAut.congr
      (centerlessCentralCharacterQuotientEquiv P hcenter reference).symm).toMonoidHom.comp
    (selectedAmbientToMulAut P S psi)

/-! ## Stabiliser transport -/

/-- An equivariant equivalence of acted sets and acting groups restricts to
an equivalence of point stabilisers. -/
def stabilizerMulEquivOfEquivariant
    {G G' Y Y' : Type u} [Group G] [Group G']
    [MulAction G Y] [MulAction G' Y']
    (groupEquiv : G ≃* G') (setEquiv : Y ≃ Y')
    (equivariant : ∀ g y,
      setEquiv (g • y) = groupEquiv g • setEquiv y)
    (y : Y) :
    MulAction.stabilizer G y ≃*
      MulAction.stabilizer G' (setEquiv y) where
  toFun g := ⟨groupEquiv g.1, by
    change groupEquiv g.1 • setEquiv y = setEquiv y
    rw [← equivariant, g.2]⟩
  invFun g := ⟨groupEquiv.symm g.1, by
    apply setEquiv.injective
    rw [equivariant, groupEquiv.apply_symm_apply, g.2]⟩
  left_inv g := Subtype.ext (groupEquiv.symm_apply_apply g.1)
  right_inv g := Subtype.ext (groupEquiv.apply_symm_apply g.1)
  map_mul' g h := Subtype.ext (groupEquiv.map_mul g.1 h.1)

@[simp]
theorem stabilizerMulEquivOfEquivariant_apply_coe
    {G G' Y Y' : Type u} [Group G] [Group G']
    [MulAction G Y] [MulAction G' Y']
    (groupEquiv : G ≃* G') (setEquiv : Y ≃ Y')
    (equivariant : ∀ g y,
      setEquiv (g • y) = groupEquiv g • setEquiv y)
    (y : Y) (g : MulAction.stabilizer G y) :
    ((stabilizerMulEquivOfEquivariant
      groupEquiv setEquiv equivariant y g :
      MulAction.stabilizer G' (setEquiv y)) : G') =
        groupEquiv g.1 :=
  rfl

/-- Inversion followed by passage to the opposite group is a group
equivalence. -/
def inverseOpEquiv (G : Type u) [Group G] : G ≃* Gᵐᵒᵖ where
  toFun g := MulOpposite.op g⁻¹
  invFun g := g.unop⁻¹
  left_inv g := by simp
  right_inv g := by
    apply MulOpposite.unop_injective
    simp
  map_mul' g h := by simp

/-- A bijective selected semidirect presentation, written in the opposite
automorphism convention used by the Brauer action. -/
def selectedOuterOpCoverEquiv
    {k X : Type u} [Field k]
    [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    SelectedOuterAmbient S ≃* (MulAut X)ᵐᵒᵖ :=
  (MulEquiv.ofBijective
      (semidirectToMulAut (selectedOuterField S)) haut).trans
    (inverseOpEquiv (MulAut X))

@[simp]
theorem selectedOuterOpCoverEquiv_apply
    {k X : Type u} [Field k]
    [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (g : SelectedOuterAmbient S) :
    selectedOuterOpCoverEquiv S haut g = selectedOuterOpCover S g :=
  by
    apply MulOpposite.unop_injective
    simp [selectedOuterOpCoverEquiv, selectedOuterOpCover,
      inverseOpEquiv, inverseOpHom]

/-- The selected semidirect action is the right automorphism action through
the opposite cover. -/
theorem selectedBrauer_smul_eq_selectedOuterOpCover
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (g : SelectedOuterAmbient S) (psi : IBr iota) :
    let _ : MulAction (SelectedOuterAmbient S) (IBr iota) :=
      selectedBrauerSemidirectAction iota S
    g • psi = selectedOuterOpCover S g • psi := by
  dsimp only
  letI : MulAction X (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : X →* MulAut X)
  letI : MulAction (SelectedOuterGroup S) (IBr iota) :=
    rightAutomorphismAction (X := IBr iota) (selectedOuterField S)
  letI : MulAction (SelectedOuterAmbient S) (IBr iota) :=
    selectedBrauerSemidirectAction iota S
  change g • psi = IrreducibleBrauerCharacter.twist iota psi
    (semidirectToMulAut (selectedOuterField S) g⁻¹)
  exact semidirect_smul_ibr_eq_twist_inverse
    iota (selectedOuterField S) g psi

/-- Restriction of the full selected automorphism presentation to the
stabiliser of one Brauer character. -/
def selectedBrauerAmbientEquivAutomorphismStabilizer
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (psi : Definition35Brauer P)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    SelectedBrauerAmbient P.iota S psi.1 ≃*
      MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1 :=
  @stabilizerMulEquivOfEquivariant
    (SelectedOuterAmbient S) ((MulAut P.H)ᵐᵒᵖ)
    (IBr P.iota) (IBr P.iota)
    _ _ (selectedBrauerSemidirectAction P.iota S) _
    (selectedOuterOpCoverEquiv S haut) (Equiv.refl _)
    (fun g chi => by
      simpa using selectedBrauer_smul_eq_selectedOuterOpCover
        P.iota S g chi)
    psi.1

/-- The centreless central quotient used for the selected Brauer
character. -/
abbrev SelectedCentralQuotient
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P) :=
  centerlessCentralQuotientBrauerSourceFromReference
    P hcenter reference psi

/-- Transport of Brauer characters from the centreless cover to its central
quotient. -/
def selectedQuotientBrauerEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P) :
    IBr P.iota ≃ IBr (SelectedCentralQuotient P hcenter reference psi).iota :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv P.iota
    (centerlessCentralCharacterQuotientEquiv P hcenter reference).symm

/-- Conjugation of automorphisms through the centreless central quotient,
in the opposite group convention. -/
def selectedQuotientAutomorphismOpEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P) :
    (MulAut P.H)ᵐᵒᵖ ≃*
      (MulAut (CentralCharacterQuotient P reference))ᵐᵒᵖ :=
  MulEquiv.op (MulAut.congr
    (centerlessCentralCharacterQuotientEquiv P hcenter reference).symm)

/-- Transport of the automorphism stabiliser to the canonical quotient
Brauer character. -/
def selectedAutomorphismStabilizerEquivQuotient
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P) :
    MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1 ≃*
      QuotientBrauerAutomorphismStabilizer P reference psi
        (SelectedCentralQuotient P hcenter reference psi) :=
  stabilizerMulEquivOfEquivariant
    (selectedQuotientAutomorphismOpEquiv P hcenter reference)
    (selectedQuotientBrauerEquiv P hcenter reference psi)
    (fun alpha chi => by
      exact IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul
        P.iota
        (centerlessCentralCharacterQuotientEquiv
          P hcenter reference).symm chi alpha)
    psi.1

/-- The selected Brauer stabiliser is the automorphism stabiliser required
for the quotient character. -/
def selectedBrauerAmbientEquivQuotientStabilizer
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    SelectedBrauerAmbient P.iota S psi.1 ≃*
      QuotientBrauerAutomorphismStabilizer P reference psi
        (SelectedCentralQuotient P hcenter reference psi) :=
  (selectedBrauerAmbientEquivAutomorphismStabilizer P S psi haut).trans
    (selectedAutomorphismStabilizerEquivQuotient
      P hcenter reference psi)

@[simp]
theorem selectedBrauerAmbientEquivQuotientStabilizer_apply_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (a : SelectedBrauerAmbient P.iota S psi.1) :
    ((selectedBrauerAmbientEquivQuotientStabilizer
        P hcenter reference psi S haut a :
      QuotientBrauerAutomorphismStabilizer P reference psi
        (SelectedCentralQuotient P hcenter reference psi)) :
      (MulAut (CentralCharacterQuotient P reference))ᵐᵒᵖ) =
    selectedQuotientAutomorphismOpEquiv P hcenter reference
      (selectedOuterOpCoverEquiv S haut a.1) :=
  rfl

/-! ## The centre and the conjugation square -/

@[simp]
theorem selectedBaseEquiv_apply_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (h : CentralCharacterQuotient P reference) :
    ((((selectedBaseEquiv P hcenter reference psi S h :
        SelectedBrauerBase P.iota S psi.1) :
      SelectedBrauerAmbient P.iota S psi.1) :
      SelectedOuterAmbient S)) =
        SemidirectProduct.inl
          (centerlessCentralCharacterQuotientEquiv
            P hcenter reference h) :=
  rfl

/-- Conjugation in the selected semidirect product agrees with its canonical
automorphism of the normal factor. -/
theorem selectedOuter_conjugate_inl
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (g : SelectedOuterAmbient S) (h : X) :
    g * SemidirectProduct.inl h * g⁻¹ =
      SemidirectProduct.inl
        (semidirectToMulAut (selectedOuterField S) g h) := by
  have hmap : semidirectToMulAut (selectedOuterField S) g =
      MulAut.conj g.left * selectedOuterField S g.right := by
    calc
      semidirectToMulAut (selectedOuterField S) g =
          semidirectToMulAut (selectedOuterField S)
            (SemidirectProduct.inl g.left *
              SemidirectProduct.inr g.right) :=
        congrArg (semidirectToMulAut (selectedOuterField S))
          (SemidirectProduct.inl_left_mul_inr_right g).symm
      _ = MulAut.conj g.left * selectedOuterField S g.right := by
        rw [map_mul, semidirectToMulAut_inl, semidirectToMulAut_inr]
  apply SemidirectProduct.ext
  · rw [hmap]
    simp [MulAut.conj_apply, mul_assoc]
  · simp

/-- The centraliser of the embedded normal factor in the selected Brauer
stabiliser is trivial. -/
theorem selectedBrauerBase_centralizer_eq_bot
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (psi : Definition35Brauer P)
    (hcenter : Subgroup.center P.H = ⊥)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    Subgroup.centralizer
      (SelectedBrauerBase P.iota S psi.1 :
        Set (SelectedBrauerAmbient P.iota S psi.1)) = ⊥ := by
  apply le_antisymm
  · intro a ha
    have hcomm : ∀ h : P.H,
        semidirectToMulAut (selectedOuterField S) a.1 *
            semidirectToMulAut (selectedOuterField S)
              (SemidirectProduct.inl h) =
          semidirectToMulAut (selectedOuterField S)
              (SemidirectProduct.inl h) *
            semidirectToMulAut (selectedOuterField S) a.1 := by
      intro h
      let b : SelectedBrauerBase P.iota S psi.1 :=
        @canonicalHToEmbeddedEquiv P.H (SelectedOuterGroup S)
          (IBr P.iota) _ _ (selectedOuterField S)
          (selectedBrauerSemidirectAction P.iota S) psi.1
          (selectedBrauer_inner_fixed P.iota S psi.1) h
      have hb : (b : SelectedBrauerAmbient P.iota S psi.1) ∈
          SelectedBrauerBase P.iota S psi.1 := b.2
      have heq := Subgroup.mem_centralizer_iff.mp ha
        (b : SelectedBrauerAmbient P.iota S psi.1) hb
      have heq' :
          (b : SelectedBrauerAmbient P.iota S psi.1).1 * a.1 =
            a.1 * (b : SelectedBrauerAmbient P.iota S psi.1).1 :=
        congrArg
          (fun z : SelectedBrauerAmbient P.iota S psi.1 ↦
            (z : SelectedOuterAmbient S)) heq
      have hbcoe :
          (b : SelectedBrauerAmbient P.iota S psi.1).1 =
            SemidirectProduct.inl h := rfl
      rw [hbcoe] at heq'
      have heq'' := congrArg
        (semidirectToMulAut (selectedOuterField S)) heq'.symm
      simpa only [map_mul] using heq''
    have htrivial :
        semidirectToMulAut (selectedOuterField S) a.1 = 1 :=
      mulAut_eq_one_of_commutes_semidirect_inner
        hcenter (selectedOuterField S)
          (semidirectToMulAut (selectedOuterField S) a.1) hcomm
    have haOne : a.1 = 1 := by
      apply haut.1
      simpa using htrivial
    have haSub : a = 1 := Subtype.ext haOne
    simp [haSub]
  · exact bot_le

/-- The selected Brauer stabiliser is centreless. -/
theorem selectedBrauerAmbient_center_eq_bot
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (psi : Definition35Brauer P)
    (hcenter : Subgroup.center P.H = ⊥)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    Subgroup.center (SelectedBrauerAmbient P.iota S psi.1) = ⊥ := by
  apply le_antisymm
  · calc
      Subgroup.center (SelectedBrauerAmbient P.iota S psi.1) ≤
          Subgroup.centralizer
            (SelectedBrauerBase P.iota S psi.1 :
              Set (SelectedBrauerAmbient P.iota S psi.1)) :=
        Subgroup.center_le_centralizer _
      _ = ⊥ := selectedBrauerBase_centralizer_eq_bot
        P S psi hcenter haut
  · exact bot_le

/-- Conjugation on the selected base is the transported quotient
automorphism. -/
theorem selectedQuotientConjugation_on_base
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (a : SelectedBrauerAmbient P.iota S psi.1)
    (h : CentralCharacterQuotient P reference) :
    ((selectedBaseEquiv P hcenter reference psi S
        (selectedQuotientConjugation P hcenter reference psi S a h) :
      SelectedBrauerBase P.iota S psi.1) :
      SelectedBrauerAmbient P.iota S psi.1) =
        a *
          (selectedBaseEquiv P hcenter reference psi S h :
            SelectedBrauerAmbient P.iota S psi.1) * a⁻¹ := by
  apply Subtype.ext
  change SemidirectProduct.inl
      (semidirectToMulAut (selectedOuterField S) a.1
        (centerlessCentralCharacterQuotientEquiv
          P hcenter reference h)) =
    a.1 * SemidirectProduct.inl
      (centerlessCentralCharacterQuotientEquiv
        P hcenter reference h) * a.1⁻¹
  exact (selectedOuter_conjugate_inl S a.1
    (centerlessCentralCharacterQuotientEquiv
      P hcenter reference h)).symm

/-! ## The automorphism quotient and the ambient package -/

/-- Quotienting the centreless selected stabiliser by its centre gives the
automorphism stabiliser of the quotient Brauer character. -/
def selectedAutomorphismQuotientEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    SelectedBrauerAmbient P.iota S psi.1 ⧸
        Subgroup.center (SelectedBrauerAmbient P.iota S psi.1) ≃*
      QuotientBrauerAutomorphismStabilizer P reference psi
        (SelectedCentralQuotient P hcenter reference psi) :=
  (QuotientGroup.quotientMulEquivOfEq
      (selectedBrauerAmbient_center_eq_bot P S psi hcenter haut)).trans
    (QuotientGroup.quotientBot.trans
      (selectedBrauerAmbientEquivQuotientStabilizer
        P hcenter reference psi S haut))

@[simp]
theorem selectedAutomorphismQuotientEquiv_mk
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (a : SelectedBrauerAmbient P.iota S psi.1) :
    selectedAutomorphismQuotientEquiv
        P hcenter reference psi S haut
        (QuotientGroup.mk'
          (Subgroup.center (SelectedBrauerAmbient P.iota S psi.1)) a) =
      selectedBrauerAmbientEquivQuotientStabilizer
        P hcenter reference psi S haut a := by
  change
    (QuotientGroup.quotientBot.trans
      (selectedBrauerAmbientEquivQuotientStabilizer
        P hcenter reference psi S haut))
      (QuotientGroup.quotientMulEquivOfEq
        (selectedBrauerAmbient_center_eq_bot P S psi hcenter haut)
        (QuotientGroup.mk a)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The quotient equivalence sends a selected ambient element to the
opposite of its inverse transported quotient automorphism. -/
theorem selectedAutomorphismQuotientEquiv_natural
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (a : SelectedBrauerAmbient P.iota S psi.1) :
    ((selectedAutomorphismQuotientEquiv
        P hcenter reference psi S haut
        (QuotientGroup.mk'
          (Subgroup.center (SelectedBrauerAmbient P.iota S psi.1)) a) :
        QuotientBrauerAutomorphismStabilizer P reference psi
          (SelectedCentralQuotient P hcenter reference psi)) :
      (MulAut (CentralCharacterQuotient P reference))ᵐᵒᵖ) =
        inverseOpHom
          (selectedQuotientConjugation
            P hcenter reference psi S) a := by
  rw [selectedAutomorphismQuotientEquiv_mk]
  rw [selectedBrauerAmbientEquivQuotientStabilizer_apply_coe]
  apply MulOpposite.unop_injective
  simp [selectedQuotientAutomorphismOpEquiv,
    selectedOuterOpCoverEquiv,
    selectedQuotientConjugation, selectedAmbientToMulAut,
    inverseOpEquiv, inverseOpHom]

/-- The selected Brauer stabiliser supplies the ambient group required by
the Spath extension condition whenever the selected semidirect presentation
is the full automorphism group. -/
abbrev selectedOuterSpathAmbientCore
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    SpathAmbientGroup P reference psi
      (SelectedCentralQuotient P hcenter reference psi) := by
  letI : Fintype (SelectedBrauerAmbient P.iota S psi.1) :=
    Fintype.ofFinite _
  letI : (SelectedBrauerBase P.iota S psi.1).Normal := by
    unfold SelectedBrauerBase
    infer_instance
  refine {
    A := SelectedBrauerAmbient P.iota S psi.1
    base := SelectedBrauerBase P.iota S psi.1
    baseEquiv := selectedBaseEquiv P hcenter reference psi S
    baseCentralizer_eq_center := ?_
    centerPrimeTo := ?_
    conjugation := selectedQuotientConjugation
      P hcenter reference psi S
    conjugation_on_base := selectedQuotientConjugation_on_base
      P hcenter reference psi S
    automorphismQuotientEquiv := selectedAutomorphismQuotientEquiv
      P hcenter reference psi S haut
    automorphismQuotientEquiv_natural :=
      selectedAutomorphismQuotientEquiv_natural
        P hcenter reference psi S haut }
  · rw [selectedBrauerBase_centralizer_eq_bot
      P S psi hcenter haut,
    selectedBrauerAmbient_center_eq_bot P S psi hcenter haut]
  · rw [selectedBrauerAmbient_center_eq_bot P S psi hcenter haut,
      Subgroup.card_bot]
    exact P.iota.prime.not_dvd_one

/-- The concrete selected outer sources for the Fischer family at the prime
three discharge the automorphism presentation hypothesis of the core
constructor. -/
def selectedOuterSpathAmbient
    (family : Definition35Family.{u} 3)
    (block : family.Block)
    (hcenter : Subgroup.center family.H = ⊥)
    (reference psi : Definition35Brauer (family.problem block))
    (S : Fi24ThreeBlockSource (k := family.k) (X := family.H))
    (Outer : C2OuterActionSource family.iota S)
    (Kernel : C2OuterInnerKernelSource family.iota S Outer) :
    SpathAmbientGroup (family.problem block) reference psi
      (SelectedCentralQuotient
        (family.problem block) hcenter reference psi) :=
  selectedOuterSpathAmbientCore
    (family.problem block) hcenter reference psi S
      (selectedSemidirectToMulAut_bijective
        family.iota S Outer Kernel hcenter)

end ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
