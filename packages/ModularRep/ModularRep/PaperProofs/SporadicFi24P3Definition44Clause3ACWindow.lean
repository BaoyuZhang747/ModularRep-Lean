import ModularRep.BrauerCharacterEquivTransport
import ModularRep.PrimeRegularRootEmbeddingSubgroup
import ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier

/-!
# A selected-carrier window for An--Dietrich Definition 4.4(3a)--(3c)

The source statement used to choose the scope of this file is the verbatim
local copy of An--Dietrich, Definition 4.4(3), especially lines 428--436:

* `X` is normal in `G_theta`, its centre is central in `G_theta`, and `theta`
  is invariant;
* the pair stabiliser is exactly the group induced by the relevant local
  normaliser, and `G_theta = X N_{G_theta}(Q)`;
* `C_{G_theta}(X)` is abelian and carries a `G_theta`-invariant Brauer
  character above the central character.

This is intentionally a moving-window module below the paper's target
predicate.  It never assumes a Definition 3.5 block-isomorphism, a character
triple predicate, BAW, or iBAW.  Its character-weight equivalence `Omega` is
arbitrary and enters only through full automorphism equivariance and the
pointwise equation `w = Omega psi`.

Source boundary: `Fi24ThreeBlockSource`, centrelessness, and bijectivity of
the selected semidirect presentation are the source-facing carrier inputs.
Everything proved below from those inputs is a kernel deduction.  The final
identification with the paper's named `Omega`, `lambda`, and character-triple
relation is deliberately left to a later join module.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.CyclicOuterRawPairNormalizer
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open scoped MonoidAlgebra

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

/-! ## The literal normal factor and its invariant character -/

/-- The original group is literally equivalent to the embedded normal
factor of its selected Brauer stabiliser. -/
noncomputable def selectedClause3BaseEquiv
    (P : Definition35Problem.{u})
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :
    P.H ≃* SelectedBrauerBase P.iota S psi.1 :=
  @canonicalHToEmbeddedEquiv P.H (SelectedOuterGroup S) (IBr P.iota)
    _ _ (selectedOuterField S) (selectedBrauerSemidirectAction P.iota S)
    psi.1 (selectedBrauer_inner_fixed P.iota S psi.1)

/-- The literal inclusion of `X` into the selected `G_theta`. -/
def selectedClause3BaseEmbedding
    (P : Definition35Problem.{u})
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :
    P.H →* SelectedBrauerAmbient P.iota S psi.1 :=
  (SelectedBrauerBase P.iota S psi.1).subtype.comp
    (selectedClause3BaseEquiv P psi S).toMonoidHom

/-- Kernel deduction corresponding to `X \triangleleft G_theta`. -/
theorem selectedClause3Base_normal
    (P : Definition35Problem.{u})
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :
    (SelectedBrauerBase P.iota S psi.1).Normal := by
  unfold SelectedBrauerBase
  infer_instance

/-- In the centreless carrier, the image of `Z(X)` is central in
`G_theta`. -/
theorem selectedClause3Center_image_le
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :
    (Subgroup.center P.H).map (selectedClause3BaseEmbedding P psi S) ≤
      Subgroup.center (SelectedBrauerAmbient P.iota S psi.1) := by
  rw [hcenter, Subgroup.map_bot]
  exact bot_le

/-- Membership in the selected Brauer stabiliser is exactly invariance of
the selected character. -/
theorem selectedClause3Character_fixed
    (P : Definition35Problem.{u})
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (a : SelectedBrauerAmbient P.iota S psi.1) :
    let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
      selectedBrauerSemidirectAction P.iota S
    a.1 • psi.1 = psi.1 := by
  dsimp only
  exact a.2

/-! ## Clause (3a): the local normaliser and product decomposition -/

/-- Every element of the selected `G_theta` is a product of an element of
the embedded `X` and an element of the matched raw-pair stabiliser.  The
extra membership proof records that the second factor really lies in
`G_theta`, not merely in the surrounding semidirect product.

The proof is pointwise in an arbitrary fully equivariant `Omega`; no witness
tied to the An--Dietrich table bijection is imported. -/
theorem selectedBrauerAmbient_factorization
    (P : Definition35Problem.{u})
    (psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1) :
    ∀ a : SelectedBrauerAmbient P.iota S psi.1,
      ∃ b : SelectedBrauerBase P.iota S psi.1,
        ∃ n : SelectedPairStabilizer P S w,
          n.1 ∈ SelectedBrauerAmbient P.iota S psi.1 ∧
          (a.1 : SelectedOuterAmbient S) =
            ((b : SelectedBrauerAmbient P.iota S psi.1) :
                SelectedOuterAmbient S) *
              ((n : SelectedPairStabilizer P S w) :
                SelectedOuterAmbient S) := by
  letI : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  letI : MulAction (SelectedOuterAmbient S)
      (RawWeightClass (p := P.p) (K := P.K) (H := P.H)) :=
    canonicalRawSemidirectAction (selectedOuterField S)
  letI : MulAction (SelectedOuterAmbient S) (GlobalWeight P) :=
    canonicalWeightSemidirectAction (selectedOuterField S)
  intro a
  let r := selectedRawWeight P.blockSource P.block w
  have hweight : a.1 • Omega psi.1 = Omega psi.1 := by
    rw [← selectedOmega_semidirect_equivariant P S Omega hOmega]
    rw [a.2]
  have horbit : rawWeightOrbit (a.1 • r) = rawWeightOrbit r := by
    calc
      rawWeightOrbit (a.1 • r) = a.1 • rawWeightOrbit r :=
        rawWeightOrbit_semidirect_smul (selectedOuterField S) a.1 r
      _ = rawWeightOrbit r := by
        rw [show rawWeightOrbit r = w.1 by
          exact rawWeightOrbit_selectedRawWeight P w]
        rw [hmatch, hweight]
  obtain ⟨h, hh⟩ := Quotient.exact horbit
  let nFull : SelectedOuterAmbient S :=
    SemidirectProduct.inl h⁻¹ * a.1
  have hnfix : nFull • r = r := by
    dsimp [nFull]
    rw [mul_smul, ← hh]
    rw [semidirect_inl_smul]
    exact inv_smul_smul h r
  let n : SelectedPairStabilizer P S w := ⟨nFull, hnfix⟩
  have hnBrauer : n.1 ∈ SelectedBrauerAmbient P.iota S psi.1 := by
    have hnInter : nFull ∈
        SelectedBrauerAmbient P.iota S psi.1 ⊓
          Subgroup.normalizer
            (rawAmbientRadical (selectedOuterField S)
              (selectedRawWeight P.blockSource P.block w) :
                Set (SelectedOuterAmbient S)) := by
      rw [← selectedPairStabilizer_eq_brauer_inf_normalizer
        P S Omega hOmega psi w hmatch]
      exact hnfix
    exact hnInter.1
  let b : SelectedBrauerBase P.iota S psi.1 :=
    @canonicalHToEmbeddedEquiv P.H (SelectedOuterGroup S) (IBr P.iota)
      _ _ (selectedOuterField S) (selectedBrauerSemidirectAction P.iota S)
      psi.1 (selectedBrauer_inner_fixed P.iota S psi.1) h
  refine ⟨b, n, hnBrauer, ?_⟩
  change a.1 = SemidirectProduct.inl h * nFull
  simp [nFull]

/-- The subgroup of automorphisms of `X` induced by elements which both fix
`theta` and normalise the literal radical. -/
def SelectedInducedPairAutomorphisms
    (P : Definition35Problem.{u})
    (psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :
    Subgroup (MulAut P.H) :=
  (SelectedBrauerAmbient P.iota S psi.1).map
      (semidirectToMulAut (selectedOuterField S)) ⊓
    (Subgroup.normalizer
      (rawAmbientRadical (selectedOuterField S)
        (selectedRawWeight P.blockSource P.block w) :
          Set (SelectedOuterAmbient S))).map
        (semidirectToMulAut (selectedOuterField S))

/-- Exact equality between the automorphisms induced by the selected pair
normaliser and the intersection required in clause (3a). -/
theorem selectedPair_inducedAutomorphisms_eq
    (P : Definition35Problem.{u})
    (psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (hinjective : Function.Injective
      (semidirectToMulAut (selectedOuterField S))) :
    (SelectedPairStabilizer P S w).map
        (semidirectToMulAut (selectedOuterField S)) =
      SelectedInducedPairAutomorphisms P psi w S := by
  rw [selectedPairStabilizer_eq_brauer_inf_normalizer
    P S Omega hOmega psi w hmatch]
  exact Subgroup.map_inf _ _ _ hinjective

/-- The pair normaliser itself is equivalent to its induced automorphism
group when the selected semidirect presentation is faithful. -/
noncomputable def selectedPairEquivInducedAutomorphisms
    (P : Definition35Problem.{u})
    (psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (hinjective : Function.Injective
      (semidirectToMulAut (selectedOuterField S))) :
    SelectedPairStabilizer P S w ≃*
      SelectedInducedPairAutomorphisms P psi w S :=
  (Subgroup.equivMapOfInjective
    (SelectedPairStabilizer P S w)
    (semidirectToMulAut (selectedOuterField S)) hinjective).trans
      (MulEquiv.subgroupCongr
        (selectedPair_inducedAutomorphisms_eq P psi w S Omega hOmega
          hmatch hinjective))

@[simp]
theorem selectedPairEquivInducedAutomorphisms_coe
    (P : Definition35Problem.{u})
    (psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (hinjective : Function.Injective
      (semidirectToMulAut (selectedOuterField S)))
    (n : SelectedPairStabilizer P S w) :
    ((selectedPairEquivInducedAutomorphisms P psi w S Omega hOmega
      hmatch hinjective n :
        SelectedInducedPairAutomorphisms P psi w S) : MulAut P.H) =
      semidirectToMulAut (selectedOuterField S) n.1 := by
  rfl

/-- The displayed induced automorphism is literally conjugation by the
normaliser element in the selected ambient group. -/
theorem selectedPair_conjugation_on_base
    (P : Definition35Problem.{u})
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (n : SelectedPairStabilizer P S w)
    (x : P.H) :
    (n.1 : SelectedOuterAmbient S) * SemidirectProduct.inl x *
        (n.1 : SelectedOuterAmbient S)⁻¹ =
      SemidirectProduct.inl
        (semidirectToMulAut (selectedOuterField S) n.1 x) :=
  selectedOuter_conjugate_inl S n.1 x

/-! ## Clauses (3b)--(3c): centraliser, its root, and gamma -/

abbrev SelectedClause3Centralizer
    (P : Definition35Problem.{u})
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :=
  Subgroup.centralizer
    (SelectedBrauerBase P.iota S psi.1 :
      Set (SelectedBrauerAmbient P.iota S psi.1))

theorem selectedClause3Centralizer_eq_bot
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    SelectedClause3Centralizer P psi S = ⊥ :=
  selectedBrauerBase_centralizer_eq_bot P S psi hcenter haut

/-- Stronger than clause (3b): the centraliser equals the ambient centre,
and both are trivial. -/
theorem selectedClause3Centralizer_eq_center
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    SelectedClause3Centralizer P psi S =
      Subgroup.center (SelectedBrauerAmbient P.iota S psi.1) := by
  rw [selectedClause3Centralizer_eq_bot P hcenter psi S haut,
    selectedBrauerAmbient_center_eq_bot P S psi hcenter haut]

/-- The clause-(3b) commutativity statement, proved from triviality. -/
theorem selectedClause3Centralizer_commutes
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (c d : SelectedClause3Centralizer P psi S) :
    c * d = d * c := by
  have hc : c.1 = 1 :=
    (Subgroup.eq_bot_iff_forall (SelectedClause3Centralizer P psi S)).mp
      (selectedClause3Centralizer_eq_bot P hcenter psi S haut) c.1 c.2
  have hd : d.1 = 1 :=
    (Subgroup.eq_bot_iff_forall (SelectedClause3Centralizer P psi S)).mp
      (selectedClause3Centralizer_eq_bot P hcenter psi S haut) d.1 d.2
  apply Subtype.ext
  simp [hc, hd]

/-- Restrict a root embedding to a subgroup.  This uses only divisibility of
finite group orders. -/
noncomputable def restrictRootToSubgroup
    {p : ℕ} {k K A : Type u}
    [Field k] [Field K] [Group A] [Finite A]
    (iota : PrimeRegularRootEmbedding p k K A) (N : Subgroup A) :
    PrimeRegularRootEmbedding p k K N where
  prime := iota.prime
  toMulEquiv :=
    PrimeRegularRootEmbedding.restrictRootsOfUnityEquiv
      (by
        simpa only [primeRegularExponent] using
          Nat.ordCompl_dvd_ordCompl_of_dvd
            (Subgroup.card_subgroup_dvd_card N) p)
      iota.toMulEquiv

/-- The unique equivalence between two subgroups both proved trivial. -/
def mulEquivOfEqBot
    {G D : Type u} [Group G] [Group D]
    (H : Subgroup G) (L : Subgroup D)
    (hH : H = ⊥) (hL : L = ⊥) : H ≃* L where
  toFun _ := 1
  invFun _ := 1
  left_inv x := by
    apply Subtype.ext
    simpa using ((Subgroup.eq_bot_iff_forall H).mp hH x.1 x.2).symm
  right_inv x := by
    apply Subtype.ext
    simpa using ((Subgroup.eq_bot_iff_forall L).mp hL x.1 x.2).symm
  map_mul' _ _ := by simp

/-- The one-dimensional trivial representation is irreducible. -/
theorem trivial_rep_irreducible
    {k C : Type u} [Field k] [Group C] :
    Representation.IsIrreducible (Representation.trivial k C k) := by
  letI : Nontrivial
      (Subrepresentation (Representation.trivial k C k)) :=
    ⟨⟨⊥, ⊤, by
      intro h
      exact (bot_ne_top : (⊥ : Submodule k k) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  letI : IsSimpleOrder (Submodule k k) :=
    is_simple_module_of_finrank_eq_one (Module.finrank_self k)
  refine IsSimpleOrder.mk ?_
  intro W
  rcases IsSimpleOrder.eq_bot_or_eq_top W.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.ext h)
  · exact Or.inr (Subrepresentation.ext h)

/-- The irreducible Brauer character of the trivial representation. -/
noncomputable def trivialIBr
    {p : ℕ} {k K C : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group C] [Finite C]
    (iota : PrimeRegularRootEmbedding p k K C) : IBr iota :=
  ⟨Representation.brauerCharacterOfRootEmbedding
      (Representation.trivial k C k) iota,
    ⟨FDRep.of (Representation.trivial k C k),
      trivial_rep_irreducible, rfl⟩⟩

@[simp]
theorem trivialIBr_apply
    {p : ℕ} {k K C : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group C] [Finite C]
    (iota : PrimeRegularRootEmbedding p k K C)
    (g : PrimeRegularElement (G := C) p) :
    (trivialIBr iota).1 g = 1 := by
  change (Multiset.map iota.lift
    ((1 : k →ₗ[k] k).charpoly.roots)).sum = 1
  rw [LinearMap.charpoly_one, Module.finrank_self, pow_one]
  rw [show (1 : Polynomial k) = Polynomial.C 1 by simp]
  rw [Polynomial.roots_X_sub_C]
  simp only [Multiset.map_singleton, Multiset.sum_singleton]
  simpa [PrimeRegularRootEmbedding.liftRoot] using
    iota.lift_coe
      (1 : rootsOfUnity (primeRegularExponent p C) k)

/-- The trivial irreducible Brauer character is invariant under every
automorphism, a statement stronger than the required ambient invariance. -/
theorem trivialIBr_fixed
    {p : ℕ} {k K C : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group C] [Finite C]
    (iota : PrimeRegularRootEmbedding p k K C)
    (alpha : MulAut C) :
    IrreducibleBrauerCharacter.twist iota (trivialIBr iota) alpha =
      trivialIBr iota := by
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  apply PrimeRegularClassFunction.ext
  intro c
  rw [PrimeRegularClassFunction.twist_apply]
  rw [trivialIBr_apply, trivialIBr_apply]

/-- The centraliser and `Z(X)` are both trivial, hence canonically
equivalent. -/
def selectedClause3CentralizerEquivCenter
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    Subgroup.center P.H ≃* SelectedClause3Centralizer P psi S :=
  mulEquivOfEqBot (Subgroup.center P.H)
    (SelectedClause3Centralizer P psi S) hcenter
    (selectedClause3Centralizer_eq_bot P hcenter psi S haut)

/-- A root embedding for the centraliser derived from the original root
embedding; no ambient root-existence hypothesis is added. -/
noncomputable def selectedClause3CentralizerRoot
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    PrimeRegularRootEmbedding P.p P.k P.K
      (SelectedClause3Centralizer P psi S) :=
  (restrictRootToSubgroup P.iota (Subgroup.center P.H)).alongMulEquiv
    (selectedClause3CentralizerEquivCenter P hcenter psi S haut)

/-- The clause-(3c) candidate is literally the trivial irreducible Brauer
character of the trivial centraliser. -/
noncomputable def selectedClause3Gamma
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    IBr (selectedClause3CentralizerRoot P hcenter psi S haut) :=
  trivialIBr (selectedClause3CentralizerRoot P hcenter psi S haut)

/-- Conjugation by `G_theta` on its normal centraliser. -/
def selectedClause3CentralizerConjugation
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    SelectedBrauerAmbient P.iota S psi.1 →*
      MulAut (SelectedClause3Centralizer P psi S) :=
  @MulAut.conjNormal (SelectedBrauerAmbient P.iota S psi.1) _
    (SelectedClause3Centralizer P psi S) (by
      rw [selectedClause3Centralizer_eq_center P hcenter psi S haut]
      infer_instance)

/-- Literal value-one compatibility.  Since both `Z(X)` and the centraliser
are trivial, this is the kernel content of `gamma` lying above the unique
(hence faithful) central character. -/
theorem selectedClause3Gamma_eq_one
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (c : PrimeRegularElement
      (G := SelectedClause3Centralizer P psi S) P.p) :
    (selectedClause3Gamma P hcenter psi S haut).1 c = 1 :=
  trivialIBr_apply _ c

/-- Clause (3c): `gamma` is invariant under conjugation by every element of
the selected `G_theta`. -/
theorem selectedClause3Gamma_invariant
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (a : SelectedBrauerAmbient P.iota S psi.1) :
    IrreducibleBrauerCharacter.twist
        (selectedClause3CentralizerRoot P hcenter psi S haut)
        (selectedClause3Gamma P hcenter psi S haut)
        (selectedClause3CentralizerConjugation P hcenter psi S haut a) =
      selectedClause3Gamma P hcenter psi S haut := by
  apply trivialIBr_fixed

end ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
