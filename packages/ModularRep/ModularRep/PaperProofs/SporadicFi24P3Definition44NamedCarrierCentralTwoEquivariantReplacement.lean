import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch

/-! The centre-order-two matched gamma-product cohomology deduction. The original extension and
the arbitrary correspondence on the common scalar sector determine the
actual matched characters. Navarro 8.12 supplies extensions of their same
chosen representations; their associated gamma-product factors agree.
The deduction works for every common scalar sector, including the faithful
sector in the manuscript. It does not assert existence of its input map. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement

open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel

universe u

theorem oneDimensional_irreducible {k H : Type u} [Field k] [Group H]
    (rho : Representation k H k) : rho.IsIrreducible := by
  let : Nontrivial (Subrepresentation rho) :=
    ⟨⟨⊥, ⊤, by
      intro h
      exact (bot_ne_top : (⊥ : Submodule k k) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  let : IsSimpleOrder (Submodule k k) :=
    is_simple_module_of_finrank_eq_one (Module.finrank_self k)
  refine IsSimpleOrder.mk ?_
  intro W
  rcases IsSimpleOrder.eq_bot_or_eq_top W.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.ext h)
  · exact Or.inr (Subrepresentation.ext h)

def collapsedProductEquiv {H : Type u} [Group H]
    (B C : Subgroup H) (hC : C ≤ B) : ↥(B ⊔ C) ≃* B :=
  MulEquiv.subgroupCongr (sup_eq_left.mpr hC)

def collapsedProductRepresentation {k H U : Type u} [Field k] [Group H]
    [AddCommGroup U] [Module k U] (B C : Subgroup H) (hC : C ≤ B)
    (rho : Representation k B U) : Representation k ↥(B ⊔ C) U :=
  rho.pullback (collapsedProductEquiv B C hC).toMonoidHom

theorem collapsedProduct_affords
    {p : ℕ} {k K H U : Type u} [Field k] [Field K] [Group H] [Finite H]
    [CharP k p] [IsAlgClosed k] [CharZero K]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (B C : Subgroup H) (hC : C ≤ B)
    (root : PrimeRegularRootEmbedding p k K B) (theta : IBr root)
    (rho : Representation k B U)
    (hchar : theta.1 = rho.brauerCharacterOfRootEmbedding root) :
    (IrreducibleBrauerCharacter.alongMulEquiv root
      (collapsedProductEquiv B C hC).symm theta).1 =
        (collapsedProductRepresentation B C hC rho).brauerCharacterOfRootEmbedding
          (root.alongMulEquiv (collapsedProductEquiv B C hC).symm) := by
  rw [IrreducibleBrauerCharacter.alongMulEquiv_val]
  change PrimeRegularClassFunction.pullback (collapsedProductEquiv B C hC).toMonoidHom theta.1 =
    (rho.pullback (collapsedProductEquiv B C hC).toMonoidHom).brauerCharacterOfRootEmbedding _
  exact (congrArg (PrimeRegularClassFunction.pullback
    (collapsedProductEquiv B C hC).toMonoidHom) hchar).trans
      (Representation.brauerCharacterOfRootEmbedding_pullback_mulEquiv
        rho root (collapsedProductEquiv B C hC).symm).symm

variable {p : ℕ} {k K G T C : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group T] [Group C] [Finite T]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (nu : Subgroup.center G →* kˣ) (phi : ScalarBrauerSector iota nu)
variable (E : GroupExtension G T C) (hC : Nat.card C = 2)
variable (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
variable (hAut : Function.Surjective E.conjAct)
variable (hZ : Nat.card (Subgroup.center G) = 2)

local notation "A" => brauerAmbient E iota (Subtype.val phi)
local notation "i" => brauerEmbedding E iota (Subtype.val phi)
local notation "hi" => brauerEmbedding_injective E iota (Subtype.val phi)
local notation "B" => MonoidHom.range i
local notation "Z" => Subgroup.centralizer (B : Set A)
local notation "eG" => MonoidHom.ofInjective hi

def centerEquiv : Subgroup.center G ≃* Z :=
  ((Subgroup.center G).equivMapOfInjective i hi).trans
    (MulEquiv.subgroupCongr (brauerCentralizer_eq_center_map E iota phi.1 hC hOuter hAut).symm)

omit [Finite T] in
theorem centerEquiv_ambient (z : Subgroup.center G) :
    (centerEquiv iota nu phi E hC hOuter hAut z : A) = i z.1 := rfl

include hC hOuter hAut in
omit [Finite T] in
theorem centralizer_le_base : Z ≤ B := by
  rw [brauerCentralizer_eq_center_map E iota phi.1 hC hOuter hAut]
  exact Subgroup.map_le_range _ _

include hC hOuter hAut hZ in
omit [Finite T] in
theorem centralizer_central : Z ≤ Subgroup.center A := by
  rw [brauerCentralizer_eq_center_map E iota phi.1 hC hOuter hAut]
  exact brauerCenterMap_central E iota phi.1 hZ

local notation "eZ" => centerEquiv iota nu phi E hC hOuter hAut

def gammaScalar : Z →* kˣ := nu.comp (eZ).symm.toMonoidHom

def gammaRoot : PrimeRegularRootEmbedding p k K Z :=
  (subgroupRoot iota (Subgroup.center G)).alongMulEquiv eZ

def gammaRepresentation : Representation k Z k where
  toFun c := (gammaScalar iota nu phi E hC hOuter hAut c : k) • LinearMap.id
  map_one' := by
    change (gammaScalar iota nu phi E hC hOuter hAut 1 : k) • (1 : Module.End k k) = 1
    rw [(gammaScalar iota nu phi E hC hOuter hAut).map_one, Units.val_one, one_smul]
  map_mul' c d := by
    change (gammaScalar iota nu phi E hC hOuter hAut (c * d) : k) • (1 : Module.End k k) =
      ((gammaScalar iota nu phi E hC hOuter hAut c : k) • 1) *
        ((gammaScalar iota nu phi E hC hOuter hAut d : k) • 1)
    rw [(gammaScalar iota nu phi E hC hOuter hAut).map_mul, Units.val_mul]
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, smul_smul]

def gamma : IBr (gammaRoot iota nu phi E hC hOuter hAut) :=
  ⟨(gammaRepresentation iota nu phi E hC hOuter hAut).brauerCharacterOfRootEmbedding
    (gammaRoot iota nu phi E hC hOuter hAut),
    ⟨FDRep.of (gammaRepresentation iota nu phi E hC hOuter hAut),
      oneDimensional_irreducible _, rfl⟩⟩

theorem gamma_value (c : PrimeRegularElement (G := Z) p) :
    (gamma iota nu phi E hC hOuter hAut).1 c =
      (gammaRoot iota nu phi E hC hOuter hAut).lift
        (gammaScalar iota nu phi E hC hOuter hAut c.1 : k) := by
  change ((((gammaScalar iota nu phi E hC hOuter hAut c.1 : k) •
    (LinearMap.id : Module.End k k)).charpoly.roots).map
      (gammaRoot iota nu phi E hC hOuter hAut).lift).sum = _
  rw [Representation.roots_charpoly_smul_id, Module.finrank_self,
    Multiset.replicate_one, Multiset.map_singleton, Multiset.sum_singleton]

include hZ in
theorem gamma_fixed (a : A) :
    IrreducibleBrauerCharacter.twist (gammaRoot iota nu phi E hC hOuter hAut)
      (gamma iota nu phi E hC hOuter hAut) (MulAut.conjNormal a) =
        gamma iota nu phi E hC hOuter hAut := by
  have he : MulAut.conjNormal a = MulEquiv.refl Z := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change a * c.1 * a⁻¹ = c.1
    rw [Subgroup.mem_center_iff.mp
      (centralizer_central iota nu phi E hC hOuter hAut hZ c.2) a,
      mul_assoc, mul_inv_cancel, mul_one]
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  rw [he]
  rfl

variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)

local notation "N" => Subgroup.normalizer (V.subgroup : Set G)
local notation "D" => embeddedNormalizer i V.subgroup
local notation "L" => embeddedLocalBase i V.subgroup
local notation "eN" => normalizerBaseEquiv i hi V.subgroup
local notation "rG" => PrimeRegularRootEmbedding.alongMulEquiv iota eG
local notation "rL" => PrimeRegularRootEmbedding.alongMulEquiv source.normalizerRoot eN
local notation "phiG" => IrreducibleBrauerCharacter.alongMulEquiv iota eG (Subtype.val phi)
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer

def globalRepresentation : Representation k B (chosenIBrRepresentation iota phi.1).V :=
  Representation.pullback (chosenIBrRepresentation iota phi.1).ρ (eG).symm.toMonoidHom

def localRepresentation : Representation k L
    (chosenIBrRepresentation source.normalizerRoot source.localBrauer).V :=
  Representation.pullback (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
    (eN).symm.toMonoidHom

theorem global_affords : (phiG).1 =
    (globalRepresentation iota nu phi E).brauerCharacterOfRootEmbedding rG := by
  rw [IrreducibleBrauerCharacter.alongMulEquiv_val]
  change _ = (Representation.pullback (chosenIBrRepresentation iota phi.1).ρ
    (eG).symm.toMonoidHom).brauerCharacterOfRootEmbedding rG
  rw [Representation.brauerCharacterOfRootEmbedding_pullback_mulEquiv,
    chosenIBrRepresentation_character]

theorem local_affords : (phiL).1 =
    (localRepresentation iota nu phi E V source).brauerCharacterOfRootEmbedding rL := by
  rw [IrreducibleBrauerCharacter.alongMulEquiv_val]
  change _ = (Representation.pullback (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
    (eN).symm.toMonoidHom).brauerCharacterOfRootEmbedding rL
  rw [Representation.brauerCharacterOfRootEmbedding_pullback_mulEquiv,
    chosenIBrRepresentation_character]

include hC hOuter hAut hZ in
omit [Finite T] in
theorem centralizer_le_normalizer : Z ≤ D :=
  (centralizer_central iota nu phi E hC hOuter hAut hZ).trans
    (Subgroup.center_le_normalizer (V.subgroup.map i : Set A))

def centralizerToNormalizer : Z →* D :=
  Subgroup.inclusion (centralizer_le_normalizer iota nu phi E hC hOuter hAut hZ V)

include hC hOuter hAut in
omit [Finite T] in
theorem local_product_denominator : L ⊔ ((Z).comap (D).subtype) = L := by
  apply sup_eq_left.mpr
  intro c hc
  exact centralizer_le_base iota nu phi E hC hOuter hAut hc

omit [Finite T] in
theorem global_model_product
    (M : AssociatedProjectiveModel B (globalRepresentation iota nu phi E))
    (x : G) (z : Subgroup.center G) :
    M.operator (i x * (eZ z : A)) = (chosenIBrRepresentation iota phi.1).ρ x *
      (gammaScalar iota nu phi E hC hOuter hAut (eZ z) : k) • 1 := by
  change M.operator ((eG x : A) * (eG z.1 : A)) = _
  rw [M.base_mul, M.restriction]
  change (chosenIBrRepresentation iota phi.1).ρ ((eG).symm (eG x)) *
    (chosenIBrRepresentation iota phi.1).ρ ((eG).symm (eG z.1)) = _
  rw [(eG).symm_apply_apply, (eG).symm_apply_apply, phi.2 z]
  change _ = _ * (nu ((eZ).symm (eZ z)) : k) • 1
  rw [(eZ).symm_apply_apply]

omit [Finite T] in
theorem local_model_product
    (hlocal : ∀ z : Subgroup.center G,
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
        (Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z) =
          (nu z : k) • 1)
    (M : AssociatedProjectiveModel L (localRepresentation iota nu phi E V source))
    (n : N) (z : Subgroup.center G) :
    M.operator (ModularRep.normalizerMap i V.subgroup n *
      centralizerToNormalizer iota nu phi E hC hOuter hAut hZ V (eZ z)) =
        (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ n *
          (gammaScalar iota nu phi E hC hOuter hAut (eZ z) : k) • 1 := by
  let nz : N := Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z
  change M.operator ((eN n : D) * (eN nz : D)) = _
  rw [M.base_mul, M.restriction]
  change (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
      ((eN).symm (eN n)) *
    (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ ((eN).symm (eN nz)) = _
  rw [(eN).symm_apply_apply, (eN).symm_apply_apply, hlocal z]
  change _ = _ * (nu ((eZ).symm (eZ z)) : k) • 1
  rw [(eZ).symm_apply_apply]


variable (Omega : ScalarBrauerSector iota nu →
  ConjugacyClass (p := p) (K := K) (G := G))
variable (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (chi chi' : ScalarBrauerSector iota nu),
  chi'.1 = a • chi.1 → Omega chi' = a • Omega chi)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) :
  ConjugacyClass (p := p) (K := K) (G := G)) = Omega phi)

local notation "rhoG" => globalRepresentation iota nu phi E
local notation "rhoL" => localRepresentation iota nu phi E V source
local notation "rZ" => gammaRoot iota nu phi E hC hOuter hAut
local notation "gam" => gamma iota nu phi E hC hOuter hAut
local notation "nuZ" => gammaScalar iota nu phi E hC hOuter hAut
local notation "ZL" => Subgroup.comap (Subgroup.subtype D) Z
local notation "hBG" => centralizer_le_base iota nu phi E hC hOuter hAut
local notation "hBL" => Iff.mp sup_eq_left (local_product_denominator iota nu phi E hC hOuter hAut V)
local notation "qE" => matchedLocalQuotientEquiv iota nu phi V Omega hOmega hclass E

/- The following two fixed predicates abbreviate output properties only.
They are never source inputs; the final proof constructs every field. -/
def GlobalGammaProduct (M : AssociatedProjectiveModel B rhoG) : Prop :=
  Representation.IsIrreducible rhoG ∧
  (phiG).1 = (rhoG).brauerCharacterOfRootEmbedding rG ∧
  (IrreducibleBrauerCharacter.alongMulEquiv rG
    (collapsedProductEquiv B Z hBG).symm phiG).1 =
      (collapsedProductRepresentation B Z hBG rhoG).brauerCharacterOfRootEmbedding
        ((rG).alongMulEquiv (collapsedProductEquiv B Z hBG).symm) ∧
  ∀ (x : G) (z : Subgroup.center G),
    M.operator (i x * (eZ z : A)) =
      (chosenIBrRepresentation iota phi.1).ρ x * (nuZ (eZ z) : k) • 1

def LocalGammaProduct (M : AssociatedProjectiveModel L rhoL) : Prop :=
  Representation.IsIrreducible rhoL ∧
  (phiL).1 = (rhoL).brauerCharacterOfRootEmbedding rL ∧
  (IrreducibleBrauerCharacter.alongMulEquiv rL
    (collapsedProductEquiv L ZL hBL).symm phiL).1 =
      (collapsedProductRepresentation L ZL hBL rhoL).brauerCharacterOfRootEmbedding
        ((rL).alongMulEquiv (collapsedProductEquiv L ZL hBL).symm) ∧
  ∀ (n : N) (z : Subgroup.center G),
    M.operator (ModularRep.normalizerMap i V.subgroup n *
      centralizerToNormalizer iota nu phi E hC hOuter hAut hZ V (eZ z)) =
        (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ n *
          (nuZ (eZ z) : k) • 1

omit [Finite T] in
/-- The centre-two gamma-product comparison in the manuscript replacement
lemma, for every original matched pair. The original chosen representations
afford both the transported characters and their collapsed central products.
Their ambient models satisfy the same-gamma operator equations and have
equal factor classes under the literal inclusion-induced quotient map. -/
theorem central_two_equivariant_replacement
    (hlocal : ∀ z : Subgroup.center G,
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
        (Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z) =
          (nu z : k) • 1)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    letI : Finite T := extension_finite E hC
    Function.Surjective (brauerAction E iota phi.1) ∧
    (∀ a : A, ∃ d : D, ∃ x : G, a = d.1 * i x) ∧
    Z ≤ Subgroup.center A ∧
    B ⊔ Z = B ∧ L ⊔ ZL = L ∧
    (∀ a : A, IrreducibleBrauerCharacter.twist rZ gam (MulAut.conjNormal a) = gam) ∧
    (∀ c : PrimeRegularElement (G := Z) p, (gam).1 c = (rZ).lift (nuZ c.1 : k)) ∧
    ∃ (MG : AssociatedProjectiveModel B rhoG) (ML : AssociatedProjectiveModel L rhoL),
      GlobalGammaProduct iota nu phi E hC hOuter hAut MG ∧
      LocalGammaProduct iota nu phi E hC hOuter hAut hZ V source ML ∧
      MG.factorSet = ScalarFactorSet.trivial ∧
      ML.factorSet = ScalarFactorSet.trivial ∧
      (∀ d : D, qE (QuotientGroup.mk' L d) = QuotientGroup.mk' B d.1) ∧
      ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
      ScalarFactorSet.Cohomologous ML.factorSet
        (ScalarFactorSet.pullback qE MG.factorSet) := by
  let : Finite T := extension_finite E hC
  refine ⟨brauerAction_surjective E iota phi.1 hAut,
    matchedAmbient_factorization iota nu phi V Omega hOmega hclass E,
    centralizer_central iota nu phi E hC hOuter hAut hZ,
    sup_eq_left.mpr hBG, local_product_denominator iota nu phi E hC hOuter hAut V,
    gamma_fixed iota nu phi E hC hOuter hAut hZ,
    gamma_value iota nu phi E hC hOuter hAut, ?_⟩
  have hG : Representation.IsIrreducible rhoG :=
    (show Representation.IsIrreducible (chosenIBrRepresentation iota phi.1).ρ from
      (Classical.choose_spec phi.1.2).1).pullback (eG).symm.toMonoidHom (eG).symm.surjective
  have hL : Representation.IsIrreducible rhoL :=
    (show Representation.IsIrreducible
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ from
        (Classical.choose_spec source.localBrauer.2).1).pullback
          (eN).symm.toMonoidHom (eN).symm.surjective
  have hcharG := global_affords iota nu phi E
  have hcharL := local_affords iota nu phi E V source
  have hcyclicG : IsCyclic (A ⧸ B) := brauerQuotient_cyclic E iota phi.1 hC
  have hcyclicL : IsCyclic (D ⧸ L) := by
    let : IsCyclic (A ⧸ B) := hcyclicG
    exact isCyclic_of_injective (qE).toMonoidHom (qE).injective
  obtain ⟨EG⟩ := Representation.exists_extension_of_brauerCharacter_fixed_cyclic_quotient
    principle rG rhoG hG hcyclicG (by
      intro a
      rw [← hcharG]
      exact congrArg Subtype.val (globalBase_fixed iota nu phi E a))
  obtain ⟨EL⟩ := Representation.exists_extension_of_brauerCharacter_fixed_cyclic_quotient
    principle rL rhoL hL hcyclicL (by
      intro d
      rw [← hcharL]
      exact congrArg Subtype.val (localBase_fixed iota nu phi V Omega hOmega hclass E source d))
  refine ⟨AssociatedProjectiveModel.ofExtension EG, AssociatedProjectiveModel.ofExtension EL,
    ⟨hG, hcharG, collapsedProduct_affords B Z hBG rG phiG rhoG hcharG,
      global_model_product iota nu phi E hC hOuter hAut _⟩,
    ⟨hL, hcharL, collapsedProduct_affords L ZL hBL rL phiL rhoL hcharL,
      local_model_product iota nu phi E hC hOuter hAut hZ V source hlocal _⟩,
    rfl, rfl, ?_, rfl, ?_⟩
  · exact matchedLocalQuotientEquiv_mk iota nu phi V Omega hOmega hclass E
  · exact ScalarFactorSet.trivial_cohomologous_pullback_trivial qE

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
