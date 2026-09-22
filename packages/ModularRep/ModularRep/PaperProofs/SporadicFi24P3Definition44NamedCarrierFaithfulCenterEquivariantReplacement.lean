import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCenterAmbient

/-! The faithful-centre character-triple deduction for centres of orders
three, four and six. The actual Brauer stabilizer is inner, so the ambient
is the original group itself. Every original global/local pair with the
same faithful scalar character has direct gamma-product models with equal
factor classes. A correspondence is needed only to select such a pair. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCenterEquivariantReplacement

open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement
open SporadicFi24P3Definition44NamedCarrierFaithfulCenterAmbient
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel

universe u

def topRestriction {k H U : Type u} [Field k] [Group H]
    [AddCommGroup U] [Module k U] (rho : Representation k H U) :
    Representation k ↥(⊤ : Subgroup H) U :=
  Representation.pullback rho (⊤ : Subgroup H).subtype

def topModel {k H U : Type u} [Field k] [Group H]
    [AddCommGroup U] [Module k U] (rho : Representation k H U) :
    AssociatedProjectiveModel (⊤ : Subgroup H) (topRestriction rho) where
  operator := rho
  operator_bijective := rho.apply_bijective
  operator_one := map_one rho
  restriction _ := rfl
  factorSet := ScalarFactorSet.trivial
  operator_mul g h := by simp [ScalarFactorSet.trivial, map_mul]

theorem topRestriction_irreducible
    {k H U : Type u} [Field k] [Group H]
    [AddCommGroup U] [Module k U]
    (rho : Representation k H U) (hirr : rho.IsIrreducible) :
    (topRestriction rho).IsIrreducible :=
  hirr.pullback (⊤ : Subgroup H).subtype
    (by intro h; exact ⟨⟨h, Subgroup.mem_top h⟩, rfl⟩)

theorem topRestriction_affords
    {p : ℕ} {k K H U : Type u}
    [Field k] [Field K] [Group H] [Finite H]
    [CharP k p] [IsAlgClosed k] [CharZero K]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (root : PrimeRegularRootEmbedding p k K H)
    (theta : IBr root) (rho : Representation k H U)
    (hchar : theta.1 = rho.brauerCharacterOfRootEmbedding root) :
    (IrreducibleBrauerCharacter.alongMulEquiv root
      (Subgroup.topEquiv.symm : H ≃* ↥(⊤ : Subgroup H)) theta).1 =
      (topRestriction rho).brauerCharacterOfRootEmbedding
        (root.alongMulEquiv (Subgroup.topEquiv.symm : H ≃* ↥(⊤ : Subgroup H))) := by
  rw [IrreducibleBrauerCharacter.alongMulEquiv_val]
  exact (congrArg
    (PrimeRegularClassFunction.pullback (⊤ : Subgroup H).subtype) hchar).trans
      (Representation.brauerCharacterOfRootEmbedding_pullback_mulEquiv
        rho root (Subgroup.topEquiv.symm : H ≃* ↥(⊤ : Subgroup H))).symm

def topQuotientEquiv {H J : Type u} [Group H] [Group J] (f : H →* J) :
    H ⧸ (⊤ : Subgroup H) ≃* J ⧸ (⊤ : Subgroup J) := by
  letI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  letI : Subsingleton (J ⧸ (⊤ : Subgroup J)) := QuotientGroup.subsingleton_quotient_top
  refine MulEquiv.ofBijective
    (QuotientGroup.map ⊤ ⊤ f (by intro x hx; trivial)) ?_
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨1, Subsingleton.elim _ _⟩⟩

theorem topQuotientEquiv_mk {H J : Type u} [Group H] [Group J]
    (f : H →* J) (x : H) :
    topQuotientEquiv f (QuotientGroup.mk' ⊤ x) = QuotientGroup.mk' ⊤ (f x) := rfl

theorem originalAmbient_centralizer {G : Type u} [Group G] :
    Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = Subgroup.center G := by
  simpa only [Subgroup.coe_top] using (Subgroup.centralizer_univ (G := G))

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (nu : Subgroup.center G →* kˣ) (phi : ScalarBrauerSector iota nu)

def gammaRoot : PrimeRegularRootEmbedding p k K (Subgroup.center G) :=
  subgroupRoot iota (Subgroup.center G)

def gammaRepresentation : Representation k (Subgroup.center G) k where
  toFun z := (nu z : k) • LinearMap.id
  map_one' := by
    change (nu 1 : k) • (1 : Module.End k k) = 1
    rw [nu.map_one, Units.val_one, one_smul]
  map_mul' c d := by
    change (nu (c * d) : k) • (1 : Module.End k k) =
      ((nu c : k) • 1) * ((nu d : k) • 1)
    rw [nu.map_mul, Units.val_mul]
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, smul_smul]

def gamma : IBr (gammaRoot iota) :=
  ⟨(gammaRepresentation nu).brauerCharacterOfRootEmbedding (gammaRoot iota),
    ⟨FDRep.of (gammaRepresentation nu), oneDimensional_irreducible _, rfl⟩⟩

theorem gamma_value (c : PrimeRegularElement (G := Subgroup.center G) p) :
    (gamma iota nu).1 c = (gammaRoot iota).lift (nu c.1 : k) := by
  change ((((nu c.1 : k) • (LinearMap.id : Module.End k k)).charpoly.roots).map
    (gammaRoot iota).lift).sum = _
  rw [Representation.roots_charpoly_smul_id, Module.finrank_self,
    Multiset.replicate_one, Multiset.map_singleton, Multiset.sum_singleton]

theorem gamma_fixed (a : G) :
    IrreducibleBrauerCharacter.twist (gammaRoot iota) (gamma iota nu)
      (MulAut.conjNormal a) = gamma iota nu := by
  have he : MulAut.conjNormal a = MulEquiv.refl (Subgroup.center G) := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change a * c.1 * a⁻¹ = c.1
    rw [Subgroup.mem_center_iff.mp c.2 a, mul_assoc, mul_inv_cancel, mul_one]
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  rw [he]
  rfl

variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)

local notation "B" => (⊤ : Subgroup G)
local notation "Z" => Subgroup.center G
local notation "N" => Subgroup.normalizer (V.subgroup : Set G)
local notation "L" => (⊤ : Subgroup N)
local notation "ZL" => Subgroup.comap (Subgroup.subtype N) Z
local notation "eG" => (Subgroup.topEquiv.symm : G ≃* B)
local notation "eN" => (Subgroup.topEquiv.symm : N ≃* L)
local notation "rG" => PrimeRegularRootEmbedding.alongMulEquiv iota eG
local notation "rL" => PrimeRegularRootEmbedding.alongMulEquiv source.normalizerRoot eN
local notation "phiG" => IrreducibleBrauerCharacter.alongMulEquiv iota eG (Subtype.val phi)
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer

def globalRepresentation : Representation k B (chosenIBrRepresentation iota phi.1).V :=
  topRestriction (chosenIBrRepresentation iota phi.1).ρ

def localRepresentation : Representation k L
    (chosenIBrRepresentation source.normalizerRoot source.localBrauer).V :=
  topRestriction (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ

theorem global_affords : (phiG).1 =
    (globalRepresentation iota nu phi).brauerCharacterOfRootEmbedding rG :=
  topRestriction_affords iota phi.1 _ (chosenIBrRepresentation_character iota phi.1)

theorem local_affords : (phiL).1 =
    (localRepresentation iota V source).brauerCharacterOfRootEmbedding rL :=
  topRestriction_affords source.normalizerRoot source.localBrauer _
    (chosenIBrRepresentation_character source.normalizerRoot source.localBrauer)

local notation "rhoG" => globalRepresentation iota nu phi
local notation "rhoL" => localRepresentation iota V source
local notation "qE" => topQuotientEquiv (Subgroup.subtype N)

theorem global_model_product (M : AssociatedProjectiveModel B rhoG)
    (x : G) (z : Subgroup.center G) :
    M.operator (x * z.1) = (chosenIBrRepresentation iota phi.1).ρ x * (nu z : k) • 1 := by
  change M.operator ((eG x : G) * (eG z.1 : G)) = _
  rw [M.base_mul, M.restriction]
  exact congrArg ((chosenIBrRepresentation iota phi.1).ρ x * ·) (phi.2 z)

theorem local_model_product
    (hlocal : ∀ z : Subgroup.center G,
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
        (Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z) =
          (nu z : k) • 1)
    (M : AssociatedProjectiveModel L rhoL) (n : N) (z : Subgroup.center G) :
    M.operator (n * Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z) =
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ n * (nu z : k) • 1 := by
  let nz : N := Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z
  change M.operator ((eN n : N) * (eN nz : N)) = _
  rw [M.base_mul, M.restriction]
  exact congrArg ((chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ n * ·)
    (hlocal z)

/- These fixed predicates abbreviate output properties only. All fields
are constructed below from the original characters and representations. -/
def GlobalGammaProduct (M : AssociatedProjectiveModel B rhoG) : Prop :=
  Representation.IsIrreducible rhoG ∧
  (phiG).1 = (rhoG).brauerCharacterOfRootEmbedding rG ∧
  (IrreducibleBrauerCharacter.alongMulEquiv rG
    (collapsedProductEquiv B Z le_top).symm phiG).1 =
      (collapsedProductRepresentation B Z le_top rhoG).brauerCharacterOfRootEmbedding
        ((rG).alongMulEquiv (collapsedProductEquiv B Z le_top).symm) ∧
  ∀ (x : G) (z : Subgroup.center G),
    M.operator (x * z.1) = (chosenIBrRepresentation iota phi.1).ρ x * (nu z : k) • 1

def LocalGammaProduct (M : AssociatedProjectiveModel L rhoL) : Prop :=
  Representation.IsIrreducible rhoL ∧
  (phiL).1 = (rhoL).brauerCharacterOfRootEmbedding rL ∧
  (IrreducibleBrauerCharacter.alongMulEquiv rL
    (collapsedProductEquiv L ZL le_top).symm phiL).1 =
      (collapsedProductRepresentation L ZL le_top rhoL).brauerCharacterOfRootEmbedding
        ((rL).alongMulEquiv (collapsedProductEquiv L ZL le_top).symm) ∧
  ∀ (n : N) (z : Subgroup.center G),
    M.operator (n * Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z) =
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ n * (nu z : k) • 1

/-- The centres-three/four/six step of the manuscript replacement lemma:
the original ambient realizes the full stabilizer; the same central gamma
and retained global/local representations give the product characters;
their factor classes agree through the actual normalizer inclusion. -/
theorem faithful_center_equivariant_replacement
    (hnu : Function.Injective nu)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (tau : MulAut G)
    (hcard : Nat.card (Subgroup.center G) = 3 ∨
      Nat.card (Subgroup.center G) = 4 ∨ Nat.card (Subgroup.center G) = 6)
    (hinverts : ∀ z : Subgroup.center G, tau (z : G) = (z : G)⁻¹)
    (hlocal : ∀ z : Subgroup.center G,
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
        (Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z) =
          (nu z : k) • 1) :
    Function.Surjective (innerEmbedding iota phi.1) ∧
    Subgroup.centralizer (B : Set G) = Z ∧
    B ⊔ Z = B ∧ L ⊔ ZL = L ∧
    (∀ a : G, IrreducibleBrauerCharacter.twist (gammaRoot iota)
      (gamma iota nu) (MulAut.conjNormal a) = gamma iota nu) ∧
    (∀ c : PrimeRegularElement (G := Z) p,
      (gamma iota nu).1 c = (gammaRoot iota).lift (nu c.1 : k)) ∧
    ∃ (MG : AssociatedProjectiveModel B rhoG) (ML : AssociatedProjectiveModel L rhoL),
      GlobalGammaProduct iota nu phi MG ∧
      LocalGammaProduct iota nu V source ML ∧
      MG.factorSet = ScalarFactorSet.trivial ∧
      ML.factorSet = ScalarFactorSet.trivial ∧
      (∀ n : N, qE (QuotientGroup.mk' L n) = QuotientGroup.mk' B n.1) ∧
      ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
      ScalarFactorSet.Cohomologous ML.factorSet
        (ScalarFactorSet.pullback qE MG.factorSet) := by
  have hgt : 2 < Nat.card (Subgroup.center G) := by
    rcases hcard with h | h | h <;> omega
  refine ⟨originalAmbient_surjective iota nu phi hnu hOuter tau hgt hinverts,
    originalAmbient_centralizer, top_sup_eq _, top_sup_eq _,
    gamma_fixed iota nu, gamma_value iota nu, ?_⟩
  have hG : Representation.IsIrreducible rhoG :=
    topRestriction_irreducible _ (Classical.choose_spec phi.1.2).1
  have hL : Representation.IsIrreducible rhoL :=
    topRestriction_irreducible _ (Classical.choose_spec source.localBrauer.2).1
  have hcharG := global_affords iota nu phi
  have hcharL := local_affords iota V source
  refine ⟨topModel (chosenIBrRepresentation iota phi.1).ρ,
    topModel (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ,
    ⟨hG, hcharG, collapsedProduct_affords B Z le_top rG phiG rhoG hcharG,
      global_model_product iota nu phi _⟩,
    ⟨hL, hcharL, collapsedProduct_affords L ZL le_top rL phiL rhoL hcharL,
      local_model_product iota nu V source hlocal _⟩,
    rfl, rfl, topQuotientEquiv_mk (Subgroup.subtype N), rfl,
    ScalarFactorSet.trivial_cohomologous_pullback_trivial qE⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCenterEquivariantReplacement


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
