import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
import Mathlib.Algebra.CharP.Reduced

/-! The original modular central scalar determines an actual ordinary
linear character through the retained root embedding. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralRootLift
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralRestrictionFormula
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open EvenFieldFLZBAWGoodFamily

universe u

theorem modularLinearValue_pow
    {p : ℕ} {k K H : Type u}
    [Field k] [Field K] [CharP k p] [Group H] [Finite H]
    (root : PrimeRegularRootEmbedding p k K H) (nu : H →* kˣ) (h : H) :
    (nu h : k) ^ primeRegularExponent p H = 1 := by
  let : Fact p.Prime := ⟨root.prime⟩
  have hcard : (nu h : k) ^ Nat.card H = 1 := by
    have heq := congrArg (fun x : kˣ => (x : k))
      (congrArg nu (pow_card_eq_one' (x := h)))
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using heq
  apply (ExpChar.pow_prime_pow_mul_eq_one_iff p
    ((Nat.card H).factorization p) (primeRegularExponent p H) (nu h : k)).mp
  have hfactor := Nat.ordProj_mul_ordCompl_eq_self (Nat.card H) p
  change p ^ (Nat.card H).factorization p * primeRegularExponent p H = Nat.card H at hfactor
  rw [hfactor]
  exact hcard

def modularLinearRoot
    {p : ℕ} {k K H : Type u}
    [Field k] [Field K] [CharP k p] [Group H] [Finite H]
    (root : PrimeRegularRootEmbedding p k K H) (nu : H →* kˣ) :
    H →* rootsOfUnity (primeRegularExponent p H) k where
  toFun h := ⟨nu h, by
    apply (mem_rootsOfUnity (primeRegularExponent p H) (nu h)).mpr
    apply Units.ext
    exact modularLinearValue_pow root nu h⟩
  map_one' := Subtype.ext (map_one nu)
  map_mul' h j := Subtype.ext (map_mul nu h j)

def liftedLinearHom
    {p : ℕ} {k K H : Type u}
    [Field k] [Field K] [CharP k p] [Group H] [Finite H]
    (root : PrimeRegularRootEmbedding p k K H) (nu : H →* kˣ) : H →* Kˣ :=
  (rootsOfUnity (primeRegularExponent p H) K).subtype.comp
    (root.toMulEquiv.toMonoidHom.comp (modularLinearRoot root nu))

def linearRepresentation {K H : Type u} [Field K] [Group H] (ell : H →* Kˣ) :
    Representation K H (Fin 1 → K) where
  toFun h := (ell h : K) • LinearMap.id
  map_one' := by
    change (ell 1 : K) • (1 : Module.End K (Fin 1 → K)) = 1
    rw [map_one, Units.val_one, one_smul]
  map_mul' h j := by
    change (ell (h * j) : K) • (1 : Module.End K (Fin 1 → K)) =
      ((ell h : K) • 1) * ((ell j : K) • 1)
    rw [map_mul, Units.val_mul]
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, smul_smul]

def ordinaryLinearIrr {K H : Type u} [Field K] [CharZero K] [Group H]
    (ell : H →* Kˣ) : OrdinaryIrreducibleCharacter.Irr K H :=
  ⟨fun h => (ell h : K), ⟨{
    dimension := 1
    representation := linearRepresentation ell
    irreducible := by
      let V := Fin 1 → K
      let rho := linearRepresentation ell
      let : Nontrivial (Subrepresentation rho) :=
        ⟨⟨⊥, ⊤, by
          intro heq
          exact (bot_ne_top : (⊥ : Submodule K V) ≠ ⊤)
            (congrArg Subrepresentation.toSubmodule heq)⟩⟩
      let : IsSimpleOrder (Submodule K V) :=
        is_simple_module_of_finrank_eq_one (show Module.finrank K V = 1 by simp [V])
      refine IsSimpleOrder.mk ?_
      intro W
      rcases IsSimpleOrder.eq_bot_or_eq_top W.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.ext h)
      · exact Or.inr (Subrepresentation.ext h)
    character_eq := by
      funext h
      simp [Representation.character, linearRepresentation] }⟩⟩

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [CharZero K]
variable [Group G] [Fintype G]

def ordinaryCentralHom (iota : PrimeRegularRootEmbedding p k K G)
    (nu : Subgroup.center G →* kˣ) : Subgroup.center G →* Kˣ :=
  liftedLinearHom (subgroupRoot iota (Subgroup.center G)) nu

def ordinaryCentralLambda (iota : PrimeRegularRootEmbedding p k K G)
    (nu : Subgroup.center G →* kˣ) : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center G) :=
  ordinaryLinearIrr (ordinaryCentralHom iota nu)

theorem ordinaryCentralLambda_subgroup_value (iota : PrimeRegularRootEmbedding p k K G)
    (nu : Subgroup.center G →* kˣ) (z : Subgroup.center G) :
    ordinaryCentralLambda iota nu z = (subgroupRoot iota (Subgroup.center G)).lift (nu z : k) := by
  exact ((subgroupRoot iota (Subgroup.center G)).lift_coe
    (modularLinearRoot (subgroupRoot iota (Subgroup.center G)) nu z)).symm

theorem ordinaryCentralLambda_value (iota : PrimeRegularRootEmbedding p k K G)
    (nu : Subgroup.center G →* kˣ) (z : Subgroup.center G) :
    ordinaryCentralLambda iota nu z = iota.lift (nu z : k) := by
  rw [ordinaryCentralLambda_subgroup_value]
  exact subgroupRoot_lift_coe iota (Subgroup.center G)
    (modularLinearRoot (subgroupRoot iota (Subgroup.center G)) nu z)

theorem ordinaryCentralLambda_one (iota : PrimeRegularRootEmbedding p k K G)
    (nu : Subgroup.center G →* kˣ) : ordinaryCentralLambda iota nu 1 = 1 := by
  change (ordinaryCentralHom iota nu 1 : K) = 1
  rw [map_one, Units.val_one]

theorem ordinaryCentralLambda_faithful (iota : PrimeRegularRootEmbedding p k K G)
    (nu : Subgroup.center G →* kˣ) (hnu : Function.Injective nu) :
    Function.Injective (ordinaryCentralLambda iota nu) := by
  intro z t h
  apply hnu
  let root := subgroupRoot iota (Subgroup.center G)
  have hu : ordinaryCentralHom iota nu z = ordinaryCentralHom iota nu t := by
    apply Units.ext
    exact h
  have hr : root.toMulEquiv (modularLinearRoot root nu z) =
      root.toMulEquiv (modularLinearRoot root nu t) := Subtype.ext hu
  exact congrArg Subtype.val (root.toMulEquiv.injective hr)

theorem rootSectorLocal_over_ordinaryCentralLambda
    (iota : PrimeRegularRootEmbedding p k K G) (nu : Subgroup.center G →* kˣ)
    (Q : RadicalSubgroup (p := p) (G := G)) (theta : RootSectorLocal iota nu Q)
    (z : Subgroup.center G) :
    centralRestriction (characterWeightAt iota.prime Q theta.val) z =
      theta.val.val 1 * ordinaryCentralLambda iota nu z := by
  rw [ordinaryCentralLambda_value]
  exact theta.property z

variable [IsAlgClosed k]

theorem scalarBrauer_lies_over_ordinaryCentralLambda
    (iota : PrimeRegularRootEmbedding p k K G) (nu : Subgroup.center G →* kˣ)
    (phi : ScalarBrauerSector iota nu) (z : PrimeRegularElement (G := Subgroup.center G) p) :
    phi.val.val (PrimeRegularElement.map (Subgroup.center G).subtype z) =
      phi.val.val ⟨1, isPrimeRegular_one⟩ * ordinaryCentralLambda iota nu z.val := by
  let rho := (chosenIBrRepresentation iota phi.val).ρ
  let : Representation.IsIrreducible rho := (Classical.choose_spec phi.val.property).1
  have hscalar : Representation.centralCharacter rho (Subgroup.center G) le_rfl = nu :=
    (Representation.existsUnique_centralCharacter rho (Subgroup.center G) le_rfl).unique
      (Representation.centralCharacter_spec rho (Subgroup.center G) le_rfl) phi.property
  have hvalue : phi.val.val (PrimeRegularElement.map (Subgroup.center G).subtype z) =
      (Module.finrank k (chosenIBrRepresentation iota phi.val).V : K) * iota.lift (nu z.val : k) := by
    rw [chosenIBrRepresentation_character]
    simpa only [hscalar, rho, PrimeRegularElement.map, Subgroup.coe_subtype] using
      Representation.brauerCharacterOfRootEmbedding_apply_central
        rho iota (Subgroup.center G) le_rfl z.val (z.property.map (Subgroup.center G).subtype)
  have hone : phi.val.val ⟨1, isPrimeRegular_one⟩ =
      (Module.finrank k (chosenIBrRepresentation iota phi.val).V : K) := by
    rw [chosenIBrRepresentation_character]
    exact brauer_value_one rho iota
  rw [hone, ordinaryCentralLambda_value]
  exact hvalue

theorem along_localBrauer_reduction {L : Type u} [Group L] [Finite L]
    (iota : PrimeRegularRootEmbedding p k K G) (V : CharacterWeight p K G)
    (source : CanonicalRawReduction iota V)
    (eN : Subgroup.normalizer (V.subgroup : Set G) ≃* L)
    (n : PrimeRegularElement (G := L) p) :
    V.localCharacter (QuotientGroup.mk'
      (V.subgroup.subgroupOf (Subgroup.normalizer (V.subgroup : Set G))) (eN.symm n.val)) =
      (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer).val n := by
  exact source.localBrauer_reduction (PrimeRegularElement.map eN.symm.toMonoidHom n)

omit [CharZero K] [IsAlgClosed k] in
theorem center_order_coprime [Fintype (Subgroup.center G)]
    [Invertible (Fintype.card (Subgroup.center G) : k)]
    (iota : PrimeRegularRootEmbedding p k K G) :
    (Nat.card (Subgroup.center G)).Coprime p := by
  have hnot : ¬ p ∣ Nat.card (Subgroup.center G) := by
    rw [Nat.card_eq_fintype_card]
    exact (CharP.isUnit_natCast_iff (R := k) iota.prime).mp
      (isUnit_of_invertible (Fintype.card (Subgroup.center G) : k))
  exact (iota.prime.coprime_iff_not_dvd.mpr hnot).symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
