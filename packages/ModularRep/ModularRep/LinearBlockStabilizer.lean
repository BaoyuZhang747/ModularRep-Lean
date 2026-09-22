import ModularRep.PrimitiveBlockAutomorphism
import ModularRep.BrauerQuotientLinearCharacterAction
import ModularRep.PrimeRegularPart
import ModularRep.PCore
import Mathlib.Algebra.CharP.Reduced
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Linear characters stabilising a block

The central-sector argument, prime-primary cancellation, quotient descent and
cardinality estimate in the general linear-block-stabiliser lemma. The only
block dictionary below is the standard existence of simple modules in blocks
and the interpretation of the tensor action on blocks. Its fields are global
representation statements; no kernel or stabiliser conclusion is assumed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.LinearBlockStabilizer

universe u v w

variable {p : ℕ} {G k : Type u} [Group G] [Field k]

/-- The central subgroup consisting of the prime regular elements. -/
def centralRegularSubgroup (p : ℕ) (G : Type u) [Group G] : Subgroup G where
  carrier g := g ∈ Subgroup.center G ∧ IsPrimeRegular p g
  one_mem' := ⟨Subgroup.one_mem _, isPrimeRegular_one⟩
  mul_mem' := by
    rintro g h ⟨hg, hgp⟩ ⟨hh, hhp⟩
    refine ⟨Subgroup.mul_mem _ hg hh, ?_⟩
    have hcomm : Commute g h := (Subgroup.mem_center_iff.mp hg h).symm
    exact Nat.Coprime.of_dvd_left hcomm.orderOf_mul_dvd_mul_orderOf (hgp.mul_left hhp)
  inv_mem' := by
    rintro g ⟨hg, hgp⟩
    exact ⟨Subgroup.inv_mem _ hg, (isPrimeRegular_inv g).mpr hgp⟩

theorem centralRegularSubgroup_le_center :
    centralRegularSubgroup p G ≤ Subgroup.center G := fun _ h => h.1

theorem centralRegularSubgroup_card_coprime [Finite G] (hp : p.Prime) :
    (Nat.card (centralRegularSubgroup p G)).Coprime p := by
  apply Nat.Coprime.symm
  apply (hp.coprime_iff_not_dvd).mpr
  intro hdiv
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := centralRegularSubgroup p G) p hdiv
  have hreg := g.property.2
  have hord : orderOf (g : G) = p := (Subgroup.orderOf_mk _ _).symm.trans hg
  change (orderOf (g : G)).Coprime p at hreg
  rw [hord] at hreg
  exact (hp.coprime_iff_not_dvd.mp hreg) (dvd_refl p)

/-- The normalising scalar for the central-sector idempotents is available
in characteristic `p`. -/
@[instance_reducible]
def centralRegularCardInvertible [Finite G] [CharP k p] (hp : p.Prime)
    [Fintype (centralRegularSubgroup p G)] :
    Invertible (Fintype.card (centralRegularSubgroup p G) : k) := by
  apply invertibleOfNonzero
  intro hzero
  have hdiv := (CharP.cast_eq_zero_iff k p _).mp hzero
  exact (hp.coprime_iff_not_dvd.mp
    (centralRegularSubgroup_card_coprime (G := G) hp).symm)
      (by simpa only [Nat.card_eq_fintype_card] using hdiv)

section Sectors

variable {V : Type w} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [IsAlgClosed k]

/-- Tensoring multiplies the central character by the restricted linear
character. This follows from the scalar action, without taking traces. -/
theorem centralCharacter_linearCharacterTwist
    (rho : Representation k G V) [rho.IsIrreducible]
    (lambda : G →* kˣ) (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) :
    letI := Representation.IsIrreducible.linearCharacterTwist
      (rho := rho) inferInstance lambda
    (rho.linearCharacterTwist lambda).centralCharacter Z hZ =
      lambda.comp Z.subtype * rho.centralCharacter Z hZ := by
  let := Representation.IsIrreducible.linearCharacterTwist
    (rho := rho) inferInstance lambda
  symm
  apply (rho.linearCharacterTwist lambda).existsUnique_centralCharacter Z hZ |>.unique
    (y₁ := lambda.comp Z.subtype * rho.centralCharacter Z hZ)
    (y₂ := (rho.linearCharacterTwist lambda).centralCharacter Z hZ)
  · intro z
    change (lambda (z : G) : k) • rho (z : G) = _
    rw [rho.centralCharacter_spec Z hZ z, smul_smul]
    rfl
  · exact (rho.linearCharacterTwist lambda).centralCharacter_spec Z hZ

/-- Two simple representations in one primitive block have the same
central sector. Applied to a representation and its linear twist, this
forces the linear character to be trivial on the central subgroup. -/
theorem trivial_on_central_subgroup_of_same_block
    (rho : Representation k G V) [rho.IsIrreducible]
    (lambda : G →* kˣ) (Z : Subgroup G) [Fintype Z]
    [Invertible (Fintype.card Z : k)] (hZ : Z ≤ Subgroup.center G)
    (b : LiteralPrimitiveBlock k G)
    (hb : ∀ v : rho.asModule, b.1 • v = v)
    (htwist : ∀ v : (rho.linearCharacterTwist lambda).asModule, b.1 • v = v) :
    Z ≤ lambda.ker := by
  let := Representation.IsIrreducible.linearCharacterTwist
    (rho := rho) inferInstance lambda
  have heq := (rho.primitiveCentralIdempotentSector_eq_centralCharacter
    Z hZ b.2 hb).symm.trans
      ((rho.linearCharacterTwist lambda).primitiveCentralIdempotentSector_eq_centralCharacter
        Z hZ b.2 htwist)
  rw [centralCharacter_linearCharacterTwist] at heq
  intro z hz
  have hval := DFunLike.congr_fun heq ⟨z, hz⟩
  change lambda z = 1
  exact mul_right_cancel (show lambda z * rho.centralCharacter Z hZ ⟨z, hz⟩ =
    1 * rho.centralCharacter Z hZ ⟨z, hz⟩ by
      simpa only [one_mul, MonoidHom.mul_apply, MonoidHom.comp_apply,
        Subgroup.coe_subtype] using hval.symm)

end Sectors

/-- A precise E1 dictionary for tensoring blocks: every literal primitive
block supports a finite-dimensional simple module, and tensoring any such
module places it in the tensor-translated block. The scalar-twist formula
itself is the existing `Representation.linearCharacterTwist` construction.
This uses positive tensoring: `c • b` supports `rho` twisted by `linear c`.
Some existing semidirect character actions use inverse tensoring. Their
block stabilisers are the same, since a subgroup is closed under inversion.
This is the module interpretation of the block tensor action, valid over
an algebraically closed coefficient field; see Navarro, *Characters and
Blocks of Finite Groups*, Chapters 2 and 3. -/
structure SimpleBlockTensorSource {C : Type w} [Group C]
    (linear : C →* (G →* kˣ)) [MulAction C (LiteralPrimitiveBlock k G)] where
  representative : LiteralPrimitiveBlock k G → FDRep k G
  irreducible : ∀ b, Representation.IsIrreducible (representative b).ρ
  supports : ∀ b, ∀ v : Representation.asModule (representative b).ρ, b.1 • v = v
  tensor_supports : ∀ (c : C) (b : LiteralPrimitiveBlock k G)
    (V : FDRep k G), Representation.IsIrreducible V.ρ →
    (∀ v : Representation.asModule V.ρ, b.1 • v = v) →
    ∀ v : Representation.asModule (Representation.linearCharacterTwist V.ρ (linear c)),
      (c • b).1 • v = v

theorem stabilizer_trivial_on_central_regular [Finite G] [CharP k p]
    [IsAlgClosed k] (hp : p.Prime) {C : Type w} [Group C]
    (linear : C →* (G →* kˣ)) [MulAction C (LiteralPrimitiveBlock k G)]
    (source : SimpleBlockTensorSource linear) (b : LiteralPrimitiveBlock k G)
    (c : MulAction.stabilizer C b) :
    centralRegularSubgroup p G ≤ (linear c.1).ker := by
  let : Fintype (centralRegularSubgroup p G) := Fintype.ofFinite _
  let := centralRegularCardInvertible (k := k) (G := G) hp
  let V := source.representative b
  let : Representation.IsIrreducible V.ρ := source.irreducible b
  apply trivial_on_central_subgroup_of_same_block V.ρ (linear c.1)
    (centralRegularSubgroup p G) centralRegularSubgroup_le_center b (source.supports b)
  have h := source.tensor_supports c.1 b V (source.irreducible b) (source.supports b)
  simpa only [show c.1 • b = b from c.2] using h

/-- An ordinary character of order prime to `p` is trivial on every
`p`-element. Both annihilating powers are used explicitly. -/
theorem primeTo_character_trivial_on_p_element (lambda : G →* kˣ)
    (horder : (orderOf lambda).Coprime p) {g : G} {n : ℕ}
    (hg : g ^ p ^ n = 1) : lambda g = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes (horder.pow_right n)
  · exact orderOf_dvd_of_pow_eq_one (DFunLike.congr_fun (pow_orderOf_eq_one lambda) g)
  · apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hg, map_one]

/-- In particular the ordinary prime-to-`p` character is trivial on the
central `p`-core (and in fact on every `p`-subgroup). -/
theorem primeTo_character_trivial_on_p_subgroup (lambda : G →* kˣ)
    (horder : (orderOf lambda).Coprime p) (P : Subgroup G) (hP : IsPGroup p P) :
    P ≤ lambda.ker := by
  intro g hg
  obtain ⟨n, hn⟩ := hP ⟨g, hg⟩
  exact primeTo_character_trivial_on_p_element lambda horder
    (congrArg Subtype.val hn)

theorem primeTo_character_trivial_on_central_pCore (lambda : G →* kˣ)
    (horder : (orderOf lambda).Coprime p) :
    (pCore p (Subgroup.center G)).map (Subgroup.center G).subtype ≤ lambda.ker := by
  exact primeTo_character_trivial_on_p_subgroup lambda horder _
    ((pCore_isPGroup p (Subgroup.center G)).map (Subgroup.center G).subtype)

/-- Absence of `p`-torsion among units in characteristic `p`. -/
theorem modular_character_trivial_on_p_element [CharP k p] (hp : p.Prime)
    (lambda : G →* kˣ) {g : G} {n : ℕ} (hg : g ^ p ^ n = 1) : lambda g = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  apply Units.ext
  have hpow : (lambda g : k) ^ (p ^ n * 1) = 1 := by
    simpa using congrArg (fun x : kˣ => (x : k)) (congrArg lambda hg)
  simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff p n 1 (lambda g : k)).mp hpow

theorem center_le_ker_of_regular_and_primary [Finite G] (hp : p.Prime)
    (lambda : G →* kˣ) (hregular : centralRegularSubgroup p G ≤ lambda.ker)
    (hprimary : ∀ (g : G) (n : ℕ), g ^ p ^ n = 1 → lambda g = 1) :
    Subgroup.center G ≤ lambda.ker := by
  intro g hg
  have hreg : primeRegularPart hp g ∈ centralRegularSubgroup p G :=
    ⟨(Subgroup.center G).pow_mem hg _, primeRegular_primeRegularPart hp g⟩
  change lambda g = 1
  rw [← primePart_mul_primeRegularPart hp g, map_mul,
    hprimary (primePart hp g) ((orderOf g).factorization p)
      (primePart_pow_primaryOrderPart hp g), hregular hreg, one_mul]

/-- Explicit factorisation through `G / NZ(G)`, using the normal subgroup
join for `NZ(G)`. -/
def descendCenterQuotient (N : Subgroup G) [N.Normal] (lambda : G →* kˣ)
    (hN : N ≤ lambda.ker) (hZ : Subgroup.center G ≤ lambda.ker) :
    G ⧸ (N ⊔ Subgroup.center G) →* kˣ :=
  LinearCharactersTrivialOn.quotientMulEquiv (N ⊔ Subgroup.center G)
    ⟨lambda, sup_le hN hZ⟩

@[simp]
theorem descendCenterQuotient_apply (N : Subgroup G) [N.Normal]
    (lambda : G →* kˣ) (hN : N ≤ lambda.ker)
    (hZ : Subgroup.center G ≤ lambda.ker) (g : G) :
    descendCenterQuotient N lambda hN hZ (QuotientGroup.mk' _ g) = lambda g := rfl

/-- A family of distinct linear characters of a finite group is finite. -/
theorem finite_of_injective_linear_characters [Finite G] {S : Type w}
    (f : S → (G →* kˣ)) (hf : Function.Injective f) : Finite S := by
  let : Fintype G := Fintype.ofFinite G
  let f' : S → (G →* k) := fun s => (Units.coeHom k).comp (f s)
  have hf' : Function.Injective f' := by
    intro s t h
    apply hf
    apply MonoidHom.ext
    intro g
    exact Units.ext (DFunLike.congr_fun h g)
  exact ((linearIndependent_monoidHom G k).comp f' hf').finite

/-- A faithfully realised group of linear characters has finite block stabilisers. -/
theorem block_stabilizer_finite [Finite G] {C : Type w} [Group C]
    (linear : C →* (G →* kˣ)) (hinj : Function.Injective linear)
    [MulAction C (LiteralPrimitiveBlock k G)] (b : LiteralPrimitiveBlock k G) :
    Finite (MulAction.stabilizer C b) :=
  finite_of_injective_linear_characters (fun c : MulAction.stabilizer C b => linear c.1)
    (fun _ _ h => Subtype.ext (hinj h))

/-- Distinct field-valued linear characters are linearly independent,
so their number is bounded by the group order, in every characteristic. -/
theorem card_le_of_injective_linear_characters [Finite G] {S : Type w}
    (f : S → (G →* kˣ)) (hf : Function.Injective f) : Nat.card S ≤ Nat.card G := by
  let : Fintype G := Fintype.ofFinite G
  let f' : S → (G →* k) := fun s => (Units.coeHom k).comp (f s)
  have hf' : Function.Injective f' := by
    intro s t h
    apply hf
    apply MonoidHom.ext
    intro g
    exact Units.ext (DFunLike.congr_fun h g)
  have hlin := (linearIndependent_monoidHom G k).comp f' hf'
  let : Finite S := hlin.finite
  let : Fintype S := Fintype.ofFinite S
  simpa only [Nat.card_eq_fintype_card, Module.finrank_fintype_fun_eq_card] using
    hlin.fintype_card_le_finrank

/-- A family of distinct linear characters trivial on `N` and the centre
embeds into the character group of `G/NZ(G)`. -/
theorem card_le_center_quotient [Finite G] (N : Subgroup G) [N.Normal]
    {S : Type w} (linear : S → (G →* kˣ)) (hinj : Function.Injective linear)
    (hN : ∀ s, N ≤ (linear s).ker)
    (hZ : ∀ s, Subgroup.center G ≤ (linear s).ker) :
    Nat.card S ≤ Nat.card (G ⧸ (N ⊔ Subgroup.center G)) := by
  let descent s := descendCenterQuotient N (linear s) (hN s) (hZ s)
  apply card_le_of_injective_linear_characters descent
  intro s t h
  apply hinj
  apply MonoidHom.ext
  intro g
  exact DFunLike.congr_fun h (QuotientGroup.mk' _ g)

/-- The modular form of the general linear-block-stabiliser lemma, for
any faithfully realised group of quotient linear characters. The result
includes the actual factor character and the sharp elementary index bound.
Taking `C = linearCharactersTrivialOn N` gives all linear Brauer characters
of `G/N`, by the existing quotient character equivalence. -/
theorem modular_block_stabilizer_bound [Finite G] [CharP k p]
    [IsAlgClosed k] (hp : p.Prime) (N : Subgroup G) [N.Normal]
    {C : Type w} [Group C] (linear : C →* (G →* kˣ))
    (hinj : Function.Injective linear) (hN : ∀ c, N ≤ (linear c).ker)
    [MulAction C (LiteralPrimitiveBlock k G)]
    (source : SimpleBlockTensorSource linear) (b : LiteralPrimitiveBlock k G) :
    (∀ c : MulAction.stabilizer C b,
      ∃ lambdaQ : G ⧸ (N ⊔ Subgroup.center G) →* kˣ,
        lambdaQ.comp (QuotientGroup.mk' _) = linear c.1) ∧
    Nat.card (MulAction.stabilizer C b) ≤ Nat.card (G ⧸ (N ⊔ Subgroup.center G)) := by
  have hZ (c : MulAction.stabilizer C b) : Subgroup.center G ≤ (linear c.1).ker := by
    apply center_le_ker_of_regular_and_primary hp _
      (stabilizer_trivial_on_central_regular hp linear source b c)
    intro g n hn
    exact modular_character_trivial_on_p_element hp _ hn
  constructor
  · intro c
    exact ⟨descendCenterQuotient N (linear c.1) (hN c.1) (hZ c), by ext g; rfl⟩
  · apply card_le_center_quotient N (fun c : MulAction.stabilizer C b => linear c.1)
      (fun _ _ h => Subtype.ext (hinj h)) (fun c => hN c.1) hZ

end ModularRep.LinearBlockStabilizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
