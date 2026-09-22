import ModularRep.PaperProofs.TypeBQ3PrincipalRadicalDecoding
import ModularRep.PaperProofs.TypeBQ3PrincipalExtensionAnchors

/-!
# Prescribed representatives with the same principal extension packet

An equality of weight classes supplies an inner conjugation to the prescribed
raw representative. The inflation graph moves by that same conjugation.
Conjugating the base embedding sends its radical back to the original local
ambient, so the existing extension characters, roots, and block catalogues
can be retained. The original projection and central-quotient equivalence
are separate fixed data. The action square records the required conjugation
of the automorphism coordinates.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalCriterionRepresentatives

open ModularRep CharacterWeight
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalExtensionAnchors
open TypeBQ3PrincipalExtensionApplication
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

variable {K Y : Type} [Field K] [CharZero K] [Group Y] [Finite Y]

local instance groupFintype (T : Type) [Group T] [Finite T] : Fintype T :=
  Fintype.ofFinite T

/-- Inner twisting retains the literal ambient weight class. -/
theorem classOf_inner_twist (U : CharacterWeight 2 K Y) (x : Y) :
    classOf (U.rightTwist (MulAut.conj x)) = classOf U := by
  have h := MulAction.orbitRel.Quotient.quotient_smul_eq
    (g := x⁻¹) (a := (Quotient.mk'' U : IsoClass (p := 2) (K := K) (G := Y)))
  change classOf (U.rightTwist (MulAut.conj ((x⁻¹)⁻¹))) = classOf U at h
  simpa only [inv_inv] using h

/-- Representative equality is derived from the orbit relation. -/
theorem exists_inner_twist_eq (U R : CharacterWeight 2 K Y)
    (sameClass : classOf U = classOf R) :
    ∃ x : Y, U.rightTwist (MulAut.conj x) = R := by
  have orbit : ∃ x : Y,
      x • (Quotient.mk'' U : IsoClass (p := 2) (K := K) (G := Y)) =
        Quotient.mk'' R := Quotient.exact sameClass.symm
  refine Exists.elim orbit ?_
  intro x hx
  refine ⟨x⁻¹, CharacterWeight.eq_of_isomorphic ?_⟩
  change (Quotient.mk'' (U.rightTwist (MulAut.conj x⁻¹)) :
    IsoClass (p := 2) (K := K) (G := Y)) = Quotient.mk'' R at hx
  exact @Quotient.exact _ (isomorphicSetoid (p := 2) (K := K) (G := Y)) _ _ hx

section GroupMaps

variable {H A : Type} [Group H] [Group A]

/-- A group homomorphism intertwines these two inner automorphisms. -/
theorem conjugation_square (q : Y →* H) (x y : Y) :
    q (MulAut.conj x y) = MulAut.conj (q x) (q y) := by
  change q (x * y * x⁻¹) = q x * q y * (q x)⁻¹
  calc
    q (x * y * x⁻¹) = q (x * y) * q (x⁻¹) := q.map_mul (x * y) x⁻¹
    _ = q x * q y * (q x)⁻¹ := by rw [q.map_mul x y, q.map_inv x]

/-- Only the base identification is conjugated; its target stays fixed. -/
def conjugatedEmbedding (i : H →* A) (g : H) : H →* A :=
  i.comp (MulAut.conj g).toMonoidHom

theorem conjugatedEmbedding_injective (i : H →* A) (hi : Function.Injective i)
    (g : H) : Function.Injective (conjugatedEmbedding i g) :=
  hi.comp (MulAut.conj g).injective

theorem conjugatedEmbedding_range (i : H →* A) (g : H) :
    (conjugatedEmbedding i g).range = i.range := by
  ext a
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨MulAut.conj g h, rfl⟩
  · rintro ⟨h, rfl⟩
    refine ⟨(MulAut.conj g).symm h, ?_⟩
    exact congrArg i ((MulAut.conj g).apply_symm_apply h)

theorem conjugatedEmbedding_projection_square (q : Y →* H) (i : H →* A)
    (x : Y) :
    (conjugatedEmbedding i (q x)).comp q =
      i.comp (q.comp (MulAut.conj x).toMonoidHom) := by
  ext y
  exact congrArg i (conjugation_square q x y).symm

/-- The old ambient action uses conjugated source coordinates for the new embedding. -/
theorem conjugatedEmbedding_action_square
    (i : H →* A) (g : H) (alpha : MulAut A) (beta : MulAut H)
    (square : ∀ h : H, alpha (i h) = i (beta h)) (h : H) :
    alpha (conjugatedEmbedding i g h) =
      conjugatedEmbedding i g
        (((MulAut.conj g)⁻¹ * beta * MulAut.conj g) h) := by
  change alpha (i (MulAut.conj g h)) =
    i (MulAut.conj g ((MulAut.conj g).symm (beta (MulAut.conj g h))))
  rw [MulEquiv.apply_symm_apply]
  exact square (MulAut.conj g h)

theorem conjugatedEmbedding_direct_radical_image
    (i : Y →* A) (U : CharacterWeight 2 K Y) (x : Y) :
    (U.rightTwist (MulAut.conj x)).subgroup.map (conjugatedEmbedding i x) =
      U.subgroup.map i := by
  change (U.subgroup.comap (MulAut.conj x).toMonoidHom).map
    (i.comp (MulAut.conj x).toMonoidHom) = U.subgroup.map i
  rw [← Subgroup.map_map,
    Subgroup.map_comap_eq_self_of_surjective (MulAut.conj x).surjective]

theorem conjugatedEmbedding_direct_normalizer
    (i : Y →* A) (U : CharacterWeight 2 K Y) (x : Y) :
    embeddedNormalizer (conjugatedEmbedding i x)
        (U.rightTwist (MulAut.conj x)).subgroup =
      embeddedNormalizer i U.subgroup := by
  unfold embeddedNormalizer
  rw [conjugatedEmbedding_direct_radical_image]

/-- The transported radical has the original image in the unchanged ambient group. -/
theorem conjugatedEmbedding_radical_image
    (q : Y →* H) (i : H →* A) (U : CharacterWeight 2 K Y)
    (V : Subgroup H) (hQ : U.subgroup.map q = V) (x : Y) :
    ((U.rightTwist (MulAut.conj x)).subgroup.map q).map
        (conjugatedEmbedding i (q x)) = V.map i := by
  rw [Subgroup.map_map, conjugatedEmbedding_projection_square]
  have hsource : (U.rightTwist (MulAut.conj x)).subgroup.map
      (MulAut.conj x).toMonoidHom = U.subgroup :=
    Subgroup.map_comap_eq_self_of_surjective (MulAut.conj x).surjective U.subgroup
  calc
    (U.rightTwist (MulAut.conj x)).subgroup.map
        (i.comp (q.comp (MulAut.conj x).toMonoidHom)) =
        (((U.rightTwist (MulAut.conj x)).subgroup.map
          (MulAut.conj x).toMonoidHom).map q).map i := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    _ = V.map i := by rw [hsource, hQ]

theorem conjugatedEmbedding_normalizer
    (q : Y →* H) (i : H →* A) (U : CharacterWeight 2 K Y)
    (V : Subgroup H) (hQ : U.subgroup.map q = V) (x : Y) :
    embeddedNormalizer (conjugatedEmbedding i (q x))
        ((U.rightTwist (MulAut.conj x)).subgroup.map q) =
      embeddedNormalizer i V := by
  unfold embeddedNormalizer
  rw [conjugatedEmbedding_radical_image q i U V hQ x]

end GroupMaps

variable (q : Y →* TypeBQ3TripleCoverCarrier.G3)

/-- The original graph is transported by the same inner element in both groups. -/
theorem rawInflates_inner_twist
    (U : CharacterWeight 2 K Y)
    (V : CharacterWeight 2 K TypeBQ3TripleCoverCarrier.G3)
    (inflates : RawInflates q U V) (x : Y) :
    RawInflates q (U.rightTwist (MulAut.conj x))
      (V.rightTwist (MulAut.conj (q x))) :=
  rawInflates_rightTwist q (MulAut.conj x) (MulAut.conj (q x))
    (conjugation_square q x) U V inflates

/-- An existing prescribed raw representative retains the same inflation graph. -/
theorem exists_prescribed_raw_pair
    (U R : CharacterWeight 2 K Y)
    (V : CharacterWeight 2 K TypeBQ3TripleCoverCarrier.G3)
    (inflates : RawInflates q U V) (sameClass : classOf U = classOf R) :
    ∃ x : Y,
      U.rightTwist (MulAut.conj x) = R ∧
      RawInflates q R (V.rightTwist (MulAut.conj (q x))) ∧
      classOf (V.rightTwist (MulAut.conj (q x))) = classOf V := by
  refine Exists.elim (exists_inner_twist_eq U R sameClass) ?_
  intro x hx
  refine ⟨x, hx, ?_, classOf_inner_twist V (q x)⟩
  rw [← hx]
  exact rawInflates_inner_twist q U V inflates x

/-- The prescribed local fibre supplies the exact raw representative and block guard. -/
theorem exists_prescribed_local_representative
    {k : Type} [Field k] [CharP k 2] [IsAlgClosed k]
    (SX : CoverWeightSource (k := k) (K := K) Y)
    (bX : LiteralPrimitiveBlock k Y)
    (Q : RadicalSubgroup (p := 2) (G := Y))
    (theta : RepresentativeDZ Nat.prime_two SX Q bX)
    (U : CharacterWeight 2 K Y)
    (V : CharacterWeight 2 K TypeBQ3TripleCoverCarrier.G3)
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Y))
    (upperClass : classOf U = w)
    (prescribedClass : classOf (characterWeightAt Nat.prime_two Q theta.val) = w)
    (inflates : RawInflates q U V) :
    SX.operations.rawWeightBlock (characterWeightAt Nat.prime_two Q theta.val) = bX ∧
    ∃ x : Y,
      U.rightTwist (MulAut.conj x) = characterWeightAt Nat.prime_two Q theta.val ∧
      RawInflates q (characterWeightAt Nat.prime_two Q theta.val)
        (V.rightTwist (MulAut.conj (q x))) ∧
      classOf (V.rightTwist (MulAut.conj (q x))) = classOf V :=
  ⟨theta.property, exists_prescribed_raw_pair q U
    (characterWeightAt Nat.prime_two Q theta.val) V inflates
    (upperClass.trans prescribedClass.symm)⟩

section Ranges

variable {H A : Type} [Group H] [Group A]

/-- The normalizer embedding has exactly the intersection with the global base. -/
theorem normalizerMap_range (i : H →* A) (hi : Function.Injective i)
    (Q : Subgroup H) :
    (ModularRep.normalizerMap i Q).range = embeddedLocalBase i Q := by
  ext n
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m.val, rfl⟩
  · intro hn
    refine Exists.elim ((normalizerBaseEquiv i hi Q).surjective ⟨n, hn⟩) ?_
    intro m hm
    exact ⟨m, congrArg Subtype.val hm⟩

end Ranges

section FixedPacket

variable {k : Type} [Field k] [CharP k 2] [IsAlgClosed k]
  (r : PrimeRegularRootEmbedding 2 k K TypeBQ3TripleCoverCarrier.G3)
  (phi : IBr r) (U : CharacterWeight 2 K Y)
  (V : CharacterWeight 2 K TypeBQ3TripleCoverCarrier.G3)
  (hQ : U.subgroup.map q = V.subgroup)

/-- The same local extension is evaluated after the explicit normalizer conjugation. -/
def twistedInflatedLocalMap (alpha : MulAut Y) :
    Subgroup.normalizer ((U.rightTwist alpha).subgroup : Set Y) →*
      embeddedNormalizer (innerEmbedding r phi) V.subgroup :=
  (inflatedLocalMap q r phi U V hQ).comp
    (rightNormalizerEquiv alpha U.subgroup).toMonoidHom

theorem twistedInflatedLocalMap_ambient (x : Y)
    (n : Subgroup.normalizer ((U.rightTwist (MulAut.conj x)).subgroup : Set Y)) :
    ((twistedInflatedLocalMap q r phi U V hQ (MulAut.conj x) n :
        embeddedNormalizer (innerEmbedding r phi) V.subgroup) :
          ActualAutAmbient r phi) =
      conjugatedEmbedding (innerEmbedding r phi) (q x) (q n.val) := by
  change innerEmbedding r phi (q (MulAut.conj x n.val)) =
    innerEmbedding r phi (MulAut.conj (q x) (q n.val))
  exact congrArg (innerEmbedding r phi) (conjugation_square q x n.val)

theorem fixed_local_value_after_twist
    (values : ∀ n : Subgroup.normalizer (U.subgroup : Set Y),
      U.localCharacter (QuotientGroup.mk n) =
        V.localCharacter (QuotientGroup.mk (normalizerImage q hQ n)))
    (reduction : CanonicalRawReduction r V)
    (hcenter : Subgroup.center TypeBQ3TripleCoverCarrier.G3 = ⊥)
    (packet : MatchedExtensionData r phi V reduction hcenter)
    (alpha : MulAut Y)
    (n : PrimeRegularElement
      (G := Subgroup.normalizer ((U.rightTwist alpha).subgroup : Set Y)) 2) :
    packet.localExtension.val.val
        (PrimeRegularElement.map (twistedInflatedLocalMap q r phi U V hQ alpha) n) =
      (U.rightTwist alpha).localCharacter (QuotientGroup.mk n.val) := by
  calc
    _ = U.localCharacter
        (QuotientGroup.mk (rightNormalizerEquiv alpha U.subgroup n.val)) :=
      local_value_inflated q r phi U V hQ values reduction hcenter packet
        (PrimeRegularElement.map (rightNormalizerEquiv alpha U.subgroup).toMonoidHom n)
    _ = _ := by
      exact congrArg
        (fun z : NormalizerQuotient U.subgroup => U.localCharacter.val z)
        (rightNormalizerQuotientEquiv_mk alpha U.subgroup n.val).symm

end FixedPacket

section DirectFixedPacket

variable {k : Type} [Field k] [CharP k 2] [IsAlgClosed k]
  (r : PrimeRegularRootEmbedding 2 k K Y) (phi : IBr r)
  (V : CharacterWeight 2 K Y)

/-- Direct representative transport evaluates the same old local extension. -/
def directTwistedLocalMap (alpha : MulAut Y) :
    Subgroup.normalizer ((V.rightTwist alpha).subgroup : Set Y) →*
      embeddedNormalizer (innerEmbedding r phi) V.subgroup :=
  (ModularRep.normalizerMap (innerEmbedding r phi) V.subgroup).comp
    (rightNormalizerEquiv alpha V.subgroup).toMonoidHom

theorem directTwistedLocalMap_ambient (x : Y)
    (n : Subgroup.normalizer ((V.rightTwist (MulAut.conj x)).subgroup : Set Y)) :
    ((directTwistedLocalMap r phi V (MulAut.conj x) n :
      embeddedNormalizer (innerEmbedding r phi) V.subgroup) : ActualAutAmbient r phi) =
        conjugatedEmbedding (innerEmbedding r phi) x n.val := rfl

theorem directTwistedLocalMap_range
    (hcenter : Subgroup.center Y = ⊥) (alpha : MulAut Y) :
    (directTwistedLocalMap r phi V alpha).range =
      embeddedLocalBase (innerEmbedding r phi) V.subgroup := by
  rw [← normalizerMap_range (innerEmbedding r phi)
    (innerEmbedding_injective r phi hcenter) V.subgroup]
  ext n
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨rightNormalizerEquiv alpha V.subgroup m, rfl⟩
  · rintro ⟨m, rfl⟩
    refine Exists.elim ((rightNormalizerEquiv alpha V.subgroup).surjective m) ?_
    intro a ha
    exact ⟨a, congrArg (ModularRep.normalizerMap (innerEmbedding r phi) V.subgroup) ha⟩

theorem fixed_direct_local_value_after_twist
    (reduction : CanonicalRawReduction r V)
    (hcenter : Subgroup.center Y = ⊥)
    (packet : MatchedExtensionData r phi V reduction hcenter)
    (alpha : MulAut Y)
    (n : PrimeRegularElement
      (G := Subgroup.normalizer ((V.rightTwist alpha).subgroup : Set Y)) 2) :
    packet.localExtension.val.val
        (PrimeRegularElement.map (directTwistedLocalMap r phi V alpha) n) =
      (V.rightTwist alpha).localCharacter (QuotientGroup.mk n.val) := by
  calc
    _ = V.localCharacter
        (QuotientGroup.mk (rightNormalizerEquiv alpha V.subgroup n.val)) :=
      local_value packet
        (PrimeRegularElement.map (rightNormalizerEquiv alpha V.subgroup).toMonoidHom n)
    _ = _ := by
      exact congrArg
        (fun z : NormalizerQuotient V.subgroup => V.localCharacter.val z)
        (rightNormalizerQuotientEquiv_mk alpha V.subgroup n.val).symm

theorem fixed_direct_global_value_after_conjugation
    (reduction : CanonicalRawReduction r V)
    (hcenter : Subgroup.center Y = ⊥)
    (packet : MatchedExtensionData r phi V reduction hcenter)
    (x : Y) (y : PrimeRegularElement (G := Y) 2) :
    packet.globalExtension.val.val
        (PrimeRegularElement.map (conjugatedEmbedding (innerEmbedding r phi) x) y) =
      phi.val y := by
  calc
    _ = phi.val (PrimeRegularElement.map (MulAut.conj x).toMonoidHom y) :=
      global_value packet (PrimeRegularElement.map (MulAut.conj x).toMonoidHom y)
    _ = phi.val y := phi.val.map_conj x y

end DirectFixedPacket

section GlobalValues

variable {A : Type} [Group A]

/-- Inner conjugation retains the original global value anchor. -/
theorem fixed_global_value_after_conjugation
    (i : TypeBQ3TripleCoverCarrier.G3 →* A)
    (globalCharacter : PrimeRegularClassFunction K A 2)
    (originalCharacter : PrimeRegularClassFunction K Y 2)
    (values : ∀ y : PrimeRegularElement (G := Y) 2,
      globalCharacter (PrimeRegularElement.map (i.comp q) y) = originalCharacter y)
    (x : Y) (y : PrimeRegularElement (G := Y) 2) :
    globalCharacter
        (PrimeRegularElement.map ((conjugatedEmbedding i (q x)).comp q) y) =
      originalCharacter y := by
  rw [conjugatedEmbedding_projection_square]
  calc
    _ = originalCharacter (PrimeRegularElement.map (MulAut.conj x).toMonoidHom y) :=
      values (PrimeRegularElement.map (MulAut.conj x).toMonoidHom y)
    _ = originalCharacter y := originalCharacter.map_conj x y

end GlobalValues

end ModularRep.PaperProofs.TypeBQ3PrincipalCriterionRepresentatives


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
