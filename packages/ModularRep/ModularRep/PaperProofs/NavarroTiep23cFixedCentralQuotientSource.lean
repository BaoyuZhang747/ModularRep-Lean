import ModularRep.NormalCoreTransport

/-!
# Navarro--Tiep (2.3(c)) for one central prime-to-`ell` quotient

This experimental module records the two literal group-theoretic outputs of
Navarro--Tiep, Lemma 2.3(c), needed at one supplied radical subgroup: the
radicality of its image and the exact image of its normaliser.  The prime
hypothesis, centrality, prime-to-`ell` order, and original radicality are
indices of the packet, not stored output fields.

The restricted normaliser map is the existing `normalizerMap`.  Its
surjectivity is proved from the supplied normaliser-image equality.  The
proof does not assume `ker (QuotientGroup.mk' Z0) ≤ Q`; that containment is
generally false for a nontrivial central `ell'` kernel and an `ell`-subgroup.

No declaration here concerns characters, representations, blocks, block
induction, normaliser quotients, BAW, iBAW, or Lemma 5.2.
-/

namespace ModularRep

universe u v w

/-- The exact fixed-`Q` E1/U outputs of Navarro--Tiep, Lemma 2.3(c), on the
literal central quotient carrier.  The ordered field inventory is exactly
`radical_image; normalizer_image`. -/
structure NavarroTiep23cFixedCentralQuotientSource
    {ell : Nat} {X : Type u} [Group X] [Finite X] [Fact ell.Prime]
    (Z0 : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X)
    (hZ0PrimeTo : ¬ ell ∣ Nat.card Z0)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup ell Q) : Prop where
  radical_image :
    IsRadicalSubgroup ell (Q.map (QuotientGroup.mk' Z0))
  normalizer_image :
    (Subgroup.normalizer (Q : Set X)).map (QuotientGroup.mk' Z0) =
      Subgroup.normalizer
        ((Q.map (QuotientGroup.mk' Z0) : Subgroup (X ⧸ Z0)) :
          Set (X ⧸ Z0))

/-- An exact normaliser-image equality makes the existing restricted
normaliser map surjective.  No kernel-containment hypothesis is used. -/
private theorem normalizerMap_surjective_of_map_eq
    {G : Type v} {H : Type w} [Group G] [Group H]
    (f : G →* H) (Q : Subgroup G)
    (hmap :
      (Subgroup.normalizer (Q : Set G)).map f =
        Subgroup.normalizer
          ((Q.map f : Subgroup H) : Set H)) :
    Function.Surjective (normalizerMap f Q) := by
  intro y
  have hy : (y : H) ∈
      (Subgroup.normalizer (Q : Set G)).map f := by
    rw [hmap]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The canonical central quotient restricts surjectively to the two literal
normalisers once the Navarro--Tiep image equality is supplied. -/
theorem centralQuotientNormalizerMap_surjective
    {ell : Nat} {X : Type u} [Group X] [Finite X] [Fact ell.Prime]
    (Z0 : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X)
    (hZ0PrimeTo : ¬ ell ∣ Nat.card Z0)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup ell Q)
    (S : NavarroTiep23cFixedCentralQuotientSource
      Z0 hZ0central hZ0PrimeTo Q hQ) :
    Function.Surjective
      (normalizerMap (QuotientGroup.mk' Z0) Q) :=
  normalizerMap_surjective_of_map_eq
    (QuotientGroup.mk' Z0) Q S.normalizer_image

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
