import ModularRep.PaperProofs.EvenFieldFLZSourceConditions
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource
import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Removing a two-group kernel from the universal central cover

If a nonabelian simple group has a full universal central extension whose
kernel is a two-group, its identity map is its universal prime-to-two cover.
The proof constructs the required quotient onto every finite perfect central
extension with odd kernel. It does not assume that the simple group is its
own *full* universal central cover.

The literal application uses Sp_(2n)(F) and its quotient by its actual centre.
The E1 source packet retains the full universal property of that projection,
the order-two centre, and simplicity and noncommutativity of the quotient.
No prime-to-two-cover conclusion or iBAW predicate is stored in the packet.

Source scope: `SF-PERFECT-SIMPLE` is Malle--Testerman, Theorem 24.17 and
Remark 24.18, pp. 212--213. `SF-COVERS` is Tables 24.2--24.3 and Remark 24.19,
pp. 211--214; the full-cover universal property also uses
`SF-UNIVERSAL-ELLPRIME-COVER`, with Gorenstein, Propositions 4.227--4.228,
p. 298. At odd field order and rank at least two, the pair (n,q) = (2,3)
is included: Malle--Testerman, Remark 24.9, p. 209 identifies PSp_4(3) with
PSU_4(2), and Table 24.3 gives its order-two multiplier. The exceptional
isomorphism alone does not identify a universal covering map.

The cover argument is a kernel-checked instance of the routine E1 quotient
construction in `SF-UNIVERSAL-ELLPRIME-COVER`, not new manuscript-specific
proof credit. Realising the source facts on these matrix carriers remains
E1/U. The original iBAW target and the Feng--Malle Proposition 3.4 passage
are not asserted here.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover

open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- A homomorphism from a two-group to a group of odd cardinality is trivial.
The domain need not be finite. -/
theorem hom_eq_one_of_twoGroup_of_odd_card
    {A B : Type u} [Group A] [Group B]
    (hA : IsPGroup 2 A) (hB : ¬ 2 ∣ Nat.card B)
    (f : A →* B) (a : A) : f a = 1 := by
  obtain ⟨k, hk⟩ := hA.exists_orderOf_dvd_pow a
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hB).symm.pow_right k)
    (orderOf_dvd_natCard (f a)) ((orderOf_map_dvd f a).trans hk)

/-- The full universal property descends through its two-group kernel to a
section of every central extension with odd kernel. Perfectness of the total
extension makes that section surjective. -/
theorem exists_surjective_section_of_fullCover_twoKernel
    {U S D : Type u} [Group U] [Group S] [Group D]
    (cover : U →* S)
    (hcover : IsUniversalCentralExtension cover)
    (hkernel : IsPGroup 2 cover.ker)
    (f : D →* S) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center D)
    (hperfect : commutator D = ⊤)
    (hodd : ¬ 2 ∣ Nat.card f.ker) :
    ∃ s : S →* D,
      Function.Surjective s ∧ f.comp s = MonoidHom.id S := by
  obtain ⟨lift, hlift, _⟩ := hcover.2 D f ⟨hsurjective, hcentral⟩
  let kernelLift : cover.ker →* f.ker :=
    { toFun := fun x => ⟨lift x, by
        change f (lift x.1) = 1
        exact (DFunLike.congr_fun hlift x.1).trans x.property⟩
      map_one' := by
        apply Subtype.ext
        exact lift.map_one
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact lift.map_mul a b }
  have hdescend : cover.ker ≤ lift.ker := by
    intro x hx
    change lift x = 1
    exact congrArg Subtype.val
      (hom_eq_one_of_twoGroup_of_odd_card hkernel hodd kernelLift ⟨x, hx⟩)
  let quotientLift : U ⧸ cover.ker →* D :=
    QuotientGroup.lift cover.ker lift hdescend
  let quotientEquiv : U ⧸ cover.ker ≃* S :=
    QuotientGroup.quotientKerEquivOfSurjective cover hcover.1.1
  let s : S →* D := quotientLift.comp quotientEquiv.symm.toMonoidHom
  have hsection : f.comp s = MonoidHom.id S := by
    ext y
    obtain ⟨x, rfl⟩ := hcover.1.1 y
    have he : quotientEquiv (QuotientGroup.mk x) = cover x := rfl
    have hes : quotientEquiv.symm (cover x) = QuotientGroup.mk x := by
      rw [← he, quotientEquiv.symm_apply_apply]
    change f (quotientLift (quotientEquiv.symm (cover x))) = cover x
    rw [hes]
    change f (lift x) = cover x
    exact DFunLike.congr_fun hlift x
  exact ⟨s,
    centralExtension_section_surjective f hcentral s hsection hperfect,
    hsection⟩

/-- A nonabelian simple group is perfect. -/
theorem perfect_of_nonabelian_simple
    {S : Type u} [Group S] (hsimple : IsSimpleGroup S)
    (hnonabelian : ¬ IsMulCommutative S) : commutator S = ⊤ := by
  letI : IsSimpleGroup S := hsimple
  have hnormal : (commutator S).Normal := inferInstance
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exact (hnonabelian ((commutator_eq_bot_iff _).mp h)).elim
  · exact h

/-- A nonabelian simple group has trivial centre. -/
theorem center_eq_bot_of_nonabelian_simple
    {S : Type u} [Group S] (hsimple : IsSimpleGroup S)
    (hnonabelian : ¬ IsMulCommutative S) : Subgroup.center S = ⊥ := by
  letI : IsSimpleGroup S := hsimple
  have hnormal : (Subgroup.center S).Normal := inferInstance
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exact h
  · exact (hnonabelian (Subgroup.center_eq_top_iff.mp h)).elim

/-- The identity prime-to-two cover is derived from the full cover and its
two-group kernel. The maximality clause quantifies over the actual finite
perfect central extensions, as required by `EllPrimeCoverSource`. -/
def identityEllPrimeCover_of_fullCover_twoKernel
    {U S : Type u} [Group U] [Group S] [Fintype S]
    (cover : U →* S)
    (hcover : IsUniversalCentralExtension cover)
    (hkernel : IsPGroup 2 cover.ker)
    (hsimple : IsSimpleGroup S)
    (hnonabelian : ¬ IsMulCommutative S) : EllPrimeCoverSource 2 S where
  S := S
  groupS := inferInstance
  fintypeS := inferInstance
  quotient := MonoidHom.id S
  quotient_surjective := Function.surjective_id
  quotient_kernel := by
    simpa [center_eq_bot_of_nonabelian_simple hsimple hnonabelian]
  perfect := perfect_of_nonabelian_simple hsimple hnonabelian
  simple := hsimple
  nonabelian := hnonabelian
  centerPrimeTo := by
    simpa [center_eq_bot_of_nonabelian_simple hsimple hnonabelian] using
      Nat.prime_two.not_dvd_one
  maximal := by
    intro D _ _ f hsurjective hcentral hperfect hodd
    exact exists_surjective_section_of_fullCover_twoKernel
      cover hcover hkernel f hsurjective hcentral hperfect hodd

/-- The literal symplectic matrix group. -/
abbrev LiteralSp (n : ℕ) (F : Type u) [Field F] :=
  Matrix.symplecticGroup (Fin n) F

/-- The literal projective symplectic group. -/
abbrev LiteralPSp (n : ℕ) (F : Type u) [Field F] :=
  LiteralSp n F ⧸ Subgroup.center (LiteralSp n F)

/-- The fixed projection, rather than an independently selected covering map. -/
def literalProjection (n : ℕ) (F : Type u) [Field F] :
    LiteralSp n F →* LiteralPSp n F :=
  QuotientGroup.mk' (Subgroup.center (LiteralSp n F))

noncomputable instance literalPSpFintype
    (n : ℕ) (F : Type u) [Field F] [Finite F] :
    Fintype (LiteralPSp n F) := Fintype.ofFinite _

/-- Exact E1 full-cover facts on the odd-field matrix carriers. The field order
is `Nat.card F`. The exceptional isomorphism at `(n, Nat.card F) = (2,3)`
is inside this scope and requires the multiplier entry described above.

These fields do not assume a prime-to-two self-cover or any iBAW conclusion.
In particular, `fullCover` is the universal property of the displayed Sp to
PSp map, not the false assertion that odd-field PSp is its own full cover. -/
structure OddSymplecticFullCoverSource
    (n : ℕ) (F : Type u) [Field F] [Finite F] : Prop where
  rank_ge_two : 2 ≤ n
  field_odd : Odd (Nat.card F)
  fullCover : IsUniversalCentralExtension (literalProjection n F)
  center_card : Nat.card (Subgroup.center (LiteralSp n F)) = 2
  simple : IsSimpleGroup (LiteralPSp n F)
  nonabelian : ¬ IsMulCommutative (LiteralPSp n F)

/-- The actual projection kernel is a two-group, by the supplied centre order. -/
theorem OddSymplecticFullCoverSource.projection_twoKernel
    {n : ℕ} {F : Type u} [Field F] [Finite F]
    (source : OddSymplecticFullCoverSource n F) :
    IsPGroup 2 (literalProjection n F).ker := by
  apply IsPGroup.of_card (n := 1)
  simpa [literalProjection, QuotientGroup.ker_mk'] using source.center_card

/-- The canonical universal prime-to-two cover is the identity of the literal
PSp group. This constructs its maximality and does not conclude iBAW. -/
def OddSymplecticFullCoverSource.identityEllPrimeCover
    {n : ℕ} {F : Type u} [Field F] [Finite F]
    (source : OddSymplecticFullCoverSource n F) :
    EllPrimeCoverSource 2 (LiteralPSp n F) :=
  identityEllPrimeCover_of_fullCover_twoKernel (literalProjection n F)
    source.fullCover source.projection_twoKernel source.simple source.nonabelian

/-- The derived cover has precisely the displayed projective simple quotient. -/
theorem OddSymplecticFullCoverSource.identityEllPrimeCover_simpleGroup
    {n : ℕ} {F : Type u} [Field F] [Finite F]
    (source : OddSymplecticFullCoverSource n F) :
    source.identityEllPrimeCover.S = LiteralPSp n F := rfl

/-- The derived covering map is literally the identity. -/
theorem OddSymplecticFullCoverSource.identityEllPrimeCover_quotient
    {n : ℕ} {F : Type u} [Field F] [Finite F]
    (source : OddSymplecticFullCoverSource n F) :
    source.identityEllPrimeCover.quotient = MonoidHom.id (LiteralPSp n F) := rfl

end ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
