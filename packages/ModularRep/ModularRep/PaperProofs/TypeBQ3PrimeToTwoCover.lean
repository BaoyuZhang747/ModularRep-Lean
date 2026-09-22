import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier

/-!
# Prime-to-two maximality of the fixed triple cover

The accepted full projection maps to every central extension of the same
matrix `G3`. Its intrinsic central subgroup of order two maps trivially into
an odd kernel, so this map factors through the existing literal `X`. The
checked perfect-target surjectivity lemma makes the factor surjective.

This is the supporting quotient construction described by
`SF-UNIVERSAL-ELLPRIME-COVER`, not a new manuscript theorem acceptance. The
matrix and free-presentation source realizations remain inherited. No new
external source or representation theoretic input is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrimeToTwoCover

open TypeBQ3TripleCoverCarrier
open EvenFieldFLZSourceConditions

variable (source : MatrixExceptionalSource)
variable (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

include source freeSource in
/-- A map over the full projection kills the removed subgroup when its image
lies in the kernel of an extension of odd kernel order. -/
theorem centralTwoSubgroup_le_lift_kernel
    {D : Type} [Group D] (f : D →* G3)
    (hodd : ¬ 2 ∣ Nat.card f.ker)
    (lift : FullCover →* D) (hlift : f.comp lift = fullProjection) :
    centralTwoSubgroup ≤ lift.ker := by
  intro x hx
  have image : lift x ∈ f.ker := by
    change f (lift x) = 1
    exact (DFunLike.congr_fun hlift x).trans
      (centralTwoSubgroup_le_kernel source freeSource hx)
  have order_two : orderOf x ∣ 2 := by
    simpa only [centralTwoSubgroup_card source freeSource] using
      (Subgroup.orderOf_dvd_natCard centralTwoSubgroup hx)
  change lift x = 1
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes
    (Nat.prime_two.coprime_iff_not_dvd.mpr hodd)
    ((orderOf_map_dvd lift x).trans order_two)
    (Subgroup.orderOf_dvd_natCard f.ker image)

/-- Every finite perfect central extension with odd kernel receives a
surjection from this exact `X`, commuting with the accepted projection. -/
theorem maximal (D : Type) [Group D] [Fintype D] (f : D →* G3)
    (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center D)
    (hperfect : commutator D = ⊤)
    (hodd : ¬ 2 ∣ Nat.card f.ker) :
    ∃ lift : X →* D,
      Function.Surjective lift ∧ f.comp lift = q source freeSource := by
  obtain ⟨fullLift, hlift, _⟩ :=
    (fullProjection_universal source freeSource).2 D f ⟨hsurjective, hcentral⟩
  let lift : X →* D :=
    QuotientGroup.lift centralTwoSubgroup fullLift
      (centralTwoSubgroup_le_lift_kernel source freeSource f hodd fullLift hlift)
  have square : f.comp lift = q source freeSource := by
    apply MonoidHom.ext
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective centralTwoSubgroup x
    change f (fullLift u) = fullProjection u
    exact DFunLike.congr_fun hlift u
  exact ⟨lift,
    TypeBExceptionalCanonicalCover.lift_surjective_of_perfect
      (q source freeSource) (q_surjective source freeSource)
      f hcentral hperfect lift square,
    square⟩

/-- The exact prime-to-two cover structure, with computed finite enumeration
and the same quotient group and projection as the principal correspondence. -/
def ellPrimeCover :
    letI : Fintype X := fintype_X source
    EllPrimeCoverSource 2 X := by
  letI : Fintype X := fintype_X source
  exact
    { S := G3
      groupS := inferInstance
      fintypeS := Fintype.ofFinite G3
      quotient := q source freeSource
      quotient_surjective := q_surjective source freeSource
      quotient_kernel := q_kernel_eq_center source freeSource
      perfect := perfect_X source freeSource
      simple := source.simple
      nonabelian := source.nonabelian
      centerPrimeTo := by
        rw [← q_kernel_eq_center source freeSource]
        exact q_kernel_primeToTwo source freeSource
      maximal := by
        intro D _ _ f hsurjective hcentral hperfect hodd
        exact maximal source freeSource D f hsurjective hcentral hperfect hodd }

end ModularRep.PaperProofs.TypeBQ3PrimeToTwoCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
