import ModularRep.PaperProofs.TypeCOddPrimeConformalCriterionCarriers

/-!
# The odd-prime cover on the actual symplectic subgroup

The covering map is the existing Sp-to-PSp projection composed with the
inverse of the actual Sp-in-CSp range equivalence. Its inclusion square,
surjectivity and kernel are proved on these fixed maps. The independent
standard cover source retains the exact universal property on this map;
no new proof of the Schur multiplier or covering classification is claimed.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddPrimeSymplecticCover

open ModularRep
open OddTwoConformalProjectiveRealisation (Sp PSp spProjection)
open TypeCOddPrimeConformalCriterionCarriers (SpSubgroup spEquiv)
open EvenFieldFLZSourceConditions

variable (n : ℕ) (F : Type) [Field F]

/-- The simple target is the pre-existing literal whole-centre quotient of
the original matrix Sp. The map is fixed by the actual range equivalence. -/
def projection : SpSubgroup n F →* PSp n F :=
  (spProjection n F).comp (spEquiv n F).symm.toMonoidHom

@[simp] theorem projection_spEquiv (g : Sp n F) :
    projection n F (spEquiv n F g) = spProjection n F g := by
  simp [projection]

theorem projection_surjective : Function.Surjective (projection n F) := by
  intro y
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Sp n F)) y
  exact ⟨spEquiv n F g, (projection_spEquiv n F g).trans hg⟩

/-- The centre comparison uses the same range equivalence, with no
independently chosen centre or quotient identification. -/
theorem center_comap :
    (Subgroup.center (Sp n F)).comap (spEquiv n F).symm.toMonoidHom =
      Subgroup.center (SpSubgroup n F) := by
  ext g
  change (spEquiv n F).symm g ∈ Subgroup.center (Sp n F) ↔
    g ∈ Subgroup.center (SpSubgroup n F)
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h x
    apply (spEquiv n F).symm.injective
    simpa only [map_mul] using h ((spEquiv n F).symm x)
  · intro h x
    have hx := congrArg (spEquiv n F).symm (h (spEquiv n F x))
    simpa only [map_mul, MulEquiv.symm_apply_apply] using hx

theorem projection_kernel :
    (projection n F).ker = Subgroup.center (SpSubgroup n F) := by
  change ((spProjection n F).comp (spEquiv n F).symm.toMonoidHom).ker = _
  rw [← MonoidHom.comap_ker]
  change ((QuotientGroup.mk' (Subgroup.center (Sp n F))).ker).comap
    (spEquiv n F).symm.toMonoidHom = _
  rw [QuotientGroup.ker_mk']
  exact center_comap n F

variable [Finite F]

local instance subgroupFintype : Fintype (SpSubgroup n F) := Fintype.ofFinite _
local instance projectiveFintype : Fintype (PSp n F) := Fintype.ofFinite _

/-- Exact E1 structure/cover dictionary for rank at least three over an odd
finite field. Maximality is stated over the fixed projection, not merely
over an unspecified abstract group isomorphic to PSp. -/
structure CoverSource (ell : ℕ) : Prop where
  rank : 3 ≤ n
  field_odd : Odd (Nat.card F)
  perfect : commutator (SpSubgroup n F) = ⊤
  simple : IsSimpleGroup (PSp n F)
  nonabelian : ¬ IsMulCommutative (PSp n F)
  center_order : Nat.card (Subgroup.center (SpSubgroup n F)) = 2
  maximal : ∀ (D : Type) [Group D] [Fintype D] (f : D →* PSp n F),
    Function.Surjective f → f.ker ≤ Subgroup.center D →
      commutator D = ⊤ → ¬ ell ∣ Nat.card f.ker →
      ∃ lift : SpSubgroup n F →* D,
        Function.Surjective lift ∧ f.comp lift = projection n F

theorem center_primeTo {ell : ℕ} (hPrime : ell.Prime) (hOdd : Odd ell)
    (source : CoverSource n F ell) :
    ¬ ell ∣ Nat.card (Subgroup.center (SpSubgroup n F)) := by
  rw [source.center_order]
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
  · exact hPrime.ne_one h
  · subst ell
    norm_num at hOdd

/-- The criterion receives the actual Sp subgroup and actual old PSp
projection. Standard classification remains explicit E1 input. -/
def ellPrimeCover {ell : ℕ} (hPrime : ell.Prime) (hOdd : Odd ell)
    (source : CoverSource n F ell) : EllPrimeCoverSource ell (SpSubgroup n F) where
  S := PSp n F
  quotient := projection n F
  quotient_surjective := projection_surjective n F
  quotient_kernel := projection_kernel n F
  perfect := source.perfect
  simple := source.simple
  nonabelian := source.nonabelian
  centerPrimeTo := center_primeTo n F hPrime hOdd source
  maximal := source.maximal

end ModularRep.PaperProofs.TypeCOddPrimeSymplecticCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
