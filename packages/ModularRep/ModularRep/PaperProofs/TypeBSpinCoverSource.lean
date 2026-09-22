import ModularRep.PaperProofs.TypeBCliffordCarriers
import ModularRep.PaperProofs.EvenFieldFLZSourceConditions

/-!
# The generic Type B cover on a fixed quotient map

This E1 boundary fixes the simple group to Spin modulo its actual centre.
Malle--Testerman, Tables 24.2--24.3 and Remark 24.19, pp. 211--214,
identify this group with Omega and its universal cover with Spin outside
(n,q)=(3,3). At odd ell the centre of order two survives in the maximal
ell-prime cover. The maximality field is the literal quotient universal
property of the published cover, not a representation theoretic target.

The exceptional full cover 6.Omega_7(3) is outside this packet's scope.
No goodness, iBAW, or character-weight correspondence occurs here.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBSpinCoverSource

open TypeBCliffordCarriers EvenFieldFLZSourceConditions

variable {n p f ell : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
variable (N : NormSource n F) [Finite (Spin n F N)]

/-- The simple-group carrier is fixed before any source theorem is used. -/
abbrev Omega := Spin n F N ⧸ Subgroup.center (Spin n F N)

local instance : Fintype (Spin n F N) := Fintype.ofFinite _
local instance : Fintype (Omega N) := Fintype.ofFinite _

/-- Source-sized generic covering facts on the actual Spin quotient.
The source maximality clause uses finite perfect central ell-prime
extensions of this same quotient, exactly as the reusable cover carrier.
Its algebraic and published-source identification remains explicit E1/U.
-/
structure GenericSpinCoverSource where
  fieldParameters : OddFieldParameters F p f
  rank : 3 ≤ n
  generic : (n, Nat.card F) ≠ (3, 3)
  perfect : commutator (Spin n F N) = ⊤
  simple : IsSimpleGroup (Omega N)
  nonabelian : ¬ IsMulCommutative (Omega N)
  centreOrder : Nat.card (Subgroup.center (Spin n F N)) = 2
  maximal : ∀ (D : Type) [Group D] [Fintype D] (r : D →* Omega N),
    Function.Surjective r → r.ker ≤ Subgroup.center D →
      commutator D = ⊤ → ¬ ell ∣ Nat.card r.ker →
      ∃ lift : Spin n F N →* D, Function.Surjective lift ∧
        r.comp lift = QuotientGroup.mk' (Subgroup.center (Spin n F N))

/-- Bind the existing literal universal ell-prime-cover carrier. Its
simple group, quotient map and kernel are fixed definitions; prime-to-ell
of the actual centre follows from the supplied source order and oddness.
-/
def genericSpinEllPrimeCover
    (hEll : Nat.Prime ell) (hOdd : Odd ell)
    (source : GenericSpinCoverSource (p := p) (f := f) (ell := ell) N) :
    EllPrimeCoverSource ell (Spin n F N) where
  S := Omega N
  quotient := QuotientGroup.mk' (Subgroup.center (Spin n F N))
  quotient_surjective := QuotientGroup.mk'_surjective _
  quotient_kernel := QuotientGroup.ker_mk' _
  perfect := source.perfect
  simple := source.simple
  nonabelian := source.nonabelian
  centerPrimeTo := by
    rw [source.centreOrder]
    exact hEll.coprime_iff_not_dvd.mp hOdd.coprime_two_right
  maximal := source.maximal

end ModularRep.PaperProofs.TypeBSpinCoverSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
