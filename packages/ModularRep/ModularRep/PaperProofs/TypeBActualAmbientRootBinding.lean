import ModularRep.PaperProofs.TypeBModularCommonRootBinding
import ModularRep.PaperProofs.TypeBSpinExtensionInstantiation
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Ordinary roots for the actual field semidirect product

The same complete modular system supplies every prime-to-ell root from
the algebraically closed residue field. A prescribed primitive root for
the ell-part of one actual finite group order then supplies all roots
for that order. The existing cyclotomic choice is retained throughout.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBActualAmbientRootBinding

open ModularRep TypeBModularCommonRootBinding

section General

universe uK uO uk

variable {ell m : ℕ} {K : Type uK} {O : Type uO} {k : Type uk}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [IsAlgClosed k] (Msys : ModularSystem ell K O k)

/-- All roots of positive prime-to-ell order come from the same residue map. -/
def primeToRoots (hm : 0 < m) (hc : m.Coprime ell) :
    HasEnoughRootsOfUnity K m := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero (m : k) :=
    ⟨TypeBModularRootReduction.residue_natCast_ne_zero Msys hc⟩
  exact (rootEquiv Msys hm hc).hasEnoughRootsOfUnity

/-- Only the ell-power part requires an additional ordinary root. -/
def enoughRoots_of_primePart (hm : 0 < m) (zeta : K)
    (primitive : IsPrimitiveRoot zeta (ell ^ m.factorization ell)) :
    HasEnoughRootsOfUnity K m := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI := primeToRoots Msys (Nat.ordCompl_pos ell hm.ne')
    (Nat.coprime_ordCompl Msys.prime hm.ne').symm
  obtain ⟨eta, heta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (ordCompl[ell] m)
  have hc : (ordProj[ell] m).Coprime (ordCompl[ell] m) :=
    (Nat.coprime_ordCompl Msys.prime hm.ne').pow_left _
  have hprimitive := primitive.pow_mul_pow_lcm heta
    (Nat.ordProj_pos m ell).ne' (Nat.ordCompl_pos ell hm.ne').ne'
  rw [hc.lcm_eq_mul, Nat.ordProj_mul_ordCompl_eq_self] at hprimitive
  exact ⟨⟨_, hprimitive⟩, rootsOfUnity.isCyclic K m⟩

end General

section Actual

open TypeBCliffordCarriers TypeBCriterionHypotheses

variable {n p f ell : ℕ} [NeZero f] {F K O k : Type}
  [Field F] [Finite F] [CharP F p] [Finite (Clifford n F)]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k]
  [Algebra O K] [IsAlgClosed k]
  {parameters : OddFieldParameters F p f}
  (N : NormSource n F) (fs : FieldActionSource n F p f parameters N)

/-- The displayed cyclic field group has exactly its defining degree. -/
theorem fieldGroup_card : Nat.card (FieldGroup f) = f := by
  simp only [FieldGroup, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-- The bound is the order of the actual semidirect-product carrier. -/
theorem ambient_card :
    Nat.card (Ambient fs.action) = Nat.card (SpecialClifford n F) * f := by
  change Nat.card (SpecialClifford n F ⋊[fs.action] FieldGroup f) = _
  rw [SemidirectProduct.card, fieldGroup_card]

/-- Its ell-part is the product of the two actual ell-parts. -/
theorem ambient_primePart :
    ell ^ (Nat.card (Ambient fs.action)).factorization ell =
      (ell ^ (Nat.card (SpecialClifford n F)).factorization ell) *
        (ell ^ f.factorization ell) := by
  rw [ambient_card N fs]
  exact Nat.ordProj_mul ell Nat.card_pos.ne' (NeZero.ne f)

/-- A literal primitive root for this ell-part supplies the exact guard
required by the checked four-extension construction. -/
def ambientRoots_of_primePart (Msys : ModularSystem ell K O k) (zeta : K)
    (primitive : IsPrimitiveRoot zeta
      (ell ^ (Nat.card (Ambient fs.action)).factorization ell)) :
    HasEnoughRootsOfUnity K (Nat.card (Ambient fs.action)) :=
  enoughRoots_of_primePart Msys Nat.card_pos zeta primitive

/-- When the field degree is prime to ell, the existing choice already
contains the required ell-part; all other roots are constructed by Hensel. -/
def ambientRoots_of_coprime_field (Msys : ModularSystem ell K O k)
    (choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K)
    (hf : ell.Coprime f) :
    HasEnoughRootsOfUnity K (Nat.card (Ambient fs.action)) := by
  let a := Nat.card (SpecialClifford n F)
  have ha : 0 < a := Nat.card_pos
  have hfpos : 0 < f := NeZero.pos f
  have hfactor : f.factorization ell = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (Msys.prime.coprime_iff_not_dvd.mp hf)
  have hdiv : ell ^ (a * f).factorization ell ∣ a := by
    simpa only [Nat.factorization_mul ha.ne' hfpos.ne', Finsupp.add_apply,
      hfactor, add_zero] using Nat.ordProj_dvd a ell
  letI := choice.ordinaryRoots
  letI : NeZero a := ⟨ha.ne'⟩
  letI : HasEnoughRootsOfUnity K (ell ^ (a * f).factorization ell) :=
    HasEnoughRootsOfUnity.of_dvd K hdiv
  obtain ⟨zeta, hprimitive⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K
    (ell ^ (a * f).factorization ell)
  have hroots := enoughRoots_of_primePart Msys (Nat.mul_pos ha hfpos) zeta hprimitive
  simpa only [ambient_card N fs] using hroots

end Actual

end ModularRep.PaperProofs.TypeBActualAmbientRootBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
