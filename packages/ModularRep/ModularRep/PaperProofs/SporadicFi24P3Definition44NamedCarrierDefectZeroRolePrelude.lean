import ModularRep.SemisimpleBlockSimpleClass
import Mathlib.RepresentationTheory.Maschke
import Mathlib.SetTheory.Cardinal.Finite
import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual
import ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow
import Mathlib.RepresentationTheory.Character
import Mathlib.Data.Nat.Factorization.Basic

/-! A nonsingleton Brauer block forces modular characteristic to divide the
group order. In that case a defect-zero ordinary reduction is nontrivial. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDefectZeroRolePrelude
open ModularRep ModularRep.FDRepSimpleClassKZero

universe u v w

theorem prime_dvd_card_of_ibrBlock_card_ne_one
    {p : ℕ} {k G : Type u} {K : Type v} {Block : Type w}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Fintype Block]
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {e : Block → k[G]} (blocks : BlockIdempotentDecomposition e)
    (b : Block)
    (hcard : Nat.card (IBrBlock iota hinj blocks b) ≠ 1) :
    p ∣ Nat.card G := by
  by_contra hp
  let : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hp
  obtain ⟨X, hX, hunique⟩ :=
    existsUnique_simpleModuleClassBlock_of_isSemisimpleRing
      (inferInstance : IsSemisimpleRing k[G]) blocks b
  have hc : Nat.card (SimpleModuleClassBlock blocks b) = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨⟨?_⟩, ⟨⟨X, hX⟩⟩⟩
    intro Y Z
    exact Subtype.ext ((hunique Y.val Y.property).trans
      (hunique Z.val Z.property).symm)
  exact hcard ((Nat.card_congr
    (simpleModuleClassBlockEquivIBrBlock iota hinj blocks b).symm).trans hc)

theorem ordinary_defect_zero_apply_one_ne_one_of_dvd_card
    {p : ℕ} {K G : Type u}
    [Field K] [CharZero K] [Group G] [Finite G]
    (hp : p.Prime) (hpG : p ∣ Nat.card G)
    (chi : OrdinaryIrreducibleCharacter.Irr K G)
    (hchi : ModularRep.IsDefectZeroOrdinaryCharacter p chi) :
    chi (1 : G) ≠ 1 := by
  intro h1
  obtain ⟨V, _hV, hchar, hdef⟩ := hchi
  have hdimK : (Module.finrank K V : K) = 1 :=
    (FDRep.char_one V).symm.trans ((congrFun hchar 1).trans h1)
  have hdim : Module.finrank K V = 1 :=
    (Nat.cast_eq_one (R := K)).mp hdimK
  have hpart : ordProj[p] (Nat.card G) = 1 := by
    change ordProj[p] (Module.finrank K V) =
      ordProj[p] (Nat.card G) at hdef
    rw [hdim] at hdef
    simpa using hdef.symm
  have hdiv := Nat.dvd_ordProj_of_dvd
    (show Nat.card G ≠ 0 from Nat.card_pos.ne') hp hpG
  rw [hpart] at hdiv
  exact hp.not_dvd_one hdiv

open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource GlobalDefectZeroCharacter)

theorem reduction_ne_trivial_of_dvd_card
    {p : ℕ} {k K G : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G]
    (iota : PrimeRegularRootEmbedding p k K G)
    (D : DefectZeroReductionSource iota)
    (hpG : p ∣ Nat.card G)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G)) :
    D.reduce (iota := iota) d ≠
      SporadicFi24P3Definition44Clause3ACWindow.trivialIBr iota := by
  intro h
  have h1 : d.1 (1 : G) = 1 := by
    let g : PrimeRegularElement (G := G) p := ⟨1, isPrimeRegular_one⟩
    exact (D.reduce_isReduction (iota := iota) d g).trans
      ((congrArg (fun phi : IBr iota => phi.val g) h).trans
        (SporadicFi24P3Definition44Clause3ACWindow.trivialIBr_apply iota g))
  exact ordinary_defect_zero_apply_one_ne_one_of_dvd_card
    iota.prime hpG d.1 d.2 h1

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDefectZeroRolePrelude


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
