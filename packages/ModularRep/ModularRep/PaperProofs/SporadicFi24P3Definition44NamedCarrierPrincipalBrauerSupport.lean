import ModularRep.GroupAlgebraCentralBrauerMap
import ModularRep.BlockCentralBrauerImage
import ModularRep.IBrBlockEquivTransport
import ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction
import Mathlib.GroupTheory.Sylow

/-! The trivial Brauer character's block has nonzero central Brauer support
at every p-subgroup. Conjugation-orbit cancellation preserves augmentation. -/

noncomputable section
open scoped MonoidAlgebra BigOperators
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrincipalBrauerSupport

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44Clause3ACWindow
  (trivialIBr trivialIBr_apply trivial_rep_irreducible)
open SporadicFi24P3Definition44NamedCarrierBrauerBlockAction

local instance subgroupFintype {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) : Fintype P := Fintype.ofFinite _

section Coefficients
variable {p : ℕ} {k G : Type*}
variable [Field k] [CharP k p] [Fact p.Prime] [Group G] [Fintype G]

theorem sum_coeff_centralBrauerRestriction
    (P : Subgroup G) (hP : IsPGroup p P) (z : GroupAlgebraCenter k G) :
    (∑ g : G, (z : k[G]).coeff g) =
      ∑ c : centralizerOf P,
        ((centralBrauerRestriction P z : GroupAlgebraCenter k (centralizerOf P)) :
          k[centralizerOf P]).coeff c := by
  classical
  let _ : MulAction P G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp P.subtype)
  let _ : Fintype (MulAction.fixedPoints P G) := Fintype.ofFinite _
  have hfixed : MulAction.fixedPoints P G = (centralizerOf P : Set G) := by
    ext x
    change (∀ q : P, (q : G) * x * (q : G)⁻¹ = x) ↔
      ∀ g : G, g ∈ (P : Set G) → g * x = x * g
    constructor
    · intro hx g hg
      exact mul_inv_eq_iff_eq_mul.mp (hx ⟨g, hg⟩)
    · intro hx q
      exact mul_inv_eq_iff_eq_mul.mpr (hx q q.property)
  have hf : ∀ q : P, ∀ g : G,
      (z : k[G]).coeff (q • g) = (z : k[G]).coeff g := by
    intro q g
    exact GroupAlgebraCenter.coeff_conjugate z (q : G) g
  let eFixed : MulAction.fixedPoints P G ≃ centralizerOf P := Equiv.setCongr hfixed
  calc
    (∑ g : G, (z : k[G]).coeff g) =
        ∑ g : MulAction.fixedPoints P G, (z : k[G]).coeff (g : G) :=
      IsPGroup.sum_eq_sum_fixedPoints_of_invariant hP (fun g => (z : k[G]).coeff g) hf
    _ = ∑ c : centralizerOf P, (z : k[G]).coeff (c : G) :=
      Fintype.sum_equiv eFixed
        (fun g : MulAction.fixedPoints P G => (z : k[G]).coeff (g : G))
        (fun c : centralizerOf P => (z : k[G]).coeff (c : G)) (fun _ => rfl)
    _ = _ := rfl

theorem centralBrauerRestriction_ne_zero_of_sum_coeff_ne_zero
    (P : Subgroup G) (hP : IsPGroup p P) (z : GroupAlgebraCenter k G)
    (haug : (∑ g : G, (z : k[G]).coeff g) ≠ 0) :
    centralBrauerRestriction P z ≠ 0 := by
  intro hz
  apply haug
  rw [sum_coeff_centralBrauerRestriction P hP z, hz]
  simp

end Coefficients

universe u
variable {p : ℕ} {k K G I : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype I]
variable {e : I → k[G]}

theorem trivialBlock_sum_coeff
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition e) :
    (∑ g : G, (e (irreducibleBrauerCharacterBlock iota hinj blocks
      (trivialIBr iota))).coeff g) = 1 := by
  classical
  let rho : Representation k G k := Representation.trivial k G k
  let V : FDRep k G := FDRep.of rho
  have hV : Representation.IsIrreducible V.ρ := trivial_rep_irreducible
  have hs := block_smul_of_affording iota hinj blocks (trivialIBr iota)
    V hV rfl
  change ∀ v : rho.asModule,
    e (irreducibleBrauerCharacterBlock iota hinj blocks (trivialIBr iota)) • v = v at hs
  have ha := congrArg rho.asModuleEquiv (hs (rho.asModuleEquiv.symm (1 : k)))
  have hact : rho.asAlgebraHom
      (e (irreducibleBrauerCharacterBlock iota hinj blocks (trivialIBr iota)))
      (1 : k) = 1 := by
    simpa only [Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply] using ha
  have hsum (x : k[G]) :
      rho.asAlgebraHom x (1 : k) = ∑ g : G, x.coeff g := by
    change (Representation.trivial k G k).asAlgebraHom x (1 : k) = _
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
    simp only [LinearMap.finsupp_sum_apply, LinearMap.smul_apply,
      Representation.trivial_apply, smul_eq_mul, mul_one]
    exact Finsupp.sum_fintype _ _ (fun _ => rfl)
  exact (hsum _).symm.trans hact

theorem trivialBlock_hasNonzeroCentralBrauerRestriction
    [Fact p.Prime]
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition e)
    (P : Subgroup G) (hP : IsPGroup p P) :
    HasNonzeroCentralBrauerRestriction blocks
      (irreducibleBrauerCharacterBlock iota hinj blocks (trivialIBr iota)) P := by
  apply centralBrauerRestriction_ne_zero_of_sum_coeff_ne_zero P hP
  change (∑ g : G, (e (irreducibleBrauerCharacterBlock iota hinj blocks
    (trivialIBr iota))).coeff g) ≠ 0
  rw [trivialBlock_sum_coeff iota hinj blocks]
  exact one_ne_zero

theorem trivialBlock_ne_of_defect_bot
    [Fact p.Prime]
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition e) (b : I)
    (hpG : p ∣ Nat.card G)
    (hDefect : IsMaximalCentralBrauerDefect (p := p) blocks b (⊥ : Subgroup G)) :
    irreducibleBrauerCharacterBlock iota hinj blocks (trivialIBr iota) ≠ b := by
  intro hb
  let P : Sylow p G := Classical.choice inferInstance
  have hsupport := trivialBlock_hasNonzeroCentralBrauerRestriction
    iota hinj blocks (P : Subgroup G) P.isPGroup'
  rw [hb] at hsupport
  have heq := hDefect.eq_of_nonzero_le (P : Subgroup G) P.isPGroup' hsupport bot_le
  exact P.ne_bot_of_dvd_card hpG heq.symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrincipalBrauerSupport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
