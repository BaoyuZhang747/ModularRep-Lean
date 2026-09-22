import ModularRep.BrauerCharacterHomPullback
import ModularRep.BlockIdempotentDecompositionEquivTransport
import ModularRep.SemisimpleBlockSimpleClass

/-!
# Transport of Brauer-character blocks along group equivalences

This file proves that the block index of an irreducible Brauer character is
unchanged when the character, its affording representation, and a complete
primitive block-idempotent decomposition are transported along a group
equivalence.  It contains no block-induction or manuscript-specific input.
-/

noncomputable section

open scoped MonoidAlgebra

namespace Representation

variable {k G H V : Type*}
variable [CommSemiring k] [Monoid G] [Monoid H]
variable [AddCommMonoid V] [Module k V]

/-- Pulling a representation back along the inverse of a group equivalence
cancels transport of a group algebra element along that equivalence. -/
@[simp]
theorem pullback_asAlgebraHom_domCongr_apply
    (rho : Representation k G V) (e : G ≃* H) (x : k[G]) :
    (rho.pullback e.symm.toMonoidHom).asAlgebraHom
        (MonoidAlgebra.domCongr k k e x) =
      rho.asAlgebraHom x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add]
      exact congrArg₂ (fun a b ↦ a + b) hx hy
  | single g r => simp [Representation.asAlgebraHom_single]

end Representation

namespace ModularRep.BlockIdempotentDecomposition

variable {k G H V ι : Type*}
variable [Field k] [Group G] [Group H] [Fintype ι]
variable [AddCommGroup V] [Module k V]

/-- Transporting a complete block decomposition along a group equivalence
preserves the block supporting a pulled-back simple representation. -/
theorem moduleBlock_alongMulEquiv
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (rho : Representation k G V) (e : G ≃* H)
    [IsSimpleModule k[G] rho.asModule]
    [IsSimpleModule k[H]
      (rho.pullback e.symm.toMonoidHom).asModule] :
    (D.alongMulEquiv e).moduleBlock
        (V := (rho.pullback e.symm.toMonoidHom).asModule) =
      D.moduleBlock (V := rho.asModule) := by
  symm
  apply (D.alongMulEquiv e).moduleBlock_eq_of_smul_eq_self
  intro v
  apply (rho.pullback e.symm.toMonoidHom).asModuleEquiv.injective
  rw [Representation.asModuleEquiv_map_smul]
  rw [Representation.pullback_asAlgebraHom_domCongr_apply]
  let u : rho.asModule :=
    rho.asModuleEquiv.symm
      ((rho.pullback e.symm.toMonoidHom).asModuleEquiv v)
  have hu := D.moduleBlock_smul (V := rho.asModule) u
  have hu' := congrArg rho.asModuleEquiv hu
  simpa only [Representation.asModuleEquiv_map_smul,
    LinearEquiv.apply_symm_apply, u] using hu'

end ModularRep.BlockIdempotentDecomposition

namespace ModularRep.FDRepSimpleClassKZero

open CategoryTheory

universe u v w

/-- The canonical representative chosen for the class of an irreducible
representation belongs to the same block as that representation. -/
theorem simpleModuleClassBlock_simpleClassOfIrreducibleFDRep
    {k G : Type u} {ι : Type w}
    [Field k] [Group G] [Finite G] [Fintype ι]
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (V : FDRep k G) (hV : Representation.IsIrreducible V.ρ)
    [IsSimpleModule k[G] (Representation.asModule V.ρ)] :
    simpleModuleClassBlock D (simpleClassOfIrreducibleFDRep V hV) =
      D.moduleBlock (V := Representation.asModule V.ρ) := by
  let X : SimpleModuleClass k[G] :=
    simpleClassOfIrreducibleFDRep V hV
  letI : IsSimpleModule k[G]
      (Representation.asModule (simpleClassFDRep X).ρ) := by
    exact (Representation.irreducible_iff_isSimpleModule_asModule
      (simpleClassFDRep X).ρ).mp (simpleClassFDRep_irreducible X)
  let eM := (FDRepFiniteLength.toModuleMonoidAlgebra
    (k := k) (G := G)).mapIso
      (simpleClassOfIrreducibleFDRepIso V hV)
  change D.moduleBlock (V := Representation.asModule
      ((simpleClassFDRep X).ρ :
        Representation k G (simpleClassFDRep X).V)) =
    D.moduleBlock (V := Representation.asModule V.ρ)
  convert D.moduleBlock_eq_of_linearEquiv eM.toLinearEquiv using 1 <;> rfl

/-- Transporting an irreducible Brauer character and a complete primitive
block decomposition along a group equivalence preserves the block index,
even when the target root embedding and target character are independently
chosen, provided their lift and class function agree with transport. -/
theorem irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq
    {p : ℕ} {k G H : Type u} {K : Type v} {ι : Type w}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group H] [Finite H] [Fintype ι]
    (iotaG : PrimeRegularRootEmbedding p k K G)
    (hinjG : IrreducibleBrauerCharacterInjectivity iotaG)
    (iotaH : PrimeRegularRootEmbedding p k K H)
    (hinjH : IrreducibleBrauerCharacterInjectivity iotaH)
    (e : G ≃* H)
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (phiG : IBr iotaG)
    (phiH : IBr iotaH)
    (hlift : iotaH.lift = iotaG.lift)
    (hphi : phiH.1 =
      PrimeRegularClassFunction.pullback e.symm.toMonoidHom phiG.1) :
    irreducibleBrauerCharacterBlock
        iotaH hinjH (D.alongMulEquiv e) phiH =
      irreducibleBrauerCharacterBlock iotaG hinjG D phiG := by
  let X : SimpleModuleClass k[G] :=
    (simpleModuleClassEquivIBr iotaG hinjG).symm phiG
  let rho : Representation k G (simpleClassFDRep X).V :=
    (simpleClassFDRep X).ρ
  have hrho : Representation.IsIrreducible rho :=
    simpleClassFDRep_irreducible X
  let hRhoSimple : IsSimpleModule k[G] rho.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule rho).mp hrho
  letI : IsSimpleModule k[G] rho.asModule := hRhoSimple
  let rhoH : Representation k H (simpleClassFDRep X).V :=
    rho.pullback e.symm.toMonoidHom
  have hrhoH : Representation.IsIrreducible rhoH := by
    simpa only [rhoH] using
      hrho.pullback e.symm.toMonoidHom e.symm.surjective
  let hRhoHSimple : IsSimpleModule k[H] rhoH.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule rhoH).mp hrhoH
  letI : IsSimpleModule k[H] rhoH.asModule := hRhoHSimple
  let VH : FDRep k H := FDRep.of rhoH
  have hVH : Representation.IsIrreducible VH.ρ := by
    simpa only [VH, FDRep.of_ρ'] using hrhoH
  let hVHSimple : IsSimpleModule k[H] (Representation.asModule VH.ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule VH.ρ).mp hVH
  letI : IsSimpleModule k[H] (Representation.asModule VH.ρ) := hVHSimple
  let Y : SimpleModuleClass k[H] :=
    simpleClassOfIrreducibleFDRep VH hVH
  have hXphi : simpleClassToIBr iotaG X = phiG := by
    simpa only [X, simpleModuleClassEquivIBr_apply] using
      (simpleModuleClassEquivIBr iotaG hinjG).apply_symm_apply phiG
  have hXphiVal :
      Representation.brauerCharacterOfRootEmbedding rho iotaG = phiG.1 :=
    congrArg Subtype.val hXphi
  have hYchar :
      simpleClassToIBr iotaH Y = phiH := by
    apply Subtype.ext
    change Representation.brauerCharacterOfRootEmbedding
        (simpleClassFDRep Y).ρ iotaH = phiH.1
    calc
      Representation.brauerCharacterOfRootEmbedding
          (simpleClassFDRep Y).ρ iotaH =
        Representation.brauerCharacterOfRootEmbedding VH.ρ iotaH :=
        Representation.brauerCharacterOfRootEmbedding_iso
          iotaH (simpleClassOfIrreducibleFDRepIso VH hVH)
      _ = Representation.brauerCharacterOfRootEmbedding rhoH iotaH := by
        rfl
      _ = PrimeRegularClassFunction.pullback e.symm.toMonoidHom
          (Representation.brauerCharacterOfRootEmbedding rho iotaG) :=
        Representation.brauerCharacterOfRootEmbedding_pullback_of_lift_eq
          (G := G) (H := H) rho iotaG iotaH
          e.symm.toMonoidHom hlift
      _ = PrimeRegularClassFunction.pullback
          e.symm.toMonoidHom phiG.1 := by
        rw [hXphiVal]
      _ = phiH.1 := hphi.symm
  have hchosen :
      (simpleModuleClassEquivIBr iotaH hinjH).symm phiH = Y := by
    apply hinjH
    have hleft :
        simpleClassToIBr iotaH
            ((simpleModuleClassEquivIBr iotaH hinjH).symm phiH) =
          phiH := by
      simpa only [simpleModuleClassEquivIBr_apply] using
        (simpleModuleClassEquivIBr iotaH hinjH).apply_symm_apply phiH
    exact hleft.trans hYchar.symm
  have hsource :
      irreducibleBrauerCharacterBlock iotaG hinjG D phiG =
        D.moduleBlock (V := rho.asModule) := by
    change simpleModuleClassBlock D X =
      D.moduleBlock (V := rho.asModule)
    rfl
  have htarget :
      irreducibleBrauerCharacterBlock
          iotaH hinjH (D.alongMulEquiv e) phiH =
        (D.alongMulEquiv e).moduleBlock (V := rhoH.asModule) := by
    change simpleModuleClassBlock (D.alongMulEquiv e)
        ((simpleModuleClassEquivIBr iotaH hinjH).symm phiH) =
      (D.alongMulEquiv e).moduleBlock (V := rhoH.asModule)
    rw [hchosen]
    simpa only [VH, FDRep.of_ρ'] using
      simpleModuleClassBlock_simpleClassOfIrreducibleFDRep
        (D.alongMulEquiv e) VH hVH
  rw [htarget, hsource]
  simpa only [rhoH] using D.moduleBlock_alongMulEquiv rho e

/-- Transporting an irreducible Brauer character and a complete primitive
block decomposition along a group equivalence preserves the block index. -/
theorem irreducibleBrauerCharacterBlock_alongMulEquiv
    {p : ℕ} {k G H : Type u} {K : Type v} {ι : Type w}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group H] [Finite H] [Fintype ι]
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinjG : IrreducibleBrauerCharacterInjectivity iota)
    (e : G ≃* H)
    (hinjH : IrreducibleBrauerCharacterInjectivity (iota.alongMulEquiv e))
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (phi : IBr iota) :
    irreducibleBrauerCharacterBlock
        (iota.alongMulEquiv e) hinjH (D.alongMulEquiv e)
        (IrreducibleBrauerCharacter.alongMulEquiv iota e phi) =
      irreducibleBrauerCharacterBlock iota hinjG D phi := by
  exact irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq
    (iotaG := iota)
    (hinjG := hinjG)
    (iotaH := iota.alongMulEquiv e)
    (hinjH := hinjH)
    (e := e)
    (D := D)
    (phiG := phi)
    (phiH := IrreducibleBrauerCharacter.alongMulEquiv iota e phi)
    (hlift := funext (fun z ↦ iota.alongMulEquiv_lift e z))
    (hphi := IrreducibleBrauerCharacter.alongMulEquiv_val iota e phi)

end ModularRep.FDRepSimpleClassKZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
