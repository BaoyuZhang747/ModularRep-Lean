import ModularRep.IBrBlock
import ModularRep.PrimitiveBlockAutomorphism
import ModularRep.Twist

/-!
# Automorphisms of Brauer-character blocks

This file proves that the block of an irreducible Brauer character is
transported by the canonical right action of group automorphisms on literal
primitive block idempotents.
-/

noncomputable section

open scoped MonoidAlgebra

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V]

/-- Twisting a representation by `alpha` cancels transport of a group algebra
element by `alpha.symm`. -/
theorem twist_asAlgebraHom_mapDomainRingEquiv_symm_apply
    (rho : Representation k G V) (alpha : MulAut G) (x : k[G]) :
    (rho.twist alpha).asAlgebraHom
        (MonoidAlgebra.mapDomainRingEquiv k alpha.symm x) =
      rho.asAlgebraHom x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g r =>
      simp [Representation.asAlgebraHom_single]

end Representation

namespace ModularRep.BlockIdempotentDecomposition

universe u v

variable {k : Type u} {G : Type v} {V : Type*} {ι : Type*}
variable [Field k] [Group G] [Fintype ι]
variable [AddCommGroup V] [Module k V]

/-- The block supporting an automorphism twist of a simple representation is
the transported literal block supporting the original representation. -/
theorem primitiveBlockOfIndex_moduleBlock_op_smul
    (rho : Representation k G V) (a : (MulAut G)ᵐᵒᵖ)
    [IsSimpleModule k[G] rho.asModule]
    [IsSimpleModule k[G] (rho.twist a.unop).asModule]
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b) :
    D.primitiveBlockOfIndex
        (D.moduleBlock (V := (rho.twist a.unop).asModule)) =
      a • D.primitiveBlockOfIndex
        (D.moduleBlock (V := rho.asModule)) := by
  let transported : LiteralPrimitiveBlock k G :=
    a • D.primitiveBlockOfIndex (D.moduleBlock (V := rho.asModule))
  let j : ι := D.primitiveBlockEquiv.symm transported
  have hjLiteral : D.primitiveBlockOfIndex j = transported := by
    simpa only [primitiveBlockEquiv_apply, j] using
      D.primitiveBlockEquiv.apply_symm_apply transported
  have hjval :
      b j = MonoidAlgebra.mapDomainRingEquiv k a.unop.symm
        (b (D.moduleBlock (V := rho.asModule))) := by
    simpa only [primitiveBlockOfIndex_val, transported,
      LiteralPrimitiveBlock.rightMulAction_smul_val] using
        congrArg Subtype.val hjLiteral
  have hj :
      j = D.moduleBlock (V := (rho.twist a.unop).asModule) := by
    apply D.moduleBlock_eq_of_smul_eq_self
    intro v
    apply (rho.twist a.unop).asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul]
    change
      (rho.twist a.unop).asAlgebraHom (b j)
          ((rho.twist a.unop).asModuleEquiv v) =
        (rho.twist a.unop).asModuleEquiv v
    rw [hjval,
      Representation.twist_asAlgebraHom_mapDomainRingEquiv_symm_apply]
    let u : rho.asModule :=
      rho.asModuleEquiv.symm ((rho.twist a.unop).asModuleEquiv v)
    have hu := D.moduleBlock_smul (V := rho.asModule) u
    have hu' := congrArg rho.asModuleEquiv hu
    simpa only [Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply, u] using hu'
  rw [← hj]
  simpa only [transported] using hjLiteral

end ModularRep.BlockIdempotentDecomposition

namespace ModularRep.FDRepSimpleClassKZero

open CategoryTheory

universe u v w

variable {p : ℕ} {k G : Type u} {K : Type v} {ι : Type w}
variable [Field k] [Field K] [Group G] [Finite G] [Fintype ι]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

/-- The literal block of an irreducible Brauer character is transported by
the canonical right action of group automorphisms. -/
theorem primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (a : (MulAut G)ᵐᵒᵖ) (phi : IBr iota) :
    D.primitiveBlockOfIndex
        (irreducibleBrauerCharacterBlock iota hinj D (a • phi)) =
      a • D.primitiveBlockOfIndex
        (irreducibleBrauerCharacterBlock iota hinj D phi) := by
  let alpha : MulAut G := a.unop
  let X : SimpleModuleClass k[G] :=
    (simpleModuleClassEquivIBr iota hinj).symm phi
  let rho : Representation k G (simpleClassFDRep X).V :=
    (simpleClassFDRep X).ρ
  have hrho : Representation.IsIrreducible rho :=
    simpleClassFDRep_irreducible X
  let _ : Representation.IsIrreducible rho := hrho
  let _ : Representation.IsIrreducible (rho.twist alpha) := hrho.twist alpha
  let Vtw : FDRep k G := FDRep.of (rho.twist alpha)
  have hVtw : Representation.IsIrreducible Vtw.ρ := by
    simpa only [Vtw, FDRep.of_ρ'] using hrho.twist alpha
  let Y : SimpleModuleClass k[G] :=
    simpleClassOfIrreducibleFDRep Vtw hVtw
  let _ : Representation.IsIrreducible (simpleClassFDRep Y).ρ :=
    simpleClassFDRep_irreducible Y
  have hXphi : simpleClassToIBr iota X = phi := by
    simpa only [X, simpleModuleClassEquivIBr_apply] using
      (simpleModuleClassEquivIBr iota hinj).apply_symm_apply phi
  have hXphiVal :
      Representation.brauerCharacterOfRootEmbedding rho iota = phi.1 := by
    exact congrArg Subtype.val hXphi
  have hYchar : simpleClassToIBr iota Y = a • phi := by
    apply Subtype.ext
    change
      Representation.brauerCharacterOfRootEmbedding
          (simpleClassFDRep Y).ρ iota =
        (a • phi).1
    calc
      Representation.brauerCharacterOfRootEmbedding
          (simpleClassFDRep Y).ρ iota =
          Representation.brauerCharacterOfRootEmbedding Vtw.ρ iota :=
        Representation.brauerCharacterOfRootEmbedding_iso iota
          (simpleClassOfIrreducibleFDRepIso Vtw hVtw)
      _ = Representation.brauerCharacterOfRootEmbedding
          (rho.twist alpha) iota := by
        rfl
      _ = (Representation.brauerCharacterOfRootEmbedding rho iota).twist alpha :=
        Representation.brauerCharacterOfRootEmbedding_twist rho iota alpha
      _ = phi.1.twist alpha := by rw [hXphiVal]
      _ = (a • phi).1 := by
        rw [IrreducibleBrauerCharacter.op_smul_val]
  have hchosen :
      (simpleModuleClassEquivIBr iota hinj).symm (a • phi) = Y := by
    apply hinj
    have hleft :
        simpleClassToIBr iota
            ((simpleModuleClassEquivIBr iota hinj).symm (a • phi)) =
          a • phi := by
      simpa only [simpleModuleClassEquivIBr_apply] using
        (simpleModuleClassEquivIBr iota hinj).apply_symm_apply (a • phi)
    exact hleft.trans hYchar.symm
  have hYblock :
      simpleModuleClassBlock D Y =
        D.moduleBlock (V := (rho.twist alpha).asModule) := by
    let hSource : IsSimpleModule k[G]
        ((FDRepFiniteLength.toModuleMonoidAlgebra
          (k := k) (G := G)).obj (simpleClassFDRep Y)) := by
      change IsSimpleModule k[G]
        (Representation.asModule (simpleClassFDRep Y).ρ)
      exact (Representation.irreducible_iff_isSimpleModule_asModule
        (simpleClassFDRep Y).ρ).mp (simpleClassFDRep_irreducible Y)
    let _ : IsSimpleModule k[G]
        ((FDRepFiniteLength.toModuleMonoidAlgebra
          (k := k) (G := G)).obj (simpleClassFDRep Y)) := hSource
    let hTarget : IsSimpleModule k[G]
        ((FDRepFiniteLength.toModuleMonoidAlgebra
          (k := k) (G := G)).obj Vtw) := by
      change IsSimpleModule k[G] (Representation.asModule Vtw.ρ)
      exact (Representation.irreducible_iff_isSimpleModule_asModule Vtw.ρ).mp hVtw
    let _ : IsSimpleModule k[G]
        ((FDRepFiniteLength.toModuleMonoidAlgebra
          (k := k) (G := G)).obj Vtw) := hTarget
    let eM := (FDRepFiniteLength.toModuleMonoidAlgebra
      (k := k) (G := G)).mapIso
        (simpleClassOfIrreducibleFDRepIso Vtw hVtw)
    change
      D.moduleBlock (V :=
        Representation.asModule
          ((simpleClassFDRep Y).ρ :
            Representation k G (simpleClassFDRep Y).V)) =
        D.moduleBlock (V := (rho.twist alpha).asModule)
    convert D.moduleBlock_eq_of_linearEquiv eM.toLinearEquiv using 1 <;> rfl
  have hphiBlock :
      irreducibleBrauerCharacterBlock iota hinj D phi =
        D.moduleBlock (V := rho.asModule) := by
    change simpleModuleClassBlock D X =
      D.moduleBlock (V := rho.asModule)
    rfl
  have htwistedBlock :
      irreducibleBrauerCharacterBlock iota hinj D (a • phi) =
        D.moduleBlock (V := (rho.twist alpha).asModule) := by
    change
      simpleModuleClassBlock D
          ((simpleModuleClassEquivIBr iota hinj).symm (a • phi)) =
        D.moduleBlock (V := (rho.twist alpha).asModule)
    rw [hchosen]
    exact hYblock
  rw [htwistedBlock, hphiBlock]
  simpa only [alpha] using
    D.primitiveBlockOfIndex_moduleBlock_op_smul rho a

end ModularRep.FDRepSimpleClassKZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
