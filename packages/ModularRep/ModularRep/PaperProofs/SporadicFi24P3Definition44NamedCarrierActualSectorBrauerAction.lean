import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoActions

/-! # The actual sector Brauer action on its canonical span -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorBrauerAction

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualTwoActions

universe u
variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (nu : CentralSector (k := k) (X := X)) (tau : MulAut X)
variable (hnu : MulOpposite.op tau • nu = nu)

def actualSectorBrauerMap : ActualBrauerSector iota hinj blocks nu →
    ActualBrauerSector iota hinj blocks nu :=
  fun phi => ⟨MulOpposite.op tau • phi.1, by
    change blockSector (brauerBlock iota hinj blocks (MulOpposite.op tau • phi.1)) = nu
    rw [brauerBlock_transport, blockSector_transport]
    change MulOpposite.op tau • brauerSector iota hinj blocks phi.1 = nu
    rw [phi.2, hnu]⟩

@[simp]
theorem actualSectorBrauerMap_apply_val (phi : ActualBrauerSector iota hinj blocks nu) :
    (actualSectorBrauerMap iota hinj blocks nu tau hnu phi).1 =
      MulOpposite.op tau • phi.1 := rfl

theorem actualSectorBrauerMap_fixed_iff (phi : ActualBrauerSector iota hinj blocks nu) :
    actualSectorBrauerMap iota hinj blocks nu tau hnu phi = phi ↔
      MulOpposite.op tau • phi.1 = phi.1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

def actualSectorBrauerFixedEquiv :
    {phi : ActualBrauerSector iota hinj blocks nu //
      actualSectorBrauerMap iota hinj blocks nu tau hnu phi = phi} ≃
    {phi : IBr iota // brauerSector iota hinj blocks phi = nu ∧
      MulOpposite.op tau • phi = phi} :=
  (Equiv.subtypeEquivRight
    (actualSectorBrauerMap_fixed_iff iota hinj blocks nu tau hnu)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun phi : IBr iota => brauerSector iota hinj blocks phi = nu)
        (fun phi : IBr iota => MulOpposite.op tau • phi = phi))

def actualSectorBrauerAction :
    actualSectorBrauerSpan iota hinj blocks nu →ₗ[K]
      actualSectorBrauerSpan iota hinj blocks nu :=
  (actualSectorBrauerBasis iota hinj blocks nu).constr K
    (fun phi => actualSectorBrauerBasis iota hinj blocks nu
      (actualSectorBrauerMap iota hinj blocks nu tau hnu phi))

@[simp]
theorem actualSectorBrauerAction_basis (phi : ActualBrauerSector iota hinj blocks nu) :
    actualSectorBrauerAction iota hinj blocks nu tau hnu
        (actualSectorBrauerBasis iota hinj blocks nu phi) =
      actualSectorBrauerBasis iota hinj blocks nu
        (actualSectorBrauerMap iota hinj blocks nu tau hnu phi) := by
  simp only [actualSectorBrauerAction, Module.Basis.constr_basis]

theorem coe_actualSectorBrauerAction_apply
    (f : actualSectorBrauerSpan iota hinj blocks nu) :
    ((actualSectorBrauerAction iota hinj blocks nu tau hnu f :
      actualSectorBrauerSpan iota hinj blocks nu) : PrimeRegularFunction K X p) =
      f.1.pullback tau.toMonoidHom := by
  let P : PrimeRegularFunction K X p →ₗ[K] PrimeRegularFunction K X p := {
    toFun := fun g => g.pullback tau.toMonoidHom
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have h : (actualSectorBrauerSpan iota hinj blocks nu).subtype.comp
      (actualSectorBrauerAction iota hinj blocks nu tau hnu) =
      P.comp (actualSectorBrauerSpan iota hinj blocks nu).subtype := by
    apply (actualSectorBrauerBasis iota hinj blocks nu).ext
    intro phi
    change ((actualSectorBrauerAction iota hinj blocks nu tau hnu
        (actualSectorBrauerBasis iota hinj blocks nu phi) :
          actualSectorBrauerSpan iota hinj blocks nu) : PrimeRegularFunction K X p) =
      ((actualSectorBrauerBasis iota hinj blocks nu phi :
        actualSectorBrauerSpan iota hinj blocks nu) : PrimeRegularFunction K X p).pullback
          tau.toMonoidHom
    rw [actualSectorBrauerAction_basis, coe_actualSectorBrauerBasis_apply,
      coe_actualSectorBrauerBasis_apply]
    rfl
  exact congrArg (fun L : actualSectorBrauerSpan iota hinj blocks nu →ₗ[K]
    PrimeRegularFunction K X p => L f) h

variable (decomposition : ∀ a : MulAut X, ∃ x : X,
  a = MulAut.conj x ∨ a = MulAut.conj x * tau)

include decomposition

theorem actualSectorBrauerMap_involutive :
    Function.Involutive (actualSectorBrauerMap iota hinj blocks nu tau hnu) := by
  intro phi
  apply Subtype.ext
  change MulOpposite.op tau • (MulOpposite.op tau • phi.1) = phi.1
  exact brauer_tau_involutive iota tau decomposition phi.1

theorem actualSectorBrauerAction_comp_self :
    (actualSectorBrauerAction iota hinj blocks nu tau hnu).comp
      (actualSectorBrauerAction iota hinj blocks nu tau hnu) = LinearMap.id := by
  apply (actualSectorBrauerBasis iota hinj blocks nu).ext
  intro phi
  change actualSectorBrauerAction iota hinj blocks nu tau hnu
      (actualSectorBrauerAction iota hinj blocks nu tau hnu
        (actualSectorBrauerBasis iota hinj blocks nu phi)) =
    actualSectorBrauerBasis iota hinj blocks nu phi
  rw [actualSectorBrauerAction_basis, actualSectorBrauerAction_basis,
    actualSectorBrauerMap_involutive iota hinj blocks nu tau hnu decomposition phi]

theorem actualSectorBrauerAction_involutive :
    Function.Involutive (actualSectorBrauerAction iota hinj blocks nu tau hnu) := by
  intro f
  exact congrArg (fun L : actualSectorBrauerSpan iota hinj blocks nu →ₗ[K]
      actualSectorBrauerSpan iota hinj blocks nu => L f)
    (actualSectorBrauerAction_comp_self iota hinj blocks nu tau hnu decomposition)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorBrauerAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
