import ModularRep.CharacterWeightBlockAssignment
import ModularRep.CharacterWeightRadicalProjection
import ModularRep.BrauerCharacterEquivTransport
import ModularRep.IBrBlockBasicSetBridge
import ModularRep.PaperProofs.CyclicOuterLemma37Concrete
import ModularRep.SemidirectEmbeddedConjugation

/-!
# Lemma 2.10 on literal block fibres

This module replaces the global carriers in the concrete Lemma 2.10 adapter
by the literal fibres `IBrBlock` and
`CharacterWeight.LocalBlockInductionSource.Fibre`.  Both fibre actions are
pulled back from canonical opposite-automorphism transport.  The radical map
is the reusable projection `CharacterWeight.radicalClass` restricted to the
weight fibre.

The source interface contains only automorphism transport of the Brauer
block index and stability of the chosen block under the cyclic outer group.
Local block formation, inflation, block induction, and cyclic Brauer
extension remain exact E1 inputs.  No blockwise equivalence, BAW/iBAW
predicate, Brough--Späth criterion, or final criterion conclusion is an
argument of any declaration below.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete

universe u

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]

/-- The literal Brauer-character fibre of a selected block. -/
abbrev BrauerFibre (block : ι) :=
  IBrBlock iota hinj blocks block

/-- The literal weight fibre defined by local block induction. -/
abbrev WeightFibre
    (blockSource : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := H) (Block := ι))
    (block : ι) :=
  blockSource.Fibre block

/-- The literal carrier of radical-subgroup conjugacy classes. -/
abbrev RadicalClass :=
  CharacterWeight.RadicalConjugacyClass (p := p) (G := H)

section CanonicalRestrictedActions

variable {A : Type u} [Group A]

/-- A homomorphism into the full automorphism stabiliser of a block, formed
from manuscript right transport. -/
def rightBlockStabilizer
    (rho : A →* MulAut H) (block : ι)
    (hfixed : ∀ a : A, inverseOpHom rho a • block = block) :
    A →* MulAction.stabilizer (MulAut H)ᵐᵒᵖ block where
  toFun a := ⟨inverseOpHom rho a, hfixed a⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (inverseOpHom rho)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (inverseOpHom rho) a b

/-- Canonical manuscript right action on a local-block-induction fibre. -/
@[instance_reducible]
def rightWeightFibreMulAction
    (rho : A →* MulAut H)
    (blockSource : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := H) (Block := ι))
    (block : ι)
    (hfixed : ∀ a : A, inverseOpHom rho a • block = block) :
    MulAction A (WeightFibre blockSource block) :=
  MulAction.compHom _ (rightBlockStabilizer rho block hfixed)

@[simp]
theorem rightWeightFibre_smul_val
    (rho : A →* MulAut H)
    (blockSource : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := H) (Block := ι))
    (block : ι)
    (hfixed : ∀ a : A, inverseOpHom rho a • block = block)
    (a : A) (w : WeightFibre blockSource block) :
    let _ : MulAction A (WeightFibre blockSource block) :=
      rightWeightFibreMulAction rho blockSource block hfixed
    (a • w).1 = inverseOpHom rho a • w.1 := by
  exact blockSource.fibre_smul_val block
    ⟨inverseOpHom rho a, hfixed a⟩ w

/-- Stability of a literal Brauer block fibre, derived from block-index
transport and fixation of the chosen block. -/
theorem rightIBrBlockStable
    (rho : A →* MulAut H) (block : ι)
    (hfixed : ∀ a : A, inverseOpHom rho a • block = block)
    (htransport : ∀ (alpha : (MulAut H)ᵐᵒᵖ) (psi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks (alpha • psi) =
        alpha • irreducibleBrauerCharacterBlock iota hinj blocks psi) :
    IsAutomorphismStableIBrBlock
      (inverseOpHom rho) iota hinj blocks block := by
  intro a psi hpsi
  rw [htransport, hpsi, hfixed]

/-- Canonical manuscript right action on a literal Brauer block fibre. -/
@[instance_reducible]
def rightIBrBlockMulAction
    (rho : A →* MulAut H) (block : ι)
    (hfixed : ∀ a : A, inverseOpHom rho a • block = block)
    (htransport : ∀ (alpha : (MulAut H)ᵐᵒᵖ) (psi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks (alpha • psi) =
        alpha • irreducibleBrauerCharacterBlock iota hinj blocks psi) :
    MulAction A (BrauerFibre iota hinj blocks block) :=
  automorphismIBrBlockMulAction (inverseOpHom rho)
    (rightIBrBlockStable iota hinj blocks rho block hfixed htransport)

@[simp]
theorem rightIBrBlock_smul_val
    (rho : A →* MulAut H) (block : ι)
    (hfixed : ∀ a : A, inverseOpHom rho a • block = block)
    (htransport : ∀ (alpha : (MulAut H)ᵐᵒᵖ) (psi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks (alpha • psi) =
        alpha • irreducibleBrauerCharacterBlock iota hinj blocks psi)
    (a : A) (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction A (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks rho block hfixed htransport
    (a • psi).1 = inverseOpHom rho a • psi.1 :=
  rfl

end CanonicalRestrictedActions

variable (phi : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)

/-- Restriction of the reusable radical-class projection to a literal
local-block-induction fibre. -/
def fibreRadical (w : WeightFibre blockSource block) :
    RadicalClass (p := p) (H := H) :=
  CharacterWeight.radicalClass w.1

/-- Inner automorphisms fix every literal radical-subgroup conjugacy class. -/
theorem inner_fixes_radicalClass (h : H)
    (q : RadicalClass (p := p) (H := H)) :
    let _ : MulAction H (RadicalClass (p := p) (H := H)) :=
      rightAutomorphismAction
        (X := RadicalClass (p := p) (H := H))
        (MulAut.conj : H →* MulAut H)
    h • q = q := by
  dsimp only [rightAutomorphismAction, inverseOpHom]
  refine Quotient.inductionOn q ?_
  intro Q
  apply Quotient.sound
  exact ⟨h, rfl⟩

/-- Narrow E1 transport data needed to put the canonical actions on the two
selected literal block fibres. -/
structure FibreTransportSource where
  brauerBlock_transport : ∀ (alpha : (MulAut H)ᵐᵒᵖ) (psi : IBr iota),
    irreducibleBrauerCharacterBlock iota hinj blocks (alpha • psi) =
      alpha • irreducibleBrauerCharacterBlock iota hinj blocks psi
  outerBlock_fixed : ∀ e : E, inverseOpHom phi e • block = block

namespace FibreTransportSource

variable (T : FibreTransportSource iota hinj blocks phi block)

/-- Inner automorphisms fix the selected block because local block induction
is inner invariant. -/
theorem innerBlock_fixed
    (blockSource : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := H) (Block := ι))
    (h : H) :
    inverseOpHom (MulAut.conj : H →* MulAut H) h • block = block := by
  change MulOpposite.op (MulAut.conj h⁻¹) • block = block
  exact blockSource.inner_blocks_fixed h block

/-- The canonical `H`- and `E`-actions on the literal Brauer fibre satisfy
the semidirect compatibility identity. -/
theorem brauerFibre_compatible :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport
    SemidirectActionCompatible
      (X := BrauerFibre iota hinj blocks block) phi := by
  dsimp only
  intro e h psi
  apply Subtype.ext
  exact rightAutomorphismSemidirectCompatible (X := IBr iota) phi e h psi.1

/-- The canonical `H`- and `E`-actions on the literal weight fibre satisfy
the semidirect compatibility identity. -/
theorem weightFibre_compatible :
    let _ : MulAction H (WeightFibre blockSource block) :=
      rightWeightFibreMulAction
        (MulAut.conj : H →* MulAut H) blockSource block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
    let _ : MulAction E (WeightFibre blockSource block) :=
      rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
    SemidirectActionCompatible (X := WeightFibre blockSource block) phi := by
  dsimp only
  intro e h w
  apply Subtype.ext
  exact rightAutomorphismSemidirectCompatible
    (X := CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H))
      phi e h w.1

/-- Inner automorphisms fix every element of the literal Brauer block
fibre. -/
theorem inner_fixes_brauerFibre (h : H)
    (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    h • psi = psi := by
  dsimp only
  apply Subtype.ext
  exact inner_fixes_ibr iota h psi.1

/-- Inner automorphisms fix every element of the literal weight block
fibre. -/
theorem inner_fixes_weightFibre (h : H)
    (w : WeightFibre blockSource block) :
    let _ : MulAction H (WeightFibre blockSource block) :=
      rightWeightFibreMulAction
        (MulAut.conj : H →* MulAut H) blockSource block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
    h • w = w := by
  dsimp only
  apply Subtype.ext
  exact inner_fixes_weightClass h w.1

/-- A merely outer-equivariant map between the literal fibres is
automatically semidirect-equivariant.  No injectivity, surjectivity, or
equivalence is assumed. -/
theorem fibreMap_semidirect_equivariant
    (omega : BrauerFibre iota hinj blocks block →
      WeightFibre blockSource block)
    (omegaE :
      let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
        rightIBrBlockMulAction iota hinj blocks phi block
          T.outerBlock_fixed T.brauerBlock_transport
      let _ : MulAction E (WeightFibre blockSource block) :=
        rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
      ∀ (e : E) (psi : BrauerFibre iota hinj blocks block),
        omega (e • psi) = e • omega psi) :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport
    let _ : MulAction H (WeightFibre blockSource block) :=
      rightWeightFibreMulAction
        (MulAut.conj : H →* MulAut H) blockSource block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
    let _ : MulAction E (WeightFibre blockSource block) :=
      rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
    let _ : MulAction (H ⋊[phi] E) (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction phi
        (brauerFibre_compatible (iota := iota) (hinj := hinj)
          (blocks := blocks) (phi := phi) (blockSource := blockSource)
          (block := block) (T := T))
    let _ : MulAction (H ⋊[phi] E) (WeightFibre blockSource block) :=
      semidirectMulAction phi
        (weightFibre_compatible (iota := iota) (hinj := hinj)
          (blocks := blocks) (phi := phi) (blockSource := blockSource)
          (block := block) (T := T))
    ∀ (g : H ⋊[phi] E) (psi : BrauerFibre iota hinj blocks block),
      omega (g • psi) = g • omega psi := by
  dsimp only
  letI : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (innerBlock_fixed (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  letI : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks phi block
      T.outerBlock_fixed T.brauerBlock_transport
  letI : MulAction H (WeightFibre blockSource block) :=
    rightWeightFibreMulAction
      (MulAut.conj : H →* MulAut H) blockSource block
      (innerBlock_fixed (blockSource := blockSource) (block := block))
  letI : MulAction E (WeightFibre blockSource block) :=
    rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
  intro g psi
  change omega (g.left • (g.right • psi)) =
    g.left • (g.right • omega psi)
  rw [inner_fixes_brauerFibre (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T),
    omegaE,
    inner_fixes_weightFibre (blockSource := blockSource)
      (block := block)]

/-- The full stabiliser of a literal Brauer-block element is the inverse
image of its cyclic-outer stabiliser. -/
theorem brauerFibre_stabilizer_eq_outer_comap
    (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport
    let hcompat := brauerFibre_compatible (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T)
    let _ : MulAction (H ⋊[phi] E) (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction phi hcompat
    MulAction.stabilizer (H ⋊[phi] E) psi =
      (MulAction.stabilizer E psi).comap SemidirectProduct.rightHom := by
  dsimp only
  letI : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (innerBlock_fixed (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  letI : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks phi block
      T.outerBlock_fixed T.brauerBlock_transport
  exact semidirect_stabilizer_eq_comap_right_stabilizer_of_left_trivial
    phi
    (brauerFibre_compatible (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T))
    (fun h x ↦ inner_fixes_brauerFibre (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T) h x)
    psi

/-- Elementwise canonical factorisation of the literal Brauer-fibre
stabiliser. -/
theorem brauerFibre_stabilizer_factorization
    (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport
    let hcompat := brauerFibre_compatible (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T)
    let _ : MulAction (H ⋊[phi] E) (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction phi hcompat
    ∀ g : H ⋊[phi] E,
      g ∈ MulAction.stabilizer (H ⋊[phi] E) psi ↔
        ∃ h : H, ∃ e : E,
          e ∈ MulAction.stabilizer E psi ∧
            g = SemidirectProduct.inl h * SemidirectProduct.inr e := by
  dsimp only
  letI : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (innerBlock_fixed (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  letI : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks phi block
      T.outerBlock_fixed T.brauerBlock_transport
  exact mem_semidirect_stabilizer_iff_exists_right_factorization
    phi
    (brauerFibre_compatible (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T))
    (fun h x ↦ inner_fixes_brauerFibre (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T) h x)
    psi

/-- The literal Brauer-fibre stabiliser quotient is cyclic. -/
theorem brauerFibre_stabilizer_quotient_cyclic
    (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport
    let hcompat := brauerFibre_compatible (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T)
    let _ : MulAction (H ⋊[phi] E) (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction phi hcompat
    IsCyclic (semidirectStabilizer (phi := phi) psi ⧸
      embeddedHStabilizer (phi := phi) psi) := by
  dsimp only
  letI : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (innerBlock_fixed (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  letI : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks phi block
      T.outerBlock_fixed T.brauerBlock_transport
  exact isCyclic_stabilizer_quotient_of_compatible
    (brauerFibre_compatible (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T)) psi

/-- The reusable radical projection remains equivariant after restriction to
the selected literal weight fibre. -/
theorem fibreRadical_outer_equivariant
    (e : E) (w : WeightFibre blockSource block) :
    let _ : MulAction E (WeightFibre blockSource block) :=
      rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
    let _ : MulAction E (RadicalClass (p := p) (H := H)) :=
      rightAutomorphismAction
        (X := RadicalClass (p := p) (H := H)) phi
    fibreRadical blockSource block (e • w) =
      e • fibreRadical blockSource block w := by
  dsimp only
  letI : MulAction E (WeightFibre blockSource block) :=
    rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
  letI : MulAction E (RadicalClass (p := p) (H := H)) :=
    rightAutomorphismAction
      (X := RadicalClass (p := p) (H := H)) phi
  change CharacterWeight.radicalClass (inverseOpHom phi e • w.1) =
    inverseOpHom phi e • CharacterWeight.radicalClass w.1
  exact CharacterWeight.radicalClass_equivariant (inverseOpHom phi e) w.1

/-- The literal weight-fibre radical projection is equivariant for the full
semidirect action. -/
theorem fibreRadical_semidirect_equivariant :
    let _ : MulAction H (WeightFibre blockSource block) :=
      rightWeightFibreMulAction
        (MulAut.conj : H →* MulAut H) blockSource block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
    let _ : MulAction E (WeightFibre blockSource block) :=
      rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
    let _ : MulAction H (RadicalClass (p := p) (H := H)) :=
      rightAutomorphismAction
        (X := RadicalClass (p := p) (H := H))
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (RadicalClass (p := p) (H := H)) :=
      rightAutomorphismAction
        (X := RadicalClass (p := p) (H := H)) phi
    let _ : MulAction (H ⋊[phi] E) (WeightFibre blockSource block) :=
      semidirectMulAction phi
        (weightFibre_compatible (iota := iota) (hinj := hinj)
          (blocks := blocks) (phi := phi) (blockSource := blockSource)
          (block := block) (T := T))
    let _ : MulAction (H ⋊[phi] E) (RadicalClass (p := p) (H := H)) :=
      semidirectMulAction phi
        (rightAutomorphismSemidirectCompatible
          (X := RadicalClass (p := p) (H := H)) phi)
    ∀ (g : H ⋊[phi] E) (w : WeightFibre blockSource block),
      fibreRadical blockSource block (g • w) =
        g • fibreRadical blockSource block w := by
  dsimp only
  letI : MulAction H (WeightFibre blockSource block) :=
    rightWeightFibreMulAction
      (MulAut.conj : H →* MulAut H) blockSource block
      (innerBlock_fixed (blockSource := blockSource) (block := block))
  letI : MulAction E (WeightFibre blockSource block) :=
    rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
  letI : MulAction H (RadicalClass (p := p) (H := H)) :=
    rightAutomorphismAction
      (X := RadicalClass (p := p) (H := H))
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (RadicalClass (p := p) (H := H)) :=
    rightAutomorphismAction
      (X := RadicalClass (p := p) (H := H)) phi
  intro g w
  change fibreRadical blockSource block (g.left • (g.right • w)) =
    g.left • (g.right • fibreRadical blockSource block w)
  rw [inner_fixes_weightFibre (blockSource := blockSource) (block := block),
    fibreRadical_outer_equivariant (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T),
    inner_fixes_radicalClass]

/-- The literal weight-fibre stabiliser quotient is cyclic. -/
theorem weightFibre_stabilizer_quotient_cyclic
    (w : WeightFibre blockSource block) :
    let _ : MulAction H (WeightFibre blockSource block) :=
      rightWeightFibreMulAction
        (MulAut.conj : H →* MulAut H) blockSource block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
    let _ : MulAction E (WeightFibre blockSource block) :=
      rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
    let hcompat := weightFibre_compatible (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T)
    let _ : MulAction (H ⋊[phi] E) (WeightFibre blockSource block) :=
      semidirectMulAction phi hcompat
    IsCyclic (semidirectStabilizer (phi := phi) w ⧸
      embeddedHStabilizer (phi := phi) w) := by
  dsimp only
  letI : MulAction H (WeightFibre blockSource block) :=
    rightWeightFibreMulAction
      (MulAut.conj : H →* MulAut H) blockSource block
      (innerBlock_fixed (blockSource := blockSource) (block := block))
  letI : MulAction E (WeightFibre blockSource block) :=
    rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
  exact isCyclic_stabilizer_quotient_of_compatible
    (weightFibre_compatible (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T)) w

/-- Equivariance of the canonical radical projection sends every stabiliser
of a literal weight-fibre element into the stabiliser of its literal radical
class. -/
theorem weightFibre_stabilizer_le_radical_stabilizer
    (w : WeightFibre blockSource block) :
    let _ : MulAction H (WeightFibre blockSource block) :=
      rightWeightFibreMulAction
        (MulAut.conj : H →* MulAut H) blockSource block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
    let _ : MulAction E (WeightFibre blockSource block) :=
      rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
    let _ : MulAction H (RadicalClass (p := p) (H := H)) :=
      rightAutomorphismAction
        (X := RadicalClass (p := p) (H := H))
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (RadicalClass (p := p) (H := H)) :=
      rightAutomorphismAction
        (X := RadicalClass (p := p) (H := H)) phi
    let _ : MulAction (H ⋊[phi] E) (WeightFibre blockSource block) :=
      semidirectMulAction phi
        (weightFibre_compatible (iota := iota) (hinj := hinj)
          (blocks := blocks) (phi := phi) (blockSource := blockSource)
          (block := block) (T := T))
    let _ : MulAction (H ⋊[phi] E) (RadicalClass (p := p) (H := H)) :=
      semidirectMulAction phi
        (rightAutomorphismSemidirectCompatible
          (X := RadicalClass (p := p) (H := H)) phi)
    semidirectStabilizer (phi := phi) w ≤
      semidirectStabilizer (phi := phi) (fibreRadical blockSource block w) := by
  dsimp only
  letI : MulAction H (WeightFibre blockSource block) :=
    rightWeightFibreMulAction
      (MulAut.conj : H →* MulAut H) blockSource block
      (innerBlock_fixed (blockSource := blockSource) (block := block))
  letI : MulAction E (WeightFibre blockSource block) :=
    rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
  letI : MulAction H (RadicalClass (p := p) (H := H)) :=
    rightAutomorphismAction
      (X := RadicalClass (p := p) (H := H))
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (RadicalClass (p := p) (H := H)) :=
    rightAutomorphismAction
      (X := RadicalClass (p := p) (H := H)) phi
  letI : MulAction (H ⋊[phi] E) (WeightFibre blockSource block) :=
    semidirectMulAction phi
      (weightFibre_compatible (iota := iota) (hinj := hinj)
        (blocks := blocks) (phi := phi) (blockSource := blockSource)
        (block := block) (T := T))
  letI : MulAction (H ⋊[phi] E) (RadicalClass (p := p) (H := H)) :=
    semidirectMulAction phi
      (rightAutomorphismSemidirectCompatible
        (X := RadicalClass (p := p) (H := H)) phi)
  intro g hg
  change g • fibreRadical blockSource block w =
    fibreRadical blockSource block w
  rw [← fibreRadical_semidirect_equivariant (iota := iota) (hinj := hinj)
    (blocks := blocks) (phi := phi) (blockSource := blockSource)
    (block := block) (T := T), hg]

/-- On the underlying function-valued Brauer character, the canonical
semidirect action on the literal block fibre is exactly twisting by the
inverse automorphism. -/
theorem semidirect_smul_brauerFibre_val_eq_twist_inverse
    (g : H ⋊[phi] E) (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport
    let hcompat := brauerFibre_compatible (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T)
    let _ : MulAction (H ⋊[phi] E) (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction phi hcompat
    (g • psi).1 = IrreducibleBrauerCharacter.twist iota psi.1
      (semidirectToMulAut phi g⁻¹) := by
  dsimp only
  letI : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (innerBlock_fixed (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  letI : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks phi block
      T.outerBlock_fixed T.brauerBlock_transport
  let hcompat := brauerFibre_compatible (iota := iota) (hinj := hinj)
    (blocks := blocks) (phi := phi) (blockSource := blockSource)
    (block := block) (T := T)
  letI : MulAction (H ⋊[phi] E) (BrauerFibre iota hinj blocks block) :=
    semidirectMulAction phi hcompat
  exact semidirect_smul_ibr_eq_twist_inverse iota phi g psi.1

/-- Global cyclic extension for an element of the literal Brauer block
fibre.  Fixedness and cyclicity are derived from the canonical fibre action;
the root embedding and irreducible pullback character are constructed in the
kernel.  The conjugation square is also proved group theoretically, so
Navarro's cyclic extension principle is the only input. -/
theorem global_extension_brauerFibre_actual
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (innerBlock_fixed (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport
    let hcompat := brauerFibre_compatible (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T)
    let _ : MulAction (H ⋊[phi] E) (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction phi hcompat
    let hinner : ∀ h : H,
        (SemidirectProduct.inl h : H ⋊[phi] E) • psi = psi := fun h ↦ by
      rw [semidirect_inl_smul]
      exact inner_fixes_brauerFibre (iota := iota) (hinj := hinj)
        (blocks := blocks) (phi := phi) (blockSource := blockSource)
        (block := block) (T := T) h psi
    let eH := canonicalHToEmbeddedEquiv psi hinner
    let iotaEmbedded := iota.alongMulEquiv eH
    ∃ W : FDRep k (embeddedHStabilizer (phi := phi) psi),
      Representation.IsIrreducible W.ρ ∧
      pullbackPrimeRegularAlongEquiv eH psi.1.1 =
        Representation.brauerCharacterOfRootEmbedding W.ρ iotaEmbedded ∧
      Nonempty (Representation.Extension
        (embeddedHStabilizer (phi := phi) psi) W.ρ) := by
  dsimp only
  letI : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (innerBlock_fixed (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  letI : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks phi block
      T.outerBlock_fixed T.brauerBlock_transport
  let hcompat := brauerFibre_compatible (iota := iota) (hinj := hinj)
    (blocks := blocks) (phi := phi) (blockSource := blockSource)
    (block := block) (T := T)
  letI : MulAction (H ⋊[phi] E) (BrauerFibre iota hinj blocks block) :=
    semidirectMulAction phi hcompat
  have hinner : ∀ h : H,
      (SemidirectProduct.inl h : H ⋊[phi] E) • psi = psi := by
    intro h
    rw [semidirect_inl_smul]
    exact inner_fixes_brauerFibre (iota := iota) (hinj := hinj)
      (blocks := blocks) (phi := phi) (blockSource := blockSource)
      (block := block) (T := T) h psi
  let eH := canonicalHToEmbeddedEquiv psi hinner
  let iotaEmbedded := iota.alongMulEquiv eH
  have hpullback : pullbackPrimeRegularAlongEquiv eH psi.1.1 =
      PrimeRegularClassFunction.pullback eH.symm.toMonoidHom psi.1.1 := by
    apply PrimeRegularClassFunction.ext
    intro x
    rfl
  have pullbackIrreducible : IsIrreducibleBrauerCharacter iotaEmbedded
      (pullbackPrimeRegularAlongEquiv eH psi.1.1) := by
    rw [hpullback]
    exact IrreducibleBrauerCharacter.pullback_isIrreducibleBrauerCharacter
      iota eH psi.1
  let psiEmbedded : IBr iotaEmbedded :=
    ⟨pullbackPrimeRegularAlongEquiv eH psi.1.1, pullbackIrreducible⟩
  have hfixed : ∀ d : semidirectStabilizer (phi := phi) psi,
      IrreducibleBrauerCharacter.twist iotaEmbedded psiEmbedded
        (MulAut.conjNormal d) = psiEmbedded := by
    intro d
    have hdInv : ((d⁻¹ : semidirectStabilizer (phi := phi) psi) :
        H ⋊[phi] E) • psi = psi := (d⁻¹).property
    have hdVal := congrArg
      (fun z : BrauerFibre iota hinj blocks block ↦ z.1) hdInv
    have hpsi : IrreducibleBrauerCharacter.twist iota psi.1
        (semidirectToMulAut phi (d : H ⋊[phi] E)) = psi.1 := by
      rw [semidirect_smul_brauerFibre_val_eq_twist_inverse
        (iota := iota) (hinj := hinj) (blocks := blocks)
        (phi := phi) (blockSource := blockSource) (block := block)
        (T := T)] at hdVal
      simpa using hdVal
    apply Subtype.ext
    apply PrimeRegularClassFunction.ext
    intro x
    change psi.1.1
        (PrimeRegularElement.map eH.symm.toMonoidHom
          (PrimeRegularElement.map (MulAut.conjNormal d).toMonoidHom x)) =
      psi.1.1 (PrimeRegularElement.map eH.symm.toMonoidHom x)
    rw [canonicalEmbedded_conjugationSquare
      (phi := phi) psi hinner d x]
    exact congrArg
      (fun chi : IBr iota ↦ chi.1
        (PrimeRegularElement.map eH.symm.toMonoidHom x)) hpsi
  exact Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
    principle iotaEmbedded psiEmbedded
      (brauerFibre_stabilizer_quotient_cyclic
        (iota := iota) (hinj := hinj) (blocks := blocks)
        (phi := phi) (blockSource := blockSource) (block := block)
        (T := T) psi)
      hfixed

end FibreTransportSource

end ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
