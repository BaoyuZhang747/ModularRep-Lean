import ModularRep.Navarro417DefectSource
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedBlockSector

/-! The remaining Fi24 numerical joins under explicit literature/table bindings.
The cyclic source is restricted to actual cyclic defects. The five-prime rows
are the seven selected noncyclic contributions, not whole-group totals.
The seven-prime noncyclic counts are derived by central-sector cancellation. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation
open SporadicFi24P3Definition44NamedCarrierFixedBlockSector
universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
local notation "B" => ActualBlock (k := k) (X := X)
local notation "W" => WeightClass (p := p) (K := K) (X := X)
local notation "f" => operationsBlock iota hinj R
abbrev weightBlockMap (w : W) : B := R.1.weightBlock w
local notation "g" => (weightBlockMap R : W → B)
local notation "BC" => fun b : B => Nat.card {phi : IBr iota // f phi = b}
local notation "WC" => fun b : B => Nat.card {w : W // g w = b}

def HasCyclicDefect (b : B) : Prop :=
  letI : Fact p.Prime := ⟨iota.prime⟩
  letI := R.1.operations.ambientBlockData.fintypeBlock
  ∃ D : Subgroup X,
    Navarro411DefectRepresentative
      (p := p) R.1.operations.ambientBlockData.blocks b D ∧ IsCyclic D

variable (tau : MulAut X)
local notation "BF" => fun b : B => Nat.card {phi : IBr iota //
  f phi = b ∧ MulOpposite.op tau • phi = phi}
local notation "WF" => fun b : B => Nat.card {w : W //
  g w = b ∧ MulOpposite.op tau • w = w}

/-- Accepted numerical consequences of the independently published cyclic-block
result, with the actual cyclic-defect guard and literal stabilizer action. -/
structure CyclicNumericalData where
  count : B → ℕ
  fixedCount : B → ℕ
  brauer_card : ∀ b, HasCyclicDefect iota R b → BC b = count b
  weight_card : ∀ b, HasCyclicDefect iota R b → WC b = count b
  brauer_fixed_card : ∀ b, HasCyclicDefect iota R b →
    MulOpposite.op tau • b = b → BF b = fixedCount b
  weight_fixed_card : ∀ b, HasCyclicDefect iota R b →
    MulOpposite.op tau • b = b → WF b = fixedCount b

/-- Intended at 11,13,17,23,29 with the accepted actual block census. -/
theorem actual_counts_of_cyclic_blocks
    (S : CyclicNumericalData iota hinj R tau)
    (allCyclic : ∀ b : B, HasCyclicDefect iota R b) :
    ActualBlockC2Counts iota hinj R tau := by
  constructor
  · intro b
    exact (S.brauer_card b (allCyclic b)).trans (S.weight_card b (allCyclic b)).symm
  · intro b hb
    exact (S.brauer_fixed_card b (allCyclic b) hb).trans
      (S.weight_fixed_card b (allCyclic b) hb).symm

/-- Printed role order 1,2,3,45,46,47,48. -/
def fiveCount : Fin 7 → ℕ := ![16, 14, 16, 16, 16, 14, 14]
def fiveTrivialFixedCount : Fin 3 → ℕ := ![16, 6, 16]
/-- The literal outer action, with its inverse checked on all seven roles. -/
def fiveOuter : Equiv.Perm (Fin 7) where
  toFun := ![0, 1, 2, 4, 3, 6, 5]
  invFun := ![0, 1, 2, 4, 3, 6, 5]
  left_inv := by decide
  right_inv := by decide
def fiveTrivialIndex (i : Fin 3) : Fin 7 :=
  ⟨i.val, lt_trans i.isLt (by decide : 3 < 7)⟩
private theorem fiveOuter_fixed_lt_three :
    ∀ i : Fin 7, fiveOuter i = i → i.val < 3 := by decide

/-- Seven literal noncyclic rows and the exhaustive cyclic complement. -/
theorem actual_counts_of_five_literal_rows
    (S : CyclicNumericalData iota hinj R tau)
    (roles : Fin 7 → B) (roles_injective : Function.Injective roles)
    (coverage : ∀ b : B, (∃ i : Fin 7, roles i = b) ∨ HasCyclicDefect iota R b)
    (role_action : ∀ i : Fin 7, MulOpposite.op tau • roles i = roles (fiveOuter i))
    (brauer_counts : ∀ i : Fin 7, BC (roles i) = fiveCount i)
    (weight_counts : ∀ i : Fin 7, WC (roles i) = fiveCount i)
    (brauer_fixed_counts : ∀ i : Fin 3,
      BF (roles (fiveTrivialIndex i)) = fiveTrivialFixedCount i)
    (weight_fixed_counts : ∀ i : Fin 3,
      WF (roles (fiveTrivialIndex i)) = fiveTrivialFixedCount i) :
    ActualBlockC2Counts iota hinj R tau := by
  constructor
  · intro b
    rcases coverage b with ⟨i, rfl⟩ | hcyclic
    · exact (brauer_counts i).trans (weight_counts i).symm
    · exact (S.brauer_card b hcyclic).trans (S.weight_card b hcyclic).symm
  · intro b hb
    rcases coverage b with ⟨i, rfl⟩ | hcyclic
    · have hi : fiveOuter i = i := roles_injective ((role_action i).symm.trans hb)
      let j : Fin 3 := ⟨i.val, fiveOuter_fixed_lt_three i hi⟩
      have hji : fiveTrivialIndex j = i := Fin.ext rfl
      simpa only [hji] using
        (brauer_fixed_counts j).trans (weight_fixed_counts j).symm
    · exact (S.brauer_fixed_card b hcyclic hb).trans (S.weight_fixed_card b hcyclic hb).symm

section Seven
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable [weightFinite : Finite (CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X))]
include weightFinite

/-- Sector totals and the whole trivial-sector fixed total are accepted AD/table
bindings. Both distinguished-block equalities are deduced by cancellation. -/
theorem actual_counts_of_seven_sector_cancellation
    (S : CyclicNumericalData iota hinj R tau)
    (hcenter : Nat.card (Subgroup.center X) = 3)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (distinguished : CentralSector (k := k) (X := X) → B)
    (distinguished_sector : ∀ nu, blockSector (distinguished nu) = nu)
    (cyclic_complement : ∀ nu (b : B), blockSector b = nu →
      b ≠ distinguished nu → HasCyclicDefect iota R b)
    (sectorCount : CentralSector (k := k) (X := X) → ℕ)
    (brauer_sector_counts : ∀ nu,
      Nat.card {phi : IBr iota // blockSector (f phi) = nu} = sectorCount nu)
    (weight_sector_counts : ∀ nu,
      Nat.card {w : W // blockSector (g w) = nu} = sectorCount nu)
    (trivialFixedCount : ℕ)
    (brauer_trivial_fixed : Nat.card {phi : IBr iota //
      blockSector (f phi) = 1 ∧ MulOpposite.op tau • phi = phi} = trivialFixedCount)
    (weight_trivial_fixed : Nat.card {w : W //
      blockSector (g w) = 1 ∧ MulOpposite.op tau • w = w} = trivialFixedCount) :
    ActualBlockC2Counts iota hinj R tau := by
  classical
  let : Fintype W := Fintype.ofFinite W
  let : Fintype B := R.1.operations.ambientBlockData.fintypeBlock
  have htotal : ∀ nu, BC (distinguished nu) = WC (distinguished nu) := by
    intro nu
    have h := supportedFixed_fibre_card_eq (A := IBr iota) (C := W) («B» := ActualBlock (k := k) (X := X)) f g (fun b : B => blockSector b = nu)
      (fun _ : IBr iota => True) (fun _ : W => True)
      (distinguished nu) (distinguished_sector nu)
      (by simpa only [and_true] using
        (brauer_sector_counts nu).trans (weight_sector_counts nu).symm)
      (fun b hb hne => by
        have hc := cyclic_complement nu b hb hne
        simpa only [and_true] using (S.brauer_card b hc).trans (S.weight_card b hc).symm)
    simpa only [and_true] using h
  have hfixed : BF (distinguished 1) = WF (distinguished 1) := by
    apply supportedFixed_fibre_card_eq (A := IBr iota) (C := W) («B» := ActualBlock (k := k) (X := X)) f g (fun b : B => blockSector b = 1)
      (fun phi : IBr iota => MulOpposite.op tau • phi = phi)
      (fun w : W => MulOpposite.op tau • w = w)
      (distinguished 1) (distinguished_sector 1)
      (brauer_trivial_fixed.trans weight_trivial_fixed.symm)
    intro b hb hne
    have hc := cyclic_complement 1 b hb hne
    by_cases hstable : MulOpposite.op tau • b = b
    · exact (S.brauer_fixed_card b hc hstable).trans (S.weight_fixed_card b hc hstable).symm
    · let _ : IsEmpty {phi : IBr iota // f phi = b ∧ MulOpposite.op tau • phi = phi} :=
        ⟨fun x => by
          have ht : f (MulOpposite.op tau • x.1) = MulOpposite.op tau • f x.1 :=
            operationsBrauerSupport (iota := iota) (hinj := hinj) R (MulOpposite.op tau) x.1
          have hxblock : f x.1 = b := x.2.1
          have hxfix : MulOpposite.op tau • x.1 = x.1 := x.2.2
          exact hstable (by simpa only [hxblock, hxfix] using ht.symm)⟩
      let _ : IsEmpty {w : W // g w = b ∧ MulOpposite.op tau • w = w} :=
        ⟨fun x => by
          have ht : g (MulOpposite.op tau • x.1) = MulOpposite.op tau • g x.1 :=
            R.1.weightBlock_transport (MulOpposite.op tau) x.1
          have hxblock : g x.1 = b := x.2.1
          have hxfix : MulOpposite.op tau • x.1 = x.1 := x.2.2
          exact hstable (by simpa only [hxblock, hxfix] using ht.symm)⟩
      simp
  constructor
  · intro b
    by_cases hb : b = distinguished (blockSector b)
    · calc
        BC b = BC (distinguished (blockSector b)) := congrArg BC hb
        _ = WC (distinguished (blockSector b)) := htotal (blockSector b)
        _ = WC b := congrArg WC hb.symm
    · have hc := cyclic_complement (blockSector b) b rfl hb
      exact (S.brauer_card b hc).trans (S.weight_card b hc).symm
  · intro b hb
    have hsector : blockSector b = 1 :=
      centralCharacterSector_eq_one_of_fixed tau hcenter hinverts b hb
    by_cases heq : b = distinguished 1
    · simpa only [heq] using hfixed
    · have hc := cyclic_complement 1 b hsector heq
      exact (S.brauer_fixed_card b hc hb).trans (S.weight_fixed_card b hc hb).symm
end Seven
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
