import ModularRep.PaperProofs.OddConlonOrbitAssembly
import Formalisation.C2Cancellation

/-! Construct representative fibre equivalences from actual total and
fixed-point counts when the two carrier actions factor through an
involution. Block orbits may be fixed or exchanged. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNumericalOrbitAssembly

open ModularRep.BlockFibreRestriction
open ModularRep.PaperProofs.OddConlonOrbitAssembly

universe u

variable {A Block X Y : Type u}
variable [Group A] [MulAction A Block]
variable [MulAction A X] [MulAction A Y]

def fibrePerm
    {W : Type u} [MulAction A W]
    (block : W → Block)
    (hblock : ∀ (a : A) (w : W), block (a • w) = a • block w)
    (a : A) (b : Block) (hb : a • b = b) :
    Equiv.Perm (BlockFibre block b) :=
  RepresentativeEquivFamily.fibreActionEquiv block hblock a b b hb

def fixedFibreActionEquiv
    {W : Type u} [MulAction A W]
    (block : W → Block)
    (hblock : ∀ (a : A) (w : W), block (a • w) = a • block w)
    (a : A) (b : Block) (hb : a • b = b) :
    Function.fixedPoints (fibrePerm block hblock a b hb) ≃
      {w : W // block w = b ∧ a • w = w} where
  toFun x := ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
  invFun w := ⟨⟨w.1, w.2.1⟩, Subtype.ext w.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

theorem representativeEquivExists
    (blockX : X → Block) (blockY : Y → Block)
    (hblockX : ∀ (a : A) (x : X), blockX (a • x) = a • blockX x)
    (hblockY : ∀ (a : A) (y : Y), blockY (a • y) = a • blockY y)
    (finiteX : ∀ b : Block, Finite (BlockFibre blockX b))
    (finiteY : ∀ b : Block, Finite (BlockFibre blockY b))
    (t : A)
    (htX : Function.Involutive (fun x : X => t • x))
    (htY : Function.Involutive (fun y : Y => t • y))
    (actionCases : ∀ a : A,
      ((∀ x : X, a • x = x) ∧ (∀ y : Y, a • y = y)) ∨
      ((∀ x : X, a • x = t • x) ∧ (∀ y : Y, a • y = t • y)))
    (totalEq : ∀ b : Block,
      Nat.card (BlockFibre blockX b) = Nat.card (BlockFibre blockY b))
    (fixedEq : ∀ b : Block, t • b = b →
      Nat.card {x : X // blockX x = b ∧ t • x = x} =
        Nat.card {y : Y // blockY y = b ∧ t • y = y}) :
    RepresentativeEquivExists blockX blockY hblockX := by
  classical
  intro omega
  let b : Block := orbitRepresentative omega
  let : Finite (BlockFibre blockX b) := finiteX b
  let : Finite (BlockFibre blockY b) := finiteY b
  let : Fintype (BlockFibre blockX b) := Fintype.ofFinite _
  let : Fintype (BlockFibre blockY b) := Fintype.ofFinite _
  have hcard : Fintype.card (BlockFibre blockX b) = Fintype.card (BlockFibre blockY b) := by
    simpa only [Nat.card_eq_fintype_card] using totalEq b
  have hlocal :
      ∃ e : BlockFibre blockX b ≃ BlockFibre blockY b,
        ∀ (a : A) (ha : a • b = b) (x : BlockFibre blockX b),
          e (fibrePerm blockX hblockX a b ha x) =
            fibrePerm blockY hblockY a b ha (e x) := by
    by_cases htb : t • b = b
    · let sigmaX := fibrePerm blockX hblockX t b htb
      let sigmaY := fibrePerm blockY hblockY t b htb
      have hsigmaX : Function.Involutive sigmaX := by
        intro x
        apply Subtype.ext
        exact htX x.1
      have hsigmaY : Function.Involutive sigmaY := by
        intro y
        apply Subtype.ext
        exact htY y.1
      have hfixedNat : Nat.card (Function.fixedPoints sigmaX) =
          Nat.card (Function.fixedPoints sigmaY) := by
        calc
          Nat.card (Function.fixedPoints sigmaX) =
              Nat.card {x : X // blockX x = b ∧ t • x = x} :=
            Nat.card_congr (fixedFibreActionEquiv blockX hblockX t b htb)
          _ = Nat.card {y : Y // blockY y = b ∧ t • y = y} := fixedEq b htb
          _ = Nat.card (Function.fixedPoints sigmaY) :=
            (Nat.card_congr (fixedFibreActionEquiv blockY hblockY t b htb)).symm
      have hfixed : Fintype.card (Function.fixedPoints sigmaX) =
          Fintype.card (Function.fixedPoints sigmaY) := by
        simpa only [Nat.card_eq_fintype_card] using hfixedNat
      obtain ⟨e, he⟩ :=
        Formalisation.C2Cancellation.exists_equivariantEquiv_of_card_eq_of_fixed_card_eq
          sigmaX sigmaY hsigmaX hsigmaY hcard hfixed
      refine ⟨e, ?_⟩
      intro a ha x
      rcases actionCases a with ⟨haX, haY⟩ | ⟨haX, haY⟩
      · have hx : fibrePerm blockX hblockX a b ha x = x := Subtype.ext (haX x.1)
        have hy : fibrePerm blockY hblockY a b ha (e x) = e x := Subtype.ext (haY (e x).1)
        rw [hx, hy]
      · have hx : fibrePerm blockX hblockX a b ha x = sigmaX x := Subtype.ext (haX x.1)
        have hy : fibrePerm blockY hblockY a b ha (e x) = sigmaY (e x) :=
          Subtype.ext (haY (e x).1)
        rw [hx, hy]
        exact he x
    · let e : BlockFibre blockX b ≃ BlockFibre blockY b := Fintype.equivOfCardEq hcard
      refine ⟨e, ?_⟩
      intro a ha x
      rcases actionCases a with ⟨haX, haY⟩ | ⟨haX, haY⟩
      · have hx : fibrePerm blockX hblockX a b ha x = x := Subtype.ext (haX x.1)
        have hy : fibrePerm blockY hblockY a b ha (e x) = e x := Subtype.ext (haY (e x).1)
        rw [hx, hy]
      · have hcontr : t • b = b := by
          calc
            t • b = blockX (t • x.1) := by rw [hblockX, x.2]
            _ = blockX (a • x.1) := congrArg blockX (haX x.1).symm
            _ = b := by rw [hblockX, x.2, ha]
        exact (htb hcontr).elim
  obtain ⟨e, he⟩ := hlocal
  refine ⟨e, ?_⟩
  intro a ha x
  exact congrArg Subtype.val (he a ha x)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNumericalOrbitAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
