import ModularRep.PaperProofs.TypeBSpinBroueMichelCarriers
import ModularRep.PaperProofs.TypeBOrdinaryBlockSplitting
import ModularRep.PaperProofs.TypeBRankThreeJordanPacketCarriers

/-!
# A fixed-label specified Levi block union

The original finite group and its actual rational dual Levi are explicit.
The rational family is indexed by conjugacy classes with defining-prime
regular representatives. The full union uses literal commuting two-elements
and their products with the prescribed label. Its finite primitive block sum
is constructed from the same ordinary selector and stable decomposition data.

Only closure of this one ordinary union on its specified blocks is sourced.
The algebraic meaning of the dual group, rational family and paired Levi,
and their common coefficient realization, remain explicit source obligations.
No full partition, packet map, block subset or actor invariance is supplied.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra BigOperators

namespace ModularRep.PaperProofs.TypeBRankThreeJordanLeviPacket

open ModularRep OrdinaryIrreducibleCharacter FDRepSimpleClassKZero
open TypeBOrdinaryBlockSplitting TypeBRationalSeriesSource

attribute [local instance] Classical.propDecidable

section DualLabels

variable (p : ℕ) (Dstar : Type) [Group Dstar]

/-- The literal rational semisimple classes in the prescribed dual group. -/
def FullRationalIndex : Type :=
  {c : ConjClasses Dstar //
    ∃ s : Dstar, ConjClasses.mk s = c ∧ p.Coprime (orderOf s)}

/-- Actual two-elements in the centralizer of the fixed label. -/
abbrev CentralizerTwoElement (s : Dstar) :=
  {t : Subgroup.centralizer ({s} : Set Dstar) //
    ∃ a : ℕ, orderOf (t.val : Dstar) = 2 ^ a}

variable {p Dstar}

theorem centralizerTwoElement_commute (s : Dstar) (t : CentralizerTwoElement Dstar s) :
    Commute s (t.val : Dstar) :=
  (Subgroup.mem_centralizer_singleton_iff.mp t.val.property).symm

theorem centralizerTwoElement_regular (hp : p.Prime) (hne : 2 ≠ p)
    (s : Dstar) (t : CentralizerTwoElement Dstar s) :
    p.Coprime (orderOf (t.val : Dstar)) := by
  obtain ⟨a, ha⟩ := t.property
  rw [ha]
  exact ((Nat.coprime_primes hp Nat.prime_two).mpr hne.symm).pow_right a

/-- The product stays defining-prime regular by its literal commuting square. -/
theorem product_regular (hp : p.Prime) (hne : 2 ≠ p)
    (s : Dstar) (regular : p.Coprime (orderOf s))
    (t : CentralizerTwoElement Dstar s) :
    p.Coprime (orderOf (s * (t.val : Dstar))) :=
  (regular.mul_right (centralizerTwoElement_regular hp hne s t)).of_dvd_right
    (centralizerTwoElement_commute s t).orderOf_mul_dvd_mul_orderOf

def productIndex (hp : p.Prime) (hne : 2 ≠ p)
    (s : Dstar) (regular : p.Coprime (orderOf s))
    (t : CentralizerTwoElement Dstar s) : FullRationalIndex p Dstar :=
  ⟨ConjClasses.mk (s * (t.val : Dstar)), s * (t.val : Dstar), rfl,
    product_regular hp hne s regular t⟩

@[simp] theorem productIndex_val (hp : p.Prime) (hne : 2 ≠ p)
    (s : Dstar) (regular : p.Coprime (orderOf s))
    (t : CentralizerTwoElement Dstar s) :
    (productIndex hp hne s regular t).val = ConjClasses.mk (s * (t.val : Dstar)) := rfl

end DualLabels

section PhysicalUnion

variable {p : ℕ} {L Dstar K O k : Type}
  [Group L] [Finite L] [Group Dstar]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]

/-- The full fixed-label union, including all commuting two-elements. -/
def ordinaryUnion
    (family : RationalSeriesSource K L (FullRationalIndex p Dstar))
    (hp : p.Prime) (hne : 2 ≠ p) (s : Dstar)
    (regular : p.Coprime (orderOf s)) (chi : Irr K L) : Prop :=
  ∃ t : CentralizerTwoElement Dstar s,
    chi ∈ family.rationalSeries (productIndex hp hne s regular t)

variable (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K L)
  [Fintype (LiteralPrimitiveBlock k L)]
  (blocks : BlockIdempotentDecomposition (fun c : LiteralPrimitiveBlock k L => c.val))
  [HasEnoughRootsOfUnity K (Nat.card L)]
  (ordinary : OrdinaryBlockSource Msys root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks)
  (family : RationalSeriesSource K L (FullRationalIndex p Dstar))
  (hp : p.Prime) (hne : 2 ≠ p) (s : Dstar) (regular : p.Coprime (orderOf s))

/-- The fixed-label Broue--Michel input concerns only ordinary block closure. -/
structure BlockClosureCertificate : Prop where
  blockClosed : ∀ chi psi : Irr K L,
    ordinary.physical.ordinaryBlock chi = ordinary.physical.ordinaryBlock psi →
      ordinaryUnion family hp hne s regular chi →
        ordinaryUnion family hp hne s regular psi

/-- Primitive support is determined by actual ordinary characters in this union. -/
def blocksAt : Finset (LiteralPrimitiveBlock k L) := by
  classical
  exact Finset.univ.filter fun c => ∃ chi : Irr K L,
    ordinaryUnion family hp hne s regular chi ∧ ordinary.physical.ordinaryBlock chi = c

theorem mem_blocksAt (c : LiteralPrimitiveBlock k L) :
    c ∈ blocksAt Msys root blocks ordinary family hp hne s regular ↔
      ∃ chi : Irr K L, ordinaryUnion family hp hne s regular chi ∧
        ordinary.physical.ordinaryBlock chi = c := by
  classical
  simp only [blocksAt, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The exact modular idempotent is computed from this primitive support. -/
def idempotent : k[L] :=
  ∑ c ∈ blocksAt Msys root blocks ordinary family hp hne s regular, c.val

theorem mul_idempotent (c : LiteralPrimitiveBlock k L) :
    c.val * idempotent Msys root blocks ordinary family hp hne s regular =
      if c ∈ blocksAt Msys root blocks ordinary family hp hne s regular
      then c.val else 0 := by
  classical
  by_cases hc : c ∈ blocksAt Msys root blocks ordinary family hp hne s regular
  · rw [if_pos hc]
    exact blocks.complete.toCompleteOrthogonalIdempotents.toOrthogonalIdempotents.mul_sum_of_mem hc
  · rw [if_neg hc]
    exact blocks.complete.toCompleteOrthogonalIdempotents.toOrthogonalIdempotents.mul_sum_of_notMem hc

theorem support_iff (c : LiteralPrimitiveBlock k L) :
    c.val * idempotent Msys root blocks ordinary family hp hne s regular = c.val ↔
      c ∈ blocksAt Msys root blocks ordinary family hp hne s regular := by
  classical
  rw [mul_idempotent]
  by_cases hc : c ∈ blocksAt Msys root blocks ordinary family hp hne s regular
  · simp [hc]
  · simp [hc, Ne.symm c.property.ne_zero]

theorem idempotent_central :
    IsMulCentral (idempotent Msys root blocks ordinary family hp hne s regular) := by
  refine ⟨?_, fun x y => (mul_assoc _ x y).symm, fun x y => mul_assoc x y _⟩
  intro x
  change idempotent Msys root blocks ordinary family hp hne s regular * x =
    x * idempotent Msys root blocks ordinary family hp hne s regular
  simp only [idempotent, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact (c.property.central.comm x).eq

theorem idempotent_idempotent :
    IsIdempotentElem (idempotent Msys root blocks ordinary family hp hne s regular) :=
  blocks.complete.toCompleteOrthogonalIdempotents.toOrthogonalIdempotents.isIdempotentElem_sum

/-- Closure makes the existential block support equivalent to membership of
every actual ordinary character in that block. -/
theorem ordinary_mem_iff
    (closure : BlockClosureCertificate Msys root blocks ordinary family hp hne s regular)
    (chi : Irr K L) :
    ordinaryUnion family hp hne s regular chi ↔
      ordinary.physical.ordinaryBlock chi ∈
        blocksAt Msys root blocks ordinary family hp hne s regular := by
  rw [mem_blocksAt]
  constructor
  · intro hchi
    exact ⟨chi, hchi, rfl⟩
  · rintro ⟨psi, hpsi, hblock⟩
    exact closure.blockClosed psi chi hblock hpsi

/-- The same specified ordinary union characterizes the constructed idempotent. -/
theorem ordinary_support_iff
    (closure : BlockClosureCertificate Msys root blocks ordinary family hp hne s regular)
    (chi : Irr K L) :
    (ordinary.physical.ordinaryBlock chi).val *
        idempotent Msys root blocks ordinary family hp hne s regular =
      (ordinary.physical.ordinaryBlock chi).val ↔
        ordinaryUnion family hp hne s regular chi := by
  rw [support_iff]
  exact (ordinary_mem_iff Msys root blocks ordinary family hp hne s regular closure chi).symm

end PhysicalUnion

end ModularRep.PaperProofs.TypeBRankThreeJordanLeviPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
