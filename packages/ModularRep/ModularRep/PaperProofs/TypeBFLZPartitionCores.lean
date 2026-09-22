import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Relation

/-!
# Literal partition labels and terminal hook removal

The label carrier is the actual mathlib partition, including its size.
A finite beta set is decoded in increasing order by subtracting the index
and deleting zero parts. An e-hook removes j and inserts j-e, with the
literal membership, positivity and vacancy guards.

The only routine external input is existence and uniqueness of the terminal
partition reached by this exact hook relation. It is intended to instantiate
Olsson Section 3 on these literal carriers; no arbitrary core map, action,
block classification or manuscript target is a certificate field.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZPartitionCores

/-- All ordinary partitions with their actual size, rather than an abstract
label type. The fixed-size fibre is exactly Nat.Partition n. -/
abbrev Partition := Sigma Nat.Partition

/-- Ascending beta numbers b_i encode the nonnegative entries b_i-i.
The ordinary partition constructor below removes zero entries. -/
def betaValues (B : Finset ℕ) : Multiset ℕ :=
  ((B.sort (· ≤ ·)).mapIdx (fun i b => b - i) : List ℕ)

/-- Decode a literal beta set into an actual partition and its size. -/
def betaPartition (B : Finset ℕ) : Partition :=
  ⟨(betaValues B).sum, Nat.Partition.ofMultiset (betaValues B)⟩

@[simp]
theorem betaPartition_size (B : Finset ℕ) :
    (betaPartition B).1 = (betaValues B).sum := rfl

/-- Zero beta entries correspond to omitted zero parts, as in the standard
beta-set convention for ordinary partitions. -/
@[simp]
theorem betaPartition_parts (B : Finset ℕ) :
    (betaPartition B).2.parts = (betaValues B).filter (· ≠ 0) := rfl

/-- Replace a beta number by the number e places below it. The relation
below separately supplies source membership and destination vacancy. -/
def removeHook (B : Finset ℕ) (j e : ℕ) : Finset ℕ :=
  insert (j - e) (B.erase j)

/-- An actual e-hook step on literal ordinary partitions. Representatives
are finite beta sets and both decoded endpoint partitions are specified. -/
def HookStep (e : ℕ) (mu kappa : Partition) : Prop :=
  ∃ (B : Finset ℕ) (j : ℕ),
    0 < e ∧ j ∈ B ∧ e ≤ j ∧ j - e ∉ B ∧
      betaPartition B = mu ∧ betaPartition (removeHook B j e) = kappa

/-- Being a core means no literal e-hook step is available. -/
def IsCore (e : ℕ) (kappa : Partition) : Prop :=
  ∀ nu : Partition, ¬ HookStep e kappa nu

/-- Terminal hook removal records a finite sequence of actual e-hooks and
the terminal absence of further hooks. -/
def TerminalCore (e : ℕ) (mu kappa : Partition) : Prop :=
  Relation.ReflTransGen (HookStep e) mu kappa ∧ IsCore e kappa

theorem terminalCore_self {e : ℕ} {kappa : Partition} (h : IsCore e kappa) :
    TerminalCore e kappa kappa := ⟨Relation.ReflTransGen.refl, h⟩

/-- E1: the standard partition-core removal theorem, on the exact beta-set
relation above and with positive hook length. Its canonical source/model
identification is audited separately; it contains no supplied core map. -/
structure CoreRemovalCertificate (e : ℕ) where
  positive : 0 < e
  terminal_unique : ∀ mu : Partition, ∃! kappa : Partition, TerminalCore e mu kappa

variable {e : ℕ} (source : CoreRemovalCertificate e)

/-- Choose the uniquely determined actual terminal partition. -/
def takeCore (mu : Partition) : Partition :=
  Classical.choose (source.terminal_unique mu).exists

/-- The chosen value is reached by the literal hook steps and is terminal. -/
theorem takeCore_spec (mu : Partition) : TerminalCore e mu (takeCore source mu) :=
  Classical.choose_spec (source.terminal_unique mu).exists

/-- No distinct terminal partition is compatible with the same input. -/
theorem takeCore_unique (mu kappa : Partition) (h : TerminalCore e mu kappa) :
    takeCore source mu = kappa :=
  (source.terminal_unique mu).unique (takeCore_spec source mu) h

/-- Core extraction fixes a partition which is already terminal. -/
theorem takeCore_of_isCore (kappa : Partition) (h : IsCore e kappa) :
    takeCore source kappa = kappa :=
  takeCore_unique source kappa kappa (terminalCore_self h)

/-- Applying the canonical extraction twice has no further effect. -/
theorem takeCore_idempotent (mu : Partition) :
    takeCore source (takeCore source mu) = takeCore source mu :=
  takeCore_of_isCore source (takeCore source mu) (takeCore_spec source mu).2

/-- A finite initial sequence of hooks leaves the same terminal core. -/
theorem takeCore_eq_of_reachable (mu nu : Partition)
    (h : Relation.ReflTransGen (HookStep e) mu nu) :
    takeCore source mu = takeCore source nu :=
  takeCore_unique source mu (takeCore source nu)
    ⟨h.trans (takeCore_spec source nu).1, (takeCore_spec source nu).2⟩

end ModularRep.PaperProofs.TypeBFLZPartitionCores


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
