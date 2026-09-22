import Mathlib.Data.Set.Image
import ModularRep.OrdinaryIrreducibleCharacter

/-!
# Literal fibres of function-valued ordinary irreducible characters

This neutral module constructs character inflation along a surjective
group homomorphism and the literal fibres of any supplied ordinary-block
selector.  Fibre-label injectivity is derived from selector surjectivity; it
is not a source field.

The file assigns no block to a character and imports no modular-character,
block-induction, weight, or paper-proof API.
-/

noncomputable section

namespace ModularRep.OrdinaryIrreducibleCharacter

universe u

/-- Inflate a function-valued ordinary irreducible character along a
surjective group homomorphism. -/
noncomputable def inflateAlong
    {K CoverG QuotientG : Type u}
    [Field K] [CharZero K] [Group CoverG] [Group QuotientG]
    (pi : CoverG →* QuotientG) (hpi : Function.Surjective pi)
    (chi : Irr K QuotientG) : Irr K CoverG := by
  refine ⟨fun x => chi (pi x), ?_⟩
  rcases chi.2 with ⟨R⟩
  refine ⟨
    { dimension := R.dimension
      representation := R.representation.pullback pi
      irreducible := R.irreducible.pullback pi hpi
      character_eq := ?_ }⟩
  funext x
  change R.representation.character (pi x) = chi (pi x)
  exact congrFun R.character_eq (pi x)

@[simp]
theorem inflateAlong_apply
    {K CoverG QuotientG : Type u}
    [Field K] [CharZero K] [Group CoverG] [Group QuotientG]
    (pi : CoverG →* QuotientG) (hpi : Function.Surjective pi)
    (chi : Irr K QuotientG) (x : CoverG) :
    inflateAlong pi hpi chi x = chi (pi x) :=
  rfl

/-- Inflation is injective when the underlying group homomorphism is
surjective. -/
theorem inflateAlong_injective
    {K CoverG QuotientG : Type u}
    [Field K] [CharZero K] [Group CoverG] [Group QuotientG]
    (pi : CoverG →* QuotientG) (hpi : Function.Surjective pi) :
    Function.Injective (inflateAlong (K := K) pi hpi) := by
  intro chi psi h
  apply OrdinaryIrreducibleCharacter.ext
  intro q
  obtain ⟨x, rfl⟩ := hpi q
  simpa only [inflateAlong_apply] using
    congrArg (fun eta : Irr K CoverG => eta x) h

end ModularRep.OrdinaryIrreducibleCharacter

namespace ModularRep.OrdinaryBlockFibre

open ModularRep.OrdinaryIrreducibleCharacter

universe u v w

/-- The literal set of ordinary irreducible characters assigned a supplied
block label. -/
def ordinaryBlockFibreSet
    {K G : Type u} {Block : Type v}
    [Field K] [CharZero K] [Group G]
    (blockOf : Irr K G -> Block) (b : Block) : Set (Irr K G) :=
  {chi | blockOf chi = b}

/-- The subtype carrier of one literal ordinary-character block fibre. -/
abbrev OrdinaryBlockFibre
    {K G : Type u} {Block : Type v}
    [Field K] [CharZero K] [Group G]
    (blockOf : Irr K G -> Block) (b : Block) :=
  {chi : Irr K G // blockOf chi = b}

/-- A surjective ordinary-block selector has injectively labelled literal
fibres.  Surjectivity is essential because unused labels otherwise have the
same empty fibre. -/
theorem ordinaryBlockFibreSet_injective
    {K G : Type u} {Block : Type v}
    [Field K] [CharZero K] [Group G]
    (blockOf : Irr K G -> Block)
    (hblockOf : Function.Surjective blockOf) :
    Function.Injective (ordinaryBlockFibreSet blockOf) := by
  intro b c h
  obtain ⟨chi, hchi⟩ := hblockOf b
  have hb : chi ∈ ordinaryBlockFibreSet blockOf b := by
    change blockOf chi = b
    exact hchi
  have hc : chi ∈ ordinaryBlockFibreSet blockOf c := by
    rw [← h]
    exact hb
  change blockOf chi = c at hc
  exact hchi.symm.trans hc

/-- An injective carrier map preserves injective labelling of image
fibres. -/
theorem imageOrdinaryBlockFibreSet_injective
    {K G : Type u} {Block : Type v} {Target : Type w}
    [Field K] [CharZero K] [Group G]
    (blockOf : Irr K G -> Block) (f : Irr K G -> Target)
    (hblockOf : Function.Surjective blockOf)
    (hf : Function.Injective f) :
    Function.Injective
      (fun b => Set.image f (ordinaryBlockFibreSet blockOf b)) :=
  hf.image_injective.comp
    (ordinaryBlockFibreSet_injective blockOf hblockOf)

end ModularRep.OrdinaryBlockFibre


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
