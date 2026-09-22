import ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources

/-!
# The Fischer prime-three block catalogue from an injection and its size

The earlier source interface identifies the three named block roles with the
complete literal block-index type by an equivalence.  This file weakens that
boundary.  A source need only identify three distinct literal block indices
and certify that the complete literal catalogue has the number of entries
printed in `fi24blocks.out`.  Lean checks that the printed number is three and
deduces surjectivity of the role map by finite cardinality.

No character, weight, automorphism, or iBAW conclusion is used in this finite
catalogue argument.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3BlockIndexBindingFromCardinality

open ModularRep.PaperProofs.SporadicFi24P3AmbientDefectTranscript
open ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources

universe u

/-- The complete ambient prime-three block count parsed from the `blocks=`
field of the canonical transcript. -/
def fi24P3BlockCountFromTranscript : Nat :=
  fi24P3AmbientBlockCountFromTranscript

theorem fi24P3BlockCountFromTranscript_eq_three :
    fi24P3BlockCountFromTranscript = 3 := by
  exact fi24P3AmbientBlockCount_exact

theorem fi24P3BlockRole_card : Fintype.card Fi24P3BlockRole = 3 := by
  decide

/-- A source-facing allocation of the three named roles to distinct literal
block indices, together with the independently parsed size of the complete
index catalogue.  Exhaustiveness is deliberately not a field. -/
structure Fi24P3BlockIndexInjectionSource (BlockIndex : Type u)
    [Fintype BlockIndex] where
  roleIndex : Fi24P3BlockRole → BlockIndex
  roleIndex_injective : Function.Injective roleIndex
  blockCount_eq_transcript :
    Fintype.card BlockIndex = fi24P3BlockCountFromTranscript

namespace Fi24P3BlockIndexInjectionSource

variable {BlockIndex : Type u} [Fintype BlockIndex]

theorem role_card_eq_block_card
    (S : Fi24P3BlockIndexInjectionSource BlockIndex) :
    Fintype.card Fi24P3BlockRole = Fintype.card BlockIndex := by
  calc
    Fintype.card Fi24P3BlockRole = 3 := fi24P3BlockRole_card
    _ = fi24P3BlockCountFromTranscript :=
      fi24P3BlockCountFromTranscript_eq_three.symm
    _ = Fintype.card BlockIndex := S.blockCount_eq_transcript.symm

theorem roleIndex_bijective
    (S : Fi24P3BlockIndexInjectionSource BlockIndex) :
    Function.Bijective S.roleIndex :=
  (Fintype.bijective_iff_injective_and_card S.roleIndex).2
    ⟨S.roleIndex_injective, S.role_card_eq_block_card⟩

/-- The old equivalence-valued interface is constructed from distinctness and
the transcript cardinality. -/
noncomputable def toBlockIndexBinding
    (S : Fi24P3BlockIndexInjectionSource BlockIndex) :
    Fi24P3BlockIndexBinding BlockIndex where
  indexEquiv := Equiv.ofBijective S.roleIndex S.roleIndex_bijective

@[simp]
theorem toBlockIndexBinding_apply
    (S : Fi24P3BlockIndexInjectionSource BlockIndex)
    (role : Fi24P3BlockRole) :
    S.toBlockIndexBinding.indexEquiv role = S.roleIndex role :=
  rfl

end Fi24P3BlockIndexInjectionSource

end ModularRep.PaperProofs.SporadicFi24P3BlockIndexBindingFromCardinality


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
