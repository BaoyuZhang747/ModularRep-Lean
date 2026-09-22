import ModularRep.PaperProofs.TypeBFLZCoreExtractionBinding
import ModularRep.PaperProofs.TypeBFLZLabelSplittingSource

/-!
# Theorem 6.3 on the constructed profile-core pairs

The source orbit carrier uses the actual class-indexed range of the SAME
profile core operator and the constructed core-pair conjugation action.
Only the primitive-block classification and its t=1 membership statement
are sourced. Core extraction and parameter conjugation are derived.

Psi, RawCore and takeCore still require identification with the published
partition/odd-defect-symbol model, including hook-core versus cocore mode.
The source records no arbitrary coreAt, action, action laws, global basic
set, blockwise matching or manuscript target. Full ordinary block-union
membership remains the separately scoped FLZ full-union certificate.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZProfileCoreSource

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBFLZLabelSource (UnipotentPredicate SemisimpleParameter AdmissibleParameter
  FullCharacterPair CharacterPair BlockPair parameterCentralizer admissibleToSemisimple)
open TypeBFLZCoreProfileConjugacy TypeBFLZCorePairConjugacy
open TypeBFLZCoreExtractionBinding
open TypeBFLZLabelSplittingSource

universe u

variable {F K k : Type u} [Field F] [Field K] [CharZero K] [Field k]
variable {p ell n : ℕ}
variable [Finite F] [CharP F p] [Finite (Clifford n F)]
variable [CharP k ell] [IsAlgClosed k]
variable (Psi RawCore : Profile F → Type u)
variable (takeCore : ∀ profile, Psi profile → RawCore profile)
variable (unipotent : UnipotentPredicate F K p n)
variable (label : ∀ s : SemisimpleParameter F p n,
  Psi (semisimpleProfile s) ≃
    {chi : Irr K (parameterCentralizer F p n s) // unipotent s chi})
variable [MulAction (CSp F n) (FullCharacterPair F K p n unipotent)]
variable (S : Equation34Source (ell := ell) unipotent)

/-- The source core orbits use this constructed action, not a caller-supplied
action on an otherwise named core family. -/
local instance actualCorePairAction :
    MulAction (CSp F n)
      (BlockPair F p ell n (CoreFamily (coreByClass Psi RawCore takeCore))) :=
  corePairAction (coreByClass Psi RawCore takeCore)

variable (ordinaryBlock : Irr K (SpecialClifford n F) →
  LiteralPrimitiveBlock k (SpecialClifford n F))

/-- E2: FLZ Theorem 6.3(1), and part (2) at t=1, on the SAME actual
parameter/profile label, constructed core pair and specified primitive block.
The finite-point, coefficient/root and combinatorial source realizations
remain explicit obligations. No extraction or conjugation field is supplied. -/
structure Theorem63Certificate
    (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
    [physicalBlocks : Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
    (blocks : BlockIdempotentDecomposition
      (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.val)) where
  modular_characteristic : CharP k ell
  modular_splitting : IsAlgClosed k
  classification : MulAction.orbitRel.Quotient (CSp F n)
      (BlockPair F p ell n (CoreFamily (coreByClass Psi RawCore takeCore))) ≃
    LiteralPrimitiveBlock k (SpecialClifford n F)
  membership : ∀ (s : AdmissibleParameter F p ell n) (mu : Psi (admissibleProfile s)),
    ordinaryBlock (S.character
      (⟨s, label (admissibleToSemisimple F p ell n s) mu⟩ :
        CharacterPair F K p ell n unipotent)).val =
      classification (Quotient.mk _
        (⟨s, profileCore Psi RawCore takeCore (admissibleProfile s) mu⟩ :
          BlockPair F p ell n (CoreFamily (coreByClass Psi RawCore takeCore))))

variable (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
variable [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.val))
variable (source : Theorem63Certificate Psi RawCore takeCore unipotent label S
  ordinaryBlock iota blocks)

/-- Recover the frozen interface from the narrower literal source.
The SAME label inverse defines extraction; its application to arbitrary
actual unipotent chi reduces the sourced mu statement to the required one. -/
def toTheorem63Source :
    Theorem63Source unipotent S (CoreFamily (coreByClass Psi RawCore takeCore))
      ordinaryBlock iota blocks where
  modular_characteristic := source.modular_characteristic
  modular_splitting := source.modular_splitting
  coreAt := extraction Psi RawCore takeCore unipotent label
  parameter_conjugation g P := corePairAction_parameter (coreByClass Psi RawCore takeCore) g P
  classification := source.classification
  membership := by
    rintro ⟨s, chi⟩
    simpa only [extraction, Equiv.apply_symm_apply] using
      source.membership s ((label (admissibleToSemisimple F p ell n s)).symm chi)

@[simp]
theorem toTheorem63Source_coreAt (s : AdmissibleParameter F p ell n)
    (chi : {chi : Irr K (parameterCentralizer F p n (admissibleToSemisimple F p ell n s)) //
      unipotent (admissibleToSemisimple F p ell n s) chi}) :
    (toTheorem63Source Psi RawCore takeCore unipotent label S ordinaryBlock iota blocks source).coreAt
        s chi = extraction Psi RawCore takeCore unipotent label s chi := rfl

@[simp]
theorem toTheorem63Source_classification :
    (toTheorem63Source Psi RawCore takeCore unipotent label S ordinaryBlock iota blocks source).classification =
      source.classification := rfl

/-- On the actual labelled character the derived extractor is exactly the
same profile core operator's value, with no extra label choice. -/
@[simp]
theorem toTheorem63Source_coreAt_label (s : AdmissibleParameter F p ell n)
    (mu : Psi (admissibleProfile s)) :
    (toTheorem63Source Psi RawCore takeCore unipotent label S ordinaryBlock iota blocks source).coreAt
        s (label (admissibleToSemisimple F p ell n s) mu) =
      profileCore Psi RawCore takeCore (admissibleProfile s) mu := by
  exact congrArg (profileCore Psi RawCore takeCore (admissibleProfile s))
    ((label (admissibleToSemisimple F p ell n s)).symm_apply_apply mu)

end ModularRep.PaperProofs.TypeBFLZProfileCoreSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
