import ModularRep.PaperProofs.TypeBFLZComponentCoreParameters
import ModularRep.PaperProofs.TypeBFLZPartitionCores
import ModularRep.PaperProofs.TypeBFLZSymbolCores
import ModularRep.PaperProofs.TypeBFLZCoreExtractionBinding

/-!
# Literal profile labels and their componentwise cores

The label family is the full product over the actual polynomial component
carrier. F0 components use the actual odd-defect symbols at half the
guarded polynomial multiplicity; other components use actual partitions
of that multiplicity. A nonzero profile polynomial is retained in a
PSigma, so the zero-polynomial fibre is empty.

Only positive-length terminal-removal certificates on the literal
partition/symbol carriers are supplied. Component lengths and the
hook/cohook mode are the explicit component-field arithmetic parameters.
The profile core operator and its attained range are then constructed.

The polynomial/centralizer multiplicity interpretation, F0 evenness,
F1 duality and the actual unipotent-character labelling remain source
realization obligations. There is no character/block certificate or
Type B target in this file.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZLiteralProfileModel

open scoped Classical
open TypeBFLZCoreProfileConjugacy TypeBFLZPolynomialComponents
open TypeBFLZComponentCoreParameters TypeBFLZSymbolCarriers

universe u

variable {F : Type u} [Field F]

/-- The actual fixed-size label on each literal polynomial component. -/
def ComponentLabel (P : Profile F) (hP : P.2 ≠ 0) (Gamma : ProfileComponent P) : Type :=
  if IsF0 P.1 Gamma.val then
    OddRankSymbol (natComponentMultiplicity P hP Gamma / 2)
  else
    Nat.Partition (natComponentMultiplicity P hP Gamma)

/-- The full product, including zero-multiplicity components. The proof
coordinate prevents any infinite-multiplicity default at a zero profile. -/
def Psi (P : Profile F) : Type u :=
  Σ' hP : P.2 ≠ 0, ∀ Gamma : ProfileComponent P, ComponentLabel P hP Gamma

theorem psi_polynomial_ne_zero (P : Profile F) (mu : Psi P) : P.2 ≠ 0 := mu.1

theorem psi_not_nonempty_of_polynomial_eq_zero (P : Profile F) (hP : P.2 = 0) :
    ¬ Nonempty (Psi P) := by
  rintro ⟨mu⟩
  exact mu.1 hP

/-- Forget only the input rank or partition size; keep the actual symbol
or actual partition carrier on which terminal removal is defined. -/
def ComponentRawCore (P : Profile F) (Gamma : ProfileComponent P) : Type :=
  if IsF0 P.1 Gamma.val then OddSymbol else TypeBFLZPartitionCores.Partition

def RawCore (P : Profile F) : Type u :=
  ∀ Gamma : ProfileComponent P, ComponentRawCore P Gamma

/-- Routine E1 inputs on literal removal relations at positive lengths.
There is no supplied core map, component mode, profile label or covariance. -/
structure RemovalInputs where
  partition : ∀ (e : ℕ), 0 < e → TypeBFLZPartitionCores.CoreRemovalCertificate e
  symbol : ∀ (kind : RemovalKind) (e : ℕ), 0 < e →
    TypeBFLZSymbolCores.CoreRemovalCertificate kind e

variable (ell : ℕ) [Fact ell.Prime]
variable (nondefining : ¬ ell ∣ Nat.card F) (inputs : RemovalInputs)

/-- Apply the appropriate literal terminal-removal operator, using the
derived positive length at this actual component field. -/
def componentTakeCore (P : Profile F) (hP : P.2 ≠ 0) (Gamma : ProfileComponent P)
    (mu : ComponentLabel P hP Gamma) : ComponentRawCore P Gamma :=
  if h0 : IsF0 P.1 Gamma.val then
    let mu0 : OddRankSymbol (natComponentMultiplicity P hP Gamma / 2) :=
      cast (show ComponentLabel P hP Gamma = _ from if_pos h0) mu
    cast (show OddSymbol = ComponentRawCore P Gamma from (if_pos h0).symm)
      (TypeBFLZSymbolCores.takeCore
        (inputs.symbol (symbolKind ell P Gamma) (symbolLength ell P Gamma)
          (symbolLength_pos ell nondefining P Gamma)) ⟨mu0.val, mu0.property.2⟩)
  else
    let mu0 : Nat.Partition (natComponentMultiplicity P hP Gamma) :=
      cast (show ComponentLabel P hP Gamma = _ from if_neg h0) mu
    cast (show TypeBFLZPartitionCores.Partition = ComponentRawCore P Gamma from
      (if_neg h0).symm)
      (TypeBFLZPartitionCores.takeCore
        (inputs.partition (partitionLength ell P Gamma)
          (partitionLength_pos ell nondefining P Gamma))
        ⟨natComponentMultiplicity P hP Gamma, mu0⟩)

/-- The exact relation specified by the chosen branch, before taking any
profile range or character labelling. -/
def ComponentTerminalCore (P : Profile F) (hP : P.2 ≠ 0) (Gamma : ProfileComponent P)
    (mu : ComponentLabel P hP Gamma) (kappa : ComponentRawCore P Gamma) : Prop :=
  if h0 : IsF0 P.1 Gamma.val then
    let mu0 : OddRankSymbol (natComponentMultiplicity P hP Gamma / 2) :=
      cast (show ComponentLabel P hP Gamma = _ from if_pos h0) mu
    TypeBFLZSymbolCores.TerminalCore (symbolKind ell P Gamma) (symbolLength ell P Gamma)
      ⟨mu0.val, mu0.property.2⟩
      (cast (show ComponentRawCore P Gamma = OddSymbol from if_pos h0) kappa)
  else
    let mu0 : Nat.Partition (natComponentMultiplicity P hP Gamma) :=
      cast (show ComponentLabel P hP Gamma = _ from if_neg h0) mu
    TypeBFLZPartitionCores.TerminalCore (partitionLength ell P Gamma)
      ⟨natComponentMultiplicity P hP Gamma, mu0⟩
      (cast (show ComponentRawCore P Gamma = TypeBFLZPartitionCores.Partition from
        if_neg h0) kappa)

theorem componentTakeCore_spec (P : Profile F) (hP : P.2 ≠ 0)
    (Gamma : ProfileComponent P) (mu : ComponentLabel P hP Gamma) :
    ComponentTerminalCore ell P hP Gamma mu
      (componentTakeCore ell nondefining inputs P hP Gamma mu) := by
  by_cases h0 : IsF0 P.1 Gamma.val
  · simp only [ComponentTerminalCore, componentTakeCore, dif_pos h0, cast_cast, cast_eq]
    exact TypeBFLZSymbolCores.takeCore_spec _ _
  · simp only [ComponentTerminalCore, componentTakeCore, dif_neg h0, cast_cast, cast_eq]
    exact TypeBFLZPartitionCores.takeCore_spec _ _

/-- There is one canonical operator on the literal full profile product. -/
def takeCore (P : Profile F) (mu : Psi P) : RawCore P :=
  fun Gamma => componentTakeCore ell nondefining inputs P mu.1 Gamma (mu.2 Gamma)

@[simp]
theorem takeCore_apply (P : Profile F) (mu : Psi P) (Gamma : ProfileComponent P) :
    takeCore ell nondefining inputs P mu Gamma =
      componentTakeCore ell nondefining inputs P mu.1 Gamma (mu.2 Gamma) := rfl

theorem takeCore_component_spec (P : Profile F) (mu : Psi P) (Gamma : ProfileComponent P) :
    ComponentTerminalCore ell P mu.1 Gamma (mu.2 Gamma)
      (takeCore ell nondefining inputs P mu Gamma) :=
  componentTakeCore_spec ell nondefining inputs P mu.1 Gamma (mu.2 Gamma)

/-- The actual attained full core values, using the frozen generic range. -/
abbrev PossibleCore (P : Profile F) :=
  TypeBFLZCoreExtractionBinding.PossibleCore Psi RawCore
    (takeCore ell nondefining inputs) P

def profileCore (P : Profile F) (mu : Psi P) : PossibleCore ell nondefining inputs P :=
  TypeBFLZCoreExtractionBinding.profileCore Psi RawCore
    (takeCore ell nondefining inputs) P mu

@[simp]
theorem profileCore_val (P : Profile F) (mu : Psi P) :
    (profileCore ell nondefining inputs P mu).val = takeCore ell nondefining inputs P mu := rfl

theorem profileCore_surjective (P : Profile F) :
    Function.Surjective (profileCore ell nondefining inputs P) :=
  TypeBFLZCoreExtractionBinding.profileCore_surjective Psi RawCore
    (takeCore ell nondefining inputs) P

/-- The literal specialization of the frozen rational-class-indexed core
family. No arbitrary Psi, RawCore or takeCore remains a parameter. -/
abbrev coreByClass {p n : ℕ} (i : TypeBFLZLabelSource.SourceIndex F p ell n) : Type u :=
  TypeBFLZCoreExtractionBinding.coreByClass Psi RawCore
    (takeCore ell nondefining inputs) i

end ModularRep.PaperProofs.TypeBFLZLiteralProfileModel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
