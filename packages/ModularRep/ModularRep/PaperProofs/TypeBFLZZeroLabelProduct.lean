import ModularRep.PaperProofs.TypeBFLZLiteralProfileModel

/-!
# Removing absent components from the literal profile label product

The product is restricted to the actual components of positive polynomial
multiplicity. Its inverse inserts the canonical partition or odd symbol
of rank zero. Partition uniqueness is already checked in mathlib. The only
routine external input is uniqueness of the literal odd rank-zero symbol;
its canonical representative and nonemptiness are constructed here.

No product equivalence, character label, covariance, core classification or
Type B target is supplied as an input. Every map preserves occurring labels
pointwise and is natural under equality of the same actual profile.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZZeroLabelProduct

open scoped Classical
open TypeBFLZCoreProfileConjugacy TypeBFLZPolynomialComponents
open TypeBFLZLiteralProfileModel TypeBFLZSymbolCarriers

universe u

/-- The rank-zero symbol represented by the unordered rows ({0}, empty). -/
def zeroOddRankSymbol : OddRankSymbol 0 :=
  ⟨ofRows ({0}, ∅), by constructor <;> norm_num [Nat.odd_iff]⟩

/-- Routine E1 uniqueness on the literal quotient/rank/odd-defect carrier.
It is the elementary rank-zero consequence of the minimum-row-sum formula
in Olsson, section 5, p.35 (also Geck--Malle, section 4.4.1, pp.301--302).
Existence is already provided by zeroOddRankSymbol. -/
structure ZeroSymbolCertificate : Prop where
  eq_zero : ∀ S : OddRankSymbol 0, S = zeroOddRankSymbol

theorem oddRankSymbol_zero_subsingleton (C : ZeroSymbolCertificate) :
    Subsingleton (OddRankSymbol 0) :=
  ⟨fun S T => (C.eq_zero S).trans (C.eq_zero T).symm⟩

variable {F : Type u} [Field F]

/-- The inherited occurring-component carrier is exactly positive finite
natural multiplicity when the same profile polynomial is nonzero. -/
theorem occurring_iff_nat_pos (P : Profile F) (hP : P.2 ≠ 0)
    (Gamma : ProfileComponent P) :
    0 < componentMultiplicity P Gamma ↔ 0 < natComponentMultiplicity P hP Gamma := by
  rw [componentMultiplicity_eq_nat P hP Gamma]
  exact ENat.natCast_lt_natCast

theorem natMultiplicity_zero_of_absent (P : Profile F) (hP : P.2 ≠ 0)
    (Gamma : ProfileComponent P) (absent : ¬ 0 < componentMultiplicity P Gamma) :
    natComponentMultiplicity P hP Gamma = 0 := by
  have hn : ¬ 0 < natComponentMultiplicity P hP Gamma :=
    fun h => absent ((occurring_iff_nat_pos P hP Gamma).mpr h)
  omega

/-- A literal zero label, with no uniqueness or choice input. -/
def zeroComponentLabel (P : Profile F) (hP : P.2 ≠ 0)
    (Gamma : ProfileComponent P) (hz : natComponentMultiplicity P hP Gamma = 0) :
    ComponentLabel P hP Gamma := by
  unfold ComponentLabel
  rw [hz]
  split_ifs
  · exact zeroOddRankSymbol
  · exact default

theorem componentLabel_eq_zero (C : ZeroSymbolCertificate)
    (P : Profile F) (hP : P.2 ≠ 0) (Gamma : ProfileComponent P)
    (hz : natComponentMultiplicity P hP Gamma = 0) (mu : ComponentLabel P hP Gamma) :
    mu = zeroComponentLabel P hP Gamma hz := by
  have hs : Subsingleton (ComponentLabel P hP Gamma) := by
    unfold ComponentLabel
    rw [hz]
    split_ifs
    · exact oddRankSymbol_zero_subsingleton C
    · infer_instance
  exact hs.elim _ _

/-- The same labels, indexed only by actual occurring polynomial components.
The nonzero-polynomial proof is retained, so the zero-profile fibre remains empty. -/
def OccurringPsi (P : Profile F) : Type u :=
  Σ' hP : P.2 ≠ 0, ∀ Gamma : OccurringComponent P, ComponentLabel P hP Gamma.val

def restrict (P : Profile F) (mu : Psi P) : OccurringPsi P :=
  ⟨mu.1, fun Gamma => mu.2 Gamma.val⟩

@[simp]
theorem restrict_apply (P : Profile F) (mu : Psi P) (Gamma : OccurringComponent P) :
    (restrict P mu).2 Gamma = mu.2 Gamma.val := rfl

/-- Extend by the explicitly constructed zero label at every absent component. -/
def extend (P : Profile F) (mu : OccurringPsi P) : Psi P :=
  ⟨mu.1, fun Gamma =>
    if h : 0 < componentMultiplicity P Gamma then mu.2 ⟨Gamma, h⟩
    else zeroComponentLabel P mu.1 Gamma (natMultiplicity_zero_of_absent P mu.1 Gamma h)⟩

@[simp]
theorem extend_occurring (P : Profile F) (mu : OccurringPsi P)
    (Gamma : OccurringComponent P) :
    (extend P mu).2 Gamma.val = mu.2 Gamma := by
  exact dif_pos Gamma.property

theorem extend_absent (P : Profile F) (mu : OccurringPsi P)
    (Gamma : ProfileComponent P) (absent : ¬ 0 < componentMultiplicity P Gamma) :
    (extend P mu).2 Gamma =
      zeroComponentLabel P mu.1 Gamma (natMultiplicity_zero_of_absent P mu.1 Gamma absent) :=
  dif_neg absent

@[simp]
theorem restrict_extend (P : Profile F) (mu : OccurringPsi P) :
    restrict P (extend P mu) = mu := by
  rcases mu with ⟨hP, mu⟩
  apply congrArg (fun nu : ∀ Gamma : OccurringComponent P,
    ComponentLabel P hP Gamma.val => (⟨hP, nu⟩ : OccurringPsi P))
  funext Gamma
  exact dif_pos Gamma.property

@[simp]
theorem extend_restrict (C : ZeroSymbolCertificate) (P : Profile F) (mu : Psi P) :
    extend P (restrict P mu) = mu := by
  rcases mu with ⟨hP, mu⟩
  apply congrArg (fun nu : ∀ Gamma : ProfileComponent P,
    ComponentLabel P hP Gamma => (⟨hP, nu⟩ : Psi P))
  funext Gamma
  change (if h : 0 < componentMultiplicity P Gamma then mu Gamma
    else zeroComponentLabel P hP Gamma (natMultiplicity_zero_of_absent P hP Gamma h)) =
      mu Gamma
  by_cases h : 0 < componentMultiplicity P Gamma
  · exact dif_pos h
  · rw [dif_neg h]
    exact (componentLabel_eq_zero C P hP Gamma
      (natMultiplicity_zero_of_absent P hP Gamma h) (mu Gamma)).symm

/-- Constructed full/occurring product equivalence; no such map is a source field. -/
def psiEquiv (C : ZeroSymbolCertificate) (P : Profile F) : Psi P ≃ OccurringPsi P where
  toFun := restrict P
  invFun := extend P
  left_inv := extend_restrict C P
  right_inv := restrict_extend P

@[simp]
theorem psiEquiv_apply (C : ZeroSymbolCertificate) (P : Profile F) (mu : Psi P)
    (Gamma : OccurringComponent P) :
    (psiEquiv C P mu).2 Gamma = mu.2 Gamma.val := rfl

@[simp]
theorem psiEquiv_symm_apply (C : ZeroSymbolCertificate) (P : Profile F)
    (mu : OccurringPsi P) (Gamma : OccurringComponent P) :
    ((psiEquiv C P).symm mu).2 Gamma.val = mu.2 Gamma :=
  extend_occurring P mu Gamma

/-- With the actual nonzero-polynomial proof prescribed, the proof coordinate
can be removed from the occurring product by proof irrelevance. -/
def occurringProductEquiv (P : Profile F) (hP : P.2 ≠ 0) :
    OccurringPsi P ≃ (∀ Gamma : OccurringComponent P, ComponentLabel P hP Gamma.val) where
  toFun mu := mu.2
  invFun nu := ⟨hP, nu⟩
  left_inv mu := by cases mu; rfl
  right_inv _ := rfl

def psiProductEquiv (C : ZeroSymbolCertificate) (P : Profile F) (hP : P.2 ≠ 0) :
    Psi P ≃ (∀ Gamma : OccurringComponent P, ComponentLabel P hP Gamma.val) :=
  (psiEquiv C P).trans (occurringProductEquiv P hP)

@[simp]
theorem psiProductEquiv_apply (C : ZeroSymbolCertificate) (P : Profile F)
    (hP : P.2 ≠ 0) (mu : Psi P) (Gamma : OccurringComponent P) :
    psiProductEquiv C P hP mu Gamma = mu.2 Gamma.val := rfl

@[simp]
theorem psiProductEquiv_symm_apply (C : ZeroSymbolCertificate) (P : Profile F)
    (hP : P.2 ≠ 0) (mu : ∀ Gamma : OccurringComponent P, ComponentLabel P hP Gamma.val)
    (Gamma : OccurringComponent P) :
    ((psiProductEquiv C P hP).symm mu).2 Gamma.val = mu Gamma :=
  extend_occurring P ⟨hP, mu⟩ Gamma

/-- Equality transport changes only the actual profile's dependent types. -/
def occurringComponentTransport {P Q : Profile F} (h : P = Q) :
    OccurringComponent P ≃ OccurringComponent Q := by
  subst Q
  exact Equiv.refl _

@[simp]
theorem occurringComponentTransport_val {P Q : Profile F} (h : P = Q)
    (Gamma : OccurringComponent P) :
    (occurringComponentTransport h Gamma).val = transportComponent h Gamma.val := by
  subst Q
  rfl

def fullTransport {P Q : Profile F} (h : P = Q) : Psi P ≃ Psi Q :=
  Equiv.cast (congrArg Psi h)

def occurringTransport {P Q : Profile F} (h : P = Q) :
    OccurringPsi P ≃ OccurringPsi Q :=
  Equiv.cast (congrArg OccurringPsi h)

theorem fullTransport_apply {P Q : Profile F} (h : P = Q) (mu : Psi P)
    (Gamma : ProfileComponent P) :
    HEq ((fullTransport h mu).2 (transportComponent h Gamma)) (mu.2 Gamma) := by
  subst Q
  rfl

theorem occurringTransport_apply {P Q : Profile F} (h : P = Q) (mu : OccurringPsi P)
    (Gamma : OccurringComponent P) :
    HEq ((occurringTransport h mu).2 (occurringComponentTransport h Gamma)) (mu.2 Gamma) := by
  subst Q
  rfl

theorem restrict_transport {P Q : Profile F} (h : P = Q) (mu : Psi P) :
    restrict Q (fullTransport h mu) = occurringTransport h (restrict P mu) := by
  subst Q
  rfl

theorem extend_transport {P Q : Profile F} (h : P = Q) (mu : OccurringPsi P) :
    extend Q (occurringTransport h mu) = fullTransport h (extend P mu) := by
  subst Q
  rfl

theorem psiEquiv_transport (C : ZeroSymbolCertificate) {P Q : Profile F}
    (h : P = Q) (mu : Psi P) :
    psiEquiv C Q (fullTransport h mu) = occurringTransport h (psiEquiv C P mu) :=
  restrict_transport h mu

end ModularRep.PaperProofs.TypeBFLZZeroLabelProduct


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
