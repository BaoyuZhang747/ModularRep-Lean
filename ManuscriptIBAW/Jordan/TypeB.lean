import ManuscriptIBAW.Jordan.BrauerRestriction
import ManuscriptIBAW.Jordan.GeneralGeometry
import ModularRep.PaperProofs.TypeBCurrentBrauerTransport

/-!
# Restriction for Type B

The theorem for the full field automorphism group uses the specified Spin
norm kernel and special Clifford group. The restriction preserves their
actions, the chosen Brauer root, the orbit representative and the extension
representation.
-/

noncomputable section

namespace ManuscriptIBAW.Jordan.TypeB

open ModularRep
open ModularRep.PaperProofs
open TypeBCliffordCarriers
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {n p f : ℕ} {F k K : Type}
  [Field F] [Finite F] [CharP F p]
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  {N : NormSource n F} {parameters : OddFieldParameters F p f}
  [Finite (SpecialClifford n F)] [NeZero f]
  (fs : FieldActionSource n F p f parameters N)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))

local instance regularAction : MulAction (SpecialClifford n F) (IBr iota) :=
  TypeBCurrentBrauerTransport.diagonalAction iota

/-- Obtain the required data from the theorem for the full field group. -/
theorem fullHypothesis
    (h : TypeBCurrentBrauerTransport.BrauerHypothesis fs iota) :
    letI := TypeBCurrentBrauerTransport.fieldAction fs iota
    FullBrauerHypothesis (D := SpecialClifford n F) iota (spinFieldAction n F fs) := by
  let := TypeBCurrentBrauerTransport.fieldAction fs iota
  intro psi0
  obtain ⟨psi, horbit, hfactor, hext⟩ := h psi0
  obtain ⟨V, hV, hchar, rho, _, ⟨equiv⟩⟩ := hext
  refine ⟨psi, horbit, ⟨{
    factorization := ?_
    module := V
    irreducible := hV
    character_eq := hchar
    extension := ⟨rho, equiv⟩ }⟩⟩
  exact (semidirectStabilizerFactors_iff_productStabilizerFactorization
    fs.action (TypeBCurrentBrauerTransport.compatible fs iota) psi).mp hfactor

/-- Choose the subgroup for each rational semisimple label before considering
all special Clifford orbits. The geometric conditions are separate
assumptions. The required restriction is proved here. -/
theorem perLabel
    (groups : TypeBCurrentBrauerTransport.SemisimpleIndex
      (n := n) (p := p) (F := F) → Subgroup (FieldGroup f))
    (h : TypeBCurrentBrauerTransport.BrauerHypothesis fs iota) :
    letI := TypeBCurrentBrauerTransport.fieldAction fs iota
    ∀ s, RestrictedBrauerHypothesis (D := SpecialClifford n F)
      iota (spinFieldAction n F fs) (groups s) := by
  let := TypeBCurrentBrauerTransport.fieldAction fs iota
  intro s
  exact fullBrauerHypothesis_restrict iota (spinFieldAction n F fs)
    (groups s) (fullHypothesis fs iota h)

/-- The first condition of Lemma 3.2, including its geometric choice and every
original orbit, follows from Proposition 4.13 for the full field group. -/
theorem permissiblePerLabel
    (C : GeometricContext (ell := 2) (k := k)
      (S := TypeBCurrentBrauerTransport.SemisimpleIndex (n := n) (p := p) (F := F))
      (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs))
    (geometry : GeometricSelection
      (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs) C)
    (h : TypeBCurrentBrauerTransport.BrauerHypothesis fs iota) :
    letI := TypeBCurrentBrauerTransport.fieldAction fs iota
    ∀ s, ∃ A : PermissibleFieldGroup
      (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs) C s,
      RestrictedBrauerHypothesis (D := SpecialClifford n F)
        iota (spinFieldAction n F fs) A.group := by
  exact perLabel_of_fullField
    (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs)
    iota C geometry (fullHypothesis fs iota h)

theorem generalPerLabel
    (C : GeometricContext (ell := 2) (k := k)
      (S := TypeBCurrentBrauerTransport.SemisimpleIndex (n := n) (p := p) (F := F))
      (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs))
    (geometry : GeometricSelection
      (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs) C)
    (h : TypeBCurrentBrauerTransport.BrauerHypothesis fs iota) :
    GeneralPerLabelHypothesis
      (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs) iota C := by
  exact generalPerLabel_of_fullField _ _ iota C geometry (fullHypothesis fs iota h)

end ManuscriptIBAW.Jordan.TypeB

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
