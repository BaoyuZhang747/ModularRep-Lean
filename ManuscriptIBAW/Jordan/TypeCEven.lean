import ManuscriptIBAW.Jordan.EmbeddedExtension
import ManuscriptIBAW.Jordan.Geometry
import ModularRep.PaperProofs.EvenFieldAssumption53Actual

/-!
# Restriction for Type C in even characteristic

Conformal fixation and cyclic extension give the required data for the full
field group on the specified finite fixed point group. The extension is
transported from its embedded coordinates and restricted to each chosen
`A_s`.
-/

noncomputable section

namespace ManuscriptIBAW.Jordan.TypeCEven

open ModularRep
open ModularRep.PaperProofs
open EvenFieldConcreteTypeC EvenFieldAssumption53Actual

variable {ell r a : ℕ} {C Fq k K : Type}
  [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
  [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
  (ha : 0 < a)
  [Finite (FiniteSymplecticFixed r a)]
  [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
  (iota : PrimeRegularRootEmbedding ell k K (FiniteSymplecticFixed r a))
  (conformal : ConformalStructuralSource r a ha C Fq)

theorem fullHypothesis
    (cyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k) :
    letI := conformalIBrAction r a iota conformal.multiplier conformal.kernelEquiv
    letI := canonicalFieldIBrAction r a ha iota
    FullBrauerHypothesis (D := C) iota (fieldAction r a ha) := by
  letI := conformalIBrAction r a iota conformal.multiplier conformal.kernelEquiv
  letI := canonicalFieldIBrAction r a ha iota
  intro psi
  refine ⟨psi, MulAction.mem_orbit_self psi, ?_⟩
  apply fullRepresentative_of_embedded iota (fieldAction r a ha) psi
  · intro c e
    rw [conformal_fixation_actual r a ha iota conformal c (e • psi),
      conformal_fixation_actual r a ha iota conformal c psi]
    simp
  · exact field_stabilizer_extension_actual r a ha iota cyclic psi

theorem perLabel {Label : Type*} (groups : Label → Subgroup (FieldGroup a))
    (cyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k) :
    letI := conformalIBrAction r a iota conformal.multiplier conformal.kernelEquiv
    letI := canonicalFieldIBrAction r a ha iota
    ∀ s, RestrictedBrauerHypothesis (D := C) iota (fieldAction r a ha) (groups s) := by
  letI := conformalIBrAction r a iota conformal.multiplier conformal.kernelEquiv
  letI := canonicalFieldIBrAction r a ha iota
  intro s
  exact fullBrauerHypothesis_restrict iota (fieldAction r a ha) (groups s)
    (fullHypothesis ha iota conformal cyclic)

/-- Choose the geometric data before restricting over every orbit. Completeness
of the labels and the full outer stabiliser are assumptions in the context
of `geometry`. They are not inferred from an arbitrary subgroup. -/
theorem permissiblePerLabel {Label : Type*}
    (context : GeometricContext (ell := ell) (k := k) (S := Label)
      (transportedConformalAction r a conformal.multiplier conformal.kernelEquiv)
      (fieldAction r a ha))
    (geometry : GeometricSelection
      (transportedConformalAction r a conformal.multiplier conformal.kernelEquiv)
      (fieldAction r a ha) context)
    (cyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k) :
    letI := conformalIBrAction r a iota conformal.multiplier conformal.kernelEquiv
    letI := canonicalFieldIBrAction r a ha iota
    ∀ s, ∃ A : PermissibleFieldGroup
      (transportedConformalAction r a conformal.multiplier conformal.kernelEquiv)
      (fieldAction r a ha) context s,
      RestrictedBrauerHypothesis (D := C) iota (fieldAction r a ha) A.group := by
  exact perLabel_of_fullField
    (transportedConformalAction r a conformal.multiplier conformal.kernelEquiv)
    (fieldAction r a ha) iota context geometry (fullHypothesis ha iota conformal cyclic)

end ManuscriptIBAW.Jordan.TypeCEven

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
