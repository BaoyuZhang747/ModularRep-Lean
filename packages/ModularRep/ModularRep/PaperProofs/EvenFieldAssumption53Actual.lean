import ModularRep.PaperProofs.CyclicOuterLemma37Concrete
import ModularRep.PaperProofs.EvenFieldConcreteTypeC
import ModularRep.BrauerCharacterEquivTransport
import ModularRep.SemidirectEmbeddedConjugation

/-!
# Actual-carrier form of the first Jordan hypothesis in Proposition 3.9

This module specialises the manuscript-specific deductions in
`EvenFieldAssumption53Relative` to the literal fixed-point symplectic group
and to function-valued irreducible Brauer characters.  The field action on
that group is definitionally `EvenFieldConcreteTypeC.fieldAction`; all
character actions below are obtained by canonical automorphism transport.

The conformal group itself is retained as an exact E1 source carrier because
the library has no conformal-symplectic matrix model.  Its action on the
literal symplectic group is not free data: it is transported from conjugation
on the kernel of its supplied multiplier through an explicit group
equivalence.  The source also states that its field action restricts to the
canonical action on the literal fixed points and that conformal conjugation
is inner.  These are precisely the routine inputs `SF-CSP-MODEL` and
`SF-FIELD-ACTION`, and receive no manuscript-specific K credit.

No Assumption 5.3, BAW-goodness, iBAW condition, Jordan-reduction hypothesis,
or conclusion of Proposition 3.9 is an input or a conclusion here.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldAssumption53Actual

open Formalisation
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete

/-- Conformal conjugation on a multiplier kernel, transported to the literal
fixed-point symplectic carrier. -/
def transportedConformalAction
    {C Fq : Type} [Group C] [Field Fq]
    (r a : ℕ)
    (multiplier : C →* Fqˣ)
    (kernelEquiv : multiplier.ker ≃* FiniteSymplecticFixed r a) :
    C →* MulAut (FiniteSymplecticFixed r a) :=
  (MulAut.congr kernelEquiv).toMonoidHom.comp
    (MulAut.conjNormal (H := multiplier.ker))

/-- Exact E1 structure identifying a conformal overgroup and its field
action with the literal fixed-point symplectic carrier.

`fieldRestriction` is an equality with the canonical `fieldAction`, not an
independent action on the symplectic group.  `conformalInner` records the
characteristic-two conformal factorisation from `SF-CSP-MODEL`. -/
structure ConformalStructuralSource
    (r a : ℕ) (ha : 0 < a)
    (C Fq : Type) [Group C] [Finite C]
    [Field Fq] [Finite Fq] [CharP Fq 2] where
  multiplier : C →* Fqˣ
  kernelEquiv : multiplier.ker ≃* FiniteSymplecticFixed r a
  conformalFieldAction : FieldGroup a →* MulAut C
  fieldRestriction : ∀ (sigma : FieldGroup a) (c : C),
    transportedConformalAction r a multiplier kernelEquiv c⁻¹ *
        fieldAction r a ha sigma⁻¹ =
      fieldAction r a ha sigma⁻¹ *
        transportedConformalAction r a multiplier kernelEquiv
          ((conformalFieldAction sigma) c)⁻¹
  conformalInner : ∀ c : C, ∃ h : FiniteSymplecticFixed r a,
    transportedConformalAction r a multiplier kernelEquiv c =
      MulAut.conj h

/-- The right field action on literal `IBr`, obtained from the canonical
fixed-point field automorphism rather than supplied as an action instance. -/
@[instance_reducible] def canonicalFieldIBrAction
    {p : ℕ} {k K : Type}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (r a : ℕ) (ha : 0 < a)
    [Finite (FiniteSymplecticFixed r a)]
    (iota : PrimeRegularRootEmbedding p k K
      (FiniteSymplecticFixed r a)) :
    MulAction (FieldGroup a) (IBr iota) :=
  rightAutomorphismAction (X := IBr iota)
    (fieldAction r a ha)

/-- The conformal action on literal `IBr`, obtained from transported
conjugation on the multiplier kernel. -/
@[instance_reducible] def conformalIBrAction
    {p : ℕ} {C Fq k K : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (r a : ℕ)
    [Finite (FiniteSymplecticFixed r a)]
    (iota : PrimeRegularRootEmbedding p k K
      (FiniteSymplecticFixed r a))
    (multiplier : C →* Fqˣ)
    (kernelEquiv : multiplier.ker ≃* FiniteSymplecticFixed r a) :
    MulAction C (IBr iota) :=
  rightAutomorphismAction (X := IBr iota)
    (transportedConformalAction r a multiplier kernelEquiv)

/-- The canonical field action on a function-valued Brauer character is
literally twisting by the inverse fixed-point field automorphism. -/
theorem canonicalFieldIBrAction_smul
    {p : ℕ} {k K : Type}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (r a : ℕ) (ha : 0 < a)
    [Finite (FiniteSymplecticFixed r a)]
    (iota : PrimeRegularRootEmbedding p k K
      (FiniteSymplecticFixed r a))
    (sigma : FieldGroup a) (psi : IBr iota) :
    let _ : MulAction (FieldGroup a) (IBr iota) :=
      canonicalFieldIBrAction r a ha iota
    sigma • psi = IrreducibleBrauerCharacter.twist iota psi
      (fieldAction r a ha sigma⁻¹) := by
  rfl

/-- The transported conformal action and canonical field action satisfy the
semidirect compatibility required for the literal set of characters. -/
theorem conformalSemidirectCompatible_actual
    {p : ℕ} {C Fq k K : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (r a : ℕ) (ha : 0 < a)
    [Finite (FiniteSymplecticFixed r a)]
    (iota : PrimeRegularRootEmbedding p k K
      (FiniteSymplecticFixed r a))
    (S : ConformalStructuralSource r a ha C Fq) :
    let _ : MulAction C (IBr iota) :=
      conformalIBrAction r a iota S.multiplier S.kernelEquiv
    let _ : MulAction (FieldGroup a) (IBr iota) :=
      canonicalFieldIBrAction r a ha iota
    SemidirectActionCompatible (X := IBr iota)
      S.conformalFieldAction := by
  dsimp only
  intro sigma c psi
  change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi
        (transportedConformalAction r a S.multiplier S.kernelEquiv c⁻¹))
        (fieldAction r a ha sigma⁻¹) =
    IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi
        (fieldAction r a ha sigma⁻¹))
      (transportedConformalAction r a S.multiplier S.kernelEquiv
        ((S.conformalFieldAction sigma) c)⁻¹)
  rw [IrreducibleBrauerCharacter.twist_mul,
    IrreducibleBrauerCharacter.twist_mul, S.fieldRestriction sigma c]

/-- Every conformal element fixes every literal irreducible Brauer
character.  The innerness itself is the exact E1 conformal input; this proof
checks its consequence on the function-valued carrier. -/
theorem conformal_fixation_actual
    {p : ℕ} {C Fq k K : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (r a : ℕ) (ha : 0 < a)
    [Finite (FiniteSymplecticFixed r a)]
    (iota : PrimeRegularRootEmbedding p k K
      (FiniteSymplecticFixed r a))
    (S : ConformalStructuralSource r a ha C Fq) :
    let _ : MulAction C (IBr iota) :=
      conformalIBrAction r a iota S.multiplier S.kernelEquiv
    ∀ c : C, ∀ psi : IBr iota, c • psi = psi := by
  dsimp only
  intro c psi
  obtain ⟨h, hh⟩ := S.conformalInner c⁻¹
  change IrreducibleBrauerCharacter.twist iota psi
      (transportedConformalAction r a S.multiplier S.kernelEquiv c⁻¹) =
    psi
  rw [hh]
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  exact PrimeRegularClassFunction.twist_conj psi.1 h

/-- Every orbit of the conformal overgroup on the literal Brauer-character
carrier is a singleton.  Thus the character itself is the representative
required in the first Jordan-reduction hypothesis. -/
theorem conformal_orbit_eq_singleton_actual
    {p : ℕ} {C Fq k K : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (r a : ℕ) (ha : 0 < a)
    [Finite (FiniteSymplecticFixed r a)]
    (iota : PrimeRegularRootEmbedding p k K
      (FiniteSymplecticFixed r a))
    (S : ConformalStructuralSource r a ha C Fq)
    (psi : IBr iota) :
    let _ : MulAction C (IBr iota) :=
      conformalIBrAction r a iota S.multiplier S.kernelEquiv
    MulAction.orbit C psi = {psi} := by
  dsimp only
  letI : MulAction C (IBr iota) :=
    conformalIBrAction r a iota S.multiplier S.kernelEquiv
  ext chi
  rw [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact conformal_fixation_actual r a ha iota S c psi
  · intro hchi
    subst chi
    exact ⟨1, one_smul C psi⟩

/-- The FLZ stabiliser factorisation on the literal Brauer-character
carrier.  There is no set of characters, character action, fixation, or
factorisation premise. -/
theorem conformal_stabilizer_factorization_actual
    {p : ℕ} {C Fq k K : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (r a : ℕ) (ha : 0 < a)
    [Finite (FiniteSymplecticFixed r a)]
    (iota : PrimeRegularRootEmbedding p k K
      (FiniteSymplecticFixed r a))
    (S : ConformalStructuralSource r a ha C Fq)
    (psi : IBr iota) :
    let _ : MulAction C (IBr iota) :=
      conformalIBrAction r a iota S.multiplier S.kernelEquiv
    let _ : MulAction (FieldGroup a) (IBr iota) :=
      canonicalFieldIBrAction r a ha iota
    let hcompat : SemidirectActionCompatible (X := IBr iota)
        S.conformalFieldAction :=
      conformalSemidirectCompatible_actual r a ha iota S
    let _ : MulAction (C ⋊[S.conformalFieldAction] FieldGroup a)
        (IBr iota) :=
      semidirectMulAction S.conformalFieldAction hcompat
    ∀ g : C ⋊[S.conformalFieldAction] FieldGroup a,
      g ∈ MulAction.stabilizer
          (C ⋊[S.conformalFieldAction] FieldGroup a) psi ↔
        ∃ c : C, ∃ sigma : FieldGroup a,
          sigma ∈ MulAction.stabilizer (FieldGroup a) psi ∧
            g = SemidirectProduct.inl c *
              SemidirectProduct.inr sigma := by
  dsimp only
  letI : MulAction C (IBr iota) :=
    conformalIBrAction r a iota S.multiplier S.kernelEquiv
  letI : MulAction (FieldGroup a) (IBr iota) :=
    canonicalFieldIBrAction r a ha iota
  have hcompat : SemidirectActionCompatible (X := IBr iota)
      S.conformalFieldAction :=
    conformalSemidirectCompatible_actual r a ha iota S
  letI : MulAction (C ⋊[S.conformalFieldAction] FieldGroup a)
      (IBr iota) :=
    semidirectMulAction S.conformalFieldAction hcompat
  exact mem_semidirect_stabilizer_iff_exists_right_factorization
    S.conformalFieldAction hcompat
      (conformal_fixation_actual r a ha iota S) psi

/-- The extension deduction for the literal fixed-point group and its
canonical field action.

The canonical copy of the group, the root embedding on that copy, and the
irreducible pullback character are constructed in the kernel.  The
conjugation square is proved above.  Thus the only input is Navarro's cyclic
extension principle, not an extension or an Assumption 5.3 premise. -/
theorem field_stabilizer_extension_actual
    {p : ℕ} {k K : Type}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (r a : ℕ) (ha : 0 < a)
    [Finite (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
    (iota : PrimeRegularRootEmbedding p k K
      (FiniteSymplecticFixed r a))
    (principle :
      Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} p k)
    (psi : IBr iota) :
    let phi := fieldAction r a ha
    let _ : MulAction (FiniteSymplecticFixed r a) (IBr iota) :=
      rightAutomorphismAction (X := IBr iota)
        (MulAut.conj : FiniteSymplecticFixed r a →*
          MulAut (FiniteSymplecticFixed r a))
    let _ : MulAction (FieldGroup a) (IBr iota) :=
      canonicalFieldIBrAction r a ha iota
    let hcompat := rightAutomorphismSemidirectCompatible
      (X := IBr iota) phi
    let _ : MulAction
        (FiniteSymplecticFixed r a ⋊[phi] FieldGroup a) (IBr iota) :=
      semidirectMulAction phi hcompat
    let hinner : ∀ h : FiniteSymplecticFixed r a,
        (SemidirectProduct.inl h :
          FiniteSymplecticFixed r a ⋊[phi] FieldGroup a) • psi = psi :=
      fun h ↦ by
        rw [semidirect_inl_smul]
        exact inner_fixes_ibr iota h psi
    let eH := canonicalHToEmbeddedEquiv psi hinner
    let iotaEmbedded := iota.alongMulEquiv eH
    ∃ W : FDRep k (embeddedHStabilizer (phi := phi) psi),
      Representation.IsIrreducible W.ρ ∧
      pullbackPrimeRegularAlongEquiv eH psi.1 =
        Representation.brauerCharacterOfRootEmbedding W.ρ iotaEmbedded ∧
      Nonempty (Representation.Extension
        (embeddedHStabilizer (phi := phi) psi) W.ρ) := by
  dsimp only
  letI : MulAction (FiniteSymplecticFixed r a) (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : FiniteSymplecticFixed r a →*
        MulAut (FiniteSymplecticFixed r a))
  letI : MulAction (FieldGroup a) (IBr iota) :=
    canonicalFieldIBrAction r a ha iota
  have hcompat : SemidirectActionCompatible (X := IBr iota)
      (fieldAction r a ha) :=
    rightAutomorphismSemidirectCompatible
      (X := IBr iota) (fieldAction r a ha)
  letI : MulAction
      (FiniteSymplecticFixed r a ⋊[fieldAction r a ha] FieldGroup a)
      (IBr iota) :=
    semidirectMulAction (fieldAction r a ha) hcompat
  have hinner : ∀ h : FiniteSymplecticFixed r a,
      (SemidirectProduct.inl h :
        FiniteSymplecticFixed r a ⋊[fieldAction r a ha] FieldGroup a) •
          psi = psi := by
    intro h
    rw [semidirect_inl_smul]
    exact inner_fixes_ibr iota h psi
  let eH := canonicalHToEmbeddedEquiv psi hinner
  have hpullback : pullbackPrimeRegularAlongEquiv eH psi.1 =
      PrimeRegularClassFunction.pullback eH.symm.toMonoidHom psi.1 := by
    apply PrimeRegularClassFunction.ext
    intro x
    rfl
  let iotaEmbedded := iota.alongMulEquiv eH
  have pullbackIrreducible : IsIrreducibleBrauerCharacter iotaEmbedded
      (pullbackPrimeRegularAlongEquiv eH psi.1) := by
    rw [hpullback]
    exact IrreducibleBrauerCharacter.pullback_isIrreducibleBrauerCharacter
      iota eH psi
  apply global_extension_actual iota (fieldAction r a ha) principle psi
    iotaEmbedded pullbackIrreducible
  intro d x
  exact canonicalEmbedded_conjugationSquare
    (phi := fieldAction r a ha) psi hinner d x

end ModularRep.PaperProofs.EvenFieldAssumption53Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
