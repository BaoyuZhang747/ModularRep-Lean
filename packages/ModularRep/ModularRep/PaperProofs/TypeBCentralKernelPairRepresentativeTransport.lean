import ModularRep.PaperProofs.TypeBCentralKernelConjugatePairBinding

/-!
# One literal pair witness and every raw representative

The relation on a character and a weight class is defined by existence of
an actual raw representative with the complete literal pair witness. Its
conjugation covariance and its consequence for every raw representative
are deductions from the checked simultaneous pair transport.

The data family fixes specified catalogues and roots independently of any
witness. Its two coherence fields are only equations of root lifts for
actual conjugate groups; it contains no pair existence, correspondence,
triple transport or inductive-condition field.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelPairRepresentativeTransport

open ModularRep TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelConjugateInertia TypeBCentralKernelConjugatePairBinding
open TypeBCentralKernelLocalReduction TypeBCentralKernelButterflyCertificate

universe u

variable {p : ℕ} {k K A : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A] (G : Subgroup A) [G.Normal]
  (root : PrimeRegularRootEmbedding p k K G)

/-- Exact root coherence of independently fixed literal pair data.
Existence of such a family on an application's prescribed coefficients
and specified catalogues remains explicit; no source inhabitant is declared. -/
structure CoherentData where
  data : ∀ (theta : IBr root) (W : CharacterWeight p K G)
    (hUT : U G W ≤ T G root theta), PairData G root theta W hUT
  ambientLifts : ∀ (theta : IBr root) (W : CharacterWeight p K G)
      (hUT : U G W ≤ T G root theta) (a : A),
    (data theta W hUT).ambientRoot.lift =
      (data (conjugationOp G a • theta) (conjugateWeight G a W)
        (conjugate_raw_le_character G root theta W a hUT)).ambientRoot.lift
  quotientLifts : ∀ (theta : IBr root) (W : CharacterWeight p K G)
      (hUT : U G W ≤ T G root theta) (a : A),
    (data (conjugationOp G a • theta) (conjugateWeight G a W)
        (conjugate_raw_le_character G root theta W a hUT)).quotientRoot.lift =
      (data theta W hUT).quotientRoot.lift

variable [IsAlgClosed K] (family : CoherentData G root)
  (navarro : Navarro318Certificate p k K)

/-- Actual raw inertia inclusion followed by the fixed complete literal witness. -/
def WitnessAt (theta : IBr root) (W : CharacterWeight p K G) : Prop :=
  ∃ hUT : U G W ≤ T G root theta,
    Nonempty (PairWitness G root theta W hUT (family.data theta W hUT) navarro)

/-- The existential raw-representative relation used for orientation.
It is a definition, not an unspecified predicate or source field. -/
def ClassWitness (theta : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) : Prop :=
  ∃ W : CharacterWeight p K G, classOf W = w ∧ WitnessAt G root family navarro theta W

variable (certificate : ButterflyCertificate p k K)

include certificate

theorem witnessAt_conjugate (theta : IBr root) (W : CharacterWeight p K G) (a : A)
    (existsWitness : WitnessAt G root family navarro theta W) :
    WitnessAt G root family navarro (conjugationOp G a • theta) (conjugateWeight G a W) := by
  obtain ⟨hUT, ⟨witness⟩⟩ := existsWitness
  let hUTA := conjugate_raw_le_character G root theta W a hUT
  refine ⟨hUTA, ?_⟩
  exact transfer_conjugate G root theta W hUT (family.data theta W hUT) navarro a
    (family.data (conjugationOp G a • theta) (conjugateWeight G a W) hUTA)
    (family.ambientLifts theta W hUT a) (family.quotientLifts theta W hUT a)
    certificate witness

theorem witnessAt_of_class_eq (theta : IBr root) (W V : CharacterWeight p K G)
    (sameClass : classOf W = classOf V)
    (existsWitness : WitnessAt G root family navarro theta W) :
    WitnessAt G root family navarro theta V := by
  obtain ⟨g, raw⟩ := exists_inner_conjugate_of_class_eq G W V sameClass
  have transported := witnessAt_conjugate G root family navarro certificate theta W (g : A)
    existsWitness
  simpa only [raw, inner_fixes_character] using transported

theorem classWitness_conjugate (theta : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) (a : A)
    (existsWitness : ClassWitness G root family navarro theta w) :
    ClassWitness G root family navarro (conjugationOp G a • theta)
      (conjugationOp G a • w) := by
  obtain ⟨W, representative, witness⟩ := existsWitness
  refine ⟨conjugateWeight G a W, ?_,
    witnessAt_conjugate G root family navarro certificate theta W a witness⟩
  rw [classOf_conjugateWeight, representative]

/-- Covariance is proved for the actual literal relation and all ambient
actors. Inversion supplies the reverse direction; no raw involution is used. -/
theorem classWitness_conjugate_iff (theta : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) (a : A) :
    ClassWitness G root family navarro (conjugationOp G a • theta)
        (conjugationOp G a • w) ↔ ClassWitness G root family navarro theta w := by
  constructor
  · intro witness
    have back := classWitness_conjugate G root family navarro certificate
      (conjugationOp G a • theta) (conjugationOp G a • w) a⁻¹ witness
    simpa only [map_inv, inv_smul_smul] using back
  · exact classWitness_conjugate G root family navarro certificate theta w a

/-- The orientation selected for one raw representative works for every
representative, by inner conjugation of an existing witness. -/
theorem all_representatives (theta : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G))
    (existsWitness : ClassWitness G root family navarro theta w)
    (V : CharacterWeight p K G) (representative : classOf V = w) :
    WitnessAt G root family navarro theta V := by
  obtain ⟨W, chosenRepresentative, witness⟩ := existsWitness
  exact witnessAt_of_class_eq G root family navarro certificate theta W V
    (chosenRepresentative.trans representative.symm) witness

end ModularRep.PaperProofs.TypeBCentralKernelPairRepresentativeTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
