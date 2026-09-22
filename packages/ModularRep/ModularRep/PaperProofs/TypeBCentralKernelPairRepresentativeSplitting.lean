import ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding

/-!
# Every raw representative of a literal pair over one modular system

The local character is the scoped reduction of the weight's own ordinary
character supplied by the splitting pair binding. Simultaneous conjugation
transports an existing complete witness through the checked Butterfly
construction. An actual inner conjugating element then supplies the witness
for every representative of the same weight class.

The ambient group stays arbitrary and finite. In the principal matrix
application it must retain both the SO and field factors.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelPairRepresentativeSplitting

open ModularRep TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelConjugateInertia TypeBCentralKernelButterflyCertificate
open TypeBCentralKernelTripleCarriers TypeBCentralKernelTripleRootFamily
open TypeBLocalReductionInstantiation
open TypeBCentralKernelPairSplittingBinding
open TypeBCentralKernelConjugatePairBinding (tripleData baseCharacter)

variable {p : ℕ} {K O k A : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A]
  (Msys : ModularSystem p K O k)
  (G : Subgroup A) [G.Normal]
  (root : PrimeRegularRootEmbedding p k K G)
  (calibration : RootResidueCompatible Msys root)
  (catalogues : ∀ (theta : IBr root) (W : CharacterWeight p K G)
    (hUT : U G W ≤ T G root theta), PhysicalBlockFamily (k := k)
      (inside G (T G root theta)) (inside (U G W) (T G root theta)))
  [HasEnoughRootsOfUnity K (Nat.card G)]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding p k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- Raw inertia inclusion and the complete witness on the prescribed pair. -/
def WitnessAt (theta : IBr root) (W : CharacterWeight p K G) : Prop :=
  ∃ hUT : U G W ≤ T G root theta,
    Nonempty (PairWitness Msys G root calibration theta W hUT navarro
      (catalogues theta W hUT))

/-- The literal class relation is existence of one actual raw representative. -/
def ClassWitness (theta : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) : Prop :=
  ∃ W : CharacterWeight p K G, classOf W = w ∧
    WitnessAt Msys G root calibration catalogues navarro theta W

variable (certificate : ButterflyCertificate p k K)

include certificate in
/-- Both conjugate characters and all root equations are computed from
the same modular system, ordinary characters and specified catalogues. -/
theorem transfer_conjugate (theta : IBr root) (W : CharacterWeight p K G)
    (hUT : U G W ≤ T G root theta) (a : A)
    (witness : PairWitness Msys G root calibration theta W hUT navarro
      (catalogues theta W hUT)) :
    Nonempty (PairWitness Msys G root calibration
      (conjugationOp G a • theta) (conjugateWeight G a W)
      (conjugate_raw_le_character G root theta W a hUT) navarro
      (catalogues (conjugationOp G a • theta) (conjugateWeight G a W)
        (conjugate_raw_le_character G root theta W a hUT))) := by
  let thetaA := conjugationOp G a • theta
  let WA := conjugateWeight G a W
  let hUTA := conjugate_raw_le_character G root theta W a hUT
  let family := coherentData Msys G root calibration catalogues
  let D := family.data theta W hUT
  let DA := family.data thetaA WA hUTA
  have ambientLifts : D.ambientRoot.lift = DA.ambientRoot.lift :=
    family.ambientLifts theta W hUT a
  have quotientLifts : DA.quotientRoot.lift = D.quotientRoot.lift :=
    family.quotientLifts theta W hUT a
  refine TypeBCentralKernelConjugateTripleTransport.transfer_to_image
    (inside G (T G root theta)) (inside G (T G root thetaA))
    (inside (U G W) (T G root theta)) (inside (U G WA) (T G root thetaA))
    (characterInertiaEquiv G root theta a) (baseEquiv G root theta a)
    (base_anchor G root theta a) (localAmbient_image G root theta W a)
    (tripleData G root theta W hUT D) (tripleData G root thetaA WA hUTA DA)
    (baseCharacter G root theta W hUT D)
    (localCharacter Msys G root calibration theta W hUT navarro (catalogues theta W hUT))
    (baseCharacter G root thetaA WA hUTA DA)
    (localCharacter Msys G root calibration thetaA WA hUTA navarro
      (catalogues thetaA WA hUTA))
    witness ?_ ?_ ?_ ?_ ?_ certificate
  · intro z _ _
    exact congrFun ambientLifts (z : k)
  · exact TypeBCentralKernelConjugateCharacters.baseRoot_lift_eq G root theta a
  · exact TypeBCentralKernelConjugateCharacters.localRoot_lift_eq G root theta a
      W hUT D.quotientRoot hUTA DA.quotientRoot quotientLifts
  · exact TypeBCentralKernelConjugateCharacters.baseBrauer_pullback G root theta a
  · intro x y hxy
    exact (TypeBCentralKernelConjugateCharacters.localBrauer_value_of_ambient
      G root theta a W hUT D.quotientRoot hUTA DA.quotientRoot
      (quotientReduction Msys W navarro) (quotientReduction Msys WA navarro)
      (quotientReduction_value Msys W navarro) (quotientReduction_value Msys WA navarro)
      x y (congrArg Subtype.val hxy).symm).symm

include certificate in
theorem witnessAt_conjugate (theta : IBr root) (W : CharacterWeight p K G) (a : A)
    (existsWitness : WitnessAt Msys G root calibration catalogues navarro theta W) :
    WitnessAt Msys G root calibration catalogues navarro
      (conjugationOp G a • theta) (conjugateWeight G a W) := by
  obtain ⟨hUT, ⟨witness⟩⟩ := existsWitness
  refine ⟨conjugate_raw_le_character G root theta W a hUT, ?_⟩
  exact transfer_conjugate Msys G root calibration catalogues navarro certificate
    theta W hUT a witness

include certificate in
theorem witnessAt_of_class_eq (theta : IBr root) (W V : CharacterWeight p K G)
    (sameClass : classOf W = classOf V)
    (existsWitness : WitnessAt Msys G root calibration catalogues navarro theta W) :
    WitnessAt Msys G root calibration catalogues navarro theta V := by
  obtain ⟨g, raw⟩ := exists_inner_conjugate_of_class_eq G W V sameClass
  have transported := witnessAt_conjugate Msys G root calibration catalogues navarro
    certificate theta W (g : A) existsWitness
  simpa only [raw, inner_fixes_character] using transported

include certificate in
theorem classWitness_conjugate (theta : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) (a : A)
    (existsWitness : ClassWitness Msys G root calibration catalogues navarro theta w) :
    ClassWitness Msys G root calibration catalogues navarro
      (conjugationOp G a • theta) (conjugationOp G a • w) := by
  obtain ⟨W, representative, witness⟩ := existsWitness
  refine ⟨conjugateWeight G a W, ?_,
    witnessAt_conjugate Msys G root calibration catalogues navarro certificate
      theta W a witness⟩
  rw [classOf_conjugateWeight, representative]

include certificate in
/-- Inversion proves the reverse direction for the same actual class relation. -/
theorem classWitness_conjugate_iff (theta : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) (a : A) :
    ClassWitness Msys G root calibration catalogues navarro
        (conjugationOp G a • theta) (conjugationOp G a • w) ↔
      ClassWitness Msys G root calibration catalogues navarro theta w := by
  constructor
  · intro witness
    have back := classWitness_conjugate Msys G root calibration catalogues navarro
      certificate (conjugationOp G a • theta) (conjugationOp G a • w) a⁻¹ witness
    simpa only [map_inv, inv_smul_smul] using back
  · exact classWitness_conjugate Msys G root calibration catalogues navarro
      certificate theta w a

include certificate in
/-- One literal class witness supplies a witness for every raw representative,
while the original Brauer character remains fixed. -/
theorem all_representatives (theta : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G))
    (existsWitness : ClassWitness Msys G root calibration catalogues navarro theta w)
    (V : CharacterWeight p K G) (representative : classOf V = w) :
    WitnessAt Msys G root calibration catalogues navarro theta V := by
  obtain ⟨W, chosenRepresentative, witness⟩ := existsWitness
  exact witnessAt_of_class_eq Msys G root calibration catalogues navarro certificate
    theta W V (chosenRepresentative.trans representative.symm) witness

end ModularRep.PaperProofs.TypeBCentralKernelPairRepresentativeSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
