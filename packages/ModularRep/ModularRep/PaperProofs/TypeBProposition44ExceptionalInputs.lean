import ModularRep.PaperProofs.TypeBExceptionalProposition44Instantiation

/-!
# Independent inputs for the exceptional branch of Proposition 4.3

The structural parameters first fix the canonical free-presentation cover
of the caller's same Omega quotient. The following package then records
only the coefficient and specified block sources used by the checked
exceptional application. Finite primitive blocks and sufficient ordinary
roots are fields, so the package is required only on this branch.

Its family and cover are computed. The complete normalized witness is
obtained by the existing exceptional theorem, which derives local specified
compatibility and subgroup cyclicity before applying the generic published
cyclic-defect result. Neither deduction nor a branch conclusion is a field.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBProposition44ExceptionalInputs

open ModularRep FDRepSimpleClassKZero
open TypeBCliffordCarriers TypeBSpinCoverSource
open TypeBExceptionalCanonicalCover TypeBExceptionalProposition44Instantiation
open TypeBExceptionalPrimitiveFamilySplitting TypeBLocalReductionInstantiation
open TypeBLocalPhysicalBlockBinding TypeBFullCriterionSplittingSource
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family

variable {n p f ell : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  (N : NormSource n F) (parameters : OddFieldParameters F p f)
  (exceptional : (n, Nat.card F) = (3, 3))
  (omega : ExceptionalOmegaSource N parameters exceptional)
  (freeSource : FreePresentationCoverSource)

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  (Msys : ModularSystem ell K O k)
  (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
  (divides : ell ∣ Nat.card (Omega N))

/-- Select the structural cover before introducing its specified block data. -/
def selectedCover :
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional omega
    EllPrimeCoverSource ell (ExceptionalCover N) := by
  letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional omega
  exact ellPrimeCover N parameters exceptional omega freeSource Msys.prime odd
    (nondefining_three exceptional nondefining)

/-- Only independent source data on the already fixed exceptional carrier.
The structural and prime-domain indices are retained explicitly. -/
structure Inputs
    {n p f ell : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
    (N : NormSource n F) (parameters : OddFieldParameters F p f)
    (exceptional : (n, Nat.card F) = (3, 3))
    (omega : ExceptionalOmegaSource N parameters exceptional)
    (freeSource : FreePresentationCoverSource)
    {k K O : Type}
    [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
    [CharP k ell] [IsAlgClosed k] [CharZero K]
    (Msys : ModularSystem ell K O k)
    (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
    (divides : ell ∣ Nat.card (Omega N)) where
  blockFintype : Fintype (LiteralPrimitiveBlock k (ExceptionalCover N))
  ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (ExceptionalCover N))
  data :
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional omega
    letI := blockFintype
    PrimitiveBlockData ell k K (ExceptionalCover N)
  navarro : ∀ (T : Type) [Group T] [Finite T]
    [HasEnoughRootsOfUnity K (Nat.card T)]
    (iota : PrimeRegularRootEmbedding ell k K T)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible
  expansion : ∀ (T : Type) [Group T] [Finite T]
    [HasEnoughRootsOfUnity K (Nat.card T)],
      ScopedDecompositionExpansionSource (H := T) Msys
  ordinary :
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional omega
    letI := blockFintype
    letI := ordinaryRoots
    ∀ Q : Subgroup (ExceptionalCover N),
      NormalizerOrdinarySource Msys data.blockSource.operations Q
  membership :
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional omega
    letI := blockFintype
    letI := ordinaryRoots
    OrdinaryInflationMembership Msys data.blockSource.operations ordinary
  coefficient : SpathCoefficientField ell k Msys.prime
  cyclicSource : TypeBExceptionalCyclicSplittingSource.CyclicDefectSplittingCertificate

variable
  (inputs : Inputs N parameters exceptional omega freeSource Msys odd nondefining divides)

/-- The family uses exactly the package's specified data and scoped reduction. -/
def family : Definition35Family ell := by
  letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional omega
  letI := inputs.blockFintype
  letI := inputs.ordinaryRoots
  exact primitiveFamily Msys inputs.data inputs.navarro

@[simp]
theorem family_H :
    (family N parameters exceptional omega freeSource Msys odd nondefining divides inputs).H =
      ExceptionalCover N := rfl

@[simp]
theorem family_K :
    (family N parameters exceptional omega freeSource Msys odd nondefining divides inputs).K =
      K := rfl

@[simp]
theorem family_k :
    (family N parameters exceptional omega freeSource Msys odd nondefining divides inputs).k =
      k := rfl

/-- The checked exceptional theorem supplies the full normalized output. -/
theorem witness :
    Nonempty (NormalizedFamilyWitness
      (familyAlgebra := (show Algebra O K from inferInstance))
      (family := family N parameters exceptional omega freeSource Msys odd nondefining
        divides inputs)
      Msys (selectedCover N parameters exceptional omega freeSource Msys odd nondefining)) := by
  letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional omega
  letI := inputs.blockFintype
  letI := inputs.ordinaryRoots
  exact exceptional_proposition_4_4_modular_instantiated N parameters exceptional omega
    freeSource Msys odd nondefining divides inputs.data inputs.navarro inputs.expansion
    inputs.ordinary inputs.membership inputs.coefficient inputs.cyclicSource

end ModularRep.PaperProofs.TypeBProposition44ExceptionalInputs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
