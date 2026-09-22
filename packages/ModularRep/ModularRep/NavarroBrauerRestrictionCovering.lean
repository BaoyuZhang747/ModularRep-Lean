import ModularRep.NavarroCoveringBrauerExtension

/-!
# Covering from an actual Brauer restriction

This E1 source interface records Navarro (9.2) followed by the supported-centre
form of Passman's criterion (9.5). It uses the literal constituent definition
and actual primitive-idempotent block indices, not an arbitrary relation or
label.

The K deductions turn an actual restriction equality into a single-term
nonnegative expansion and apply that interface. No normaliser, radical
subgroup, Fischer block, induced-block equality, or global-extension choice is
part of this source principle.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.NavarroBrauerRestrictionCovering

open ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroCoveringBrauerExtension
open Representation.Extension

universe u

noncomputable local instance subgroupFintypeForRestrictionCovering
    {A : Type u} [Group A] [Finite A] (N : Subgroup A) : Fintype N :=
  Fintype.ofFinite N

/-- The precise general direction of Navarro (9.2) followed by (9.5).
Normality and agreement of the two modular root conventions are explicit.
The source quantifies over all characters and literal block catalogues. -/
def Navarro9295BrauerRestrictionCoveringPrinciple
    (p : Nat) (k K : Type u)
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] : Prop :=
  ∀ {A : Type u} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal],
    ∀ (iotaA : PrimeRegularRootEmbedding p k K A)
      (iotaN : PrimeRegularRootEmbedding p k K N)
      (rootAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent p N) k,
        iotaN.lift (((zeta : kˣ) : k)) =
          iotaA.lift (((zeta : kˣ) : k)))
      (fieldSource : SpathCoefficientField p k iotaA.prime)
      {AmbientBlock BaseBlock : Type u}
      [Fintype AmbientBlock] [Fintype BaseBlock]
      {ambientIdempotent : AmbientBlock → k[A]}
      {baseIdempotent : BaseBlock → k[N]}
      (ambientBlocks : BlockIdempotentDecomposition ambientIdempotent)
      (baseBlocks : BlockIdempotentDecomposition baseIdempotent)
      (hinjA : IrreducibleBrauerCharacterInjectivity iotaA)
      (hinjN : IrreducibleBrauerCharacterInjectivity iotaN)
      (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
      (baseCatalogue : BlockCentralCharacterCatalogue baseBlocks)
      (Phi : IBr iotaA) (phi : IBr iotaN),
      BrauerOccursInRestriction N iotaA iotaN Phi phi →
      CentralCharacterCovers N
        (ambientCatalogue.centralCharacter
          (irreducibleBrauerCharacterBlock iotaA hinjA ambientBlocks Phi))
        (baseCatalogue.centralCharacter
          (irreducibleBrauerCharacterBlock iotaN hinjN baseBlocks phi))

/-- A restriction equal to phi is the one-term expansion with multiplicity
one at phi. This is a deduction from the actual class-function equality. -/
theorem brauerOccursInRestriction_of_pullback_eq
    {p : Nat} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Finite A]
    (N : Subgroup A)
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaN : PrimeRegularRootEmbedding p k K N)
    (Phi : IBr iotaA) (phi : IBr iotaN)
    (hrestriction : PrimeRegularClassFunction.pullback N.subtype Phi.1 = phi.1) :
    BrauerOccursInRestriction N iotaA iotaN Phi phi := by
  classical
  refine ⟨Finsupp.single phi 1, by simp, ?_⟩
  intro x
  have hx := congrArg
    (fun f : PrimeRegularClassFunction K N p => f x) hrestriction
  simpa using hx

/-- The block of an actual extension covers the block of its restricted
character. The source theorem is general, and the constituent witness is
constructed internally from the SAME extension term. -/
theorem centralCharacterCovers_of_extension
    {p : Nat} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Fintype A]
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (N : Subgroup A) [N.Normal]
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaN : PrimeRegularRootEmbedding p k K N)
    (rootAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent p N) k,
      iotaN.lift (((zeta : kˣ) : k)) =
        iotaA.lift (((zeta : kˣ) : k)))
    (fieldSource : SpathCoefficientField p k iotaA.prime)
    {AmbientBlock BaseBlock : Type u}
    [Fintype AmbientBlock] [Fintype BaseBlock]
    {ambientIdempotent : AmbientBlock → k[A]}
    {baseIdempotent : BaseBlock → k[N]}
    (ambientBlocks : BlockIdempotentDecomposition ambientIdempotent)
    (baseBlocks : BlockIdempotentDecomposition baseIdempotent)
    (hinjA : IrreducibleBrauerCharacterInjectivity iotaA)
    (hinjN : IrreducibleBrauerCharacterInjectivity iotaN)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (baseCatalogue : BlockCentralCharacterCatalogue baseBlocks)
    (phi : IBr iotaN)
    (extension : BrauerCharacterExtensionWitness iotaA iotaN phi) :
    CentralCharacterCovers N
      (ambientCatalogue.centralCharacter
        (irreducibleBrauerCharacterBlock iotaA hinjA ambientBlocks extension.1))
      (baseCatalogue.centralCharacter
        (irreducibleBrauerCharacterBlock iotaN hinjN baseBlocks phi)) :=
  S9295 N iotaA iotaN rootAgreement fieldSource
    ambientBlocks baseBlocks hinjA hinjN ambientCatalogue baseCatalogue
    extension.1 phi
    (brauerOccursInRestriction_of_pullback_eq
      N iotaA iotaN extension.1 phi extension.2)

end ModularRep.NavarroBrauerRestrictionCovering



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
