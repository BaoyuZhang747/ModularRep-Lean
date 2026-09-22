import ModularRep.CentralCharacterCovering
import ModularRep.BrauerCharacterHomPullback
import ModularRep.IBrBlock
import ModularRep.SpathNavarroSourceAdapter
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Choosing a Brauer extension in a covering block

Two uniform E1 source interfaces are explicit. S9495 packages Navarro (9.4)
with the supported-centre form of Passman's criterion (9.5). S820 is not
Navarro (8.20) alone: it packages the cyclic quotient route of Navarro
(8.20)+(8.7), together with the modular cyclic, fixed-root-lift, and
tensor-compatibility identifications needed for the displayed K-valued twist
formula. It does not supply an initial extension; eta remains an explicit
argument, obtainable separately from the existing Navarro (8.12) constructor.

The kernel deductions restrict the returned quotient-linear twist to the
normal subgroup and select the resulting actual extension in a supplied
covering block. No radical subgroup, normaliser, Fischer group, induced-block
equality, or iBAW conclusion occurs in either uniform source interface.

BrauerOccursInRestriction is an actual nonnegative character expansion, not a
source-supplied relation. Literal instantiation of the source interfaces and
the covering calculation remain separate from these K deductions.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.NavarroCoveringBrauerExtension

open ModularRep.FDRepSimpleClassKZero
open Representation.Extension

universe u

noncomputable local instance subgroupFintypeForCoveringExtension
    {A : Type u} [Group A] [Finite A] (N : Subgroup A) : Fintype N :=
  Fintype.ofFinite N

/-- Literal Brauer constituent support in a restriction: a finite
nonnegative integral combination of the actual irreducible Brauer characters,
with nonzero multiplicity at the specified base character. -/
def BrauerOccursInRestriction
    {p : Nat} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Finite A]
    (N : Subgroup A)
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaN : PrimeRegularRootEmbedding p k K N)
    (Phi : IBr iotaA) (phi : IBr iotaN) : Prop :=
  ∃ multiplicity : IBr iotaN →₀ Nat,
    multiplicity phi ≠ 0 ∧
      ∀ x : PrimeRegularElement (G := N) p,
        Phi.1 (PrimeRegularElement.map N.subtype x) =
          multiplicity.sum (fun psi n => (n : K) * psi.1 x)

/-- Uniform Navarro (9.4), with actual block covering expressed by the
equivalent supported-central character criterion of (9.5). The block labels
come from the displayed complete primitive-idempotent decompositions.

Root agreement binds the characteristic-zero values on the subgroup to the
same modular character convention. `fieldSource` is the existing source's
coefficient field hypothesis, not a selected-block assertion. -/
def Navarro9495BrauerCoveringPrinciple
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
      (B : AmbientBlock) (b : BaseBlock) (phi : IBr iotaN),
      irreducibleBrauerCharacterBlock iotaN hinjN baseBlocks phi = b →
      CentralCharacterCovers N
        (ambientCatalogue.centralCharacter B)
        (baseCatalogue.centralCharacter b) →
      ∃ Phi : IBr iotaA,
        irreducibleBrauerCharacterBlock iotaA hinjA ambientBlocks Phi = B ∧
          BrauerOccursInRestriction N iotaA iotaN Phi phi

/-- The uniform cyclic-quotient twist source interface for the composite
Navarro (8.20)+(8.7) route, together with the modular cyclic, fixed-root-lift,
and tensor-compatibility identifications used in its K-valued formula. It
exposes a quotient-linear twist of an explicit initial extension rather than
asserting the desired restriction equality. No block or local-subgroup data
occur here. -/
def Navarro820CyclicBrauerTwistPrinciple
    (p : Nat) (k K : Type u)
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] : Prop :=
  ∀ {A : Type u} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaN : PrimeRegularRootEmbedding p k K N)
    (rootAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent p N) k,
      iotaN.lift (((zeta : kˣ) : k)) =
        iotaA.lift (((zeta : kˣ) : k)))
    (hcyclic : IsCyclic (A ⧸ N))
    (phi : IBr iotaN)
    (eta : BrauerCharacterExtensionWitness iotaA iotaN phi)
    (Phi : IBr iotaA),
    BrauerOccursInRestriction N iotaA iotaN Phi phi →
      ∃ lambda : (A ⧸ N) →* Kˣ,
        ∀ x : PrimeRegularElement (G := A) p,
          Phi.1 x =
            ((lambda (QuotientGroup.mk' N x.1) : Kˣ) : K) * eta.1.1 x

/-- The quotient linear twist returned by the uniform Gallagher source is
trivial on `N`. Thus every character supplied by that source really extends
the SAME base character; the conclusion is a K deduction, not a source field. -/
theorem restriction_eq_of_cyclic_twist
    {p : Nat} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Fintype A]
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (N : Subgroup A) [N.Normal]
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaN : PrimeRegularRootEmbedding p k K N)
    (rootAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent p N) k,
      iotaN.lift (((zeta : kˣ) : k)) =
        iotaA.lift (((zeta : kˣ) : k)))
    (hcyclic : IsCyclic (A ⧸ N))
    (phi : IBr iotaN)
    (eta : BrauerCharacterExtensionWitness iotaA iotaN phi)
    (Phi : IBr iotaA)
    (hOccurs : BrauerOccursInRestriction N iotaA iotaN Phi phi) :
    PrimeRegularClassFunction.pullback N.subtype Phi.1 = phi.1 := by
  obtain ⟨lambda, htwist⟩ :=
    S820 N iotaA iotaN rootAgreement hcyclic phi eta Phi hOccurs
  apply PrimeRegularClassFunction.ext
  intro x
  have hcoset : QuotientGroup.mk' N ((x.1 : N) : A) = 1 :=
    (QuotientGroup.eq_one_iff ((x.1 : N) : A)).mpr x.1.property
  change Phi.1 (PrimeRegularElement.map N.subtype x) = phi.1 x
  calc
    Phi.1 (PrimeRegularElement.map N.subtype x) =
        ((lambda (QuotientGroup.mk' N ((x.1 : N) : A)) : Kˣ) : K) *
          eta.1.1 (PrimeRegularElement.map N.subtype x) :=
      htwist (PrimeRegularElement.map N.subtype x)
    _ = eta.1.1 (PrimeRegularElement.map N.subtype x) := by
      rw [hcoset, map_one]
      simp
    _ = phi.1 x :=
      congrArg (fun f : PrimeRegularClassFunction K N p => f x) eta.2

/-- Choose an actual Brauer extension in any specified covering block.
Both representation theoretic principles are uniform in all finite groups,
normal subgroups, characters and catalogues. The selected covering equality
is an intermediate hypothesis, to be proved by the separate block-covering
calculation in an application; no induced-block conclusion is assumed here. -/
theorem exists_extension_in_covering_block
    {p : Nat} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Fintype A]
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (N : Subgroup A) [N.Normal]
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaN : PrimeRegularRootEmbedding p k K N)
    (rootAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent p N) k,
      iotaN.lift (((zeta : kˣ) : k)) =
        iotaA.lift (((zeta : kˣ) : k)))
    (fieldSource : SpathCoefficientField p k iotaA.prime)
    (hcyclic : IsCyclic (A ⧸ N))
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
    (B : AmbientBlock) (phi : IBr iotaN)
    (eta : BrauerCharacterExtensionWitness iotaA iotaN phi)
    (hcover : CentralCharacterCovers N
      (ambientCatalogue.centralCharacter B)
      (baseCatalogue.centralCharacter
        (irreducibleBrauerCharacterBlock iotaN hinjN baseBlocks phi))) :
    ∃ extension : BrauerCharacterExtensionWitness iotaA iotaN phi,
      irreducibleBrauerCharacterBlock iotaA hinjA ambientBlocks extension.1 = B := by
  obtain ⟨Phi, hB, hOccurs⟩ :=
    S9495 N iotaA iotaN rootAgreement fieldSource
      ambientBlocks baseBlocks hinjA hinjN ambientCatalogue baseCatalogue
      B (irreducibleBrauerCharacterBlock iotaN hinjN baseBlocks phi) phi rfl hcover
  have hrestriction := restriction_eq_of_cyclic_twist
    S820 N iotaA iotaN rootAgreement hcyclic phi eta Phi hOccurs
  exact ⟨⟨Phi, hrestriction⟩, hB⟩

end ModularRep.NavarroCoveringBrauerExtension



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
