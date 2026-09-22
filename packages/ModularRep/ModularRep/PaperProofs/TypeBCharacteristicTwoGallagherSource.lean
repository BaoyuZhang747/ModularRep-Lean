import ModularRep.PaperProofs.TypeBCharacteristicTwoExtensionCarriers
import ModularRep.PaperProofs.TypeBCharacteristicTwoConstituentSource

/-!
# The precise modular Gallagher source for Lemma 4.6

This is the one-way composite E1 specialization of Navarro, Corollary 8.20,
p. 176: restrict an actual extension to an intermediate group and apply
modular Gallagher there. Irreducible modular characters of the abelian
quotient are linear (Navarro, Theorem 1.20 and the following paragraph,
p. 14; their linear character interpretation is Problem 2.7, p. 46).
The source conclusion is
the literal product formula on prime regular elements. Identifying these
K-valued functions with the published character convention is E1/U and
requires all three displayed root agreements.

The source never supplies character invariance, any action compatibility,
an abstract lies-over relation, or a stabilizer factorization. In particular
the extension is on Gamma_theta itself, as in the manuscript, and not on
the larger semidirect product containing field automorphisms.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoGallagherSource

open TypeBLemma47LeviApplication TypeBCharacteristicTwoExtensionCarriers
open TypeBCharacteristicTwoConstituentSource

universe u

/-- Agreement is only on the roots actually needed by the smaller carrier;
the two lifts need not agree on all elements of the coefficient field. -/
def RootsAgree {A B k K : Type u} [Group A] [Finite A] [Group B] [Finite B]
    [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
    (iotaA : PrimeRegularRootEmbedding 2 k K A)
    (iotaB : PrimeRegularRootEmbedding 2 k K B) : Prop :=
  ∀ z : rootsOfUnity (primeRegularExponent 2 B) k,
    iotaB.lift (((z : kˣ) : k)) = iotaA.lift (((z : kˣ) : k))

/-- Uniform finite group certificate: an actual extension on the full
ambient inertia group yields the published quotient-linear product formula
for each actual character of H_theta above theta. Commutativity refers to
Gamma/N, whereas the scalar character lives on H_theta/N. -/
def Navarro820AbelianProductPrinciple (k K : Type u)
    [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K] : Prop :=
  ∀ {Gamma : Type u} [Group Gamma] [Finite Gamma]
    (H N : Subgroup Gamma) [H.Normal] [N.Normal]
    [IsMulCommutative (Gamma ⧸ N)] (hNH : N ≤ H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN)
    (iotaI : PrimeRegularRootEmbedding 2 k K (BrauerInertia H N iotaN theta))
    (iotaA : PrimeRegularRootEmbedding 2 k K (AmbientInertia N iotaN theta)),
    RootsAgree iotaI iotaN → RootsAgree iotaA iotaN → RootsAgree iotaA iotaI →
    ∀ (extension : AmbientExtension N iotaN theta iotaA) (eta : IBr iotaI),
      OccursAlong (baseEmbeddingInBrauerInertia H N hNH iotaN theta)
        iotaI iotaN eta theta →
      HasGallagherProduct H N iotaN theta iotaI iotaA extension.character eta

end ModularRep.PaperProofs.TypeBCharacteristicTwoGallagherSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
