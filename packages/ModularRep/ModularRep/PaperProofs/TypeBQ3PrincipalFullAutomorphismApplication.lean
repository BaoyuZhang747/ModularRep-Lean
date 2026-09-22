import ModularRep.PaperProofs.TypeBQ3PrincipalTripleCoverApplication
import ModularRep.PaperProofs.TypeBQ3TripleCoverAutomorphisms

/-!
# Every actual automorphism preserves the same principal correspondence

The accepted principal lift supplies one matching with its deflation equation
and literal ordinary inflation graph. The actual quotient descent and matrix
automorphism realization supply a matching SO actor for every automorphism
of the triple cover. Applying the accepted equivariance statement to that
actor proves full automorphism equivariance for the same matching.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalFullAutomorphismApplication

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelInertia
open TypeBRankThreePrincipalCountBinding
open TypeBQ3TripleCoverCarrier
open TypeBQ3PrincipalWeightInflation
open TypeBQ3PrincipalTripleCoverApplication
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The same constructed principal correspondence intertwines every actual
automorphism, with its original deflation equation and ordinary graph. -/
theorem exists_principalTripleCover_fullAutomorphismEquivariantEquiv
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource) :
  letI : Finite X := finite_X matrixSource
  ∀ (rootX : PrimeRegularRootEmbedding 2 k K X)
    (SX : CoverWeightSource (k := k) (K := K) X)
    (literalX : ∀ c, SX.operations.ambientBlockData.blockIdempotent c = c.val)
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val),
  letI : Fintype (LiteralPrimitiveBlock k X) := SX.operations.ambientBlockData.fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k (G (ZMod 3))) :=
    S.operations.ambientBlockData.fintypeBlock
  ∀ (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX)
    (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
    (primitive : CentralPrimeToPrimitiveImageSource (k := k)
      (q matrixSource freeSource) (q_surjective matrixSource freeSource) rootX.prime
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource))
    (weightSource : FLZ23Source
    (q matrixSource freeSource) (q_surjective matrixSource freeSource)
    (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
    SX literalX S literal rootX bX hbX b hb
    (TypeBQ3PrincipalBrauerInflation.principal_image
      (q matrixSource freeSource) (q_surjective matrixSource freeSource)
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
      rootX (omegaDecomposition (ZMod 3) S literal) bX hbX b hb primitive))
  [HasEnoughRootsOfUnity K (Nat.card (H (ZMod 3)))]
  (delta : H (ZMod 3)) (indexTwo : (G (ZMod 3)).index = 2)
  (outside : delta ∉ G (ZMod 3))
  (SH : SOWeightSource (k := k) (K := K) (ZMod 3))
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (bH : LiteralPrimitiveBlock k (H (ZMod 3))) (hbH : IsPrincipal bH)
  [Fintype (OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b)]
  [DecidableEq (OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b)]
  [Fintype (OmegaWeight (ZMod 3) S b)]
  [DecidableEq (OmegaWeight (ZMod 3) S b)]
  [Fintype (SOWeight (ZMod 3) SH bH)]
  [DecidableEq (SOWeight (ZMod 3) SH bH)]
  (Msys : ModularSystem 2 K O k)
  (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G (ZMod 3)) Msys)
  (brauerSource : TypeBQ3PrincipalBrauerBinding.LiteralSource
    S literal (rootDown matrixSource freeSource rootX) b hb delta indexTwo outside)
  (covering : TypeBQ3PrincipalWeightBinding.PublishedWeightCovering
    S literal b hb delta indexTwo outside SH literalH bH hbH Msys dgn),
    ∃ seed : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b ≃
        OmegaWeight (ZMod 3) S b,
    ∃ lifted : BrauerFibre rootX bX ≃ CoverWeight SX bX,
      (∀ (h : H (ZMod 3))
          (theta : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b),
        seed (brauerStep (ZMod 3) S literal (rootDown matrixSource freeSource rootX)
          b hb h theta) = weightStep (ZMod 3) S literal b hb h (seed theta)) ∧
      (∀ phi : BrauerFibre rootX bX,
        principalWeightEquiv weightSource (lifted phi) =
          seed (brauerDeflation matrixSource freeSource rootX SX literalX S literal
            bX hbX b hb primitive phi)) ∧
      (∀ phi : BrauerFibre rootX bX,
        ClassInflates (q matrixSource freeSource) (lifted phi).val
          (seed (brauerDeflation matrixSource freeSource rootX SX literalX S literal
            bX hbX b hb primitive phi)).val) ∧
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : BrauerFibre rootX bX),
        lifted (TypeBQ3PrincipalBrauerInflation.principalStep rootX
          (coverDecomposition SX literalX) bX hbX alpha phi) =
        coverWeightStep SX literalX bX hbX alpha (lifted phi)) := by
  letI : Finite X := finite_X matrixSource
  intro rootX SX literalX S literal
  letI : Fintype (LiteralPrimitiveBlock k X) := SX.operations.ambientBlockData.fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k (G (ZMod 3))) :=
    S.operations.ambientBlockData.fintypeBlock
  intro bX hbX b hb primitive weightSource ordinaryRootsH delta indexTwo outside
    SH literalH bH hbH fintypeBrauer decidableBrauer fintypeOmegaWeight decidableOmegaWeight
    fintypeSOWeight decidableSOWeight Msys dgn brauerSource covering
  obtain ⟨seed, lifted, seedSO, deflation, graph, matched⟩ :=
    TypeBQ3PrincipalTripleCoverApplication.exists_principalTripleCover_equivariantEquiv
      matrixSource freeSource rootX SX literalX S literal bX hbX b hb primitive weightSource
      delta indexTwo outside SH literalH bH hbH Msys dgn brauerSource covering
  refine ⟨seed, lifted, seedSO, deflation, graph, ?_⟩
  intro alpha phi
  obtain ⟨h, square⟩ :=
    TypeBQ3TripleCoverAutomorphisms.exists_SO_actor matrixSource freeSource automorphisms alpha
  exact matched alpha h square phi

end ModularRep.PaperProofs.TypeBQ3PrincipalFullAutomorphismApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
