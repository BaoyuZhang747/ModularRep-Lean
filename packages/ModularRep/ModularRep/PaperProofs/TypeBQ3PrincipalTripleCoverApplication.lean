import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.TypeBQ3PrincipalBrauerInflation
import ModularRep.PaperProofs.TypeBQ3PrincipalWeightInflation
import ModularRep.PaperProofs.TypeBQ3PrincipalOrbitApplication

/-!
# Lifting the same principal matching to the actual triple cover

The root is restricted along the constructed central projection. Specified
principal Brauer deflation and the published ordinary inflation graph give
two carrier transports. The accepted SO correspondence is constructed once
and lifted through these transports. Its exact graph and equivariance for
every actual matched automorphism pair are retained.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalTripleCoverApplication

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelInertia
open TypeBRankThreePrincipalCountBinding
open TypeBQ3TripleCoverCarrier
open TypeBQ3PrincipalWeightInflation
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The downstairs convention is computed from the same actual projection. -/
abbrev rootDown
    (rootX : letI : Finite X := finite_X matrixSource
      PrimeRegularRootEmbedding 2 k K X) :
    PrimeRegularRootEmbedding 2 k K (G (ZMod 3)) := by
  letI : Finite X := finite_X matrixSource
  exact TypeBQ3PrincipalBrauerInflation.downRoot
    (q matrixSource freeSource) (q_surjective matrixSource freeSource) rootX

/-- Both decompositions come from the same specified weight sources used in
the final correspondence. The principal image is derived internally. -/
def brauerDeflation :
    letI : Finite X := finite_X matrixSource
    ∀ (rootX : PrimeRegularRootEmbedding 2 k K X)
      (SX : CoverWeightSource (k := k) (K := K) X)
      (literalX : ∀ c, SX.operations.ambientBlockData.blockIdempotent c = c.val)
      (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
      (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
      (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX)
      (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
      (primitive : CentralPrimeToPrimitiveImageSource (k := k)
        (q matrixSource freeSource) (q_surjective matrixSource freeSource) rootX.prime
        (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)),
      BrauerFibre rootX bX ≃
        OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b := by
  letI : Finite X := finite_X matrixSource
  intro rootX SX literalX S literal bX hbX b hb primitive
  letI : Fintype (LiteralPrimitiveBlock k X) := SX.operations.ambientBlockData.fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k (G (ZMod 3))) :=
    S.operations.ambientBlockData.fintypeBlock
  exact TypeBQ3PrincipalBrauerInflation.principalBrauerDeflation
    (q matrixSource freeSource) (q_surjective matrixSource freeSource)
    (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
    rootX (coverDecomposition SX literalX) (omegaDecomposition (ZMod 3) S literal)
    bX hbX b hb primitive

/-- One constructed Omega matching lifts to the complete actual principal
triple-cover fibres. The commuting square and the literal ordinary inflation
graph identify the same matching for every compatible pair of actors. -/
theorem exists_principalTripleCover_equivariantEquiv :
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
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (h : H (ZMod 3)),
        (∀ x : X, q matrixSource freeSource (alpha.unop x) =
          (conjugationOp (G (ZMod 3)) h).unop (q matrixSource freeSource x)) →
        ∀ phi : BrauerFibre rootX bX,
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
  obtain ⟨seed, _seedDelta, seedSO⟩ :=
    TypeBQ3PrincipalOrbitApplication.exists_principalOmega_SO_equivariantEquiv
      S literal (rootDown matrixSource freeSource rootX) b hb delta indexTwo outside
      SH literalH bH hbH Msys dgn brauerSource covering
  let EB := brauerDeflation matrixSource freeSource rootX SX literalX S literal
    bX hbX b hb primitive
  let EW := principalWeightEquiv weightSource
  let lifted : BrauerFibre rootX bX ≃ CoverWeight SX bX :=
    EB.trans (seed.trans EW.symm)
  have graph (phi : BrauerFibre rootX bX) : EW (lifted phi) = seed (EB phi) :=
    EW.apply_symm_apply (seed (EB phi))
  refine ⟨seed, lifted, seedSO, graph, ?_, ?_⟩
  · intro phi
    have rawGraph := principalWeightEquiv_graph weightSource (lifted phi)
    change ClassInflates (q matrixSource freeSource) (lifted phi).val
      (EW (lifted phi)).val at rawGraph
    rw [graph phi] at rawGraph
    exact rawGraph
  · intro alpha h square phi
    have brauerNatural :
        EB (TypeBQ3PrincipalBrauerInflation.principalStep rootX
          (coverDecomposition SX literalX) bX hbX alpha phi) =
        brauerStep (ZMod 3) S literal (rootDown matrixSource freeSource rootX)
          b hb h (EB phi) := by
      apply Subtype.ext
      exact TypeBQ3PrincipalBrauerInflation.principalBrauerDeflation_twist
        (q matrixSource freeSource) (q_surjective matrixSource freeSource)
        (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
        rootX (coverDecomposition SX literalX) (omegaDecomposition (ZMod 3) S literal)
        bX hbX b hb primitive alpha (conjugationOp (G (ZMod 3)) h) square phi
    apply EW.injective
    calc
      EW (lifted (TypeBQ3PrincipalBrauerInflation.principalStep rootX
          (coverDecomposition SX literalX) bX hbX alpha phi)) =
          seed (EB (TypeBQ3PrincipalBrauerInflation.principalStep rootX
            (coverDecomposition SX literalX) bX hbX alpha phi)) := graph _
      _ = seed (brauerStep (ZMod 3) S literal (rootDown matrixSource freeSource rootX)
          b hb h (EB phi)) := congrArg seed brauerNatural
      _ = weightStep (ZMod 3) S literal b hb h (seed (EB phi)) := seedSO h (EB phi)
      _ = weightStep (ZMod 3) S literal b hb h (EW (lifted phi)) :=
        congrArg (weightStep (ZMod 3) S literal b hb h) (graph phi).symm
      _ = EW (coverWeightStep SX literalX bX hbX alpha (lifted phi)) :=
        (principalWeightEquiv_equivariant weightSource alpha h square (lifted phi)).symm

end ModularRep.PaperProofs.TypeBQ3PrincipalTripleCoverApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
