import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.TypeBQ3PrincipalBrauerInflation
import ModularRep.PaperProofs.TypeBQ3PrincipalBrauerBinding
import ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual
import ModularRep.PaperProofs.TypeBQ3FaithfulFibreBinding
import ModularRep.PaperProofs.TypeBLiteralBlockReindex

/-!
The actual principal block of the retained triple cover is the named B1.
The complete downstairs principal dictionary has twelve characters. Literal
principal deflation transfers this count along the same q and its restricted
root. The complete named dictionary then identifies the unique twelve-entry
fibre. No value identification of the first printed row is required.

Both dictionaries and their specified block interpretations retain their
existing source scope. This module only derives the identification needed by
the final nine-block construction; it introduces no source structure.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3AssemblyPrincipalIdentification

open ModularRep FDRepSimpleClassKZero
open Formalisation.ComputationArithmetic
open ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate
open TypeBQ3TripleCoverCarrier TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBExceptionalQ3Proposition416Actual TypeBRankThreePrincipalCountBinding
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

variable {k K : Type} [Field k] [Field K] [CharZero K]
  [CharP k 2] [IsAlgClosed k]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

private theorem index_eq_B1_of_count_twelve (i : Q3Block)
    (count : q3BrauerCount i = 12) : i = .B1 := by
  cases i <;> simp_all [q3BrauerCount]

section Named

variable [Finite X]
  (root : PrimeRegularRootEmbedding 2 k K X)
  {d : Q3Block → k[X]} (blocks : BlockIdempotentDecomposition d)
  (brauerMap : LiteralBrauerOutputMap root)
  (map_injective : Function.Injective brauerMap.character)
  (map_surjective : Function.Surjective brauerMap.character)
  (compatible : BrauerBlockFibreCompatible root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks brauerMap)

private def namedFibreEquiv (i : Q3Block) :
    BrauerOutputFibre i ≃ BrauerFibre root (primitiveBlockOfLabel blocks i) :=
  (brauerBlockFibreEquiv root (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
    blocks brauerMap map_injective map_surjective compatible i).trans
    (TypeBQ3FaithfulFibreBinding.brauerFibreEquiv root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks i)

include map_injective map_surjective compatible in
private theorem named_fibre_card (i : Q3Block) :
    Nat.card (BrauerFibre root (primitiveBlockOfLabel blocks i)) = q3BrauerCount i := by
  calc
    Nat.card (BrauerFibre root (primitiveBlockOfLabel blocks i)) =
        Nat.card (BrauerOutputFibre i) :=
      Nat.card_congr (namedFibreEquiv root blocks brauerMap
        map_injective map_surjective compatible i).symm
    _ = Fintype.card (BrauerOutputFibre i) := Nat.card_eq_fintype_card
    _ = q3BrauerCount i := brauerOutputFibre_card i

include map_injective map_surjective compatible in
private theorem eq_B1_of_brauer_card_twelve
    (bX : LiteralPrimitiveBlock k X) (count : Nat.card (BrauerFibre root bX) = 12) :
    bX = primitiveBlockOfLabel blocks .B1 := by
  let i : Q3Block := (primitiveBlockEquiv blocks).symm bX
  have identified : primitiveBlockOfLabel blocks i = bX :=
    (primitiveBlockEquiv blocks).apply_symm_apply bX
  have count_i : q3BrauerCount i = 12 := by
    calc
      q3BrauerCount i =
          Nat.card (BrauerFibre root (primitiveBlockOfLabel blocks i)) :=
        (named_fibre_card root blocks brauerMap map_injective map_surjective compatible i).symm
      _ = Nat.card (BrauerFibre root bX) := by rw [identified]
      _ = 12 := count
  exact identified.symm.trans
    (congrArg (primitiveBlockOfLabel blocks) (index_eq_B1_of_count_twelve i count_i))

end Named

section Principal

variable [Finite X]
  (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
  (rootX : PrimeRegularRootEmbedding 2 k K X)
  {d : Q3Block → k[X]} (blocks : BlockIdempotentDecomposition d)
  (brauerMap : LiteralBrauerOutputMap rootX)
  (map_injective : Function.Injective brauerMap.character)
  (map_surjective : Function.Surjective brauerMap.character)
  (compatible : BrauerBlockFibreCompatible rootX
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding rootX) blocks brauerMap)
  (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX)
  (b : LiteralPrimitiveBlock k G3) (hb : IsPrincipal b)
  (delta : H (ZMod 3)) (indexTwo : (G (ZMod 3)).index = 2)
  (outside : delta ∉ G (ZMod 3))
  (primitive : CentralPrimeToPrimitiveImageSource (k := k)
    (q matrixSource freeSource) (q_surjective matrixSource freeSource) rootX.prime
    (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource))
  (principalSource : TypeBQ3PrincipalBrauerBinding.LiteralSource S literal
    (TypeBQ3PrincipalBrauerInflation.downRoot
      (q matrixSource freeSource) (q_surjective matrixSource freeSource) rootX)
    b hb delta indexTwo outside)

include matrixSource freeSource rootX brauerMap map_injective map_surjective compatible
  S literal hbX b hb delta indexTwo outside primitive principalSource in
/-- The same principal fibre is the unique specified named fibre of size twelve. -/
theorem principal_eq_B1 : bX = primitiveBlockOfLabel blocks .B1 := by
  letI : Fintype (LiteralPrimitiveBlock k X) :=
    TypeBLiteralBlockReindex.literalBlockFintype blocks
  letI : Fintype (LiteralPrimitiveBlock k G3) :=
    S.operations.ambientBlockData.fintypeBlock
  let rootDown := TypeBQ3PrincipalBrauerInflation.downRoot
    (q matrixSource freeSource) (q_surjective matrixSource freeSource) rootX
  let deflation : BrauerFibre rootX bX ≃ OmegaBrauer (ZMod 3) rootDown b :=
    TypeBQ3PrincipalBrauerInflation.principalBrauerDeflation
      (q matrixSource freeSource) (q_surjective matrixSource freeSource)
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
      rootX (TypeBLiteralBlockReindex.literalBlocks blocks)
      (omegaDecomposition (ZMod 3) S literal) bX hbX b hb primitive
  have downCount : Nat.card (OmegaBrauer (ZMod 3) rootDown b) = 12 := by
    calc
      Nat.card (OmegaBrauer (ZMod 3) rootDown b) =
          Nat.card SimplePrincipalBrauerLabel :=
        Nat.card_congr (TypeBQ3PrincipalBrauerBinding.labelEquiv
          S literal rootDown b hb delta indexTwo outside principalSource).symm
      _ = Fintype.card SimplePrincipalBrauerLabel := Nat.card_eq_fintype_card
      _ = 12 := by decide
  exact eq_B1_of_brauer_card_twelve rootX blocks brauerMap
    map_injective map_surjective compatible bX ((Nat.card_congr deflation).trans downCount)

include matrixSource freeSource rootX brauerMap map_injective map_surjective compatible
  S literal bX hbX b hb delta indexTwo outside primitive principalSource in
/-- Principality of the printed block is a consequence of the identification. -/
theorem named_B1_isPrincipal : IsPrincipal (primitiveBlockOfLabel blocks .B1) := by
  rw [← principal_eq_B1 matrixSource freeSource rootX blocks brauerMap
    map_injective map_surjective compatible S literal bX hbX b hb delta indexTwo
    outside primitive principalSource]
  exact hbX

end Principal

end ModularRep.PaperProofs.TypeBQ3AssemblyPrincipalIdentification


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
