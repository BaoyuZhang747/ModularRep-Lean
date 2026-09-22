import ManuscriptIBAW.TypeC.OddRationalAutomorphisms
import ManuscriptIBAW.TypeC.OddGlobalFactorization

/-!
# The symplectic basic set and its automorphism action

The ordinary predicate is the specified rational ℓ′ union. Its stability
under the ambient automorphisms follows from the Cabanes–Enguehard and
Taylor source statements. The remaining assumptions supply the integral
decomposition theorem and the block operations.
-/

noncomputable section
open scoped MonoidAlgebra
namespace ManuscriptIBAW.TypeC.OddLiteralBasicSet
open ModularRep ModularRep.PaperProofs
open FDRepSimpleClassKZero ExactGrothendieckGroup DecompositionBasicSetBridge
open BlockFibreRestriction OrdinaryIrreducibleCharacter
open OddGFactorizationLemma312Relative TypeBCriterionHypotheses
open TypeCOddPrimeConformalCriterionCarriers
open TypeCCurrentConstituentFactorization (combinedAut)

variable (n : ℕ) (F : Type) [Field F] [Finite F]
  [(SpSubgroup n F).Normal]
  {ell : ℕ} {K O k : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  [Fintype (LiteralPrimitiveBlock k (SpSubgroup n F))]
  [MulAction (Ambient (fieldAction n F)) (LiteralPrimitiveBlock k (SpSubgroup n F))]
  (iota : PrimeRegularRootEmbedding ell k K (SpSubgroup n F))
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (SpSubgroup n F) => b.1))
  (upper : OddRationalSeries.Conformal n F K)
  (lower : OddRationalSeries.Symplectic n F K)
  (scope : StructuralSource n F)

local instance literalBaseFintype : Fintype (SpSubgroup n F) := Fintype.ofFinite _

/-- Integral decomposition and block assumptions on the specified rational
union. The two automorphism sources concern ordinary rational series. Their
consequence for the ℓ′ union is proved before defining the action on its
characters. -/
structure SourceInputs where
  regular : OddRationalAutomorphisms.RegularEmbeddingSource n F upper lower scope
  taylor : OddRationalAutomorphisms.Taylor72Source n F lower scope
  modularSystem : ModularSystem ell K O k
  reductionCompatible : StableReductionBrauerCharacterCompatibility modularSystem iota
  blockOf : {chi : Irr K (SpSubgroup n F) // lower.ellPrime ell chi} →
    LiteralPrimitiveBlock k (SpSubgroup n F)
  block_equivariant : ∀ (a : Ambient (fieldAction n F))
      (chi : {chi : Irr K (SpSubgroup n F) // lower.ellPrime ell chi}),
    blockOf ⟨ordinaryAutomorphismAct
        (combinedAut (SpSubgroup n F) (fieldAction n F) (naturalAction n F)) a chi.1,
      OddRationalAutomorphisms.ellPrime_ambient n F upper lower scope regular taylor
        ell a chi.1 chi.2⟩ = a • blockOf chi
  [finiteOrdinary : Finite {chi : Irr K (SpSubgroup n F) // lower.ellPrime ell chi}]
  linearEquiv : MonoidAlgebra ℤ {chi : Irr K (SpSubgroup n F) // lower.ellPrime ell chi} ≃ₗ[ℤ]
    MonoidAlgebra ℤ (IBr iota)
  decomposition : ∀ v : MonoidAlgebra ℤ {chi : Irr K (SpSubgroup n F) // lower.ellPrime ell chi},
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
        (linearEquiv v) =
      decompositionMapOfStableReduction modularSystem iota reductionCompatible
        (labelledSimpleClassKZero
          (TypeBOrdinaryLabelSplitting.ordinarySeriesLabel (K := K) (lower.ellPrime ell)) v)
  blockDiagonal : BlockDiagonalLinearEquiv blockOf
    (irreducibleBrauerCharacterBlock iota hinj blocks) linearEquiv
  brauerBlockEquivariant : ∀ (a : Ambient (fieldAction n F)) (phi : IBr iota),
    irreducibleBrauerCharacterBlock iota hinj blocks
        (IrreducibleBrauerCharacter.twist iota phi
          ((combinedAut (SpSubgroup n F) (fieldAction n F) (naturalAction n F)) a⁻¹)) =
      a • irreducibleBrauerCharacterBlock iota hinj blocks phi

variable (S : SourceInputs n F (O := O) iota hinj blocks upper lower scope)

/-- Construct the Conlon data using the proved stability, with the same rational
predicate and decomposition map. -/
def SourceInputs.toBasicSetSource : OddGlobalFactorization.BasicSetSource
    (O := O) (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iota hinj blocks where
  modularSystem := S.modularSystem
  reductionCompatible := S.reductionCompatible
  ordinary := {
    predicate := lower.ellPrime ell
    predicate_stable := OddRationalAutomorphisms.ellPrime_ambient n F upper lower scope
      S.regular S.taylor ell
    blockOf := S.blockOf
    block_equivariant := S.block_equivariant }
  finiteOrdinary := S.finiteOrdinary
  linearEquiv := S.linearEquiv
  decomposition := S.decomposition
  blockDiagonal := S.blockDiagonal
  brauerBlockEquivariant := S.brauerBlockEquivariant

end ManuscriptIBAW.TypeC.OddLiteralBasicSet

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
