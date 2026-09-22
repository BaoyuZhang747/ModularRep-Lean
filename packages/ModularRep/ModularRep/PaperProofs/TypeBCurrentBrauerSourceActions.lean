import ModularRep.PaperProofs.TypeBCurrentBrauerSource

/-!
# Proposition 4.13 on the actual Spin and special Clifford carriers

The source records retain the actual regular embedding, minimal proper Levi,
common roots, constituent geometry, and the published modular Jordan bijection.
They do not contain a representative, stabilizer equality, extension, or the
assumption of the Jordan reduction. Original type A/B2/Spin representatives,
component return, Clifford transfer, the diagonal quotient, full-field
promotion, cyclic extension and exhaustive orbit coverage are Lean deductions.

The external geometric boundary is Malle--Testerman, Theorems 21.7 and 22.5;
Ruhstorfer, Lemma 4.5(a)--(b); and Feng--Li--Zhang, Lemma 5.1, the proof
of Proposition 5.2, Proposition 5.6 and Theorem 5.7. The Jordan equivalence is
on the complete literal idempotent packets and retains its block correspondence.
Its source interpretation on these precise algebraic groups is an explicit U
identification, as are the common coefficient and root identifications.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCurrentBrauerHypothesis

open ModularRep FDRepSimpleClassKZero TypeBCliffordCarriers
open TypeBRegularLeviRationalCarriers TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeSelection TypeBLemma47LeviApplication
open TypeBCharacteristicTwoConstituentSource TypeBRankThreeJordanPacketCarriers
open TypeBCurrentBrauerTransport TypeBCurrentLeviAssembly
open TypeBCurrentJordanCliffordCarriers
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {n p f : ℕ} {F A k K : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field A] [Algebra F A]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable {normF : NormSource n F} {normA : NormSource n A}
variable {parameters : OddFieldParameters F p f}
variable [Finite (SpecialClifford n F)] [NeZero f]
variable (fs : FieldActionSource n F p f parameters normF)
variable (iotaG : PrimeRegularRootEmbedding 2 k K (Spin n F normF))
variable {BG : Type} [Fintype BG] {bG : BG → k[Spin n F normF]}
variable (blocksG : BlockIdempotentDecomposition bG)
variable (parametersG : ParameterSource fs (k := k))
variable (Frob : MulAut (SpecialClifford n A))
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable (points : CliffordFixedPointSource n p f F A normF normA Frob)

namespace LeviSource

variable {fs iotaG blocksG parametersG Frob points}
variable {s : SemisimpleIndex (n := n) (p := p) (F := F)}
variable (source : LeviSource fs iotaG blocksG parametersG Frob points s)

@[instance_reducible] def gammaCharacters :
    MulAction (Gamma Frob source.Lbar) (IBr iotaG) :=
  letI := diagonalAction iotaG
  MulAction.compHom _ (gammaEmbedding points source.Lbar)

@[instance_reducible] def fieldCharacters :
    MulAction (parametersG.stabilizer s) (IBr iotaG) :=
  letI := fieldAction fs iotaG
  MulAction.compHom _ (parametersG.stabilizer s).subtype

/-- The injection used by stabilizer transport is derived from the bijection
on the complete packets; its values are the original ambient characters. -/
def jordanCharacter :
    letI : Fintype source.BL := source.finiteBL
    Packet (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL → IBr iotaG :=
  fun psi => (source.jordan psi).val

theorem jordanCharacter_injective : Function.Injective source.jordanCharacter := by
  intro x y h
  exact source.jordan.injective (Subtype.ext h)


end LeviSource
end ModularRep.PaperProofs.TypeBCurrentBrauerHypothesis









/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
