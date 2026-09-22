import ModularRep.PaperProofs.TypeBCurrentBrauerTransport
import ModularRep.PaperProofs.TypeBCurrentLeviAssembly
import ModularRep.PaperProofs.TypeBCurrentJordanFiniteProduct
import ModularRep.PaperProofs.TypeBCurrentJordanQuotient
import ModularRep.PaperProofs.TypeBCurrentPrincipalResults
import ModularRep.PaperProofs.TypeBRankThreeJordanOvergroup

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
-- The consumers use record projections, so omit unused constructor-injectivity auxiliaries.
set_option genInjectivity false
-- Keep SizeOf instances; omit unused constructor specification simp/grind auxiliaries.
set_option genSizeOfSpec false
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

/-- The chosen proper Levi and the literal published Jordan data for one
semisimple block parameter. All factor inputs are uniform in the actual
packet character and its actual restriction constituent.

Exact U calibration: for every `s`, `Lbar` is the primal Levi dual to the
unique minimal dual Levi containing `C°(s) C(s)^F`. Ruhstorfer, Lemma
4.5(a)--(b), supplies a conjugate of the chosen Frobenius power that
stabilises the Levi and its idempotent. The manuscript then conjugates
the Levi and the corresponding dual pair to obtain stability under the
chosen Frobenius power itself. Its chosen field group is exactly
`parametersG.stabilizer s`. The subgroup copies `H` and `N` are the original
rational `L` and `[L,L]` under the canonical equivalences in
`TypeBLeviRepresentativeCarriers`; all three roots use those same copies.
`eL` is the image of the Broué--Michel `e_s^L` under that canonical
group algebra transport, and its dual label is the same original class `s`.
`jordan` is the modular Jordan bijection of Feng--Li--Zhang, Lemma 5.1 and
the proof of Proposition 5.2, transported to `H` by that same equivalence.
`blockCorrespondence` is its block correspondence on the complete unions,
not an independently selected matching. `components` interprets the lower
root-component and block-support conclusions in the proof of their
Proposition 5.6 and Theorem 5.7, including principality of every B factor
on the actual restriction constituent.

This uniform specified calibration is an explicit accepted U boundary;
inhabiting the algebraic record alone does not establish it. No resulting
character representative, stabilizer equality or extension belongs to it. -/
structure LeviGeometry (s : SemisimpleIndex (n := n) (p := p) (F := F)) where
  Lbar : Subgroup (SpecialClifford n A)
  levi_le_spin : Lbar ≤ SpinSubgroup n A normA
  proper : Lbar ≠ SpinSubgroup n A normA
  leviStable : Lbar.map Frob.toMonoidHom = Lbar
  decomposition : ∀ x : SpecialClifford n A,
    ∃ g ∈ SpinSubgroup n A normA, ∃ z ∈ Subgroup.center (SpecialClifford n A), x = g * z
  intersection : pairedLevi Lbar ⊓ SpinSubgroup n A normA ≤ Lbar
  lang : TypeBRankThreeJordanDiagonalProduct.LeviLangSource Frob Lbar
  field : FieldData Frob Lbar (parametersG.stabilizer s)
  field_square : ∀ (e : parametersG.stabilizer s) (g : Gamma Frob Lbar),
    gammaEmbedding points Lbar (field.fieldOnGamma e g) =
      fs.action e.val (gammaEmbedding points Lbar g)
 
/-- Original Levi characters, their literal blocks, and raw constituent sources. -/
structure LeviLocalSource (s : SemisimpleIndex (n := n) (p := p) (F := F))
    extends LeviGeometry fs parametersG Frob points s where
  iotaL : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar)
  iotaN : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar)
  iotaGamma : PrimeRegularRootEmbedding 2 k K (Gamma Frob Lbar)
  BL : Type
  [finiteBL : Fintype BL]
  bL : BL → k[H Frob Lbar]
  blocksL : BlockIdempotentDecomposition bL
  eL : k[H Frob Lbar]
  centralL : IsMulCentral eL
  idempotentL : IsIdempotentElem eL
  gammaInvariant : ∀ g : Gamma Frob Lbar,
    MonoidAlgebra.mapDomainRingEquiv k (MulAut.conjNormal (H := H Frob Lbar) g) eL = eL
  fieldInvariant : ∀ e : parametersG.stabilizer s,
    MonoidAlgebra.mapDomainRingEquiv k
      (restrictAutomorphismHom (H Frob Lbar) field.fieldOnGamma field.H_stable e) eL = eL
  clifford : CliffordInput Frob Lbar iotaL iotaN iotaGamma
  constituent : ∀ psi : Packet (rootH Frob Lbar iotaL) blocksL eL,
    ∃ theta : IBr (rootN Frob Lbar iotaN),
      Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
        (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi.val theta
  components : ∀ (psi : Packet (rootH Frob Lbar iotaL) blocksL eL)
      (theta : IBr (rootN Frob Lbar iotaN)),
    Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
      (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi.val theta →
    ComponentInput Frob Lbar leviStable field iotaN theta

/-- The complete same-parameter Jordan packets and their published equivariance.
The precise U interpretation is the one stated on `LeviGeometry`. -/
structure LeviSource (s : SemisimpleIndex (n := n) (p := p) (F := F))
    extends LeviLocalSource (K := K) fs parametersG Frob points s where
  jordan : Packet (rootH Frob Lbar iotaL) blocksL eL ≃
    Packet iotaG blocksG (parametersG.idempotent s)
  gamma_equivariant :
    letI := packetMulAction (rootH Frob Lbar iotaL) blocksL eL
      (MulAut.conjNormal (H := H Frob Lbar)) gammaInvariant
    letI := diagonalAction iotaG
    ∀ (g : Gamma Frob Lbar) (psi : Packet (rootH Frob Lbar iotaL) blocksL eL),
      (jordan (g • psi)).val = gammaEmbedding points Lbar g • (jordan psi).val
  field_equivariant :
    letI := packetMulAction (rootH Frob Lbar iotaL) blocksL eL
      (restrictAutomorphismHom (H Frob Lbar) field.fieldOnGamma field.H_stable) fieldInvariant
    letI := fieldAction fs iotaG
    ∀ (e : parametersG.stabilizer s) (psi : Packet (rootH Frob Lbar iotaL) blocksL eL),
      (jordan (e • psi)).val = (e : FieldGroup f) • (jordan psi).val
  blockCorrespondence : LiteralSupport eL ≃ LiteralSupport (parametersG.idempotent s)
  block_equation : ∀ psi : Packet (rootH Frob Lbar iotaL) blocksL eL,
    supportingBlock iotaG blocksG (jordan psi).val =
      (blockCorrespondence ⟨supportingBlock (rootH Frob Lbar iotaL) blocksL psi.val,
        psi.property⟩).val

-- The stored Fintype is installed explicitly by consumers, never as a global projection instance.

end ModularRep.PaperProofs.TypeBCurrentBrauerHypothesis





/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
