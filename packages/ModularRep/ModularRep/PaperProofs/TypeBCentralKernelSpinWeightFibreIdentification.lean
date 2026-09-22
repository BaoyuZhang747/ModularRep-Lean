import ModularRep.PaperProofs.TypeBCentralKernelSpinFibreIdentification

/-!
# Specified weight fibres on the literal Spin and Omega equivalences

The normalizer idempotent square is deduced from reductions of the same
ordinary local character, canonical local roots, and the two guarded local
block laws in the fixed modular system. Block induction then determines the
same ambient primitive block. Restriction of the already constructed actual
ordinary-weight class equivalence follows only after these specified squares.

Inputs are the existing Navarro 3.18 reduction certificate, actual local
block operations and catalogues, their literal ambient allocations, and
root-guarded block compatibility. No local compatibility, ambient weight
block matching, weight-fibre equivalence, or inductive target is assumed.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCentralKernelSpinWeightFibreIdentification

open ModularRep CharacterWeight
open TypeBCentralKernelSpinFibreIdentification TypeBCentralKernelBlockSource
open TypeBCentralKernelBrauerBlocks TypeBCentralKernelLocalReduction
open TypeBCentralKernelLocalBlockBinding TypeBCentralKernelWeightBlockTransport
open TypeBFixedRootDefinitionFamily TypeBCentralKernelButterflyCertificate

universe u

section Normalizers

variable {X Y : Type u} [Group X] [Group Y]

/-- The actual homomorphism between the two normalizers is an equivalence,
with no normalizer-identification source. -/
def normalizerEquiv (e : X ≃* Y) (Q : Subgroup X) :
    Subgroup.normalizer (Q : Set X) ≃*
      Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup Y) : Set Y) :=
  MulEquiv.ofBijective (normalizerMap e.toMonoidHom Q) ⟨by
    intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h)),
    normalizerMap_surjective e.toMonoidHom e.surjective Q
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le)⟩

@[simp] theorem normalizerEquiv_val (e : X ≃* Y) (Q : Subgroup X)
    (x : Subgroup.normalizer (Q : Set X)) :
    (normalizerEquiv e Q x : Y) = e x := rfl

end Normalizers

section PhysicalBlocks

variable {p : ℕ} {k K X Y : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group X] [Finite X] [Group Y] [Finite Y]
  [Fintype (LiteralPrimitiveBlock k X)] [Fintype (LiteralPrimitiveBlock k Y)]

theorem selectedBlock_along (e : X ≃* Y)
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (DX : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k X => b.val))
    (DY : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k Y => b.val))
    (phiX : IBr iotaX) (phiY : IBr iotaY)
    (lifts : iotaY.lift = iotaX.lift)
    (values : phiY.val = PrimeRegularClassFunction.pullback e.symm.toMonoidHom phiX.val) :
    blockAlong e (block iotaX DX phiX) = block iotaY DY phiY := by
  have support :=
    TypeBCentralKernelButterflyCharacterIdentification.supported_along_of_lift_eq
      e iotaX iotaY (block iotaX DX phiX) phiX phiY lifts values
      ((supported_iff_block iotaX DX _ phiX).mpr rfl)
  exact ((supported_iff_block iotaY DY _ phiY).mp support).symm

end PhysicalBlocks

section WeightBlocks

variable {p : ℕ} {k K X Y : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [IsAlgClosed K]
  [Group X] [Fintype X] [Group Y] [Fintype Y]

variable (e : X ≃* Y)
  (iotaX : PrimeRegularRootEmbedding p k K X)
  (iotaY : PrimeRegularRootEmbedding p k K Y)
  (lifts : iotaY.lift = iotaX.lift)
  (OX : LocalBlockInductionOperations
    (p := p) (k := k) (K := K) (G := X) (Block := LiteralPrimitiveBlock k X))
  (OY : LocalBlockInductionOperations
    (p := p) (k := k) (K := K) (G := Y) (Block := LiteralPrimitiveBlock k Y))
  (reduction : Navarro318Certificate p k K)
  (guardX : GuardedBlockCompatibility iotaX OX)
  (guardY : GuardedBlockCompatibility iotaY OY)

include lifts reduction guardX guardY in
/-- The specified local block equation is proved, not a renamed matching
guard. Every local root and both actual reduction characters are constructed. -/
theorem ownNormalizerBlock_along (W : CharacterWeight p K X) :
    algebraMapOf (normalizerMap e.toMonoidHom W.subgroup) (ownNormalizerBlock OX W).val =
      (ownNormalizerBlock OY (rawWeightEquiv e W)).val := by
  let WY := rawWeightEquiv e W
  let n := normalizerEquiv e W.subgroup
  let qY := weightQuotientRoot iotaY WY
  let q := TypeBCentralKernelWeightTransport.localEquiv e.toMonoidHom e.surjective
    (equivKernel_isPGroup (p := p) e) W
  let qX := qY.alongMulEquiv q.symm
  let nX := normalizerRoot W qX
  let nY := normalizerRoot WY qY
  have nLifts : nX.lift = nY.lift := by
    ext z
    calc
      nX.lift z = qX.lift z :=
        PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift _ _ _ z
      _ = qY.lift z := qY.alongMulEquiv_lift q.symm z
      _ = nY.lift z :=
        (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift _ _ _ z).symm
  have agreeY : NormalizerRootAgreement iotaY WY.subgroup nY :=
    normalizerRoot_weightQuotientRoot_agrees iotaY WY
  have agreeX : NormalizerRootAgreement iotaX W.subgroup nX := by
    intro z
    exact (TypeBCentralKernelTripleRootFamily.surjection_agrees iotaY
      n.toMonoidHom n.surjective (equivKernel_isPGroup (p := p) n)
      nX nY nLifts agreeY z).trans (congrFun lifts _)
  obtain ⟨phiX, reduceX⟩ := exists_normalizer_reduction W qX reduction
  obtain ⟨phiY, reduceY⟩ := exists_normalizer_reduction WY qY reduction
  have values : phiY.val = PrimeRegularClassFunction.pullback n.symm.toMonoidHom phiX.val := by
    apply PrimeRegularClassFunction.ext
    intro y
    change phiY.val y = phiX.val (PrimeRegularElement.map n.symm.toMonoidHom y)
    have h := normalizer_reduction_quotient_square W e.toMonoidHom e.surjective
      (equivKernel_isPGroup (p := p) e) nX nY phiX phiY reduceX reduceY
      (PrimeRegularElement.map n.symm.toMonoidHom y)
    change phiX.val (PrimeRegularElement.map n.symm.toMonoidHom y) =
      phiY.val (PrimeRegularElement.map n.toMonoidHom
        (PrimeRegularElement.map n.symm.toMonoidHom y)) at h
    have hy : PrimeRegularElement.map n.toMonoidHom
        (PrimeRegularElement.map n.symm.toMonoidHom y) = y :=
      Subtype.ext (n.apply_symm_apply y.val)
    exact (h.trans (congrArg (fun z => phiY.val z) hy)).symm
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    (OX.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) WY.subgroup) :=
    (OY.inflatedNormalizerBlockData WY.subgroup).fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer ((W.subgroup.map e.toMonoidHom : Subgroup Y) : Set Y))) :=
    (OY.inflatedNormalizerBlockData WY.subgroup).fintypeBlock
  have hX := guardX.normalizer_block_of_reduction W nX phiX agreeX reduceX
  have hY := guardY.normalizer_block_of_reduction WY nY phiY agreeY reduceY
  change block nX (OX.inflatedNormalizerBlockData W.subgroup).blocks phiX =
    ownNormalizerBlock OX W at hX
  change block nY (OY.inflatedNormalizerBlockData WY.subgroup).blocks phiY =
    ownNormalizerBlock OY WY at hY
  have physical : blockAlong n (ownNormalizerBlock OX W) = ownNormalizerBlock OY WY := by
    rw [← hX, ← hY]
    exact selectedBlock_along n nX nY
      (OX.inflatedNormalizerBlockData W.subgroup).blocks
      (OY.inflatedNormalizerBlockData WY.subgroup).blocks phiX phiY nLifts.symm values
  exact congrArg Subtype.val physical

include lifts reduction guardX guardY in
/-- Induction of the specified local block determines the transported ambient
primitive block. The operations' ambient allocations remain literal b.val. -/
theorem rawWeightBlock_along
    (literalX : ∀ b, OX.ambientBlockData.blockIdempotent b = b.val)
    (literalY : ∀ b, OY.ambientBlockData.blockIdempotent b = b.val)
    (W : CharacterWeight p K X) :
    OY.rawWeightBlock (rawWeightEquiv e W) =
      primitiveBlockEquiv e (OX.rawWeightBlock W) := by
  let WY := rawWeightEquiv e W
  let U := Subgroup.normalizer (W.subgroup : Set X)
  let V := Subgroup.normalizer (WY.subgroup : Set Y)
  let n := normalizerEquiv e W.subgroup
  have hker : e.toMonoidHom.ker ≤ W.subgroup := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    exact bot_le
  have hmap : U.map e.toMonoidHom = V :=
    map_normalizer_eq_of_surjective_of_ker_le e.toMonoidHom e.surjective W.subgroup hker
  have saturated : ∀ x : X, x ∈ U ↔ e x ∈ V := by
    intro x
    change x ∈ U ↔ x ∈ V.comap e.toMonoidHom
    rw [← hmap, Subgroup.comap_map_eq_self (hker.trans W.subgroup.le_normalizer)]
  letI : Fintype (LiteralPrimitiveBlock k X) := OX.ambientBlockData.fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k Y) := OY.ambientBlockData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    (OX.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) WY.subgroup) :=
    (OY.inflatedNormalizerBlockData WY.subgroup).fintypeBlock
  have hX : BlockInducesTo U
      (OX.inflatedNormalizerBlockData W.subgroup).catalogue
      OX.ambientBlockData.catalogue (ownNormalizerBlock OX W) (OX.rawWeightBlock W) :=
    inducedBlock_spec U (OX.inflatedNormalizerBlockData W.subgroup).catalogue
      OX.ambientBlockData.catalogue (ownNormalizerBlock OX W) (OX.blockInductionDefined W)
  have physical : algebraMapOf e.toMonoidHom
      (OX.ambientBlockData.blockIdempotent (OX.rawWeightBlock W)) =
      OY.ambientBlockData.blockIdempotent (primitiveBlockEquiv e (OX.rawWeightBlock W)) := by
    rw [literalX, literalY]
    rfl
  have hY := blockInducesTo_map U V e.toMonoidHom e.surjective
    n.toMonoidHom n.surjective (fun _ => rfl) saturated
    OX.ambientBlockData.catalogue OY.ambientBlockData.catalogue
    (OX.inflatedNormalizerBlockData W.subgroup).catalogue
    (OY.inflatedNormalizerBlockData WY.subgroup).catalogue
    (ownNormalizerBlock OX W) (ownNormalizerBlock OY WY)
    (OX.rawWeightBlock W) (primitiveBlockEquiv e (OX.rawWeightBlock W))
    (ownNormalizerBlock_along e iotaX iotaY lifts OX OY reduction guardX guardY W)
    physical hX (OY.blockInductionDefined WY)
  exact (eq_inducedBlock_of_blockInducesTo V
    (OY.inflatedNormalizerBlockData WY.subgroup).catalogue OY.ambientBlockData.catalogue
    (ownNormalizerBlock OY WY) (OY.blockInductionDefined WY) hY).symm

end WeightBlocks

section WeightFibres

variable {p : ℕ} {k K X Y : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [IsAlgClosed K]
  [Group X] [Fintype X] [Group Y] [Fintype Y]

variable (e : X ≃* Y)
  (iotaX : PrimeRegularRootEmbedding p k K X)
  (iotaY : PrimeRegularRootEmbedding p k K Y)
  (lifts : iotaY.lift = iotaX.lift)
  (SX : LocalBlockInductionSource
    (p := p) (k := k) (K := K) (G := X) (Block := LiteralPrimitiveBlock k X))
  (SY : LocalBlockInductionSource
    (p := p) (k := k) (K := K) (G := Y) (Block := LiteralPrimitiveBlock k Y))
  (literalX : ∀ b, SX.operations.ambientBlockData.blockIdempotent b = b.val)
  (literalY : ∀ b, SY.operations.ambientBlockData.blockIdempotent b = b.val)
  (reduction : Navarro318Certificate p k K)
  (guardX : GuardedBlockCompatibility iotaX SX.operations)
  (guardY : GuardedBlockCompatibility iotaY SY.operations)

include lifts literalX literalY reduction guardX guardY in
theorem weightBlock_map
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X)) :
    SY.weightBlock (weightClassEquiv e w) = primitiveBlockEquiv e (SX.weightBlock w) := by
  refine Quotient.inductionOn w ?_
  intro w
  refine Quotient.inductionOn w ?_
  intro W
  change SY.operations.rawWeightBlock (rawWeightEquiv e W) =
    primitiveBlockEquiv e (SX.operations.rawWeightBlock W)
  exact rawWeightBlock_along e iotaX iotaY lifts SX.operations SY.operations
    reduction guardX guardY literalX literalY W

/-- The literal fibre equivalence is a restriction of the already checked
ordinary-weight class map, after its specified block identity is proved. -/
def weightFibreEquiv (b : LiteralPrimitiveBlock k X) :
    {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X) // SX.weightBlock w = b} ≃
    {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := Y) //
      SY.weightBlock w = primitiveBlockEquiv e b} :=
  (weightClassEquiv e).subtypeEquiv (by
    intro w
    rw [weightBlock_map e iotaX iotaY lifts SX SY literalX literalY reduction guardX guardY]
    exact (primitiveBlockEquiv (k := k) e).injective.eq_iff.symm)

@[simp] theorem weightFibreEquiv_val (b : LiteralPrimitiveBlock k X)
    (w : {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X) //
      SX.weightBlock w = b}) :
    (weightFibreEquiv e iotaX iotaY lifts SX SY literalX literalY reduction guardX guardY b w).val =
      weightClassEquiv e w.val := rfl

include lifts literalX literalY reduction guardX guardY in
theorem weightBlock_principal_iff
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X)) :
    IsPrincipal (SY.weightBlock (weightClassEquiv e w)) ↔ IsPrincipal (SX.weightBlock w) := by
  rw [weightBlock_map e iotaX iotaY lifts SX SY literalX literalY reduction guardX guardY]
  exact primitiveBlockEquiv_principal_iff e _

end WeightFibres

section Spin

open TypeBCliffordCarriers TypeBAutomorphismSource TypeBWeightStabilizerSource TypeBSpinCoverSource

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  {N : NormSource n F} {parameters : OddFieldParameters F r f}
  (S : FieldActionSource n F r f parameters N)
  [Finite (TypeBCentralKernelSpinBinding.A S)] [Finite (Spin n F N)]

local instance finiteGroupFintype (H : Type) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

variable {k0 K0 : Type} [Field k0] [Field K0] [CharP k0 2]
  [IsAlgClosed k0] [CharZero K0] [IsAlgClosed K0]

/-- Partial application to the actual Spin embedding and exactly the roots
used by the existing source construction. The remaining displayed arguments
are the two literal local block packages and their routine guarded laws. -/
def spinWeightFibreEquiv
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (rank : 3 ≤ n) (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N)) :=
  weightFibreEquiv (TypeBCentralKernelSpinBinding.spinEquiv S)
    (literalSpinRoot S centre rank omegaRoot) (embeddedSpinRoot S centre rank omegaRoot)
    (literalSpinRoot_lift S centre rank omegaRoot)

/-- The literal Omega quotient equivalence, using the same prescribed
Omega root and the exact quotient root in `SpinTransportData`. -/
def omegaWeightFibreEquiv (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N)) :=
  weightFibreEquiv (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S) omegaRoot
    (TypeBCentralKernelSourceAssembly.spinQuotientRoot S omegaRoot)
    (funext (TypeBCentralKernelSourceAssembly.spinQuotientRoot_lift S omegaRoot))

end Spin

end ModularRep.PaperProofs.TypeBCentralKernelSpinWeightFibreIdentification


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
