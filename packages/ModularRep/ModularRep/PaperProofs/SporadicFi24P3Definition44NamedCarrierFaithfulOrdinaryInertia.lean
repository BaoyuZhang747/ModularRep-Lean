import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryTransport

/-! Intrinsic ordinary inertia of the same faithful pair. No reduction
or local block compatibility is needed for these deductions. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia

open ModularRep ModularRep.CharacterWeight
open TypeBCentralKernelNormalizerInertia
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "A" => (MulAut G)ᵐᵒᵖ
local notation "S" => FaithfulSector (k := k) (X := G)
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1
local notation "pX" => faithfulBrauerSector iota hinj blocks R E1
local notation "pY" => faithfulWeightSector iota hinj blocks R E1

open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryTransport

theorem faithful_fixed_fixes_center (phi : FB) (alpha : MulAut G)
    (hfixed : MulOpposite.op alpha • phi.val = phi.val) :
    ∀ z : Subgroup.center G, alpha z.val = z.val := by
  have hnu :=
    (brauerSector_equivariant iota hinj blocks E1 (MulOpposite.op alpha) phi.val).symm.trans
      (congrArg (brauerSector iota hinj blocks) hfixed)
  intro z
  exact congrArg Subtype.val (phi.faithful (DFunLike.congr_fun hnu z))

theorem rawIsoClass_fixed_iff (V : CharacterWeight p K G) (a : A) :
    a • (Quotient.mk'' V : CharacterWeight.IsoClass) = Quotient.mk'' V ↔
      V.rightTwist a.unop = V := by
  constructor
  · intro h
    exact CharacterWeight.eq_of_isomorphic (Quotient.exact h)
  · intro h
    change (Quotient.mk'' (V.rightTwist a.unop) : CharacterWeight.IsoClass) = Quotient.mk'' V
    rw [h]

omit [Fintype G] in
theorem radical_fixed_iff (Q : RadicalSubgroup (p := p) (G := G)) (a : A) :
    a • Q = Q ↔ Q.1.comap a.unop.toMonoidHom = Q.1 := by
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

theorem rawIsoClass_stabilizer_eq (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val) :
    MulAction.stabilizer A (Quotient.mk'' V : CharacterWeight.IsoClass) =
      MulAction.stabilizer A phi.val ⊓
        MulAction.stabilizer A (⟨V.subgroup, V.radical⟩ : RadicalSubgroup (p := p) (G := G)) := by
  apply Subgroup.ext
  intro a
  change (a • (Quotient.mk'' V : CharacterWeight.IsoClass) = Quotient.mk'' V) ↔
    (a • phi.val = phi.val ∧ a • (⟨V.subgroup, V.radical⟩ : RadicalSubgroup (p := p) (G := G)) = _)
  rw [rawIsoClass_fixed_iff, radical_fixed_iff]
  constructor
  · intro h
    have stable : V.subgroup.comap a.unop.toMonoidHom = V.subgroup :=
      congrArg CharacterWeight.subgroup h
    refine ⟨?_, stable⟩
    have hf := (original_local_fixed_iff iota hinj blocks R E1 e hFamily phi V hmatch
      a.unop stable).mpr ((rightTwist_eq_iff_local_fixed V a.unop stable).mp h)
    simpa only [MulOpposite.op_unop] using hf
  · rintro ⟨hf, stable⟩
    apply (rightTwist_eq_iff_local_fixed V a.unop stable).mpr
    apply (original_local_fixed_iff iota hinj blocks R E1 e hFamily phi V hmatch
      a.unop stable).mp
    simpa only [MulOpposite.op_unop] using hf

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
