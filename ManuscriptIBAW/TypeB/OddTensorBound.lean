import ManuscriptIBAW.Library.TensorStabilizer
import ManuscriptIBAW.Library.MultiplierQuotient
import ModularRep.PaperProofs.TypeBPhysicalBlockAction
import ModularRep.PaperProofs.TypeBConlonJordanSourceInstantiation
import ModularRep.PaperProofs.TypeBSpinDiagonalNormSource

/-!
# The tensor stabiliser bound for the special Clifford group

The specified group algebra action determines how the action on blocks
corresponds to tensoring simple modules. The norm and the scalar centre
theorem give index two. The general central character lemma then bounds the
kernel of the projection from each primitive block stabiliser to the field
group. It uses no comparison of Jordan block labels or their scalar
translates.
-/

noncomputable section
open scoped MonoidAlgebra
namespace ManuscriptIBAW.TypeB.OddTensorBound
open ModularRep ModularRep.PaperProofs
open FDRepSimpleClassKZero LinearBlockStabilizer
open TypeCConformalActionAdapter TypeBPhysicalBlockAction
open TypeBCliffordCarriers TypeBCliffordCentreSource

section PhysicalTensor
variable {G E k : Type} [Group G] [Finite G] [Group E] [Field k]
variable (N : Subgroup G) [N.Normal] (field : E →* MulAut G)
  (invariant : FieldInvariantSubgroup.IsInvariant N field)

/-- The inverse character dictated by the actual left block action. -/
def reciprocal : TensorCharacters (k := k) N →* (G →* kˣ) where
  toFun c := c.val⁻¹
  map_one' := by ext g; simp
  map_mul' := by intro c d; ext g; simp [mul_comm]

omit [Finite G] [N.Normal] in
theorem reciprocal_injective : Function.Injective (reciprocal (k := k) N) := by
  intro c d h
  exact Subtype.ext (inv_injective h)

omit [Finite G] [N.Normal] in
theorem reciprocal_trivial (c : TensorCharacters (k := k) N) :
    N ≤ (reciprocal (k := k) N c).ker := by
  intro g hg
  change (c.val g)⁻¹ = 1
  rw [c.property hg, inv_one]

omit [Finite G] in
private theorem support_asModule {V : Type} [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (b : k[G]) (h : rho.asAlgebraHom b = 1) :
    ∀ v : rho.asModule, b • v = v := by
  intro v
  apply rho.asModuleEquiv.injective
  rw [Representation.asModuleEquiv_map_smul, h]
  rfl

omit [Finite G] in
private theorem support_asAlgebraHom {V : Type} [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (b : k[G])
    (h : ∀ v : rho.asModule, b • v = v) : rho.asAlgebraHom b = 1 := by
  ext w
  obtain ⟨v, rfl⟩ := rho.asModuleEquiv.surjective w
  change rho.asAlgebraHom b (rho.asModuleEquiv v) = rho.asModuleEquiv v
  simpa only [Representation.asModuleEquiv_map_smul] using congrArg rho.asModuleEquiv (h v)

/-- The correspondence with tensoring modules follows from cancellation in the
specified algebra action. It requires existence of a supporting simple
module. The application obtains one from its ordinary primitive block
source. -/
def physicalTensorSource
    (existsSimple : ∀ b : LiteralPrimitiveBlock k G, ∃ V : FDRep k G,
      Representation.IsIrreducible V.ρ ∧ Representation.asAlgebraHom V.ρ b.val = 1) :
    letI := blockAction (k := k) N field invariant
    letI := tensorBlockAction (B := LiteralPrimitiveBlock k G)
      (LinearCharactersTrivialOn.fieldAction (k := k) field
        (FieldInvariantSubgroup.isFieldStable N field invariant))
    SimpleBlockTensorSource (reciprocal (k := k) N) := by
  classical
  letI := blockAction (k := k) N field invariant
  letI := tensorBlockAction (B := LiteralPrimitiveBlock k G)
    (LinearCharactersTrivialOn.fieldAction (k := k) field
      (FieldInvariantSubgroup.isFieldStable N field invariant))
  refine {
    representative := fun b => Classical.choose (existsSimple b)
    irreducible := fun b => (Classical.choose_spec (existsSimple b)).1
    supports := fun b => support_asModule _ _ (Classical.choose_spec (existsSimple b)).2
    tensor_supports := ?_ }
  intro c b V _ supports
  apply support_asModule
  have hb : (c • b).val = tensorRingEquiv c.val b.val := by
    change tensorRingEquiv c.val
      (MonoidAlgebra.mapDomainRingEquiv k (field 1) b.val) = _
    apply congrArg (tensorRingEquiv c.val)
    ext g
    simp only [MonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply, map_one]
    rfl
  change Representation.asAlgebraHom (Representation.linearCharacterTwist V.ρ c.val⁻¹)
    (c • b).val = 1
  rw [hb, tensor_cancel]
  exact support_asAlgebraHom _ _ supports

end PhysicalTensor

section Clifford
variable {n p f ell : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F p] [Finite (Clifford n F)]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  (parameters : OddFieldParameters F p f) (rank : 1 ≤ n) (N : NormSource n F)
  (centre : CentreSource n F parameters rank)

include centre in
omit [Finite (Clifford n F)] in
/-- The centre image under the actual Clifford norm is the square subgroup. -/
theorem norm_center_image :
    (Subgroup.center (SpecialClifford n F)).map N.norm = (powMonoidHom 2).range := by
  rw [centre.center_eq_scalarRange, MonoidHom.map_range,
    TypeBCliffordNormSquareQuotient.norm_comp_scalar]

include centre in
omit [Finite (Clifford n F)] in
/-- The index of Spin times the centre in the special Clifford group, as used in
Lemma 4.2. -/
theorem index_eq_two :
    Nat.card (SpecialClifford n F ⧸
      (SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F))) = 2 := by
  apply multiplier_index_eq_two p
    (show p ≠ 2 from by
      intro h
      have odd := parameters.odd
      rw [h] at odd
      exact (by decide : ¬ Odd 2) odd)
    N.norm (TypeBCliffordNormSurjectivity.norm_surjective n F rank N)
    (norm_center_image parameters rank N centre)

variable [NeZero f] (fs : FieldActionSource n F p f parameters N)
  (Msys : ModularSystem ell K O k)
  (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.val))
  (ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)))
  (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
    Msys iota hinj blocks (ordinaryRoots := ordinaryRoots))

include ordinary in
/-- Supporting simple modules are obtained from the same interpretation of
primitive blocks. -/
theorem exists_supporting_simple (b : LiteralPrimitiveBlock k (SpecialClifford n F)) :
    ∃ V : FDRep k (SpecialClifford n F),
      Representation.IsIrreducible V.ρ ∧ Representation.asAlgebraHom V.ρ b.val = 1 := by
  obtain ⟨phi⟩ := TypeBConlonJordanSourceInstantiation.brauerFibre_nonempty
    Msys iota hinj blocks ordinaryRoots ordinary b
  obtain ⟨V, irreducible, _, supported⟩ :=
    (TypeBCentralKernelBrauerBlocks.supported_iff_block iota blocks b phi.val).mpr phi.property
  exact ⟨V, irreducible, supported⟩

variable [Finite (TensorCharacters (k := k) (SpinSubgroup n F N))]

include centre ordinary in
/-- The central character argument for the specified stabiliser under tensoring
and field automorphisms. -/
theorem stabilizer_structure (b : LiteralPrimitiveBlock k (SpecialClifford n F)) :
    letI := blockAction (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)
    let actor := LinearCharactersTrivialOn.fieldAction (k := k) fs.action
      (FieldInvariantSubgroup.isFieldStable (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs))
    let J := MulAction.stabilizer
      (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs)) b
    let D := (TypeCExactStabilizerLemma310Relative.fieldProjection actor J).ker
    Nat.card D ≤ 2 ∧ D.Normal ∧ IsCyclic (J ⧸ D) ∧
      ∀ U : Subgroup J, IntegralBasicSetBridge.IsPHypoelementary 2 U := by
  let := blockAction (k := k) (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs)
  exact tensor_field_stabilizer_structure _ Msys.prime (SpinSubgroup n F N)
    (reciprocal (k := k) (SpinSubgroup n F N)) (reciprocal_injective _)
    (reciprocal_trivial _)
    (physicalTensorSource (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
      (exists_supporting_simple Msys iota hinj blocks ordinaryRoots ordinary))
    (le_of_eq (index_eq_two parameters rank N centre)) b

end Clifford
end ManuscriptIBAW.TypeB.OddTensorBound

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
