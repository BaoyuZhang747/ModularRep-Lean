import ModularRep.PaperProofs.TypeBRankThreeJordanActions
import ModularRep.PaperProofs.TypeBLeviRepresentativeSelection
import ModularRep.PaperProofs.TypeBRankThreeMoritaPacketInertia
import ModularRep.CyclicOuterBAW

/-!
# The original field actor covers actual packet character inertia

The finite Clifford semidirect product uses exactly the retained FieldData.
The existing semidirect automorphism homomorphism is restricted to its
characteristic Spin subgroup. Its character action is inverse pullback.

The only new source is the group-only direction of Ruhstorfer Proposition
4.9: the outer image of this normalized actor covers the stabilizer of the
same specified packet idempotent. Its normalization and algebraic/finite
interpretation remain E2/U. Arbitrary FieldData does not supply this fact.

The final deduction uses actual packet fixedness and an inner Spin
adjustment. The kernel of the constructed homomorphism is retained.
The packet parameter stays explicit. In the rank-three consumer it must
be the same JordanSource.ambientParameter of the original reduction;
the resulting ambient idempotent is definitionally the original eG.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeSameFieldAutomorphism

open ModularRep FDRepSimpleClassKZero TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBLeviRepresentativeSelection TypeBRankThreeJordanCliffordCarriers
open ModularRep.ManuscriptVerification.CyclicOuterBAW

variable {p f : ℕ} {F A E : Type}
  [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A]
  {N : NormSource 3 F} {Nbar : NormSource 3 A}
  {Frob : MulAut (SpecialClifford 3 A)}
  {Lbar : Subgroup (SpecialClifford 3 A)}
  [Finite (fixedPoints Frob.toMonoidHom)] [Group E]
  (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)
  (field : FieldData Frob Lbar E)

/-- The full finite Clifford group and the same original field actor. -/
abbrev Ambient :=
  SpecialClifford 3 F ⋊[cliffordFieldAction points field.fieldPoints] E

/-- The actual Spin inclusion, with no quotient by an action kernel. -/
def spinEmbedding : Spin 3 F N →* Ambient points field :=
  SemidirectProduct.inl.comp (SpinSubgroup 3 F N).subtype

theorem spinEmbedding_injective :
    Function.Injective (spinEmbedding points field) := by
  intro x y h
  apply Subtype.ext
  exact congrArg SemidirectProduct.left h

variable (perfect : commutator (Spin 3 F N) = ⊤)

/-- Restrict the existing semidirect conjugation map to characteristic Spin. -/
def nu : Ambient points field →* MulAut (Spin 3 F N) := by
  letI : (SpinSubgroup 3 F N).Characteristic :=
    spinSubgroup_characteristic N perfect
  exact (MulAut.characteristic (SpinSubgroup 3 F N)).comp
    (semidirectToMulAut (cliffordFieldAction points field.fieldPoints))

@[simp] theorem nu_coe (a : Ambient points field) (x : Spin 3 F N) :
    (nu points field perfect a x).val =
      a.left * cliffordFieldAction points field.fieldPoints a.right x.val *
        a.left⁻¹ := rfl

/-- Multiplication of the two actual automorphisms means composition. -/
theorem nu_eq (a : Ambient points field) :
    nu points field perfect a =
      MulAut.conjNormal (H := SpinSubgroup 3 F N) a.left *
        TypeBRankThreeJordanCliffordCarriers.spinFieldAction
          points field.fieldPoints perfect a.right := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem nu_inl (m : SpecialClifford 3 F) :
    nu points field perfect (SemidirectProduct.inl m) =
      MulAut.conjNormal (H := SpinSubgroup 3 F N) m := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change m * cliffordFieldAction points field.fieldPoints 1 x.val * m⁻¹ =
    m * x.val * m⁻¹
  rw [map_one]
  rfl

@[simp] theorem nu_inr (e : E) :
    nu points field perfect (SemidirectProduct.inr e) =
      TypeBRankThreeJordanCliffordCarriers.spinFieldAction
        points field.fieldPoints perfect e := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change 1 * cliffordFieldAction points field.fieldPoints e x.val * 1⁻¹ =
    cliffordFieldAction points field.fieldPoints e x.val
  simp only [one_mul, inv_one, mul_one]

@[simp] theorem nu_spinEmbedding (g : Spin 3 F N) :
    nu points field perfect (spinEmbedding points field g) = MulAut.conj g := by
  rw [spinEmbedding, MonoidHom.comp_apply, nu_inl]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

section OuterImage

variable {k : Type} [Field k]

/-- The needed group-only consequence of Ruhstorfer Proposition 4.9,
author text 3229--3239. It is scoped to this field actor and idempotent.
No character fixedness or inertia conclusion is a source field. -/
structure NormalizedOuterImage (eG : k[Spin 3 F N]) : Prop where
  covers : ∀ alpha : MulAut (Spin 3 F N),
    MonoidAlgebra.mapDomainRingEquiv k alpha eG = eG →
      ∃ a : Ambient points field,
        QuotientGroup.mk' (TypeBAutomorphismSource.innerAutomorphisms N)
            (nu points field perfect a) =
          QuotientGroup.mk' (TypeBAutomorphismSource.innerAutomorphisms N) alpha

/-- An inner adjustment lifts the normalized outer representative exactly.
No surjectivity on all automorphisms and no kernel triviality is used. -/
theorem exists_preimage_of_idempotent_fixed
    (eG : k[Spin 3 F N])
    (normalized : NormalizedOuterImage points field perfect eG)
    (alpha : MulAut (Spin 3 F N))
    (fixed : MonoidAlgebra.mapDomainRingEquiv k alpha eG = eG) :
    ∃ a : Ambient points field, nu points field perfect a = alpha := by
  obtain ⟨a, ha⟩ := normalized.covers alpha fixed
  have inner : alpha * (nu points field perfect a)⁻¹ ∈
      TypeBAutomorphismSource.innerAutomorphisms N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (TypeBAutomorphismSource.innerAutomorphisms N)
      (alpha * (nu points field perfect a)⁻¹) = 1
    rw [map_mul, map_inv, ha]
    exact mul_inv_cancel _
  obtain ⟨g, hg⟩ := inner
  refine ⟨spinEmbedding points field g * a, ?_⟩
  rw [map_mul, nu_spinEmbedding, hg]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end OuterImage

section Characters

variable {k K : Type} [Field k] [Field K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Finite (SpecialClifford 3 F)] [Finite (Spin 3 F N)]
  (iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))

/-- The canonical pullback of actual automorphisms along the constructed nu. -/
@[instance_reducible]
def brauerAction : MulAction (Ambient points field) (IBr iota) :=
  CyclicOuterLemma37Concrete.rightAutomorphismAction (nu points field perfect)

theorem brauerAction_apply (a : Ambient points field) (phi : IBr iota) :
    letI := brauerAction points field perfect iota
    a • phi = MulOpposite.op ((nu points field perfect a)⁻¹) • phi := by
  change IrreducibleBrauerCharacter.twist iota phi
      (nu points field perfect a⁻¹) =
    IrreducibleBrauerCharacter.twist iota phi
      ((nu points field perfect a)⁻¹)
  rw [map_inv]

/-- The pullback is the SAME Clifford/field action used by Jordan transport. -/
theorem brauerAction_factors (a : Ambient points field) (phi : IBr iota) :
    letI := brauerAction points field perfect iota
    letI := TypeBRankThreeJordanActions.cliffordBrauerAction iota
    letI := TypeBRankThreeJordanActions.spinBrauerFieldAction
      points field.fieldPoints perfect iota
    a • phi = a.left • (a.right • phi) := by
  change IrreducibleBrauerCharacter.twist iota phi
      (nu points field perfect a⁻¹) =
    IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota phi
        (TypeBRankThreeJordanCliffordCarriers.spinFieldAction
          points field.fieldPoints perfect a.right⁻¹))
      (MulAut.conjNormal (H := SpinSubgroup 3 F N) a.left⁻¹)
  rw [map_inv, IrreducibleBrauerCharacter.twist_mul, nu_eq]
  simp only [mul_inv_rev, map_inv]

section PhysicalPacket

variable {O : Type} [CommRing O] [IsDomain O] [Algebra O K]
  (parameters : OddFieldParameters F p f)
  (Msys : ModularSystem 2 K O k)
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F N) => c.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks)
  (series : TypeBRankThreeNonprincipalSeriesBinding.Sources parameters Msys iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary)
  (s : TypeBSpinBroueMichelCarriers.AdmissibleParameter
    (p := p) (ell := 2) (n := 3) (F := F))

/-- Every actual character-inertia element has an actual inertia preimage
in the same Clifford/field semidirect product. All actions are on full IBr;
no full-automorphism action on the fixed packet subtype is assumed. -/
theorem packet_inertia_preimage
    (covariance : TypeBRankThreeMoritaPacketInertia.PacketFamilyCovariance
      parameters Msys iota blocks ordinary series s)
    (normalized : NormalizedOuterImage points field perfect
      (TypeBRankThreeJordanAmbientPacket.idempotent
        parameters Msys iota blocks ordinary series s))
    (phi : TypeBRankThreeJordanPacketCarriers.Packet iota blocks
      (TypeBRankThreeJordanAmbientPacket.idempotent
        parameters Msys iota blocks ordinary series s))
    (alpha : MulAut (Spin 3 F N)) :
    letI : MulAction (MulAut (Spin 3 F N)) (IBr iota) :=
      CyclicOuterLemma37Concrete.rightAutomorphismAction
        (MonoidHom.id (MulAut (Spin 3 F N)))
    letI := brauerAction points field perfect iota
    alpha • phi.val = phi.val →
      ∃ a : Ambient points field,
        nu points field perfect a = alpha ∧ a • phi.val = phi.val := by
  letI : MulAction (MulAut (Spin 3 F N)) (IBr iota) :=
    CyclicOuterLemma37Concrete.rightAutomorphismAction
      (MonoidHom.id (MulAut (Spin 3 F N)))
  letI := brauerAction points field perfect iota
  intro fixed
  have fixed' : MulOpposite.op (alpha⁻¹) • phi.val = phi.val := fixed
  have packetFixed :=
    TypeBRankThreeMoritaPacketInertia.packet_idempotent_fixed
      parameters Msys iota blocks ordinary series s covariance phi alpha fixed'
  obtain ⟨a, ha⟩ := exists_preimage_of_idempotent_fixed points field perfect
    (TypeBRankThreeJordanAmbientPacket.idempotent
      parameters Msys iota blocks ordinary series s)
    normalized alpha packetFixed
  refine ⟨a, ha, ?_⟩
  rw [brauerAction_apply, ha]
  exact fixed'

end PhysicalPacket
end Characters

end ModularRep.PaperProofs.TypeBRankThreeSameFieldAutomorphism


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
