import ModularRep.PaperProofs.TypeBRankThreeJordanAmbientPacket

/-!
# Actual character inertia fixes the computed ambient packet

The source supplies only covariance of the actual finite block-sum family
under actual Spin automorphisms. Its rational series, coefficient and
algebraic-to-finite automorphism interpretation remains E2/U source data.
It supplies no character fixedness or inertia conclusion.

An automorphism fixing a packet character fixes its specified supporting
primitive block. Covariance makes that block support both the original
and transported packet. The existing support theorem identifies their
rational parameter indices, hence their literal finite block sums agree.
The character convention is inverse pullback throughout.

This file stops at packet fixedness. It does not replace the chosen field
actor by a different full automorphism source, or assert the normalized
Ruhstorfer Proposition 4.9 outer-image realization.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaPacketInertia

open ModularRep OrdinaryIrreducibleCharacter FDRepSimpleClassKZero
open TypeBCliffordCarriers TypeBOrdinaryBlockSplitting
open TypeBRankThreeNonprincipalSeriesBinding TypeBSpinBroueMichelCarriers
open TypeBRankThreeJordanPacketCarriers

section SupportingBlock

variable {k K G I : Type}
  [Field k] [Field K] [Group G] [Finite G] [Fintype I]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  {b : I → k[G]}

/-- Fixedness under inverse pullback fixes the actual supporting block
under the forward group algebra automorphism. -/
theorem supportingBlock_fixed_of_character_fixed
    (iota : PrimeRegularRootEmbedding 2 k K G)
    (blocks : BlockIdempotentDecomposition b)
    (alpha : MulAut G) (phi : IBr iota)
    (fixed : MulOpposite.op (alpha⁻¹) • phi = phi) :
    MonoidAlgebra.mapDomainRingEquiv k alpha
      (supportingBlock iota blocks phi).val =
        (supportingBlock iota blocks phi).val := by
  letI : MulAction (MulAut G) (IBr iota) :=
    CyclicOuterLemma37Concrete.rightAutomorphismAction (MonoidHom.id (MulAut G))
  have fixed' : alpha • phi = phi := fixed
  have transported : (supportingBlock iota blocks (alpha • phi)).val =
      MonoidAlgebra.mapDomainRingEquiv k alpha
        (supportingBlock iota blocks phi).val :=
    supportingBlock_smul_val iota blocks (MonoidHom.id (MulAut G)) alpha phi
  rw [fixed'] at transported
  exact transported.symm

end SupportingBlock

section ActualPacket

variable {p f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]
  {N : NormSource 3 F} [Finite (Spin 3 F N)]
  (parameters : OddFieldParameters F p f)
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F N) => c.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (ordinary : OrdinaryBlockSource Msys iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks)
  (series : Sources parameters Msys iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary)

/-- Covariance of the same computed packet at the retained admissible
parameter. The witness is another actual rational parameter, with no
character or stabilizer assertion. Its specified realization remains U. -/
structure PacketFamilyCovariance
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F)) : Prop where
  image : ∀ alpha : MulAut (Spin 3 F N),
    ∃ t : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F),
      MonoidAlgebra.mapDomainRingEquiv k alpha
          (TypeBRankThreeJordanAmbientPacket.idempotent
            parameters Msys iota blocks ordinary series s) =
        TypeBRankThreeJordanAmbientPacket.idempotent
          parameters Msys iota blocks ordinary series t

/-- The block sum depends on the rational class index, not the choice
of its admissible representative. -/
theorem idempotent_eq_of_parameterIndex_eq
    (s t : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F))
    (sameIndex : parameterIndex s = parameterIndex t) :
    TypeBRankThreeJordanAmbientPacket.idempotent
        parameters Msys iota blocks ordinary series s =
      TypeBRankThreeJordanAmbientPacket.idempotent
        parameters Msys iota blocks ordinary series t := by
  classical
  simp only [TypeBRankThreeJordanAmbientPacket.idempotent,
    TypeBRankThreeJordanAmbientPacket.blocksAt, sameIndex]

/-- Actual character fixedness forces fixedness of its computed packet
idempotent by the specified supporting-block and rational-index laws. -/
theorem packet_idempotent_fixed
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F))
    (covariance : PacketFamilyCovariance parameters Msys iota blocks ordinary series s)
    (phi : Packet iota blocks
      (TypeBRankThreeJordanAmbientPacket.idempotent
        parameters Msys iota blocks ordinary series s))
    (alpha : MulAut (Spin 3 F N))
    (fixed : MulOpposite.op (alpha⁻¹) • phi.val = phi.val) :
    MonoidAlgebra.mapDomainRingEquiv k alpha
        (TypeBRankThreeJordanAmbientPacket.idempotent
          parameters Msys iota blocks ordinary series s) =
      TypeBRankThreeJordanAmbientPacket.idempotent
        parameters Msys iota blocks ordinary series s := by
  let c := supportingBlock iota blocks phi.val
  have blockFixed : MonoidAlgebra.mapDomainRingEquiv k alpha c.val = c.val :=
    supportingBlock_fixed_of_character_fixed iota blocks alpha phi.val fixed
  have originalSupport : c.val *
      TypeBRankThreeJordanAmbientPacket.idempotent
        parameters Msys iota blocks ordinary series s = c.val := phi.property
  have transportedSupport : c.val *
      MonoidAlgebra.mapDomainRingEquiv k alpha
        (TypeBRankThreeJordanAmbientPacket.idempotent
          parameters Msys iota blocks ordinary series s) = c.val := by
    simpa only [map_mul, blockFixed] using
      congrArg (MonoidAlgebra.mapDomainRingEquiv k alpha) originalSupport
  obtain ⟨t, ht⟩ := covariance.image alpha
  rw [ht] at transportedSupport
  have originalIndex :=
    (TypeBRankThreeJordanAmbientPacket.support_iff
      parameters Msys iota blocks ordinary series s c).mp originalSupport
  have transportedIndex :=
    (TypeBRankThreeJordanAmbientPacket.support_iff
      parameters Msys iota blocks ordinary series t c).mp transportedSupport
  have sameIndex : parameterIndex t = parameterIndex s :=
    transportedIndex.symm.trans originalIndex
  exact ht.trans (idempotent_eq_of_parameterIndex_eq
    parameters Msys iota blocks ordinary series t s sameIndex)

/-- The same deduction in the canonical actual-automorphism action;
the action is installed here and is not a source parameter. -/
theorem character_inertia_fixes_packet
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F))
    (covariance : PacketFamilyCovariance parameters Msys iota blocks ordinary series s)
    (phi : Packet iota blocks
      (TypeBRankThreeJordanAmbientPacket.idempotent
        parameters Msys iota blocks ordinary series s))
    (alpha : MulAut (Spin 3 F N)) :
    letI : MulAction (MulAut (Spin 3 F N)) (IBr iota) :=
      CyclicOuterLemma37Concrete.rightAutomorphismAction
        (MonoidHom.id (MulAut (Spin 3 F N)))
    alpha • phi.val = phi.val →
      MonoidAlgebra.mapDomainRingEquiv k alpha
          (TypeBRankThreeJordanAmbientPacket.idempotent
            parameters Msys iota blocks ordinary series s) =
        TypeBRankThreeJordanAmbientPacket.idempotent
          parameters Msys iota blocks ordinary series s := by
  letI : MulAction (MulAut (Spin 3 F N)) (IBr iota) :=
    CyclicOuterLemma37Concrete.rightAutomorphismAction
      (MonoidHom.id (MulAut (Spin 3 F N)))
  intro fixed
  exact packet_idempotent_fixed
    parameters Msys iota blocks ordinary series s covariance phi alpha fixed

end ActualPacket

end ModularRep.PaperProofs.TypeBRankThreeMoritaPacketInertia


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
