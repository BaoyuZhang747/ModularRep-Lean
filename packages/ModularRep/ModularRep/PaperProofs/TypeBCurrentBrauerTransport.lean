import ModularRep.PaperProofs.TypeBCliffordCarriers
import ModularRep.PaperProofs.TypeBLeviRepresentativeField
import ModularRep.PaperProofs.TypeBRankThreeJordanPacketCarriers
import ModularRep.PaperProofs.TypeBSpinConlonBlockSourceInstantiation
import ModularRep.PaperProofs.TypeBRankThreeJordanPacketTransport

/-!
# Actual field actions and semisimple-parameter promotion in type B

The output uses the literal finite Spin norm kernel, special Clifford group,
standard Frobenius action, original Brauer root, and honest representation
extension. The semisimple parameter is a rational odd-order class in the
literal dual PCSp. The source boundary is Cabanes--Enguehard, Theorem 9.12,
and the equivariance of these block parameters (Bonnafé--Dat--Rouquier,
Lemma 7.4, and Feng--Li--Zhang, Lemma 5.1). Uniqueness is stated on primitive
blocks, before any character or representative is chosen.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCurrentBrauerTransport

open ModularRep TypeBCliffordCarriers FDRepSimpleClassKZero
open TypeBLemma47LeviApplication TypeBLeviRepresentativeField
open TypeBRankThreeJordanPacketCarriers
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {n p f : ℕ} {F k K : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable {N : NormSource n F} {parameters : OddFieldParameters F p f}
variable [Finite (SpecialClifford n F)] [NeZero f]
variable (fs : FieldActionSource n F p f parameters N)
variable (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))

@[instance_reducible] def diagonalAction :
    MulAction (SpecialClifford n F) (IBr iota) :=
  ambientBrauerAction (SpinSubgroup n F N) iota

@[instance_reducible] def fieldAction : MulAction (FieldGroup f) (IBr iota) :=
  EvenFieldAssumption53Relative.rightAutomorphismAction iota (spinFieldAction n F fs)

theorem spin_stable (e : FieldGroup f) (g : SpecialClifford n F) :
    g ∈ SpinSubgroup n F N ↔ fs.action e g ∈ SpinSubgroup n F N := by
  constructor
  · exact field_preserves_spin n F fs e g
  · intro h
    have h' := field_preserves_spin n F fs e⁻¹ (fs.action e g) h
    rw [map_inv] at h'
    change (fs.action e).symm (fs.action e g) ∈ SpinSubgroup n F N at h'
    simpa only [MulEquiv.symm_apply_apply] using h'

theorem spinFieldAction_eq_restrict : spinFieldAction n F fs =
    restrictAutomorphismHom (SpinSubgroup n F N) fs.action (spin_stable fs) := by
  ext e g
  rfl

theorem compatible :
    letI := diagonalAction iota
    letI := fieldAction fs iota
    Formalisation.SemidirectActionCompatible (X := IBr iota) fs.action := by
  intro e g psi
  change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi (MulAut.conjNormal g⁻¹))
      (spinFieldAction n F fs e⁻¹) =
    IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi (spinFieldAction n F fs e⁻¹))
      (MulAut.conjNormal (fs.action e g)⁻¹)
  rw [spinFieldAction_eq_restrict fs]
  exact field_ambient_brauer_naturality (SpinSubgroup n F N) iota
    fs.action (spin_stable fs) e g psi

/-- The extension assertion with the original root and actual left inclusion. -/
def Extends (psi : IBr iota) : Prop :=
  ∃ V : FDRep k (Spin n F N),
    Representation.IsIrreducible V.ρ ∧
    psi.val = Representation.brauerCharacterOfRootEmbedding V.ρ iota ∧
    ∃ rho : Representation k (FieldSemidirect iota (spinFieldAction n F fs) psi) V,
      Representation.IsIrreducible rho ∧
      Nonempty (Representation.Equiv
        (rho.pullback (SemidirectProduct.inl : Spin n F N →*
          FieldSemidirect iota (spinFieldAction n F fs) psi)) V.ρ)

/-- The fixed mathematical conclusion for a representative in Proposition 4.13. -/
def Representative (psi : IBr iota) : Prop :=
  letI := diagonalAction iota
  letI := fieldAction fs iota
  Formalisation.SemidirectStabilizerFactors fs.action (compatible fs iota) psi ∧
    Extends fs iota psi

/-- Every original orbit has a representative with these two actual conclusions. -/
def BrauerHypothesis : Prop :=
  letI := diagonalAction iota
  ∀ psi0 : IBr iota, ∃ psi : IBr iota,
    psi ∈ MulAction.orbit (SpecialClifford n F) psi0 ∧ Representative fs iota psi

theorem representative_of_product
    (cyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (psi : IBr iota)
    (separated : letI := diagonalAction iota; letI := fieldAction fs iota;
      ProductStabilizerFactorization (D := SpecialClifford n F)
        (E := FieldGroup f) psi) : Representative fs iota psi := by
  letI := diagonalAction iota
  letI := fieldAction fs iota
  exact ⟨(semidirectStabilizerFactors_iff_productStabilizerFactorization
    fs.action (compatible fs iota) psi).mpr separated,
    honest_field_extension iota (spinFieldAction n F fs) cyclic psi⟩

theorem representative_of_field_fixed
    (cyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (psi : IBr iota)
    (fixed : ∀ e : FieldGroup f,
      IrreducibleBrauerCharacter.twist iota psi (spinFieldAction n F fs e) = psi) :
    Representative fs iota psi := by
  apply representative_of_product fs iota cyclic psi
  letI := diagonalAction iota
  letI := fieldAction fs iota
  intro g e
  have he : e • psi = psi := fixed e⁻¹
  rw [he]
  simp only [and_true]

/-- The prime-field case uses the trivial literal field group. -/
theorem prime_field
    (cyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (hf : f = 1) : BrauerHypothesis fs iota := by
  subst f
  letI := diagonalAction iota
  intro psi0
  refine ⟨psi0, MulAction.mem_orbit_self psi0, ?_⟩
  apply representative_of_field_fixed fs iota cyclic psi0
  intro e
  have he : e = 1 := Subsingleton.elim _ _
  rw [he, map_one]
  exact IrreducibleBrauerCharacter.twist_refl iota psi0

abbrev SemisimpleIndex := TypeBSpinConlonBlockSourceInstantiation.RationalIndex p 2 n F

/-- Forward transport of a literal primitive block along a group automorphism. -/
def blockForward (alpha : MulAut (Spin n F N))
    (b : LiteralPrimitiveBlock k (Spin n F N)) : LiteralPrimitiveBlock k (Spin n F N) :=
  ⟨MonoidAlgebra.mapDomainRingEquiv k alpha b.val,
    b.property.mapRingEquiv (MonoidAlgebra.mapDomainRingEquiv k alpha)⟩

variable {BG : Type} [Fintype BG] {bG : BG → k[Spin n F N]}
variable (blocks : BlockIdempotentDecomposition bG)

/-- Exact source-level block parameters and their published action laws.

U interpretation, uniformly for every rational semisimple odd-order class `s`
and every literal primitive block `b`: `action` is the permutation of
`RationalIndex p 2 n F` induced by the actual dual standard `p`-Frobenius,
with the same powers as `fs.action`; `idempotent s` is the Broué--Michel
central idempotent `e_s` in the group algebra of this exact Spin norm kernel;
and `blockParameter b` is the unique rational odd-order semisimple class
whose `e_s` contains `b`. The class carrier is the literal `PCSp F n`, the
quotient of CSp by all nonzero scalars, not PSp. The root `iota` and the
algebraically closed characteristic-two coefficient field remain those of
the consumer. Cabanes--Enguehard, *Representation Theory of Finite Reductive
Groups*, Theorem 9.12, supplies this block partition; Bonnafé--Dat--Rouquier,
Lemma 7.4, supplies invariance under the regular embedding; the rational
series equivariance is that of Feng--Li--Zhang, Lemma 5.1.

These identifications are accepted U premises of the literature-relative
certificate. Merely providing arbitrary maps satisfying the algebraic fields
does not authenticate their identification with the published maps.
There is no character selector, field-stabilizer restriction, or stabilizer equality here. -/
structure ParameterSource where
  action : FieldGroup f →* Equiv.Perm (SemisimpleIndex (n := n) (p := p) (F := F))
  blockParameter : LiteralPrimitiveBlock k (Spin n F N) →
    SemisimpleIndex (n := n) (p := p) (F := F)
  idempotent : SemisimpleIndex (n := n) (p := p) (F := F) → k[Spin n F N]
  central : ∀ s, IsMulCentral (idempotent s)
  idempotent_eq : ∀ s, IsIdempotentElem (idempotent s)
  unique : ∀ b s, b.val * idempotent s = b.val ↔ blockParameter b = s
  diagonal : ∀ g b, blockParameter
    (blockForward (MulAut.conjNormal (H := SpinSubgroup n F N) g) b) = blockParameter b
  field : ∀ e b, blockParameter (blockForward (spinFieldAction n F fs e) b) =
    action e (blockParameter b)

namespace ParameterSource

variable {fs}
variable (source : ParameterSource fs (k := k))

@[instance_reducible] def indexAction :
    MulAction (FieldGroup f) (SemisimpleIndex (n := n) (p := p) (F := F)) :=
  MulAction.compHom _ source.action

def characterParameter (psi : IBr iota) := source.blockParameter (supportingBlock iota blocks psi)

theorem in_packet_iff (s : SemisimpleIndex (n := n) (p := p) (F := F)) (psi : IBr iota) :
    InPacket iota blocks (source.idempotent s) psi ↔
      source.characterParameter iota blocks psi = s :=
  source.unique (supportingBlock iota blocks psi) s

theorem diagonal_parameter (g : SpecialClifford n F) (psi : IBr iota) :
    letI := diagonalAction iota
    source.characterParameter iota blocks (g • psi) = source.characterParameter iota blocks psi := by
  letI := diagonalAction iota
  have h : supportingBlock iota blocks (g • psi) =
      blockForward (MulAut.conjNormal (H := SpinSubgroup n F N) g)
        (supportingBlock iota blocks psi) := by
    apply Subtype.ext
    exact supportingBlock_smul_val iota blocks (MulAut.conjNormal (H := SpinSubgroup n F N)) g psi
  unfold characterParameter
  rw [h]
  exact source.diagonal g _

theorem field_parameter (e : FieldGroup f) (psi : IBr iota) :
    letI := fieldAction fs iota
    source.characterParameter iota blocks (e • psi) =
      source.action e (source.characterParameter iota blocks psi) := by
  letI := fieldAction fs iota
  have h : supportingBlock iota blocks (e • psi) =
      blockForward (spinFieldAction n F fs e) (supportingBlock iota blocks psi) := by
    apply Subtype.ext
    exact supportingBlock_smul_val iota blocks (spinFieldAction n F fs) e psi
  unfold characterParameter
  rw [h]
  exact source.field e _

def stabilizer (s : SemisimpleIndex (n := n) (p := p) (F := F)) : Subgroup (FieldGroup f) :=
  letI := source.indexAction
  MulAction.stabilizer (FieldGroup f) s

/-- Uniqueness of the block parameter forces the full field component into D. -/
theorem field_component_mem (s : SemisimpleIndex (n := n) (p := p) (F := F))
    (psi : IBr iota) (packet : InPacket iota blocks (source.idempotent s) psi)
    (g : SpecialClifford n F) (e : FieldGroup f)
    (fixed : letI := diagonalAction iota; letI := fieldAction fs iota;
      g • (e • psi) = psi) : e ∈ source.stabilizer s := by
  letI := diagonalAction iota
  letI := fieldAction fs iota
  have hs := (source.in_packet_iff iota blocks s psi).mp packet
  have h := congrArg (source.characterParameter iota blocks) fixed
  rw [source.diagonal_parameter, source.field_parameter, hs] at h
  exact h

/-- A factorization over the parameter fixer promotes to the full field group. -/
theorem full_field_factorization
    (s : SemisimpleIndex (n := n) (p := p) (F := F))
    (psi : IBr iota) (packet : InPacket iota blocks (source.idempotent s) psi)
    (localFactorization : letI := diagonalAction iota; letI := fieldAction fs iota;
      ∀ g : SpecialClifford n F, ∀ e : source.stabilizer s,
        g • ((e : FieldGroup f) • psi) = psi ↔
          g • psi = psi ∧ (e : FieldGroup f) • psi = psi) :
    letI := diagonalAction iota
    letI := fieldAction fs iota
    ProductStabilizerFactorization (D := SpecialClifford n F) (E := FieldGroup f) psi := by
  letI := diagonalAction iota
  letI := fieldAction fs iota
  intro g e
  constructor
  · intro h
    exact (localFactorization g ⟨e, source.field_component_mem iota blocks s psi packet g e h⟩).mp h
  · rintro ⟨hg, he⟩
    rw [he, hg]

/-- The restricted fixer maps onto the whole actual field fixer, for the
same packet character. Thus the field subgroup used in the extension
is also exactly the image of its fixer inside the semisimple-parameter group. -/
theorem field_stabilizer_image
    (s : SemisimpleIndex (n := n) (p := p) (F := F))
    (psi : IBr iota) (packet : InPacket iota blocks (source.idempotent s) psi) :
    (fieldStabilizer iota ((spinFieldAction n F fs).comp (source.stabilizer s).subtype) psi).map
        (source.stabilizer s).subtype =
      fieldStabilizer iota (spinFieldAction n F fs) psi := by
  letI := diagonalAction iota
  letI := fieldAction fs iota
  ext e
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact hd
  · intro he
    have fixed : e • psi = psi := he
    have hd := source.field_component_mem iota blocks s psi packet 1 e
      (by simpa only [one_smul] using fixed)
    exact ⟨⟨e, hd⟩, he, rfl⟩

end ParameterSource
end ModularRep.PaperProofs.TypeBCurrentBrauerTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
