import ModularRep.PaperProofs.TypeBRankThreeJordanMap
import ModularRep.PaperProofs.TypeBRankThreeJordanFiniteProduct
import ModularRep.PaperProofs.TypeBRankThreeJordanOvergroup
import ModularRep.PaperProofs.TypeBRankThreeJordanPacketTransport

/-!
# The actual diagonal enlargement of a modular Jordan correspondent

The source character is in the complete literal original-Levi packet.
The preceding Levi factorization is transported through the one-way
published packet injection. The derived rational Spin-times-Levi product
then gives the ambient Clifford factorization. The equality of the
original field stabilizers follows from the same injection.

The final source-instantiated consumer must construct the Levi
representative by the checked preceding window and bind both packet
idempotents at its retained dual label. A factorization used here is
that preceding K deduction, never an external Jordan/ambient conclusion.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeJordanTransfer

open ModularRep TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBLeviRepresentativeCarriers TypeBLeviRepresentativeSelection
open TypeBRankThreeJordanPacketCarriers TypeBRankThreeJordanOriginalTransport
open TypeBRankThreeJordanCliffordCarriers TypeBRankThreeJordanActions
open TypeBRankThreeJordanMap
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {p f : ℕ} {F A E k K : Type}
variable [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A]
variable {N : NormSource 3 F} {Nbar : NormSource 3 A}
variable {Frob : MulAut (SpecialClifford 3 A)}
variable [Finite (SpecialClifford 3 F)] [Finite (Spin 3 F N)]
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable [Group E] [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)
variable (Lbar : Subgroup (SpecialClifford 3 A))
variable (field : FieldData Frob Lbar E)
variable (perfect : commutator (Spin 3 F N) = ⊤)
variable (iotaL : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
variable (iotaG : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))
variable {IL IG : Type} [Fintype IL] [Fintype IG]
variable {bL : IL → k[L Frob.toMonoidHom Lbar]}
variable {bG : IG → k[Spin 3 F N]}
variable (blocksL : BlockIdempotentDecomposition bL)
variable (blocksG : BlockIdempotentDecomposition bG)
variable (eL : k[L Frob.toMonoidHom Lbar]) (eG : k[Spin 3 F N])
variable (gammaInvariant : ∀ m : Gamma Frob Lbar,
  MonoidAlgebra.mapDomainRingEquiv k (originalConjugation Frob Lbar m) eL = eL)
variable (fieldInvariant : ∀ a : E,
  MonoidAlgebra.mapDomainRingEquiv k (originalField Frob Lbar field a) eL = eL)
variable (J : ModularJordanMap points Lbar field perfect iotaL iotaG
  blocksL blocksG eL eG gammaInvariant fieldInvariant)

@[instance_reducible]
def leviGamma : MulAction (Gamma Frob Lbar) (IBr iotaL) :=
  originalAmbientAction Frob Lbar iotaL
@[instance_reducible]
def leviField : MulAction E (IBr iotaL) :=
  originalFieldAction Frob Lbar iotaL field
@[instance_reducible]
def packetGamma : MulAction (Gamma Frob Lbar) (Packet iotaL blocksL eL) :=
  packetMulAction iotaL blocksL eL (originalConjugation Frob Lbar) gammaInvariant
@[instance_reducible]
def packetField : MulAction E (Packet iotaL blocksL eL) :=
  packetMulAction iotaL blocksL eL (originalField Frob Lbar field) fieldInvariant
@[instance_reducible]
def ambientClifford : MulAction (SpecialClifford 3 F) (IBr iotaG) :=
  cliffordBrauerAction iotaG
@[instance_reducible]
def ambientGamma : MulAction (Gamma Frob Lbar) (IBr iotaG) :=
  gammaBrauerAction points iotaG Lbar
@[instance_reducible]
def ambientField : MulAction E (IBr iotaG) :=
  spinBrauerFieldAction points field.fieldPoints perfect iotaG

/-- A preceding factorization restricts to the literal invariant packet
without any new stabilizer premise. -/
theorem packet_factorization (psi : Packet iotaL blocksL eL)
    (levi :
      letI := leviGamma Lbar iotaL
      letI := leviField Lbar field iotaL
      ProductStabilizerFactorization (D := Gamma Frob Lbar) (E := E) psi.val) :
    letI := packetGamma Lbar iotaL blocksL eL gammaInvariant
    letI := packetField Lbar field iotaL blocksL eL fieldInvariant
    ProductStabilizerFactorization (D := Gamma Frob Lbar) (E := E) psi := by
  letI := leviGamma Lbar iotaL
  letI := leviField Lbar field iotaL
  letI := packetGamma Lbar iotaL blocksL eL gammaInvariant
  letI := packetField Lbar field iotaL blocksL eL fieldInvariant
  intro m a
  constructor
  · intro fixed
    have value : m • (a • psi.val) = psi.val := congrArg Subtype.val fixed
    obtain ⟨hm, ha⟩ := (levi m a).mp value
    exact ⟨Subtype.ext hm, Subtype.ext ha⟩
  · rintro ⟨hm, ha⟩
    rw [ha, hm]

/-- The Jordan image has the claimed Clifford-by-field factorization and
the same stabilizer in the original field actor E. -/
theorem stabilizer_transfer
    (levi_le_spin : Lbar ≤ SpinSubgroup 3 A Nbar)
    (decomposition : ∀ x : SpecialClifford 3 A,
      ∃ g ∈ SpinSubgroup 3 A Nbar, ∃ z ∈ Subgroup.center (SpecialClifford 3 A),
        x = g * z)
    (intersection : pairedLevi Lbar ⊓ SpinSubgroup 3 A Nbar ≤ Lbar)
    (lang : TypeBRankThreeJordanDiagonalProduct.LeviLangSource Frob Lbar)
    (psi : Packet iotaL blocksL eL)
    (levi :
      letI := leviGamma Lbar iotaL
      letI := leviField Lbar field iotaL
      ProductStabilizerFactorization (D := Gamma Frob Lbar) (E := E) psi.val) :
    letI := leviField Lbar field iotaL
    letI := ambientClifford iotaG
    letI := ambientField points Lbar field perfect iotaG
    Formalisation.SemidirectStabilizerFactors
        (cliffordFieldAction points field.fieldPoints)
        (clifford_semidirect_compatible points field.fieldPoints perfect iotaG)
        (J.character psi) ∧
      MulAction.stabilizer E (J.character psi) = MulAction.stabilizer E psi.val ∧
      InPacket iotaG blocksG eG (J.character psi) := by
  letI := leviGamma Lbar iotaL
  letI := leviField Lbar field iotaL
  letI := packetGamma Lbar iotaL blocksL eL gammaInvariant
  letI := packetField Lbar field iotaL blocksL eL fieldInvariant
  letI := ambientClifford iotaG
  letI := ambientGamma points Lbar iotaG
  letI := ambientField points Lbar field perfect iotaG
  have packetLevi : ProductStabilizerFactorization
      (D := Gamma Frob Lbar) (E := E) psi :=
    packet_factorization Lbar field iotaL blocksL eL gammaInvariant fieldInvariant psi levi
  have imageLevi : ProductStabilizerFactorization
      (D := Gamma Frob Lbar) (E := E) (J.character psi) :=
    TypeBRankThreeJordanPacketTransport.product_factorization_of_injective_equivariant
      J.character J.injective J.gamma_equivariant J.field_equivariant psi packetLevi
  have ambient : ProductStabilizerFactorization
      (D := SpecialClifford 3 F) (E := E) (J.character psi) :=
    TypeBRankThreeJordanOvergroup.product_factorization_of_levi
      (gammaEmbedding points Lbar) (SpinSubgroup 3 F N)
      (TypeBRankThreeJordanFiniteProduct.finite_product points Lbar
        levi_le_spin decomposition intersection lang)
      (inner_spin_fixes iotaG)
      (fun m phi => (gamma_action_eq points iotaG Lbar m phi).symm)
      (J.character psi) imageLevi
  have samePacket : MulAction.stabilizer E (J.character psi) = MulAction.stabilizer E psi :=
    TypeBRankThreeJordanPacketTransport.field_stabilizer_eq
      J.character J.injective J.field_equivariant psi
  have sameValue : MulAction.stabilizer E psi = MulAction.stabilizer E psi.val :=
    Formalisation.stabilizer_eq_of_injective_equivariant
      (f := fun x : Packet iotaL blocksL eL => x.val) Subtype.val_injective
      (fun (_ : E) (_ : Packet iotaL blocksL eL) => rfl) psi
  refine ⟨?_, samePacket.trans sameValue, ?_⟩
  · exact (semidirectStabilizerFactors_iff_productStabilizerFactorization
      (cliffordFieldAction points field.fieldPoints)
      (clifford_semidirect_compatible points field.fieldPoints perfect iotaG)
      (J.character psi)).mpr ambient
  · exact character_in_packet points Lbar field perfect iotaL iotaG
      blocksL blocksG eL eG gammaInvariant fieldInvariant J psi

end ModularRep.PaperProofs.TypeBRankThreeJordanTransfer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
