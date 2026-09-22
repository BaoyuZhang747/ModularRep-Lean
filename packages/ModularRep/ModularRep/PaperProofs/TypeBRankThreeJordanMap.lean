import ModularRep.PaperProofs.TypeBRankThreeJordanActions
import ModularRep.PaperProofs.TypeBRankThreeJordanOriginalTransport
import ModularRep.PaperProofs.TypeBRankThreeJordanPacketCarriers

/-!
# The one-way modular Jordan map on the original sets of characters

This is the exact map-level consequence used from FLZ Jordan 2022,
Section 4.3/Theorem 4.2 and the proof of Proposition 5.2. A single map on
the complete eL packet and a single primitive-block map come from the same
reduced top-cohomology assignment. Whole-packet equivariance, rather than
independently chosen maps on stabilized blocks, is retained.

The specified consumer must bind eL and eG to the full ordinary unions at
the same retained dual label, use the paired original Levi and the same
modular system, roots, Clifford points and chosen field actor. This file
does not supply that source authentication. The published applicability
and cohomological identification remain the explicit E2/U boundary.
Neither a stabilizer conclusion nor surjectivity is an input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeJordanMap

open ModularRep TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBLeviRepresentativeCarriers TypeBLeviRepresentativeSelection
open TypeBRankThreeJordanPacketCarriers TypeBRankThreeJordanOriginalTransport
open TypeBRankThreeJordanActions

/-- The six one-way map inputs, with constructor checking on plain carriers. -/
structure PacketMapCore (X Y SL SG BG : Type)
    (src : X → SL) (dst : Y → BG) (forget : SG → BG)
    (gammaCondition fieldCondition : (X → Y) → Prop) where
  character : X → Y
  injective : Function.Injective character
  block : SL → SG
  supporting_block : ∀ x : X, dst (character x) = forget (block (src x))
  gamma_equivariant : gammaCondition character
  field_equivariant : fieldCondition character

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

@[instance_reducible]
def packetGamma : MulAction (Gamma Frob Lbar) (Packet iotaL blocksL eL) :=
  packetMulAction iotaL blocksL eL (originalConjugation Frob Lbar) gammaInvariant
@[instance_reducible]
def packetField : MulAction E (Packet iotaL blocksL eL) :=
  packetMulAction iotaL blocksL eL (originalField Frob Lbar field) fieldInvariant
@[instance_reducible]
def ambientGamma : MulAction (Gamma Frob Lbar) (IBr iotaG) :=
  gammaBrauerAction points iotaG Lbar
@[instance_reducible]
def ambientField : MulAction E (IBr iotaG) :=
  spinBrauerFieldAction points field.fieldPoints perfect iotaG

/-- Equivariance for the fixed canonical Levi and ambient gamma actions. -/
def GammaEquivariant (character : Packet iotaL blocksL eL → IBr iotaG) : Prop :=
  letI := packetGamma (Lbar := Lbar) (iotaL := iotaL) (blocksL := blocksL)
    (eL := eL) (gammaInvariant := gammaInvariant)
  letI := ambientGamma (points := points) (Lbar := Lbar) (iotaG := iotaG)
  ∀ (m : Gamma Frob Lbar) (psi : Packet iotaL blocksL eL),
    character (m • psi) = m • character psi

/-- Equivariance for the fixed canonical original field actions. -/
def FieldEquivariant (character : Packet iotaL blocksL eL → IBr iotaG) : Prop :=
  letI := packetField (Lbar := Lbar) (field := field) (iotaL := iotaL)
    (blocksL := blocksL) (eL := eL) (fieldInvariant := fieldInvariant)
  letI := ambientField (points := points) (Lbar := Lbar) (field := field)
    (perfect := perfect) (iotaG := iotaG)
  ∀ (a : E) (psi : Packet iotaL blocksL eL),
    character (a • psi) = a • character psi

/-- One uniform simple-character map and the primitive-block map from the
same published cohomology construction, on the original literal packets. -/
abbrev ModularJordanMap :=
  PacketMapCore (Packet iotaL blocksL eL) (IBr iotaG)
    (LiteralSupport eL) (LiteralSupport eG)
    (LiteralPrimitiveBlock k (Spin 3 F N))
    (fun psi : Packet iotaL blocksL eL =>
      (⟨supportingBlock iotaL blocksL psi.val, psi.property⟩ : LiteralSupport eL))
    (supportingBlock iotaG blocksG)
    (fun c : LiteralSupport eG => c.val)
    (GammaEquivariant points Lbar iotaL iotaG blocksL eL gammaInvariant)
    (FieldEquivariant points Lbar field perfect iotaL iotaG blocksL eL fieldInvariant)

variable (J : ModularJordanMap points Lbar field perfect iotaL iotaG
  blocksL blocksG eL eG gammaInvariant fieldInvariant)

/-- Membership in the ambient packet follows from the same-block equation;
it is not a separately chosen target packet assertion. -/
theorem character_in_packet (psi : Packet iotaL blocksL eL) :
    InPacket iotaG blocksG eG (J.character psi) := by
  change (supportingBlock iotaG blocksG (J.character psi)).val * eG =
    (supportingBlock iotaG blocksG (J.character psi)).val
  have h := J.supporting_block psi
  change supportingBlock iotaG blocksG (J.character psi) =
    (J.block ⟨supportingBlock iotaL blocksL psi.val, psi.property⟩).val at h
  rw [h]
  exact (J.block ⟨supportingBlock iotaL blocksL psi.val, psi.property⟩).property

/-- The derived packet-valued map keeps exactly the source character image. -/
def packetMap (psi : Packet iotaL blocksL eL) : Packet iotaG blocksG eG :=
  ⟨J.character psi, character_in_packet points Lbar field perfect iotaL iotaG
    blocksL blocksG eL eG gammaInvariant fieldInvariant J psi⟩

@[simp] theorem packetMap_value (psi : Packet iotaL blocksL eL) :
    (packetMap points Lbar field perfect iotaL iotaG blocksL blocksG eL eG
      gammaInvariant fieldInvariant J psi).val = J.character psi := rfl

end ModularRep.PaperProofs.TypeBRankThreeJordanMap


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
