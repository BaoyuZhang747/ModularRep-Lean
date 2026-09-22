import ModularRep.PaperProofs.TypeBQ3AssemblyApplication
import ModularRep.PaperProofs.TypeBQ3PrimeToTwoCover

/-!
# The target of Proposition 4.11

The group is the constructed central triple cover of the specified matrix
Omega group over ZMod 3. Each block uses one of the two natural
presentations established by the proof for the nine blocks. The cover, its
projection and its maximality are constructed separately from the
representation theoretic conclusion.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.Exceptional

open ModularRep ModularRep.PaperProofs
open TypeBQ3TripleCoverCarrier TypeBCentralKernelBlockSource
open TypeBQ3PrincipalWeightInflation TypeBRankThreePrincipalCountBinding
open EvenFieldFLZSourceConditions

local instance exceptionalTargetFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

/-- The coefficient fields, groups, characters and weights are fixed before
the inductive condition is proved. The ordinary field has characteristic zero.
Only the modular field is assumed algebraically closed. -/
structure Target (S : Type) [Group S] where
  k : Type
  K : Type
  [fieldk : Field k]
  [fieldK : Field K]
  [chark : CharP k 2]
  [closedk : IsAlgClosed k]
  [zeroK : CharZero K]
  matrixSource : MatrixExceptionalSource
  freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource
  root :
    letI : Finite X := finite_X matrixSource
    PrimeRegularRootEmbedding 2 k K X
  R : OmegaWeightSource (k := k) (K := K) (ZMod 3)
  RX :
    letI : Finite X := finite_X matrixSource
    CoverWeightSource (k := k) (K := K) X
  base : G3 ≃* S

attribute [instance] Target.fieldk Target.fieldK Target.chark Target.closedk Target.zeroK

variable {S : Type} [Group S] (T : Target S)

/-- The universal prime-to-two cover is this exact triple cover construction. -/
def Target.cover :
    letI : Fintype X := fintype_X T.matrixSource
    EllPrimeCoverSource 2 X :=
  TypeBQ3PrimeToTwoCover.ellPrimeCover T.matrixSource T.freeSource

@[simp] theorem Target.cover_projection :
    letI : Fintype X := fintype_X T.matrixSource
    T.cover.quotient = q T.matrixSource T.freeSource := rfl

/-- The isomorphism identifies the simple base group and preserves the covering
group. -/
def Target.simpleEquiv :
    letI : Fintype X := fintype_X T.matrixSource
    T.cover.S ≃* S := T.base

theorem Target.cover_kernel_card :
    letI : Fintype X := fintype_X T.matrixSource
    Nat.card T.cover.quotient.ker = 3 :=
  q_kernel_card T.matrixSource T.freeSource

include T in
theorem Target.cover_center_card : Nat.card (Subgroup.center X) = 3 :=
  center_X_card T.matrixSource T.freeSource

/-- The quotient root is computed from the original triple cover root. -/
def Target.rootDown : PrimeRegularRootEmbedding 2 T.k T.K G3 := by
  letI : Finite X := finite_X T.matrixSource
  exact TypeBQ3B2CentralQuotient.downRoot T.matrixSource T.freeSource T.root

/-- The data on the specified natural quotient presentations. Their fields
include common kernels and the kernel of each character, the specified block
images, deflation values, the complete equivariant matching and every
extension clause. -/
def Target.NaturalWitness (b : LiteralPrimitiveBlock T.k X) : Type :=
  letI : Finite X := finite_X T.matrixSource
  TypeBQ3AssemblyQuotientPresentation.Witness T.matrixSource T.freeSource T.root b
      (q T.matrixSource T.freeSource) T.rootDown T.R ⊕
    TypeBQ3AssemblyQuotientPresentation.Witness T.matrixSource T.freeSource T.root b
      (MonoidHom.id X) T.root T.RX

/-- The independently fixed complete target, quantified over every actual
primitive block, not just over the nine labels. -/
def Target.Complete : Prop :=
  ∀ b : LiteralPrimitiveBlock T.k X, Nonempty (T.NaturalWitness b)

/-- Choose the data supplied by the proof for each block. -/
def Target.selected (complete : T.Complete) (b : LiteralPrimitiveBlock T.k X) :
    T.NaturalWitness b := Classical.choice (complete b)

end ManuscriptIBAW.TypeB.Exceptional

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
