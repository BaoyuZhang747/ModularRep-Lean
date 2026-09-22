import ModularRep.PaperProofs.SporadicFi24P3PrincipalCancellationFromSources

/-!
# The An--Dietrich source certificate for `Fi'_{24}` at three

An--Dietrich, Definition 4.4 and Section 4.3.4, supply an existential
automorphism-equivariant bijection between the complete Brauer-character and
sets of weights in the centreless case.  They do not identify those published
carriers with the literal carriers below, and they do not assert block
preservation.

This file records exactly that separation.  `AnDietrichFi24P3SourceCertificate`
contains only the published global equivariant bijection.
`AnDietrichFi24P3LiteralCarrierBridge` separately identifies the published
automorphism action, Brauer carrier, and set of weights with the corresponding
literal objects.  Centrelessness remains an explicit hypothesis of the
adapter.  The final theorem passes the transported global equivalence to the
existing source-facing cancellation theorem; its remaining arguments are the
independent sources for the two known block fibres.

There is no block-preserving correspondence, principal-block correspondence,
principal signature, compatible-extension clause, or iBAW conclusion in
either source structure.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate

open Formalisation
open Formalisation.BlockCancellation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24QOneNormalisationActual
open SporadicFi24ThreeBlockCancellationActual
open SporadicFi24KnownFibreBridgeActual
open SporadicFi24P3PrincipalCancellationFromSources

universe u

variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction]
variable [MulAction SourceAction SourceBrauer]
variable [MulAction SourceAction SourceWeight]

/-- The exact global correspondence supplied by An--Dietrich in the
centreless `Fi'_{24}`, `p = 3` case.  `SourceAction` is the paper's right
automorphism action written as a left action.  No literal-carrier or block
identification is part of this certificate. -/
structure AnDietrichFi24P3SourceCertificate where
  sourceEquiv : SourceBrauer ≃ SourceWeight
  sourceEquivariant : ∀ (a : SourceAction) (phi : SourceBrauer),
    sourceEquiv (a • phi) = a • sourceEquiv phi

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

/-- The unresolved identification of the three published source carriers with
the literal Lean carriers.  The action-group equivalence includes the passage
from the paper's exponent/right-action convention to the literal left action
of `(MulAut X)ᵐᵒᵖ`.

The two intertwining fields assert action compatibility of the carrier
identifications themselves.  They do not mention blocks or central sectors. -/
structure AnDietrichFi24P3LiteralCarrierBridge
    (iota : PrimeRegularRootEmbedding 3 k K X) where
  actionIdentification : (MulAut X)ᵐᵒᵖ ≃* SourceAction
  brauerIdentification : IBr iota ≃ SourceBrauer
  brauerIdentification_equivariant :
    ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      brauerIdentification (a • phi) =
        actionIdentification a • brauerIdentification phi
  weightIdentification :
    SourceWeight ≃ WeightClass (p := 3) (K := K) (X := X)
  weightIdentification_equivariant :
    ∀ (a : (MulAut X)ᵐᵒᵖ) (weight : SourceWeight),
      weightIdentification (actionIdentification a • weight) =
        a • weightIdentification weight

namespace AnDietrichFi24P3SourceCertificate

variable (iota : PrimeRegularRootEmbedding 3 k K X)

variable
  (AD : AnDietrichFi24P3SourceCertificate
    (SourceAction := SourceAction)
    (SourceBrauer := SourceBrauer)
    (SourceWeight := SourceWeight))
  (Bridge : AnDietrichFi24P3LiteralCarrierBridge
    (SourceAction := SourceAction)
    (SourceBrauer := SourceBrauer)
    (SourceWeight := SourceWeight) (k := k) (K := K) (X := X) iota)

/-- Transport the published global bijection across the explicit carrier
identifications. -/
def literalEquiv :
    IBr iota ≃ WeightClass (p := 3) (K := K) (X := X) :=
  (Bridge.brauerIdentification.trans AD.sourceEquiv).trans
    Bridge.weightIdentification

/-- The transported bijection is equivariant for the full literal
automorphism action. -/
theorem literalEquiv_equivariant
    (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    literalEquiv iota AD Bridge (a • phi) =
      a • literalEquiv iota AD Bridge phi := by
  change Bridge.weightIdentification
      (AD.sourceEquiv (Bridge.brauerIdentification (a • phi))) =
    a • Bridge.weightIdentification
      (AD.sourceEquiv (Bridge.brauerIdentification phi))
  rw [Bridge.brauerIdentification_equivariant,
    AD.sourceEquivariant, Bridge.weightIdentification_equivariant]

variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R :
  LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-- For a centreless literal carrier, the transported published bijection
supplies the raw central-sector family.  Sector preservation is automatic
because the central-sector type is a subsingleton; no block fact is used. -/
def toRawSectorFamily
    (hcenter : ∀ z : Subgroup.center X, z = 1) :
    RawSectorFamily iota hinj blocks E1 :=
  rawSectorFamilyOfEquivariantEquiv iota hinj blocks E1 hcenter
    (literalEquiv iota AD Bridge)
    (literalEquiv_equivariant iota AD Bridge)

include AD Bridge

/-- Feed the An--Dietrich source certificate and its explicit literal-carrier
bridge to the existing source-facing principal cancellation theorem.

The principal equivalence is a conclusion.  The two known-fibre sources are
the independent hypotheses already required by that theorem. -/
theorem exists_principalFibreEquiv_from_anDietrich
    (hcenter : ∀ z : Subgroup.center X, z = 1)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (Z0 : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (F0 : Fi24DefectZeroBlockIdentification iota hinj blocks D S)
    (NC : Fi24NonprincipalCensusSource iota hinj blocks E1 S) :
    ∃ principal :
        BrauerFibre iota hinj blocks S.principalBlock ≃
          WeightFibre (R := R) S.principalBlock,
      Intertwines principal
        (principalBrauerPerm iota hinj blocks E1 S)
        (principalWeightPerm (R := R) S) :=
  exists_principalFibreEquiv_from_sources
    iota hinj blocks E1 hcenter
    (literalEquiv iota AD Bridge)
    (literalEquiv_equivariant iota AD Bridge)
    D T C B Z0 S F0 NC

end AnDietrichFi24P3SourceCertificate

end ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
