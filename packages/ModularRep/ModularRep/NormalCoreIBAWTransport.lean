import ModularRep.NormalCoreTransport
import Formalisation.IBAWCore

/-!
# Transport of iBAW data through a normal p-core

This file proves the deduction in manuscript Lemma 2.6.  The
acting groups are allowed to differ: `AUp` models the upstairs group `A`,
`ADown` models `A / P`, and `actionMap` models the quotient homomorphism.

The structure `Inputs` contains only source-shaped transport data.  In
particular, it contains explicit equivalences for blocks, radical classes,
Brauer objects, weights, sectors, and the defect-zero normalisation objects.
It also states separately that inflation preserves the intermediate block
equalities, compatible extensions, and modular character triples.  It does
not contain an upstairs candidate, an upstairs iBAW datum, or the conclusion
of the transport theorem.

The group-theoretic construction of the radical and local-weight maps is in
`ModularRep.NormalCoreTransport`.  Identifying the principal-block Brauer
objects, proving that the actions factor through `A / P`, and instantiating
the three preservation fields are the remaining character-theoretic inputs
from the proof of Martínez--Rizo--Rossi, Lemma 6.3.  Their Brauer-character
inflation step cites Navarro, Lemma 2.32, and their character-triple step is
Martínez--Rizo--Rossi, Lemma 3.14.
-/

noncomputable section

namespace ModularRep.ManuscriptVerification.NormalCoreIBAWTransport

open Formalisation.IBAW

universe uAD uAU uBD uBU uRD uRU uSD uSU uXD uXU uYD uYU uDD uDU

variable
  {ADown : Type uAD} {AUp : Type uAU}
  {BDown : Type uBD} {BUp : Type uBU}
  {RDown : Type uRD} {RUp : Type uRU}
  {SDown : Type uSD} {SUp : Type uSU}
  {XDown : Type uXD} {XUp : Type uXU}
  {YDown : Type uYD} {YUp : Type uYU}
  {DZDown : Type uDD} {DZUp : Type uDU}
  [Group ADown] [Group AUp]
  [MulAction ADown BDown] [MulAction ADown RDown]
  [MulAction ADown SDown] [MulAction ADown XDown]
  [MulAction ADown YDown] [MulAction ADown DZDown]
  [MulAction AUp BUp] [MulAction AUp RUp]
  [MulAction AUp SUp] [MulAction AUp XUp]
  [MulAction AUp YUp] [MulAction AUp DZUp]

/-- Exact transport inputs for passage from a downstairs iBAW context to an
upstairs context.  The equivariance equations say that the upstairs action
is the pullback of the downstairs action along `actionMap` after applying the
displayed equivalences.

The last three fields are deliberately independent.  They isolate the parts
of the normal-core theorem concerning intermediate block equalities,
extensions, and modular character triples from the set-theoretic transport
of the bijection. -/
structure Inputs
    (CDown : Context ADown BDown RDown SDown XDown YDown DZDown)
    (CUp : Context AUp BUp RUp SUp XUp YUp DZUp) where
  actionMap : AUp →* ADown
  blockEquiv : BDown ≃ BUp
  radicalEquiv : RDown ≃ RUp
  sectorEquiv : SDown ≃ SUp
  inflateBrauer : XDown ≃ XUp
  liftWeight : YDown ≃ YUp
  inflateDefectZero : DZDown ≃ DZUp
  blockEquiv_equivariant : ∀ (a : AUp) (b : BDown),
    blockEquiv (actionMap a • b) = a • blockEquiv b
  radicalEquiv_equivariant : ∀ (a : AUp) (r : RDown),
    radicalEquiv (actionMap a • r) = a • radicalEquiv r
  sectorEquiv_equivariant : ∀ (a : AUp) (s : SDown),
    sectorEquiv (actionMap a • s) = a • sectorEquiv s
  inflateBrauer_equivariant : ∀ (a : AUp) (x : XDown),
    inflateBrauer (actionMap a • x) = a • inflateBrauer x
  liftWeight_equivariant : ∀ (a : AUp) (y : YDown),
    liftWeight (actionMap a • y) = a • liftWeight y
  inflateDefectZero_equivariant : ∀ (a : AUp) (d : DZDown),
    inflateDefectZero (actionMap a • d) = a • inflateDefectZero d
  brauerBlock_compatible : ∀ x : XDown,
    CUp.brauerBlock (inflateBrauer x) =
      blockEquiv (CDown.brauerBlock x)
  weightBlock_compatible : ∀ y : YDown,
    CUp.weightBlock (liftWeight y) =
      blockEquiv (CDown.weightBlock y)
  weightRadical_compatible : ∀ y : YDown,
    CUp.weightRadical (liftWeight y) =
      radicalEquiv (CDown.weightRadical y)
  blockSector_compatible : ∀ b : BDown,
    CUp.blockSector (blockEquiv b) =
      sectorEquiv (CDown.blockSector b)
  oneRadical_compatible : radicalEquiv CDown.oneRadical = CUp.oneRadical
  reduce_compatible : ∀ d : DZDown,
    CUp.reduce (inflateDefectZero d) = inflateBrauer (CDown.reduce d)
  atOne_compatible : ∀ d : DZDown,
    CUp.atOne (inflateDefectZero d) = liftWeight (CDown.atOne d)
  intermediateBlockEqualities_preserved : ∀ x : XDown, ∀ y : YDown,
    CDown.intermediateBlockEqualitiesOK x y →
      CUp.intermediateBlockEqualitiesOK (inflateBrauer x) (liftWeight y)
  extensions_preserved : ∀ x : XDown, ∀ y : YDown,
    CDown.extensionsOK x y →
      CUp.extensionsOK (inflateBrauer x) (liftWeight y)
  characterTriple_preserved : ∀ x : XDown, ∀ y : YDown,
    CDown.characterTripleOK x y →
      CUp.characterTripleOK (inflateBrauer x) (liftWeight y)

namespace Inputs

variable
  {CDown : Context ADown BDown RDown SDown XDown YDown DZDown}
  {CUp : Context AUp BUp RUp SUp XUp YUp DZUp}

/-- The modular-character-triple field of `Inputs`, exposed through the
individual lifting interface from `NormalCoreTransport`. -/
def modularCharacterTripleLifting (T : Inputs CDown CUp) :
    NormalCoreTransport.ModularCharacterTripleLifting
      XDown YDown XUp YUp where
  DownstairsTripleIsomorphism := CDown.characterTripleOK
  UpstairsTripleIsomorphism := CUp.characterTripleOK
  inflateGlobal := T.inflateBrauer
  inflateLocal := T.liftWeight
  lift := T.characterTriple_preserved

/-- Inverse inflation is equivariant for the pullback action. -/
theorem inflateBrauer_symm_equivariant (T : Inputs CDown CUp)
    (a : AUp) (x : XUp) :
    T.inflateBrauer.symm (a • x) =
      T.actionMap a • T.inflateBrauer.symm x := by
  apply T.inflateBrauer.injective
  rw [T.inflateBrauer.apply_symm_apply,
    T.inflateBrauer_equivariant,
    T.inflateBrauer.apply_symm_apply]

/-- The upstairs equivalence obtained by deflating a Brauer object, applying
the downstairs iBAW bijection, and lifting the resulting weight. -/
def transportedEquiv (T : Inputs CDown CUp) (D : Data CDown) : XUp ≃ YUp :=
  T.inflateBrauer.symm.trans (D.equiv.trans T.liftWeight)

@[simp]
theorem transportedEquiv_inflateBrauer
    (T : Inputs CDown CUp) (D : Data CDown) (x : XDown) :
    T.transportedEquiv D (T.inflateBrauer x) = T.liftWeight (D.equiv x) := by
  simp [transportedEquiv]

/-- The transported equivalence is equivariant for the upstairs action. -/
theorem transportedEquiv_equivariant
    (T : Inputs CDown CUp) (D : Data CDown)
    (a : AUp) (x : XUp) :
    T.transportedEquiv D (a • x) = a • T.transportedEquiv D x := by
  simp only [transportedEquiv, Equiv.trans_apply]
  rw [T.inflateBrauer_symm_equivariant,
    D.equiv_equivariant,
    T.liftWeight_equivariant]

/-- The transported equivalence preserves the block induced from the local
weight. -/
theorem transportedEquiv_block_preserving
    (T : Inputs CDown CUp) (D : Data CDown) (x : XUp) :
    CUp.weightBlock (T.transportedEquiv D x) = CUp.brauerBlock x := by
  let xDown := T.inflateBrauer.symm x
  have hx : T.inflateBrauer xDown = x := T.inflateBrauer.apply_symm_apply x
  calc
    CUp.weightBlock (T.transportedEquiv D x) =
        CUp.weightBlock (T.liftWeight (D.equiv xDown)) := by
      rw [← hx]
      exact congrArg CUp.weightBlock
        (T.transportedEquiv_inflateBrauer D xDown)
    _ = T.blockEquiv (CDown.weightBlock (D.equiv xDown)) :=
      T.weightBlock_compatible _
    _ = T.blockEquiv (CDown.brauerBlock xDown) :=
      congrArg T.blockEquiv (D.block_preserving xDown)
    _ = CUp.brauerBlock (T.inflateBrauer xDown) :=
      (T.brauerBlock_compatible xDown).symm
    _ = CUp.brauerBlock x := congrArg CUp.brauerBlock hx

/-- The transported equivalence before the three representation theoretic
certifications are attached. -/
def candidate (T : Inputs CDown CUp) (D : Data CDown) : Candidate CUp where
  equiv := T.transportedEquiv D
  equiv_equivariant := T.transportedEquiv_equivariant D
  block_preserving := T.transportedEquiv_block_preserving D

/-- Full transport of iBAW data.  Lean combines the upstairs datum from the
downstairs datum and the individually stated fields of `Inputs`; no upstairs
candidate or conclusion is assumed. -/
def transport (T : Inputs CDown CUp) (D : Data CDown) : Data CUp where
  toCandidate := T.candidate D
  intermediateBlockEqualities x := by
    let xDown := T.inflateBrauer.symm x
    change CUp.intermediateBlockEqualitiesOK x
      (T.liftWeight (D.equiv xDown))
    have h := T.intermediateBlockEqualities_preserved
      xDown (D.equiv xDown) (D.intermediateBlockEqualities xDown)
    exact T.inflateBrauer.apply_symm_apply x ▸ h
  extensions x := by
    let xDown := T.inflateBrauer.symm x
    change CUp.extensionsOK x (T.liftWeight (D.equiv xDown))
    have h := T.extensions_preserved
      xDown (D.equiv xDown) (D.extensions xDown)
    exact T.inflateBrauer.apply_symm_apply x ▸ h
  characterTriple x := by
    let xDown := T.inflateBrauer.symm x
    change CUp.characterTripleOK x (T.liftWeight (D.equiv xDown))
    have h := T.modularCharacterTripleLifting.lift
      xDown (D.equiv xDown) (D.characterTriple xDown)
    exact T.inflateBrauer.apply_symm_apply x ▸ h
  normalisation d := by
    let dDown := T.inflateDefectZero.symm d
    have hd : T.inflateDefectZero dDown = d :=
      T.inflateDefectZero.apply_symm_apply d
    calc
      T.transportedEquiv D (CUp.reduce d) =
          T.transportedEquiv D
            (CUp.reduce (T.inflateDefectZero dDown)) := by rw [hd]
      _ = T.transportedEquiv D
            (T.inflateBrauer (CDown.reduce dDown)) := by
        rw [T.reduce_compatible]
      _ = T.liftWeight (D.equiv (CDown.reduce dDown)) :=
        T.transportedEquiv_inflateBrauer D _
      _ = T.liftWeight (CDown.atOne dDown) :=
        congrArg T.liftWeight (D.normalisation dDown)
      _ = CUp.atOne (T.inflateDefectZero dDown) :=
        (T.atOne_compatible dDown).symm
      _ = CUp.atOne d := congrArg CUp.atOne hd

/-- The radical part of the transported datum is the image of the downstairs
radical part. -/
theorem transport_part_inflateBrauer
    (T : Inputs CDown CUp) (D : Data CDown) (x : XDown) :
    (T.transport D).toCandidate.part (T.inflateBrauer x) =
      T.radicalEquiv (D.toCandidate.part x) := by
  simp only [Candidate.part, transport, candidate,
    transportedEquiv_inflateBrauer]
  exact T.weightRadical_compatible (D.equiv x)

/-- Transport also preserves the central sector determined by a block. -/
theorem transport_sector_inflateBrauer
    (T : Inputs CDown CUp) (x : XDown) :
    CUp.blockSector (CUp.brauerBlock (T.inflateBrauer x)) =
      T.sectorEquiv (CDown.blockSector (CDown.brauerBlock x)) := by
  rw [T.brauerBlock_compatible, T.blockSector_compatible]

/-- The distinguished radical class used in the normalisation is transported
to the distinguished upstairs class. -/
theorem transport_oneRadical (T : Inputs CDown CUp) :
    T.radicalEquiv CDown.oneRadical = CUp.oneRadical :=
  T.oneRadical_compatible

end Inputs

end ModularRep.ManuscriptVerification.NormalCoreIBAWTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
