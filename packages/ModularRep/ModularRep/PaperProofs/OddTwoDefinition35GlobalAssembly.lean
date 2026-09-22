import ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
import ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow

/-!
# Actual block-stabilizer maps combined into the literal FM global map

Only the equivalences and equivariance of a Definition 3.5 family are
needed here. The fixed stabilizer adapters convert their actions to the
actual opposite automorphism group. The construction from block orbit representatives
then gives the global map. No compatibility between independently chosen
maps on different blocks is assumed.

The literal family below reuses precisely a LiteralFengMalleProblem's
coefficients, group, root, primitive blocks and local operations. Its
acting groups are the actual block stabilizers. No character-triple,
extension, source theorem or final iBAW conclusion is asserted here.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoDefinition35GlobalAssembly

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.OddConlonOrbitAssembly
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow

universe u

/-- The map-only part of a fixed family. The actual acting-group
identification is supplied separately by its stabilizer adapter. -/
structure BlockMapFamily {ell : ℕ} (family : Definition35Family.{u} ell) where
  omega : ∀ block : family.Block,
    Definition35Brauer (family.problem block) ≃
      Definition35Weight (family.problem block)
  equivariant : ∀ block : family.Block,
    Definition35Equivariant (family.problem block) (omega block)

def mapsOfDefinition35Family {ell : ℕ} {family : Definition35Family.{u} ell}
    {automorphisms : ∀ block, Definition35AutomorphismStabilizerAdapter (family.problem block)}
    {source : ∀ block, FLZSourceSemantics (family.problem block) (automorphisms block)}
    (witness : Definition35IBAWFamilyWitness family automorphisms source) :
    BlockMapFamily family where
  omega block := (witness.blockWitness block).omega
  equivariant block := (witness.blockWitness block).equivariant

def familyBrauerBlock {ell : ℕ} (family : Definition35Family.{u} ell)
    (psi : IBr family.iota) : family.Block :=
  irreducibleBrauerCharacterBlock family.iota family.irreducibleBrauerInjective
    family.blocks psi

namespace BlockMapFamily

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable (maps : BlockMapFamily family)

/-- Each representative uses its own given block map. The exact
stabilizer adapter proves the equivariance required by construction from orbit representatives. -/
def representativeMaps (automorphisms : ∀ block,
    Definition35AutomorphismStabilizerAdapter (family.problem block)) :
    RepresentativeEquivFamily (familyBrauerBlock family) family.blockSource.weightBlock
      family.brauerBlock_transport where
  equiv orbit := maps.omega (orbitRepresentative orbit)
  equivariant orbit a hfix psi := by
    let b := orbitRepresentative orbit
    letI := definition35BrauerAction (family.problem b)
    letI := definition35WeightAction (family.problem b)
    let lift : (family.automorphisms b).Gamma :=
      (automorphisms b).equiv.symm ⟨a, hfix⟩
    have hlift : inverseOpHom (family.automorphisms b).gamma lift = a := by
      change inverseOpHom (family.problem b).gamma lift = a
      rw [← (automorphisms b).equiv_coe lift]
      exact congrArg Subtype.val ((automorphisms b).equiv.apply_symm_apply ⟨a, hfix⟩)
    have h := congrArg Subtype.val (maps.equivariant b lift psi)
    change (maps.omega b ⟨inverseOpHom (family.automorphisms b).gamma lift • psi.1, _⟩).1 =
      @CharacterWeight.rightTwistConjugacyClass ell family.K family.H
        family.fieldK family.charZeroK family.groupH (by infer_instance)
        (inverseOpHom (family.automorphisms b).gamma lift).unop (maps.omega b psi).1 at h
    change (maps.omega b ⟨a • psi.1, _⟩).1 =
      @CharacterWeight.rightTwistConjugacyClass ell family.K family.H
        family.fieldK family.charZeroK family.groupH (by infer_instance)
        a.unop (maps.omega b psi).1
    simpa only [hlift] using h

variable (automorphisms : ∀ block,
  Definition35AutomorphismStabilizerAdapter (family.problem block))

include maps automorphisms

def globalEquiv : IBr family.iota ≃
    ConjugacyClass (p := ell) (K := family.K) (G := family.H) :=
  (maps.representativeMaps automorphisms).globalEquiv
    (familyBrauerBlock family) family.blockSource.weightBlock
    family.brauerBlock_transport family.blockSource.weightBlock_transport

theorem globalEquiv_equivariant (a : (MulAut family.H)ᵐᵒᵖ) (psi : IBr family.iota) :
    maps.globalEquiv automorphisms (a • psi) = a • maps.globalEquiv automorphisms psi :=
  (maps.representativeMaps automorphisms).globalEquiv_equivariant
    (familyBrauerBlock family) family.blockSource.weightBlock
    family.brauerBlock_transport family.blockSource.weightBlock_transport a psi

theorem globalEquiv_block (psi : IBr family.iota) :
    family.blockSource.weightBlock (maps.globalEquiv automorphisms psi) =
      familyBrauerBlock family psi :=
  (maps.representativeMaps automorphisms).globalEquiv_block_preserving
    (familyBrauerBlock family) family.blockSource.weightBlock
    family.brauerBlock_transport family.blockSource.weightBlock_transport psi

end BlockMapFamily

section LiteralFamily

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
local instance spFintype : Fintype (LiteralSp n F) := Fintype.ofFinite _
local instance automorphismFinite : Finite (MulAut (LiteralSp n F)) :=
  Finite.of_injective (fun a : MulAut (LiteralSp n F) => (a : LiteralSp n F → LiteralSp n F))
    DFunLike.coe_injective
local instance oppositeAutomorphismFinite : Finite (MulAut (LiteralSp n F))ᵐᵒᵖ :=
  Finite.of_equiv (MulAut (LiteralSp n F)) MulOpposite.opEquiv

variable (P : LiteralFengMalleProblem n F)

abbrev LiteralBlock := LiteralPrimitiveBlock P.k (LiteralSp n F)
abbrev LiteralBlockStabilizer (b : LiteralBlock P) :=
  MulAction.stabilizer (MulAut (LiteralSp n F))ᵐᵒᵖ b

local instance blockStabilizerFinite (b : LiteralBlock P) : Finite (LiteralBlockStabilizer P b) :=
  Finite.of_injective
    (fun a : LiteralBlockStabilizer P b => (a.1 : (MulAut (LiteralSp n F))ᵐᵒᵖ))
    Subtype.val_injective

def literalBlockGamma (b : LiteralBlock P) : LiteralBlockStabilizer P b →* MulAut (LiteralSp n F) where
  toFun a := a.1.unop⁻¹
  map_one' := by simp
  map_mul' a c := by
    change (c.1.unop * a.1.unop)⁻¹ = a.1.unop⁻¹ * c.1.unop⁻¹
    exact mul_inv_rev _ _

theorem literalBlockGamma_coe (b : LiteralBlock P) (a : LiteralBlockStabilizer P b) :
    inverseOpHom (literalBlockGamma P b) a = a.1 := by
  change MulOpposite.op ((a.1.unop⁻¹)⁻¹) = a.1
  rw [inv_inv, MulOpposite.op_unop]

theorem literalBlockGamma_fixed (b : LiteralBlock P) (a : LiteralBlockStabilizer P b) :
    inverseOpHom (literalBlockGamma P b) a • b = b := by
  rw [literalBlockGamma_coe]
  exact a.2

variable (support : OperationsBrauerSupport P.iota P.irreducibleBrauerInjective
  P.blockSource.operations)
variable (reduction : ∀ (b : LiteralBlock P) (w : LiteralWeightFibre P.blockSource b),
  SelectedLocalReductionSource P.blockSource b w)

/-- Canonical all-block presentation on literally the input FM problem.
Support transport and selected reductions are standard bookkeeping, not
block maps. The set of blocks is its actual primitive central idempotents. -/
def literalFamily : Definition35Family.{u} 2 where
  ellPrime := Nat.prime_two
  k := P.k
  K := P.K
  H := LiteralSp n F
  Block := LiteralBlock P
  fieldk := P.fieldk
  fieldK := P.fieldK
  charPk := P.charPk
  algClosedk := P.algClosedk
  charZeroK := P.charZeroK
  fintypeBlock := P.blockSource.operations.ambientBlockData.fintypeBlock
  blockIdempotent := P.blockSource.operations.ambientBlockData.blockIdempotent
  iota := P.iota
  irreducibleBrauerInjective := P.irreducibleBrauerInjective
  blocks := P.blockSource.operations.ambientBlockData.blocks
  blockSource := P.blockSource
  brauerBlock_transport := support
  automorphisms b :=
    { Gamma := LiteralBlockStabilizer P b
      gamma := literalBlockGamma P b
      gammaBlock_fixed := literalBlockGamma_fixed P b }
  localReduction := reduction

/-- The canonical stabilizer adapter is the identity on the actual
subgroup, with its inverse/op action equality proved above. -/
def literalAutomorphisms (b : LiteralBlock P) :
    Definition35AutomorphismStabilizerAdapter
      ((literalFamily P support reduction).problem b) where
  equiv := MulEquiv.refl _
  equiv_coe a := (literalBlockGamma_coe P b a).symm

/-- K: only the existing block-orbit construction is used to build this
literal map. No new global-map source is accepted. -/
def literalGlobalMap (maps : BlockMapFamily (literalFamily P support reduction)) :
    LiteralGlobalMap P where
  equiv := maps.globalEquiv (literalAutomorphisms P support reduction)
  equivariant := maps.globalEquiv_equivariant (literalAutomorphisms P support reduction)
  block_preserving := maps.globalEquiv_block (literalAutomorphisms P support reduction)

end LiteralFamily

end ModularRep.PaperProofs.OddTwoDefinition35GlobalAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
