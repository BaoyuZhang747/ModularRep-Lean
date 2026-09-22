import ModularRep.PaperProofs.TypeCActualCaseSourceData
import ModularRep.PaperProofs.CurrentFiniteSplittingAssembly
import ModularRep.PaperProofs.CurrentCentralQuotientReturnAdapter

/-!
# Li–Li's rank two theorem and the separate central lift

Li–Li, Algebra Colloquium 26 (2019), Theorem 1.1, proves the
inductive blockwise Alperin weight condition for PSp4(q), for odd q and
every nondefining prime. Section 6 and Theorem 6.9 use PSp4 itself at two.
At odd primes the cover is Sp4 with its central quotient map.
These statements include q = 3.

Li–Li is interpreted separately in a splitting modular system and over an
algebraically closed ordinary field. Compatibility across blocks is a
separate published source assumption.
The principal bijection on Sp4 at two uses the proved central lift and a
separate interpretation of the condition for each character and its
corresponding weight.
None of these interfaces asserts pointwise field fixation or the stronger
Feng–Malle hypotheses.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeC.LiLiSource

open ModularRep CharacterWeight
open ModularRep.PaperProofs
open OddTwoConformalProjectiveRealisation (Sp PSp spProjection)
open OddTwoUniversalPrimeToTwoSelfCover
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open CyclicOuterLemma37LiteralLocalExtension
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition
open CurrentCentralQuotientReturnAdapter
open ModularRep.ManuscriptVerification.CyclicOuterBAW

local instance rankTwoFinite (G : Type) [Finite G] : Fintype G := Fintype.ofFinite G

/-- The exact selected cover, up to specified group coordinates. At two the
projection is the identity on PSp4. At odd primes it is Sp4 to PSp4. -/
structure CoverCoordinates (ell : ℕ) (F : Type) [Field F]
    {H : Type} [Group H] [Fintype H] (cover : EllPrimeCoverSource ell H) where
  simpleEquiv : cover.S ≃* PSp 2 F
  atTwo : ell = 2 → ∃ e : H ≃* PSp 2 F,
    simpleEquiv.toMonoidHom.comp cover.quotient = e.toMonoidHom
  atOdd : ell ≠ 2 → ∃ e : H ≃* Sp 2 F,
    simpleEquiv.toMonoidHom.comp cover.quotient = (spProjection 2 F).comp e.toMonoidHom

/-- Reuse the proved universal prime-to-two identity cover. -/
def twoCoverCoordinates (F : Type) [Field F] [Finite F]
    (source : OddSymplecticFullCoverSource 2 F) :
    CoverCoordinates 2 F source.identityEllPrimeCover where
  simpleEquiv := MulEquiv.refl _
  atTwo _ := ⟨MulEquiv.refl _, rfl⟩
  atOdd h := False.elim (h rfl)

/-- Reuse the proved odd-prime cover on literal Sp4 and its exact projection. -/
def oddCoverCoordinates (ell : ℕ) (F : Type) [Field F] [Finite F]
    (prime : Nat.Prime ell) (notTwo : ell ≠ 2)
    (source : OddSymplecticFullCoverSource 2 F)
    (perfect : commutator (Sp 2 F) = ⊤) :
    CoverCoordinates ell F
      (TypeCRankTwoOddSourceApplication.actualCover F source perfect ell prime notTwo) where
  simpleEquiv := MulEquiv.refl _
  atTwo h := False.elim (notTwo h)
  atOdd _ := ⟨MulEquiv.refl _, rfl⟩

/-- Specified coefficients, literal block operations and root identifications.
No block matching is part of these inputs. The fraction field only needs
the splitting roots of the finite group, not algebraic closure. -/
structure Coefficients {ell : ℕ} (family : Definition35Family.{0} ell) where
  O : Type
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraO : Algebra O family.K]
  modularSystem : ModularSystem ell family.K O family.k
  ordinaryRoots : HasEnoughRootsOfUnity family.K (Nat.card family.H)
  root : family.iota = TypeBModularGroupRootBinding.groupRoot modularSystem family.H
  coefficient : SpathCoefficientField ell family.k family.ellPrime
  idempotent : ∀ b, family.blockSource.operations.ambientBlockData.blockIdempotent b =
    family.blockIdempotent b
  physical : GuardedBlockCompatibility family.iota family.blockSource.operations
  roots : ∀ b w, QuotientRootAgreement family.iota
    (SelectedRadical family.blockSource b w) (family.localReduction b w).iota

attribute [instance] Coefficients.ringO Coefficients.domainO Coefficients.algebraO

/-- Li–Li Theorem 1.1 in the specified interpretation for each block, on the
actual prime-to-ell cover. This is an external source certificate, not a
kernel proof of Li–Li or of the interpretation of its character data.
The acting group must be identified with the full block stabiliser before
this source is applied. The coefficient prime need not divide q²-1. -/
structure Source : Prop where
  blockwise : ∀ (ell : ℕ) (F : Type) [Field F] [Finite F]
      (family : Definition35Family.{0} ell) (cover : EllPrimeCoverSource ell family.H)
      (_coordinates : CoverCoordinates ell F cover) (_coefficients : Coefficients family)
      (_stabilizers : ∀ b, Definition35AutomorphismStabilizerAdapter (family.problem b)),
    Odd (Nat.card F) → ¬ ell ∣ Nat.card F → ell ∣ Nat.card (PSp 2 F) →
    ∀ b, Nonempty (BlockWitness family cover b)

/-- Identification with the full block stabiliser forces the action on the
underlying group to be faithful. -/
theorem stabilizer_action_injective (P : Definition35Problem.{0})
    (stabilizer : Definition35AutomorphismStabilizerAdapter P) :
    Function.Injective P.gamma := by
  intro a b same
  apply stabilizer.equiv.injective
  apply Subtype.ext
  rw [stabilizer.equiv_coe, stabilizer.equiv_coe]
  change MulOpposite.op (P.gamma a⁻¹) = MulOpposite.op (P.gamma b⁻¹)
  rw [map_inv, map_inv, same]

/-- A nonfaithful action cannot meet the stabiliser hypothesis of the source. -/
theorem no_stabilizer_of_nonfaithful (P : Definition35Problem.{0})
    (nonfaithful : ¬ Function.Injective P.gamma) :
    IsEmpty (Definition35AutomorphismStabilizerAdapter P) :=
  ⟨fun stabilizer => nonfaithful (stabilizer_action_injective P stabilizer)⟩

/-- In particular, the trivial action of a nontrivial group is excluded. -/
theorem no_stabilizer_of_trivial_action (P : Definition35Problem.{0})
    [Nontrivial P.Gamma] (trivial : ∀ a, P.gamma a = 1) :
    IsEmpty (Definition35AutomorphismStabilizerAdapter P) := by
  apply no_stabilizer_of_nonfaithful P
  intro faithful
  obtain ⟨a, b, different⟩ := exists_pair_ne P.Gamma
  exact different (faithful ((trivial a).trans (trivial b).symm))

/-- A trivial acting group cannot be the full block stabiliser of a
nonabelian group. Inner automorphisms fix every block, so such an
identification would force every conjugation to be trivial. This excludes
the singleton acting group used in the original source counterexample. -/
theorem no_stabilizer_of_subsingleton_on_nonabelian (P : Definition35Problem.{0})
    [Subsingleton P.Gamma] (nonabelian : ¬ IsMulCommutative P.H) :
    IsEmpty (Definition35AutomorphismStabilizerAdapter P) := by
  refine ⟨fun stabilizer => nonabelian ?_⟩
  refine ⟨⟨fun x y => ?_⟩⟩
  let a : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ P.block :=
    ⟨MulOpposite.op (MulAut.conj x), by
      change MulOpposite.op (MulAut.conj x) • P.block = P.block
      simpa only [inv_inv] using P.blockSource.inner_blocks_fixed x⁻¹ P.block⟩
  have ha : a = 1 := stabilizer.equiv.symm.injective (Subsingleton.elim _ _)
  have hc : x * y * x⁻¹ = y := by
    have h := congrArg (fun t : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ P.block =>
      MulOpposite.unop t.val y) ha
    exact h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (fun z => z * x) hc

/-- The separately specified compatibility and root normalisation across
blocks. This reuses the Koshitani–Späth/Späth source over splitting coefficients. -/
abbrev FamilyCompatibilitySource := CurrentFiniteSplittingAssembly.Source

/-- Independent rank two source inputs, with cover and coefficients fixed
before Li–Li supplies any block witness. -/
structure Inputs (ell : ℕ) (F : Type) [Field F] [Finite F] (prime : Nat.Prime ell) where
  family : Definition35Family.{0} ell
  cover : EllPrimeCoverSource ell family.H
  coordinates : CoverCoordinates ell F cover
  coefficients : Coefficients family
  stabilizers : ∀ b, Definition35AutomorphismStabilizerAdapter (family.problem b)
  fieldOdd : Odd (Nat.card F)
  liLi : Source
  compatibility : FamilyCompatibilitySource

namespace Inputs

variable {ell : ℕ} {F : Type} [Field F] [Finite F] {prime : Nat.Prime ell}

def target (D : Inputs ell F prime) : TypeCActualCaseSourceData.ActualTarget 2 ell F where
  family := D.family
  cover := D.cover
  simpleEquiv := D.coordinates.simpleEquiv

/-- Apply Li–Li to each block and then the separate compatibility theorem. -/
theorem complete (D : Inputs ell F prime) (notDvd : ¬ ell ∣ Nat.card F)
    (divides : ell ∣ Nat.card (PSp 2 F)) :
    Nonempty (FamilyWitness D.target.family D.target.cover) :=
  CurrentFiniteSplittingAssembly.fullFamily D.family D.cover D.coefficients.modularSystem
    D.compatibility D.coefficients.ordinaryRoots D.coefficients.root
    D.coefficients.coefficient D.coefficients.idempotent D.coefficients.physical
    D.coefficients.roots
    (D.liLi.blockwise ell F D.family D.cover D.coordinates D.coefficients
      D.stabilizers D.fieldOdd notDvd divides)

end Inputs

/-- Reference and coefficient normalisation for a given Brauer character and its corresponding weight.
The common central quotient defined by the reference character is
transported using equality of its central kernel with that of psi. The character and ordinary weight pair
remain fixed, with coherent extension and intermediate block data for that
same pair. Roots on every auxiliary
group must agree, beyond the splitting roots of the base group.

This explicit interpretation is separate from Li–Li. Its scope is the
standard quotient formulation in Brough–Späth Definition 4.3 and Remark 4.4.
A universal ell-prime cover is not asserted to be a full universal cover.
In particular, PSp4 at two uses its identity ell-prime cover. This source
supplies neither a new bijection nor a predetermined matching. -/
structure SingleBlockCompatibilitySource : Prop where
  normalize : ∀ {ell : ℕ} (family : Definition35Family.{0} ell)
    (cover : EllPrimeCoverSource ell family.H) (_coefficients : Coefficients family)
    (block : family.Block) (W : BlockWitness family cover block)
    (psi : Definition35Brauer (family.problem block)),
      Nonempty (CurrentCyclicOuterBAW.CoherentMatchedCondition
        (family.problem block) psi (W.relative.omega psi))

/-- Preserve the published bijection and its equivariance exactly. Only the
reference quotient and coefficient identifications use the separate source. -/
def SingleBlockCompatibilitySource.coherent (source : SingleBlockCompatibilitySource)
    {ell : ℕ} (family : Definition35Family.{0} ell)
    (cover : EllPrimeCoverSource ell family.H) (coefficients : Coefficients family)
    (block : family.Block) (W : BlockWitness family cover block) :
    CoherentBlockWitness (family.problem block) where
  omega := W.relative.omega
  equivariant := W.relative.equivariant
  matched psi := source.normalize family cover coefficients block W psi

/-- The actual Sp4 central lift at two. The quotient family, quotient block
and coefficient fields are computed by `central`, before Li–Li is applied.
The commuting projection and central normal core identify the manuscript's
Sp4/Z quotient. All triple and inflation hypotheses remain explicit in
`central`, which contains no upstairs block witness. -/
structure RankTwoPrincipalInputs (F : Type) [Field F] [Finite F]
    (P : Definition35Problem.{0})
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (semantics : FLZSourceSemantics P automorphisms) where
  primeTwo : P.p = 2
  fieldOdd : Odd (Nat.card F)
  notDvd : ¬ P.p ∣ Nat.card F
  divides : P.p ∣ Nat.card (PSp 2 F)
  upstairs : P.H ≃* Sp 2 F
  core_center : pCore P.p P.H = Subgroup.center P.H
  central : CentralReturnInputs P automorphisms semantics
  cover : EllPrimeCoverSource P.p central.downFamily.H
  coordinates : CoverCoordinates P.p F cover
  quotient_coordinates : ∀ h : P.H,
    coordinates.simpleEquiv (cover.quotient (QuotientGroup.mk' (pCore P.p P.H) h)) =
      spProjection 2 F (upstairs h)
  coefficients : Coefficients central.downFamily
  liLi : Source
  compatibility : SingleBlockCompatibilitySource

namespace RankTwoPrincipalInputs

variable {F : Type} [Field F] [Finite F] {P : Definition35Problem.{0}}
variable {automorphisms : Definition35AutomorphismStabilizerAdapter P}
variable {semantics : FLZSourceSemantics P automorphisms}

/-- The principal seed follows from Li–Li downstairs and the already proved
central lift on that exact witness. No Feng–Malle assumption is used. -/
def seed (D : RankTwoPrincipalInputs F P automorphisms semantics) :
    Definition35IBAWBijection P automorphisms semantics :=
  D.central.toDefinition35
    (D.compatibility.coherent D.central.downFamily D.cover D.coefficients D.central.downBlock
      (Classical.choice (D.liLi.blockwise P.p F D.central.downFamily D.cover D.coordinates
        D.coefficients
        (by
          letI := D.central.quotientFintype
          letI := D.central.downBlockFintype
          exact CurrentFiniteSplittingFamily.primitiveFamily_automorphisms
            D.central.iotaDown D.central.hinjDown D.central.downBlocks
            P.iota.prime D.central.physicalDown)
        D.fieldOdd D.notDvd D.divides D.central.downBlock)))

end RankTwoPrincipalInputs

/-! The Type C relative principal construction uses an algebraically closed
ordinary coefficient field. The source interfaces below apply in that field.
The global rank two theorem and Type B relative principal construction use the
splitting modular systems above. No change of coefficient fields is claimed. -/

/-- The exact family, primitive idempotents and root convention over an
algebraically closed ordinary field. The specified ambient embedding remains
family.iota, with the guarded block operations and local quotient roots.
There is no change of coefficient field in this record. -/
structure ClosedCoefficients {ell : ℕ} (family : Definition35Family.{0} ell) where
  ordinarySplitting : IsAlgClosed family.K
  ordinaryRoots : HasEnoughRootsOfUnity family.K (Nat.card family.H)
  coefficient : SpathCoefficientField ell family.k family.ellPrime
  idempotent : ∀ b, family.blockSource.operations.ambientBlockData.blockIdempotent b =
    family.blockIdempotent b
  physical : GuardedBlockCompatibility family.iota family.blockSource.operations
  roots : ∀ b w, QuotientRootAgreement family.iota
    (SelectedRadical family.blockSource b w) (family.localReduction b w).iota

/-- Li–Li Theorem 1.1 interpreted over the specified algebraically closed
ordinary coefficient field. The actual cover and all nondefining primes are
the same as in Source, but no modular system with this field as its fraction field is
required or asserted. This is a separate external source interpretation,
not a coefficient-change theorem derived from the modular-system interface.
The acting group is required to be the full block stabiliser. -/
structure ClosedSource : Prop where
  blockwise : ∀ (ell : ℕ) (F : Type) [Field F] [Finite F]
      (family : Definition35Family.{0} ell) (cover : EllPrimeCoverSource ell family.H)
      (_coordinates : CoverCoordinates ell F cover) (_coefficients : ClosedCoefficients family)
      (_stabilizers : ∀ b, Definition35AutomorphismStabilizerAdapter (family.problem b)),
    Odd (Nat.card F) → ¬ ell ∣ Nat.card F → ell ∣ Nat.card (PSp 2 F) →
    ∀ b, Nonempty (BlockWitness family cover b)

/-- The same pointwise reference and root interpretation over closed
coefficients. It supplies coherent data for the given character and its
corresponding weight, without choosing a new bijection. -/
structure ClosedSingleBlockCompatibilitySource : Prop where
  normalize : ∀ {ell : ℕ} (family : Definition35Family.{0} ell)
    (cover : EllPrimeCoverSource ell family.H) (_coefficients : ClosedCoefficients family)
    (block : family.Block) (W : BlockWitness family cover block)
    (psi : Definition35Brauer (family.problem block)),
      Nonempty (CurrentCyclicOuterBAW.CoherentMatchedCondition
        (family.problem block) psi (W.relative.omega psi))

/-- Preserve the published bijection and its equivariance exactly. Only the
reference quotient and coefficient identifications use the separate source. -/
def ClosedSingleBlockCompatibilitySource.coherent (source : ClosedSingleBlockCompatibilitySource)
    {ell : ℕ} (family : Definition35Family.{0} ell)
    (cover : EllPrimeCoverSource ell family.H) (coefficients : ClosedCoefficients family)
    (block : family.Block) (W : BlockWitness family cover block) :
    CoherentBlockWitness (family.problem block) where
  omega := W.relative.omega
  equivariant := W.relative.equivariant
  matched psi := source.normalize family cover coefficients block W psi

/-- The rank two principal seed for Type C over an algebraically closed
ordinary field. The central quotient, structural identities and character
triple hypotheses are fixed by the input. Li–Li supplies the quotient block
witness in this coefficient setting. No discrete valuation ring with this
ordinary field as its fraction field is assumed. -/
structure ClosedRankTwoPrincipalInputs (F : Type) [Field F] [Finite F]
    (P : Definition35Problem.{0})
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (semantics : FLZSourceSemantics P automorphisms) where
  primeTwo : P.p = 2
  fieldOdd : Odd (Nat.card F)
  notDvd : ¬ P.p ∣ Nat.card F
  divides : P.p ∣ Nat.card (PSp 2 F)
  upstairs : P.H ≃* Sp 2 F
  core_center : pCore P.p P.H = Subgroup.center P.H
  central : CentralReturnInputs P automorphisms semantics
  cover : EllPrimeCoverSource P.p central.downFamily.H
  coordinates : CoverCoordinates P.p F cover
  quotient_coordinates : ∀ h : P.H,
    coordinates.simpleEquiv (cover.quotient (QuotientGroup.mk' (pCore P.p P.H) h)) =
      spProjection 2 F (upstairs h)
  coefficients : ClosedCoefficients central.downFamily
  liLi : ClosedSource
  compatibility : ClosedSingleBlockCompatibilitySource

namespace ClosedRankTwoPrincipalInputs

variable {F : Type} [Field F] [Finite F] {P : Definition35Problem.{0}}
variable {automorphisms : Definition35AutomorphismStabilizerAdapter P}
variable {semantics : FLZSourceSemantics P automorphisms}

/-- The principal seed follows from Li–Li downstairs and the already proved
central lift on that exact witness. No Feng–Malle assumption is used. -/
def seed (D : ClosedRankTwoPrincipalInputs F P automorphisms semantics) :
    Definition35IBAWBijection P automorphisms semantics :=
  D.central.toDefinition35
    (D.compatibility.coherent D.central.downFamily D.cover D.coefficients D.central.downBlock
      (Classical.choice (D.liLi.blockwise P.p F D.central.downFamily D.cover D.coordinates
        D.coefficients
        (by
          letI := D.central.quotientFintype
          letI := D.central.downBlockFintype
          exact CurrentFiniteSplittingFamily.primitiveFamily_automorphisms
            D.central.iotaDown D.central.hinjDown D.central.downBlocks
            P.iota.prime D.central.physicalDown)
        D.fieldOdd D.notDvd D.divides D.central.downBlock)))

end ClosedRankTwoPrincipalInputs

end ManuscriptIBAW.TypeC.LiLiSource

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
