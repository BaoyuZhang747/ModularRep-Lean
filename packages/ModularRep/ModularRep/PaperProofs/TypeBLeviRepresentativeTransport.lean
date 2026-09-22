import ModularRep.PaperProofs.TypeBCharacteristicTwoConstituentSource
import ModularRep.NavarroBrauerRestrictionCovering

/-!
# One conjugating element for the prescribed Levi representative

Supporting deduction for the actual Levi representative window, canonical
`03b-type-b.tex` SHA256 9FEDDE026114148802FA26D24D8DB73C335846622C5297EE3B9FBE868FA806B9,
lines 910--947. Gamma is the actual paired rational Levi, H its literal L
subgroup and N its literal L0 subgroup. The root's final application supplies
their canonical original-carrier root transports.

The input P is the prescribed Gamma-orbit of psi0, already contained in the
specified series. An element theta of the orbit of an actual restriction
constituent theta0 determines ONE y; psi is defined using that SAME y.
Orbit membership, series membership and restriction naturality are deductions.
No selected representative, extension or stabilizer conclusion is a source.

The only extra source here is the fixed H/(N subgroupOf H), root and catalogue
instance of Navarro (9.2)/(9.5), pp.194 and 196: actual restriction occurrence
implies the supported-centre covering equation for the actual character blocks.
Normality, coherent roots, the coefficient field scope, and the specified
catalogues remain explicit. This standard one-way E1 source is independent of
P, psi0, theta0, theta and y. No full generic representation theory is rebuilt.
This helper has no standalone manuscript-window acceptance credit.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeTransport

open ModularRep FDRepSimpleClassKZero
open TypeBCharacteristicTwoConstituentSource TypeBLemma47LeviApplication

universe u

variable {Gamma k K : Type u} [Group Gamma] [Finite Gamma]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (H N : Subgroup Gamma) [H.Normal] [N.Normal] (hNH : N ≤ H)
variable (iotaH : PrimeRegularRootEmbedding 2 k K H)
variable (iotaN : PrimeRegularRootEmbedding 2 k K N)

noncomputable local instance finiteH : Fintype H := Fintype.ofFinite H
noncomputable local instance finiteNInH : Fintype (N.subgroupOf H) :=
  Fintype.ofFinite (N.subgroupOf H)

variable {BlockH BlockN : Type u} [Fintype BlockH] [Fintype BlockN]
variable {idempotentH : BlockH → k[H]}
variable {idempotentN : BlockN → k[N.subgroupOf H]}
variable (blocksH : BlockIdempotentDecomposition idempotentH)
variable (blocksN : BlockIdempotentDecomposition idempotentN)
variable (hinjH : IrreducibleBrauerCharacterInjectivity iotaH)
variable (hinjN : IrreducibleBrauerCharacterInjectivity (embeddedRoot H N hNH iotaN))
variable (catalogueH : BlockCentralCharacterCatalogue blocksH)
variable (catalogueN : BlockCentralCharacterCatalogue blocksN)

/-- The fixed literal instance of the standard restriction-covering source.
The guarded source says nothing about an orbit, chosen y or representative.
The base character and root use the value-preserving canonical subgroup copy. -/
def FixedRestrictionCovering
    (_roots : RootAgreement H N iotaH iotaN)
    (_fieldScope : SpathCoefficientField 2 k iotaH.prime) : Prop :=
  ∀ (psi : IBr iotaH) (theta : IBr iotaN),
    Occurs H N hNH iotaH iotaN psi theta →
      CentralCharacterCovers (N.subgroupOf H)
        (catalogueH.centralCharacter
          (irreducibleBrauerCharacterBlock iotaH hinjH blocksH psi))
        (catalogueN.centralCharacter
          (irreducibleBrauerCharacterBlock (embeddedRoot H N hNH iotaN)
            hinjN blocksN (embeddedCharacter H N hNH iotaN theta)))

local instance ambientH : MulAction Gamma (IBr iotaH) := ambientBrauerAction H iotaH
local instance ambientN : MulAction Gamma (IBr iotaN) := ambientBrauerAction N iotaN

/-- Transport the prescribed representative with the SAME y that transports
its restriction constituent. Covering concerns the resulting two blocks;
neither block is asserted to be unchanged by y. -/
theorem transport_prescribed_representative
    (roots : RootAgreement H N iotaH iotaN)
    (fieldScope : SpathCoefficientField 2 k iotaH.prime)
    (navarro : FixedRestrictionCovering H N hNH iotaH iotaN
      blocksH blocksN hinjH hinjN catalogueH catalogueN roots fieldScope)
    (P series : Set (IBr iotaH)) (psi0 : IBr iotaH)
    (prescribedOrbit : P = MulAction.orbit Gamma psi0)
    (orbitInSeries : P ⊆ series)
    (theta0 theta : IBr iotaN)
    (occurs0 : Occurs H N hNH iotaH iotaN psi0 theta0)
    (selectedInOrbit : theta ∈ MulAction.orbit Gamma theta0) :
    ∃ (y : Gamma) (psi : IBr iotaH),
      psi = y • psi0 ∧ theta = y • theta0 ∧
      psi ∈ P ∧ psi ∈ series ∧
      Occurs H N hNH iotaH iotaN psi theta ∧
      CentralCharacterCovers (N.subgroupOf H)
        (catalogueH.centralCharacter
          (irreducibleBrauerCharacterBlock iotaH hinjH blocksH psi))
        (catalogueN.centralCharacter
          (irreducibleBrauerCharacterBlock (embeddedRoot H N hNH iotaN)
            hinjN blocksN (embeddedCharacter H N hNH iotaN theta))) := by
  obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.mp selectedInOrbit
  have inP : y • psi0 ∈ P := by
    rw [prescribedOrbit]
    exact MulAction.mem_orbit psi0 y
  have occurs : Occurs H N hNH iotaH iotaN (y • psi0) theta := by
    rw [← hy]
    exact occurs_ambient H N hNH iotaH iotaN y psi0 theta0 occurs0
  exact ⟨y, y • psi0, rfl, hy.symm, inP, orbitInSeries inP, occurs,
    navarro (y • psi0) theta occurs⟩

end ModularRep.PaperProofs.TypeBLeviRepresentativeTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
