import ModularRep.PaperProofs.TypeBLeviRepresentativeTransport
import ModularRep.PaperProofs.TypeBLeviRepresentativeClifford
import ModularRep.PaperProofs.TypeBLeviRepresentativeField

/-!
# Construction after the actual component representative has been constructed

Supporting integration for canonical `03b-type-b.tex`, SHA256
63DEDB23B79FC017A4BB9AE563039415332A7349C0B563D6383B1F47BD096200,
lines 929--992, using the direct Gallagher lemma at lines 383--422.
The historical 9FED manuscript's lines 910--980 used an effective-exponent
input; that uncompiled construction freeze is retained in the audit history.
Gamma, H and N are the SAME actual rational paired Levi,
L and L0 carriers as in the three imported helpers. The selected series is
the literal union of the displayed blocks under the actual character-block
map; no arbitrary series-membership oracle is introduced.

This helper is called AFTER the component argument constructs theta in the
Gamma-orbit of theta0, fixed by that orbit's field stabilizer. Those two
theta facts, normality and quotient commutativity are internal K inputs
from the final specified application. They must
not be moved into its external source packet. Evaluated inertia roots and
the Navarro 8.9 instance belong to this SAME theta.

The source inputs are exactly the previously designated fixed restriction
covering theorem, GM multiplicity-free restriction, the uniform finite group
above/homogeneous Clifford principles, and Navarro 8.7/8.9/8.20/8.12 together
with the retained common-root guards. In particular there is no
source assumption supplying an ambient inertia extension, local or full
psi factorization, field-fixer equality, or honest psi extension.

Lean identifies the two EO carriers by actual orbit equality, uses ONE y to
transport both psi0 and theta0, derives theta's local factorization from its
constructed fixation, and applies the derived characteristic-two argument.
It then promotes to the full field and supplies an honest irreducible
representation on literal H semidirect E_psi with the original-root psi.
This integration helper is not a standalone accepted manuscript window;
the final specified endpoint must construct its internal inputs.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeAssembly

open ModularRep FDRepSimpleClassKZero
open TypeBLemma47LeviApplication TypeBCharacteristicTwoConstituentSource
open TypeBCharacteristicTwoCorrespondenceSource TypeBCharacteristicTwoExtensionCarriers
open TypeBCharacteristicTwoCliffordKernel TypeBCharacteristicTwoCliffordApplication
open TypeBCharacteristicTwoGallagherSource TypeBCharacteristicTwoGallagherProduct
open TypeBLeviRepresentativeTransport TypeBLeviRepresentativeClifford
open TypeBLeviRepresentativeField

universe u

variable {Gamma E k K : Type u} [Group Gamma] [Finite Gamma]
variable [Group E] [Finite E] [IsCyclic E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (H N : Subgroup Gamma) [H.Normal] [N.Normal]
variable [IsMulCommutative (Gamma ⧸ N)] (hNH : N ≤ H)
variable (iotaGamma : PrimeRegularRootEmbedding 2 k K Gamma)
variable (iotaH : PrimeRegularRootEmbedding 2 k K H)
variable (iotaN : PrimeRegularRootEmbedding 2 k K N)
variable (field : E →* MulAut Gamma)
variable (hH : ∀ e : E, ∀ g : Gamma, g ∈ H ↔ field e g ∈ H)
variable (hN : ∀ e : E, ∀ g : Gamma, g ∈ N ↔ field e g ∈ N)

noncomputable local instance finiteH : Fintype H := Fintype.ofFinite H
noncomputable local instance finiteNInH : Fintype (N.subgroupOf H) :=
  Fintype.ofFinite (N.subgroupOf H)

local instance ambientH : MulAction Gamma (IBr iotaH) := ambientBrauerAction H iotaH
local instance ambientN : MulAction Gamma (IBr iotaN) := ambientBrauerAction N iotaN

/-- Actual orbit membership identifies the two setwise field stabilizers.
This transports EO(theta0), retained by Components, to EO(theta), used by
the Clifford and promotion steps, inside the SAME original field group. -/
theorem orbit_field_stabilizer_eq
    (theta0 theta : IBr iotaN)
    (selectedInOrbit : theta ∈ MulAction.orbit Gamma theta0) :
    orbitFieldStabilizer N iotaN field hN theta =
      orbitFieldStabilizer N iotaN field hN theta0 := by
  have horbit : MulAction.orbit Gamma theta = MulAction.orbit Gamma theta0 :=
    MulAction.orbit_eq_iff.mpr selectedInOrbit
  unfold orbitFieldStabilizer TypeBComponentReturnCarrierTransport.orbitStabilizer
  rw [horbit]

variable {BlockH BlockN : Type u} [Fintype BlockH] [Fintype BlockN]
variable {idempotentH : BlockH → k[H]}
variable {idempotentN : BlockN → k[N.subgroupOf H]}
variable (blocksH : BlockIdempotentDecomposition idempotentH)
variable (blocksN : BlockIdempotentDecomposition idempotentN)
variable (hinjH : IrreducibleBrauerCharacterInjectivity iotaH)
variable (hinjN : IrreducibleBrauerCharacterInjectivity (embeddedRoot H N hNH iotaN))
variable (catalogueH : BlockCentralCharacterCatalogue blocksH)
variable (catalogueN : BlockCentralCharacterCatalogue blocksN)

/-- The SAME transported character supplies the prescribed orbit and
actual block-union memberships, literal constituent and covering equation,
full semidirect stabilizer factorization, field-fixer image equality inside
the original E, and honest original-root semidirect extension.

The theta choice/fixation and subgroup-chain facts are already constructed
internal results. The final specified theorem must derive them before this
helper is invoked; they are not external character-theoretic sources. -/
theorem assemble_prescribed_representative
    (roots_N_H : RootAgreement H N iotaH iotaN)
    (fieldScope : SpathCoefficientField 2 k iotaH.prime)
    (covering : FixedRestrictionCovering H N hNH iotaH iotaN
      blocksH blocksN hinjH hinjN catalogueH catalogueN roots_N_H fieldScope)
    (seriesBlocks : Set BlockH) (P : Set (IBr iotaH)) (psi0 : IBr iotaH)
    (prescribedOrbit : P = MulAction.orbit Gamma psi0)
    (orbitInSeries : ∀ psi ∈ P,
      irreducibleBrauerCharacterBlock iotaH hinjH blocksH psi ∈ seriesBlocks)
    (theta0 theta : IBr iotaN)
    (occurs0 : Occurs H N hNH iotaH iotaN psi0 theta0)
    (selectedInOrbit : theta ∈ MulAction.orbit Gamma theta0)
    (selectedFixed :
      letI := fieldBrauerAction N iotaN field hN;
      ∀ e : orbitFieldStabilizer N iotaN field hN theta0,
      (e : E) • theta = theta)
    (iotaI : PrimeRegularRootEmbedding 2 k K (BrauerInertia H N iotaN theta))
    (iotaA : PrimeRegularRootEmbedding 2 k K (AmbientInertia N iotaN theta))
    (roots_N_G : RootsAgree iotaGamma iotaN)
    (roots_A_G : RootsAgree iotaGamma iotaA)
    (roots_N_A : RootsAgree iotaA iotaN)
    (roots_I_A : RootsAgree iotaA iotaI)
    (multiplicityFree : MultiplicityFreeRestriction N iotaGamma iotaN)
    (above : ExistsAbovePrinciple k K)
    (homogeneousClifford : HomogeneousCliffordPrinciple k K)
    (source87 : Navarro87Principle k K)
    (source89 : Navarro89Source H N hNH iotaH iotaN theta iotaI)
    (source820 : Navarro820AbelianProductPrinciple k K)
    (source812 : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k) :
    letI := fieldBrauerAction H iotaH field hH;
    ∃ (y : Gamma) (psi : IBr iotaH),
      psi = y • psi0 ∧ theta = y • theta0 ∧
      psi ∈ P ∧
      irreducibleBrauerCharacterBlock iotaH hinjH blocksH psi ∈ seriesBlocks ∧
      Occurs H N hNH iotaH iotaN psi theta ∧
      CentralCharacterCovers (N.subgroupOf H)
        (catalogueH.centralCharacter
          (irreducibleBrauerCharacterBlock iotaH hinjH blocksH psi))
        (catalogueN.centralCharacter
          (irreducibleBrauerCharacterBlock (embeddedRoot H N hNH iotaN)
            hinjN blocksN (embeddedCharacter H N hNH iotaN theta))) ∧
      Formalisation.SemidirectStabilizerFactors field
        (field_ambient_semidirect_compatible H iotaH field hH) psi ∧
      (fieldStabilizer iotaH
        ((restrictAutomorphismHom H field hH).comp
          (orbitFieldStabilizer N iotaN field hN theta0).subtype) psi).map
          (orbitFieldStabilizer N iotaN field hN theta0).subtype =
        fieldStabilizer iotaH (restrictAutomorphismHom H field hH) psi ∧
      ∃ W : FDRep k H,
        Representation.IsIrreducible W.ρ ∧
        psi.1 = Representation.brauerCharacterOfRootEmbedding W.ρ iotaH ∧
        ∃ rho : Representation k
          (FieldSemidirect iotaH (restrictAutomorphismHom H field hH) psi) W,
          Representation.IsIrreducible rho ∧
          Nonempty (Representation.Equiv
            (rho.pullback (SemidirectProduct.inl : H →*
              FieldSemidirect iotaH (restrictAutomorphismHom H field hH) psi))
            W.ρ) := by
  letI := fieldBrauerAction H iotaH field hH
  letI := fieldBrauerAction N iotaN field hN
  have hEO := orbit_field_stabilizer_eq N iotaN field hN
    theta0 theta selectedInOrbit
  let EO := orbitFieldStabilizer N iotaN field hN theta
  let fieldO : EO →* MulAut Gamma := field.comp EO.subtype
  have hHO : ∀ e : EO, ∀ g : Gamma, g ∈ H ↔ fieldO e g ∈ H :=
    fun e g => hH e.1 g
  have hNO : ∀ e : EO, ∀ g : Gamma, g ∈ N ↔ fieldO e g ∈ N :=
    fun e g => hN e.1 g
  have hthetaFixed : ∀ e : EO, (e : E) • theta = theta := by
    intro e
    have he : e.1 ∈ orbitFieldStabilizer N iotaN field hN theta0 := by
      rw [← hEO]
      exact e.2
    exact selectedFixed ⟨e.1, he⟩
  have hthetaFactorization :
      letI := ambientBrauerAction N iotaN;
      letI := fieldBrauerAction N iotaN fieldO hNO;
      Formalisation.SemidirectStabilizerFactors fieldO
        (field_ambient_semidirect_compatible N iotaN fieldO hNO) theta := by
    letI := fieldBrauerAction N iotaN fieldO hNO
    intro x
    change x.left • ((x.right : E) • theta) = theta ↔
      x.left • theta = theta ∧ (x.right : E) • theta = theta
    rw [hthetaFixed x.right]
    simp only [eq_self_iff_true, and_true]
  let series : Set (IBr iotaH) :=
    {psi | irreducibleBrauerCharacterBlock iotaH hinjH blocksH psi ∈ seriesBlocks}
  obtain ⟨y, psi, hpsi, htheta, hinP, hinSeries, hoccurs, hcovers⟩ :=
    transport_prescribed_representative H N hNH iotaH iotaN
      blocksH blocksN hinjH hinjN catalogueH catalogueN roots_N_H fieldScope
      covering P series psi0 prescribedOrbit orbitInSeries
      theta0 theta occurs0 selectedInOrbit
  have hlocal := representative_characteristic_two_clifford (E := EO)
    H N hNH iotaGamma iotaH iotaN psi theta hoccurs iotaI iotaA
    roots_N_G roots_A_G multiplicityFree above homogeneousClifford
    source87 source89 source820 roots_N_A roots_I_A
    fieldO hHO hNO hthetaFactorization
  have hlocalPointwise : ∀ a : Gamma, ∀ e : EO,
      a • ((e : E) • psi) = psi ↔ a • psi = psi ∧ (e : E) • psi = psi := by
    intro a e
    exact hlocal (⟨a, e⟩ : Gamma ⋊[fieldO] EO)
  have hfull := full_field_factorization H N hNH iotaH iotaN field hH hN
    roots_N_H source87 psi theta hoccurs hlocalPointwise
  have himage := local_field_stabilizer_image H N hNH iotaH iotaN field hH hN
    roots_N_H source87 psi theta hoccurs
  rw [hEO] at himage
  exact ⟨y, psi, hpsi, htheta, hinP, hinSeries, hoccurs, hcovers, hfull, himage,
    honest_field_extension iotaH (restrictAutomorphismHom H field hH) source812 psi⟩

end ModularRep.PaperProofs.TypeBLeviRepresentativeAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
