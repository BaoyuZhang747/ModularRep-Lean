import ModularRep.IBrBlockEquivTransport

/-!
# Irreducible Brauer characters across a central prime-to-characteristic quotient

This source-neutral module isolates the character-carrier part of transport
through a central quotient.  Pullback along the quotient map constructs an
irreducible Brauer character upstairs.  Conversely, if the central subgroup
has trivial central character on an irreducible representation, that
representation factors through the quotient by `QuotientGroup.lift`.

Only two pieces of root/regular-element realisation data are exposed:

* the chosen root lifts agree on the roots used on the quotient; and
* every prime regular quotient element has a prime regular lift.

For a central `p'`-subgroup the second statement is the standard elementary
prime regular lifting fact.  Neither field chooses a Brauer character or
states surjectivity onto a character fibre.  The equivalence with the trivial
block-central character fibre is constructed below.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport

open ModularRep.FDRepSimpleClassKZero

universe u

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]

/-! ## Narrow quotient-realisation source -/

/-- Root and regular-element compatibility for a fixed quotient map.

The first field concerns only roots of unity occurring for the quotient
group.  The second is group-theoretic and contains no character data.  In the
intended application it follows from the standard prime regular-part argument
for a quotient by a central `p'`-subgroup. -/
structure QuotientRealisationSource
    (Z : Subgroup G) [Z.Normal]
    (coverIota : PrimeRegularRootEmbedding p k K G)
    (quotientIota : PrimeRegularRootEmbedding p k K (G ⧸ Z)) : Prop where
  root_lift_agrees :
    ∀ zeta : rootsOfUnity (primeRegularExponent p (G ⧸ Z)) k,
      coverIota.lift (((zeta : kˣ) : k)) =
        quotientIota.lift (((zeta : kˣ) : k))
  primeRegular_surjective :
    Function.Surjective
      (PrimeRegularElement.map (p := p) (QuotientGroup.mk' Z))

variable {Z : Subgroup G} [Z.Normal]

noncomputable local instance subgroupFintype : Fintype Z :=
  Fintype.ofFinite Z

variable (coverIota : PrimeRegularRootEmbedding p k K G)
variable (quotientIota : PrimeRegularRootEmbedding p k K (G ⧸ Z))
variable (source : QuotientRealisationSource Z coverIota quotientIota)

include source in
/-- The root source gives exactly the representation-specific compatibility
required by `BrauerCharacterHomPullback`. -/
theorem QuotientRealisationSource.compatibleAlong
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k (G ⧸ Z) V) :
    Representation.BrauerRootLiftCompatibleAlong rho quotientIota coverIota
      (QuotientGroup.mk' Z) := by
  intro g a
  let gbar : PrimeRegularElement (G := G ⧸ Z) p :=
    PrimeRegularElement.map (QuotientGroup.mk' Z) g
  let abar : {a : k // a ∈ (rho gbar.1).charpoly.roots} := a
  let zeta : rootsOfUnity (primeRegularExponent p (G ⧸ Z)) k :=
    rho.charpolyRootAsRootOfUnity quotientIota gbar abar
  have hzeta : (((zeta : kˣ) : k)) = a.1 :=
    Representation.coe_charpolyRootAsRootOfUnity
      rho quotientIota gbar abar
  calc
    coverIota.lift a.1 = coverIota.lift (((zeta : kˣ) : k)) :=
      congrArg coverIota.lift hzeta.symm
    _ = quotientIota.lift (((zeta : kˣ) : k)) :=
      source.root_lift_agrees zeta
    _ = quotientIota.lift a.1 := congrArg quotientIota.lift hzeta

include source in
/-- Surjectivity on prime regular elements makes pullback injective on all
prime regular class functions. -/
theorem QuotientRealisationSource.pullback_injective :
    Function.Injective
      (fun chi : PrimeRegularClassFunction K (G ⧸ Z) p ↦
        PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) chi) := by
  intro chi psi h
  apply PrimeRegularClassFunction.ext
  intro y
  obtain ⟨x, hx⟩ := source.primeRegular_surjective y
  have heval := congrArg
    (fun f : PrimeRegularClassFunction K G p ↦ f x) h
  change chi (PrimeRegularElement.map (QuotientGroup.mk' Z) x) =
    psi (PrimeRegularElement.map (QuotientGroup.mk' Z) x) at heval
  simpa only [hx] using heval

/-! ## Chosen affording representations -/

/-- Select the irreducible finite-dimensional representation already stored
in an `IBr` witness.  This is choice from the definition of `IBr`, not an
external source. -/
def affordingRepresentation
    {H : Type u} [Group H] [Finite H]
    (iota : PrimeRegularRootEmbedding p k K H) (phi : IBr iota) :
    FDRep k H :=
  Classical.choose phi.2

/-- The selected representation is irreducible. -/
theorem affordingRepresentation_irreducible
    {H : Type u} [Group H] [Finite H]
    (iota : PrimeRegularRootEmbedding p k K H) (phi : IBr iota) :
    Representation.IsIrreducible (affordingRepresentation iota phi).ρ :=
  (Classical.choose_spec phi.2).1

/-- The selected representation affords the original literal class
function. -/
theorem affordingRepresentation_character
    {H : Type u} [Group H] [Finite H]
    (iota : PrimeRegularRootEmbedding p k K H) (phi : IBr iota) :
    phi.1 = Representation.brauerCharacterOfRootEmbedding
      (affordingRepresentation iota phi).ρ iota :=
  (Classical.choose_spec phi.2).2

/-! ## The block-central character fibre -/

variable {BlockIndex : Type u} [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[G]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (coverHinj : IrreducibleBrauerCharacterInjectivity coverIota)
variable (hZ : Z ≤ Subgroup.center G)
variable [Invertible (Fintype.card Z : k)]

include blocks coverHinj hZ in
/-- The central character of the block containing a literal irreducible
Brauer character, restricted to the nominated central subgroup. -/
def blockCentralCharacter (phi : IBr coverIota) : Z →* kˣ :=
  blocks.centralCharacterSector Z hZ
    (irreducibleBrauerCharacterBlock coverIota coverHinj blocks phi)

/-- The literal fibre on which the nominated central subgroup has trivial
block central character. -/
abbrev TrivialCentralCharacterFibre :=
  {phi : IBr coverIota //
    blockCentralCharacter coverIota blocks coverHinj hZ phi = 1}

/-- The block central character of an `IBr` element is the central character
of any irreducible representation affording that element.

The proof uses character injectivity only to identify the simple-module label
used by the block assignment with the label of the supplied representation.
-/
theorem blockCentralCharacter_eq_of_affords
    (phi : IBr coverIota) (V : FDRep k G)
    [hV : Representation.IsIrreducible V.ρ]
    (hcharacter : phi.1 =
      Representation.brauerCharacterOfRootEmbedding V.ρ coverIota) :
    blockCentralCharacter coverIota blocks coverHinj hZ phi =
      Representation.centralCharacter V.ρ Z hZ := by
  letI : IsSimpleModule k[G] (Representation.asModule V.ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hV
  let Y : SimpleModuleClass k[G] :=
    simpleClassOfIrreducibleFDRep V hV
  have hYphi : simpleClassToIBr coverIota Y = phi := by
    apply Subtype.ext
    change Representation.brauerCharacterOfRootEmbedding
        (simpleClassFDRep Y).ρ coverIota = phi.1
    calc
      Representation.brauerCharacterOfRootEmbedding
          (simpleClassFDRep Y).ρ coverIota =
        Representation.brauerCharacterOfRootEmbedding V.ρ coverIota :=
          Representation.brauerCharacterOfRootEmbedding_iso coverIota
            (simpleClassOfIrreducibleFDRepIso V hV)
      _ = phi.1 := hcharacter.symm
  have hlabel :
      (simpleModuleClassEquivIBr coverIota coverHinj).symm phi = Y := by
    apply (simpleModuleClassEquivIBr coverIota coverHinj).injective
    rw [Equiv.apply_symm_apply]
    simpa only [simpleModuleClassEquivIBr_apply] using hYphi.symm
  have hblock :
      irreducibleBrauerCharacterBlock coverIota coverHinj blocks phi =
        blocks.moduleBlock (V := Representation.asModule V.ρ) := by
    unfold irreducibleBrauerCharacterBlock
    rw [hlabel]
    exact simpleModuleClassBlock_simpleClassOfIrreducibleFDRep blocks V hV
  unfold blockCentralCharacter
  rw [hblock]
  exact Representation.moduleBlockSector_eq_centralCharacter V.ρ blocks Z hZ

/-! ## Representation factorisation -/

/-- Factor a representation through the quotient once the nominated
subgroup lies in its kernel. -/
def factorRepresentation
    {V : Type u} [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (hkernel : Z ≤ rho.ker) :
    Representation k (G ⧸ Z) V :=
  QuotientGroup.lift Z rho hkernel

@[simp]
theorem factorRepresentation_apply_mk
    {V : Type u} [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (hkernel : Z ≤ rho.ker) (g : G) :
    factorRepresentation (Z := Z) rho hkernel
        (QuotientGroup.mk' Z g) = rho g :=
  QuotientGroup.lift_mk' Z hkernel g

@[simp]
theorem factorRepresentation_pullback
    {V : Type u} [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (hkernel : Z ≤ rho.ker) :
    (factorRepresentation (Z := Z) rho hkernel).pullback
        (QuotientGroup.mk' Z) =
      rho :=
  QuotientGroup.lift_comp_mk' Z rho hkernel

/-- Factorisation through a surjective quotient preserves irreducibility. -/
theorem factorRepresentation_irreducible
    {V : Type u} [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (hkernel : Z ≤ rho.ker)
    (hirreducible : Representation.IsIrreducible rho) :
    Representation.IsIrreducible
      (factorRepresentation (Z := Z) rho hkernel) := by
  apply (Representation.isIrreducible_pullback_iff
    (factorRepresentation (Z := Z) rho hkernel) (QuotientGroup.mk' Z)
    (QuotientGroup.mk'_surjective Z)).mp
  rw [factorRepresentation_pullback]
  exact hirreducible

/-- A trivial central character puts the central subgroup in the
representation kernel. -/
theorem le_ker_of_centralCharacter_eq_one
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V) [hirreducible : Representation.IsIrreducible rho]
    (hcentral : Representation.centralCharacter rho Z hZ = 1) :
    Z ≤ rho.ker := by
  intro z hz
  change rho z = LinearMap.id
  have hspec := Representation.centralCharacter_spec rho Z hZ ⟨z, hz⟩
  rw [hcentral] at hspec
  simpa [Module.End.one_eq_id] using hspec

/-! A kernel criterion in the reverse direction. -/

/-- An irreducible representation on which the nominated central subgroup
acts trivially has trivial central character. -/
theorem centralCharacter_eq_one_of_le_ker
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V)
    [hirreducible : Representation.IsIrreducible rho]
    (hkernel : Z ≤ rho.ker) :
    Representation.centralCharacter rho Z hZ = 1 := by
  have hone : ∀ z : Z,
      rho (z : G) =
        (((1 : Z →* kˣ) z : k)) • LinearMap.id := by
    intro z
    have hz : rho (z : G) = 1 := hkernel z.property
    rw [hz]
    simp [Module.End.one_eq_id]
  have hunique :=
    (Representation.existsUnique_centralCharacter rho Z hZ).unique hone
      (Representation.centralCharacter_spec rho Z hZ)
  exact hunique.symm

/-! ## Inflation, deflation, and the fibre equivalence -/

include source in
/-- Inflate an actual quotient `IBr` element.  Irreducibility is a kernel
consequence of surjectivity of the quotient map; the root source supplies
only the character-function comparison. -/
def inflateIBr (phi : IBr quotientIota) : IBr coverIota := by
  let V := affordingRepresentation quotientIota phi
  let rho := Representation.pullback V.ρ (QuotientGroup.mk' Z)
  have hV : Representation.IsIrreducible V.ρ :=
    affordingRepresentation_irreducible quotientIota phi
  have hrho : Representation.IsIrreducible rho :=
    hV.pullback (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  refine ⟨PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) phi.1,
    ⟨FDRep.of rho, hrho, ?_⟩⟩
  change PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) phi.1 =
    Representation.brauerCharacterOfRootEmbedding rho coverIota
  calc
    PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) phi.1 =
        PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z)
          (Representation.brauerCharacterOfRootEmbedding V.ρ quotientIota) :=
      congrArg (PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z))
        (affordingRepresentation_character quotientIota phi)
    _ = Representation.brauerCharacterOfRootEmbedding rho coverIota :=
      (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
        V.ρ quotientIota coverIota (QuotientGroup.mk' Z)
          (QuotientRealisationSource.compatibleAlong
            coverIota quotientIota source V.ρ)).symm

@[simp]
theorem inflateIBr_val (phi : IBr quotientIota) :
    (inflateIBr coverIota quotientIota source phi).1 =
      PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) phi.1 :=
  rfl

/-- Inflation is injective before any block or central-sector restriction. -/
theorem inflateIBr_injective :
    Function.Injective (inflateIBr coverIota quotientIota source) := by
  intro phi psi h
  apply Subtype.ext
  apply QuotientRealisationSource.pullback_injective
    coverIota quotientIota source
  simpa only [inflateIBr_val] using congrArg Subtype.val h

include source in
/-- Inflated quotient characters land in the literal trivial
block-central character fibre. -/
def inflateToTrivialFibre (phi : IBr quotientIota) :
    TrivialCentralCharacterFibre coverIota blocks coverHinj hZ := by
  let V := affordingRepresentation quotientIota phi
  let rho := Representation.pullback V.ρ (QuotientGroup.mk' Z)
  have hV : Representation.IsIrreducible V.ρ :=
    affordingRepresentation_irreducible quotientIota phi
  have hrho : Representation.IsIrreducible rho :=
    hV.pullback (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  letI : Representation.IsIrreducible V.ρ := hV
  letI : Representation.IsIrreducible rho := hrho
  letI : Representation.IsIrreducible (FDRep.of rho).ρ := by
    simpa only [FDRep.of_ρ'] using hrho
  refine ⟨inflateIBr coverIota quotientIota source phi, ?_⟩
  have hcharacter :
      (inflateIBr coverIota quotientIota source phi).1 =
        Representation.brauerCharacterOfRootEmbedding (FDRep.of rho).ρ
          coverIota := by
    change PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) phi.1 =
      Representation.brauerCharacterOfRootEmbedding rho coverIota
    calc
      PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) phi.1 =
          PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z)
            (Representation.brauerCharacterOfRootEmbedding V.ρ
              quotientIota) :=
        congrArg (PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z))
          (affordingRepresentation_character quotientIota phi)
      _ = Representation.brauerCharacterOfRootEmbedding rho coverIota :=
        (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
          V.ρ quotientIota coverIota (QuotientGroup.mk' Z)
            (QuotientRealisationSource.compatibleAlong
              coverIota quotientIota source V.ρ)).symm
  calc
    blockCentralCharacter coverIota blocks coverHinj hZ
        (inflateIBr coverIota quotientIota source phi) =
      Representation.centralCharacter rho Z hZ :=
        blockCentralCharacter_eq_of_affords coverIota blocks coverHinj hZ
          (inflateIBr coverIota quotientIota source phi) (FDRep.of rho)
          hcharacter
    _ = 1 := by
      apply centralCharacter_eq_one_of_le_ker (Z := Z) hZ rho
      intro z hz
      change V.ρ (QuotientGroup.mk' Z z) = LinearMap.id
      have hzq : QuotientGroup.mk' Z z = 1 :=
        (QuotientGroup.eq_one_iff z).mpr hz
      rw [hzq]
      simp [Module.End.one_eq_id]

/-- Deflate a trivial-sector character by factoring its chosen affording
representation through the quotient.  No quotient character is supplied as
source data. -/
def deflateIBr
    (phi : TrivialCentralCharacterFibre coverIota blocks coverHinj hZ) :
    IBr quotientIota := by
  let V := affordingRepresentation coverIota phi.1
  have hV : Representation.IsIrreducible V.ρ :=
    affordingRepresentation_irreducible coverIota phi.1
  letI : Representation.IsIrreducible V.ρ := hV
  have hcentral : Representation.centralCharacter V.ρ Z hZ = 1 := by
    calc
      Representation.centralCharacter V.ρ Z hZ =
          blockCentralCharacter coverIota blocks coverHinj hZ phi.1 :=
        (blockCentralCharacter_eq_of_affords coverIota blocks coverHinj hZ
          phi.1 V
          (affordingRepresentation_character coverIota phi.1)).symm
      _ = 1 := phi.2
  let hkernel : Z ≤ V.ρ.ker :=
    le_ker_of_centralCharacter_eq_one (Z := Z) hZ V.ρ hcentral
  let rhoBar := factorRepresentation (Z := Z) V.ρ hkernel
  have hrhoBar : Representation.IsIrreducible rhoBar :=
    factorRepresentation_irreducible (Z := Z) V.ρ hkernel hV
  exact ⟨Representation.brauerCharacterOfRootEmbedding rhoBar quotientIota,
    ⟨FDRep.of rhoBar, hrhoBar, rfl⟩⟩

/-- Deflation is a right inverse to inflation on the trivial fibre.  This is
the kernel-checked representation-factorisation step that removes the former
surjectivity/factorisation source premise. -/
theorem inflate_deflate
    (phi : TrivialCentralCharacterFibre coverIota blocks coverHinj hZ) :
    inflateIBr coverIota quotientIota source
        (deflateIBr coverIota quotientIota blocks coverHinj hZ phi) =
      phi.1 := by
  let V := affordingRepresentation coverIota phi.1
  have hV : Representation.IsIrreducible V.ρ :=
    affordingRepresentation_irreducible coverIota phi.1
  letI : Representation.IsIrreducible V.ρ := hV
  have hcentral : Representation.centralCharacter V.ρ Z hZ = 1 := by
    calc
      Representation.centralCharacter V.ρ Z hZ =
          blockCentralCharacter coverIota blocks coverHinj hZ phi.1 :=
        (blockCentralCharacter_eq_of_affords coverIota blocks coverHinj hZ
          phi.1 V
          (affordingRepresentation_character coverIota phi.1)).symm
      _ = 1 := phi.2
  let hkernel : Z ≤ V.ρ.ker :=
    le_ker_of_centralCharacter_eq_one (Z := Z) hZ V.ρ hcentral
  let rhoBar := factorRepresentation (Z := Z) V.ρ hkernel
  apply Subtype.ext
  change PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z)
      (Representation.brauerCharacterOfRootEmbedding rhoBar quotientIota) =
    phi.1.1
  calc
    PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z)
        (Representation.brauerCharacterOfRootEmbedding rhoBar quotientIota) =
      Representation.brauerCharacterOfRootEmbedding
        (Representation.pullback rhoBar (QuotientGroup.mk' Z)) coverIota :=
      (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
        rhoBar quotientIota coverIota (QuotientGroup.mk' Z)
          (QuotientRealisationSource.compatibleAlong
            coverIota quotientIota source rhoBar)).symm
    _ = Representation.brauerCharacterOfRootEmbedding V.ρ coverIota := by
      rw [show Representation.pullback rhoBar (QuotientGroup.mk' Z) = V.ρ from
        factorRepresentation_pullback (Z := Z) V.ρ hkernel]
    _ = phi.1.1 :=
      (affordingRepresentation_character coverIota phi.1).symm

theorem inflateToTrivialFibre_injective :
    Function.Injective
      (inflateToTrivialFibre coverIota quotientIota source blocks coverHinj
        hZ) := by
  intro phi psi h
  apply inflateIBr_injective coverIota quotientIota source
  exact congrArg Subtype.val h

theorem inflateToTrivialFibre_surjective :
    Function.Surjective
      (inflateToTrivialFibre coverIota quotientIota source blocks coverHinj
        hZ) := by
  intro phi
  refine ⟨deflateIBr coverIota quotientIota blocks coverHinj hZ phi, ?_⟩
  apply Subtype.ext
  exact inflate_deflate coverIota quotientIota source blocks coverHinj hZ phi

/-- The quotient `IBr` carrier is equivalent to the literal trivial
block-central character fibre upstairs. -/
def quotientIBrEquivTrivialCentralCharacterFibre :
    IBr quotientIota ≃
      TrivialCentralCharacterFibre coverIota blocks coverHinj hZ :=
  Equiv.ofBijective
    (inflateToTrivialFibre coverIota quotientIota source blocks coverHinj hZ)
    ⟨inflateToTrivialFibre_injective coverIota quotientIota source blocks
        coverHinj hZ,
      inflateToTrivialFibre_surjective coverIota quotientIota source blocks
        coverHinj hZ⟩

end ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
