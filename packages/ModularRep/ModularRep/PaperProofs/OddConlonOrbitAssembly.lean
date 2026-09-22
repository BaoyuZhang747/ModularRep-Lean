import ModularRep.BlockFibreRestriction

/-!
# Construction from orbit representatives for manuscript Proposition 3.14

This file isolates the deduction in condition (ii) of the Brough--Späth
criterion used in Proposition 3.14.  On one representative of every block
orbit, Proposition 3.11 supplies a stabiliser-equivariant bijection from
Brauer characters to ordinary labels.  Li's cited parametrisation supplies
an equivariant, block-preserving bijection from ordinary labels to weights.
The results below transport the first family along the block orbits and
compose the two maps.

The acting group is abstract.  A concrete application must use the opposite
group, or the equivalent inverse action, to translate the manuscript's right
action into Lean's left `MulAction`.  In particular, this file does not
identify tensoring by a linear character with an automorphism of the finite
group.

No extension, block-induction, character-triple, inductive BAW, or iBAW
conclusion occurs in the statements below.
-/

namespace ModularRep.PaperProofs.OddConlonOrbitAssembly

open BlockFibreRestriction

noncomputable section

universe u

variable {A Block X Y Z : Type u}
variable [Group A]
variable [MulAction A Block]
variable [MulAction A X] [MulAction A Y] [MulAction A Z]

abbrev BlockOrbit (A Block : Type u) [Group A] [MulAction A Block] :=
  MulAction.orbitRel.Quotient A Block

/-- The representative selected by `Quotient.out` for a block orbit. -/
def orbitRepresentative (omega : BlockOrbit A Block) : Block :=
  omega.out

/-- An element carrying the selected representative of the orbit of `b` to
`b`.  Its existence is a consequence of the definition of an orbit. -/
def orbitTransporter (b : Block) : A := by
  let omega : BlockOrbit A Block := Quotient.mk'' b
  have hrep : orbitRepresentative omega ∈ MulAction.orbit A b := by
    change MulAction.orbitRel A Block (orbitRepresentative omega) b
    rw [← Quotient.eq'']
    simp [orbitRepresentative, omega, Quotient.out_eq' omega]
  have hb : b ∈ MulAction.orbit A (orbitRepresentative omega) :=
    MulAction.mem_orbit_symm.mp hrep
  exact Classical.choose hb

@[simp]
theorem orbitTransporter_smul_representative (b : Block) :
    orbitTransporter (A := A) b •
        orbitRepresentative (Quotient.mk'' b : BlockOrbit A Block) = b := by
  let omega : BlockOrbit A Block := Quotient.mk'' b
  have hrep : orbitRepresentative omega ∈ MulAction.orbit A b := by
    change MulAction.orbitRel A Block (orbitRepresentative omega) b
    rw [← Quotient.eq'']
    simp [orbitRepresentative, omega, Quotient.out_eq' omega]
  have hb : b ∈ MulAction.orbit A (orbitRepresentative omega) :=
    MulAction.mem_orbit_symm.mp hrep
  exact Classical.choose_spec hb

@[simp]
theorem blockOrbit_smul (a : A) (b : Block) :
    (Quotient.mk'' (a • b) : BlockOrbit A Block) = Quotient.mk'' b :=
  MulAction.orbitRel.Quotient.quotient_smul_eq

variable (blockX : X → Block) (blockY : Y → Block)
variable (hblockX : ∀ (a : A) (x : X), blockX (a • x) = a • blockX x)
variable (hblockY : ∀ (a : A) (y : Y), blockY (a • y) = a • blockY y)

/-- Transport a point in a block fibre back to the selected representative
of its block orbit. -/
def toRepresentativeX (x : X) :
    BlockFibre blockX
      (orbitRepresentative
        (Quotient.mk'' (blockX x) : BlockOrbit A Block)) := by
  let t := orbitTransporter (A := A) (blockX x)
  refine ⟨t⁻¹ • x, ?_⟩
  change blockX (t⁻¹ • x) =
    orbitRepresentative (Quotient.mk'' (blockX x) : BlockOrbit A Block)
  rw [hblockX]
  have ht := orbitTransporter_smul_representative (A := A) (blockX x)
  calc
    t⁻¹ • blockX x = t⁻¹ •
        (t • orbitRepresentative
          (Quotient.mk'' (blockX x) : BlockOrbit A Block)) := by
      rw [ht]
    _ = orbitRepresentative
          (Quotient.mk'' (blockX x) : BlockOrbit A Block) :=
      inv_smul_smul t _

/-- The analogous transport on the target family of block fibres. -/
def toRepresentativeY (y : Y) :
    BlockFibre blockY
      (orbitRepresentative
        (Quotient.mk'' (blockY y) : BlockOrbit A Block)) := by
  let t := orbitTransporter (A := A) (blockY y)
  refine ⟨t⁻¹ • y, ?_⟩
  change blockY (t⁻¹ • y) =
    orbitRepresentative (Quotient.mk'' (blockY y) : BlockOrbit A Block)
  rw [hblockY]
  have ht := orbitTransporter_smul_representative (A := A) (blockY y)
  calc
    t⁻¹ • blockY y = t⁻¹ •
        (t • orbitRepresentative
          (Quotient.mk'' (blockY y) : BlockOrbit A Block)) := by
      rw [ht]
    _ = orbitRepresentative
          (Quotient.mk'' (blockY y) : BlockOrbit A Block) :=
      inv_smul_smul t _

/-- A family of bijections on orbit representatives.  The equivariance
hypothesis is only under the stabiliser of the representative block. -/
structure RepresentativeEquivFamily where
  equiv : ∀ omega : BlockOrbit A Block,
    BlockFibre blockX (orbitRepresentative omega) ≃
      BlockFibre blockY (orbitRepresentative omega)
  equivariant : ∀ (omega : BlockOrbit A Block) (a : A)
      (hfix : a • orbitRepresentative omega = orbitRepresentative omega)
      (x : BlockFibre blockX (orbitRepresentative omega)),
        (equiv omega ⟨a • x.1, by
          change blockX (a • x.1) = orbitRepresentative omega
          rw [hblockX, x.2, hfix]⟩).1 = a • (equiv omega x).1

/-- Existence, rather than a preselected family, of the local bijection on
each orbit representative.  This is the form supplied by an application of
Proposition 3.11 to each representative block. -/
def RepresentativeEquivExists : Prop :=
  ∀ omega : BlockOrbit A Block,
    ∃ e : BlockFibre blockX (orbitRepresentative omega) ≃
        BlockFibre blockY (orbitRepresentative omega),
      ∀ (a : A)
        (hfix : a • orbitRepresentative omega = orbitRepresentative omega)
        (x : BlockFibre blockX (orbitRepresentative omega)),
          (e ⟨a • x.1, by
            change blockX (a • x.1) = orbitRepresentative omega
            rw [hblockX, x.2, hfix]⟩).1 = a • (e x).1

namespace RepresentativeEquivFamily

/-- Select the local equivalences whose existence is known on the orbit
representatives.  All global compatibility is proved later rather than put
into this choice. -/
def ofExists
    (hexists : RepresentativeEquivExists blockX blockY hblockX) :
    RepresentativeEquivFamily blockX blockY hblockX where
  equiv omega := Classical.choose (hexists omega)
  equivariant omega a hfix x :=
    Classical.choose_spec (hexists omega) a hfix x

variable
  (F : RepresentativeEquivFamily blockX blockY hblockX)

/-- Acting by `a` gives an equivalence from the fibre over `b` to the fibre
over `c` whenever `a • b = c`. -/
def fibreActionEquiv {W : Type u} [MulAction A W]
    (blockW : W → Block)
    (hblockW : ∀ (a : A) (w : W), blockW (a • w) = a • blockW w)
    (a : A) (b c : Block) (h : a • b = c) :
    BlockFibre blockW b ≃ BlockFibre blockW c where
  toFun w := ⟨a • w.1, by
    change blockW (a • w.1) = c
    rw [hblockW, w.2, h]⟩
  invFun w := ⟨a⁻¹ • w.1, by
    change blockW (a⁻¹ • w.1) = b
    rw [hblockW, w.2, ← h]
    simp⟩
  left_inv w := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply Subtype.ext
    simp

/-- The transported bijection on `b`, written using an explicitly chosen
description `omega` of its orbit.  Keeping the orbit equality explicit avoids
hiding dependent casts in the equivariance proof. -/
def atBlockEquivAt (b : Block) (omega : BlockOrbit A Block)
    (homega : (Quotient.mk'' b : BlockOrbit A Block) = omega) :
    BlockFibre blockX b ≃ BlockFibre blockY b :=
  let t := orbitTransporter (A := A) b
  let ht : t • orbitRepresentative omega = b := by
    have ht0 := orbitTransporter_smul_representative (A := A) b
    have hrep := congrArg orbitRepresentative homega
    rw [← hrep]
    exact ht0
  ((fibreActionEquiv blockX hblockX t
      (orbitRepresentative omega) b ht).symm).trans
    ((F.equiv omega).trans
      (fibreActionEquiv blockY hblockY t
        (orbitRepresentative omega) b ht))

/-- The transported bijection on an arbitrary block. -/
def atBlockEquiv (b : Block) :
    BlockFibre blockX b ≃ BlockFibre blockY b :=
  atBlockEquivAt (A := A) blockX blockY hblockX hblockY F b
    (Quotient.mk'' b) rfl

theorem atBlockEquiv_eq_at (b : Block) (omega : BlockOrbit A Block)
    (homega : (Quotient.mk'' b : BlockOrbit A Block) = omega) :
    atBlockEquiv (A := A) blockX blockY hblockX hblockY F b =
      atBlockEquivAt (A := A) blockX blockY hblockX hblockY F b omega homega := by
  subst omega
  rfl

/-- The transported block maps combine into a global bijection. -/
def globalEquiv : X ≃ Y :=
  (Equiv.sigmaFiberEquiv blockX).symm |>.trans
    (Equiv.sigmaCongrRight
      (atBlockEquiv (A := A) blockX blockY hblockX hblockY F)) |>.trans
    (Equiv.sigmaFiberEquiv blockY)

@[simp]
theorem globalEquiv_apply (x : X) :
    globalEquiv (A := A) blockX blockY hblockX hblockY F x =
      (atBlockEquiv (A := A) blockX blockY hblockX hblockY F
        (blockX x) ⟨x, rfl⟩).1 := rfl

theorem globalEquiv_block_preserving (x : X) :
    blockY (globalEquiv (A := A) blockX blockY hblockX hblockY F x) =
      blockX x :=
  (atBlockEquiv (A := A) blockX blockY hblockX hblockY F
    (blockX x) ⟨x, rfl⟩).2

theorem globalEquiv_eq_atBlock (b : Block) (x : X)
    (hx : blockX x = b) :
    globalEquiv (A := A) blockX blockY hblockX hblockY F x =
      (atBlockEquiv (A := A) blockX blockY hblockX hblockY F b
        ⟨x, hx⟩).1 := by
  subst b
  rfl

theorem atBlockEquiv_equivariant (a : A) (b : Block)
    (x : BlockFibre blockX b) :
    atBlockEquiv (A := A) blockX blockY hblockX hblockY F (a • b)
        ⟨a • x.1, by
          change blockX (a • x.1) = a • b
          rw [hblockX, x.2]⟩ =
      ⟨a • (atBlockEquiv (A := A) blockX blockY hblockX hblockY F b x).1,
        by
          change blockY (a • _) = a • b
          rw [hblockY,
            (atBlockEquiv (A := A) blockX blockY hblockX hblockY F b x).2]⟩ := by
  let omega : BlockOrbit A Block := Quotient.mk'' b
  let t := orbitTransporter (A := A) b
  let t' := orbitTransporter (A := A) (a • b)
  let h := t'⁻¹ * a * t
  have ht : t • orbitRepresentative omega = b := by
    simp [t, omega]
  have ht' : t' • orbitRepresentative omega = a • b := by
    have htransport :=
      orbitTransporter_smul_representative (A := A) (a • b)
    simpa [t', omega, blockOrbit_smul] using htransport
  have hrep : h • orbitRepresentative omega = orbitRepresentative omega := by
    calc
      h • orbitRepresentative omega =
          t'⁻¹ • (a • (t • orbitRepresentative omega)) := by
        simp [h, mul_smul]
      _ = t'⁻¹ • (a • b) := by rw [ht]
      _ = t'⁻¹ • (t' • orbitRepresentative omega) := by rw [ht']
      _ = orbitRepresentative omega := inv_smul_smul t' _
  have homega :
      (Quotient.mk'' (a • b) : BlockOrbit A Block) = omega := by
    simp [omega]
  apply Subtype.ext
  rw [atBlockEquiv_eq_at
    (A := A) blockX blockY hblockX hblockY F (a • b) omega homega]
  rw [atBlockEquiv_eq_at
    (A := A) blockX blockY hblockX hblockY F b omega (by rfl)]
  simp only [atBlockEquivAt, Equiv.trans_apply]
  simp only [fibreActionEquiv]
  change t' • (F.equiv omega
      ⟨t'⁻¹ • (a • x.1), _⟩).1 =
    a • (t • (F.equiv omega ⟨t⁻¹ • x.1, _⟩).1)
  have hinput :
      (⟨t'⁻¹ • (a • x.1), by
        change blockX (t'⁻¹ • (a • x.1)) = orbitRepresentative omega
        rw [hblockX, hblockX, x.2, ← ht']
        simp⟩ : BlockFibre blockX (orbitRepresentative omega)) =
      ⟨h • (t⁻¹ • x.1), by
        change blockX (h • (t⁻¹ • x.1)) = orbitRepresentative omega
        rw [hblockX, hblockX, x.2]
        simp [h, mul_smul, ← ht']⟩ := by
    apply Subtype.ext
    simp [h, mul_smul]
  have hxrep :
      blockX (t⁻¹ • x.1) = orbitRepresentative omega := by
    rw [hblockX, x.2, ← ht]
    simp
  have hlocal := F.equivariant omega h hrep
    (⟨t⁻¹ • x.1, hxrep⟩ :
      BlockFibre blockX (orbitRepresentative omega))
  rw [hinput, hlocal]
  simp [h, mul_smul]

theorem globalEquiv_equivariant (a : A) (x : X) :
    globalEquiv (A := A) blockX blockY hblockX hblockY F (a • x) =
      a • globalEquiv (A := A) blockX blockY hblockX hblockY F x := by
  have h := atBlockEquiv_equivariant
    (A := A) blockX blockY hblockX hblockY F a (blockX x) ⟨x, rfl⟩
  calc
    globalEquiv (A := A) blockX blockY hblockX hblockY F (a • x) =
        (atBlockEquiv (A := A) blockX blockY hblockX hblockY F
          (a • blockX x) ⟨a • x, hblockX a x⟩).1 :=
      globalEquiv_eq_atBlock
        (A := A) blockX blockY hblockX hblockY F
        (a • blockX x) (a • x) (hblockX a x)
    _ = a • (atBlockEquiv (A := A) blockX blockY hblockX hblockY F
          (blockX x) ⟨x, rfl⟩).1 := congrArg Subtype.val h
    _ = a • globalEquiv (A := A) blockX blockY hblockX hblockY F x := by
      rw [globalEquiv_apply]

end RepresentativeEquivFamily

variable {Brauer Label Weight : Type u}
variable [MulAction A Brauer] [MulAction A Label] [MulAction A Weight]

/-- The genuine orbit-construction step in Proposition 3.14, condition (ii).

`alphaExists` represents the Proposition 3.11 bijections on one block in each
orbit.  `rho` represents Li's ordinary-label-to-weight correspondence.  The
conclusion is only the equivariant block-preserving bijection required in
condition (ii), not the Brough--Späth criterion's final conclusion. -/
theorem exists_condition_ii_bijection_of_orbitwise_composition
    (brauerBlock : Brauer → Block)
    (labelBlock : Label → Block)
    (weightBlock : Weight → Block)
    (hbrauerBlock : ∀ (a : A) (x : Brauer),
      brauerBlock (a • x) = a • brauerBlock x)
    (hlabelBlock : ∀ (a : A) (x : Label),
      labelBlock (a • x) = a • labelBlock x)
    (alphaExists : RepresentativeEquivExists
      brauerBlock labelBlock hbrauerBlock)
    (rho : Label ≃ Weight)
    (rho_equivariant : ∀ (a : A) (x : Label), rho (a • x) = a • rho x)
    (rho_block_preserving : ∀ x : Label,
      weightBlock (rho x) = labelBlock x) :
    ∃ omega : Brauer ≃ Weight,
      (∀ (a : A) (x : Brauer), omega (a • x) = a • omega x) ∧
      (∀ x : Brauer, weightBlock (omega x) = brauerBlock x) := by
  let alpha := RepresentativeEquivFamily.ofExists
    (A := A) (blockX := brauerBlock) (blockY := labelBlock)
      (hblockX := hbrauerBlock) alphaExists
  let alphaGlobal := RepresentativeEquivFamily.globalEquiv
    (A := A) (blockX := brauerBlock) (blockY := labelBlock)
      (hblockX := hbrauerBlock) (hblockY := hlabelBlock) alpha
  let omega := alphaGlobal.trans rho
  refine ⟨omega, ?_, ?_⟩
  · intro a x
    exact (congrArg rho
      (RepresentativeEquivFamily.globalEquiv_equivariant
        (A := A) (blockX := brauerBlock) (blockY := labelBlock)
        (hblockX := hbrauerBlock) (hblockY := hlabelBlock) alpha a x)).trans
      (rho_equivariant a (alphaGlobal x))
  · intro x
    exact (rho_block_preserving (alphaGlobal x)).trans
      (RepresentativeEquivFamily.globalEquiv_block_preserving
        (A := A) (blockX := brauerBlock) (blockY := labelBlock)
        (hblockX := hbrauerBlock) (hblockY := hlabelBlock) alpha x)

end

end ModularRep.PaperProofs.OddConlonOrbitAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
