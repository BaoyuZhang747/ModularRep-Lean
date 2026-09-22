import ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

/-! Restrict the same global map to all central fibres, for arbitrary characteristic. -/
noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJointSectorAssembly

open Formalisation
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R :
  LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-- Restrict a global automorphism-equivariant, block-preserving equivalence
to the literal central-sector fibres.  Sector preservation and both inverse
fibre-membership proofs are kernel deductions from `hblock`. -/
def sectorFamilyOfGlobalEquiv
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (alpha • phi) = alpha • Omega phi)
    (hblock : ∀ phi,
      R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi) :
    EquivariantFibreEquiv
      (brauerSector iota hinj blocks)
      (weightSector (R := R))
      (brauerSector_equivariant iota hinj blocks E1)
      (weightSector_equivariant_actual
        (iota := iota) (hinj := hinj) (blocks := blocks) (R := R) E1) where
  fibreEquiv sector :=
    { toFun := fun phi =>
        ⟨Omega phi, by
          have hsector :
              weightSector (R := R) (Omega phi) =
                brauerSector iota hinj blocks phi := by
            unfold weightSector brauerSector
            rw [hblock phi]
          exact hsector.trans phi.2⟩
      invFun := fun weight =>
        ⟨Omega.symm weight, by
          have hsector :
              weightSector (R := R) (Omega (Omega.symm weight)) =
                brauerSector iota hinj blocks (Omega.symm weight) := by
            unfold weightSector brauerSector
            rw [hblock (Omega.symm weight)]
          rw [Omega.apply_symm_apply] at hsector
          exact hsector.symm.trans weight.2⟩
      left_inv := by
        intro phi
        apply Subtype.ext
        exact Omega.symm_apply_apply phi
      right_inv := by
        intro weight
        apply Subtype.ext
        exact Omega.apply_symm_apply weight }
  map_actFibre alpha _sector phi := by
    apply Subtype.ext
    exact hOmega alpha phi

/-- Package the restricted family with the already proved literal block
equality and pair predicate.  No field of `AnDietrichSectorInput` is accepted
as an input. -/
def anDietrichSectorInput_ofGlobalEquiv
    (ModularCharacterTriple :
      IBr iota → WeightClass (p := p) (K := K) (X := X) → Prop)
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (alpha • phi) = alpha • Omega phi)
    (hblock : ∀ phi,
      R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi)
    (htriple : ∀ phi, ModularCharacterTriple phi (Omega phi)) :
    AnDietrichSectorInput iota hinj blocks E1 ModularCharacterTriple where
  family := sectorFamilyOfGlobalEquiv
    iota hinj blocks E1 Omega hOmega hblock
  blockInduction _sector phi := by
    change R.1.weightBlock (Omega phi.1) =
      brauerBlock iota hinj blocks phi.1
    exact hblock phi.1
  characterTriple _sector phi := by
    change ModularCharacterTriple phi.1 (Omega phi.1)
    exact htriple phi.1


/-- The same strong concrete joint assertion occupies all three legacy fields. -/
theorem joint_sector_assembly
    (P : IBr iota → WeightClass (p := p) (K := K) (X := X) → Prop)
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi)
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi)
    (hjoint : ∀ phi, P phi (Omega phi)) :
    ∃ AD : AnDietrichSectorInput iota hinj blocks E1 P,
      (∀ phi, AnDietrichSectorInput.assemble iota hinj blocks E1 AD phi = Omega phi) ∧
      Nonempty (SpathLemma61Input iota hinj blocks E1 P P P AD) ∧
      Nonempty (Fi24AssembledClauses iota hinj blocks E1 P P P AD) := by
  let AD := anDietrichSectorInput_ofGlobalEquiv iota hinj blocks E1 P Omega hOmega hblock hjoint
  let SP : SpathLemma61Input iota hinj blocks E1 P P P AD := {
    intermediateBlockEqualities := fun _ phi => hjoint phi.val
    compatibleExtensions := fun _ phi => hjoint phi.val }
  exact ⟨AD, fun _ => rfl, ⟨SP⟩, ⟨fi24_source_shaped_assembly iota hinj blocks E1 P P P AD SP⟩⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJointSectorAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
