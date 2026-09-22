import ModularRep.PaperProofs.TypeBRankThreeJordanCliffordCarriers
import ModularRep.PaperProofs.TypeBLemma47LeviApplication

/-!
# Actual Clifford, paired-Levi and field actions on the same Spin characters

All actions are inverse pullback along the already constructed group maps.
The paired Levi acts through its literal Clifford inclusion. The field
action restricts the same finite point actor to the characteristic Spin
subgroup. Both semidirect compatibility laws are deductions from these
maps, with no character-action or stabilizer assertion as a source input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeJordanActions

open ModularRep TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBRankThreeJordanCliffordCarriers
open TypeBLemma47LeviApplication
open EvenFieldAssumption53Relative

variable {p f : ℕ} {F A E k K : Type}
variable [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A]
variable {N : NormSource 3 F} {Nbar : NormSource 3 A}
variable {Frob : MulAut (SpecialClifford 3 A)}
variable [Finite (SpecialClifford 3 F)] [Finite (Spin 3 F N)]
variable [Group E] [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)
variable (fieldPoints : E →* MulAut (fixedPoints Frob.toMonoidHom))
variable (perfect : commutator (Spin 3 F N) = ⊤)
variable (iotaG : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))

/-- The literal Clifford conjugation action on the original Spin characters. -/
@[instance_reducible]
def cliffordBrauerAction : MulAction (SpecialClifford 3 F) (IBr iotaG) :=
  ambientBrauerAction (SpinSubgroup 3 F N) iotaG

/-- The prescribed field action on Brauer characters with the fixed root embedding. -/
@[instance_reducible]
def spinBrauerFieldAction : MulAction E (IBr iotaG) :=
  rightAutomorphismAction iotaG
    (TypeBRankThreeJordanCliffordCarriers.spinFieldAction points fieldPoints perfect)

/-- The original rational paired Levi acts through its actual inclusion. -/
@[instance_reducible]
def gammaBrauerAction (Lbar : Subgroup (SpecialClifford 3 A)) :
    MulAction (M Frob.toMonoidHom Lbar) (IBr iotaG) := by
  letI := cliffordBrauerAction iotaG
  exact MulAction.compHom (IBr iotaG) (gammaEmbedding points Lbar)

theorem clifford_action_apply (m : SpecialClifford 3 F) (phi : IBr iotaG) :
    letI := cliffordBrauerAction iotaG
    m • phi = IrreducibleBrauerCharacter.twist iotaG phi
      (MulAut.conjNormal (H := SpinSubgroup 3 F N) m⁻¹) := rfl

theorem field_action_apply (e : E) (phi : IBr iotaG) :
    letI := spinBrauerFieldAction points fieldPoints perfect iotaG
    e • phi = IrreducibleBrauerCharacter.twist iotaG phi
      (TypeBRankThreeJordanCliffordCarriers.spinFieldAction points fieldPoints perfect e⁻¹) :=
  rfl

/-- Equality with the action of the SAME included finite Clifford element. -/
theorem gamma_action_eq (Lbar : Subgroup (SpecialClifford 3 A))
    (m : M Frob.toMonoidHom Lbar) (phi : IBr iotaG) :
    letI := cliffordBrauerAction iotaG
    letI := gammaBrauerAction points iotaG Lbar
    m • phi = gammaEmbedding points Lbar m • phi := rfl

theorem gamma_action_apply (Lbar : Subgroup (SpecialClifford 3 A))
    (m : M Frob.toMonoidHom Lbar) (phi : IBr iotaG) :
    letI := gammaBrauerAction points iotaG Lbar
    m • phi = IrreducibleBrauerCharacter.twist iotaG phi
      (MulAut.conjNormal (H := SpinSubgroup 3 F N) (gammaEmbedding points Lbar m)⁻¹) :=
  rfl

/-- Inner Spin elements fix every original irreducible Brauer character. -/
theorem inner_spin_fixes (g : Spin 3 F N) (phi : IBr iotaG) :
    letI := cliffordBrauerAction iotaG
    (g : SpecialClifford 3 F) • phi = phi :=
  subgroup_element_fixes_brauer_character (SpinSubgroup 3 F N) iotaG g phi

include perfect in
/-- The transported finite field actor preserves the literal norm kernel. -/
theorem spin_stable (e : E) (g : SpecialClifford 3 F) :
    g ∈ SpinSubgroup 3 F N ↔
      cliffordFieldAction points fieldPoints e g ∈ SpinSubgroup 3 F N := by
  let alpha := cliffordFieldAction points fieldPoints e
  have hmap := spinSubgroup_map_of_perfect N perfect alpha
  constructor
  · intro hg
    have h := Subgroup.mem_map_of_mem alpha.toMonoidHom hg
    rw [hmap] at h
    exact h
  · intro hg
    have h : alpha g ∈ (SpinSubgroup 3 F N).map alpha.toMonoidHom := by
      rw [hmap]
      exact hg
    obtain ⟨x, hx, heq⟩ := h
    exact (alpha.injective heq) ▸ hx

/-- The checked Spin action equals the existing literal subgroup restriction. -/
theorem spinFieldAction_eq_restrict :
    TypeBRankThreeJordanCliffordCarriers.spinFieldAction points fieldPoints perfect =
      restrictAutomorphismHom (SpinSubgroup 3 F N)
        (cliffordFieldAction points fieldPoints) (spin_stable points fieldPoints perfect) := by
  apply MonoidHom.ext
  intro e
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rfl

/-- The field and Clifford actions satisfy the actual semidirect law. -/
theorem clifford_semidirect_compatible :
    letI := cliffordBrauerAction iotaG
    letI := spinBrauerFieldAction points fieldPoints perfect iotaG
    Formalisation.SemidirectActionCompatible (X := IBr iotaG)
      (cliffordFieldAction points fieldPoints) := by
  intro e g phi
  change IrreducibleBrauerCharacter.twist iotaG
      (IrreducibleBrauerCharacter.twist iotaG phi
        (MulAut.conjNormal (H := SpinSubgroup 3 F N) g⁻¹))
      (TypeBRankThreeJordanCliffordCarriers.spinFieldAction points fieldPoints perfect e⁻¹) =
    IrreducibleBrauerCharacter.twist iotaG
      (IrreducibleBrauerCharacter.twist iotaG phi
        (TypeBRankThreeJordanCliffordCarriers.spinFieldAction points fieldPoints perfect e⁻¹))
      (MulAut.conjNormal (H := SpinSubgroup 3 F N)
        (cliffordFieldAction points fieldPoints e g)⁻¹)
  rw [spinFieldAction_eq_restrict points fieldPoints perfect]
  exact field_ambient_brauer_naturality (SpinSubgroup 3 F N) iotaG
    (cliffordFieldAction points fieldPoints) (spin_stable points fieldPoints perfect) e g phi

variable (Lbar : Subgroup (SpecialClifford 3 A))
variable (stable : ∀ (e : E) (x : fixedPoints Frob.toMonoidHom),
  x ∈ M Frob.toMonoidHom Lbar ↔ fieldPoints e x ∈ M Frob.toMonoidHom Lbar)

/-- Paired-Levi compatibility follows through the original inclusion square. -/
theorem gamma_semidirect_compatible :
    letI := gammaBrauerAction points iotaG Lbar
    letI := spinBrauerFieldAction points fieldPoints perfect iotaG
    Formalisation.SemidirectActionCompatible (X := IBr iotaG)
      (gammaFieldAction fieldPoints Lbar stable) := by
  letI := cliffordBrauerAction iotaG
  letI := gammaBrauerAction points iotaG Lbar
  letI := spinBrauerFieldAction points fieldPoints perfect iotaG
  intro e m phi
  change e • (gammaEmbedding points Lbar m • phi) =
    gammaEmbedding points Lbar (gammaFieldAction fieldPoints Lbar stable e m) • (e • phi)
  rw [gammaEmbedding_field points fieldPoints Lbar stable]
  exact clifford_semidirect_compatible points fieldPoints perfect iotaG e
    (gammaEmbedding points Lbar m) phi

end ModularRep.PaperProofs.TypeBRankThreeJordanActions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
