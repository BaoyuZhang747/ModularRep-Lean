import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionDominatedBlock

/-!
# Nontrivial central sectors of the actual q3 triple cover

The carrier and its order-three centre are the accepted free-cover quotient.
The input that a named literal block has nontrivial central sector is the
specified E3 table binding: canonical Table typeb-q3-blocks and the retained
o7blocks.out central ratios identify B6/B8 and B7/B9 with the two nontrivial
sectors. This file constructs no inhabitant of that binding.

The consequences below concern the common central kernel and the same chosen
representation of every supported Brauer character. They introduce no
ordinary-character object or conclusion about the full representation kernel.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3FaithfulCentralSector

open ModularRep
open TypeBQ3TripleCoverCarrier TypeBQ3PrincipalCriterionDominatedBlock
open TypeBCentralKernelBlockSource

variable (source : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
variable [Finite X]
variable {k : Type} [Field k] [CharP k 2] [IsAlgClosed k]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

/-- A nontrivial scalar homomorphism on this centre has trivial kernel. -/
theorem sectorKernel_eq_bot
    (b : LiteralPrimitiveBlock k X)
    (nontrivial : centralSector source freeSource b ≠ 1) :
    (centralSector source freeSource b).ker = ⊥ := by
  letI : Fact (Nat.card (Subgroup.center X)).Prime := ⟨by
    rw [center_X_card source freeSource]
    decide⟩
  exact ((centralSector source freeSource b).ker.eq_bot_or_eq_top_of_prime_card).resolve_right
    (fun htop => nontrivial (MonoidHom.ker_eq_top_iff.mp htop))

/-- Embed the common sector kernel into the original group. -/
theorem mappedSectorKernel_eq_bot
    (b : LiteralPrimitiveBlock k X)
    (nontrivial : centralSector source freeSource b ≠ 1) :
    (centralSector source freeSource b).ker.map (Subgroup.center X).subtype = ⊥ := by
  rw [sectorKernel_eq_bot source freeSource b nontrivial, Subgroup.map_bot]

/-- Every irreducible representation in the literal block is centrally faithful. -/
theorem supportedRepresentation_centralKernel_eq_bot
    (b : LiteralPrimitiveBlock k X)
    (nontrivial : centralSector source freeSource b ≠ 1)
    (V : FDRep k X) (irreducible : Representation.IsIrreducible V.ρ)
    (support : Representation.asAlgebraHom V.ρ b.val = 1) :
    Subgroup.center X ⊓ V.ρ.ker = ⊥ := by
  letI : Representation.IsIrreducible V.ρ := irreducible
  letI := centralOrderInvertible source freeSource (k := k)
  letI : Fact (Nat.card (Subgroup.center X)).Prime := ⟨by
    rw [center_X_card source freeSource]
    decide⟩
  have same : centralSector source freeSource b =
      Representation.centralCharacter V.ρ (Subgroup.center X) le_rfl := by
    apply Representation.primitiveCentralIdempotentSector_eq_centralCharacter
      V.ρ (Subgroup.center X) le_rfl b.property
    intro v
    apply (Representation.asModuleEquiv V.ρ).injective
    rw [Representation.asModuleEquiv_map_smul, support]
    rfl
  let restricted : Subgroup.center X →* Module.End k V :=
    V.ρ.comp (Subgroup.center X).subtype
  have restrictedKernel : restricted.ker = ⊥ :=
    (restricted.ker.eq_bot_or_eq_top_of_prime_card).resolve_right (by
      intro htop
      apply nontrivial
      apply same.trans
      apply SporadicFi24P3Definition44NamedCarrierCentralBlockKernel.centralCharacter_eq_one_of_le_ker
        (Subgroup.center X) le_rfl V.ρ
      intro x hx
      have member : (⟨x, hx⟩ : Subgroup.center X) ∈ restricted.ker := by
        rw [htop]
        trivial
      exact member)
  apply bot_unique
  intro x hx
  have member : (⟨x, hx.1⟩ : Subgroup.center X) ∈ restricted.ker := hx.2
  rw [restrictedKernel] at member
  exact Subgroup.mem_bot.mpr
    (congrArg Subtype.val (Subgroup.mem_bot.mp member))

variable {K : Type} [Field K] [CharZero K]

/-- The original character's chosen affording representation has this kernel. -/
theorem supportedBrauer_centralKernel_eq_bot
    (root : PrimeRegularRootEmbedding 2 k K X)
    [Fintype (LiteralPrimitiveBlock k X)]
    (D : BlockIdempotentDecomposition (fun c : LiteralPrimitiveBlock k X => c.val))
    (b : LiteralPrimitiveBlock k X)
    (nontrivial : centralSector source freeSource b ≠ 1)
    (phi : {phi : IBr root // Supported root b phi}) :
    TypeBBSCentralCharacterQuotient.centralKernel root phi.val = ⊥ := by
  exact supportedRepresentation_centralKernel_eq_bot source freeSource b nontrivial
    (EvenFieldFLZBAWGoodFamily.chosenIBrRepresentation root phi.val)
    (Classical.choose_spec phi.val.property).1
    (TypeBQ3PrincipalBrauerInflation.chosenRepresentation_support root D b phi)

end ModularRep.PaperProofs.TypeBQ3FaithfulCentralSector


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
