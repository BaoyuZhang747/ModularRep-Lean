import ModularRep.PaperProofs.TypeBGlobalExtensionBinding
import ModularRep.PaperProofs.TypeBLocalOrdinaryExtensionSplitting

/-!
# The four extension clauses with sufficient ordinary roots

The two Brauer extensions use the cyclic representation theorem. Each
ordinary extension uses the scoped cyclic theorem on its own raw inertia
quotient. Sufficient roots for the full semidirect ambient group supply
the two local root conditions in the same coefficient field.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBExtensionClausesSplitting

open ModularRep TypeBCriterionHypotheses TypeBLocalOrdinaryGeometry
open TypeBLocalOrdinaryExtensionSplitting

variable {ell : ℕ} {k K M E : Type}
  [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
  [Group M] [Finite M] [Group E] [Finite E] [IsCyclic E]
  (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
  (action : NaturalAction G field)
  [HasEnoughRootsOfUnity K (Nat.card (Ambient field))]

/-- The actual first inertia quotient inherits its roots from the ambient group. -/
def mRoots (W : CharacterWeight ell K G) :
    HasEnoughRootsOfUnity K (Nat.card (Inertia G field action W (embeddedM field) ⧸
      RadicalInInertia G field action W (embeddedM field))) :=
  localRoots_of_ambientRoots G field action W (embeddedM field)

/-- The second quotient includes its field-degree contribution in this bound. -/
def geRoots (W : CharacterWeight ell K G) :
    HasEnoughRootsOfUnity K (Nat.card (Inertia G field action W (baseFieldGroup G field) ⧸
      RadicalInInertia G field action W (baseFieldGroup G field))) :=
  localRoots_of_ambientRoots G field action W (baseFieldGroup G field)

variable (iota : PrimeRegularRootEmbedding ell k K G)

/-- All four clauses follow from the independent cyclic theorems on their
literal carriers. The ordinary sources quantify over every raw weight. -/
theorem extensionClauses
    (brauerPrinciple : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (quotient_cyclic : IsCyclic (M ⧸ G))
    (ordinaryM : ∀ W : CharacterWeight ell K G,
      letI := mRoots G field action W
      ScopedCyclicExtensionSource K (Inertia G field action W (embeddedM field) ⧸
        RadicalInInertia G field action W (embeddedM field)))
    (ordinaryGE : ∀ W : CharacterWeight ell K G,
      letI := geRoots G field action W
      ScopedCyclicExtensionSource K (Inertia G field action W (baseFieldGroup G field) ⧸
        RadicalInInertia G field action W (baseFieldGroup G field))) :
    ExtensionClauses G field action iota where
  brauer_M phi := ⟨TypeBGlobalExtensionBinding.brauer_M
    G field action iota phi brauerPrinciple quotient_cyclic⟩
  brauer_GE phi := ⟨TypeBGlobalExtensionBinding.brauer_GE
    G field action iota phi brauerPrinciple⟩
  ordinary_M W := by
    letI := mRoots G field action W
    exact TypeBLocalOrdinaryExtensionSplitting.ordinary_M
      G field action W (ordinaryM W) quotient_cyclic
  ordinary_GE W := by
    letI := geRoots G field action W
    exact TypeBLocalOrdinaryExtensionSplitting.ordinary_GE
      G field action W (ordinaryGE W)

end ModularRep.PaperProofs.TypeBExtensionClausesSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
