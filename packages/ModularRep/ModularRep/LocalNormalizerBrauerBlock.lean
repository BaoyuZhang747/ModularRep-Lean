import ModularRep.IBrBlock
import ModularRep.LocalNormalizerBlockOperations

/-!
# The literal normaliser block of a Brauer character

The complete block decomposition stored at a fixed subgroup `Q` determines
the literal normaliser block containing an irreducible Brauer character.  The
selector below is a kernel construction from that decomposition and the
canonical injectivity theorem for the chosen root embedding.
-/

noncomputable section

namespace ModularRep.CharacterWeight

open ModularRep.FDRepSimpleClassKZero

universe u

variable {p : Nat} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable {Q : Subgroup G}

namespace LocalNormalizerBlockOperations

noncomputable def normalizerBrauerBlock
    (O : LocalNormalizerBlockOperations
      (p := p) (k := k) (K := K) (G := G) Q)
    (iota : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer (Q : Set G)))
    (phi : IBr iota) : InflatedNormalizerBlock (k := k) Q := by
  let localData := O.normalizerBlockData
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  exact irreducibleBrauerCharacterBlock iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    localData.blocks phi

end LocalNormalizerBlockOperations
end ModularRep.CharacterWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
