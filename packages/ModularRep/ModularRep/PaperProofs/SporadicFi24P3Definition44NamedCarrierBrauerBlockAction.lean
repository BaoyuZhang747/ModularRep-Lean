import ModularRep.IBrBlockEquivTransport

/-! Actual block actions on an affording representation, and Brauer values
at elements killed by that representation. No character or block support
is supplied as an additional field. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction

open ModularRep ModularRep.FDRepSimpleClassKZero

universe u v
variable {p : ℕ} {k G : Type u} {K : Type v}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

theorem block_smul_of_affording
    {ι : Type*} [Fintype ι] {b : ι → k[G]}
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (D : BlockIdempotentDecomposition b) (phi : IBr iota)
    (V : FDRep k G) (hV : Representation.IsIrreducible V.ρ)
    (hchar : phi.1 = Representation.brauerCharacterOfRootEmbedding V.ρ iota) :
    ∀ v : Representation.asModule V.ρ,
      b (irreducibleBrauerCharacterBlock iota hinj D phi) • v = v := by
  let : IsSimpleModule k[G] (Representation.asModule V.ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hV
  have hphi : simpleClassToIBr iota
      (simpleClassOfIrreducibleFDRep V hV) = phi := by
    apply Subtype.ext
    change Representation.brauerCharacterOfRootEmbedding
      (simpleClassFDRep (simpleClassOfIrreducibleFDRep V hV)).ρ iota = phi.1
    rw [hchar]
    exact Representation.brauerCharacterOfRootEmbedding_iso iota
      (simpleClassOfIrreducibleFDRepIso V hV)
  have hblock : irreducibleBrauerCharacterBlock iota hinj D phi =
      D.moduleBlock (V := Representation.asModule V.ρ) := by
    rw [← hphi, irreducibleBrauerCharacterBlock_simpleClassToIBr]
    exact simpleModuleClassBlock_simpleClassOfIrreducibleFDRep D V hV
  intro v
  rw [hblock]
  exact D.moduleBlock_smul v

theorem brauer_apply_eq_one_of_mem_ker
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V) (iota : PrimeRegularRootEmbedding p k K G)
    (g : PrimeRegularElement (G := G) p) (hg : g.1 ∈ rho.ker) :
    rho.brauerCharacterOfRootEmbedding iota g =
      rho.brauerCharacterOfRootEmbedding iota ⟨1, isPrimeRegular_one⟩ := by
  change (Multiset.map iota.lift (LinearMap.charpoly (rho g.1)).roots).sum =
    (Multiset.map iota.lift (LinearMap.charpoly (rho 1)).roots).sum
  rw [MonoidHom.mem_ker.mp hg, map_one]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
