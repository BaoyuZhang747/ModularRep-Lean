import ModularRep.BrauerCharacterSeparation
import ModularRep.BrauerTraceRecovery
import ModularRep.CyclotomicDeterminantSpecialization
import ModularRep.PrimeRegularEvaluationMatrix
import ModularRep.SimpleTraceLinearIndependence

/-!
# Linear independence of irreducible Brauer characters

The modular trace functions of the simple modules are linearly independent.
They therefore have a nonsingular evaluation matrix on prime regular elements.
Every entry is a finite sum of roots of unity, and the explicit root
equivalence defining the Brauer values carries this matrix to the corresponding
characteristic-zero evaluation matrix.  Cyclotomic determinant specialisation
preserves its nonvanishing.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.FDRepSimpleClassKZero

universe u v

variable {p : ℕ} {k G : Type u} {K : Type v}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

private abbrev SimpleIndex := SimpleModuleClass k[G]

omit [CharZero K] in
/-- The modular trace functions of the simple module classes have a
nonsingular evaluation matrix on prime regular elements. -/
theorem exists_simpleClass_primeRegular_trace_det_ne_zero
    [Fintype (SimpleIndex (k := k) (G := G))]
    [DecidableEq (SimpleIndex (k := k) (G := G))]
    (hp : p.Prime) :
    ∃ x : SimpleIndex (k := k) (G := G) →
        PrimeRegularElement (G := G) p,
      Matrix.det (fun X j ↦
        (simpleClassFDRep X).character (x j).1) ≠ 0 := by
  apply
    PrimeRegularEvaluationMatrix.exists_fdRep_character_evaluation_det_ne_zero
      hp (fun X : SimpleIndex (k := k) (G := G) ↦
        simpleClassFDRep X)
  change LinearIndependent k
    (fun X : SimpleModuleClass k[G] ↦
      Representation.character (simpleClassFDRep X).ρ)
  exact SimpleTraceLinearIndependence.simpleModuleClass_character_linearIndependent
    (k := k) (G := G)

/-- The corresponding evaluation matrix of the lifted Brauer values is
nonsingular. -/
theorem exists_simpleClass_primeRegular_brauer_det_ne_zero
    [Fintype (SimpleIndex (k := k) (G := G))]
    [DecidableEq (SimpleIndex (k := k) (G := G))]
    (iota : PrimeRegularRootEmbedding p k K G) :
    ∃ x : SimpleIndex (k := k) (G := G) →
        PrimeRegularElement (G := G) p,
      Matrix.det (fun X j ↦ simpleClassBrauerFamily iota X (x j)) ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ :=
    exists_simpleClass_primeRegular_trace_det_ne_zero
      (k := k) (G := G) iota.prime
  let n := primeRegularExponent p G
  have hnpos : 0 < n := primeRegularExponent_pos p G
  let _ : NeZero n := ⟨hnpos.ne'⟩
  have hcop : n.Coprime p := by
    exact (Nat.coprime_ordCompl iota.prime Nat.card_pos.ne').symm
  have hnot : ¬p ∣ n := iota.prime.coprime_iff_not_dvd.mp hcop.symm
  let _ : NeZero (n : k) := ⟨by
    intro hzero
    exact hnot ((CharP.cast_eq_zero_iff k p n).mp hzero)⟩
  obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.prim (M := k) (n := n)
  let a : Matrix (SimpleIndex (k := k) (G := G))
      (SimpleIndex (k := k) (G := G))
      (Multiset (rootsOfUnity n k)) := fun X j ↦
    BrauerTraceRecovery.charpolyRootsOfUnity
      (simpleClassFDRep X).ρ iota (x j)
  have hsource : Matrix.det
      (fun X j ↦ ((a X j).map fun z ↦
        (((z : rootsOfUnity n k) : kˣ) : k)).sum) ≠ 0 := by
    have hmatrix :
        (fun X j ↦ ((a X j).map fun z ↦
          (((z : rootsOfUnity n k) : kˣ) : k)).sum) =
        (fun X j ↦ (simpleClassFDRep X).character (x j).1) := by
      funext X j
      rw [show ((a X j).map fun z ↦
          (((z : rootsOfUnity n k) : kˣ) : k)) =
          ((simpleClassFDRep X).ρ (x j).1).charpoly.roots by
        exact BrauerTraceRecovery.charpolyRootsOfUnity_map_source
          (simpleClassFDRep X).ρ iota (x j)]
      change ((simpleClassFDRep X).ρ (x j).1).charpoly.roots.sum =
        LinearMap.trace k (simpleClassFDRep X) ((simpleClassFDRep X).ρ (x j).1)
      exact (Module.End.trace_eq_sum_roots_charpoly_of_splits
        (IsAlgClosed.splits
          ((simpleClassFDRep X).ρ (x j).1).charpoly)).symm
    rw [hmatrix]
    exact hx
  have himage :=
    CyclotomicDeterminantSpecialization.rootMultisetMatrix_det_ne_zero_transfer
      hnpos iota.toMulEquiv hzeta a hsource
  refine ⟨x, ?_⟩
  have hmatrix :
      (fun X j ↦ ((a X j).map fun z ↦
        (((iota.toMulEquiv z : rootsOfUnity n K) : Kˣ) : K)).sum) =
      (fun X j ↦ simpleClassBrauerFamily iota X (x j)) := by
    funext X j
    rw [show ((a X j).map fun z ↦
        (((iota.toMulEquiv z : rootsOfUnity n K) : Kˣ) : K)) =
        ((simpleClassFDRep X).ρ (x j).1).charpoly.roots.map iota.lift by
      exact BrauerTraceRecovery.charpolyRootsOfUnity_map_image
        (simpleClassFDRep X).ρ iota (x j)]
    rfl
  rw [← hmatrix]
  exact himage

/-- The function-valued irreducible Brauer characters indexed by simple
module classes are linearly independent over the target field. -/
theorem irreducibleBrauerCharacterLinearIndependence_of_rootEmbedding
    (iota : PrimeRegularRootEmbedding p k K G) :
    IrreducibleBrauerCharacterLinearIndependence iota := by
  classical
  let _ := Fintype.ofFinite (SimpleIndex (k := k) (G := G))
  obtain ⟨x, hx⟩ :=
    exists_simpleClass_primeRegular_brauer_det_ne_zero iota
  have hrows : LinearIndependent K
      (fun X j ↦ simpleClassBrauerFamily iota X (x j)) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hx
  change LinearIndependent K (simpleClassBrauerFamily iota)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcEval : Fintype.linearCombination K
      (fun X j ↦ simpleClassBrauerFamily iota X (x j)) c = 0 := by
    funext j
    have hj := congrFun hc (x j)
    simpa [Fintype.linearCombination_apply] using hj
  have hc0 : c = 0 :=
    hrows.fintypeLinearCombination_injective (by simpa using hcEval)
  intro i
  exact congrFun hc0 i

/-- The literal family indexed by the function-valued set `IBr` is linearly
independent. -/
theorem irreducibleBrauerCharacters_linearIndependent
    (iota : PrimeRegularRootEmbedding p k K G) :
    LinearIndependent K (fun phi : IBr iota ↦ phi.1.toFun) := by
  let hinj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let e := simpleModuleClassEquivIBr iota hinj
  have h :=
    (irreducibleBrauerCharacterLinearIndependence_of_rootEmbedding iota).comp
      e.symm e.symm.injective
  change LinearIndependent K
    (fun phi : IBr iota ↦ (e (e.symm phi)).1.toFun) at h
  simpa only [Equiv.apply_symm_apply] using h

end ModularRep.FDRepSimpleClassKZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
