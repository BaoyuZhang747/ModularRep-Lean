import ModularRep.PaperProofs.TypeBCliffordCarriers
import ModularRep.PaperProofs.TypeBCentralKernelBrauerBlocks
import ModularRep.PaperProofs.TypeBCharacteristicTwoConstituentSource
import ModularRep.LiteralOrdinaryPBlockSource
import ModularRep.BrauerDecompositionMap

/-!
# Specified decomposition numbers on the literal Spin carrier

The coefficients below are the nonnegative Jordan--Hölder coordinates of
the actual reduction of a stable lattice in an affording representation.
They are not supplied as an arbitrary matrix. Stable-reduction character
compatibility identifies them with the exact decomposition map and proves
their character expansion and automorphism naturality.

The ordinary block source is specialized to this very support relation and
to the primitive idempotents of the same modular group algebra. Navarro
2.11 remains a narrowly stated column-rank input on these coefficients.
Neither splitting nor root compatibility follows from `ModularSystem`.
In particular its fraction field is not assumed algebraically closed.
-/

noncomputable section
open scoped MonoidAlgebra BigOperators

namespace ModularRep.PaperProofs.TypeBSpinPrincipalDecompositionBinding

open ExactGrothendieckGroup FDRepSimpleClassKZero FDRepJordanHolderKZero
open OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks

universe u

section Coordinates

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G]

/-- Actual simple-factor coordinates, labelled by their Brauer characters. -/
def brauerCoordinates (iota : PrimeRegularRootEmbedding p k K G) :
    FDRepKZero k G →+ (IBr iota →₀ ℤ) :=
  FreeAbelianGroup.toFinsupp.comp
    ((FreeAbelianGroup.map (simpleClassToIBr iota)).comp fdRepSimpleJordanHolderHom)

theorem brauerCoordinates_simple (iota : PrimeRegularRootEmbedding p k K G)
    (X : SimpleModuleClass k[G]) :
    brauerCoordinates iota (simpleClassToFDRepKZeroGenerator X) =
      Finsupp.single (simpleClassToIBr iota X) 1 := by
  simp [brauerCoordinates]

/-- Nonnegativity is proved on an actual module, by counting its factors. -/
theorem brauerCoordinates_nonneg (iota : PrimeRegularRootEmbedding p k K G)
    (V : FDRep k G) (phi : IBr iota) :
    0 ≤ brauerCoordinates iota (classOf (FDRep k G) V) phi := by
  classical
  simp only [brauerCoordinates, AddMonoidHom.comp_apply,
    fdRepSimpleJordanHolderHom_classOf, compositionFactorSimpleSum,
    map_sum, FreeAbelianGroup.map_of_apply, FreeAbelianGroup.toFinsupp_of,
    Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg (fun i _ => by
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num)

private def brauerFunctionHom (iota : PrimeRegularRootEmbedding p k K G) :
    FDRepKZero k G →+ PrimeRegularFunction K G p where
  toFun x := (brauerCharacterKZeroHom iota x).toFun
  map_zero' := by rw [map_zero]; rfl
  map_add' x y := by rw [map_add]; rfl

/-- The coordinates reconstruct the actual function-valued Brauer character. -/
theorem brauerCoordinates_character (iota : PrimeRegularRootEmbedding p k K G)
    (x : FDRepKZero k G) :
    Finsupp.linearCombination ℤ (fun phi : IBr iota => phi.val.toFun)
        (brauerCoordinates iota x) =
      (brauerCharacterKZeroHom iota x).toFun := by
  have h :
      ((Finsupp.linearCombination ℤ (fun phi : IBr iota => phi.val.toFun)).toAddMonoidHom.comp
        (brauerCoordinates iota)).comp simpleClassToFDRepKZero =
      (brauerFunctionHom iota).comp simpleClassToFDRepKZero := by
    apply FreeAbelianGroup.lift_ext
    intro X
    change (Finsupp.linearCombination ℤ (fun phi : IBr iota => phi.val.toFun))
        (brauerCoordinates iota (simpleClassToFDRepKZeroGenerator X)) =
      brauerFunctionHom iota (simpleClassToFDRepKZeroGenerator X)
    rw [brauerCoordinates_simple, Finsupp.linearCombination_single, one_smul]
    change (Representation.brauerCharacterOfRootEmbedding (simpleClassFDRep X).ρ iota).toFun =
      (brauerCharacterKZeroHom iota (classOf (FDRep k G) (simpleClassFDRep X))).toFun
    rw [brauerCharacterKZeroHom_classOf]
  have hx := congrArg (fun h => h (fdRepSimpleJordanHolderHom x)) h
  simp only [AddMonoidHom.comp_apply,
    simpleClassToFDRepKZero_fdRepSimpleJordanHolderHom] at hx
  exact hx

end Coordinates

section Spin

variable {n : ℕ} {F K O k : Type u} [Field F]
  {N : NormSource n F} [Finite (Spin n F N)]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]

variable (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))

/-- A chosen actual representation affording this ordinary character. -/
def ordinaryRepresentation (chi : Irr K (Spin n F N)) : FDRep K (Spin n F N) :=
  FDRep.of (Classical.choice chi.property).representation

theorem ordinaryRepresentation_character (chi : Irr K (Spin n F N)) :
    (ordinaryRepresentation chi).character = chi.val :=
  (Classical.choice chi.property).character_eq

/-- Integer coordinates of the literal stable-lattice reduction. -/
def decompositionRow (chi : Irr K (Spin n F N)) : IBr iota →₀ ℤ :=
  brauerCoordinates iota (chosenReductionClass Msys (ordinaryRepresentation chi))

theorem decompositionRow_nonneg (chi : Irr K (Spin n F N)) (phi : IBr iota) :
    0 ≤ decompositionRow Msys iota chi phi :=
  brauerCoordinates_nonneg iota
    (stableLatticeReduction Msys (ordinaryRepresentation chi)
      (chosenStableLattice O (ordinaryRepresentation chi))) phi

/-- The actual nonnegative decomposition multiplicity, not an input matrix. -/
def decompositionNumber (chi : Irr K (Spin n F N)) (phi : IBr iota) : ℕ :=
  (decompositionRow Msys iota chi phi).toNat

theorem decompositionNumber_int (chi : Irr K (Spin n F N)) (phi : IBr iota) :
    (decompositionNumber Msys iota chi phi : ℤ) = decompositionRow Msys iota chi phi :=
  Int.toNat_of_nonneg (decompositionRow_nonneg Msys iota chi phi)

variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)

/-- Identification with the existing exact decomposition map. -/
theorem decompositionRow_exact (chi : Irr K (Spin n F N)) :
    decompositionRow Msys iota chi = brauerCoordinates iota
      (decompositionMapOfStableReduction Msys iota hcompat
        (classOf (FDRep K (Spin n F N)) (ordinaryRepresentation chi))) := by
  apply congrArg (brauerCoordinates iota)
  apply brauerCharacterKZeroHom_injective iota
  have hchosen := ExactCharacterBridge.chosenReductionClass_compatible Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat) (ordinaryRepresentation chi)
  have hexact := congrArg
    (fun h => h (classOf (FDRep K (Spin n F N)) (ordinaryRepresentation chi)))
    (decompositionMapOfStableReduction_characterSquare Msys iota hcompat)
  exact hchosen.trans hexact.symm

include hcompat in
/-- Navarro 2.9's literal prime regular expansion follows from reduction. -/
theorem decompositionRow_character (chi : Irr K (Spin n F N)) :
    Finsupp.linearCombination ℤ (fun phi : IBr iota => phi.val.toFun)
        (decompositionRow Msys iota chi) =
      fun x : PrimeRegularElement (G := Spin n F N) 2 => chi x.val := by
  rw [decompositionRow, brauerCoordinates_character]
  have hchosen := ExactCharacterBridge.chosenReductionClass_compatible Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat) (ordinaryRepresentation chi)
  change brauerCharacterKZeroHom iota _ = ordinaryCharacterKZero 2 _ at hchosen
  rw [hchosen]
  funext x
  rw [ordinaryCharacterKZero_classOf_apply]
  exact congrFun (ordinaryRepresentation_character chi) x.val

include hcompat in
/-- Coefficient naturality is a deduction from the same character expansion. -/
theorem decompositionRow_twist (alpha : MulAut (Spin n F N))
    (chi : Irr K (Spin n F N)) :
    decompositionRow Msys iota (OrdinaryIrreducibleCharacter.twist K _ chi alpha) =
      Finsupp.equivMapDomain (TypeBCharacteristicTwoConstituentSource.twistEquiv iota alpha)
        (decompositionRow Msys iota chi) := by
  apply (((irreducibleBrauerCharacters_linearIndependent iota).restrict_scalars' ℤ).finsuppLinearCombination_injective)
  rw [decompositionRow_character Msys iota hcompat,
    Finsupp.linearCombination_equivMapDomain]
  have hrow := decompositionRow_character Msys iota hcompat chi
  funext x
  have hx := congrFun hrow (PrimeRegularElement.map alpha.toMonoidHom x)
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_apply',
    Function.comp_apply, Pi.smul_apply] at hx ⊢
  change chi (alpha x.val) = (decompositionRow Msys iota chi).sum
    (fun phi a => a • phi.val (PrimeRegularElement.map alpha.toMonoidHom x))
  change (decompositionRow Msys iota chi).sum
    (fun phi a => a • phi.val (PrimeRegularElement.map alpha.toMonoidHom x)) =
      chi (alpha x.val) at hx
  exact hx.symm

include hcompat in
theorem decompositionNumber_twist (alpha : MulAut (Spin n F N))
    (chi : Irr K (Spin n F N)) (phi : IBr iota) :
    decompositionNumber Msys iota (OrdinaryIrreducibleCharacter.twist K _ chi alpha)
        (IrreducibleBrauerCharacter.twist iota phi alpha) =
      decompositionNumber Msys iota chi phi := by
  unfold decompositionNumber
  rw [decompositionRow_twist Msys iota hcompat]
  exact congrArg Int.toNat
    (show Finsupp.equivMapDomain
      (TypeBCharacteristicTwoConstituentSource.twistEquiv iota alpha)
      (decompositionRow Msys iota chi)
      ((TypeBCharacteristicTwoConstituentSource.twistEquiv iota alpha) phi) = _ by
        simp only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply])

include hcompat in
theorem decomposition_expansion [Fintype (IBr iota)]
    (chi : Irr K (Spin n F N)) (x : PrimeRegularElement (G := Spin n F N) 2) :
    chi x.val = ∑ phi : IBr iota, (decompositionNumber Msys iota chi phi : K) * phi.val x := by
  have h := congrFun (decompositionRow_character Msys iota hcompat chi) x
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_apply', Pi.smul_apply] at h
  change (decompositionRow Msys iota chi).sum
    (fun phi a => a • phi.val x) = chi x.val at h
  calc
    chi x.val = (decompositionRow Msys iota chi).sum (fun phi a => a • phi.val x) := h.symm
    _ = ∑ phi : IBr iota, (decompositionRow Msys iota chi phi) • phi.val x :=
      Finsupp.sum_fintype (decompositionRow Msys iota chi)
        (fun (phi : IBr iota) (a : ℤ) => a • phi.val x) (fun _ => zero_smul ℤ _)
    _ = ∑ phi : IBr iota, (decompositionNumber Msys iota chi phi : K) * phi.val x := by
      apply Finset.sum_congr rfl
      intro phi _
      exact (congrArg (fun a : ℤ => a • phi.val x)
        (decompositionNumber_int Msys iota chi phi).symm).trans
        ((natCast_zsmul (phi.val x) (decompositionNumber Msys iota chi phi)).trans
          (nsmul_eq_mul (decompositionNumber Msys iota chi phi) (phi.val x)))

variable [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin n F N) => b.val))

/-- Navarro ordinary block selector, with its support fixed to our specified d.
Its realization in the chosen adequate splitting modular system is E1/U. -/
abbrev OrdinaryBlockSource :=
  LiteralOrdinaryPBlockSource iota (injective iota) blocks
    (fun chi phi => decompositionNumber Msys iota chi phi ≠ 0)

theorem literalBrauerBlock_eq (phi : IBr iota) :
    literalBrauerBlock iota (injective iota) blocks phi = block iota blocks phi := by
  apply Subtype.ext
  rfl

variable (source : OrdinaryBlockSource Msys iota blocks)

theorem supported_of_decompositionNumber_ne_zero (chi : Irr K (Spin n F N))
    (phi : IBr iota) (h : decompositionNumber Msys iota chi phi ≠ 0) :
    Supported iota (source.ordinaryBlock chi) phi := by
  apply (supported_iff_block iota blocks _ phi).mpr
  exact (literalBrauerBlock_eq iota blocks phi).symm.trans
    ((source.support_nonempty_and_sound chi).2 phi h)

theorem ordinaryBlock_eq_iff (chi : Irr K (Spin n F N))
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    source.ordinaryBlock chi = b ↔
      ∃ phi : IBr iota, decompositionNumber Msys iota chi phi ≠ 0 ∧ Supported iota b phi := by
  constructor
  · intro hb
    obtain ⟨phi, hphi⟩ := (source.support_nonempty_and_sound chi).1
    exact ⟨phi, hphi, hb ▸ supported_of_decompositionNumber_ne_zero Msys iota blocks source chi phi hphi⟩
  · rintro ⟨phi, hphi, hsupp⟩
    exact ((source.support_nonempty_and_sound chi).2 phi hphi).symm.trans
      ((literalBrauerBlock_eq iota blocks phi).trans
        ((supported_iff_block iota blocks b phi).mp hsupp))

theorem decompositionNumber_zero_of_other_block (chi : Irr K (Spin n F N))
    (phi : IBr iota) (h : ¬ Supported iota (source.ordinaryBlock chi) phi) :
    decompositionNumber Msys iota chi phi = 0 := by
  by_contra hn
  exact h (supported_of_decompositionNumber_ne_zero Msys iota blocks source chi phi hn)

include hcompat in
theorem ordinaryBlock_twist (alpha : MulAut (Spin n F N))
    (chi : Irr K (Spin n F N)) :
    source.ordinaryBlock (OrdinaryIrreducibleCharacter.twist K _ chi alpha) =
      LiteralPrimitiveBlock.rightTwistBlock (source.ordinaryBlock chi) alpha := by
  obtain ⟨phi, hphi⟩ := (source.support_nonempty_and_sound chi).1
  apply (ordinaryBlock_eq_iff Msys iota blocks source _ _).mpr
  refine ⟨IrreducibleBrauerCharacter.twist iota phi alpha, ?_, ?_⟩
  · simpa only [decompositionNumber_twist Msys iota hcompat] using hphi
  · exact supported_twist iota blocks _ alpha phi
      (supported_of_decompositionNumber_ne_zero Msys iota blocks source chi phi hphi)

/-- Exact Navarro 2.11 column rank on the physically constructed matrix.
The adequate ordinary splitting/root realization is still E1/U; this record
has no arbitrary coefficients, basis, projection, or fixation field. -/
structure DecompositionColumnIndependenceSource : Prop where
  independent : LinearIndependent K
    (fun phi : IBr iota => fun chi : Irr K (Spin n F N) =>
      (decompositionNumber Msys iota chi phi : K))

end Spin

end ModularRep.PaperProofs.TypeBSpinPrincipalDecompositionBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
