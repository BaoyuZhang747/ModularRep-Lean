import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.LinearAlgebra.Matrix.Notation
import ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter

/-!
# The quaternion factor in the corrected odd characteristic construction

For a field of odd characteristic, this file constructs an explicit faithful
two dimensional symplectic representation of `QuaternionGroup 2`, of the
abstract type required for an `E_-^3` factor.  The matrices

`i = !![0, 1; -1, 0]` and `j = !![a, b; b, -a]`

satisfy the quaternion relations whenever `a^2 + b^2 = -1`.  Existence of
such `a` and `b` follows in positive characteristic from
`CharP.sq_add_sq`.  The image is therefore a concrete subgroup of the
isometry group of the standard alternating form, rather than an abstract
subgroup supplied as an input to the Proposition 3.3 adapter.

This module does not identify that image with a subgroup named in the
classification literature.  In particular, when Feng--Yu--Zhang permit two
isometry-group conjugacy classes, it does not prove that this image is their
source-labelled `alpha = 0` class used as the right tensor factor in equation
(3.35).  The resulting full even-multiplicity factor has index `alpha = 1`.
That source-class identification, the coordinate
permutation group, the remaining direct factors, and the ambient block
diagonal realisation remain separate typed inputs.
-/

open Matrix

namespace ModularRep.PaperProofs.OddTwoQuaternionFactor

variable {F : Type*} [Field F]

def omega : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]
def iMatrix : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]
def jMatrix (a b : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; b, -a]

theorem omega_transpose : (omega (F := F))ᵀ = -omega := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omega]

theorem omega_det : Matrix.det (omega (F := F)) = 1 := by
  simp [omega, Matrix.det_fin_two_of]

theorem omega_det_ne_zero : Matrix.det (omega (F := F)) ≠ 0 := by
  rw [omega_det]
  exact one_ne_zero

theorem i_sq : iMatrix (F := F) * iMatrix = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [iMatrix, Matrix.mul_apply]

theorem j_sq {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    jMatrix a b * jMatrix a b = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [jMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals try ring
  all_goals simpa [add_comm] using hab

theorem ij_neg_ji (a b : F) :
    iMatrix * jMatrix a b = -(jMatrix a b * iMatrix) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [iMatrix, jMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem i_preserves :
    (iMatrix (F := F))ᵀ * omega * iMatrix = omega := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [iMatrix, omega, Matrix.mul_apply, Fin.sum_univ_two]

theorem j_preserves {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    (jMatrix a b)ᵀ * omega * jMatrix a b = omega := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [jMatrix, omega, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals try ring
  all_goals
    first
    | simpa [add_comm] using hab
    | have hneg := congrArg Neg.neg hab
      simpa [sub_eq_add_neg, add_comm] using hneg

noncomputable def iGL : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero iMatrix (by
    simp [iMatrix, Matrix.det_fin_two_of])

noncomputable def jGL (a b : F) (hab : a ^ 2 + b ^ 2 = -1) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (jMatrix a b) (by
    unfold jMatrix
    rw [Matrix.det_fin_two_of]
    have h : -(a ^ 2 + b ^ 2) = 1 := by rw [hab]; simp
    have hdet : a * -a - b * b = 1 := by
      simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    rw [hdet]
    exact one_ne_zero)

@[simp] theorem iGL_coe :
    ↑(iGL (F := F)) = (iMatrix (F := F) : Matrix (Fin 2) (Fin 2) F) := rfl
@[simp] theorem jGL_coe (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    ↑(jGL a b hab) = jMatrix a b := rfl

noncomputable def iIso :
  ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
      (omega (F := F)) :=
  ⟨iGL (F := F), i_preserves⟩

noncomputable def jIso (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
      (omega (F := F)) :=
  ⟨jGL a b hab, j_preserves hab⟩

theorem iIso_sq_matrix :
    ↑((iIso (F := F)) ^ 2).1 = (-1 : Matrix (Fin 2) (Fin 2) F) := by
  simpa only [pow_two, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    iIso, iGL_coe] using i_sq (F := F)

theorem iIso_pow_four : (iIso (F := F)) ^ 4 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (iMatrix (F := F)) ^ 4 = 1
  simp only [show (4 : ℕ) = 2 + 2 by omega, pow_add, pow_two]
  rw [i_sq]
  simp

theorem jIso_sq_eq_iIso_sq (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    (jIso a b hab) ^ 2 = (iIso (F := F)) ^ 2 := by
  apply Subtype.ext
  apply Units.ext
  change (jMatrix a b) ^ 2 = (iMatrix (F := F)) ^ 2
  simp only [pow_two]
  rw [j_sq hab, i_sq]

theorem iIso_mul_jIso_eq_iIso_sq_mul (a b : F)
    (hab : a ^ 2 + b ^ 2 = -1) :
    iIso * jIso a b hab = iIso ^ 2 * (jIso a b hab * iIso) := by
  apply Subtype.ext
  apply Units.ext
  change iMatrix * jMatrix a b = iMatrix ^ 2 * (jMatrix a b * iMatrix)
  simp only [pow_two]
  rw [i_sq]
  simpa using ij_neg_ji (F := F) a b

theorem iIso_mul_jIso_eq_jIso_mul_iIso_cube (a b : F)
    (hab : a ^ 2 + b ^ 2 = -1) :
    iIso * jIso a b hab = jIso a b hab * iIso ^ 3 := by
  apply Subtype.ext
  apply Units.ext
  change iMatrix * jMatrix a b = jMatrix a b * iMatrix ^ 3
  rw [show (3 : ℕ) = 2 + 1 by omega, pow_add, pow_one, pow_two, i_sq]
  simpa [mul_assoc] using ij_neg_ji (F := F) a b

noncomputable def iZModAddHom :
    ZMod 4 →+
      Additive
        (ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
          (omega (F := F))) :=
  ZMod.lift 4 ⟨zmultiplesHom _ (Additive.ofMul (iIso (F := F))), by
    change (4 : ℤ) • Additive.ofMul (iIso (F := F)) = 0
    rw [ofNat_zsmul]
    change Additive.ofMul ((iIso (F := F)) ^ 4) = 0
    rw [iIso_pow_four]
    rfl⟩

noncomputable def iZModHom :
    Multiplicative (ZMod 4) →*
      ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
        (omega (F := F)) :=
  ((MulEquiv.multiplicativeAdditive _).toMonoidHom).comp
    (iZModAddHom (F := F)).toMultiplicative

@[simp] theorem iZModHom_apply (k : ZMod 4) :
    iZModHom (F := F) (Multiplicative.ofAdd k) = iIso ^ k.val := by
  change (iZModAddHom (F := F) k).toMul = iIso ^ k.val
  have hk : k = ((k.val : ℤ) : ZMod 4) := by
    simpa using (ZMod.natCast_zmod_val k).symm
  have hvalue :
      iZModAddHom (F := F) k = Additive.ofMul (iIso (F := F) ^ k.val) := by
    calc
      iZModAddHom (F := F) k =
          iZModAddHom (F := F) ((k.val : ℤ) : ZMod 4) := congrArg _ hk
      _ = Additive.ofMul (iIso (F := F) ^ k.val) := by
        unfold iZModAddHom
        rw [ZMod.lift_coe]
        change (k.val : ℤ) • Additive.ofMul (iIso (F := F)) =
          Additive.ofMul (iIso (F := F) ^ k.val)
        rw [natCast_zsmul]
        rfl
  rw [hvalue]
  rfl

theorem exists_quaternion_parameters (p : ℕ) [NeZero p] [CharP F p] :
    ∃ a b : F, a ^ 2 + b ^ 2 = -1 := by
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F p (-1 : ℤ)
  exact ⟨(a : F), (b : F), by simpa using hab⟩

theorem iIso_mul_jIso_eq_jIso_mul_iIso_inv (a b : F)
    (hab : a ^ 2 + b ^ 2 = -1) :
    iIso * jIso a b hab = jIso a b hab * (iIso (F := F))⁻¹ := by
  rw [iIso_mul_jIso_eq_jIso_mul_iIso_cube]
  congr 1
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ' (iIso (F := F)) 3]
  exact iIso_pow_four (F := F)

theorem iIso_pow_mul_jIso (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (n : ℕ) :
    (iIso (F := F)) ^ n * jIso a b hab =
      jIso a b hab * ((iIso (F := F)) ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        iIso ^ (n + 1) * jIso a b hab =
            iIso ^ n * (iIso * jIso a b hab) := by simp [pow_succ, mul_assoc]
        _ = iIso ^ n * (jIso a b hab * iIso⁻¹) := by
          rw [iIso_mul_jIso_eq_jIso_mul_iIso_inv]
        _ = (iIso ^ n * jIso a b hab) * iIso⁻¹ := by simp [mul_assoc]
        _ = (jIso a b hab * (iIso ^ n)⁻¹) * iIso⁻¹ := by rw [ih]
        _ = jIso a b hab * (iIso ^ (n + 1))⁻¹ := by group

theorem iZModHom_mul_jIso (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (k : ZMod 4) :
    iZModHom (F := F) (Multiplicative.ofAdd k) * jIso a b hab =
      jIso a b hab * iZModHom (F := F) (Multiplicative.ofAdd (-k)) := by
  rw [iZModHom_apply, iIso_pow_mul_jIso]
  congr 1
  have hinv :
      iZModHom (F := F) (Multiplicative.ofAdd (-k)) =
        (iZModHom (F := F) (Multiplicative.ofAdd k))⁻¹ := by
    exact (iZModHom (F := F)).map_inv (Multiplicative.ofAdd k)
  rw [← iZModHom_apply (F := F) k]
  exact hinv.symm

theorem jIso_sq_eq_iZModHom_two (a b : F)
    (hab : a ^ 2 + b ^ 2 = -1) :
    jIso a b hab * jIso a b hab =
      iZModHom (F := F) (Multiplicative.ofAdd (2 : ZMod 4)) := by
  rw [← pow_two, jIso_sq_eq_iIso_sq, iZModHom_apply]
  have hval : (2 : ZMod 4).val = 2 := by decide
  rw [hval]

noncomputable def quaternionEmbedding (a b : F)
    (hab : a ^ 2 + b ^ 2 = -1) :
    QuaternionGroup 2 →*
      ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
        (omega (F := F)) where
  toFun
    | QuaternionGroup.a k => iZModHom (F := F) (Multiplicative.ofAdd k)
    | QuaternionGroup.xa k =>
        jIso a b hab * iZModHom (F := F) (Multiplicative.ofAdd k)
  map_one' := (iZModHom (F := F)).map_one
  map_mul' := by
    rintro (k | k) (l | l)
    · exact (iZModHom (F := F)).map_mul _ _
    · change jIso a b hab * iZModHom (Multiplicative.ofAdd (l - k)) =
        iZModHom (Multiplicative.ofAdd k) *
          (jIso a b hab * iZModHom (Multiplicative.ofAdd l))
      rw [← mul_assoc, iZModHom_mul_jIso, mul_assoc, ← map_mul]
      congr 2
      apply_fun Multiplicative.toAdd
      change l - k = -k + l
      abel
    · change jIso a b hab * iZModHom (Multiplicative.ofAdd (k + l)) =
        (jIso a b hab * iZModHom (Multiplicative.ofAdd k)) *
          iZModHom (Multiplicative.ofAdd l)
      rw [mul_assoc, ← map_mul]
      congr 2
    · change iZModHom (Multiplicative.ofAdd (2 + l - k)) =
        (jIso a b hab * iZModHom (Multiplicative.ofAdd k)) *
          (jIso a b hab * iZModHom (Multiplicative.ofAdd l))
      symm
      calc
        (jIso a b hab * iZModHom (Multiplicative.ofAdd k)) *
            (jIso a b hab * iZModHom (Multiplicative.ofAdd l)) =
          jIso a b hab *
            (iZModHom (Multiplicative.ofAdd k) * jIso a b hab) *
              iZModHom (Multiplicative.ofAdd l) := by group
        _ = jIso a b hab *
            (jIso a b hab * iZModHom (Multiplicative.ofAdd (-k))) *
              iZModHom (Multiplicative.ofAdd l) := by
          rw [iZModHom_mul_jIso]
        _ = (jIso a b hab * jIso a b hab) *
            (iZModHom (Multiplicative.ofAdd (-k)) *
              iZModHom (Multiplicative.ofAdd l)) := by group
        _ = iZModHom (Multiplicative.ofAdd (2 : ZMod 4)) *
            (iZModHom (Multiplicative.ofAdd (-k)) *
              iZModHom (Multiplicative.ofAdd l)) := by
          rw [jIso_sq_eq_iZModHom_two]
        _ = iZModHom (Multiplicative.ofAdd (2 + l - k)) := by
          rw [← map_mul, ← map_mul]
          congr 2
          apply_fun Multiplicative.toAdd
          change (2 : ZMod 4) + (-k + l) = 2 + l - k
          abel

def traceTwo (M : Matrix (Fin 2) (Fin 2) F) : F := M 0 0 + M 1 1

theorem jIso_mul_iZModHom_traceTwo (a b : F)
    (hab : a ^ 2 + b ^ 2 = -1) (k : ZMod 4) :
    traceTwo
      (↑(jIso a b hab *
        iZModHom (F := F) (Multiplicative.ofAdd k)).1 :
          Matrix (Fin 2) (Fin 2) F) = 0 := by
  rw [iZModHom_apply]
  have hk : k.val < 4 := ZMod.val_lt k
  interval_cases hval : k.val <;>
    simp [traceTwo, iIso, jIso, iGL, jGL, iMatrix, jMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem quaternionEmbedding_injective (a b : F)
    (hab : a ^ 2 + b ^ 2 = -1) (hTwo : (2 : F) ≠ 0) :
    Function.Injective (quaternionEmbedding a b hab) := by
  apply (injective_iff_map_eq_one (quaternionEmbedding a b hab)).2
  intro x hx
  cases x with
  | a k =>
    change iZModHom (F := F) (Multiplicative.ofAdd k) = 1 at hx
    rw [iZModHom_apply] at hx
    have hk : k.val < 4 := ZMod.val_lt k
    interval_cases hval : k.val
    · rw [(ZMod.val_eq_zero k).mp hval]
      rfl
    · exfalso
      have hentry := congrArg
        (fun g :
          ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
            (omega (F := F)) => (↑g.1 : Matrix (Fin 2) (Fin 2) F) 0 1) hx
      simpa [hval, iIso, iGL, iMatrix] using hentry
    · exfalso
      have hentry := congrArg
        (fun g :
          ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
            (omega (F := F)) => (↑g.1 : Matrix (Fin 2) (Fin 2) F) 0 0) hx
      have hnegOne : (-1 : F) ≠ 1 := by
        intro h
        apply hTwo
        have hadd := congrArg (fun x : F => x + 1) h
        simpa only [neg_add_cancel, one_add_one_eq_two] using hadd.symm
      exact hnegOne (by
        simpa [hval, iIso, iGL, iMatrix, pow_two,
          Matrix.mul_apply, Fin.sum_univ_two] using hentry)
    · exfalso
      have hentry := congrArg
        (fun g :
          ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
            (omega (F := F)) => (↑g.1 : Matrix (Fin 2) (Fin 2) F) 0 1) hx
      simpa [hval, iIso, iGL, iMatrix, pow_succ,
        Matrix.mul_apply, Fin.sum_univ_two] using hentry
  | xa k =>
    exfalso
    change jIso a b hab * iZModHom (F := F) (Multiplicative.ofAdd k) = 1 at hx
    have hTrace := jIso_mul_iZModHom_traceTwo a b hab k
    have hTraceOne := congrArg
      (fun g :
        ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
          (omega (F := F)) => traceTwo (↑g.1 : Matrix (Fin 2) (Fin 2) F)) hx
    have : (0 : F) = 2 := by
      rw [← hTrace]
      simpa [traceTwo, one_add_one_eq_two] using hTraceOne
    exact hTwo this.symm

noncomputable def quaternionRangeEquiv (a b : F)
    (hab : a ^ 2 + b ^ 2 = -1) (hTwo : (2 : F) ≠ 0) :
    QuaternionGroup 2 ≃*
      (quaternionEmbedding a b hab).range :=
  MulEquiv.ofBijective (quaternionEmbedding a b hab).rangeRestrict
    ⟨(fun _ _ h => quaternionEmbedding_injective a b hab hTwo
        (congrArg Subtype.val h)),
      MonoidHom.rangeRestrict_surjective (quaternionEmbedding a b hab)⟩

theorem two_ne_zero_of_charP (p : ℕ) [CharP F p] (hp : ¬ p ∣ 2) :
    (2 : F) ≠ 0 := by
  intro h
  exact hp ((CharP.cast_eq_zero_iff F p 2).mp h)

theorem exists_quaternion_isometry_subgroup (p : ℕ)
    [NeZero p] [CharP F p] (hp : ¬ p ∣ 2) :
    ∃ E : Subgroup
        (ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
          (omega (F := F))),
      Nonempty (QuaternionGroup 2 ≃* E) := by
  obtain ⟨a, b, hab⟩ := exists_quaternion_parameters (F := F) p
  let E := (quaternionEmbedding a b hab).range
  exact ⟨E, ⟨quaternionRangeEquiv a b hab (two_ne_zero_of_charP p hp)⟩⟩

/-! The following noncomputable choices turn the preceding existence theorem
into a literal finite-characteristic instance.  No source conjugacy class is
selected by this choice: `canonicalQuaternionParameters_spec` supplies only
the matrix relation used below. -/

noncomputable def canonicalQuaternionParameterA (p : ℕ)
    [NeZero p] [CharP F p] : F :=
  Classical.choose (exists_quaternion_parameters (F := F) p)

noncomputable def canonicalQuaternionParameterB (p : ℕ)
    [NeZero p] [CharP F p] : F :=
  Classical.choose
    (Classical.choose_spec (exists_quaternion_parameters (F := F) p))

theorem canonicalQuaternionParameters_spec (p : ℕ)
    [NeZero p] [CharP F p] :
    canonicalQuaternionParameterA (F := F) p ^ 2 +
        canonicalQuaternionParameterB (F := F) p ^ 2 = -1 :=
  Classical.choose_spec
    (Classical.choose_spec (exists_quaternion_parameters (F := F) p))

noncomputable def canonicalQuaternionEmbedding (p : ℕ)
    [NeZero p] [CharP F p] :
    QuaternionGroup 2 →*
      ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
        (omega (F := F)) :=
  quaternionEmbedding
    (canonicalQuaternionParameterA (F := F) p)
    (canonicalQuaternionParameterB (F := F) p)
    (canonicalQuaternionParameters_spec (F := F) p)

noncomputable def canonicalQuaternionSubgroup (p : ℕ)
    [NeZero p] [CharP F p] :
    Subgroup
      (ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter.FormIsometryGroup
        (omega (F := F))) :=
  (canonicalQuaternionEmbedding (F := F) p).range

theorem canonicalQuaternionEmbedding_injective (p : ℕ)
    [NeZero p] [CharP F p] (hp : ¬ p ∣ 2) :
    Function.Injective (canonicalQuaternionEmbedding (F := F) p) :=
  quaternionEmbedding_injective
    (canonicalQuaternionParameterA (F := F) p)
    (canonicalQuaternionParameterB (F := F) p)
    (canonicalQuaternionParameters_spec (F := F) p)
    (two_ne_zero_of_charP p hp)

noncomputable def canonicalQuaternionRangeEquiv (p : ℕ)
    [NeZero p] [CharP F p] (hp : ¬ p ∣ 2) :
    QuaternionGroup 2 ≃* canonicalQuaternionSubgroup (F := F) p :=
  MulEquiv.ofBijective
    (canonicalQuaternionEmbedding (F := F) p).rangeRestrict
    ⟨(fun _ _ h => canonicalQuaternionEmbedding_injective (F := F) p hp
        (congrArg Subtype.val h)),
      MonoidHom.rangeRestrict_surjective
        (canonicalQuaternionEmbedding (F := F) p)⟩

section SourceAdapter

open OddTwoCorrectedFactorAdapter

universe v w x y

variable {I : Type v} {A : Type w} {Omega : Type x} {K G : Type y}
variable [Fintype I] [DecidableEq I]
variable [Group A] [Group K] [Group G] [Nonempty Omega]

/-- The corrected-factor adapter with the right tensor factor instantiated by
the explicit quaternion representation above.  The conclusion also records
that the concrete factor really is `Q_8` in odd characteristic.

The equality `hR` is intentionally the remaining source-shaped input: it must
identify the subgroup named in the classification with this exact tensor,
wreath, remaining-factor, and ambient-image construction. -/
theorem source_identified_quaternion_factor_and_exclusion
    (a b : F) (hab : a ^ 2 + b ^ 2 = -1) (hTwo : (2 : F) ≠ 0)
    (JI : Matrix I I F) (rho : A →* Equiv.Perm Omega)
    (C : Subgroup K)
    (f : (CorrectedWreathGroup JI (omega (F := F)) rho × K) →* G)
    (hf : Function.Injective f)
    (t : FormIsometryGroup JI) (htSq : t ^ 2 = 1)
    (htNonscalar : ∀ c : F,
      (↑t.1 : Matrix I I F) ≠ c • (1 : Matrix I I F))
    (Rsource : Subgroup G)
    (hR : Rsource = correctedAmbientSubgroup JI (omega (F := F)) rho
      (quaternionEmbedding a b hab).range C f)
    (IsPrincipalWeight : Prop)
    (principalCentreSylow : IsPrincipalWeight →
      ∃ P : Sylow 2 (Subgroup.centralizer (Rsource : Set G)),
        (P : Subgroup (Subgroup.centralizer (Rsource : Set G))) =
          OddTwoWreathReflection.centreInCentralizer Rsource) :
    Nonempty (QuaternionGroup 2 ≃* (quaternionEmbedding a b hab).range) ∧
      ¬ IsPrincipalWeight := by
  constructor
  · exact ⟨quaternionRangeEquiv a b hab hTwo⟩
  · exact source_identified_corrected_even_multiplicity_factor_not_principal
      JI (omega (F := F)) rho (quaternionEmbedding a b hab).range C f hf
        t htSq htNonscalar Rsource hR IsPrincipalWeight principalCentreSylow

/-- The exclusion component of
`source_identified_quaternion_factor_and_exclusion`. -/
theorem source_identified_quaternion_factor_not_principal
    (a b : F) (hab : a ^ 2 + b ^ 2 = -1) (hTwo : (2 : F) ≠ 0)
    (JI : Matrix I I F) (rho : A →* Equiv.Perm Omega)
    (C : Subgroup K)
    (f : (CorrectedWreathGroup JI (omega (F := F)) rho × K) →* G)
    (hf : Function.Injective f)
    (t : FormIsometryGroup JI) (htSq : t ^ 2 = 1)
    (htNonscalar : ∀ c : F,
      (↑t.1 : Matrix I I F) ≠ c • (1 : Matrix I I F))
    (Rsource : Subgroup G)
    (hR : Rsource = correctedAmbientSubgroup JI (omega (F := F)) rho
      (quaternionEmbedding a b hab).range C f)
    (IsPrincipalWeight : Prop)
    (principalCentreSylow : IsPrincipalWeight →
      ∃ P : Sylow 2 (Subgroup.centralizer (Rsource : Set G)),
        (P : Subgroup (Subgroup.centralizer (Rsource : Set G))) =
          OddTwoWreathReflection.centreInCentralizer Rsource) :
    ¬ IsPrincipalWeight :=
  (source_identified_quaternion_factor_and_exclusion
    a b hab hTwo JI rho C f hf t htSq htNonscalar Rsource hR
      IsPrincipalWeight principalCentreSylow).2

end SourceAdapter

end ModularRep.PaperProofs.OddTwoQuaternionFactor


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
