import ModularRep.PaperProofs.TypeBSpinRationalUnipotentClassBinding
import ModularRep.PaperProofs.TypeBGGGRRankProposition412Relative

/-!
# Component fibres for the actual Spin regular embedding

The component presentation and the compatible rational-class parametrisations
are explicit Taylor E2/U inputs. Their algebraic interpretation uses the same
regular embedding whose finite inclusion is the norm-kernel inclusion below.
The exceptional double fibre, all other singleton fibres, and the actual
ambient conjugation action are deductions, not source fields.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankGGGRFibres

open ModularRep TypeBCliffordCarriers TypeBSpinRationalUnipotentClassBinding

section Components

variable {A V : Type} [Group A] [CommGroup V]

/-- The part of Taylor's extraspecial component presentation used here.
The centre is exactly the kernel of the displayed quotient; no conjugacy
class or fibre-cardinality conclusion is included. Multiplicative `1` in
`V` is the manuscript's additive `0`. -/
structure ComponentPresentation (A V : Type) [Group A] [CommGroup V] where
  quotient : A →* V
  quotient_surjective : Function.Surjective quotient
  theta : A
  theta_ne_one : theta ≠ 1
  kernel : ∀ x, quotient x = 1 ↔ x = 1 ∨ x = theta
  centre_eq_kernel : Subgroup.center A = quotient.ker

namespace ComponentPresentation

variable (P : ComponentPresentation A V)

/-- The actual map on component conjugacy classes followed by the canonical
identification of conjugacy classes in the commutative upper component. -/
def classProjection : ConjClasses A → V :=
  fun c => ConjClasses.mkEquiv.symm (ConjClasses.map P.quotient c)

@[simp] theorem classProjection_mk (x : A) :
    P.classProjection (ConjClasses.mk x) = P.quotient x := rfl

theorem theta_in_kernel : P.quotient P.theta = 1 :=
  (P.kernel P.theta).2 (Or.inr rfl)

theorem classProjection_surjective : Function.Surjective P.classProjection := by
  intro v
  obtain ⟨x, hx⟩ := P.quotient_surjective v
  exact ⟨ConjClasses.mk x, hx⟩

/-- Noncentrality supplies a nontrivial commutator; the two-element kernel
then identifies it with theta. Thus the conjugacy witness is derived. -/
theorem conjugate_mul_theta (x : A) (hx : P.quotient x ≠ 1) :
    IsConj x (x * P.theta) := by
  classical
  have hnoncentral : x ∉ Subgroup.center A := by
    intro hc
    rw [P.centre_eq_kernel] at hc
    exact hx hc
  have hex : ∃ a : A, a * x ≠ x * a := by
    by_contra h
    apply hnoncentral
    apply Subgroup.mem_center_iff.mpr
    intro a
    by_contra ha
    exact h ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  let d := x⁻¹ * (a * x * a⁻¹)
  have hd : P.quotient d = 1 := by
    dsimp [d]
    simp only [map_mul, map_inv]
    simp [mul_comm, mul_left_comm, mul_assoc]
  have hdne : d ≠ 1 := by
    intro h
    have heq : a * x * a⁻¹ = x := (inv_mul_eq_one.mp h).symm
    exact ha (mul_inv_eq_iff_eq_mul.mp heq)
  have hdtheta : d = P.theta := ((P.kernel d).1 hd).resolve_left hdne
  apply isConj_iff.mpr
  refine ⟨a, ?_⟩
  calc
    a * x * a⁻¹ = x * d := by dsimp [d]; group
    _ = x * P.theta := by rw [hdtheta]

theorem same_quotient (x y : A) (h : P.quotient x = P.quotient y) :
    y = x ∨ y = x * P.theta := by
  have hk : P.quotient (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  rcases (P.kernel _).1 hk with heq | heq
  · exact Or.inl (inv_mul_eq_one.mp heq).symm
  · right
    calc
      y = x * (x⁻¹ * y) := by group
      _ = x * P.theta := by rw [heq]

theorem classProjection_eq_one_iff (c : ConjClasses A) :
    P.classProjection c = 1 ↔
      c = ConjClasses.mk (1 : A) ∨ c = ConjClasses.mk P.theta := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  constructor
  · intro h
    rcases (P.kernel x).1 h with hx | hx
    · exact Or.inl (congrArg ConjClasses.mk hx)
    · exact Or.inr (congrArg ConjClasses.mk hx)
  · rintro (h | h)
    · rw [h, P.classProjection_mk, map_one]
    · rw [h, P.classProjection_mk, P.theta_in_kernel]

theorem identity_class_ne_theta_class :
    ConjClasses.mk (1 : A) ≠ ConjClasses.mk P.theta := by
  intro h
  have hi := ConjClasses.mk_eq_mk_iff_isConj.mp h
  exact P.theta_ne_one (isConj_one_right.mp hi)

theorem nonidentity_fibre_subsingleton (v : V) (hv : v ≠ 1)
    (c d : ConjClasses A) (hc : P.classProjection c = v)
    (hd : P.classProjection d = v) : c = d := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  obtain ⟨y, rfl⟩ := ConjClasses.mk_surjective d
  rcases P.same_quotient x y (hc.trans hd.symm) with h | h
  · exact congrArg ConjClasses.mk h.symm
  · rw [h]
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact P.conjugate_mul_theta x
      (by simpa only [← hc, P.classProjection_mk] using hv)

end ComponentPresentation

end Components

/-- Inverse class maps are proved on an abstract group before specializing
to the nested Clifford subgroup carrier. -/
private theorem conjugacyClassMap_symm_apply {H : Type} [Group H]
    (beta : MulAut H) (c : ConjClasses H) :
    ConjClasses.map beta.symm.toMonoidHom
      (ConjClasses.map beta.toMonoidHom c) = c := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  change ConjClasses.mk (beta.symm (beta x)) = ConjClasses.mk x
  exact congrArg ConjClasses.mk (beta.symm_apply_apply x)

private theorem conjugacyClassMap_apply_symm {H : Type} [Group H]
    (beta : MulAut H) (c : ConjClasses H) :
    ConjClasses.map beta.toMonoidHom
      (ConjClasses.map beta.symm.toMonoidHom c) = c := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  change ConjClasses.mk (beta (beta.symm x)) = ConjClasses.mk x
  exact congrArg ConjClasses.mk (beta.apply_symm_apply x)

section ActualClasses

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  {N : NormSource n F} [Finite (Spin n F N)]

/-- Defining-prime unipotent classes on the literal special Clifford carrier. -/
def UpperUnipotentClass : Type :=
  {c : ConjClasses (SpecialClifford n F) //
    ∃ g : SpecialClifford n F, ConjClasses.mk g = c ∧
      ∃ a : ℕ, g ^ (r ^ a) = 1}

/-- The class map induced by the actual norm-kernel inclusion. -/
def upperClassMap (c : UnipotentClass (r := r) (N := N)) :
    UpperUnipotentClass (n := n) (F := F) (r := r) :=
  ⟨ConjClasses.map (SpinSubgroup n F N).subtype c.val, by
    obtain ⟨g, hg, a, ha⟩ := c.property
    refine ⟨g.val, ?_, a, ?_⟩
    · rw [← hg]
      rfl
    · exact (map_pow (SpinSubgroup n F N).subtype g (r ^ a)).symm.trans
        ((congrArg (SpinSubgroup n F N).subtype ha).trans
          (map_one (SpinSubgroup n F N).subtype))⟩

@[simp] theorem upperClassMap_val (c : UnipotentClass (r := r) (N := N)) :
    (upperClassMap c).val =
      ConjClasses.map (SpinSubgroup n F N).subtype c.val := rfl

/-- The literal forward class transport, with prime-power preservation. -/
def unipotentClassMap (beta : MulAut (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)) :
    UnipotentClass (r := r) (N := N) :=
  ⟨ConjClasses.map beta.toMonoidHom c.val, by
    obtain ⟨x, hx, a, ha⟩ := c.property
    refine ⟨beta x, ?_, a, ?_⟩
    · rw [← hx]
      rfl
    · rw [← map_pow, ha, map_one]⟩

private theorem unipotentClassMap_symm_apply (beta : MulAut (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)) :
    unipotentClassMap beta.symm (unipotentClassMap beta c) = c :=
  Subtype.ext (conjugacyClassMap_symm_apply beta c.val)

private theorem unipotentClassMap_apply_symm (beta : MulAut (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)) :
    unipotentClassMap beta (unipotentClassMap beta.symm c) = c :=
  Subtype.ext (conjugacyClassMap_apply_symm beta c.val)

/-- Transport of the actual lower unipotent class by a Spin automorphism. -/
def classAutomorphism (beta : MulAut (Spin n F N)) :
    Equiv.Perm (UnipotentClass (r := r) (N := N)) where
  toFun := unipotentClassMap beta
  invFun := unipotentClassMap beta.symm
  left_inv := unipotentClassMap_symm_apply beta
  right_inv := unipotentClassMap_apply_symm beta

theorem upperClassMap_conjugation (g : SpecialClifford n F)
    (c : UnipotentClass (r := r) (N := N)) :
    upperClassMap (classAutomorphism (MulAut.conjNormal
      (H := SpinSubgroup n F N) g) c) = upperClassMap c := by
  apply Subtype.ext
  obtain ⟨x, hx⟩ := ConjClasses.mk_surjective c.val
  change ConjClasses.map (SpinSubgroup n F N).subtype
    (ConjClasses.map (MulAut.conjNormal (H := SpinSubgroup n F N) g).toMonoidHom
      c.val) = ConjClasses.map (SpinSubgroup n F N).subtype c.val
  rw [← hx]
  change ConjClasses.mk (g * x.val * g⁻¹) = ConjClasses.mk x.val
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact (isConj_iff.mpr ⟨g, rfl⟩).symm

variable {GeometricClass : Type}
  (geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass)
  (upperGeometricClass : UpperUnipotentClass (n := n) (F := F) (r := r) → GeometricClass)
  (geometric_square : ∀ c, upperGeometricClass (upperClassMap c) = geometricClass c)

abbrev UpperRationalFibre (C : GeometricClass) :=
  {c : UpperUnipotentClass (n := n) (F := F) (r := r) // upperGeometricClass c = C}

def rationalClassMap (C : GeometricClass) (c : RationalFibre geometricClass C) :
    UpperRationalFibre upperGeometricClass C :=
  ⟨upperClassMap c.val, (geometric_square c.val).trans c.property⟩

/-- Ambient conjugation preserves the geometric fibre, derived through the
same inclusion square and its fixation of the upper rational class. -/
def ambientClassEquiv (C : GeometricClass) (g : SpecialClifford n F) :
    Equiv.Perm (RationalFibre geometricClass C) where
  toFun c := ⟨classAutomorphism (MulAut.conjNormal (H := SpinSubgroup n F N) g) c.val,
    by rw [← geometric_square, upperClassMap_conjugation, geometric_square]; exact c.property⟩
  invFun c := ⟨(classAutomorphism (MulAut.conjNormal (H := SpinSubgroup n F N) g)).symm c.val,
    by
      rw [← geometric_square]
      have h := upperClassMap_conjugation g
        ((classAutomorphism (MulAut.conjNormal (H := SpinSubgroup n F N) g)).symm c.val)
      rw [(classAutomorphism (MulAut.conjNormal (H := SpinSubgroup n F N) g)).apply_symm_apply]
        at h
      rw [← h, geometric_square]
      exact c.property⟩
  left_inv c := Subtype.ext ((classAutomorphism
    (MulAut.conjNormal (H := SpinSubgroup n F N) g)).symm_apply_apply c.val)
  right_inv c := Subtype.ext ((classAutomorphism
    (MulAut.conjNormal (H := SpinSubgroup n F N) g)).apply_symm_apply c.val)

@[simp] theorem ambientClassEquiv_val (C : GeometricClass) (g : SpecialClifford n F)
    (c : RationalFibre geometricClass C) :
    (ambientClassEquiv geometricClass upperGeometricClass geometric_square C g c).val.val =
      ConjClasses.map (MulAut.conjNormal (H := SpinSubgroup n F N) g).toMonoidHom
        c.val.val := rfl

@[simp] theorem map_ambientClassEquiv (C : GeometricClass) (g : SpecialClifford n F)
    (c : RationalFibre geometricClass C) :
    rationalClassMap geometricClass upperGeometricClass geometric_square C
      (ambientClassEquiv geometricClass upperGeometricClass geometric_square C g c) =
      rationalClassMap geometricClass upperGeometricClass geometric_square C c := by
  apply Subtype.ext
  exact upperClassMap_conjugation g c.val

/-- Taylor E2/U source on one represented geometric class of this exact
regular embedding. Algebraic connected-centre interpretation and trivial
Frobenius on the displayed component groups remain source authentication.
Both parametrisations and both sides of the compatibility square are kept. -/
structure CompatibleComponentParametrisation
    (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
    (C : GeometricClass) (A V : Type) [Group A] [CommGroup V]
    (presentation : ComponentPresentation A V) where
  lowerParameter : RationalFibre geometricClass C ≃ ConjClasses A
  upperParameter : UpperRationalFibre upperGeometricClass C ≃ V
  compatibility : ∀ c, upperParameter
    (rationalClassMap geometricClass upperGeometricClass geometric_square C c) =
      presentation.classProjection (lowerParameter c)

/-- A derived interface for the entry calculation. Consumers receive this
only from `CompatibleComponentParametrisation.fibreGeometry`; the specified
source record above does not accept it. Ambient conjugation is the global
literal `ambientClassEquiv`, not an action field of this interface. -/
structure FibreGeometry (C : GeometricClass) where
  exceptional : UpperRationalFibre upperGeometricClass C
  relabel : RationalFibre geometricClass C ≃
    Sum {u : UpperRationalFibre upperGeometricClass C // u ≠ exceptional} (Fin 2)
  map_relabel_symm_inl : ∀ u,
    rationalClassMap geometricClass upperGeometricClass geometric_square C
      (relabel.symm (Sum.inl u)) = u.val
  map_relabel_symm_inr : ∀ i,
    rationalClassMap geometricClass upperGeometricClass geometric_square C
      (relabel.symm (Sum.inr i)) = exceptional

namespace CompatibleComponentParametrisation

variable {geometricClass upperGeometricClass geometric_square}
  {parameters : OddFieldParameters F r f} {rank : 4 ≤ n}
  {C : GeometricClass} {A V : Type} [Group A] [CommGroup V]
  {presentation : ComponentPresentation A V}
  (S : CompatibleComponentParametrisation geometricClass upperGeometricClass
    geometric_square parameters rank C A V presentation)

local notation "π" => rationalClassMap geometricClass upperGeometricClass geometric_square C

def exceptional : UpperRationalFibre upperGeometricClass C := S.upperParameter.symm 1

def firstClass : RationalFibre geometricClass C :=
  S.lowerParameter.symm (ConjClasses.mk (1 : A))

def secondClass : RationalFibre geometricClass C :=
  S.lowerParameter.symm (ConjClasses.mk presentation.theta)

theorem map_firstClass : π S.firstClass = S.exceptional := by
  apply S.upperParameter.injective
  rw [S.compatibility]
  simp [firstClass, exceptional, presentation.classProjection_mk]

theorem map_secondClass : π S.secondClass = S.exceptional := by
  apply S.upperParameter.injective
  rw [S.compatibility]
  simp [secondClass, exceptional, presentation.classProjection_mk,
    presentation.theta_in_kernel]

theorem firstClass_ne_secondClass : S.firstClass ≠ S.secondClass := by
  intro h
  apply presentation.identity_class_ne_theta_class
  have heq := congrArg S.lowerParameter h
  simpa [firstClass, secondClass] using heq

/-- The exceptional fibre consists of exactly the two central component
classes, transported by the actual compatible parametrisations. -/
theorem map_eq_exceptional_iff (c : RationalFibre geometricClass C) :
    π c = S.exceptional ↔ c = S.firstClass ∨ c = S.secondClass := by
  constructor
  · intro h
    have hp : presentation.classProjection (S.lowerParameter c) = 1 := by
      rw [← S.compatibility, h]
      exact S.upperParameter.apply_symm_apply 1
    rcases (presentation.classProjection_eq_one_iff _).1 hp with hc | hc
    · left
      apply S.lowerParameter.injective
      simpa [firstClass] using hc
    · right
      apply S.lowerParameter.injective
      simpa [secondClass] using hc
  · rintro (rfl | rfl)
    · exact S.map_firstClass
    · exact S.map_secondClass

include S in
theorem map_surjective : Function.Surjective π := by
  intro u
  obtain ⟨c, hc⟩ := presentation.classProjection_surjective (S.upperParameter u)
  refine ⟨S.lowerParameter.symm c, S.upperParameter.injective ?_⟩
  rw [S.compatibility, S.lowerParameter.apply_symm_apply]
  exact hc

/-- Every upper class other than the exceptional one has at most one
preimage, proved from the component kernel and centre calculation. -/
theorem nonexceptional_fibre_unique
    (u : UpperRationalFibre upperGeometricClass C) (hu : u ≠ S.exceptional)
    (c d : RationalFibre geometricClass C) (hc : π c = u) (hd : π d = u) : c = d := by
  apply S.lowerParameter.injective
  apply presentation.nonidentity_fibre_subsingleton (S.upperParameter u)
  · intro h
    apply hu
    apply S.upperParameter.injective
    simpa [exceptional] using h
  · rw [← S.compatibility, hc]
  · rw [← S.compatibility, hd]

/-- Exactly one preimage, retaining the actual upper rational-class map. -/
theorem singleton_fibre (u : UpperRationalFibre upperGeometricClass C)
    (hu : u ≠ S.exceptional) : ∃! c, π c = u := by
  obtain ⟨c, hc⟩ := S.map_surjective u
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact S.nonexceptional_fibre_unique u hu d c hd hc

def exceptionalFibreEquiv : {c : RationalFibre geometricClass C // π c = S.exceptional} ≃
    Fin 2 := by
  classical
  let pair : Fin 2 → {c : RationalFibre geometricClass C // π c = S.exceptional} :=
    fun i => if i = 0 then ⟨S.firstClass, S.map_firstClass⟩
      else ⟨S.secondClass, S.map_secondClass⟩
  apply Equiv.symm
  apply Equiv.ofBijective pair
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · have heq := congrArg Subtype.val h
      exact False.elim (S.firstClass_ne_secondClass (by simpa [pair] using heq))
    · have heq := congrArg Subtype.val h
      exact False.elim (S.firstClass_ne_secondClass (by simpa [pair] using heq.symm))
    · rfl
  · rintro ⟨c, hc⟩
    rcases (S.map_eq_exceptional_iff c).1 hc with h | h
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      simpa [pair] using h.symm
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      simpa [pair] using h.symm

theorem exceptional_fibre_card :
    Nat.card {c : RationalFibre geometricClass C // π c = S.exceptional} = 2 := by
  simpa using Nat.card_congr S.exceptionalFibreEquiv

def nonexceptionalEquiv :
    {c : RationalFibre geometricClass C // π c ≠ S.exceptional} ≃
      {u : UpperRationalFibre upperGeometricClass C // u ≠ S.exceptional} := by
  apply Equiv.ofBijective (fun c => ⟨π c.val, c.property⟩)
  constructor
  · intro c d h
    apply Subtype.ext
    exact S.nonexceptional_fibre_unique (π c.val) c.property d.val c.val
      (congrArg Subtype.val h).symm rfl |>.symm
  · rintro ⟨u, hu⟩
    obtain ⟨c, hc⟩ := S.map_surjective u
    refine ⟨⟨c, by simpa only [hc] using hu⟩, ?_⟩
    exact Subtype.ext hc

/-- The lower rational classes split into singleton upper fibres and the
two central component classes. The equivalence is constructed from the
derived uniqueness and the actual class map. -/
def relabel : RationalFibre geometricClass C ≃
    Sum {u : UpperRationalFibre upperGeometricClass C // u ≠ S.exceptional} (Fin 2) := by
  classical
  exact (Equiv.sumCompl (fun c : RationalFibre geometricClass C =>
    π c ≠ S.exceptional)).symm.trans
      (Equiv.sumCongr S.nonexceptionalEquiv
        ((Equiv.subtypeEquivRight (fun _ => not_not)).trans S.exceptionalFibreEquiv))

theorem map_relabel_symm_inl
    (u : {u : UpperRationalFibre upperGeometricClass C // u ≠ S.exceptional}) :
    π (S.relabel.symm (Sum.inl u)) = u.val := by
  change π (S.nonexceptionalEquiv.symm u).val = u.val
  exact congrArg Subtype.val (S.nonexceptionalEquiv.apply_symm_apply u)

theorem map_relabel_symm_inr (i : Fin 2) :
    π (S.relabel.symm (Sum.inr i)) = S.exceptional := by
  change π (S.exceptionalFibreEquiv.symm i).val = S.exceptional
  exact (S.exceptionalFibreEquiv.symm i).property

/-- Constructor used by the specified entry calculation. No finished fibre
model or prescribed matrix is an input to this definition. -/
def fibreGeometry : FibreGeometry geometricClass upperGeometricClass geometric_square C where
  exceptional := S.exceptional
  relabel := S.relabel
  map_relabel_symm_inl := S.map_relabel_symm_inl
  map_relabel_symm_inr := S.map_relabel_symm_inr

end CompatibleComponentParametrisation

end ActualClasses

end ModularRep.PaperProofs.TypeBAllRankGGGRFibres


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
