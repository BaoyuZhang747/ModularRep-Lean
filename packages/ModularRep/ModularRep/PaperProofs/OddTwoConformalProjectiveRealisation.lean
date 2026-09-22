import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.SemidirectProduct
import ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
import ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow

/-!
# Literal conformal and projective symplectic groups for the Brough--Spath lane

The conformal group is the subgroup of GL on the SAME `Fin n + Fin n`
matrix coordinates whose elements satisfy `g.transpose * J * g = m • J`
for an actual unit m of F. Closure, the Sp inclusion, entrywise field
automorphisms and quotient action squares are K constructions.

PCSp is literally the quotient of this group by its whole centre. The
PSp inclusion is the map of the two centre quotients induced by the fixed
matrix inclusion. Its injectivity follows from the exact E1 centre
intersection equality. No arbitrary group named PCSp is a parameter.

The standard finite group structure remains an explicit E1 source:
rank at least two, odd actual field order, the centre intersection,
the derived subgroup and index two, cyclic field automorphisms, and the
full natural automorphism identification. The latter is an equivalence
on the constructed PCSp/field semidirect group with a formula forcing its
action to be actual conjugation after entrywise field automorphism.
These facts are the group realization in FM Section 3, pp. 4--6, used
with the existing exact full-cover source including (n,q)=(2,3).

No source instance, covering weight, DGN correspondence, character
extension, block-triple relation or orbit witness is constructed here.
In particular the odd-field PCSp extension is not replaced by an
equal-group self-cover candidate. The source-specific stabilizers and
compatible character/root bindings remain the next task.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation

open ModularRep.PaperProofs.NormalCoreLemma48SourceInstantiation
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
  (OddFieldParameters LiteralDiagonalFieldRealisation)

universe u

abbrev Coordinate (n : ℕ) := Fin n ⊕ Fin n

abbrev Sp (n : ℕ) (F : Type u) [Field F] := Matrix.symplecticGroup (Fin n) F

abbrev PSp (n : ℕ) (F : Type u) [Field F] := Sp n F ⧸ Subgroup.center (Sp n F)

section MatrixGroup

variable (n : ℕ) (F : Type u) [Field F]

/-- The literal similitude equation, with its multiplier a field unit. -/
def IsConformal (g : Matrix.GeneralLinearGroup (Coordinate n) F) : Prop :=
  ∃ m : Fˣ, (g : Matrix (Coordinate n) (Coordinate n) F).transpose *
      Matrix.J (Fin n) F * (g : Matrix (Coordinate n) (Coordinate n) F) =
    (m : F) • Matrix.J (Fin n) F

theorem isConformal_one : IsConformal n F 1 := by
  refine ⟨1, ?_⟩
  simp

theorem isConformal_mul
    {g h : Matrix.GeneralLinearGroup (Coordinate n) F}
    (hg : IsConformal n F g) (hh : IsConformal n F h) :
    IsConformal n F (g * h) := by
  obtain ⟨m, hm⟩ := hg
  obtain ⟨r, hr⟩ := hh
  refine ⟨m * r, ?_⟩
  change ((g : Matrix (Coordinate n) (Coordinate n) F) *
      (h : Matrix (Coordinate n) (Coordinate n) F)).transpose *
      Matrix.J (Fin n) F * ((g : Matrix (Coordinate n) (Coordinate n) F) *
        (h : Matrix (Coordinate n) (Coordinate n) F)) = _
  calc
    _ = (h : Matrix (Coordinate n) (Coordinate n) F).transpose *
        ((g : Matrix (Coordinate n) (Coordinate n) F).transpose * Matrix.J (Fin n) F *
          (g : Matrix (Coordinate n) (Coordinate n) F)) *
        (h : Matrix (Coordinate n) (Coordinate n) F) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (m : F) • ((h : Matrix (Coordinate n) (Coordinate n) F).transpose *
        Matrix.J (Fin n) F * (h : Matrix (Coordinate n) (Coordinate n) F)) := by
      rw [hm]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = ((m * r : Fˣ) : F) • Matrix.J (Fin n) F := by
      rw [hr, smul_smul]
      rfl

theorem isConformal_inv
    {g : Matrix.GeneralLinearGroup (Coordinate n) F}
    (hg : IsConformal n F g) : IsConformal n F g⁻¹ := by
  obtain ⟨m, hm⟩ := hg
  have hJ : Matrix.J (Fin n) F = (m : F) •
      ((g⁻¹ : Matrix.GeneralLinearGroup (Coordinate n) F).val.transpose *
        Matrix.J (Fin n) F * (g⁻¹ : Matrix.GeneralLinearGroup (Coordinate n) F).val) := by
    calc
      Matrix.J (Fin n) F =
          ((g * g⁻¹ : Matrix.GeneralLinearGroup (Coordinate n) F).val).transpose *
            Matrix.J (Fin n) F * (g * g⁻¹ : Matrix.GeneralLinearGroup (Coordinate n) F).val := by
        simp
      _ = (g⁻¹ : Matrix.GeneralLinearGroup (Coordinate n) F).val.transpose *
          (g.val.transpose * Matrix.J (Fin n) F * g.val) *
          (g⁻¹ : Matrix.GeneralLinearGroup (Coordinate n) F).val := by
        simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hm]; simp only [Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨m⁻¹, ?_⟩
  have h := congrArg (fun M : Matrix (Coordinate n) (Coordinate n) F =>
    ((m⁻¹ : Fˣ) : F) • M) hJ
  simpa only [smul_smul, Units.inv_mul, one_smul] using h.symm

/-- The actual conformal symplectic subgroup of GL. -/
def conformalSubgroup : Subgroup (Matrix.GeneralLinearGroup (Coordinate n) F) where
  carrier := IsConformal n F
  one_mem' := isConformal_one n F
  mul_mem' := isConformal_mul n F
  inv_mem' := isConformal_inv n F

abbrev CSp := ↥(conformalSubgroup n F)

/-- PCSp is the actual whole-centre quotient. -/
abbrev PCSp := CSp n F ⧸ Subgroup.center (CSp n F)

def cspMatrix (g : CSp n F) : Matrix (Coordinate n) (Coordinate n) F := g.1.val

theorem cspMatrix_injective : Function.Injective (cspMatrix n F) := by
  intro g h heq
  apply Subtype.ext
  exact Units.ext heq

instance cspFinite [Finite F] : Finite (CSp n F) :=
  Finite.of_injective (cspMatrix n F) (cspMatrix_injective n F)

instance pcspFinite [Finite F] : Finite (PCSp n F) := inferInstance

/-- The existing Sp group, placed in GL with its existing inverse. -/
def spToGL : Sp n F →* Matrix.GeneralLinearGroup (Coordinate n) F where
  toFun g :=
    { val := g.1
      inv := (g⁻¹).1
      val_inv := by
        change ((g * g⁻¹ : Sp n F) : Matrix (Coordinate n) (Coordinate n) F) = 1
        rw [mul_inv_cancel]
        rfl
      inv_val := by
        change ((g⁻¹ * g : Sp n F) : Matrix (Coordinate n) (Coordinate n) F) = 1
        rw [inv_mul_cancel]
        rfl }
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

/-- The fixed inclusion uses multiplier one and the existing equivalent
transpose-first symplectic equation from mathlib. -/
def spEmbedding : Sp n F →* CSp n F where
  toFun g := ⟨spToGL n F g, 1, by
    change g.1.transpose * Matrix.J (Fin n) F * g.1 = (1 : F) • Matrix.J (Fin n) F
    simpa only [one_smul] using (SymplecticGroup.mem_iff'.mp g.2)⟩
  map_one' := Subtype.ext (Units.ext rfl)
  map_mul' _ _ := Subtype.ext (Units.ext rfl)

@[simp] theorem spEmbedding_matrix (g : Sp n F) :
    cspMatrix n F (spEmbedding n F g) = (g : Matrix (Coordinate n) (Coordinate n) F) := rfl

theorem spEmbedding_injective : Function.Injective (spEmbedding n F) := by
  intro g h heq
  apply Subtype.ext
  exact congrArg (cspMatrix n F) heq

def spProjection : Sp n F →* PSp n F := QuotientGroup.mk' (Subgroup.center (Sp n F))

def cspProjection : CSp n F →* PCSp n F := QuotientGroup.mk' (Subgroup.center (CSp n F))

end MatrixGroup

section FieldActions

variable {n : ℕ} {F : Type u} [Field F]

theorem isConformal_map (sigma : F ≃+* F)
    {g : Matrix.GeneralLinearGroup (Coordinate n) F} (hg : IsConformal n F g) :
    IsConformal n F (Matrix.GeneralLinearGroup.map sigma.toRingHom g) := by
  obtain ⟨m, hm⟩ := hg
  refine ⟨Units.map sigma.toMonoidHom m, ?_⟩
  change (g.val.map sigma).transpose * Matrix.J (Fin n) F * (g.val.map sigma) =
    sigma (m : F) • Matrix.J (Fin n) F
  have h := congrArg (fun M : Matrix (Coordinate n) (Coordinate n) F => M.map sigma) hm
  simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_J,
    Matrix.map_smul' sigma (m : F) (Matrix.J (Fin n) F) sigma.map_mul] using h

/-- Entrywise field automorphism of the literal conformal matrices. -/
def cspFieldAut (sigma : F ≃+* F) : MulAut (CSp n F) where
  toFun g := ⟨Matrix.GeneralLinearGroup.map sigma.toRingHom g.1, isConformal_map sigma g.2⟩
  invFun g := ⟨Matrix.GeneralLinearGroup.map sigma.symm.toRingHom g.1,
    isConformal_map sigma.symm g.2⟩
  left_inv g := by
    apply cspMatrix_injective n F
    ext i j
    exact sigma.symm_apply_apply (cspMatrix n F g i j)
  right_inv g := by
    apply cspMatrix_injective n F
    ext i j
    exact sigma.apply_symm_apply (cspMatrix n F g i j)
  map_mul' g h := Subtype.ext ((Matrix.GeneralLinearGroup.map sigma.toRingHom).map_mul g.1 h.1)

@[simp] theorem cspFieldAut_matrix (sigma : F ≃+* F) (g : CSp n F) :
    cspMatrix n F (cspFieldAut sigma g) = (cspMatrix n F g).map sigma := rfl

def cspFieldAction : (F ≃+* F) →* MulAut (CSp n F) where
  toFun := cspFieldAut
  map_one' := by
    apply DFunLike.ext
    intro g
    apply cspMatrix_injective n F
    rfl
  map_mul' sigma tau := by
    apply DFunLike.ext
    intro g
    apply cspMatrix_injective n F
    rfl

/-- The corresponding entrywise automorphism on the existing Sp matrices. -/
def spFieldAut (sigma : F ≃+* F) : MulAut (Sp n F) where
  toFun g := ⟨g.1.map sigma, SymplecticGroup.map_mem g.2 sigma⟩
  invFun g := ⟨g.1.map sigma.symm, SymplecticGroup.map_mem g.2 sigma.symm⟩
  left_inv g := by
    apply Subtype.ext
    ext i j
    exact sigma.symm_apply_apply (g.1 i j)
  right_inv g := by
    apply Subtype.ext
    ext i j
    exact sigma.apply_symm_apply (g.1 i j)
  map_mul' g h := Subtype.ext (Matrix.map_mul (f := sigma))

@[simp] theorem spFieldAut_matrix (sigma : F ≃+* F) (g : Sp n F) :
    (spFieldAut sigma g : Matrix (Coordinate n) (Coordinate n) F) = g.1.map sigma := rfl

def spFieldAction : (F ≃+* F) →* MulAut (Sp n F) where
  toFun := spFieldAut
  map_one' := by
    apply DFunLike.ext
    intro g
    apply Subtype.ext
    rfl
  map_mul' sigma tau := by
    apply DFunLike.ext
    intro g
    apply Subtype.ext
    rfl

/-- The two entrywise actions agree along the fixed matrix inclusion. -/
theorem field_spEmbedding (sigma : F ≃+* F) (g : Sp n F) :
    cspFieldAut sigma (spEmbedding n F g) = spEmbedding n F (spFieldAut sigma g) := by
  apply cspMatrix_injective n F
  rfl

/-- An actual automorphism induces its canonical whole-centre quotient
automorphism. This packages the existing quotient construction as a hom. -/
def centerQuotientAutHom (G : Type u) [Group G] :
    MulAut G →* MulAut (G ⧸ Subgroup.center G) where
  toFun alpha := quotientMulAut (Subgroup.center G) alpha
    (Subgroup.characteristic_iff_map_eq.mp inferInstance alpha)
  map_one' := by
    apply DFunLike.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
    rfl
  map_mul' alpha beta := by
    apply DFunLike.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
    rfl

@[simp] theorem centerQuotientAutHom_mk {G : Type u} [Group G]
    (alpha : MulAut G) (g : G) :
    centerQuotientAutHom G alpha (QuotientGroup.mk' (Subgroup.center G) g) =
      QuotientGroup.mk' (Subgroup.center G) (alpha g) := rfl

def pcspFieldAction : (F ≃+* F) →* MulAut (PCSp n F) :=
  (centerQuotientAutHom (CSp n F)).comp cspFieldAction

def pspFieldAction : (F ≃+* F) →* MulAut (PSp n F) :=
  (centerQuotientAutHom (Sp n F)).comp spFieldAction

@[simp] theorem pcspFieldAction_projection (sigma : F ≃+* F) (g : CSp n F) :
    pcspFieldAction sigma (cspProjection n F g) =
      cspProjection n F (cspFieldAut sigma g) := rfl

@[simp] theorem pspFieldAction_projection (sigma : F ≃+* F) (g : Sp n F) :
    pspFieldAction sigma (spProjection n F g) =
      spProjection n F (spFieldAut sigma g) := rfl

/-- Agreement with the actual entrywise field map already used by the
Feng--Malle source problem, including its opposite-group convention. -/
theorem spFieldAut_eq_existing [Finite F] (O : LiteralDiagonalFieldRealisation n F)
    (sigma : F ≃+* F) :
    spFieldAut sigma = (O.outer.field (MulOpposite.op sigma)).unop := by
  apply DFunLike.ext
  intro g
  apply Subtype.ext
  exact (O.field_apply (MulOpposite.op sigma) g).symm

end FieldActions

section ProjectiveInclusion

variable (n : ℕ) (F : Type u) [Field F] [Finite F]

/-- Exact standard E1 centre intersection on the literal matrix inclusion.
The rank/field scope is the one used in the odd-field Type C source. -/
structure CenterIntersectionSource : Prop where
  parameters : OddFieldParameters n F
  center_preimage : (Subgroup.center (CSp n F)).comap (spEmbedding n F) =
    Subgroup.center (Sp n F)

variable {n F}

/-- The PSp inclusion is the actual quotient map of the matrix inclusion. -/
def pspEmbedding (C : CenterIntersectionSource n F) : PSp n F →* PCSp n F :=
  QuotientGroup.map (Subgroup.center (Sp n F)) (Subgroup.center (CSp n F))
    (spEmbedding n F) C.center_preimage.symm.le

@[simp] theorem pspEmbedding_projection (C : CenterIntersectionSource n F) (g : Sp n F) :
    pspEmbedding C (spProjection n F g) = cspProjection n F (spEmbedding n F g) := rfl

theorem pspEmbedding_injective (C : CenterIntersectionSource n F) :
    Function.Injective (pspEmbedding C) := by
  apply (MonoidHom.ker_eq_bot_iff (pspEmbedding C)).mp
  change (QuotientGroup.map (Subgroup.center (Sp n F)) (Subgroup.center (CSp n F))
    (spEmbedding n F) C.center_preimage.symm.le).ker = ⊥
  rw [QuotientGroup.ker_map, C.center_preimage, QuotientGroup.map_mk'_self]

/-- Both projective field actions commute with the fixed projective inclusion. -/
theorem field_pspEmbedding (C : CenterIntersectionSource n F)
    (sigma : F ≃+* F) (x : PSp n F) :
    pcspFieldAction sigma (pspEmbedding C x) = pspEmbedding C (pspFieldAction sigma x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Sp n F)) x
  change cspProjection n F (cspFieldAut sigma (spEmbedding n F g)) =
    cspProjection n F (spEmbedding n F (spFieldAut sigma g))
  rw [field_spEmbedding]

/-- The actual PCSp/field semidirect group used in the source criterion. -/
abbrev Ambient := PCSp n F ⋊[pcspFieldAction] (F ≃+* F)

/-- Its fixed copy of PSp. -/
def baseEmbedding (C : CenterIntersectionSource n F) : PSp n F →* Ambient (n := n) (F := F) :=
  SemidirectProduct.inl.comp (pspEmbedding C)

theorem baseEmbedding_injective (C : CenterIntersectionSource n F) :
    Function.Injective (baseEmbedding C) :=
  SemidirectProduct.inl_injective.comp (pspEmbedding_injective C)

/-- Exact standard group facts on the FIXED groups and natural action.
The value formula determines fullAut uniquely; it is not an arbitrary
equivalence with an unrelated action. No character or relation is a field.

The centre/derived/index and full automorphism facts are the PCSp/field
realization in FM Section 3, pp. 4--6. They have not been instantiated here.
The actual prime-to-two covering-group application additionally uses the
existing OddSymplecticFullCoverSource and its identityEllPrimeCover.
-/
structure BroughGroupSource (C : CenterIntersectionSource n F) where
  normal_image : (pspEmbedding C).range.Normal
  derived_image : commutator (PCSp n F) = (pspEmbedding C).range
  quotient_card : letI := normal_image
    Nat.card (PCSp n F ⧸ (pspEmbedding C).range) = 2
  center_eq_bot : Subgroup.center (PCSp n F) = ⊥
  field_cyclic : IsCyclic (F ≃+* F)
  fullAut : Ambient (n := n) (F := F) ≃* MulAut (PSp n F)
  fullAut_apply : ∀ (a : Ambient (n := n) (F := F)) (x : PSp n F),
    pspEmbedding C (fullAut a x) =
      a.left * pcspFieldAction a.right (pspEmbedding C x) * a.left⁻¹
  ambient_centralizer :
    Subgroup.centralizer ((baseEmbedding C).range : Set (Ambient (n := n) (F := F))) = ⊥

namespace BroughGroupSource

variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)

/-- The actual faithful PCSp action is obtained by restricting the fixed
full natural automorphism equivalence. -/
def pcspToAut : PCSp n F →* MulAut (PSp n F) :=
  S.fullAut.toMonoidHom.comp SemidirectProduct.inl

theorem pcspToAut_injective : Function.Injective S.pcspToAut :=
  S.fullAut.injective.comp SemidirectProduct.inl_injective

/-- Its conjugation formula on the actual embedded PSp subgroup. -/
theorem pcspToAut_apply (g : PCSp n F) (x : PSp n F) :
    pspEmbedding C (S.pcspToAut g x) = g * pspEmbedding C x * g⁻¹ := by
  simpa only [pcspToAut, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    map_one, MulAut.one_apply] using S.fullAut_apply (SemidirectProduct.inl g) x

/-- The full source map restricts to the already constructed entrywise
projective field automorphisms, rather than a freely chosen action. -/
theorem fullAut_field (sigma : F ≃+* F) :
    S.fullAut (SemidirectProduct.inr sigma) = pspFieldAction sigma := by
  apply DFunLike.ext
  intro x
  apply pspEmbedding_injective C
  have h := S.fullAut_apply (SemidirectProduct.inr sigma) x
  simpa only [SemidirectProduct.left_inr, SemidirectProduct.right_inr,
    one_mul, inv_one, mul_one, field_pspEmbedding] using h

/-- The base-group action is literally the inner automorphism. -/
theorem pcspToAut_base (x : PSp n F) :
    S.pcspToAut (pspEmbedding C x) = MulAut.conj x := by
  apply DFunLike.ext
  intro y
  apply pspEmbedding_injective C
  rw [S.pcspToAut_apply]
  simp only [MulAut.conj_apply, map_mul, map_inv]

end BroughGroupSource

end ProjectiveInclusion

end ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
