import ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding
import ModularRep.PaperProofs.TypeBCentralKernelBlockSource

/-!
# The dominating rank-three Spin block on the literal matrix projection

This is the primal block join in prop:type-b-two-rank-three. The projection
is the constructed vector action on the actual Clifford norm kernel, with
codomain the independently defined matrix Omega. The existing odd-field,
projection, finite Spin and centre-order hypotheses retain those carriers.

Navarro 7.6 and 9.10 enter only through the existing central normal-p-subgroup
primitive-idempotent principle. The old blockEquiv wrapper reads a root only
for its primality field. The small specialization below uses Nat.prime_two
instead, so this block-only deduction has no characteristic-zero field,
root, modular system or chosen representation input. Literal primitive
idempotents are transported through the constructed group algebra map; no
independent block equivalence is assumed. Principalness is tested by the
same trivial representation as TypeBCentralKernelBlockSource.IsPrincipal.

The argument does not need q different from three: that restriction belongs
to the later manuscript branch. No dual semisimple carrier or label is used
here, and this support join is not a complete block-criterion endpoint.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeNonprincipalBlockBinding

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource

section RootFreeBlocks

variable {k A B : Type} [Field k] [CharP k 2] [IsAlgClosed k]
  [Group A] [Group B]

/-- The same Navarro quotient-idempotent construction, with primality fixed
at two rather than obtained from an otherwise unused root. -/
private def quotientBlockEquiv [Finite A]
    (P : Subgroup A) [P.Normal] (twoGroup : IsPGroup 2 P)
    (central : P ≤ Subgroup.center A)
    (navarro : NavarroCentralBlockPrinciple 2 k) :
    LiteralPrimitiveBlock k A ≃ LiteralPrimitiveBlock k (A ⧸ P) :=
  Equiv.ofBijective
    (fun b : LiteralPrimitiveBlock k A =>
      (⟨quotientAlgebraMap P b.val,
        (navarro A P Nat.prime_two twoGroup central).1 b⟩ :
          LiteralPrimitiveBlock k (A ⧸ P)))
    ⟨fun b c h =>
      (navarro A P Nat.prime_two twoGroup central).2.1 b c
        (congrArg Subtype.val h),
      fun c => by
        obtain ⟨b, hb⟩ := (navarro A P Nat.prime_two twoGroup central).2.2 c
        exact ⟨b, Subtype.ext hb⟩⟩

/-- Reindex the literal primitive subtype by the actual group algebra
isomorphism induced by a constructed group equivalence. -/
private def blocksAlong (e : A ≃* B) :
    LiteralPrimitiveBlock k A ≃ LiteralPrimitiveBlock k B where
  toFun b := ⟨MonoidAlgebra.domCongr k k e b.val,
    b.property.mapRingEquiv (MonoidAlgebra.domCongr k k e).toRingEquiv⟩
  invFun b := ⟨(MonoidAlgebra.domCongr k k e).symm b.val,
    b.property.mapRingEquiv (MonoidAlgebra.domCongr k k e).symm.toRingEquiv⟩
  left_inv b := Subtype.ext ((MonoidAlgebra.domCongr k k e).symm_apply_apply b.val)
  right_inv b := Subtype.ext ((MonoidAlgebra.domCongr k k e).apply_symm_apply b.val)

/-- The literal trivial-module square, with no representation data supplied
by a source. This is the same principal test used by blockEquiv_principal_iff. -/
private theorem trivial_algebra_map (f : A →* B) (b : k[A]) :
    Representation.asAlgebraHom (1 : Representation k B k)
        (MonoidAlgebra.mapDomainAlgHom k k f b) =
      Representation.asAlgebraHom (1 : Representation k A k) b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add b c hb hc => simp only [map_add, hb, hc]
  | single g a => simp [Representation.asAlgebraHom_single]

end RootFreeBlocks

variable {p f : ℕ} {F k : Type} [Field F] [Finite F] [CharP F p]
  [Field k] [CharP k 2] [IsAlgClosed k]
  (parameters : OddFieldParameters F p f) (N : NormSource 3 F)
  (orthogonal : TypeBCliffordOrthogonalSourceBinding.Source 3 F p f parameters (by decide) N)
  (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 p f F N)
  [Finite (Spin 3 F N)]
  (navarro : NavarroCentralBlockPrinciple 2 k)

include parameters centre in
private theorem centre_isTwoGroup : IsPGroup 2 (Subgroup.center (Spin 3 F N)) := by
  apply IsPGroup.of_card (n := 1)
  simpa only [pow_one] using centre.centre_order parameters (by decide : 3 ≤ 3)

/-- The block equivalence is constructed through the actual central quotient
and its checked identification with the independently defined matrix Omega. -/
def blockEquiv :
    LiteralPrimitiveBlock k (Spin 3 F N) ≃
      LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F) :=
  (quotientBlockEquiv (Subgroup.center (Spin 3 F N))
    (centre_isTwoGroup parameters N centre) le_rfl navarro).trans
    (blocksAlong (TypeBCliffordOrthogonalSourceBinding.matrixOmegaEquiv
      3 F N parameters (by decide) orthogonal centre))

/-- The image is the group algebra map of the same literal Spin projection. -/
theorem blockEquiv_val (b : LiteralPrimitiveBlock k (Spin 3 F N)) :
    (blockEquiv parameters N orthogonal centre navarro b).val =
      MonoidAlgebra.mapDomainAlgHom k k
        (TypeBCliffordOrthogonalSourceBinding.spinProjection
          3 F parameters (by decide) N orthogonal) b.val := by
  let e := TypeBCliffordOrthogonalSourceBinding.matrixOmegaEquiv
    3 F N parameters (by decide) orthogonal centre
  let pi := TypeBCliffordOrthogonalSourceBinding.spinProjection
    3 F parameters (by decide) N orthogonal
  have square : e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (Spin 3 F N))) = pi := by
    apply MonoidHom.ext
    intro g
    exact TypeBCliffordOrthogonalSourceBinding.spinQuotientEquiv_mk
      3 F N parameters (by decide) orthogonal centre g
  change MonoidAlgebra.mapDomainAlgHom k k e.toMonoidHom
      (MonoidAlgebra.mapDomainAlgHom k k
        (QuotientGroup.mk' (Subgroup.center (Spin 3 F N))) b.val) =
    MonoidAlgebra.mapDomainAlgHom k k pi b.val
  calc
    _ = MonoidAlgebra.mapDomainAlgHom k k
        (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (Spin 3 F N)))) b.val :=
      (congrArg (fun h : k[Spin 3 F N] →ₐ[k]
          k[TypeBOrthogonalOmegaCarriers.Omega 3 F] => h b.val)
        (MonoidAlgebra.mapDomainAlgHom_comp (R := k) (A := k)
          (QuotientGroup.mk' (Subgroup.center (Spin 3 F N))) e.toMonoidHom)).symm
    _ = _ := by rw [square]

/-- Principalness is preserved by this same specified algebra image. -/
theorem blockEquiv_principal_iff (b : LiteralPrimitiveBlock k (Spin 3 F N)) :
    IsPrincipal (blockEquiv parameters N orthogonal centre navarro b) ↔ IsPrincipal b := by
  unfold IsPrincipal
  rw [blockEquiv_val, trivial_algebra_map]

/-- The unique dominating Spin block, selected by the constructed equivalence. -/
def dominatingBlock
    (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F)) :
    LiteralPrimitiveBlock k (Spin 3 F N) :=
  (blockEquiv parameters N orthogonal centre navarro).symm b

theorem dominatingBlock_image
    (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F)) :
    MonoidAlgebra.mapDomainAlgHom k k
        (TypeBCliffordOrthogonalSourceBinding.spinProjection
          3 F parameters (by decide) N orthogonal)
        (dominatingBlock parameters N orthogonal centre navarro b).val = b.val := by
  rw [← blockEquiv_val parameters N orthogonal centre navarro
    (dominatingBlock parameters N orthogonal centre navarro b)]
  exact congrArg Subtype.val
    ((blockEquiv parameters N orthogonal centre navarro).apply_symm_apply b)

theorem dominatingBlock_unique
    (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
    (c : LiteralPrimitiveBlock k (Spin 3 F N))
    (image : MonoidAlgebra.mapDomainAlgHom k k
      (TypeBCliffordOrthogonalSourceBinding.spinProjection
        3 F parameters (by decide) N orthogonal) c.val = b.val) :
    c = dominatingBlock parameters N orthogonal centre navarro b := by
  apply (blockEquiv parameters N orthogonal centre navarro).injective
  apply Subtype.ext
  exact (blockEquiv_val parameters N orthogonal centre navarro c).trans
    (image.trans (congrArg Subtype.val
      ((blockEquiv parameters N orthogonal centre navarro).apply_symm_apply b)).symm)

theorem dominatingBlock_nonprincipal
    (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
    (nonprincipal : ¬ IsPrincipal b) :
    ¬ IsPrincipal (dominatingBlock parameters N orthogonal centre navarro b) := by
  intro principal
  have down := (blockEquiv_principal_iff parameters N orthogonal centre navarro
    (dominatingBlock parameters N orthogonal centre navarro b)).mpr principal
  exact nonprincipal (by
    simpa only [dominatingBlock, Equiv.apply_symm_apply] using down)

include centre navarro in
/-- Every actual nonprincipal lower block has exactly one actual dominating
Spin block, with its literal projection image and proved nonprincipality. -/
theorem existsUnique_nonprincipal_dominatingBlock
    (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
    (nonprincipal : ¬ IsPrincipal b) :
    ∃! c : LiteralPrimitiveBlock k (Spin 3 F N),
      MonoidAlgebra.mapDomainAlgHom k k
          (TypeBCliffordOrthogonalSourceBinding.spinProjection
            3 F parameters (by decide) N orthogonal) c.val = b.val ∧
        ¬ IsPrincipal c := by
  refine ⟨dominatingBlock parameters N orthogonal centre navarro b,
    ⟨dominatingBlock_image parameters N orthogonal centre navarro b,
      dominatingBlock_nonprincipal parameters N orthogonal centre navarro b nonprincipal⟩, ?_⟩
  intro c hc
  exact dominatingBlock_unique parameters N orthogonal centre navarro b c hc.1

end ModularRep.PaperProofs.TypeBRankThreeNonprincipalBlockBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
