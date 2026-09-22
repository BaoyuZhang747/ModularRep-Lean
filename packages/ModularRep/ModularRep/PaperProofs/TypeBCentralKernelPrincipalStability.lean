import ModularRep.PaperProofs.TypeBCentralKernelBrauerBlocks

/-!
# Automorphism stability of the actual principal block and its Brauer fibre

The principal-block test is the action of a literal primitive idempotent on
the one-dimensional trivial representation. Orthogonality in the displayed
specified decomposition proves uniqueness, and twisting the trivial
representation proves that every actual group automorphism fixes this block.
The existing specified Brauer-block transport then gives stability of its
supported fibre. No character correspondence or new external source is used.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCentralKernelPrincipalStability

open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks

universe u

variable {k G : Type u} [Field k] [Group G]

theorem trivial_twist (alpha : MulAut G) :
    (1 : Representation k G k).twist alpha = 1 := by
  apply MonoidHom.ext
  intro g
  rfl

/-- The principal support test is preserved by the canonical right twist
of the specified group algebra idempotent. -/
theorem isPrincipal_rightTwist (b : LiteralPrimitiveBlock k G)
    (hb : IsPrincipal b) (alpha : MulAut G) :
    IsPrincipal (LiteralPrimitiveBlock.rightTwistBlock b alpha) := by
  change (1 : Representation k G k).asAlgebraHom
    (MonoidAlgebra.mapDomainRingEquiv k alpha.symm b.val) = 1
  have transport := Representation.twist_asAlgebraHom_mapDomainRingEquiv_symm_apply
    (1 : Representation k G k) alpha b.val
  rw [trivial_twist] at transport
  exact transport.trans hb

variable [Fintype (LiteralPrimitiveBlock k G)]
  (D : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G => b.val))

include D in
/-- Two orthogonal specified blocks cannot both act identically on the
same nonzero trivial module. -/
theorem principal_unique (b c : LiteralPrimitiveBlock k G)
    (hb : IsPrincipal b) (hc : IsPrincipal c) : b = c := by
  by_contra hne
  have orthogonal : b.val * c.val = 0 := D.complete.ortho hne
  have impossible := congrArg (Representation.asAlgebraHom (1 : Representation k G k))
    orthogonal
  change (1 : Representation k G k).asAlgebraHom b.val = 1 at hb
  change (1 : Representation k G k).asAlgebraHom c.val = 1 at hc
  rw [map_mul, hb, hc, map_zero, one_mul] at impossible
  exact one_ne_zero impossible

include D in
theorem principal_rightTwist_eq (b : LiteralPrimitiveBlock k G)
    (hb : IsPrincipal b) (alpha : MulAut G) :
    LiteralPrimitiveBlock.rightTwistBlock b alpha = b :=
  principal_unique D _ b (isPrincipal_rightTwist b hb alpha) hb

include D in
theorem principal_op_smul_eq (b : LiteralPrimitiveBlock k G)
    (hb : IsPrincipal b) (alpha : (MulAut G)ᵐᵒᵖ) : alpha • b = b :=
  principal_rightTwist_eq D b hb alpha.unop

variable {p : ℕ} {K : Type u}
  [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [Finite G]
  (iota : PrimeRegularRootEmbedding p k K G)

include D in
/-- The supported Brauer fibre of this same literal principal block is
stable under every actual automorphism. -/
theorem supported_principal_twist (b : LiteralPrimitiveBlock k G)
    (hb : IsPrincipal b) (alpha : MulAut G)
    (phi : IBr iota) (hphi : Supported iota b phi) :
    Supported iota b (IrreducibleBrauerCharacter.twist iota phi alpha) := by
  have supported := supported_twist iota D b alpha phi hphi
  rw [principal_rightTwist_eq D b hb alpha] at supported
  exact supported

include D in
theorem supported_principal_op_smul (b : LiteralPrimitiveBlock k G)
    (hb : IsPrincipal b) (alpha : (MulAut G)ᵐᵒᵖ)
    (phi : IBr iota) (hphi : Supported iota b phi) :
    Supported iota b (alpha • phi) :=
  supported_principal_twist D iota b hb alpha.unop phi hphi

/-- The actual opposite-automorphism action restricted to the principal
support fibre; the projection remains the original Brauer character. -/
def principalFibreMulAction (b : LiteralPrimitiveBlock k G) (hb : IsPrincipal b) :
    MulAction (MulAut G)ᵐᵒᵖ {phi : IBr iota // Supported iota b phi} where
  smul alpha phi :=
    ⟨alpha • phi.val, supported_principal_op_smul D iota b hb alpha phi.val phi.property⟩
  one_smul phi := Subtype.ext (one_smul (MulAut G)ᵐᵒᵖ phi.val)
  mul_smul alpha beta phi := Subtype.ext (mul_smul alpha beta phi.val)

end ModularRep.PaperProofs.TypeBCentralKernelPrincipalStability


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
