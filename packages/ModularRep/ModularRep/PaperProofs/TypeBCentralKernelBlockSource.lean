import ModularRep.PaperProofs.TypeBCentralKernelBrauerInflation
import ModularRep.PrimitiveBlockAutomorphism

/-!
# Literal central-kernel block and Brauer fibres

Navarro 7.6 (pp. 137--138) and 9.10 (p. 201), restricted to a central
normal p-subgroup, supply the primitive-idempotent theorem for the ACTUAL
quotient algebra map. No freely chosen block equivalence is an input.
The representation square, principal-block test and supported Brauer-fibre
equivalence are deductions. A supported character has an actual affording
irreducible representation on which the specified idempotent acts as one.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCentralKernelBlockSource

open TypeBCentralKernelBrauerInflation
open ModularRep.RepresentationSurjectiveDescent

universe u

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G]

def quotientAlgebraMap (P : Subgroup G) [P.Normal] : k[G] →ₐ[k] k[G ⧸ P] :=
  MonoidAlgebra.mapDomainAlgHom k k (QuotientGroup.mk' P)

/-- The narrowly stated E1 primitive-idempotent form of the central case
of Navarro's block correspondence. All three clauses refer to q# itself. -/
def NavarroCentralBlockPrinciple (p : ℕ) (k : Type u)
    [Field k] [CharP k p] [IsAlgClosed k] : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (P : Subgroup X) [P.Normal],
    p.Prime → IsPGroup p P → P ≤ Subgroup.center X →
      (∀ b : LiteralPrimitiveBlock k X,
        IsPrimitiveCentralIdempotent (quotientAlgebraMap P b.val)) ∧
      (∀ b c : LiteralPrimitiveBlock k X,
        quotientAlgebraMap P b.val = quotientAlgebraMap P c.val → b = c) ∧
      (∀ c : LiteralPrimitiveBlock k (X ⧸ P),
        ∃ b : LiteralPrimitiveBlock k X, quotientAlgebraMap P b.val = c.val)

variable (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
  (central : P ≤ Subgroup.center G)
  (iotaDown : PrimeRegularRootEmbedding p k K (G ⧸ P))

def blockMap (source : NavarroCentralBlockPrinciple p k)
    (b : LiteralPrimitiveBlock k G) : LiteralPrimitiveBlock k (G ⧸ P) :=
  ⟨quotientAlgebraMap P b.val, (source G P iotaDown.prime hP central).1 b⟩

def blockEquiv (source : NavarroCentralBlockPrinciple p k) :
    LiteralPrimitiveBlock k G ≃ LiteralPrimitiveBlock k (G ⧸ P) :=
  Equiv.ofBijective (blockMap P hP central iotaDown source) ⟨
    fun b c h => (source G P iotaDown.prime hP central).2.1 b c (congrArg Subtype.val h),
    fun c => by
      obtain ⟨b, hb⟩ := (source G P iotaDown.prime hP central).2.2 c
      exact ⟨b, Subtype.ext hb⟩⟩

theorem blockEquiv_val (source : NavarroCentralBlockPrinciple p k)
    (b : LiteralPrimitiveBlock k G) :
    (blockEquiv P hP central iotaDown source b).val = quotientAlgebraMap P b.val := rfl

/-- The literal representation square across any quotient. -/
theorem algebra_action_pullback {V : Type u} [AddCommGroup V] [Module k V]
    (rho : Representation k (G ⧸ P) V) (b : k[G]) :
    (rho.pullback (QuotientGroup.mk' P)).asAlgebraHom b =
      rho.asAlgebraHom (quotientAlgebraMap P b) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [map_add, hb, hc]
  | single g a => simp [quotientAlgebraMap, Representation.asAlgebraHom_single]

/-- The principal block is tested on the literal one-dimensional trivial
representation. This definition does not select or assume a principal fibre. -/
def IsPrincipal {X : Type u} [Group X] (b : LiteralPrimitiveBlock k X) : Prop :=
  (1 : Representation k X k).asAlgebraHom b.val = 1

theorem blockEquiv_principal_iff (source : NavarroCentralBlockPrinciple p k)
    (b : LiteralPrimitiveBlock k G) :
    IsPrincipal (blockEquiv P hP central iotaDown source b) ↔ IsPrincipal b := by
  change (1 : Representation k (G ⧸ P) k).asAlgebraHom
    (quotientAlgebraMap P b.val) = 1 ↔ _
  rw [← algebra_action_pullback P]
  rfl

/-- Literal membership in a primitive block, using actual simple modules. -/
def Supported {X : Type u} [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (b : LiteralPrimitiveBlock k X) (phi : IBr iota) : Prop :=
  ∃ V : FDRep k X, Representation.IsIrreducible V.ρ ∧
    phi.val = Representation.brauerCharacterOfRootEmbedding V.ρ iota ∧
    Representation.asAlgebraHom V.ρ b.val = 1

theorem supported_inflate_iff (kernel : Navarro232Principle p k)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
    (blocks : NavarroCentralBlockPrinciple p k)
    (b : LiteralPrimitiveBlock k G) (phi : IBr iotaDown) :
    Supported (upRoot P hP iotaDown) b
        (brauerEquiv P hP iotaDown kernel regular phi) ↔
      Supported iotaDown (blockEquiv P hP central iotaDown blocks b) phi := by
  constructor
  · rintro ⟨V, hV, hchar, hsupp⟩
    have hk : (QuotientGroup.mk' P).ker ≤ V.ρ.ker := by
      simpa only [QuotientGroup.ker_mk'] using kernel G P iotaDown.prime hP V hV
    let rho := descend (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P) V.ρ hk
    have hirr : Representation.IsIrreducible rho :=
      descend_irreducible _ _ _ _ hV
    let phi' : IBr iotaDown :=
      ⟨Representation.brauerCharacterOfRootEmbedding rho iotaDown, ⟨FDRep.of rho, hirr, rfl⟩⟩
    have hinflate : brauerEquiv P hP iotaDown kernel regular phi' =
        brauerEquiv P hP iotaDown kernel regular phi := by
      apply Subtype.ext
      rw [brauerEquiv_val, hchar]
      change PrimeRegularClassFunction.pullback (QuotientGroup.mk' P)
        (Representation.brauerCharacterOfRootEmbedding rho iotaDown) = _
      rw [← Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
        rho iotaDown (upRoot P hP iotaDown) (QuotientGroup.mk' P)
        (root_compatible P hP iotaDown (FDRep.of rho))]
      rw [descend_pullback]
    have heq : phi' = phi := (brauerEquiv P hP iotaDown kernel regular).injective hinflate
    refine ⟨FDRep.of rho, hirr, (congrArg Subtype.val heq).symm, ?_⟩
    change rho.asAlgebraHom (quotientAlgebraMap P b.val) = 1
    rw [← algebra_action_pullback P, descend_pullback]
    exact hsupp
  · rintro ⟨V, hV, hchar, hsupp⟩
    let rho := Representation.pullback V.ρ (QuotientGroup.mk' P)
    refine ⟨FDRep.of rho, hV.pullback _ (QuotientGroup.mk'_surjective P), ?_, ?_⟩
    · rw [brauerEquiv_val, hchar]
      exact (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
        V.ρ iotaDown (upRoot P hP iotaDown) (QuotientGroup.mk' P)
        (root_compatible P hP iotaDown V)).symm
    · change rho.asAlgebraHom b.val = 1
      rw [algebra_action_pullback P]
      exact hsupp

/-- The equivalence is restricted only AFTER support compatibility has been
proved on literal idempotents. Its principal specialization is therefore safe. -/
def brauerBlockEquiv (kernel : Navarro232Principle p k)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
    (blocks : NavarroCentralBlockPrinciple p k) (b : LiteralPrimitiveBlock k G) :
    {phi : IBr iotaDown // Supported iotaDown
      (blockEquiv P hP central iotaDown blocks b) phi} ≃
    {psi : IBr (upRoot P hP iotaDown) // Supported (upRoot P hP iotaDown) b psi} :=
  (brauerEquiv P hP iotaDown kernel regular).subtypeEquiv
    (fun phi => (supported_inflate_iff P hP central iotaDown kernel regular blocks b phi).symm)

end ModularRep.PaperProofs.TypeBCentralKernelBlockSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
