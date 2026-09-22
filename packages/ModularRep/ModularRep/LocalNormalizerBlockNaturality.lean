import ModularRep.LocalNormalizerBlockOperations
import ModularRep.WeightCharacterBridge

/-!
# Naturality of the local normaliser block operations

The character of a weight has canonical transport along an automorphism of
the ambient group, and that automorphism also gives canonical equivalences of
the corresponding normaliser quotient and normaliser.  This file packages
the one compatibility still needed from externally supplied local block
operations: selecting the block of the transported character and inflating it
must give the transport of the original inflated block.

The source law is uniform in the subgroup, defect-zero character, and
automorphism.  It contains no ambient block, table row, chosen representative,
or block-induction assertion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.CharacterWeight

universe u

variable {p : Nat} {k K G : Type u}
variable [Field k] [Field K] [CharZero K]
variable [Group G] [Fintype G]

/-- Transport a literal primitive normaliser block along an equivalence of
normalisers. -/
def inflatedNormalizerBlockAlongMulEquiv
    {Q R : Subgroup G}
    (e : Subgroup.normalizer (Q : Set G) ≃*
      Subgroup.normalizer (R : Set G))
    (b : InflatedNormalizerBlock (k := k) Q) :
    InflatedNormalizerBlock (k := k) R :=
  ⟨MonoidAlgebra.domCongr k k e b.1,
    b.2.mapRingEquiv (MonoidAlgebra.domCongr k k e).toRingEquiv⟩

omit [Fintype G] in
@[simp]
theorem inflatedNormalizerBlockAlongMulEquiv_idempotent
    {Q R : Subgroup G}
    (e : Subgroup.normalizer (Q : Set G) ≃*
      Subgroup.normalizer (R : Set G))
    (b : InflatedNormalizerBlock (k := k) Q) :
    inflatedNormalizerBlockIdempotent (k := k) R
        (inflatedNormalizerBlockAlongMulEquiv e b) =
      MonoidAlgebra.domCongr k k e
        (inflatedNormalizerBlockIdempotent (k := k) Q b) :=
  rfl

omit [Fintype G] in
/-- Transporting a literal normaliser block successively agrees with
transport along the composite equivalence. -/
theorem inflatedNormalizerBlockAlongMulEquiv_trans
    {Q R S : Subgroup G}
    (e : Subgroup.normalizer (Q : Set G) ≃*
      Subgroup.normalizer (R : Set G))
    (f : Subgroup.normalizer (R : Set G) ≃*
      Subgroup.normalizer (S : Set G))
    (b : InflatedNormalizerBlock (k := k) Q) :
    inflatedNormalizerBlockAlongMulEquiv f
        (inflatedNormalizerBlockAlongMulEquiv e b) =
      inflatedNormalizerBlockAlongMulEquiv (e.trans f) b := by
  apply Subtype.ext
  exact congrArg
    (fun sigma : k[Subgroup.normalizer (Q : Set G)] ≃ₐ[k]
        k[Subgroup.normalizer (S : Set G)] ↦ sigma b.1)
    (MonoidAlgebra.trans_domCongr_domCongr (R := k) (A := k) e f)

/-- The local normaliser block attached by the two externally supplied
operations to a defect-zero quotient character. -/
def LocalNormalizerBlockOperations.attachedNormalizerBlock
    {Q : Subgroup G}
    (O : LocalNormalizerBlockOperations
      (p := p) (k := k) (K := K) (G := G) Q)
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
    (hchi : IsDefectZeroOrdinaryCharacter p chi) :
    InflatedNormalizerBlock (k := k) Q :=
  O.inflateToNormalizer (O.localCharacterBlock chi hchi)

/-- Attached blocks respect literal equality of the subgroup and of the
dependently transported character.  No compatibility of independently
chosen operations is used here: after eliminating the subgroup equality,
both sides are applications of the same functions. -/
theorem LocalNormalizerBlockOperations.attachedNormalizerBlock_along_subgroup_eq
    {operations : ∀ Q : Subgroup G,
      LocalNormalizerBlockOperations
        (p := p) (k := k) (K := K) (G := G) Q}
    {Q R : Subgroup G} (hQ : Q = R)
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
    (chi' : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient R))
    (hchi : CharacterWeight.castLocalCharacter hQ chi = chi')
    (hdz : IsDefectZeroOrdinaryCharacter p chi)
    (hdz' : IsDefectZeroOrdinaryCharacter p chi') :
    inflatedNormalizerBlockAlongMulEquiv
        (MulEquiv.cast
          (M := fun S : Subgroup G ↦
            Subgroup.normalizer (S : Set G)) hQ)
        ((operations Q).attachedNormalizerBlock chi hdz) =
      (operations R).attachedNormalizerBlock chi' hdz' := by
  subst R
  change chi = chi' at hchi
  subst chi'
  have hdzEq : hdz = hdz' := Subsingleton.elim _ _
  subst hdz'
  apply Subtype.ext
  change MonoidAlgebra.domCongr k k
      (MulEquiv.cast
        (M := fun S : Subgroup G ↦
          Subgroup.normalizer (S : Set G)) rfl)
      ((operations Q).attachedNormalizerBlock chi hdz).1 =
    ((operations Q).attachedNormalizerBlock chi hdz).1
  rw [show
      MulEquiv.cast
          (M := fun S : Subgroup G ↦
            Subgroup.normalizer (S : Set G)) rfl =
        MulEquiv.refl (Subgroup.normalizer (Q : Set G)) from rfl,
    MonoidAlgebra.domCongr_refl]
  rfl

/-- Canonical forward transport of a normaliser block from `Q` to the
subgroup occurring in the right twist by `alpha`. -/
def inflatedNormalizerBlockAlongRightTwist
    (Q : Subgroup G) (alpha : MulAut G)
    (b : InflatedNormalizerBlock (k := k) Q) :
    InflatedNormalizerBlock (k := k) (Q.comap alpha.toMonoidHom) :=
  inflatedNormalizerBlockAlongMulEquiv
    (rightNormalizerEquiv alpha Q).symm b

omit [Fintype G] in
@[simp]
theorem inflatedNormalizerBlockAlongRightTwist_idempotent
    (Q : Subgroup G) (alpha : MulAut G)
    (b : InflatedNormalizerBlock (k := k) Q) :
    inflatedNormalizerBlockIdempotent (k := k)
        (Q.comap alpha.toMonoidHom)
        (inflatedNormalizerBlockAlongRightTwist Q alpha b) =
      MonoidAlgebra.domCongr k k (rightNormalizerEquiv alpha Q).symm
        (inflatedNormalizerBlockIdempotent (k := k) Q b) :=
  rfl

/-- Uniform naturality source for the composite "take the local character
block, then inflate it" operation.

This is deliberately one composite law: it is the weakest operation-level
compatibility needed by consumers which only use the attached normaliser
block.  In particular it does not demand separately chosen transports of
quotient-block labels. -/
structure LocalNormalizerBlockOperations.RightTwistNaturality
    (operations : ∀ Q : Subgroup G,
      LocalNormalizerBlockOperations
        (p := p) (k := k) (K := K) (G := G) Q) : Prop where
  attachedNormalizerBlock_rightTwist :
    ∀ (Q : Subgroup G)
      (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
      (hchi : IsDefectZeroOrdinaryCharacter p chi)
      (alpha : MulAut G),
      inflatedNormalizerBlockAlongRightTwist Q alpha
          ((operations Q).attachedNormalizerBlock chi hchi) =
        (operations (Q.comap alpha.toMonoidHom)).attachedNormalizerBlock
          (OrdinaryIrreducibleCharacter.mapEquiv chi
            (rightNormalizerQuotientEquiv alpha Q).symm)
          (hchi.mapEquiv (rightNormalizerQuotientEquiv alpha Q).symm)

namespace LocalNormalizerBlockOperations.RightTwistNaturality

variable {operations : ∀ Q : Subgroup G,
  LocalNormalizerBlockOperations
    (p := p) (k := k) (K := K) (G := G) Q}

/-- Idempotent form of the naturality source.  This is a theorem obtained by
forgetting the primitive-idempotent proofs in the literal block equality. -/
theorem attachedNormalizerBlock_idempotent_rightTwist
    (N : LocalNormalizerBlockOperations.RightTwistNaturality operations)
    (Q : Subgroup G)
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
    (hchi : IsDefectZeroOrdinaryCharacter p chi)
    (alpha : MulAut G) :
    MonoidAlgebra.domCongr k k (rightNormalizerEquiv alpha Q).symm
        (inflatedNormalizerBlockIdempotent (k := k) Q
          ((operations Q).attachedNormalizerBlock chi hchi)) =
      inflatedNormalizerBlockIdempotent (k := k)
        (Q.comap alpha.toMonoidHom)
        ((operations (Q.comap alpha.toMonoidHom)).attachedNormalizerBlock
          (OrdinaryIrreducibleCharacter.mapEquiv chi
            (rightNormalizerQuotientEquiv alpha Q).symm)
          (hchi.mapEquiv (rightNormalizerQuotientEquiv alpha Q).symm)) := by
  exact congrArg Subtype.val
    (N.attachedNormalizerBlock_rightTwist Q chi hchi alpha)

end LocalNormalizerBlockOperations.RightTwistNaturality

end ModularRep.CharacterWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
