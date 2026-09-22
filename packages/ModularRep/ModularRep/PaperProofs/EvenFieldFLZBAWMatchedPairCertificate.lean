import ModularRep.PaperProofs.EvenFieldFLZQuotientBlockFibre

/-!
# Concrete matched-pair certificates for the even-field BAW route

This module packages the relative Brough--Späth block condition with the exact
automorphism adapter used by the surrounding family.  The two additional
sources needed to identify the full Brauer fibre of the selected central
quotient block are kept in a separate completion certificate.  The module
does not define or prove the independent BAW-good relation used in
Feng--Li--Zhang, Section 3.5.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZBAWMatchedPairCertificate

open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZQuotientBlockFibre
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- Concrete matched-pair data for one literal block and one fixed universal
prime-to-`ell` cover.  The equality pins the automorphism adapter stored in the
relative witness to the independently fixed adapter used by the surrounding
family. -/
structure BroughSpathMatchedPairBlockCertificate {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (block : family.Block)
    (automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block)) : Type (u + 1) where
  relative : RelativeBlockConditionWitness family cover block
  automorphismStabilizer_eq :
    relative.automorphismStabilizer = automorphisms

namespace BroughSpathMatchedPairBlockCertificate

variable {ell : ℕ}
variable {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H}
variable {block : family.Block}
variable {automorphisms : Definition35AutomorphismStabilizerAdapter
  (family.problem block)}

/-- The single bijection already fixed by the relative block witness. -/
abbrev omega
    (certificate : BroughSpathMatchedPairBlockCertificate
      family cover block automorphisms) :=
  certificate.relative.omega

/-- The pointwise matched-pair witness at the image of the fixed bijection. -/
abbrev matched
    (certificate : BroughSpathMatchedPairBlockCertificate
      family cover block automorphisms)
    (psi : Definition35Brauer (family.problem block)) :=
  certificate.relative.matched psi

end BroughSpathMatchedPairBlockCertificate

/-- The independently graded completion of the fixed quotient block fibre.
It is not part of the Brough--Späth matched-pair certificate. -/
structure FixedQuotientFibreCompletion {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {block : family.Block}
    {automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block)}
    (certificate : BroughSpathMatchedPairBlockCertificate
      family cover block automorphisms) : Prop where
  roots : FixedQuotientRootSource certificate.relative
  reverse : QuotientBlockFibreReverseSource certificate.relative roots

namespace FixedQuotientFibreCompletion

variable {ell : ℕ}
variable {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H}
variable {block : family.Block}
variable {automorphisms : Definition35AutomorphismStabilizerAdapter
  (family.problem block)}
variable {certificate : BroughSpathMatchedPairBlockCertificate
  family cover block automorphisms}

/-- Kernel construction of the exact Brauer-fibre equivalence for the fixed
quotient block.  The equivalence is derived rather than stored in either
certificate. -/
def fixedFibreEquiv
    (completion : FixedQuotientFibreCompletion certificate) :
    Definition35Brauer (family.problem block) ≃
      FixedQuotientBrauerFibre certificate.relative :=
  originalBrauerFibreEquivFixedQuotientBrauerFibre
    certificate.relative completion.roots completion.reverse

@[simp]
theorem fixedFibreEquiv_apply
    (completion : FixedQuotientFibreCompletion certificate)
    (psi : Definition35Brauer (family.problem block)) :
    completion.fixedFibreEquiv psi =
      descentToFixedQuotientFibre
        certificate.relative completion.roots psi :=
  rfl

end FixedQuotientFibreCompletion

/-- The remaining E2/U bridge from a concrete matched-pair certificate to one
independently fixed BAW-good relation.  The relation is an index, and this
proposition asserts only that it holds at the certificate's already fixed
bijection. -/
structure BroughSpathToBAWGoodRelationSource {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {block : family.Block}
    {automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block)}
    (certificate : BroughSpathMatchedPairBlockCertificate
      family cover block automorphisms)
    (relation : FLZBAWGoodRelation
      (family.problem block) automorphisms cover) : Prop where
  relation_of_certificate :
    ∀ psi : Definition35Brauer (family.problem block),
      relation.bawGoodBlockIsomorphic psi (certificate.omega psi)

/-- Combine the BAW-good block witness from the concrete matched-pair data
and the separate assertion for the independently fixed relation. -/
def BroughSpathMatchedPairBlockCertificate.toBAWGoodBlockWitness
    {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {block : family.Block}
    {automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block)}
    {relation : FLZBAWGoodRelation
      (family.problem block) automorphisms cover}
    (certificate : BroughSpathMatchedPairBlockCertificate
      family cover block automorphisms)
    (source : BroughSpathToBAWGoodRelationSource certificate relation) :
    FLZBAWGoodBlockWitness
      (family.problem block) automorphisms cover relation where
  omega := certificate.omega
  equivariant := certificate.relative.equivariant
  blockIsomorphism := source.relation_of_certificate

/-- One exact matched-pair certificate for every block of a literal family,
all indexed by the same cover and the same family of automorphism adapters. -/
structure BroughSpathMatchedPairFamilyCertificate {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter
        (family.problem block)) : Type (u + 1) where
  blockCertificate : ∀ block : family.Block,
    BroughSpathMatchedPairBlockCertificate
      family cover block (automorphisms block)

/-- Fixed quotient-fibre completion for every block certificate in one
family.  This remains separate from the matched-pair family certificate. -/
structure FixedQuotientFibreFamilyCompletion {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block)}
    (certificate : BroughSpathMatchedPairFamilyCertificate
      family cover automorphisms) : Prop where
  blockCompletion : ∀ block : family.Block,
    FixedQuotientFibreCompletion (certificate.blockCertificate block)

namespace BroughSpathMatchedPairFamilyCertificate

variable {ell : ℕ}
variable {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H}
variable {automorphisms : ∀ block : family.Block,
  Definition35AutomorphismStabilizerAdapter (family.problem block)}

/-- Forget only the fixed quotient-fibre sources and retain the relative
block-condition witness for every block. -/
def toRelativeFamilyWitness
    (certificate : BroughSpathMatchedPairFamilyCertificate
      family cover automorphisms) :
    RelativeBlockConditionFamilyWitness family where
  cover := cover
  blockWitness block := (certificate.blockCertificate block).relative

/-- Recover the two fixed quotient-fibre sources for the relative family
witness obtained from the same certificate. -/
theorem toQuotientFibreFamilySource
    (certificate : BroughSpathMatchedPairFamilyCertificate
      family cover automorphisms)
    (completion : FixedQuotientFibreFamilyCompletion certificate) :
    QuotientBlockFibreFamilySource certificate.toRelativeFamilyWitness where
  roots block := (completion.blockCompletion block).roots
  reverse block := (completion.blockCompletion block).reverse

end BroughSpathMatchedPairFamilyCertificate

/-- The family-level E2/U assertion that each independently fixed BAW-good
relation holds at the corresponding concrete certificate's bijection. -/
structure BroughSpathToBAWGoodRelationFamilySource {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block)}
    (certificate : BroughSpathMatchedPairFamilyCertificate
      family cover automorphisms)
    (semantics : FLZBAWGoodFamilySemantics
      family cover automorphisms) : Prop where
  relation_of_certificate :
    ∀ (block : family.Block)
      (psi : Definition35Brauer (family.problem block)),
      (semantics.relation block).bawGoodBlockIsomorphic psi
        ((certificate.blockCertificate block).omega psi)

/-- Combine the BAW-good family witness from the concrete family certificate
and the separate relation source. -/
def BroughSpathMatchedPairFamilyCertificate.toBAWGoodFamilyWitness
    {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block)}
    {semantics : FLZBAWGoodFamilySemantics family cover automorphisms}
    (certificate : BroughSpathMatchedPairFamilyCertificate
      family cover automorphisms)
    (source : BroughSpathToBAWGoodRelationFamilySource
      certificate semantics) :
    FLZBAWGoodFamilyWitness family cover automorphisms semantics where
  blockWitness block :=
    (certificate.blockCertificate block).toBAWGoodBlockWitness
      { relation_of_certificate := source.relation_of_certificate block }

end ModularRep.PaperProofs.EvenFieldFLZBAWMatchedPairCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
