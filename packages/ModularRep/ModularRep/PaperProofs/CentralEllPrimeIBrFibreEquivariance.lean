import ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport

/-!
# Automorphism naturality of central `ell'` quotient `IBr` transport

This source-neutral module proves the automorphism square for the literal
equivalence between `IBr (G / Z)` and the trivial central character fibre in
`IBr G`.  The only automorphism datum is a descent homomorphism together with
its pointwise commuting square with `QuotientGroup.mk' Z`.  No character
equivalence or equivariance conclusion is accepted as a premise.

The cover-fibre action is constructed from the existing literal `IBr` twist.
Its closure proof uses only the central character/kernel bridge.  Naturality
of inflation is then equality of pulled-back prime regular class functions.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.CentralEllPrimeIBrFibreEquivariance

open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport

universe u

/-! ## The elementary commuting-square consequences -/

variable {p : ℕ} {K G H : Type u}
variable [Group G] [Group H]

/-- Pullback of prime regular class functions commutes with automorphism
twists whenever the underlying homomorphism square commutes. -/
theorem pullback_twist_of_commuting
    (q : G →* H) (alpha : MulAut G) (beta : MulAut H)
    (hcomm : ∀ g : G, q (alpha g) = beta (q g))
    (phi : PrimeRegularClassFunction K H p) :
    PrimeRegularClassFunction.pullback q (phi.twist beta) =
      (PrimeRegularClassFunction.pullback q phi).twist alpha := by
  apply PrimeRegularClassFunction.ext
  intro g
  exact congrArg phi (Subtype.ext (hcomm g.1).symm)

variable {Z : Subgroup G} [Z.Normal]

/-- A commuting quotient-automorphism square forces the cover automorphism
to carry the quotient kernel into itself. -/
theorem quotientSquare_maps_mem
    (alpha : MulAut G) (beta : MulAut (G ⧸ Z))
    (hcomm : ∀ g : G,
      QuotientGroup.mk' Z (alpha g) = beta (QuotientGroup.mk' Z g))
    {z : G} (hz : z ∈ Z) :
    alpha z ∈ Z := by
  apply (QuotientGroup.eq_one_iff (alpha z)).mp
  calc
    QuotientGroup.mk' Z (alpha z) =
        beta (QuotientGroup.mk' Z z) := hcomm z
    _ = beta 1 := congrArg beta ((QuotientGroup.eq_one_iff z).mpr hz)
    _ = 1 := map_one beta

/-! ## The literal trivial-fibre twist -/

variable {k : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Fintype G]

noncomputable local instance subgroupFintype : Fintype Z :=
  Fintype.ofFinite Z

variable (coverIota : PrimeRegularRootEmbedding p k K G)
variable {BlockIndex : Type u} [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[G]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (coverHinj : IrreducibleBrauerCharacterInjectivity coverIota)
variable (hZ : Z ≤ Subgroup.center G)
variable [Invertible (Fintype.card Z : k)]

/-- The literal automorphism twist preserves the trivial
block-central character fibre when it descends through `G / Z`.

The proof does not assume block transport.  It passes from the fibre equation
to the kernel of an affording representation, uses the quotient square to
show that the twisted representation still kills `Z`, and returns to the
block-defined central character. -/
def twistTrivialCentralCharacterFibre
    (alpha : MulAut G) (beta : MulAut (G ⧸ Z))
    (hcomm : ∀ g : G,
      QuotientGroup.mk' Z (alpha g) = beta (QuotientGroup.mk' Z g))
    (phi : TrivialCentralCharacterFibre coverIota blocks coverHinj hZ) :
    TrivialCentralCharacterFibre coverIota blocks coverHinj hZ := by
  let V := affordingRepresentation coverIota phi.1
  have hV : Representation.IsIrreducible V.ρ :=
    affordingRepresentation_irreducible coverIota phi.1
  let _ : Representation.IsIrreducible V.ρ := hV
  let rhoTw := Representation.twist V.ρ alpha
  have hTw : Representation.IsIrreducible rhoTw := hV.twist alpha
  let _ : Representation.IsIrreducible rhoTw := hTw
  let Vtw : FDRep k G := FDRep.of rhoTw
  let _ : Representation.IsIrreducible Vtw.ρ := by
    change Representation.IsIrreducible rhoTw
    exact hTw
  refine ⟨IrreducibleBrauerCharacter.twist coverIota phi.1 alpha, ?_⟩
  have hcharacter :
      phi.1.1 = Representation.brauerCharacterOfRootEmbedding V.ρ coverIota :=
    affordingRepresentation_character coverIota phi.1
  have hcentral :
      Representation.centralCharacter V.ρ Z hZ = 1 := by
    calc
      Representation.centralCharacter V.ρ Z hZ =
          blockCentralCharacter coverIota blocks coverHinj hZ phi.1 :=
        (blockCentralCharacter_eq_of_affords coverIota blocks coverHinj hZ
          phi.1 V hcharacter).symm
      _ = 1 := phi.2
  have hkernel : Z ≤ V.ρ.ker :=
    le_ker_of_centralCharacter_eq_one (Z := Z) hZ V.ρ hcentral
  have hkernelTw : Z ≤ rhoTw.ker := by
    intro z hz
    have hzalpha : alpha z ∈ Z :=
      quotientSquare_maps_mem (Z := Z) alpha beta hcomm hz
    have hzker := hkernel hzalpha
    change V.ρ (alpha z) = 1 at hzker
    change V.ρ (alpha z) = LinearMap.id
    simpa only [Module.End.one_eq_id] using hzker
  have hcharacterTw :
      (IrreducibleBrauerCharacter.twist coverIota phi.1 alpha).1 =
        Representation.brauerCharacterOfRootEmbedding Vtw.ρ coverIota := by
    change phi.1.1.twist alpha =
      Representation.brauerCharacterOfRootEmbedding rhoTw coverIota
    calc
      phi.1.1.twist alpha =
          (Representation.brauerCharacterOfRootEmbedding V.ρ coverIota).twist
            alpha := congrArg (fun chi ↦ chi.twist alpha) hcharacter
      _ = Representation.brauerCharacterOfRootEmbedding
          (Representation.twist V.ρ alpha) coverIota :=
        (Representation.brauerCharacterOfRootEmbedding_twist
          V.ρ coverIota alpha).symm
      _ = Representation.brauerCharacterOfRootEmbedding rhoTw coverIota :=
        rfl
  calc
    blockCentralCharacter coverIota blocks coverHinj hZ
        (IrreducibleBrauerCharacter.twist coverIota phi.1 alpha) =
      Representation.centralCharacter Vtw.ρ Z hZ :=
        blockCentralCharacter_eq_of_affords coverIota blocks coverHinj hZ
          (IrreducibleBrauerCharacter.twist coverIota phi.1 alpha) Vtw
          hcharacterTw
    _ = Representation.centralCharacter rhoTw Z hZ := rfl
    _ = 1 :=
      centralCharacter_eq_one_of_le_ker (Z := Z) hZ rhoTw hkernelTw

/-! ## Descent actions and naturality of the constructed equivalence -/

variable (quotientIota : PrimeRegularRootEmbedding p k K (G ⧸ Z))
variable (source : QuotientRealisationSource Z coverIota quotientIota)

omit [Invertible (Fintype.card Z : k)] in
/-- Literal inflation commutes with one pair of automorphisms satisfying the
quotient square.  Root compatibility is used only through the already
constructed `inflateIBr`; naturality of its underlying class function is
formal. -/
theorem inflateIBr_twist_of_quotientSquare
    (alpha : MulAut G) (beta : MulAut (G ⧸ Z))
    (hcomm : ∀ g : G,
      QuotientGroup.mk' Z (alpha g) = beta (QuotientGroup.mk' Z g))
    (phi : IBr quotientIota) :
    inflateIBr coverIota quotientIota source
        (IrreducibleBrauerCharacter.twist quotientIota phi beta) =
      IrreducibleBrauerCharacter.twist coverIota
        (inflateIBr coverIota quotientIota source phi) alpha := by
  apply Subtype.ext
  change PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z)
      (phi.1.twist beta) =
    (PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) phi.1).twist
      alpha
  exact pullback_twist_of_commuting (QuotientGroup.mk' Z) alpha beta hcomm
    phi.1

/-- Restrict the quotient `IBr` action along an explicit automorphism-descent
homomorphism. -/
@[instance_reducible]
def quotientIBrMulAction
    (descent : (MulAut G)ᵐᵒᵖ →* (MulAut (G ⧸ Z))ᵐᵒᵖ) :
    MulAction (MulAut G)ᵐᵒᵖ (IBr quotientIota) :=
  MulAction.compHom _ descent

/-- The canonical cover action on the trivial fibre, constructed from the
literal `IBr` twist and the commuting quotient square. -/
@[instance_reducible]
def trivialCentralCharacterFibreMulAction
    (descent : (MulAut G)ᵐᵒᵖ →* (MulAut (G ⧸ Z))ᵐᵒᵖ)
    (hcomm : ∀ (a : (MulAut G)ᵐᵒᵖ) (g : G),
      QuotientGroup.mk' Z (a.unop g) =
        (descent a).unop (QuotientGroup.mk' Z g)) :
    MulAction (MulAut G)ᵐᵒᵖ
      (TrivialCentralCharacterFibre coverIota blocks coverHinj hZ) where
  smul a phi :=
    twistTrivialCentralCharacterFibre coverIota blocks coverHinj hZ
      a.unop (descent a).unop (hcomm a) phi
  one_smul phi := by
    apply Subtype.ext
    change IrreducibleBrauerCharacter.twist coverIota phi.1
        (MulOpposite.unop 1) = phi.1
    rw [MulOpposite.unop_one]
    exact IrreducibleBrauerCharacter.twist_refl coverIota phi.1
  mul_smul a b phi := by
    apply Subtype.ext
    change IrreducibleBrauerCharacter.twist coverIota phi.1
        (MulOpposite.unop (a * b)) =
      IrreducibleBrauerCharacter.twist coverIota
        (IrreducibleBrauerCharacter.twist coverIota phi.1 b.unop) a.unop
    rw [MulOpposite.unop_mul]
    exact (IrreducibleBrauerCharacter.twist_mul coverIota phi.1
      b.unop a.unop).symm

section DescentAction

variable (descent : (MulAut G)ᵐᵒᵖ →* (MulAut (G ⧸ Z))ᵐᵒᵖ)
variable (hcomm : ∀ (a : (MulAut G)ᵐᵒᵖ) (g : G),
  QuotientGroup.mk' Z (a.unop g) =
    (descent a).unop (QuotientGroup.mk' Z g))

/-- The constructed quotient/fibre equivalence is equivariant.  The source
surface is exactly the root-realisation source, the descent homomorphism, and
the commuting quotient square. -/
theorem quotientIBrEquivTrivialCentralCharacterFibre_equivariant
    (a : (MulAut G)ᵐᵒᵖ) (phi : IBr quotientIota) :
    letI : MulAction (MulAut G)ᵐᵒᵖ (IBr quotientIota) :=
      quotientIBrMulAction quotientIota descent
    letI : MulAction (MulAut G)ᵐᵒᵖ
        (TrivialCentralCharacterFibre coverIota blocks coverHinj hZ) :=
      trivialCentralCharacterFibreMulAction coverIota blocks coverHinj hZ
        descent hcomm
    quotientIBrEquivTrivialCentralCharacterFibre coverIota quotientIota source
        blocks coverHinj hZ (a • phi) =
      a • quotientIBrEquivTrivialCentralCharacterFibre coverIota quotientIota
        source blocks coverHinj hZ phi := by
  let _ : MulAction (MulAut G)ᵐᵒᵖ (IBr quotientIota) :=
    quotientIBrMulAction quotientIota descent
  let _ : MulAction (MulAut G)ᵐᵒᵖ
      (TrivialCentralCharacterFibre coverIota blocks coverHinj hZ) :=
    trivialCentralCharacterFibreMulAction coverIota blocks coverHinj hZ
      descent hcomm
  apply Subtype.ext
  change inflateIBr coverIota quotientIota source
      (IrreducibleBrauerCharacter.twist quotientIota phi (descent a).unop) =
    IrreducibleBrauerCharacter.twist coverIota
      (inflateIBr coverIota quotientIota source phi) a.unop
  exact inflateIBr_twist_of_quotientSquare coverIota quotientIota source
    a.unop (descent a).unop (hcomm a) phi

/-- Equivariance of the inverse (the direction used by a cover-to-quotient
carrier transport) is a formal consequence of the forward square. -/
theorem quotientIBrEquivTrivialCentralCharacterFibre_symm_equivariant
    (a : (MulAut G)ᵐᵒᵖ)
    (phi : TrivialCentralCharacterFibre coverIota blocks coverHinj hZ) :
    letI : MulAction (MulAut G)ᵐᵒᵖ (IBr quotientIota) :=
      quotientIBrMulAction quotientIota descent
    letI : MulAction (MulAut G)ᵐᵒᵖ
        (TrivialCentralCharacterFibre coverIota blocks coverHinj hZ) :=
      trivialCentralCharacterFibreMulAction coverIota blocks coverHinj hZ
        descent hcomm
    (quotientIBrEquivTrivialCentralCharacterFibre coverIota quotientIota
        source blocks coverHinj hZ).symm (a • phi) =
      a • (quotientIBrEquivTrivialCentralCharacterFibre coverIota quotientIota
        source blocks coverHinj hZ).symm phi := by
  let _ : MulAction (MulAut G)ᵐᵒᵖ (IBr quotientIota) :=
    quotientIBrMulAction quotientIota descent
  let _ : MulAction (MulAut G)ᵐᵒᵖ
      (TrivialCentralCharacterFibre coverIota blocks coverHinj hZ) :=
    trivialCentralCharacterFibreMulAction coverIota blocks coverHinj hZ
      descent hcomm
  let E := quotientIBrEquivTrivialCentralCharacterFibre coverIota quotientIota
    source blocks coverHinj hZ
  apply E.injective
  calc
    E (E.symm (a • phi)) = a • phi := E.apply_symm_apply (a • phi)
    _ = a • E (E.symm phi) :=
      congrArg (fun psi ↦ a • psi) (E.apply_symm_apply phi).symm
    _ = E (a • E.symm phi) :=
      (quotientIBrEquivTrivialCentralCharacterFibre_equivariant
        (coverIota := coverIota) (quotientIota := quotientIota)
        (source := source) (blocks := blocks) (coverHinj := coverHinj)
        (hZ := hZ) (descent := descent) (hcomm := hcomm) a
        (E.symm phi)).symm

end DescentAction

end ModularRep.PaperProofs.CentralEllPrimeIBrFibreEquivariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
