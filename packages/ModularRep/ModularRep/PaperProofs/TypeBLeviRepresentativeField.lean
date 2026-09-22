import ModularRep.PaperProofs.TypeBCharacteristicTwoConstituentSource
import ModularRep.PaperProofs.TypeBComponentReturnCarrierTransport
import ModularRep.PaperProofs.TypeBTwoCommon
import ModularRep.BrauerCharacterExtensionBridge

/-!
# Full field promotion and the actual Levi semidirect extension

Supporting deduction for canonical `03b-type-b.tex`, SHA256
9FEDDE026114148802FA26D24D8DB73C335846622C5297EE3B9FBE868FA806B9,
lines 961--980. Gamma is the actual rational paired Levi, H its L subgroup,
N its L0 subgroup, and E the finite cyclic field group on these fixed points.
All character actions below are the existing inverse-pullback actions.

Inputs: the SAME roots, psi, theta and literal restriction occurrence used
in the preceding construction; Navarro 8.7 on these roots; the preceding
K factorization over the ACTUAL setwise stabilizer of Gamma's theta orbit;
and the universal Navarro 8.12 cyclic representation-extension principle.
The local factorization is an intermediate proved result, not an external
source designation. No full field factorization, field-fixer equality,
conjugation invariance, extension, or character-action faithfulness is input.

Lean derives constituent return and full field promotion. For extension it
uses the literal group H semidirect E_psi, identifies H with the kernel of
its right projection, and transports the SAME root and character along that
canonical equivalence. Quotient cyclicity and conjugation invariance are K
deductions. The output is an honest irreducible representation of this
literal semidirect group, with an exact restriction equivalence to one
representation of the original H affording psi. This helper alone has no
standalone manuscript-window acceptance credit.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeField

open ModularRep
open TypeBLemma47LeviApplication TypeBCharacteristicTwoConstituentSource
open ModularRep.ManuscriptVerification.CharacteristicTwoClifford

universe u

section FieldFixer

variable {H E k K : Type u} [Group H] [Finite H] [Group E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The actual stabilizer for the canonical field action on the original
function-valued Brauer character. -/
def fieldStabilizer (iota : PrimeRegularRootEmbedding 2 k K H)
    (phi : E →* MulAut H) (psi : IBr iota) : Subgroup E := by
  letI := EvenFieldAssumption53Relative.rightAutomorphismAction iota phi
  exact MulAction.stabilizer E psi

/-- The exact group requested by the manuscript extension conclusion. -/
abbrev FieldSemidirect (iota : PrimeRegularRootEmbedding 2 k K H)
    (phi : E →* MulAut H) (psi : IBr iota) :=
  H ⋊[phi.comp (fieldStabilizer iota phi psi).subtype]
    fieldStabilizer iota phi psi

end FieldFixer

section Promotion

variable {Gamma E k K : Type u} [Group Gamma] [Finite Gamma] [Group E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (H N : Subgroup Gamma) [H.Normal] [N.Normal] (hNH : N ≤ H)
variable (iotaH : PrimeRegularRootEmbedding 2 k K H)
variable (iotaN : PrimeRegularRootEmbedding 2 k K N)
variable (field : E →* MulAut Gamma)
variable (hH : ∀ e : E, ∀ g : Gamma, g ∈ H ↔ field e g ∈ H)
variable (hN : ∀ e : E, ∀ g : Gamma, g ∈ N ↔ field e g ∈ N)

local instance ambientH : MulAction Gamma (IBr iotaH) := ambientBrauerAction H iotaH
local instance ambientN : MulAction Gamma (IBr iotaN) := ambientBrauerAction N iotaN

/-- D_O is the literal setwise stabilizer of the constituent orbit, using
the same orbit carrier as the component-return transport. -/
def orbitFieldStabilizer (theta : IBr iotaN) : Subgroup E := by
  letI := fieldBrauerAction N iotaN field hN
  exact TypeBComponentReturnCarrierTransport.orbitStabilizer
    (D := Gamma) (E := E) theta

theorem mem_orbitFieldStabilizer_iff (theta : IBr iotaN) (e : E) :
    e ∈ orbitFieldStabilizer N iotaN field hN theta ↔
      letI := fieldBrauerAction N iotaN field hN;
      TypeBTwoCommon.OrbitSetwiseStable (A := Gamma) theta e := by
  letI := fieldBrauerAction N iotaN field hN
  change (fun x : IBr iotaN => e • x) '' MulAction.orbit Gamma theta =
      MulAction.orbit Gamma theta ↔
    ∀ x : IBr iotaN,
      x ∈ MulAction.orbit Gamma theta ↔ e • x ∈ MulAction.orbit Gamma theta
  constructor
  · intro he x
    constructor
    · intro hx
      rw [← he]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← he] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      exact (MulAction.injective e hxy) ▸ hy
  · intro he
    apply Set.ext
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (he y).mp hy
    · intro hx
      refine ⟨e⁻¹ • x, ?_, smul_inv_smul e x⟩
      apply (he (e⁻¹ • x)).mpr
      simpa only [smul_inv_smul] using hx

/-- The combined fixer returns the SAME chosen constituent to its ambient
orbit. The witness is obtained from literal Clifford restriction support. -/
theorem constituent_return
    (roots : RootAgreement H N iotaH iotaN)
    (navarro : Navarro87Principle k K)
    (psi : IBr iotaH) (theta : IBr iotaN)
    (chosen : Occurs H N hNH iotaH iotaN psi theta)
    (a : Gamma) (e : E)
    (fixed : letI := fieldBrauerAction H iotaH field hH;
      a • (e • psi) = psi) :
    letI := fieldBrauerAction N iotaN field hN;
    e • theta ∈ MulAction.orbit Gamma theta := by
  letI := fieldBrauerAction H iotaH field hH
  letI := fieldBrauerAction N iotaN field hN
  let constituents := constituentOrbit H N hNH iotaH iotaN roots
    field hH hN navarro psi theta chosen
  obtain ⟨h, hh⟩ := adjust_to_fix_constituent H.subtype psi theta
    constituents fixed
  change ((h : Gamma) * a) • (e • theta) = theta at hh
  refine MulAction.mem_orbit_iff.mpr ⟨((h : Gamma) * a)⁻¹, ?_⟩
  calc
    ((h : Gamma) * a)⁻¹ • theta =
        ((h : Gamma) * a)⁻¹ • (((h : Gamma) * a) • (e • theta)) := by rw [hh]
    _ = e • theta := inv_smul_smul _ _

/-- The local EO-fixer and full E-fixer coincide as actual subgroups of E.
The left side maps the literal stabilizer inside EO through its inclusion. -/
theorem local_field_stabilizer_image
    (roots : RootAgreement H N iotaH iotaN)
    (navarro : Navarro87Principle k K)
    (psi : IBr iotaH) (theta : IBr iotaN)
    (chosen : Occurs H N hNH iotaH iotaN psi theta) :
    (fieldStabilizer iotaH
      ((restrictAutomorphismHom H field hH).comp
        (orbitFieldStabilizer N iotaN field hN theta).subtype) psi).map
        (orbitFieldStabilizer N iotaN field hN theta).subtype =
      fieldStabilizer iotaH (restrictAutomorphismHom H field hH) psi := by
  letI := fieldBrauerAction H iotaH field hH
  letI := fieldBrauerAction N iotaN field hN
  ext e
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact hd
  · intro he
    have hfix : e • psi = psi := he
    have hstable :=
      (TypeBTwoCommon.field_fix_iff_orbitSetwiseStable_and_field_fix
        field (field_ambient_semidirect_compatible N iotaN field hN)
        theta psi e
        (constituent_return H N hNH iotaH iotaN field hH hN
          roots navarro psi theta chosen)).mp hfix
    have heO : e ∈ orbitFieldStabilizer N iotaN field hN theta :=
      (mem_orbitFieldStabilizer_iff N iotaN field hN theta e).mpr hstable.1
    exact ⟨⟨e, heO⟩, he, rfl⟩

/-- Promotion from the previously proved local factorization over EO to
the full actual semidirect action. Each field element of a combined fixer
lies in EO by constituent return; no final stabilizer premise is supplied. -/
theorem full_field_factorization
    (roots : RootAgreement H N iotaH iotaN)
    (navarro : Navarro87Principle k K)
    (psi : IBr iotaH) (theta : IBr iotaN)
    (chosen : Occurs H N hNH iotaH iotaN psi theta)
    (localFactorization :
      letI := fieldBrauerAction H iotaH field hH;
      ∀ a : Gamma,
      ∀ e : orbitFieldStabilizer N iotaN field hN theta,
        a • ((e : E) • psi) = psi ↔ a • psi = psi ∧ (e : E) • psi = psi) :
    letI := fieldBrauerAction H iotaH field hH;
    Formalisation.SemidirectStabilizerFactors field
      (field_ambient_semidirect_compatible H iotaH field hH) psi := by
  letI := fieldBrauerAction H iotaH field hH
  letI := fieldBrauerAction N iotaN field hN
  have hfull := TypeBTwoCommon.productStabilizerFactorization_of_orbit_stabilizer
    field (field_ambient_semidirect_compatible N iotaN field hN)
    theta psi
    (constituent_return H N hNH iotaH iotaN field hH hN
      roots navarro psi theta chosen)
    (fun a e he => localFactorization a
      ⟨e, (mem_orbitFieldStabilizer_iff N iotaN field hN theta e).mpr he⟩)
  intro x
  exact hfull x.left x.right

end Promotion

section HonestExtension

variable {H E k K : Type u} [Group H] [Finite H] [Group E] [Finite E] [IsCyclic E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- Original H identified with the actual kernel of the right projection.
The underlying semidirect element of the image is exactly inl h. -/
def leftKernelEquiv (phi : E →* MulAut H) :
    H ≃* (SemidirectProduct.rightHom (φ := phi)).ker where
  toFun h := ⟨SemidirectProduct.inl h, rfl⟩
  invFun x := x.1.left
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact x.2.symm
  map_mul' h g := by
    apply Subtype.ext
    exact map_mul (SemidirectProduct.inl : H →* H ⋊[phi] E) h g

@[simp] theorem leftKernelEquiv_coe (phi : E →* MulAut H) (h : H) :
    ((leftKernelEquiv phi h : (SemidirectProduct.rightHom (φ := phi)).ker) :
      H ⋊[phi] E) = SemidirectProduct.inl h := rfl

/-- Conjugation in the displayed semidirect group acts on its left kernel
by the actual inner automorphism followed by its actual field coordinate. -/
theorem leftKernel_conjugation (phi : E →* MulAut H)
    (d : H ⋊[phi] E) (n : (SemidirectProduct.rightHom (φ := phi)).ker) :
    (leftKernelEquiv phi).symm (MulAut.conjNormal d n) =
      (MulAut.conj d.left * phi d.right) ((leftKernelEquiv phi).symm n) := by
  have hn : n.1.right = 1 := n.2
  change (d * n.1 * d⁻¹).left = d.left * phi d.right n.1.left * d.left⁻¹
  simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, hn, mul_assoc]

/-- An extension on literal H semidirect E_psi. W is a representation
of the ORIGINAL H affording psi for the SAME original root; rho is an
irreducible representation of the displayed semidirect group and its
restriction along the actual inl is equivalent to W. -/
theorem honest_field_extension
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (phi : E →* MulAut H)
    (navarro : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k)
    (psi : IBr iota) :
    ∃ W : FDRep k H,
      Representation.IsIrreducible W.ρ ∧
      psi.1 = Representation.brauerCharacterOfRootEmbedding W.ρ iota ∧
      ∃ rho : Representation k (FieldSemidirect iota phi psi) W,
        Representation.IsIrreducible rho ∧
        Nonempty (Representation.Equiv
          (rho.pullback (SemidirectProduct.inl : H →* FieldSemidirect iota phi psi))
          W.ρ) := by
  let S := fieldStabilizer iota phi psi
  let phiS := phi.comp S.subtype
  let M := H ⋊[phiS] S
  let N : Subgroup M := (SemidirectProduct.rightHom (φ := phiS)).ker
  letI : Finite M := Finite.of_equiv (H × S) SemidirectProduct.equivProd.symm
  let eH : H ≃* N := leftKernelEquiv phiS
  let iotaN := iota.alongMulEquiv eH
  let psiN := IrreducibleBrauerCharacter.alongMulEquiv iota eH psi
  have hfield : ∀ d : S,
      IrreducibleBrauerCharacter.twist iota psi (phiS d) = psi := by
    intro d
    change IrreducibleBrauerCharacter.twist iota psi (phi (d : E)) = psi
    have hd := (d⁻¹).2
    change IrreducibleBrauerCharacter.twist iota psi (phi ((d⁻¹ : S) : E)⁻¹) = psi at hd
    simpa only [Subgroup.coe_inv, inv_inv] using hd
  have hfixed : ∀ d : M,
      IrreducibleBrauerCharacter.twist iotaN psiN (MulAut.conjNormal d) = psiN := by
    intro d
    have hpsi : IrreducibleBrauerCharacter.twist iota psi
        (MulAut.conj d.left * phiS d.right) = psi := by
      rw [← IrreducibleBrauerCharacter.twist_mul]
      have hinner : IrreducibleBrauerCharacter.twist iota psi
          (MulAut.conj d.left) = psi := by
        apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
        exact PrimeRegularClassFunction.twist_conj psi.1 d.left
      rw [hinner]
      exact hfield d.right
    apply Subtype.ext
    apply PrimeRegularClassFunction.ext
    intro x
    change psi.1 (PrimeRegularElement.map eH.symm.toMonoidHom
        (PrimeRegularElement.map (MulAut.conjNormal d).toMonoidHom x)) =
      psi.1 (PrimeRegularElement.map eH.symm.toMonoidHom x)
    have hsquare : PrimeRegularElement.map eH.symm.toMonoidHom
        (PrimeRegularElement.map (MulAut.conjNormal d).toMonoidHom x) =
        PrimeRegularElement.map (MulAut.conj d.left * phiS d.right).toMonoidHom
          (PrimeRegularElement.map eH.symm.toMonoidHom x) := by
      apply Subtype.ext
      exact leftKernel_conjugation phiS d x.1
    rw [hsquare]
    exact congrArg (fun chi : IBr iota =>
      chi.1 (PrimeRegularElement.map eH.symm.toMonoidHom x)) hpsi
  have hcyclic : IsCyclic (M ⧸ N) :=
    isCyclic_of_injective
      (SemidirectProduct.toGroupExtension phiS).quotientKerRightHomEquivRight.toMonoidHom
      (SemidirectProduct.toGroupExtension phiS).quotientKerRightHomEquivRight.injective
  obtain ⟨W0, hW0, hcharacter, ⟨extension⟩⟩ :=
    Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
      navarro iotaN psiN hcyclic hfixed
  let W : FDRep k H := FDRep.of (Representation.pullback W0.ρ eH.toMonoidHom)
  have hW : Representation.IsIrreducible W.ρ := hW0.pullback _ eH.surjective
  have hchar : psi.1 = Representation.brauerCharacterOfRootEmbedding W.ρ iota := by
    change psi.1 = Representation.brauerCharacterOfRootEmbedding
      (Representation.pullback W0.ρ eH.toMonoidHom) iota
    rw [Representation.brauerCharacterOfRootEmbedding_pullback_of_lift_eq
      W0.ρ iotaN iota eH.toMonoidHom
      (funext fun z => (iota.alongMulEquiv_lift eH z).symm)]
    apply PrimeRegularClassFunction.ext
    intro x
    have hx := congrArg (fun chi : PrimeRegularClassFunction K N 2 =>
      chi (PrimeRegularElement.map eH.toMonoidHom x)) hcharacter
    change psi.1 (PrimeRegularElement.map eH.symm.toMonoidHom
        (PrimeRegularElement.map eH.toMonoidHom x)) =
      (Representation.brauerCharacterOfRootEmbedding W0.ρ iotaN)
        (PrimeRegularElement.map eH.toMonoidHom x) at hx
    have hmap : PrimeRegularElement.map eH.symm.toMonoidHom
        (PrimeRegularElement.map eH.toMonoidHom x) = x := by
      apply Subtype.ext
      exact eH.symm_apply_apply x.1
    rw [hmap] at hx
    exact hx
  refine ⟨W, hW, hchar, extension.representation,
    extension.representation_isIrreducible hW0, ?_⟩
  exact ⟨extension.restrictionEquiv.pullback eH.toMonoidHom⟩

end HonestExtension

end ModularRep.PaperProofs.TypeBLeviRepresentativeField


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
