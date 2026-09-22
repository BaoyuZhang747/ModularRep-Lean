import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerBlockFibre
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceTransport

/-!
# Central quotients by a subgroup of order prime to p

For the specified surjective homomorphism with central kernel of order prime
to p, the proofs construct the subgroup lift, prove its uniqueness and the
normaliser preimage identity, and establish the correspondence of radical
subgroups. These statements include the trivial subgroup.

The transport of characters and weights uses this homomorphism, the
restricted root correspondence and the specified primitive block images. It
preserves block support, every radical fibre, inflation of the original
local ordinary characters and the compatible automorphism actions. Local
reduction, the stated block image and interval laws, and finite complete
block decompositions remain explicit assumptions. The correspondence on the
quotient is a hypothesis to be transported.

This transport concerns the trivial central character sector. Faithful
sectors and the original universal prime-to-p cover remain part of the
complete family conclusion.
-/

namespace ManuscriptIBAW.Sporadic.CentralQuotient

export ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups
  (map_pSubgroup_injective exists_pSubgroup_lift pSubgroupLift
   pSubgroupLift_isPGroup pSubgroupLift_map)
export ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
  (normalizer_comap_of_central_primeTo normalizerMap_surjective_of_central_primeTo
   radical_iff_map_of_central_primeTo fixedCentralQuotientSource)
export ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerBlockFibre
  (physicalBrauerBlockFibreEquiv)
export ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceTransport
  (correspondenceTransportOutput central_quotient_correspondence_transport_deduction)

end ManuscriptIBAW.Sporadic.CentralQuotient

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
