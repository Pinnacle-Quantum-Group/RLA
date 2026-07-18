/-
  Axiom audit — the machine-checked claim → theorem map for RLA.

  Each `#print axioms` below reports the complete axiom footprint of one
  headline result. CI (.github/workflows/lean.yml) runs this file and fails
  if any reported axiom falls outside the standard trust base:

    propext, Classical.choice, Quot.sound

  This makes the results falsifiable in two concrete ways:
  * an admitted proof anywhere beneath a listed theorem surfaces in the
    reported axioms as `sorryAx` and turns CI red (a plain `lake build`
    merely warns about admitted proofs);
  * any custom `axiom` smuggled into the development is listed by name and
    rejected by the CI allowlist.

  If a theorem is renamed or deleted, this file fails to elaborate, so the
  claim map cannot silently drift out of sync with the proofs.
-/
import RLA.WeylGeometry
import RLA.TwistedBracket
import RLA.CentralExtensions
import RLA.JacobiIdentity
import RLA.RepresentationProperty
import RLA.ScaledCommutator
import RLA.DiracMobiusMixing
import RLA.ContinuousParameter

-- Twisted Jacobi identity holds under alpha-closure
#print axioms RLA.JacobiIdentity.twisted_jacobi_holds
-- Commutator representation property
#print axioms RLA.RepresentationProperty.commutator_representation
-- L3: scaled commutator antisymmetry
#print axioms RLA.ScaledCommutator.L3_antisymmetric
-- Central extensions: coboundaries meeting antisymmetry are trivial
#print axioms RLA.CentralExtensions.coboundary_antisymm_intersection_trivial
-- Twisted bracket antisymmetry
#print axioms RLA.TwistedBracket.twisted_antisymmetry
-- Weyl geometry: non-metricity vanishes iff alpha = 0
#print axioms RLA.WeylGeometry.nonmetricity_vanishes_iff
-- T7: min-entropy is invariant under the Möbius pushforward
#print axioms RLA.DiracMobiusMixing.T7_minEntropy_value_eq
-- XOR-noise mixing never decreases entropy (Gibbs inequality)
#print axioms RLA.DiracMobiusMixing.xor_noise_nondecreasing
-- TRNG entropy anchor for the Dirac–Möbius mixer
#print axioms RLA.DiracMobiusMixing.DM_TRNG_entropy_anchor
-- P8: continuous scale parameter composes additively
#print axioms RLA.ContinuousParameter.P8_scale_composition
