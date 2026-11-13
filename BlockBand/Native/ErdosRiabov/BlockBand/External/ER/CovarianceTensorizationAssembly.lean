module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ExactGaussianMoments
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ProfileAnalytic

/-!
# Exact covariance and profile-tensorization assembly for the ER Gaussian ring

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, Definition 2.1, Example 2.3, and Proposition 2.8(ii).
For every finite `Params` (`n ≥ 4`, `W ≥ 1`, `0 < b < 1/2`, `c + 2b = 1`) and
every concrete Gaussian-ring `Law`, the theorem supplies the exact Hermitian Gaussian
entry package, including centering, all finite moments, diagonal variance, the two
half-variances of a strict upper entry, zero complex second moment, and positive
squared-norm covariance.  It also identifies the site covariance entrywise as

`C_{kl} * (1 / W)`,

with scalar flatness constant `1`, site flatness constant `1 / W`, and stochasticity
constant `1`.  The same witnesses are returned under either `Even n` or `Odd n`; no
antipodal case or parity-dependent constant is introduced.

The covariance sign is positive:
`∫ ‖H_xy‖² = S_xy`; circular strict upper entries instead satisfy
`∫ H_xy² = 0`.  This is independent of the later resolvent convention, where the ER
source Green function is `(H - z)⁻¹ = -(z - H)⁻¹`.

This is deliberately the nearest **unconditional exact** assembly.  It does not claim
the still stronger seven-clause Definition 2.4/2.5 analytic admissibility package
(control-kernel convolutions and spectral-domain stability).  No such unproved
admissibility certificate is accepted as an input here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERCovarianceTensorizationAssembly

open ERProfile ERProfileAnalytic ERExactGaussianMoments

/-- Unconditional assembly of the two exact ER Gaussian-ring nodes presently proved.

The first component contains the pointwise Hermitian law and all entry moment facts,
including `E |H_xy|² = S_xy` and `E H_xy² = 0` for strict selected upper entries.
The second component is Proposition 2.8(ii)'s omitted scalar-to-block tensorization.
The next two components are the exact Definition 2.1 and Example 2.3 profile witnesses.
The final component makes the absence of any parity restriction explicit.

All constants and quantifiers are fixed by `Params`: the scalar row mass is `1`, the
within-block kernel is exactly `1 / W`, and the full site flatness bound is `1 / W`.
No limit and no asymptotic uniformity claim occurs in this finite theorem. -/
theorem exactCovarianceTensorizationAssembly (p : Params) (M : Law p) :
    ExactGaussianRingMoments p M ∧
      (∀ x y : Site p.n p.W,
        siteCovariance p x y =
          cyclicCovariance p x.1 y.1 * normalizedBlockKernel p x.2 y.2) ∧
      ERDefinition21Profile p ∧
      ERBlockBandProfile p ∧
      ((Even p.n → ERDefinition21Profile p ∧ ERBlockBandProfile p) ∧
        (Odd p.n → ERDefinition21Profile p ∧ ERBlockBandProfile p)) := by
  have hmoments : ExactGaussianRingMoments p M := exactGaussianRingMoments p M
  have hprofiles : ERDefinition21Profile p ∧ ERBlockBandProfile p :=
    tensorized_profile_prerequisites p
  refine ⟨hmoments, proposition28ii_tensorization p, hprofiles.1, hprofiles.2, ?_⟩
  exact ⟨fun _ => hprofiles, fun _ => hprofiles⟩

end ERCovarianceTensorizationAssembly
end GaussianRing
end ERNative.BlockBand
