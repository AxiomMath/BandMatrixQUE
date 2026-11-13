module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.PhysicalKernelBridge
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ConcreteExpansion
public import BlockBand.Native.ErdosRiabov.BlockBand.Published.BandLocalLawInput

/-!
# Algebraic adapter from the Erdős–Riabov Gaussian ring to the short-ring interface

This module proves the normalization and convention changes between the concrete
Erdős–Riabov development and the quantities of the short-ring local law
(`shortRingGreen`, `shortRingSiteDistance`, `shortRingLength`, …),
following Erdős–Riabov, arXiv:2506.06441v1, Definition 2.1,
Proposition 2.8(ii), Theorem 3.3 and (3.17).

The results are finite algebraic identities, uniform over every `Params` (and hence
both even and odd block rings).  In particular, they do not assert the
probabilistic tail/bootstrap estimate of the local law.
The resolvent identity below records the minus sign between the resolvent
`(z I - H)⁻¹` used here and ER's `(H - z)⁻¹`; the distance identity records that the
flattened cyclic distance is ER's physical-site distance.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand.GaussianRing.ERRingAdapter

open ERProfile ERConcrete ERPhysicalBridge

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The total dimension of the interface is the ER dimension `N = nW`, with no hidden
bandwidth rescaling. -/
@[simp] theorem shortRing_dimension (p : Params) : p.L = p.n * p.W :=
  p.L_eq

/-- The concrete ER covariance is exactly the Gaussian-ring entry variance,
including the factor `W⁻¹`. -/
@[simp] theorem siteCovariance_eq_varianceProfile (p : Params)
    (x y : Site p.n p.W) :
    siteCovariance p x y = varianceProfile p x y :=
  rfl

/-- The exact row normalization required by ER is inherited from `Params`/`Law`:
the full physical-site covariance has total mass one. -/
theorem siteCovariance_row_normalization (p : Params) (x : Site p.n p.W) :
    ∑ y, siteCovariance p x y = 1 :=
  siteCovariance_stochastic p x

/-- ER's source-sign Green function is exactly `shortRingGreen`: both sides are
`-(zI-H)⁻¹`. -/
@[simp] theorem shortRingGreen_eq_green {p : Params} (M : Law p)
    (z : ℂ) (ω : M.Ω) :
    shortRingGreen (M.H ω) z = green M z ω :=
  rfl

/-- The row-major cyclic metric of the interface is ER's physical-site metric.
Thus the flattened-distance convention introduces no comparison constant. -/
@[simp] theorem shortRingSiteDistance_eq_erSiteDistance (p : Params)
    (x y : Site p.n p.W) :
    shortRingSiteDistance p x y = erSiteDistance p x y :=
  rfl

/-- The localization length of the interface has the same normalization as ER's
`min(W / sqrt η, N)`; only the arguments of `min` are printed in reverse order. -/
@[simp] theorem shortRingLength_eq_erLocalizationLength (p : Params) (η : ℝ) :
    shortRingLength p η = erLocalizationLength p η := by
  simp [shortRingLength, erLocalizationLength, min_comm]

/-- On the upper half-plane, the semicircle branch of the interface is exactly ER's
Stieltjes transform. -/
@[simp] theorem semicircleStieltjes_eq_erSemicircleStieltjes {z : ℂ}
    (hz : 0 ≤ z.im) :
    semicircleStieltjes z = erSemicircleStieltjes z := by
  rw [erSemicircleStieltjes_eq_upperFormula_of_im_nonneg hz]
  rfl

/-- Specialization of the semicircle-branch adapter to the spectral
parameter `e + η i`. -/
theorem semicircleStieltjes_energy_height (e η : ℝ) (hη : 0 < η) :
    semicircleStieltjes (e + η * Complex.I) =
      erSemicircleStieltjes (e + η * Complex.I) := by
  apply semicircleStieltjes_eq_erSemicircleStieltjes
  simp [hη.le]

/-- The entry error of the interface agrees with the concrete ER error after
expanding the ER-sign resolvent, upper-half-plane semicircle branch, and
Kronecker diagonal. -/
theorem shortRingEntryError_eq_entryError {p : Params} (M : Law p)
    (e η : ℝ) (hη : 0 < η) (x y : Site p.n p.W) (ω : M.Ω) :
    shortRingEntryError (M.H ω) e η x y =
      entryError M (e + η * Complex.I) x y ω := by
  rw [shortRingEntryError, entryError, resolventError]
  rw [shortRingGreen_eq_green]
  rw [semicircleStieltjes_energy_height e η hη]
  simp only [semicircleMatrix]
  by_cases hxy : x = y <;> simp [hxy]

end ERNative.BlockBand.GaussianRing.ERRingAdapter
