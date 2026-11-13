module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneLocalRectangleBootstrap
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Holomorphic continuation of the finite CEH scalar MDE at the boundary

At a real boundary energy the finite scalar Dyson equation is a rational
holomorphic equation in the spectral parameter and scalar mean.  This module
proves the local complex implicit-function step from a boundary
solution with positive imaginary part and nonzero ordinary stability
Denominator.  The resulting holomorphic germ is identified with the
unconditional upper branch on the upper-half-plane side by uniqueness.

All radii supplied by the implicit-function theorem are pointwise and may
depend on `N`, the deformation, the energy, and the boundary solution.  Turning
these scalar germs into the matrix-valued witness from
`LocalETHRegularBoundaryWindow`, and extracting a finite-cover modulus in the
entry-sum gauge, remains the exact assembly step needed for
`LocalRectangleTraceClosure`; no residual proposition is assumed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped Topology

/-- At any positive-imaginary scalar solution, including one over a real
spectral parameter, the derivative of the residual in the mean coordinate is
invertible precisely from nonzero ordinary stability. -/
theorem mdeResidual_snd_isInvertible_of_stability
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    (s : ℝ) {z m : ℂ}
    (hheight : 0 < effectiveHeight s z m)
    (hstab : stabilityDenominator f s z m ≠ 0) :
    (fderiv ℂ (mdeResidual f s) (z, m) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  have hne : ∀ i, (f i : ℂ) - z - (s : ℂ) * m ≠ 0 :=
    denominator_ne_zero f hheight
  have hcdf := contDiffAt_mdeResidual f s (p := (z, m)) hne
  have hder := hasDerivAt_mdeResidual_snd hN f s z m hne
  have hdiff : DifferentiableAt ℂ (mdeResidual f s) (z, m) :=
    hcdf.differentiableAt (by simp)
  have hcomp := (hdiff.hasFDerivAt.comp m
    (hasFDerivAt_prodMk_right z m)).unique hder.hasFDerivAt
  rw [hcomp]
  rw [ContinuousLinearMap.isInvertible_iff_isHomeomorph]
  convert isHomeomorph_smul₀ (α := ℂ) hstab using 1
  funext x
  simp
  ring

/-- Local holomorphic extension through a boundary point.  Besides the germ
and the exact interpolation value, the theorem records both the MDE equation
nearby and identification with the upper branch on the upper-half-plane
side. -/
theorem exists_analytic_boundaryMDE_extension
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) {x : ℝ} {m : ℂ}
    (hm : IsSolution f s (x : ℂ) m) (hmim : 0 < m.im)
    (hstab : stabilityDenominator f s (x : ℂ) m ≠ 0) :
    ∃ ψ : ℂ → ℂ,
      AnalyticAt ℂ ψ (x : ℂ) ∧
      ψ (x : ℂ) = m ∧
      (∀ᶠ z in nhds (x : ℂ), mdeResidual f s (z, ψ z) = 0) ∧
      (ψ =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}]
        upperBranch hN f hs) := by
  have hheight : 0 < effectiveHeight s (x : ℂ) m := by
    simpa [effectiveHeight] using mul_pos hs hmim
  have hne : ∀ i, (f i : ℂ) - (x : ℂ) - (s : ℂ) * m ≠ 0 :=
    denominator_ne_zero f hheight
  let cdf : ContDiffAt ℂ ⊤ (mdeResidual f s) ((x : ℂ), m) :=
    contDiffAt_mdeResidual f s (p := ((x : ℂ), m)) hne
  let hinv : (fderiv ℂ (mdeResidual f s) ((x : ℂ), m) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible :=
    mdeResidual_snd_isInvertible_of_stability hN f s hheight hstab
  let ψ : ℂ → ℂ := cdf.implicitFunction (by simp) hinv
  have hψsmooth : ContDiffAt ℂ ⊤ ψ (x : ℂ) :=
    cdf.contDiffAt_implicitFunction (by simp) hinv
  have hψself : ψ (x : ℂ) = m :=
    cdf.implicitFunction_apply_self (by simp) hinv
  have heq0 : mdeResidual f s ((x : ℂ), m) = 0 := by
    unfold mdeResidual
    exact sub_eq_zero.mpr hm.1
  have hres : ∀ᶠ z in nhds (x : ℂ),
      mdeResidual f s (z, ψ z) = 0 := by
    filter_upwards [cdf.eventually_apply_implicitFunction (by simp) hinv] with z hz
    simpa [heq0] using hz
  have hψim : ∀ᶠ z in nhds (x : ℂ), 0 < (ψ z).im := by
    have ht : Tendsto (fun z => (ψ z).im) (nhds (x : ℂ)) (nhds m.im) := by
      change Tendsto (Complex.im ∘ ψ) (nhds (x : ℂ)) (nhds m.im)
      simpa [hψself] using
        Complex.continuous_im.continuousAt.tendsto.comp hψsmooth.continuousAt.tendsto
    exact ht (Ioi_mem_nhds hmim)
  have hid : ψ =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}]
      upperBranch hN f hs := by
    filter_upwards [hres.filter_mono nhdsWithin_le_nhds,
      hψim.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hzres hzψ hzup
    have hsol : IsSolution f s z (ψ z) := by
      refine ⟨?_, hzψ⟩
      unfold mdeResidual at hzres
      exact sub_eq_zero.mp hzres
    simp only [upperBranch, dite_eq_left hzup]
    exact eq_upperSolution hN f hs hzup hsol
  exact ⟨ψ, hψsmooth.analyticAt, hψself, hres, hid⟩

/-- Pointwise local continuity across the real boundary supplied by the
holomorphic germ.  This is the scalar ingredient from which a later finite
cover must build a fixed-`N` rectangle modulus. -/
theorem exists_continuous_boundaryMDE_extension
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) {x : ℝ} {m : ℂ}
    (hm : IsSolution f s (x : ℂ) m) (hmim : 0 < m.im)
    (hstab : stabilityDenominator f s (x : ℂ) m ≠ 0) :
    ∃ ψ : ℂ → ℂ,
      ContinuousAt ψ (x : ℂ) ∧ ψ (x : ℂ) = m ∧
      (ψ =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}]
        upperBranch hN f hs) := by
  obtain ⟨ψ, hψ, hself, _hres, hid⟩ :=
    exists_analytic_boundaryMDE_extension hN f hs hm hmim hstab
  exact ⟨ψ, hψ.continuousAt, hself, hid⟩

end CEHNative.BlockBand.CEH
