module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneBoundaryIdentification

/-!
# Compatibility of CEH boundary implicit-function germs

This module proves the key non-circular compatibility statement needed before
compact assembly: a continuous real family of scalar boundary MDE
solutions agrees locally with the complex implicit-function germ based at any
one of its nondegenerate points.  The proof uses Mathlib's local uniqueness
clause for the implicit-function theorem, not an assumed compatibility or joint
continuity statement.

The remaining finite-cover step must transport this scalar compatibility
through `spectralLift` and choose common radii on the compact inner interval.
No residual proposition is assumed, and no theta-one completion is claimed in
this module.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped Topology

/-- A continuous real curve of scalar solutions lies on the same local
complex IFT germ as its value at the base energy.  Simultaneously, that germ is
the unconditional upper branch on the upper-half-plane side. -/
theorem exists_analytic_boundaryMDE_extension_agrees_real
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) {x : ℝ} {m : ℂ}
    (hm : IsSolution f s (x : ℂ) m) (hmim : 0 < m.im)
    (hstab : stabilityDenominator f s (x : ℂ) m ≠ 0)
    (mR : ℝ → ℂ) (hmRcont : ContinuousAt mR x) (hmRx : mR x = m)
    (hmRsol : ∀ᶠ y : ℝ in nhds x, IsSolution f s (y : ℂ) (mR y)) :
    ∃ ψ : ℂ → ℂ,
      AnalyticAt ℂ ψ (x : ℂ) ∧
      ψ (x : ℂ) = m ∧
      ((fun y : ℝ => ψ (y : ℂ)) =ᶠ[nhds x] mR) ∧
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
  have hchar := cdf.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  have hpair : Tendsto (fun y : ℝ => ((y : ℂ), mR y))
      (nhds x) (nhds ((x : ℂ), m)) := by
    have hre : Tendsto (fun y : ℝ => (y : ℂ)) (nhds x) (nhds (x : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    exact hre.prodMk_nhds (by simpa [hmRx] using hmRcont.tendsto)
  have hcharR : ∀ᶠ y : ℝ in nhds x,
      mdeResidual f s ((y : ℂ), mR y) = mdeResidual f s ((x : ℂ), m) ↔
        ψ (y : ℂ) = mR y := hpair.eventually hchar
  have hagree : (fun y : ℝ => ψ (y : ℂ)) =ᶠ[nhds x] mR := by
    filter_upwards [hcharR, hmRsol] with y hy hsol
    apply hy.mp
    rw [heq0]
    unfold mdeResidual
    exact sub_eq_zero.mpr hsol.1
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
  have hu : ψ =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}]
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
  exact ⟨ψ, hψsmooth.analyticAt, hψself, hagree, hu⟩

/-- Regular-boundary values have compatible scalar IFT germs at every
point.  This discharges germ compatibility directly from the boundary contract
and boundary identification. -/
theorem regularBoundaryWindow_compatible_scalar_germs
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s E₀ r c K : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K) :
    ∃ Mb : ℝ → LocalETHMatrix N,
      ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
        ∃ ψ : ℂ → ℂ,
          AnalyticAt ℂ ψ (x : ℂ) ∧
          ψ (x : ℂ) = Conventions.normalizedTrace (Mb x) ∧
          ((fun y : ℝ => ψ (y : ℂ)) =ᶠ[nhds x]
            fun y => Conventions.normalizedTrace (Mb y)) ∧
          (ψ =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}]
            upperBranch hN (hermitianSpectrum hF) hs) := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  refine ⟨Mb, ?_⟩
  intro x hx
  have hidx := boundary_matrix_scalar_identification hF hN hs hc
    (hdata x hx).1 (hdata x hx).2.2.2.1
  let mR : ℝ → ℂ := fun y => Conventions.normalizedTrace (Mb y)
  have hmRcont : ContinuousAt mR x := by
    unfold mR Conventions.normalizedTrace Matrix.trace
    have hsum : ∀ t : Finset (Fin N),
        ContinuousAt (fun y : ℝ => ∑ i ∈ t, Mb y i i) x := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using (continuousAt_const :
          ContinuousAt (fun _ : ℝ => (0 : ℂ)) x)
      | @insert i t hit iht =>
          simp only [Finset.sum_insert hit]
          exact ((hdata x hx).2.1 i i).continuousAt.add iht
    exact continuousAt_const.mul (by simpa using hsum Finset.univ)
  have hopen : Ioo (E₀ - r) (E₀ + r) ∈ nhds x :=
    Ioo_mem_nhds hx.1 hx.2
  have hmRsol : ∀ᶠ y : ℝ in nhds x,
      IsSolution (hermitianSpectrum hF) s (y : ℂ) (mR y) := by
    filter_upwards [hopen] with y hy
    exact (boundary_matrix_scalar_identification hF hN hs hc
      (hdata y hy).1 (hdata y hy).2.2.2.1).1
  have hnorm : c ≤ ‖stabilityDenominator (hermitianSpectrum hF) s
      (x : ℂ) (mR x)‖ := by
    rw [← hidx.2.2]
    exact (hdata x hx).2.2.2.2.2
  have hstab : stabilityDenominator (hermitianSpectrum hF) s
      (x : ℂ) (mR x) ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hc hnorm)
  exact exists_analytic_boundaryMDE_extension_agrees_real hN
    (hermitianSpectrum hF) hs hidx.1 hidx.1.2 hstab mR
    hmRcont rfl hmRsol

end CEHNative.BlockBand.CEH
