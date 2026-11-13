module

public import BlockBand.Endpoints.Response.LifetimeBridgeKernel
public import BlockBand.Endpoints.Response.LifetimeBridgeSpherePosNonneg
public import BlockBand.Endpoints.Response.LifetimeBridgeSpherePosAnalytic

/-!
# Strict positivity of the spherical heat kernel

`lbkSphereKernelPos_holds : 0 < D0 → LbkSphereKernelPos D0`, i.e.
`0 < Σ_n (2n+1) e^{-(D₀/2)n(n+1)t} P̃_n(y) P̃_n(y')` for all `t > 0`, `y, y' ∈ [0,1]`
(poles and antipodes included).

The proof needs no maximum principle:
1. Nonnegativity (`lbkp_series_nonneg`): the Legendre operator is a Metzler (nonnegative
   off-diagonal) matrix in each Bernstein basis, so its semigroup, the Euler limit of `(1 + sL)ⁱ`,
   preserves the Bernstein cone; testing the kernel against Bernstein approximations of
   `max(-k_t(y,·), 0)` gives `k_t ≥ 0`.
2. Strict positivity: by Chapman–Kolmogorov and symmetry,
   `k_t(y,y') = ∫₀¹ k_{t/2}(y,w) k_{t/2}(y',w) dw` with a continuous nonnegative integrand. If it
   vanished, the integrand would vanish on `[0,1]`; `k_{t/2}(y,·)` has integral `1`, so it is
   nonzero on a subinterval, where `k_{t/2}(y',·)` must vanish; by unique continuation
   (`lbkp_series_unique_continuation`, holomorphy of the series) `k_{t/2}(y',·) ≡ 0` on `[0,1]`,
   contradicting `∫₀¹ k_{t/2}(y',w) dw = 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Polynomial

/-- Strict positivity of the spherical heat kernel on `[0,1]²` (`LbkSphereKernelPos`). -/
theorem lbkSphereKernelPos_holds (D0 : ℝ) (hD0 : 0 < D0) : LbkSphereKernelPos D0 := by
  intro t ht y hy y' hy'
  have ht2 : 0 < t / 2 := by positivity
  have hCK := lbkp_chapman hD0 ht2 ht2 hy hy'
  rw [add_halves] at hCK
  rw [hCK]
  set f := lbkSphereSeries D0 (t / 2) y with hfdef
  set g := lbkSphereSeries D0 (t / 2) y' with hgdef
  have hfc : ContinuousOn f (Icc 0 1) := lbk_sphereSeries_continuousOn hD0 ht2 hy
  have hgc : ContinuousOn g (Icc 0 1) := lbk_sphereSeries_continuousOn hD0 ht2 hy'
  have hsym : (fun w => f w * lbkSphereSeries D0 (t / 2) w y') = fun w => f w * g w := by
    funext w; rw [lbkp_series_symm D0 (t / 2) w y']
  rw [hsym]
  have hnn : ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ f w * g w := fun w hw =>
    mul_nonneg (lbkp_series_nonneg hD0 ht2 hy hw) (lbkp_series_nonneg hD0 ht2 hy' hw)
  have hI0 : 0 ≤ ∫ w in (0 : ℝ)..1, f w * g w :=
    intervalIntegral.integral_nonneg zero_le_one hnn
  by_contra hle
  have h0 : ∫ w in (0 : ℝ)..1, f w * g w = 0 := le_antisymm (not_lt.1 hle) hI0
  have hfg := lbkp_eq_zero_of_integral_eq_zero (hfc.mul hgc) hnn h0
  have hf1 := lbkp_integral_series_one hD0 ht2 hy
  have hg1 := lbkp_integral_series_one hD0 ht2 hy'
  have hzero_int : ∀ h : ℝ → ℝ, (∀ w ∈ Icc (0 : ℝ) 1, h w = 0) →
      ∫ w in (0 : ℝ)..1, h w = 0 := by
    intro h hh
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun w hw => by
      rw [uIcc_of_le zero_le_one] at hw; exact hh w hw]
    simp
  obtain ⟨w0, hw0, hfw0⟩ : ∃ w0 ∈ Icc (0 : ℝ) 1, f w0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hzero_int f hcon
    rw [hfdef] at this
    linarith
  obtain ⟨c, d, hc0, hcd, hd1, hcdf⟩ :=
    lbkp_exists_Icc_sub hfc hw0 isOpen_compl_singleton (mem_compl_singleton_iff.2 hfw0)
  have hgz : ∀ w ∈ Icc c d, g w = 0 := fun w hw =>
    (mul_eq_zero.1 (hfg w ⟨hc0.trans hw.1, hw.2.trans hd1⟩)).resolve_left
      (mem_compl_singleton_iff.1 (hcdf w hw))
  have hg0 := lbkp_series_unique_continuation hD0 ht2 hy' hc0 hcd hd1 hgz
  have := hzero_int g hg0
  rw [hgdef] at this
  linarith

end BlockBand.Endpoints
