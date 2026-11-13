module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneCompactBootstrap
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEAnalyticity

/-!
# Positive-height derivative input for the CEH theta-one bootstrap

This module differentiates the unconditional scalar MDE branch in the
upper half-plane.  The resulting exact implicit-function identity has the CEH
ordinary stability denominator, and hence yields the sharp derivative bound
when that denominator is bounded below.  All statements are fixed in
the dimension `N`; no convergence-rate or stability bound is assumed.

The fixed-`N` compact boundary bootstrap does not by itself give a common
positive-height stability neighborhood over the whole energy continuum: the
boundary hypothesis gives only pointwise convergence in energy.  Consequently
this module does not prove `UniformBoundaryToStripResidual`.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped BigOperators Topology

/-- Derivative of a single scalar resolvent entry along the upper
MDE branch. -/
theorem hasDerivAt_entry_upperBranch
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) (i : Fin N) :
    HasDerivAt (fun w => entry f s w (upperBranch hN f hs w) i)
      ((1 + (s : ℂ) * deriv (upperBranch hN f hs) z) *
        entry f s z (upperBranch hN f hs z) i ^ 2) z := by
  let mfun := upperBranch hN f hs
  let m := mfun z
  let m' := deriv mfun z
  have hmder : HasDerivAt mfun m' z :=
    (analyticAt_upperBranch hN f hs hz).differentiableAt.hasDerivAt
  have hm : IsSolution f s z m := upperBranch_isSolution hN f hs hz
  have hheight : 0 < effectiveHeight s z m := by
    unfold effectiveHeight
    nlinarith [hm.2]
  have hne : (f i : ℂ) - z - (s : ℂ) * m ≠ 0 :=
    denominator_ne_zero f hheight i
  have hd : HasDerivAt
      (fun w : ℂ => (f i : ℂ) - w - (s : ℂ) * mfun w)
      (-1 - (s : ℂ) * m') z := by
    have hd' := ((hasDerivAt_const z (f i : ℂ)).sub
      (hasDerivAt_id z)).sub (hmder.const_mul (s : ℂ))
    convert hd' using 1
    · ext w
      rfl
    · ring
  unfold entry
  convert hd.inv hne using 1
  dsimp only [m, m']
  field_simp [hne]
  ring

/-- Exact positive-height implicit derivative identity.  This is the scalar
form of differentiating the CEH MDE: the ordinary stability denominator
multiplies the derivative of the upper branch. -/
theorem upperBranch_derivative_identity
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    stabilityDenominator f s z (upperBranch hN f hs z) *
        deriv (upperBranch hN f hs) z =
      average (fun i => entry f s z (upperBranch hN f hs z) i ^ 2) := by
  let mfun := upperBranch hN f hs
  let m := mfun z
  let m' := deriv mfun z
  have hmder : HasDerivAt mfun m' z :=
    (analyticAt_upperBranch hN f hs hz).differentiableAt.hasDerivAt
  have hm : IsSolution f s z m := upperBranch_isSolution hN f hs hz
  have hheight : 0 < effectiveHeight s z m := by
    unfold effectiveHeight
    nlinarith [hm.2]
  have hne : ∀ i, (f i : ℂ) - z - (s : ℂ) * m ≠ 0 :=
    denominator_ne_zero f hheight
  have hi (i : Fin N) : HasDerivAt
      (fun w => entry f s w (mfun w) i)
      ((1 + (s : ℂ) * m') * (entry f s z m i) ^ 2) z := by
    exact hasDerivAt_entry_upperBranch hN f hs hz i
  have havg : HasDerivAt
      (fun w => average (fun i => entry f s w (mfun w) i))
      (average (fun i =>
        (1 + (s : ℂ) * m') * (entry f s z m i) ^ 2)) z := by
    have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N)))
      (fun i _ => hi i)
    simpa [average] using hsum.div_const (N : ℂ)
  have heq : mfun =ᶠ[nhds z]
      (fun w => average (fun i => entry f s w (mfun w) i)) := by
    have hevent : ∀ᶠ w in nhds z, 0 < w.im :=
      (Complex.continuous_im.tendsto z) (Ioi_mem_nhds hz)
    filter_upwards [hevent] with w hw
    exact (upperBranch_isSolution hN f hs hw).1
  have hderEq : m' = average (fun i =>
      (1 + (s : ℂ) * m') * (entry f s z m i) ^ 2) := by
    exact hmder.unique (havg.congr_of_eventuallyEq heq)
  have hfactor : average (fun i =>
      (1 + (s : ℂ) * m') * (entry f s z m i) ^ 2) =
      (1 + (s : ℂ) * m') * average (fun i => entry f s z m i ^ 2) := by
    exact average_const_mul _ _
  change (1 - (s : ℂ) * average (fun i => entry f s z m i ^ 2)) * m' =
    average (fun i => entry f s z m i ^ 2)
  have hlin := hderEq.trans hfactor
  linear_combination hlin

/-- Entrywise derivative formula for the Hermitian matrix MDE
branch.  It is the unitary spectral lift of the scalar entry derivatives, whose
common feedback factor is controlled by the ordinary stability denominator. -/
theorem deriv_hermitianMDEBranch_apply_of_im_pos
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) :
    deriv (fun w => hermitianMDEBranch hF hs w i j) z =
      spectralLift hF (fun k =>
        (1 + (s : ℂ) * deriv
          (upperBranch hN (hermitianSpectrum hF) hs) z) *
        entry (hermitianSpectrum hF) s z
          (upperBranch hN (hermitianSpectrum hF) hs z) k ^ 2) i j := by
  let u := upperBranch hN (hermitianSpectrum hF) hs
  let d : Fin N → ℂ := fun k =>
    (1 + (s : ℂ) * deriv u z) *
      entry (hermitianSpectrum hF) s z (u z) k ^ 2
  have hk (k : Fin N) : HasDerivAt
      (fun w => entry (hermitianSpectrum hF) s w (u w) k) (d k) z := by
    exact hasDerivAt_entry_upperBranch hN (hermitianSpectrum hF) hs hz k
  have hspectral : HasDerivAt (fun w =>
      spectralLift hF (fun k =>
        entry (hermitianSpectrum hF) s w (u w) k) i j)
      (spectralLift hF d i j) z := by
    simp only [spectralLift_apply]
    exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N)))
      (fun k _ => ((hk k).const_mul
        ((hF.eigenvectorUnitary : LocalETHMatrix N) i k)).mul_const
          (star ((hF.eigenvectorUnitary : LocalETHMatrix N) j k)))
  have heq : (fun w => hermitianMDEBranch hF hs w i j) =ᶠ[nhds z]
      (fun w => spectralLift hF (fun k =>
        entry (hermitianSpectrum hF) s w (u w) k) i j) := by
    have hevent : ∀ᶠ w in nhds z, 0 < w.im :=
      (Complex.continuous_im.tendsto z) (Ioi_mem_nhds hz)
    filter_upwards [hevent] with w hw
    simp [hermitianMDEBranch, hN, hermitianMDEMean, hw, u]
  exact (hspectral.congr_of_eventuallyEq heq).deriv

/-- A lower bound on the ordinary stability denominator gives the exact
positive-height derivative modulus.  The numerator remains the squared
MDE-entry average; no reciprocal-height substitute is introduced. -/
theorem norm_deriv_upperBranch_le_of_stability
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s γ B : ℝ} (hs : 0 < s) (hγ : 0 < γ)
    {z : ℂ} (hz : 0 < z.im)
    (hdenom : γ ≤ ‖stabilityDenominator f s z (upperBranch hN f hs z)‖)
    (hnum : ‖average (fun i =>
      entry f s z (upperBranch hN f hs z) i ^ 2)‖ ≤ B) :
    ‖deriv (upperBranch hN f hs) z‖ ≤ B / γ := by
  have hid := upperBranch_derivative_identity hN f hs hz
  apply (le_div_iff₀ hγ).2
  calc
    ‖deriv (upperBranch hN f hs) z‖ * γ =
        γ * ‖deriv (upperBranch hN f hs) z‖ := by ring
    _ ≤ ‖stabilityDenominator f s z (upperBranch hN f hs z)‖ *
        ‖deriv (upperBranch hN f hs) z‖ :=
      mul_le_mul_of_nonneg_right hdenom (norm_nonneg _)
    _ = ‖average (fun i =>
        entry f s z (upperBranch hN f hs z) i ^ 2)‖ := by
      rw [← norm_mul, hid]
    _ ≤ B := hnum

/-- The uniform-in-dimension convergence rate at the exact canonical CEH
heights, stated as a `Prop`.  It records the limit order: first `N → ∞`, uniformly over the fixed
closed energy window, with height exactly `N^ξ η_f,N(x)`. -/
def CanonicalHeightBoundaryRateResidual
    (Mf : ∀ N : ℕ, ℂ → LocalETHMatrix N)
    (Mb : ∀ N : ℕ, ℝ → LocalETHMatrix N)
    (etaF : ∀ _N : ℕ, ℝ → ℝ) (ξ a b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ Icc a b,
      matrixEntryDistance
        (Mf N ((x : ℂ) +
          (((N : ℝ) ^ ξ * etaF N x : ℝ) : ℂ) * Complex.I))
        (Mb N x) < ε

/-- The second quantitative component needed uniformly in dimension:
positive-height stability and its derivative numerator must have constants
independent of `N`.  Together with `CanonicalHeightBoundaryRateResidual` this
is the precise asymptotic information absent from pointwise boundary
convergence. -/
def CanonicalStripDerivativeRateResidual
    (N₀ : ℕ) (ξ γ B : ℝ) : Prop :=
  0 < γ ∧ 0 ≤ B ∧
  ∀ N ≥ N₀, ∀ hN : 0 < N, ∀ F : LocalETHMatrix N, ∀ hF : F.IsHermitian,
    ∀ s : ℝ, ∀ hs : 0 < s, ∀ x η : ℝ,
      0 < η → η ≤ (N : ℝ) ^ ξ →
      γ ≤ ‖stabilityDenominator (hermitianSpectrum hF) s
        ((x : ℂ) + (η : ℂ) * Complex.I)
        (upperBranch hN (hermitianSpectrum hF) hs
          ((x : ℂ) + (η : ℂ) * Complex.I))‖ ∧
      ‖average (fun i => entry (hermitianSpectrum hF) s
        ((x : ℂ) + (η : ℂ) * Complex.I)
        (upperBranch hN (hermitianSpectrum hF) hs
          ((x : ℂ) + (η : ℂ) * Complex.I)) i ^ 2)‖ ≤ B

end CEHNative.BlockBand.CEH
