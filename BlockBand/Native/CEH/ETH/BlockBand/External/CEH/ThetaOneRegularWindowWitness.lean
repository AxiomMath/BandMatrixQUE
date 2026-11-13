module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneRegularWindowClosure

/-!
# The CEH theta-one regular-window witness

This module threads the single boundary witness supplied by
`LocalETHRegularBoundaryWindow` through the canonical two-energy construction.
Under the published quantifier order `0 ≤ ξ < β ≤ 1/2`, it produces, eventually
in the dimension, the cutoff coefficient one and one explicit `s₂`
bound whose constants are chosen before the dimension quantifier.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix Filter Set
open scoped Matrix.Norms.L2Operator ComplexConjugate Topology
open CEHNative.BlockBand
open CEHNative.BlockBand.CEH

/-- **CEH theta-one packaging at a regular window.**  Fix the variance,
regular window, source exponents and source observable family, in that order.
If `0 ≤ ξ < β ≤ 1/2`, then for all sufficiently large `N` the canonical points
`x_N+iN^ξη_f(x_N)` and `y_N+iN^ξη_f(y_N)` use the theta-one cutoff and
their regularized observable has the displayed dimension-independent
`HasSTwoBound`.  The constants in that bound depend only on the fixed regular
window data and are outside the eventual dimension quantifier. -/
theorem eventually_thetaOne_regularWindowWitness
    {s E₀ r c K β ξ : ℝ} (hs : 0 < s) (hr : 0 < r) (hc : 0 < c)
    (hξ₀ : 0 ≤ ξ) (hξβ : ξ < β) (hβ : β ≤ 1 / 2)
    (F : (N : ℕ) → LocalETHMatrix N)
    (hF : ∀ N, (F N).IsHermitian)
    (hregular : ∀ N, LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch (hF N) hs) E₀ r c K)
    (x y : ℕ → ℝ)
    (hx : ∀ N, |x N - E₀| ≤ (N : ℝ) ^ (β - 1))
    (hy : ∀ N, |y N - E₀| ≤ (N : ℝ) ^ (β - 1))
    (J : (N : ℕ) → LocalETHMatrix N)
    (hJ : ∀ N, ‖J N‖ ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ hN : 4 ≤ N,
      let f := hermitianSpectrum (hF N)
      let ηx := (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs (x N)
      let ηy := (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs (y N)
      let qx := entry f s (((x N : ℝ) : ℂ) + (ηx : ℂ) * Complex.I)
        (upperBranch (by omega) f hs
          (((x N : ℝ) : ℂ) + (ηx : ℂ) * Complex.I))
      let qy := entry f s (((y N : ℝ) : ℂ) + (ηy : ℂ) * Complex.I)
        (upperBranch (by omega) f hs
          (((y N : ℝ) : ℂ) + (ηy : ℂ) * Complex.I))
      let M₁ := spectralLift (hF N) qx
      let M₂ := spectralLift (hF N) qy
      regularizationCoefficient (Real.sqrt s : ℂ) M₁ M₂ᴴ = 1 ∧
        HasSTwoBound (Real.sqrt s : ℂ) M₁ M₂
          (regularizedObservable 1 M₁ M₂ᴴ (J N))
          (Real.sqrt (thetaOneSTwoBound ‖(Real.sqrt s : ℂ)‖
            ((s * c)⁻¹ + 1) (c / 2) ((2 * s)⁻¹) (c / 2))) := by
  have hcanonical := eventually_regularBoundaryWindow_canonical_conditions
    (K := K) hs hr hc hξβ hβ
  have hfixed := eventually_thetaOne_regularWindow_fixed_constants
    (K := K) hs hc hξβ hβ
  filter_upwards [hcanonical, hfixed] with N hcanonicalN hfixedN
  intro hN
  dsimp only
  let hFN := hF N
  let f := hermitianSpectrum hFN
  let ηx := (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs (x N)
  let ηy := (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs (y N)
  let qx := entry f s (((x N : ℝ) : ℂ) + (ηx : ℂ) * Complex.I)
    (upperBranch (by omega) f hs
      (((x N : ℝ) : ℂ) + (ηx : ℂ) * Complex.I))
  let qy := entry f s (((y N : ℝ) : ℂ) + (ηy : ℂ) * Complex.I)
    (upperBranch (by omega) f hs
      (((y N : ℝ) : ℂ) + (ηy : ℂ) * Complex.I))
  obtain ⟨Mb, Mb', hdata⟩ := (hregular N).boundary
  have hxopen : x N ∈ Ioo (E₀ - r) (E₀ + r) := by
    rw [mem_Ioo]
    have hxN := hx N
    rw [abs_le] at hxN
    constructor <;> linarith
  have hyopen : y N ∈ Ioo (E₀ - r) (E₀ + r) := by
    rw [mem_Ioo]
    have hyN := hy N
    rw [abs_le] at hyN
    constructor <;> linarith
  let mx := Conventions.normalizedTrace (Mb (x N))
  let my := Conventions.normalizedTrace (Mb (y N))
  have hidx := boundary_matrix_scalar_identification hFN (by omega) hs hc
    (hdata (x N) hxopen).1 (hdata (x N) hxopen).2.2.2.1
  have hidy := boundary_matrix_scalar_identification hFN (by omega) hs hc
    (hdata (y N) hyopen).1 (hdata (y N) hyopen).2.2.2.1
  have hbx : Tendsto (fun t : ℝ => upperBranch (by omega) f hs
      (((x N : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds mx) := by
    have ht := continuous_normalizedTrace.continuousAt.tendsto.comp
      (hdata (x N) hxopen).1
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t htpos
    simp only [Function.comp_apply]
    have htpos' : 0 < t := htpos
    rw [normalizedTrace_hermitianMDEBranch hFN (by omega) hs
      (by simpa using htpos'.ne')]
    rw [hermitianMDEMean_of_im_pos hFN (by omega) hs
      (by simpa using htpos')]
  have hby : Tendsto (fun t : ℝ => upperBranch (by omega) f hs
      (((y N : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds my) := by
    have ht := continuous_normalizedTrace.continuousAt.tendsto.comp
      (hdata (y N) hyopen).1
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t htpos
    simp only [Function.comp_apply]
    have htpos' : 0 < t := htpos
    rw [normalizedTrace_hermitianMDEBranch hFN (by omega) hs
      (by simpa using htpos'.ne')]
    rw [hermitianMDEMean_of_im_pos hFN (by omega) hs
      (by simpa using htpos')]
  have hstabx : c ≤ ‖CEHNative.BlockBand.CEH.stabilityDenominator f s ((x N : ℝ) : ℂ) mx‖ := by
    rw [← hidx.2.2]
    exact (hdata (x N) hxopen).2.2.2.2.2
  have hstaby : c ≤ ‖CEHNative.BlockBand.CEH.stabilityDenominator f s ((y N : ℝ) : ℂ) my‖ := by
    rw [← hidy.2.2]
    exact (hdata (y N) hyopen).2.2.2.2.2
  have hvx (i : Fin N) : ‖qx i - entry f s ((x N : ℝ) : ℂ) mx i‖ ≤
      canonicalVerticalEntryRate N ξ s c := by
    exact canonicalEntry_close_boundary_le_rate hN f hs hc hξ₀ hidx.1
      (hdata (x N) hxopen).2.2.2.1 hstabx hbx hcanonicalN.2.1 i
  have hvy (i : Fin N) : ‖qy i - entry f s ((y N : ℝ) : ℂ) my i‖ ≤
      canonicalVerticalEntryRate N ξ s c := by
    exact canonicalEntry_close_boundary_le_rate hN f hs hc hξ₀ hidy.1
      (hdata (y N) hyopen).2.2.2.1 hstaby hby hcanonicalN.2.1 i
  have hK : 0 ≤ K :=
    (norm_nonneg (Mb' (x N))).trans (hdata (x N) hxopen).2.2.1
  have hmxy : ‖my - mx‖ ≤ K * |y N - x N| := by
    rcases le_total (x N) (y N) with hxy | hyx
    · have hseg : Icc (x N) (y N) ⊆ Ioo (E₀ - r) (E₀ + r) := by
        intro t ht
        exact ⟨hxopen.1.trans_le ht.1, ht.2.trans_lt hyopen.2⟩
      simpa [abs_of_nonneg (sub_nonneg.mpr hxy)] using
        norm_normalizedTrace_sub_le_of_regularDerivative (by omega)
          hxy hseg (fun t ht => (hdata t ht).2.1)
          (fun t ht => (hdata t ht).2.2.1)
    · rw [norm_sub_rev, abs_sub_comm]
      have hseg : Icc (y N) (x N) ⊆ Ioo (E₀ - r) (E₀ + r) := by
        intro t ht
        exact ⟨hyopen.1.trans_le ht.1, ht.2.trans_lt hxopen.2⟩
      simpa [abs_of_nonneg (sub_nonneg.mpr hyx)] using
        norm_normalizedTrace_sub_le_of_regularDerivative (by omega)
          hyx hseg (fun t ht => (hdata t ht).2.1)
          (fun t ht => (hdata t ht).2.2.1)
  have hhoriz (i : Fin N) :
      ‖entry f s ((y N : ℝ) : ℂ) my i -
          entry f s ((x N : ℝ) : ℂ) mx i‖ ≤
        sourceHorizontalEntryRate N β s c K := by
    apply (norm_boundary_entry_sub_le_of_mean_modulus f hs hc hK
      (hdata (x N) hxopen).2.2.2.1 (hdata (y N) hyopen).2.2.2.1
      hmxy i).trans
    unfold sourceHorizontalEntryRate
    have hsep := abs_sub_le_two_mul_rpow_of_sourceWindow (hx N) (hy N)
    have hcoef : 0 ≤ 1 + s * K := by positivity
    rw [abs_sub_comm] at hsep
    gcongr
  let q₀ := entry f s ((x N : ℝ) : ℂ) mx
  have hq₀ (i : Fin N) : ‖q₀ i‖ ≤ (s * c)⁻¹ := by
    have hh : s * c ≤ effectiveHeight s ((x N : ℝ) : ℂ) mx := by
      simp only [effectiveHeight, Complex.ofReal_im, zero_add]
      exact mul_le_mul_of_nonneg_left (hdata (x N) hxopen).2.2.2.1 hs.le
    exact (norm_entry_le_inv_effectiveHeight f
      (lt_of_lt_of_le (mul_pos hs hc) hh) i).trans
      (inv_anti₀ (by positivity) hh)
  let δ := canonicalMixedEntryRate N ξ β s c K
  have hqx (i : Fin N) : ‖qx i - q₀ i‖ ≤ δ := by
    exact (hvx i).trans (le_add_of_nonneg_right (by
      unfold sourceHorizontalEntryRate
      positivity))
  have hqy (i : Fin N) : ‖qy i - q₀ i‖ ≤ δ := by
    apply (calc
      ‖qy i - q₀ i‖ =
          ‖(qy i - entry f s ((y N : ℝ) : ℂ) my i) +
            (entry f s ((y N : ℝ) : ℂ) my i - q₀ i)‖ := by
              congr 1
              ring
      _ ≤ ‖qy i - entry f s ((y N : ℝ) : ℂ) my i‖ +
          ‖entry f s ((y N : ℝ) : ℂ) my i - q₀ i‖ := norm_add_le _ _).trans
    exact add_le_add (hvy i) (hhoriz i)
  have hward := scaledPairing_boundary_eq_one (by omega) f hs hidx.1
  have hδ0 : 0 ≤ δ := by
    exact (norm_nonneg (qx ⟨0, by omega⟩ - q₀ ⟨0, by omega⟩)).trans
      (hqx ⟨0, by omega⟩)
  have hpairScalar := scaledPairing_gt_half_of_uniform_close (by omega) hs
    q₀ qx qy (by positivity) hδ0 hward hq₀ hqx hqy hcanonicalN.2.2
  have hpair : 1 / 2 < (s * NTrace
      (spectralLift hFN qx * (spectralLift hFN qy)ᴴ)).re := by
    rw [NTrace_spectralLift_mul_conjTranspose]
    simpa [scaledPairing] using hpairScalar
  have havgq₀ : average q₀ = mx := by
    rw [← normalizedTrace_spectralLift hFN q₀, ← hidx.2.1]
  have hq₀im : c ≤ (average q₀).im := by
    rw [havgq₀]
    exact (hdata (x N) hxopen).2.2.2.1
  have htrace₁ : c / 2 ≤ |(NTrace (spectralLift hFN qx)).im| := by
    change c / 2 ≤ |(Conventions.normalizedTrace (spectralLift hFN qx)).im|
    rw [normalizedTrace_spectralLift hFN]
    apply le_trans (average_im_half_margin_of_uniform_close (by omega)
      qx q₀ hc.le hq₀im hqx hfixedN.1)
    exact le_abs_self _
  have htrace₂ : c / 2 ≤ |(NTrace (spectralLift hFN qy)).im| := by
    change c / 2 ≤ |(Conventions.normalizedTrace (spectralLift hFN qy)).im|
    rw [normalizedTrace_spectralLift hFN]
    apply le_trans (average_im_half_margin_of_uniform_close (by omega)
      qy q₀ hc.le hq₀im hqy hfixedN.1)
    exact le_abs_self _
  have hqxNorm (i : Fin N) : ‖qx i‖ ≤ (s * c)⁻¹ + 1 := by
    calc
      ‖qx i‖ = ‖(qx i - q₀ i) + q₀ i‖ := by congr 1; ring
      _ ≤ ‖qx i - q₀ i‖ + ‖q₀ i‖ := norm_add_le _ _
      _ ≤ δ + (s * c)⁻¹ := add_le_add (hqx i) (hq₀ i)
      _ = (s * c)⁻¹ + δ := by ring
      _ ≤ (s * c)⁻¹ + 1 := hfixedN.2.1
  have hqyNorm (i : Fin N) : ‖qy i‖ ≤ (s * c)⁻¹ + 1 := by
    calc
      ‖qy i‖ = ‖(qy i - q₀ i) + q₀ i‖ := by congr 1; ring
      _ ≤ ‖qy i - q₀ i‖ + ‖q₀ i‖ := norm_add_le _ _
      _ ≤ δ + (s * c)⁻¹ := add_le_add (hqy i) (hq₀ i)
      _ = (s * c)⁻¹ + δ := by ring
      _ ≤ (s * c)⁻¹ + 1 := hfixedN.2.1
  have hpairNorm : (2 * s)⁻¹ ≤ ‖NTrace
      (spectralLift hFN qx * (spectralLift hFN qy)ᴴ)‖ :=
    mixedPairing_norm_ge_inv_two_mul hs _ _ hpair
  have hq₀den : c ≤ ‖1 - (s : ℂ) * average (fun i => q₀ i * q₀ i)‖ := by
    rw [← normalizedTrace_spectralLift_mul hFN q₀ q₀, ← hidx.2.1]
    exact (hdata (x N) hxopen).2.2.2.2.2
  have hden : c / 2 ≤ ‖stabilityDenominator (Real.sqrt s : ℂ)
      (NTrace (spectralLift hFN qx * spectralLift hFN qy))‖ := by
    change c / 2 ≤ ‖stabilityDenominator (Real.sqrt s : ℂ)
      (Conventions.normalizedTrace (spectralLift hFN qx * spectralLift hFN qy))‖
    rw [normalizedTrace_spectralLift_mul]
    unfold stabilityDenominator
    have hsqrt : ((Real.sqrt s : ℂ) ^ 2) = (s : ℂ) := by
      norm_cast
      exact Real.sq_sqrt hs.le
    rw [hsqrt]
    exact ordinaryDenominator_half_margin (by omega) hs.le hc.le
      q₀ qx qy (by positivity) hδ0 hq₀ hqx hqy hq₀den hfixedN.2.2
  exact thetaOneCompactClosure (by omega) hFN hs qx qy (J N)
    (by positivity) (by positivity) (by positivity) (by positivity)
    hqxNorm hqyNorm htrace₁ htrace₂ (hJ N) hpair hpairNorm hden

end CEHNative.BlockBand.External.CEH
