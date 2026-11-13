module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneUniformQuantitativeIFT
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform scalar first-exit bootstrap for the CEH boundary branch

The first-exit argument in this module is dimension free.  A continuous upper
MDE branch starts at an identified positive-density real boundary solution.
If it first reached the boundary of a scalar ball, the quantitative IFT
bootstrap would force its displacement to be strictly smaller than the ball
radius.  The hypotheses on the radius and height are explicit scalar
inequalities involving only `s` and the regular-boundary margin `c`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped Topology

/-- The scalar upper branch completed by its real boundary value. -/
def boundaryUpperBranchPath {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    (x : ℝ) (m₀ : ℂ) (η : ℝ) : ℂ :=
  if η = 0 then m₀
  else upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I)

@[simp] theorem boundaryUpperBranchPath_zero
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) (x : ℝ) (m₀ : ℂ) :
    boundaryUpperBranchPath hN f hs x m₀ 0 = m₀ := by
  simp [boundaryUpperBranchPath]

@[simp] theorem boundaryUpperBranchPath_pos
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) (x : ℝ) (m₀ : ℂ)
    {η : ℝ} (hη : 0 < η) :
    boundaryUpperBranchPath hN f hs x m₀ η =
      upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I) := by
  simp [boundaryUpperBranchPath, hη.ne']

/-- Pointwise boundary convergence plus upper-half-plane analyticity makes the
completed scalar path continuous on every closed positive-height interval. -/
theorem continuousOn_boundaryUpperBranchPath
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) (x H : ℝ) {m₀ : ℂ}
    (hboundary : Tendsto
      (fun η : ℝ => upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds m₀)) :
    ContinuousOn (boundaryUpperBranchPath hN f hs x m₀) (Icc 0 H) := by
  intro η hηIcc
  by_cases hη0 : η = 0
  · subst η
    rw [ContinuousWithinAt]
    intro V hV
    have hV0 : V ∈ nhds m₀ := by simpa using hV
    have hb := hboundary.eventually hV0
    have hbfull : ∀ᶠ t : ℝ in nhds 0, t ∈ Ioi (0 : ℝ) →
        upperBranch hN f hs ((x : ℂ) + (t : ℂ) * Complex.I) ∈ V :=
      eventually_nhdsWithin_iff.mp hb
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [hbfull] with t ht htIcc
    by_cases ht0 : t = 0
    · simpa [boundaryUpperBranchPath, ht0] using mem_of_mem_nhds hV0
    · have htpos : 0 < t := lt_of_le_of_ne htIcc.1 (Ne.symm ht0)
      simpa [boundaryUpperBranchPath, ht0] using ht htpos
  · have hηpos : 0 < η := lt_of_le_of_ne hηIcc.1 (Ne.symm hη0)
    let Z : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * Complex.I
    have hZ : Continuous Z := by
      unfold Z
      fun_prop
    have hzim : 0 < (Z η).im := by simp [Z, hηpos]
    have hu : ContinuousAt (fun z => upperBranch hN f hs z) (Z η) :=
      (analyticAt_upperBranch hN f hs hzim).continuousAt
    have hcomp : ContinuousAt
        (fun t => upperBranch hN f hs (Z t)) η :=
      hu.comp hZ.continuousAt
    have hpos : ∀ᶠ t : ℝ in nhds η, 0 < t :=
      (Ioi_mem_nhds hηpos)
    have heq : boundaryUpperBranchPath hN f hs x m₀ =ᶠ[nhds η]
        fun t => upperBranch hN f hs (Z t) := by
      filter_upwards [hpos] with t ht
      simp [boundaryUpperBranchPath, Z, ht.ne']
    exact (hcomp.congr_of_eventuallyEq heq).continuousWithinAt

/-- Dimension-free no-escape theorem.  The four scalar inequalities are the
closed bootstrap conditions: the ball preserves positive effective height,
the cubic perturbation preserves half the stability margin, and the IFT
modulus maps the full height interval strictly inside the ball. -/
theorem upperBranch_noEscape_of_quantitativeIFT
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s c R H x : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hR : 0 < R) (_hH : 0 < H)
    (hRheight : R ≤ c / 2)
    (hsmall : s * (H + s * R) * (s * c / 2)⁻¹ ^ 3 ≤ c / 2)
    (hcontract : 8 * H / (s ^ 2 * c ^ 3) < R)
    {m₀ : ℂ} (hm₀sol : IsSolution f s (x : ℂ) m₀)
    (hm₀im : c ≤ m₀.im)
    (hm₀stab : c ≤ ‖stabilityDenominator f s (x : ℂ) m₀‖)
    (hboundary : Tendsto
      (fun η : ℝ => upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds m₀)) :
    ∀ η : ℝ, 0 < η → η ≤ H →
      ‖upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I) - m₀‖ < R := by
  let g : ℝ → ℂ := boundaryUpperBranchPath hN f hs x m₀
  let d : ℝ → ℝ := fun t => ‖g t - m₀‖
  have hgcont : ContinuousOn g (Icc 0 H) :=
    continuousOn_boundaryUpperBranchPath hN f hs x H hboundary
  have hdcont : ContinuousOn d (Icc 0 H) := by
    exact (continuous_norm.comp_continuousOn
      (hgcont.sub continuousOn_const))
  have hd0 : d 0 = 0 := by simp [d, g]
  intro η hη hηH
  have hηIcc : η ∈ Icc (0 : ℝ) H := ⟨hη.le, hηH⟩
  have hgη : g η = upperBranch hN f hs
      ((x : ℂ) + (η : ℂ) * Complex.I) := by
    exact boundaryUpperBranchPath_pos hN f hs x m₀ hη
  rw [← hgη]
  change d η < R
  by_contra hnot
  have hRle : R ≤ d η := le_of_not_gt hnot
  have hRmem : R ∈ Icc (d 0) (d η) := by
    rw [hd0]
    exact ⟨hR.le, hRle⟩
  have hdcontη : ContinuousOn d (Icc 0 η) :=
    hdcont.mono (Icc_subset_Icc_right hηH)
  obtain ⟨t, htIcc, hdt⟩ :=
    (intermediate_value_Icc hη.le hdcontη hRmem)
  have htpos : 0 < t := by
    rcases htIcc.1.eq_or_lt with ht0 | ht0
    · rw [← ht0, hd0] at hdt
      linarith
    · exact ht0
  have htH : t ≤ H := htIcc.2.trans hηH
  have hgt : g t = upperBranch hN f hs
      ((x : ℂ) + (t : ℂ) * Complex.I) :=
    boundaryUpperBranchPath_pos hN f hs x m₀ htpos
  have hnormt : ‖upperBranch hN f hs
      ((x : ℂ) + (t : ℂ) * Complex.I) - m₀‖ = R := by
    simpa [d, hgt] using hdt
  let zt : ℂ := (x : ℂ) + (t : ℂ) * Complex.I
  let mt : ℂ := upperBranch hN f hs zt
  have hzt : 0 < zt.im := by simp [zt, htpos]
  have hmtsol : IsSolution f s zt mt :=
    upperBranch_isSolution hN f hs hzt
  have himdiff : |mt.im - m₀.im| ≤ ‖mt - m₀‖ := by
    simpa using Complex.abs_im_le_norm (mt - m₀)
  have hmtim : c / 2 ≤ mt.im := by
    have hlower := (neg_le_of_abs_le himdiff)
    dsimp only [mt]
    rw [show ‖upperBranch hN f hs zt - m₀‖ = R by
      simpa [zt] using hnormt] at hlower
    linarith
  have hheightt : s * c / 2 ≤ effectiveHeight s zt mt := by
    simp only [effectiveHeight]
    have : 0 ≤ zt.im := hzt.le
    nlinarith
  have hheight₀ : s * c / 2 ≤ effectiveHeight s (x : ℂ) m₀ := by
    simp only [effectiveHeight, Complex.ofReal_im, zero_add]
    nlinarith
  have hzdist : ‖zt - (x : ℂ)‖ = t := by
    simp [zt, abs_of_pos htpos]
  have hsmallt : s * (‖zt - (x : ℂ)‖ + s * ‖mt - m₀‖) *
      (s * c / 2)⁻¹ ^ 3 ≤ c / 2 := by
    rw [hzdist, show ‖mt - m₀‖ = R by simpa [mt, zt] using hnormt]
    apply le_trans _ hsmall
    gcongr
  have hboot := boundary_quantitativeIFT_bootstrap hN f hs hc
    hmtsol hm₀sol hheightt hheight₀ hm₀stab hsmallt
  have hforce : R ≤ 8 * H / (s ^ 2 * c ^ 3) := by
    rw [← hnormt]
    exact hboot.2.trans (by
      gcongr
      rw [hzdist]
      exact htH)
  linarith

/-- An explicit dimension-free scalar ball radius. -/
def quantitativeIFTRadius (s c : ℝ) : ℝ :=
  min (c / 4) (s * c ^ 4 / 64)

/-- An explicit dimension-free height cutoff for the first-exit bootstrap. -/
def quantitativeIFTHeight (s c : ℝ) : ℝ :=
  min (s ^ 2 * c ^ 4 / 64)
    (quantitativeIFTRadius s c * s ^ 2 * c ^ 3 / 16)

/-- The explicit radius and height satisfy every scalar inequality required by
the no-escape theorem. -/
theorem quantitativeIFTRadius_height_spec {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    0 < quantitativeIFTRadius s c ∧
    0 < quantitativeIFTHeight s c ∧
    quantitativeIFTRadius s c ≤ c / 2 ∧
    s * (quantitativeIFTHeight s c +
        s * quantitativeIFTRadius s c) * (s * c / 2)⁻¹ ^ 3 ≤ c / 2 ∧
    8 * quantitativeIFTHeight s c / (s ^ 2 * c ^ 3) <
      quantitativeIFTRadius s c := by
  let R := quantitativeIFTRadius s c
  let H := quantitativeIFTHeight s c
  have hRpos : 0 < R := by
    dsimp [R, quantitativeIFTRadius]
    exact lt_min (by positivity) (by positivity)
  have hHpos : 0 < H := by
    dsimp [H, quantitativeIFTHeight]
    exact lt_min (by positivity) (by positivity)
  have hRc : R ≤ c / 4 := by
    exact min_le_left _ _
  have hRs : R ≤ s * c ^ 4 / 64 := by
    exact min_le_right _ _
  have hHc : H ≤ s ^ 2 * c ^ 4 / 64 := by
    exact min_le_left _ _
  have hHR : H ≤ R * s ^ 2 * c ^ 3 / 16 := by
    exact min_le_right _ _
  have hsum : H + s * R ≤ s ^ 2 * c ^ 4 / 32 := by
    have hsR : s * R ≤ s ^ 2 * c ^ 4 / 64 := by
      calc
        s * R ≤ s * (s * c ^ 4 / 64) :=
          mul_le_mul_of_nonneg_left hRs hs.le
        _ = s ^ 2 * c ^ 4 / 64 := by ring
    linarith
  have hscale :
      s * (H + s * R) * (s * c / 2)⁻¹ ^ 3 =
        8 * (H + s * R) / (s ^ 2 * c ^ 3) := by
    field_simp [hs.ne', hc.ne']
    ring
  have hsmall : s * (H + s * R) * (s * c / 2)⁻¹ ^ 3 ≤ c / 2 := by
    rw [hscale]
    apply (div_le_iff₀ (by positivity : 0 < s ^ 2 * c ^ 3)).2
    have := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (8 : ℝ) by norm_num)
    nlinarith [sq_pos_of_pos hs, pow_pos hc 3]
  have hcontract : 8 * H / (s ^ 2 * c ^ 3) < R := by
    have hden : 0 < s ^ 2 * c ^ 3 := by positivity
    apply (div_lt_iff₀ hden).2
    have hscaled := mul_le_mul_of_nonneg_left hHR (show 0 ≤ (8 : ℝ) by norm_num)
    have hprod : 0 < R * (s ^ 2 * c ^ 3) := mul_pos hRpos hden
    have hRden : R * (s ^ 2 * c ^ 3) / 2 <
        R * (s ^ 2 * c ^ 3) := by linarith
    nlinarith
  exact ⟨hRpos, hHpos, hRc.trans (by linarith), hsmall, hcontract⟩

/-- Fully explicit form of the uniform first-exit conclusion. -/
theorem upperBranch_close_boundary_below_quantitativeIFTHeight
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s c x : ℝ} (hs : 0 < s) (hc : 0 < c)
    {m₀ : ℂ} (hm₀sol : IsSolution f s (x : ℂ) m₀)
    (hm₀im : c ≤ m₀.im)
    (hm₀stab : c ≤ ‖stabilityDenominator f s (x : ℂ) m₀‖)
    (hboundary : Tendsto
      (fun η : ℝ => upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds m₀)) :
    ∀ η : ℝ, 0 < η → η ≤ quantitativeIFTHeight s c →
      ‖upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I) - m₀‖ <
          quantitativeIFTRadius s c := by
  obtain ⟨hR, hH, hRheight, hsmall, hcontract⟩ :=
    quantitativeIFTRadius_height_spec hs hc
  exact upperBranch_noEscape_of_quantitativeIFT hN f hs hc
    hR hH hRheight hsmall hcontract hm₀sol hm₀im hm₀stab hboundary

/-- The regular-boundary hypothesis `LocalETHRegularBoundaryWindow` supplies every
hypothesis of the explicit no-escape theorem.  The resulting scalar cutoff depends only on the
source constants `s,c`, not on `N`, the deformation, or the energy. -/
theorem regularBoundaryWindow_uniformScalarFirstExit
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s E₀ r c K a b : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K)
    (hinner : Icc a b ⊆ Ioo (E₀ - r) (E₀ + r)) :
    ∃ Mb : ℝ → LocalETHMatrix N,
      ∀ x ∈ Icc a b, ∀ η : ℝ, 0 < η →
        η ≤ quantitativeIFTHeight s c →
        ‖upperBranch hN (hermitianSpectrum hF) hs
          ((x : ℂ) + (η : ℂ) * Complex.I) -
            Conventions.normalizedTrace (Mb x)‖ <
          quantitativeIFTRadius s c := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  refine ⟨Mb, ?_⟩
  intro x hx η hη hηH
  have hxopen := hinner hx
  have hidx := boundary_matrix_scalar_identification hF hN hs hc
    (hdata x hxopen).1 (hdata x hxopen).2.2.2.1
  have hnorm : c ≤ ‖stabilityDenominator (hermitianSpectrum hF) s
      (x : ℂ) (Conventions.normalizedTrace (Mb x))‖ := by
    rw [← hidx.2.2]
    exact (hdata x hxopen).2.2.2.2.2
  have htrace : Tendsto
      (fun t : ℝ => Conventions.normalizedTrace
        (hermitianMDEBranch hF hs
          ((x : ℂ) + (t : ℂ) * Complex.I)))
      (nhdsWithin 0 (Ioi 0))
      (nhds (Conventions.normalizedTrace (Mb x))) := by
    exact continuous_normalizedTrace.continuousAt.tendsto.comp
      (hdata x hxopen).1
  have hscalar : Tendsto
      (fun t : ℝ => upperBranch hN (hermitianSpectrum hF) hs
        ((x : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0))
      (nhds (Conventions.normalizedTrace (Mb x))) := by
    apply htrace.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    rw [normalizedTrace_hermitianMDEBranch hF hN hs
      (by simpa using htpos.ne')]
    rw [hermitianMDEMean_of_im_pos hF hN hs (by simpa using htpos)]
  exact upperBranch_close_boundary_below_quantitativeIFTHeight
    hN (hermitianSpectrum hF) hs hc hidx.1
    (hdata x hxopen).2.2.2.1 hnorm hscalar η hη hηH

/-- The elementary large-dimension inequality in the exact CEH
normalization.  For `ξ<1`, the factor is a positive constant times
`N^(1-ξ)` and hence diverges. -/
theorem eventually_one_lt_ceh_test_density_scale
    {ξ H c : ℝ} (hξ : ξ < 1) (hH : 0 < H) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      1 < (N : ℝ) * (H / (N : ℝ) ^ ξ) *
        (c / (2 * Real.pi)) := by
  let A : ℝ := H * (c / (2 * Real.pi))
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - ξ)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hξ)).comp
      tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun N : ℕ => A * (N : ℝ) ^ (1 - ξ))
      atTop atTop :=
    (tendsto_const_mul_atTop_iff_pos hpow).2 hA
  have hevent := hprod.eventually_gt_atTop 1
  filter_upwards [hevent, eventually_ge_atTop 1] with N hlarge hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hid : (N : ℝ) * (H / (N : ℝ) ^ ξ) *
      (c / (2 * Real.pi)) = A * (N : ℝ) ^ (1 - ξ) := by
    rw [Real.rpow_sub hNpos, Real.rpow_one]
    dsimp [A]
    field_simp [hNpos.ne', (Real.rpow_pos_of_pos hNpos ξ).ne',
      Real.pi_ne_zero]
  rwa [hid]

/-- At every sufficiently large dimension, scalar first-exit control puts the
exact canonical CEH height below the same dimension-free cutoff. -/
theorem canonicalHeight_lt_quantitativeIFTHeight_of_boundaryData
    {N : ℕ} (hN : 4 ≤ N) (f : DeformationSpectrum N)
    {s c x ξ : ℝ} (hs : 0 < s) (hc : 0 < c) (hξ₀ : 0 ≤ ξ)
    {m₀ : ℂ} (hm₀sol : IsSolution f s (x : ℂ) m₀)
    (hm₀im : c ≤ m₀.im)
    (hm₀stab : c ≤ ‖stabilityDenominator f s (x : ℂ) m₀‖)
    (hboundary : Tendsto
      (fun η : ℝ => upperBranch (by omega) f hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds m₀))
    (hlarge : 1 < (N : ℝ) *
      (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
        (c / (2 * Real.pi))) :
    (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x <
      quantitativeIFTHeight s c := by
  have hspec := quantitativeIFTRadius_height_spec hs hc
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hpow : 1 ≤ (N : ℝ) ^ ξ := by
    exact Real.one_le_rpow (by norm_num [show (1 : ℝ) ≤ N by exact_mod_cast
      (show 1 ≤ N by omega)]) hξ₀
  have htest : 0 < quantitativeIFTHeight s c / (N : ℝ) ^ ξ :=
    div_pos hspec.2.1 (Real.rpow_pos_of_pos hNpos ξ)
  have htestle : quantitativeIFTHeight s c / (N : ℝ) ^ ξ ≤
      quantitativeIFTHeight s c := by
    exact div_le_self hspec.2.1.le hpow
  have hcloseR := upperBranch_close_boundary_below_quantitativeIFTHeight
    (by omega) f hs hc hm₀sol hm₀im hm₀stab hboundary
    _ htest htestle
  have hclose : ‖upperBranch (by omega) f hs
      ((x : ℂ) + ((quantitativeIFTHeight s c /
        (N : ℝ) ^ ξ : ℝ) : ℂ) * Complex.I) - m₀‖ < c / 2 :=
    hcloseR.trans_le hspec.2.2.1
  exact rpow_mul_cehTypicalSpacing_lt_of_boundary_close hN f hs x ξ
    (quantitativeIFTHeight s c) c hspec.2.1 hc hm₀im hclose hlarge

end CEHNative.BlockBand.CEH
