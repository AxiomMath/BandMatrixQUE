module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHRectangularSpectralGrid
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ConsumerAdapterHeightComparison
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TypicalSpacingRegularWindowBounds

/-!
# Canonical CEH heights lie in an explicit deterministic rectangle

The two-dimensional grid does not require a Lipschitz modulus for the typical-spacing
function.  This module supplies its two inputs from the regular-boundary data: the
unconditional lower spacing bound and the quantitative first-exit upper bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped Topology

/-- The CEH variance bound only needs positivity of the effective height; the
spectral parameter itself may lie on the real boundary. -/
theorem variance_mul_im_sq_le_one_of_effectiveHeight_pos
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (_hs : 0 < s) {z m : ℂ} (hm : IsSolution f s z m)
    (hz : 0 ≤ z.im) (hh : 0 < effectiveHeight s z m) :
    s * m.im ^ 2 ≤ 1 := by
  have hid := imaginaryPart_identity hN f s z m hm
  have havg := averageReal_normSq_le_inv_sq_effectiveHeight hN f hh
  have hmle : m.im ≤ (effectiveHeight s z m)⁻¹ := by
    calc
      m.im = effectiveHeight s z m *
          averageReal (fun i => ‖entry f s z m i‖ ^ 2) := hid
      _ ≤ effectiveHeight s z m * ((effectiveHeight s z m)⁻¹ ^ 2) := by
        gcongr
      _ = (effectiveHeight s z m)⁻¹ := by field_simp [hh.ne']
  have hseff : s * m.im ≤ effectiveHeight s z m := by
    unfold effectiveHeight
    linarith
  have hmprod : s * m.im ^ 2 ≤ m.im * effectiveHeight s z m := by
    nlinarith [hm.2]
  have hmheight : m.im * effectiveHeight s z m ≤ 1 := by
    calc
      m.im * effectiveHeight s z m =
          effectiveHeight s z m * m.im := by ring
      _ ≤ effectiveHeight s z m * (effectiveHeight s z m)⁻¹ :=
        mul_le_mul_of_nonneg_left hmle hh.le
      _ = 1 := by field_simp [hh.ne']
  exact hmprod.trans hmheight

/-- A positive real-boundary solution with imaginary part at least `c`
forces the deterministic lower endpoint of the rectangular height grid to
lie strictly below the canonical first-exit upper rate. -/
theorem canonicalHeightLower_lt_canonicalHeightRate_of_boundarySolution
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s c x ξ : ℝ} (hs : 0 < s) (hc : 0 < c)
    {m : ℂ} (hm : IsSolution f s (x : ℂ) m) (him : c ≤ m.im) :
    (N : ℝ) ^ ξ * (Real.pi * Real.sqrt s / (N : ℝ)) <
      canonicalHeightRate N ξ c := by
  have hh : 0 < effectiveHeight s (x : ℂ) m := by
    unfold effectiveHeight
    change 0 < 0 + s * m.im
    rw [zero_add]
    exact mul_pos hs (hc.trans_le him)
  have hsq := variance_mul_im_sq_le_one_of_effectiveHeight_pos
    hN f hs hm (by simp) hh
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hmle : m.im ≤ (Real.sqrt s)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hsqrt]
    have hnonneg : 0 ≤ m.im * Real.sqrt s :=
      mul_nonneg hm.2.le hsqrt.le
    apply (sq_le_sq₀ hnonneg zero_le_one).mp
    rw [mul_pow, Real.sq_sqrt hs.le, one_pow]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsq
  have hsc : Real.sqrt s < 2 / c := by
    apply (lt_div_iff₀ hc).2
    have : c * Real.sqrt s ≤ 1 := by
      calc
        c * Real.sqrt s ≤ m.im * Real.sqrt s :=
          mul_le_mul_of_nonneg_right him hsqrt.le
        _ ≤ 1 := (le_div_iff₀ hsqrt).mp
          (by simpa [one_div] using hmle)
    nlinarith
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpow : 0 < (N : ℝ) ^ ξ := Real.rpow_pos_of_pos hNr ξ
  rw [canonicalHeightRate, Real.rpow_sub hNr, Real.rpow_one]
  calc
    (N : ℝ) ^ ξ * (Real.pi * Real.sqrt s / (N : ℝ)) =
        ((N : ℝ) ^ ξ / (N : ℝ)) * Real.pi * Real.sqrt s := by ring
    _ < ((N : ℝ) ^ ξ / (N : ℝ)) * Real.pi * (2 / c) := by
      gcongr
    _ = (2 * Real.pi / c) * ((N : ℝ) ^ ξ / (N : ℝ)) := by ring

/-- On a regular boundary window, the exact canonical lifted height belongs to
an explicit deterministic interval.  This is the replacement for a Lipschitz
spacing-graph hypothesis in the rectangular-grid extraction. -/
theorem canonicalHeight_mem_Icc_of_regularWindow
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s E₀ R c K x ξ : ℝ} (hs : 0 < s) (hc : 0 < c) (hξ₀ : 0 ≤ ξ)
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ R c K)
    (hx : x ∈ Ioo (E₀ - R) (E₀ + R))
    (hlarge : 1 < (N : ℝ) *
      (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
        (c / (2 * Real.pi))) :
    (N : ℝ) ^ ξ * cehTypicalSpacing N hN (hermitianSpectrum hF) hs x ∈
      Icc
        ((N : ℝ) ^ ξ * (Real.pi * Real.sqrt s / (N : ℝ)))
        (canonicalHeightRate N ξ c) := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  obtain ⟨hboundary, _hderiv, _hderivBound, hdensity, _hnorm, hstability⟩ :=
    hdata x hx
  obtain ⟨hsol, hMb, hstabId⟩ :=
    boundary_matrix_scalar_identification hF (by omega) hs hc hboundary hdensity
  have hscalarBoundary : Tendsto
      (fun η : ℝ => upperBranch (by omega) (hermitianSpectrum hF) hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0))
      (nhds (Conventions.normalizedTrace (Mb x))) := by
    have ht := continuous_normalizedTrace.continuousAt.tendsto.comp hboundary
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : 0 < η := hη
    simp only [Function.comp_apply]
    rw [normalizedTrace_hermitianMDEBranch hF (by omega) hs
      (by simpa using hη'.ne')]
    rw [hermitianMDEMean_of_im_pos hF (by omega) hs (by simpa using hη')]
  have hstab : c ≤ ‖stabilityDenominator (hermitianSpectrum hF) s (x : ℂ)
      (Conventions.normalizedTrace (Mb x))‖ := by
    rw [← hstabId]
    exact hstability
  constructor
  · exact rpow_mul_pi_sqrt_div_natCast_le_rpow_mul_cehTypicalSpacing
      hN (hermitianSpectrum hF) hs ξ x
  · exact canonicalHeight_le_rate_of_boundaryData hN (hermitianSpectrum hF)
      hs hc hξ₀ hsol hdensity hstab hscalarBoundary hlarge

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.External.CEH

open Matrix Set
open scoped Matrix.Norms.L2Operator
open CEHNative.BlockBand

/-- The regular-boundary hypotheses feed the rectangular-grid event inclusion
directly.  No modulus of the typical-spacing graph occurs: only the explicit
lower and upper canonical-height bounds and a deterministic product mesh. -/
theorem localETHTwoResolventRandomBadEvent_subset_rectangularGrid_of_regularWindow
    {Ω : Type*} {N realMesh heightMesh : ℕ} (hN : 4 ≤ N)
    (H : Ω → Matrix (Fin N) (Fin N) ℂ)
    (hH : ∀ ω, (H ω).IsHermitian)
    (c₁ c₂ : AdjointChoice) (A : Matrix (Fin N) (Fin N) ℂ)
    {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s E₀ R c K ξ : ℝ} (hs : 0 < s) (hc : 0 < c) (hξ₀ : 0 ≤ ξ)
    (hregular : LocalETHRegularBoundaryWindow s
      (CEH.hermitianMDEBranch hF hs) E₀ R c K)
    (hR : 0 < R) (hrm : 0 < realMesh) (hhm : 0 < heightMesh)
    (hlarge : 1 < (N : ℝ) *
      (CEH.quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
        (c / (2 * Real.pi)))
    (lam : Ω → Fin N → ℝ)
    (hlam : ∀ ω i, lam ω i ∈ Ioo (E₀ - R) (E₀ + R))
    (threshold : Fin N → Fin N → ℝ) (gridThreshold : ℝ)
    (hbudget : ∀ i j,
      gridThreshold +
          2 * (2 * R / realMesh +
              (CEH.canonicalHeightRate N ξ c -
                (N : ℝ) ^ ξ * (Real.pi * Real.sqrt s / (N : ℝ))) /
                  heightMesh) *
            ((N : ℝ) ^ ξ * (Real.pi * Real.sqrt s / (N : ℝ)))⁻¹ ^ 3 *
              ‖A‖ ≤ threshold i j) :
    localETHTwoResolventRandomBadEvent
        (fun ω z₁ z₂ =>
          twoResolventObservable c₁ c₂
            (cehHermitianResolvent (H ω) z₁) A
            (cehHermitianResolvent (H ω) z₂))
        (CEH.cehTypicalSpacing N hN (CEH.hermitianSpectrum hF) hs) ξ
        lam threshold ⊆
      fixedTwoResolventGridBadEvent
        (fun ω z₁ z₂ =>
          twoResolventObservable c₁ c₂
            (cehHermitianResolvent (H ω) z₁) A
            (cehHermitianResolvent (H ω) z₂))
        (localETHRectangularSpectralGridPoint E₀ R
          ((N : ℝ) ^ ξ * (Real.pi * Real.sqrt s / (N : ℝ)))
          (CEH.canonicalHeightRate N ξ c) realMesh heightMesh)
        gridThreshold := by
  have hheightRange :
      (N : ℝ) ^ ξ * (Real.pi * Real.sqrt s / (N : ℝ)) <
        CEH.canonicalHeightRate N ξ c := by
    obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
    have hx₀ : E₀ ∈ Ioo (E₀ - R) (E₀ + R) := by
      constructor <;> linarith
    obtain ⟨hboundary, _hderiv, _hderivBound, hdensity,
      _hnorm, _hstability⟩ := hdata E₀ hx₀
    obtain ⟨hsol, _hMb, _hstabId⟩ :=
      CEH.boundary_matrix_scalar_identification hF (by omega) hs hc
        hboundary hdensity
    exact CEH.canonicalHeightLower_lt_canonicalHeightRate_of_boundarySolution
      (by omega) (CEH.hermitianSpectrum hF) hs hc hsol hdensity
  apply localETHTwoResolventRandomBadEvent_subset_rectangularGrid
    (by omega) H hH c₁ c₂ A
    (CEH.cehTypicalSpacing N hN (CEH.hermitianSpectrum hF) hs)
    ξ E₀ R
    ((N : ℝ) ^ ξ * (Real.pi * Real.sqrt s / (N : ℝ)))
    (CEH.canonicalHeightRate N ξ c)
    hR hrm hhm
  · exact mul_pos (Real.rpow_pos_of_pos (by positivity) ξ)
      (div_pos (mul_pos Real.pi_pos (Real.sqrt_pos.2 hs)) (by positivity))
  · exact hheightRange
  · intro ω i
    exact ⟨(hlam ω i).1.le, (hlam ω i).2.le⟩
  · intro ω i
    exact CEH.canonicalHeight_mem_Icc_of_regularWindow hN hF hs hc hξ₀
      hregular (hlam ω i) hlarge
  · exact hbudget

end CEHNative.BlockBand.External.CEH
