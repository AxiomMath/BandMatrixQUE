module

public import BlockBand.SourceProcess.PhysApprox.ClosingKAlg
public import BlockBand.SourceProcess.PhysApprox.ClosingAnalytic
public import BlockBand.SourceProcess.PhysApprox.ClosingGram

/-!
# Fractional moments of the closing error of `𝒦`

This file proves `TargetT2`.

Measure `μ_W = probedPathLaw W np b ⊗ phaseLaw`, `0 < p < 1`. For a probed path with
Hermitian blocks and `N^n → 0` (almost surely, all large `W`):
* each `F_c(z) = (e_i + ce_k)*(𝒦_cl(z) - 𝒦)(e_i + ce_k)`, `c ∈ {±1, ±i}`, is analytic on a ball
  of radius `R > 1` with `F_c(0) = 0` (`kForm_eq`, `exists_radius_scalar`);
* Kolmogorov (`hK`, under `phaseLaw`) gives `E_z|F_c|^p ≤ C (E_z|Im F_c|)^p`, and
  `|Im F_c| ≤ η G` with `G = 2(a_i + a_k)(d_i + d_k) + (d_i + d_k)²` (`abs_im_kForm_le`);
* polarization `4Δ_ik = F_1 - iF_i - F_{-1} + iF_{-i}` and `(Σ a)^p ≤ Σ a^p`.
So `E_z|Δ_ik|^p ≤ 4C(η E_z G)^p`; Jensen in the path (`lintegral_rpow_le_rpow_lintegral`) gives
`E|Δ_ik|^p ≤ 4C(η E G)^p`, and `E G` is small by AM–GM, the raw moments (`E a_j²`) and the input
leakage `TagChannelLeakage` (`E d_j² ≤ 2 m_j E Tr(A_- Y_j)/W`), exactly as for
`GramClosingSmall`.

* `kClosingFractional_of_raw : KolmogorovConjugate → RawTagMoments → TagChannelLeakage →
  KClosingFractional`;
* `t2 : TargetT2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingLeak
open BlockBand.SourceProcess.ClosingAux BlockBand.Transmission.Bridge
open scoped ENNReal

variable {W np : ℕ}

/-- The bound `G = 2(a_i + a_k)(d_i + d_k) + (d_i + d_k)²` on the joint sample. -/
def kBound (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ) (i k : Fin np)
    (y : ProbedPath W np × ℝ) : ℝ :=
  2 * (colA b E T τ m W i y + colA b E T τ m W k y) *
      (colD b E s T h τ m W i y + colD b E s T h τ m W k y) +
    (colD b E s T h τ m W i y + colD b E s T h τ m W k y) ^ 2

theorem kBound_nonneg (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ) (i k : Fin np)
    (y : ProbedPath W np × ℝ) : 0 ≤ kBound b E s T h τ m W i k y := by
  have := l2_nonneg ((probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m y.1)ᵀ i)
  have := l2_nonneg ((probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m y.1)ᵀ k)
  have := l2_nonneg ((closedFrame b E s T h τ m W (phase y.2) y.1 -
    probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m y.1)ᵀ i)
  have := l2_nonneg ((closedFrame b E s T h τ m W (phase y.2) y.1 -
    probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m y.1)ᵀ k)
  unfold kBound colA colD
  positivity

theorem measurable_kBound (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ) (i k : Fin np) :
    Measurable (kBound b E s T h τ m W i k) := by
  have hA := measurable_colA b E T τ m W i
  have hA' := measurable_colA b E T τ m W k
  have hD := measurable_colD b E s T h τ m W i
  have hD' := measurable_colD b E s T h τ m W k
  unfold kBound
  exact ((measurable_const.mul (hA.add hA')).mul (hD.add hD')).add ((hD.add hD').pow_const 2)

/-- AM–GM for `G`. -/
theorem kBound_le_amgm {l : ℝ} (hl : 0 < l) (ai ak di dk : ℝ) :
    2 * (ai + ak) * (di + dk) + (di + dk) ^ 2 ≤
      2 * l * (ai ^ 2 + ak ^ 2) + (2 / l + 2) * (di ^ 2 + dk ^ 2) := by
  have h1 := mul_le_amgm hl (ai + ak) (di + dk)
  have h2 : (ai + ak) ^ 2 ≤ 2 * (ai ^ 2 + ak ^ 2) := by nlinarith [sq_nonneg (ai - ak)]
  have h3 : (di + dk) ^ 2 ≤ 2 * (di ^ 2 + dk ^ 2) := by nlinarith [sq_nonneg (di - dk)]
  have e : 1 / (2 * l) * (di + dk) ^ 2 * 2 = 1 / l * (di + dk) ^ 2 := by field_simp
  have h4 : 1 / l * (di + dk) ^ 2 ≤ 1 / l * (2 * (di ^ 2 + dk ^ 2)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have e2 : 2 / l + 2 = 2 * (1 / l) + 2 := by ring
  rw [e2]
  nlinarith

/-- `(a + b + c + d)^p ≤ a^p + b^p + c^p + d^p` for `0 ≤ p ≤ 1`. -/
theorem rpow_add4_le {a b c d : ℝ≥0∞} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (a + b + c + d) ^ p ≤ a ^ p + b ^ p + c ^ p + d ^ p := by
  refine (ENNReal.rpow_add_le_add_rpow _ _ hp0 hp1).trans (add_le_add ?_ le_rfl)
  refine (ENNReal.rpow_add_le_add_rpow _ _ hp0 hp1).trans (add_le_add ?_ le_rfl)
  exact ENNReal.rpow_add_le_add_rpow _ _ hp0 hp1

/-- **The per-path Kolmogorov bound**: `E_z |Δ_ik|^p ≤ 4C (∫ ηG)^p`. -/
theorem lintegral_phase_kDiff_le {b E s T h : ℝ} (hη : 0 ≤ etaZ b E) (hh : h ^ 2 < 1)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {C : ℝ}
    (hC : ∀ (f : ℂ → ℂ) (R : ℝ), 1 < R → DifferentiableOn ℂ f (Metric.ball 0 R) → f 0 = 0 →
      ∫⁻ θ, ENNReal.ofReal (‖f (phase θ)‖ ^ p) ∂phaseLaw ≤
        ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal |(f (phase θ)).im| ∂phaseLaw) ^ p)
    (τ m : Fin np → ℝ) (x : ProbedPath W np) (hA : ∀ k, (x.1.1 k).IsHermitian)
    (hN : Tendsto (fun n => closingN (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1)
        (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ x.1))
        (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1)) ^ n) atTop (𝓝 0))
    (i k : Fin np) :
    ∫⁻ θ, ENNReal.ofReal (‖closedK b E s T h τ m W (phase θ) x i k -
        complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x i k‖ ^ p) ∂phaseLaw ≤
      4 * ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal (etaZ b E * kBound b E s T h τ m W i k (x, θ))
        ∂phaseLaw) ^ p := by
  -- one test value
  have hone : ∀ c : ℂ, ‖c‖ = 1 →
      (Continuous fun θ => kForm b E s T h τ m W x (testVec i k c) (phase θ)) ∧
      ∫⁻ θ, ENNReal.ofReal (‖kForm b E s T h τ m W x (testVec i k c) (phase θ)‖ ^ p)
        ∂phaseLaw ≤ ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal
          (etaZ b E * kBound b E s T h τ m W i k (x, θ)) ∂phaseLaw) ^ p := by
    intro c hc
    obtain ⟨R, hR, -, hd⟩ := exists_radius_scalar hN
      (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x *ᵥ testVec i k c)
      ((farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1) *
        scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 *
        probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x) *ᵥ testVec i k c)
    have hF : DifferentiableOn ℂ (kForm b E s T h τ m W x (testVec i k c))
        (Metric.ball 0 R) := by
      have hlin : DifferentiableOn ℂ (fun z : ℂ => -(((2 * etaZ b E : ℝ) : ℂ) * Complex.I * z))
          (Metric.ball 0 R) := by fun_prop
      refine (hlin.mul hd).congr fun z _ => ?_
      rw [kForm_eq]
      rfl
    have hF0 : kForm b E s T h τ m W x (testVec i k c) 0 = 0 := by
      rw [kForm_eq]
      simp
    have hcont : Continuous fun θ => kForm b E s T h τ m W x (testVec i k c) (phase θ) :=
      hF.continuousOn.comp_continuous continuous_phase fun θ => by
        rw [Metric.mem_ball, dist_zero_right, norm_phase]
        exact hR
    refine ⟨hcont, (hC _ R hR hF hF0).trans (mul_le_mul_right (ENNReal.rpow_le_rpow
      (lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ?_) hp0.le) _)⟩
    have hH : ClosingHyp b E h ⌊(W : ℝ) * s⌋₊ ⌊(W : ℝ) * T⌋₊ x.1 (phase θ) :=
      ⟨scattering_mul_conjTranspose b E _ x.1 hA, conjTranspose_mul_scattering b E _ x.1 hA, hh,
        isUnit_det_of_tendsto hN (norm_phase _), phase_mul_star _⟩
    exact abs_im_kForm_le b E s T h τ m x (phase θ) hH i k hc hη
  have hnI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hn1 : ‖(1 : ℂ)‖ = 1 := norm_one
  have hnm1 : ‖(-1 : ℂ)‖ = 1 := by rw [norm_neg, norm_one]
  have hnmI : ‖-Complex.I‖ = 1 := by rw [norm_neg, Complex.norm_I]
  obtain ⟨c1, i1⟩ := hone 1 hn1
  obtain ⟨c2, i2⟩ := hone Complex.I hnI
  obtain ⟨c3, i3⟩ := hone (-1) hnm1
  obtain ⟨c4, i4⟩ := hone (-Complex.I) hnmI
  set F := fun c θ => kForm b E s T h τ m W x (testVec i k c) (phase θ) with hFdef
  -- polarization, pointwise in `θ`
  have hpol : ∀ θ, ENNReal.ofReal (‖closedK b E s T h τ m W (phase θ) x i k -
      complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x i k‖ ^ p) ≤
      ENNReal.ofReal (‖F 1 θ‖ ^ p) + ENNReal.ofReal (‖F Complex.I θ‖ ^ p) +
        ENNReal.ofReal (‖F (-1) θ‖ ^ p) + ENNReal.ofReal (‖F (-Complex.I) θ‖ ^ p) := by
    intro θ
    have h4 := polarization (closedK b E s T h τ m W (phase θ) x -
      complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x) i k
    have hle : ‖closedK b E s T h τ m W (phase θ) x i k -
        complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x i k‖ ≤
        ‖F 1 θ‖ + ‖F Complex.I θ‖ + ‖F (-1) θ‖ + ‖F (-Complex.I) θ‖ := by
      have e : 4 * ‖closedK b E s T h τ m W (phase θ) x i k -
          complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x i k‖ =
          ‖F 1 θ - Complex.I * F Complex.I θ - F (-1) θ + Complex.I * F (-Complex.I) θ‖ := by
        have h4' : 4 * (closedK b E s T h τ m W (phase θ) x -
            complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x) i k =
            F 1 θ - Complex.I * F Complex.I θ - F (-1) θ + Complex.I * F (-Complex.I) θ := h4
        rw [← h4', norm_mul, Matrix.sub_apply]
        norm_num
      have h5 : ‖F 1 θ - Complex.I * F Complex.I θ - F (-1) θ + Complex.I * F (-Complex.I) θ‖ ≤
          ‖F 1 θ‖ + ‖F Complex.I θ‖ + ‖F (-1) θ‖ + ‖F (-Complex.I) θ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, hnI, one_mul]
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add le_rfl ?_)) le_rfl)) le_rfl
        rw [norm_mul, hnI, one_mul]
      have := norm_nonneg (closedK b E s T h τ m W (phase θ) x i k -
        complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x i k)
      linarith
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    refine (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hle) hp0.le).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (norm_nonneg _),
      ENNReal.ofReal_add (by positivity) (norm_nonneg _),
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact rpow_add4_le hp0.le hp1.le
  have hm : ∀ c : ℂ, Continuous (F c) → Measurable fun θ => ENNReal.ofReal (‖F c θ‖ ^ p) :=
    fun c hc => (ENNReal.continuous_ofReal.comp
      (hc.norm.rpow_const fun _ => Or.inr hp0.le)).measurable
  refine (lintegral_mono hpol).trans ?_
  have m12 : Measurable fun θ => ENNReal.ofReal (‖F 1 θ‖ ^ p) +
      ENNReal.ofReal (‖F Complex.I θ‖ ^ p) := (hm 1 c1).add (hm _ c2)
  have m123 : Measurable fun θ => ENNReal.ofReal (‖F 1 θ‖ ^ p) +
      ENNReal.ofReal (‖F Complex.I θ‖ ^ p) + ENNReal.ofReal (‖F (-1) θ‖ ^ p) :=
    m12.add (hm _ c3)
  rw [lintegral_add_left m123, lintegral_add_left m12, lintegral_add_left (hm 1 c1)]
  calc _ ≤ ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal
          (etaZ b E * kBound b E s T h τ m W i k (x, θ)) ∂phaseLaw) ^ p +
        ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal
          (etaZ b E * kBound b E s T h τ m W i k (x, θ)) ∂phaseLaw) ^ p +
        ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal
          (etaZ b E * kBound b E s T h τ m W i k (x, θ)) ∂phaseLaw) ^ p +
        ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal
          (etaZ b E * kBound b E s T h τ m W i k (x, θ)) ∂phaseLaw) ^ p :=
      add_le_add (add_le_add (add_le_add i1 i2) i3) i4
    _ = _ := by ring

/-- **`KClosingFractional` from Kolmogorov, the raw tag moments and `TagChannelLeakage`.** -/
theorem kClosingFractional_of_raw (hK : KolmogorovConjugate) (hR : RawTagMoments)
    (hL : TagChannelLeakage) : KClosingFractional := by
  intro b E np τ m T hD s hs hτ p hp0 hp1 i k ε hε
  obtain ⟨C, hC0, hC⟩ := lintegral_phase_kolmogorov hK hp0 hp1
  obtain ⟨B, hB0, W₀, hA⟩ := lintegral_colA_le hR hD
  obtain ⟨hb0, hb1, hE1, hE2, -, -, hm, hτT⟩ := hD
  have hη : 0 < etaZ b E := Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  have hsT : s < T := (hτ i).trans (hτT i)
  -- the target size of `E[ηG]`
  set t0 : ℝ := (ε / (4 * (C + 1))) ^ (1 / p) with ht0
  have ht0pos : 0 < t0 := Real.rpow_pos_of_pos (by positivity) _
  set t : ℝ := t0 / etaZ b E with ht
  have htpos : 0 < t := by positivity
  set l : ℝ := t / (8 * (B + 1)) with hl
  have hl0 : 0 < l := by positivity
  set c : ℝ := 2 / l + 2 with hc
  have hc0 : 0 < c := by positivity
  set M : ℝ := m i + m k + 1 with hMdef
  have hM0 : 0 < M := by linarith [hm i, hm k]
  set δ : ℝ := t / (2 * c * (4 * M)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hlt : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < 1 := nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  filter_upwards [hL b hb0 hb1 E hE1 hE2 s (τ i) T hs (hτ i) (hτT i) δ hδ0,
    hL b hb0 hb1 E hE1 hE2 s (τ k) T hs (hτ k) (hτT k) δ hδ0, hlt, self_mem_nhdsWithin]
    with h hLi hLk hh1 hh0
  have hh0' : (0 : ℝ) < h := hh0
  have hh2 : h ^ 2 < 1 := by nlinarith
  filter_upwards [hLi, hLk, eventually_ge_atTop W₀,
    closedReflection_holds b hb0 hb1 E hE1 hE2 s T h hs hsT hh0' hh1,
    lintegral_colD_le (np := np) hb0 hb1 hE1 hE2 hs hsT hh0' hh1 τ m hm]
    with W hWi hWk hW0 hWN hWD
  set μ := (probedPathLaw W np b).prod phaseLaw
  have hG := measurable_kBound b E s T h τ m W i k
  have hH : Measurable fun y => ENNReal.ofReal (etaZ b E * kBound b E s T h τ m W i k y) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hG)
  have hae := ae_probed_of_ae (np := np) ((ae_growth_isHermitian W b).and hWN)
  -- `E[ηG]` is small
  have hEG : ∫⁻ y, ENNReal.ofReal (etaZ b E * kBound b E s T h τ m W i k y) ∂μ ≤
      ENNReal.ofReal t0 := by
    have hAi : Measurable fun y => ENNReal.ofReal (colA b E T τ m W i y ^ 2) :=
      ENNReal.measurable_ofReal.comp ((measurable_colA b E T τ m W i).pow_const 2)
    have hAk : Measurable fun y => ENNReal.ofReal (colA b E T τ m W k y ^ 2) :=
      ENNReal.measurable_ofReal.comp ((measurable_colA b E T τ m W k).pow_const 2)
    have hDi : Measurable fun y => ENNReal.ofReal (colD b E s T h τ m W i y ^ 2) :=
      ENNReal.measurable_ofReal.comp ((measurable_colD b E s T h τ m W i).pow_const 2)
    have hDk : Measurable fun y => ENNReal.ofReal (colD b E s T h τ m W k y ^ 2) :=
      ENNReal.measurable_ofReal.comp ((measurable_colD b E s T h τ m W k).pow_const 2)
    have hpt : ∀ y, ENNReal.ofReal (etaZ b E * kBound b E s T h τ m W i k y) ≤
        ENNReal.ofReal (etaZ b E) * (ENNReal.ofReal (2 * l) *
          (ENNReal.ofReal (colA b E T τ m W i y ^ 2) +
            ENNReal.ofReal (colA b E T τ m W k y ^ 2)) +
          ENNReal.ofReal c * (ENNReal.ofReal (colD b E s T h τ m W i y ^ 2) +
            ENNReal.ofReal (colD b E s T h τ m W k y ^ 2))) := by
      intro y
      rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc0.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hη.le]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hη.le)
      exact kBound_le_amgm hl0 _ _ _ _
    have hA2 : Measurable fun y => ENNReal.ofReal (colA b E T τ m W i y ^ 2) +
        ENNReal.ofReal (colA b E T τ m W k y ^ 2) := hAi.add hAk
    have hD2 : Measurable fun y => ENNReal.ofReal (colD b E s T h τ m W i y ^ 2) +
        ENNReal.ofReal (colD b E s T h τ m W k y ^ 2) := hDi.add hDk
    have hAll : Measurable fun y => ENNReal.ofReal (2 * l) *
        (ENNReal.ofReal (colA b E T τ m W i y ^ 2) +
          ENNReal.ofReal (colA b E T τ m W k y ^ 2)) := hA2.const_mul _
    have hSum : Measurable fun y => ENNReal.ofReal (2 * l) *
        (ENNReal.ofReal (colA b E T τ m W i y ^ 2) +
          ENNReal.ofReal (colA b E T τ m W k y ^ 2)) +
        ENNReal.ofReal c * (ENNReal.ofReal (colD b E s T h τ m W i y ^ 2) +
          ENNReal.ofReal (colD b E s T h τ m W k y ^ 2)) := hAll.add (hD2.const_mul _)
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul _ hSum, lintegral_add_left hAll, lintegral_const_mul _ hA2,
      lintegral_const_mul _ hD2, lintegral_add_left hAi, lintegral_add_left hDi]
    have hmi := hm i
    have hmk := hm k
    calc ENNReal.ofReal (etaZ b E) * (ENNReal.ofReal (2 * l) *
          (∫⁻ y, ENNReal.ofReal (colA b E T τ m W i y ^ 2) ∂μ +
            ∫⁻ y, ENNReal.ofReal (colA b E T τ m W k y ^ 2) ∂μ) +
          ENNReal.ofReal c * (∫⁻ y, ENNReal.ofReal (colD b E s T h τ m W i y ^ 2) ∂μ +
            ∫⁻ y, ENNReal.ofReal (colD b E s T h τ m W k y ^ 2) ∂μ))
        ≤ ENNReal.ofReal (etaZ b E) * (ENNReal.ofReal (2 * l) *
            (ENNReal.ofReal B + ENNReal.ofReal B) +
          ENNReal.ofReal c * (ENNReal.ofReal (2 * m i) * ENNReal.ofReal δ +
            ENNReal.ofReal (2 * m k) * ENNReal.ofReal δ)) := by
          refine mul_le_mul_right (add_le_add (mul_le_mul_right
            (add_le_add (hA W hW0 i) (hA W hW0 k)) _) (mul_le_mul_right (add_le_add ?_ ?_) _)) _
          · exact (hWD i).trans (mul_le_mul_right hWi _)
          · exact (hWD k).trans (mul_le_mul_right hWk _)
      _ = ENNReal.ofReal (etaZ b E * (2 * l * (B + B) + c * (2 * m i * δ + 2 * m k * δ))) := by
          rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * m i by linarith),
            ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * m k by linarith),
            ← ENNReal.ofReal_add hB0 hB0, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hc0.le,
            ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hη.le]
      _ ≤ ENNReal.ofReal t0 := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : 2 * l * (B + B) ≤ t / 2 := by
            rw [hl, show 2 * (t / (8 * (B + 1))) * (B + B) = t / 2 * (B / (B + 1)) by
              field_simp; ring]
            exact mul_le_of_le_one_right (by positivity)
              ((div_le_one (by positivity)).2 (by linarith))
          have h2 : c * δ * (4 * M) = t / 2 := by
            rw [hδ]
            field_simp
          have h3 : c * (2 * m i * δ + 2 * m k * δ) ≤ c * δ * (4 * M) := by
            have : 2 * m i * δ + 2 * m k * δ ≤ δ * (4 * M) := by
              rw [hMdef]
              nlinarith
            nlinarith
          have h4 : etaZ b E * t = t0 := by
            rw [ht]
            field_simp
          nlinarith
  -- assemble
  calc ∫⁻ y, ENNReal.ofReal (‖closedK b E s T h τ m W (phase y.2) y.1 i k -
        complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m y.1 i k‖ ^ p) ∂μ
      ≤ ∫⁻ x, ∫⁻ θ, ENNReal.ofReal (‖closedK b E s T h τ m W (phase θ) x i k -
          complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x i k‖ ^ p) ∂phaseLaw
          ∂probedPathLaw W np b := lintegral_prod_le _
    _ ≤ ∫⁻ x, 4 * ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal
          (etaZ b E * kBound b E s T h τ m W i k (x, θ)) ∂phaseLaw) ^ p
          ∂probedPathLaw W np b :=
        lintegral_mono_ae (hae.mono fun x hx =>
          lintegral_phase_kDiff_le hη.le hh2 hp0 hp1 hC τ m x hx.1 hx.2 i k)
    _ = 4 * ENNReal.ofReal C * ∫⁻ x, (∫⁻ θ, ENNReal.ofReal
          (etaZ b E * kBound b E s T h τ m W i k (x, θ)) ∂phaseLaw) ^ p
          ∂probedPathLaw W np b :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    _ ≤ 4 * ENNReal.ofReal C * (∫⁻ x, ∫⁻ θ, ENNReal.ofReal
          (etaZ b E * kBound b E s T h τ m W i k (x, θ)) ∂phaseLaw ∂probedPathLaw W np b) ^ p :=
        mul_le_mul_right (lintegral_rpow_le_rpow_lintegral
          (hH.lintegral_prod_right' (ν := phaseLaw)).aemeasurable hp0 hp1) _
    _ = 4 * ENNReal.ofReal C * (∫⁻ y, ENNReal.ofReal
          (etaZ b E * kBound b E s T h τ m W i k y) ∂μ) ^ p := by
        rw [lintegral_prod _ hH.aemeasurable]
    _ ≤ 4 * ENNReal.ofReal C * (ENNReal.ofReal t0) ^ p :=
        mul_le_mul_right (ENNReal.rpow_le_rpow hEG hp0.le) _
    _ ≤ ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg ht0pos.le hp0.le, ht0, ← Real.rpow_mul (by positivity),
          one_div_mul_cancel hp0.ne', Real.rpow_one,
          show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show 4 * C * (ε / (4 * (C + 1))) = ε * (C / (C + 1)) by field_simp]
        exact mul_le_of_le_one_right hε.le ((div_le_one (by positivity)).2 (by linarith))

/-- **`TargetT2`.** -/
theorem t2 : TargetT2 := fun hMT hGA hSR hLp _ hK hL =>
  kClosingFractional_of_raw hK (RawTag.rawTagMoments_holds hGA hLp hSR hMT) hL

end BlockBand.SourceProcess.PhysApprox
