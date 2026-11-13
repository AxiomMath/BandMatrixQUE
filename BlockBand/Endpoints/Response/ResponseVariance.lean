module

public import BlockBand.Endpoints.Response.ResponseVarianceBound
public import BlockBand.Endpoints.Response.ResponseVarianceTrace
public import BlockBand.Endpoints.Response.ResponseVarianceGaussian
public import BlockBand.Endpoints.Response.ResponseVarianceMoment

/-!
# Physical Fourier variance bounds the signed response

For fixed `m ∈ ℤ∖{0}` let `V_{W,m} = E Σ_α w(u_α)|ν_α(e^{2πim·})|²`, `w ≥ 0`, `w ∈ C_c^∞`,
`∫w = 1`; `q_m(s) = cos(2πms/τ)` and `J_{τ,m}(x,y) = E_{x,y}[1{σ₀ ≤ τ} ∫_0^τ q_m(s)R_s ds]`.
For every fixed `x ≥ 0`, `0 ≤ y < 1` there is a finite `C_{x,y,b,E,τ}` with
`(8πρ(E))²|J_{τ,m}(x,y)|² ≤ C liminf_{W→∞} V_{W,m}`.

## Lean form (`responseVariance`)

* Fixed `0 < b < 1/2`, bulk `-2 < E < 2`, `τ > 0`, `x ≥ 0`, `0 ≤ y < 1`; then one constant
  `C ≥ 0` (depending on `b, E, τ, x, y` only), valid for every `m ∈ ℤ` (the hypothesis `m ≠ 0`
  is not needed by the proof, so the statement is given for all `m`), every
  `w : SpectralWeight` (the fixed smooth nonnegative compactly supported unit-mass weight),
  every critical sequence `n_j/W_j → τ`, `W_j → ∞` (`CriticalSequence`), and every sequence of
  exact finite realizations `R j` of the physical model.
* The liminf is taken in `[0, ∞]` (`ENNReal.ofReal` of the nonnegative `V_{W,m}`), i.e. in the
  extended reals; the left side is finite.

## Proof

The port mass fraction of the matched-lead Gaussian profile is shown to vanish directly from the
negative clock theorem (the interior clock is not small; `portFraction_uniform`), instead of
through the vanishing block atom and the common port ratios. The `ClocksCommonPort` contract is
therefore not used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
  BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

/-!
### Elementary limits
-/

theorem rv_ofReal_le_liminf {a C : ℝ} (hC : 0 ≤ C) {V : ℕ → ℝ}
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, a ≤ C * V k + δ) :
    ENNReal.ofReal a ≤ ENNReal.ofReal C * liminf (fun k => ENNReal.ofReal (V k)) atTop := by
  rw [← ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ) < δ := hδ
  have hle : ENNReal.ofReal (a - δ) ≤
      liminf (fun k => ENNReal.ofReal C * ENNReal.ofReal (V k)) atTop := by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [h δ hδ'] with k hk
    rcases le_total 0 (V k) with hV | hV
    · rw [← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [ENNReal.ofReal_of_nonpos (by nlinarith)]
      exact zero_le
  calc ENNReal.ofReal a = ENNReal.ofReal ((a - δ) + δ) := by ring_nf
    _ ≤ ENNReal.ofReal (a - δ) + ENNReal.ofReal δ := ENNReal.ofReal_add_le
    _ ≤ _ := by rw [ENNReal.ofReal_coe_nnreal]; gcongr

theorem rv_length_ratio_tendsto {τ : ℝ} (s : CriticalSequence τ) :
    Tendsto (fun k => ((s.n k - 3 : ℕ) : ℝ) / s.W k) atTop (𝓝 τ) := by
  have h3 : Tendsto (fun k => (3 : ℝ) / s.W k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp s.width_tendsto)
  have := s.ratio_tendsto.sub h3
  rw [sub_zero] at this
  refine this.congr fun k => ?_
  have hn := s.n_ge_four k
  have hW : (0 : ℝ) < s.W k := by exact_mod_cast s.W_pos k
  rw [Nat.cast_sub (by omega)]
  field_simp
  norm_num

theorem rv_gridError_tendsto (m : ℤ) {τ : ℝ} (hτ : 0 < τ) (s : CriticalSequence τ) :
    Tendsto (fun k => rvGridError m τ (s.n k) (s.W k)) atTop (𝓝 0) := by
  have hW : Tendsto (fun k => (s.W k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  have hn : Tendsto (fun k => (s.n k : ℝ)) atTop atTop := by
    refine (s.ratio_tendsto.pos_mul_atTop hτ hW).congr fun k => ?_
    have : (s.W k : ℝ) ≠ 0 := by exact_mod_cast (s.W_pos k).ne'
    field_simp
  have hinvn : Tendsto (fun k => 1 / (s.n k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have hinvW : Tendsto (fun k => 1 / (s.W k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hW
  have hlim : Tendsto (fun k => 2 * Real.pi * |(m : ℝ)| *
      (|(s.n k : ℝ) / s.W k / τ - 3 / τ * (1 / s.W k) - (1 - 3 * (1 / s.n k))| + 1 / s.n k))
      atTop (𝓝 (2 * Real.pi * |(m : ℝ)| * (|τ / τ - 3 / τ * 0 - (1 - 3 * 0)| + 0))) := by
    refine tendsto_const_nhds.mul (Tendsto.add ?_ hinvn)
    refine (((s.ratio_tendsto.div_const τ).sub (tendsto_const_nhds.mul hinvW)).sub
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinvn))).abs
  rw [div_self hτ.ne'] at hlim
  simp only [mul_zero, sub_zero, sub_self, abs_zero, add_zero] at hlim
  refine hlim.congr fun k => ?_
  have hn4 := s.n_ge_four k
  have hn0 : (0 : ℝ) < s.n k := by exact_mod_cast (show 0 < s.n k by omega)
  have hW0 : (0 : ℝ) < s.W k := by exact_mod_cast s.W_pos k
  have hr : (((s.n k - 3 : ℕ) : ℝ)) = (s.n k : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hr0 : (0 : ℝ) ≤ (s.n k : ℝ) - 3 := by
    have : (4 : ℝ) ≤ s.n k := by exact_mod_cast hn4
    linarith
  rw [rvGridError, hr]
  congr 2
  rw [← abs_of_nonneg hr0, ← abs_mul]
  congr 1
  field_simp

theorem rv_weight_support (w : SpectralWeight) : ∃ U : ℝ, ∀ u, u ∉ Icc (-U) U → w u = 0 := by
  obtain ⟨U, hU⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
    w.compactSupport.isCompact.isBounded
  refine ⟨U, fun u hu => image_eq_zero_of_notMem_tsupport fun ht => hu ?_⟩
  have := hU ht
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at this
  exact this

/-!
### The theorem
-/

/-- Fixed `0 < b < 1/2`, bulk `E`, `τ > 0`, `x ≥ 0`, `0 ≤ y < 1`: there is a finite
`C ≥ 0` such that for every `m`, the signed response `J = J_{τ,m}(x,y)` of the `p = 1`
boundary dual (`IsSignedResponse`, corner `(0,0)` with `J = 0`) exists, and for every
spectral weight `w`, critical sequence and sequence of exact realizations,
`(8πρ(E))²|J|² ≤ C · liminf_j V_{W_j,m}` in `[0, ∞]`, `V_{W,m} = rvFourierVariance`.
-/
theorem responseVariance (hMom : FullSourceMomentsContract)
    (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hLen : TransmissionLengthUniformContract) (hCount : ConditionalBlockGUECount)
    (hLead : PhysicalLeadProfileContract) (hNeg : NegativeClockContract) :
    ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 → ∀ τ : ℝ, 0 < τ →
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℤ,
        (∃ J : ℝ, IsSignedResponse (transportD0 b E) τ (rvCosineTest τ m) x y J) ∧
        ∀ J : ℝ, IsSignedResponse (transportD0 b E) τ (rvCosineTest τ m) x y J →
        ∀ (w : SpectralWeight) (s : CriticalSequence τ)
          (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
          ENNReal.ofReal ((8 * Real.pi * Parameters.semicircleDensity E) ^ 2 * |J| ^ 2) ≤
            ENNReal.ofReal C *
              liminf (fun j => ENNReal.ofReal (rvFourierVariance (R j) E w m)) atTop := by
  intro b hb hb' E hE1 hE2 τ hτ x y hx hy0 hy1
  obtain ⟨c, hc, hD⟩ := rvSignedTraceBound_holds x y hx hy0 hy1
  obtain ⟨cG, hcG, hG⟩ := rvGaussianVarianceLower_holds
  have hEabs : |E| < 2 := abs_lt.2 ⟨hE1, hE2⟩
  have hκ : 0 < (2 - |E|) / 2 := by linarith
  obtain ⟨Cm, W₀, hmom⟩ := rvClockConductanceMoment_of_contracts hUnifMom hLen hCount b hb hb'
    ((2 - |E|) / 2) (τ / 2) (2 * τ) hκ (by linarith)
  set Cm' := max Cm 0
  have hCm' : 0 ≤ Cm' := le_max_right _ _
  set C₃ := (4 * max (x + y) c * Real.sqrt (2 * cG)) ^ 2 * Cm'
  have hC₃ : 0 ≤ C₃ := by positivity
  refine ⟨3 * C₃, by positivity, fun m => ?_⟩
  obtain ⟨-, hcl2⟩ := passDerivative_of_contracts hMom hUnifLaw hUnifMom hBdry hCount
  have hfl : Tendsto (fun W : ℕ => ((⌊τ * W⌋₊ : ℕ) : ℝ) / W) atTop (𝓝 τ) :=
    (tendsto_nat_floor_mul_div_atTop hτ.le).comp tendsto_natCast_atTop_atTop
  obtain ⟨v, hv, -⟩ := hcl2 b hb hb' E hE1 hE2 τ hτ _ hfl x y hx hy0 hy1 (rvCosineTest τ m)
    (rvCosineTest_continuous τ m) ⟨1, rvCosineTest_abs_le τ m⟩
  have hhalf := rv_isSignedResponse_half (fun t => rvCosineTest_reflect τ hτ.ne' m t) hv
  refine ⟨⟨v / 2, hhalf⟩, fun J hJ w s R => ?_⟩
  have hJv : v = 2 * J := by
    have := rv_isSignedResponse_unique hhalf hJ; linarith
  obtain ⟨U, hU⟩ := rv_weight_support w
  have hρ := semicircleDensity_pos hE1 hE2
  set a := 8 * Real.pi * Parameters.semicircleDensity E * |J|
  have ha : 0 ≤ a := by positivity
  have hgoal : (8 * Real.pi * Parameters.semicircleDensity E) ^ 2 * |J| ^ 2 = a ^ 2 := by ring
  rw [hgoal]
  refine rv_ofReal_le_liminf (by positivity) fun δ hδ => ?_
  set ε := min 1 (δ / (2 * a + 9 * C₃ + 1))
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hεδ : (2 * a + 9 * C₃) * ε ≤ δ := by
    have h1 : ε ≤ δ / (2 * a + 9 * C₃ + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  -- eventual facts along the critical sequence
  have hlead := hLead b hb hb' E hE1 hE2 w w.smooth w.compactSupport (rvFourierTest m) τ hτ s R
  have hratio := rv_length_ratio_tendsto s
  have hgr := (rv_gridError_tendsto m hτ s).pow 2
  rw [zero_pow two_ne_zero] at hgr
  filter_upwards [rv_signedPass_uniform hMom hUnifLaw hUnifMom hBdry hCount hb hb' hE1 hE2 hτ s
      hx hy0 hy1 (rvCosineTest_continuous τ m) ⟨1, rvCosineTest_abs_le τ m⟩ hv U ε hε,
    portFraction_uniform hNeg hb hb' hE1 hE2 hτ s U hε,
    hlead.eventually (Metric.ball_mem_nhds 0 hε), hgr.eventually (Iic_mem_nhds hε),
    s.width_tendsto.eventually_ge_atTop W₀,
    hratio.eventually (Ioo_mem_nhds (by linarith : τ / 2 < τ) (by linarith : τ < 2 * τ)),
    eventually_microEnergy_mem_bulk hb hb' hE1 hE2 s U] with k h1 h2 h3 h4 h5 h6 h7
  set p := s.parameters b hb hb' k
  have hWk : (0 : ℝ) < s.W k := by exact_mod_cast s.W_pos k
  obtain ⟨h6a, h6b⟩ := h6
  rw [lt_div_iff₀ hWk] at h6a
  rw [div_lt_iff₀ hWk] at h6b
  have hbulk : ∀ u ∈ Icc (-U) U, -2 < microEnergy p E u ∧ microEnergy p E u < 2 := by
    intro u hu
    obtain ⟨hl, hr⟩ := h7 u hu
    exact ⟨by linarith, by linarith⟩
  have hmom' : ∀ u ∈ Icc (-U) U,
      ∫⁻ ω, ENNReal.ofReal ((1 + Real.sqrt (rvConductance p.b (microEnergy p E u) p.W
          (p.n - 3) ω)) ^ 2 * (rvLeadClock p.b (microEnergy p E u) p.W (p.n - 3) ω).trace.re ^ 2)
        ∂growthPathLaw p.W p.b ≤ ENNReal.ofReal Cm' := fun u hu =>
    (hmom (s.W k) h5 _ (h7 u hu) (s.n k - 3) h6a.le h6b.le).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hfb := rv_finite_bound hCount p m w hE1 hE2 hτ hx hy0 hy1 hc hcG hCm' hU hD hG hJv h1 h2
    hbulk hmom' h4
  have hV : rvFourierVariance (R k) E w m = physicalOneMark (R k) E w (rvFourierTest m) :=
    rvFourierVariance_eq_physicalOneMark (R k) E w m
  have h3' : leadOneMark p E w (rvFourierTest m) ≤ rvFourierVariance (R k) E w m + ε := by
    rw [hV]
    have := (abs_lt.1 (by simpa [Real.dist_eq] using h3)).1
    linarith
  have hmul := mul_le_mul_of_nonneg_left h3' (by positivity : (0 : ℝ) ≤ 3 * C₃)
  nlinarith

end BlockBand.Endpoints
