module

public import BlockBand.Endpoints.Clock.DetClockProofLayer
public import BlockBand.Endpoints.Clock.DetClockBulkWard
public import BlockBand.Endpoints.Clock.DetClockBulkCov

/-!
# The deterministic-clock lemma on `bulkInterval κ`: the one-step bound, energy-uniform

`DetClockProof.stepDefect_le` fixes `-2 < E < 2` and a stationary jet `s` before `C, W₀`. Here
`C, W₀` depend only on `(b, κ, K, K_q)`, and the bound `|stepDefect| ≤ C Λ⁹ W^{-3/2}` holds for
every `E ∈ bulkInterval κ` and every stationary jet `s` at `E` (`stepDefect_le_unif`). The
`E`-dependent inputs of the fixed-energy proof are replaced as follows (after the reduction
`κ ↦ min κ 1`):
* Ward mean: `DetClockBulk.wardMean_unif`; injection mean: `DetClockBulk.injectionMean_unif`;
* covariance identities: `DetClockBulk.covTraceSquare_unif` (from
  `PassiveCovarianceEnergyUniformHyp`);
* centered `L³` entries of `LL*`: `PassiveSourceMixingEnergyUniformContract.oneStepFluctuation`
  (`p = 3`);
* the layer moments: `GaussianAbsorptionContract` at `η₀ = η_κ`, `M = 3`;
* `‖f‖ ≤ (Im z)⁻¹ + |c₀| ≤ 2/η_κ` (`fBound_le`);
* `D₀ = 2/(b(4-E²)) ≤ 2/(bκ(4-κ))` (`transportD0_le_bulk`), in the off-domain constant.

The deterministic assembly (`stepDefect_decomp`, `stepDefect_domain`, `stepDefect_crude`) is used
at each `E`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

namespace MovingEnergy

namespace DetClockBulk

open DetClockProof ClockMixingAlg ClockMixingProb DetClockTaylor
open BlockBand.Internal.Contracts.TransmissionUniform3

variable {b κ : ℝ}

/-- `D₀^max = 2/(bκ(4-κ))`, the uniform bound of `D₀ = 2/(b(4-E²))` on `bulkInterval κ`. -/
def transportD0Max (b κ : ℝ) : ℝ := 2 / (b * (κ * (4 - κ)))

theorem transportD0Max_nonneg (hb0 : 0 < b) (hκ : 0 < κ) (hκ4 : κ < 4) :
    0 ≤ transportD0Max b κ := by
  have : 0 < 4 - κ := by linarith
  unfold transportD0Max; positivity

/-- `D₀ ≤ D₀^max` on `bulkInterval κ` (`0 < κ ≤ 2`): `4 - E² ≥ 4 - (2-κ)² = κ(4-κ)`. -/
theorem transportD0_le_bulk (hb0 : 0 < b) (hκ : 0 < κ) (hκ2 : κ ≤ 2) {E : ℝ}
    (hE : E ∈ bulkInterval κ) : transportD0 b E ≤ transportD0Max b κ := by
  obtain ⟨h1, h2⟩ := hE
  have h4 : 0 < 4 - κ := by linarith
  have hsq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hpos : 0 < b * (κ * (4 - κ)) := by positivity
  unfold transportD0 transportD0Max
  exact div_le_div_of_nonneg_left (by norm_num) hpos (mul_le_mul_of_nonneg_left hsq hb0.le)

/-- **The one-step bound, uniformly in `E ∈ bulkInterval κ₀` and in the stationary jet**
(the uniform version of `DetClockProof.stepDefect_le`). For fixed
`0 < b < 1/2`, `κ₀ > 0`, `K ≥ 1`, `K_q ≥ 0` there are `C, W₀` such that
`|stepDefect| ≤ C Λ⁹ W^{-3/2}` for `W ≥ W₀`, every `E ∈ bulkInterval κ₀`, every stationary jet
`s` at `E`, every Hermitian `X`, every `Q ⪰ 0`, `a ∈ [K⁻¹, K]`, `q ∈ [0, K_q]`. -/
theorem stepDefect_le_unif (hPSMU : PassiveSourceMixingEnergyUniformContract)
    (hPCU : PassiveCovarianceEnergyUniformHyp) (hGA : GaussianAbsorptionContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract)
    {κ₀ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ₀ : 0 < κ₀) {K Kq : ℝ} (hK : 1 ≤ K)
    (hKq : 0 ≤ Kq) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ₀, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      X.IsHermitian → ∀ Q : Matrix (Fin W) (Fin W) ℂ, Q.PosSemidef →
        ∀ a ∈ Set.Icc K⁻¹ K, ∀ qv ∈ Set.Icc 0 Kq,
          |stepDefect W b E qv a X Q| ≤
            C * pastWeight W b E s X Q ^ 9 * ((Real.sqrt W)⁻¹) ^ 3 := by
  set κ := min κ₀ 1 with hκdef
  have hκ : 0 < κ := lt_min hκ₀ one_pos
  have hκ1 : κ ≤ 1 := min_le_right _ _
  have hκ4 : κ < 4 := by linarith
  have hηL := etaLow_pos hb1 hκ hκ4
  obtain ⟨Cw, dw, Ww, hdw, hward⟩ := wardMean_unif hGA hWC hb0 hb1 hκ hκ4
  obtain ⟨Cf, Wf, hfl⟩ := hPSMU.oneStepFluctuation b hb0 hb1 κ hκ 3 (by norm_num)
  obtain ⟨Cc, Wc, hcov⟩ := covTraceSquare_unif hPCU hPSMU hb0 hb1 hκ
  obtain ⟨Ci, Wi, hinj⟩ := injectionMean_unif hGA hb0 hb1 hκ hκ4
  obtain ⟨ε₁, CA, hε₁, hCA, habs'⟩ := hGA b hb0 hb1 (etaLow b κ) 3 hηL
  set Kf := 2 / etaLow b κ with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  set D0m := transportD0Max b κ with hD0m
  have hD0m0 : 0 ≤ D0m := transportD0Max_nonneg hb0 hκ hκ4
  have hd := (dStar_pos (by linarith : b < 1)).le
  set Cdom := domConst K Kq Kf (max Cw 0) (max Cf 0) (max Cc 0) (max Ci 0) CA with hCdom
  set Coff := (2 + D0m * K ^ 2 + dStar b * Kq * K) / dw ^ 2 with hCoff
  have hK0 : 0 ≤ K := by linarith
  have hCdom0 : 0 ≤ Cdom := domConst_nonneg hK0 hKq hKf0 (le_max_right _ _) (le_max_right _ _)
    (le_max_right _ _) (le_max_right _ _)
  have hCoff0 : 0 ≤ Coff := by positivity
  refine ⟨Cdom + Coff, max (max (max Ww Wf) (max Wc Wi)) (max ⌈6 / ε₁⌉₊ 1),
    by positivity, fun W hWW E hE₀ s hs X hX Q hQ a ha qv hqv => ?_⟩
  have hE : E ∈ bulkInterval κ := bulkInterval_mono (min_le_left κ₀ 1) hE₀
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hE
  have hz : 0 < (boundaryZ b E).im := im_pos_of_bulk hb1 hκ hκ4 hE
  have hD := (transportD0_pos hb0 hE0 hE1).le
  have hDle : transportD0 b E ≤ D0m := transportD0_le_bulk hb0 hκ (by linarith) hE
  have hWw : Ww ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hWW
  have hWf : Wf ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hWW
  have hWc : Wc ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hWW
  have hWi : Wi ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hWW
  have hWε : ⌈6 / ε₁⌉₊ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hWW
  have hWpos : 0 < W := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hWW))
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
  have hW0 : (0 : ℝ) < W := by linarith
  have h6W : (6 : ℝ) ≤ ε₁ * W := by
    have h1 : 6 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWε)
    rw [div_le_iff₀ hε₁] at h1; linarith
  obtain ⟨ha0', haK⟩ := ha
  have ha0 : 0 ≤ a := le_trans (inv_nonneg.mpr hK0) ha0'
  obtain ⟨hqv0, hqvK⟩ := hqv
  set w := (Real.sqrt W)⁻¹ with hwdef
  have hsW : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW1
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ hsW
  have hw2 : w ^ 2 = (W : ℝ)⁻¹ := by rw [hwdef, inv_pow, Real.sq_sqrt hW0.le]
  -- the fresh layer
  have hXl := CavityMeanProb.cavityLift_isHermitian hX
  obtain ⟨_hinv, hmom⟩ := habs' W hWpos LayerShape.oneBlockOnePort (cavityLift X) hXl E
    (boundaryZ b E) (etaLow_le_im hb1 hκ hE) (norm_boundaryZ_le3 hb0 hb1 hκ hE)
  have hG6 : eLpNorm (fun ω => ‖freshLayer b E X ω‖) (ENNReal.ofReal (2 * 3)) (freshLaw W b) ≤
      ENNReal.ofReal CA := by
    rw [show (2 : ℝ) * 3 = 6 by norm_num]; exact hmom 6 (by norm_num) h6W
  have hG2 : Integrable (fun ω => ‖freshLayer b E X ω‖ ^ 2) (freshLaw W b) :=
    BlockBand.Layers.meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) (by linarith))
  have hsq := condSq_le (ν := freshLaw W b) (p := 3) (by norm_num) hCA.le hG6
  have hCm : Measurable (fun ω => freshC b E X ω) :=
    (meas_freshC (W := W) b E).comp (f := fun ω => (X, ω)) (measurable_const.prodMk measurable_id)
  have hβ : eLpNorm (fun ω => (freshC b E X ω).trace.re) (ENNReal.ofReal 3) (freshLaw W b) ≤
      ENNReal.ofReal ((W : ℝ) * CA ^ 2) := by
    have h1 : eLpNorm (fun ω => (freshC b E X ω).trace.re) (ENNReal.ofReal 3) (freshLaw W b) ≤
        eLpNorm (fun ω => (W : ℝ) * ‖freshLayer b E X ω‖ ^ 2) (ENNReal.ofReal 3) (freshLaw W b) :=
      eLpNorm_mono_real (Complex.measurable_re.comp (meas_trace hCm)).aestronglyMeasurable
        fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (trace_re_nonneg (freshC_posSemidef b E X ω))]
          exact trace_freshC_le b E X ω
    refine h1.trans ?_
    rw [eLpNorm_real_mul_le, abs_of_nonneg hW0.le, ENNReal.ofReal_mul hW0.le]
    gcongr
  have hCn : eLpNorm (fun ω => ‖freshC b E X ω‖) (ENNReal.ofReal 3) (freshLaw W b) ≤
      ENNReal.ofReal (CA ^ 2) := by
    refine le_trans (eLpNorm_mono_real (meas_freshC (W := W) b E |>.comp
      (f := fun ω => (X, ω)) (measurable_const.prodMk measurable_id)).norm.aestronglyMeasurable
      fun ω => ?_) hsq
    rw [Real.norm_eq_abs, abs_norm]; exact norm_freshC_le b E X ω
  have hUi := integrable_freshU_apply hG2
  have hfl3 : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
      matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal 3) (freshLaw W b) ≤
      ENNReal.ofReal (max Cf 0 * (Real.sqrt W)⁻¹ * vecNorm u * vecNorm v) := by
    intro u v
    refine (hfl W hWf E hE X (passiveY_posSemidef hX) u v).1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hu : 0 ≤ vecNorm u := Real.sqrt_nonneg _
    have hv : 0 ≤ vecNorm v := Real.sqrt_nonneg _
    rw [div_eq_mul_inv]
    gcongr
    exact le_max_left _ _
  have hdec := stepDefect_decomp (b := b) (E := E) (qv := qv) (a := a) (X := X) hQ ha0 hqv0
    hWpos (c := max Cf 0 * (Real.sqrt W)⁻¹) (mβ := (W : ℝ) * CA ^ 2) (mC := CA ^ 2)
    (by positivity) (by positivity) (sq_nonneg _) hUi hfl3 hβ hCn
  by_cases hδ : jetDistance0 b E X ≤ dw
  · -- the scalar domain
    obtain ⟨Ω, hΩ, hRem⟩ := hward W hWw E hE X hX hδ
    have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have hApsd := resolventWeight_posSemidef hQ ha0
    obtain ⟨hc1, hc2⟩ := hcov W hWc E hE s hs X hX (resolventWeight Q a) hApsd
    have hb1' : 0 ≤ (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
        (jetDistance0 b E X + jetDistance1 b E s X) := by
      have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
      positivity
    have hsA0 : 0 ≤ (resolventWeight Q a * passiveF b E X * resolventWeight Q a *
        (passiveF b E X)ᴴ).trace.re := by
      rw [trace_sandwich_eq_sum hApsd.1, Complex.ofReal_re]; exact sandwichSum_nonneg hApsd _
    have hcov' := And.intro
      (le_max_mul (add_nonneg (by positivity) (mul_nonneg hb1' (sq_nonneg _))) hc1)
      (le_max_mul (add_nonneg (div_nonneg hsA0 hW0.le) (mul_nonneg hb1' (sq_nonneg _))) hc2)
    have hfn : ‖passiveF b E X‖ ≤ Kf :=
      (ClockMixingAlg.norm_passiveF_le b E hz hX).trans (fBound_le hb1 hκ hκ4 hE)
    refine (stepDefect_domain hW1 hQ hK hKq ⟨ha0', haK⟩ ⟨hqv0, hqvK⟩ (le_max_right _ _)
      (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) hCA.le hKf0
      hfn Ω (le_max_mul (by positivity) hΩ)
      (le_max_mul (by positivity) hRem) hcov'
      (le_max_mul (by positivity) (hinj W hWi E hE X hX).2) hdec).trans ?_
    have hP0 : 0 ≤ pastWeight W b E s X Q ^ 9 * w ^ 3 := by
      have : 0 ≤ pastWeight W b E s X Q := by
        unfold pastWeight
        have h1 := trace_re_nonneg hQ
        have h2 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
        have h3 := hsSandwich_nonneg Q (passiveF b E X)
        have h4 : 0 ≤ (W : ℝ) * (jetDistance0 b E X + jetDistance1 b E s X) :=
          mul_nonneg hW0.le (add_nonneg hδ0 h2)
        have h5 : 0 ≤ Real.sqrt W * (‖(Q * passiveF b E X).trace‖ +
            hsSandwich Q (passiveF b E X)) := mul_nonneg (Real.sqrt_nonneg _)
          (add_nonneg (norm_nonneg _) h3)
        linarith
      positivity
    have := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCoff0 : Cdom ≤ Cdom + Coff) hP0
    calc Cdom * pastWeight W b E s X Q ^ 9 * w ^ 3 = Cdom * (pastWeight W b E s X Q ^ 9 * w ^ 3) :=
          by ring
      _ ≤ (Cdom + Coff) * (pastWeight W b E s X Q ^ 9 * w ^ 3) := this
      _ = _ := by ring
  · -- off the scalar domain
    push Not at hδ
    have hcr := stepDefect_crude (X := X) hQ ha0 hqv0 hD hd (b := b) (E := E) (qv := qv) (W := W)
    set Λ := pastWeight W b E s X Q with hΛ
    have hγ0 := trace_re_nonneg hQ
    have hδ10 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    have hΛe : Λ = 1 + Q.trace.re + W * (jetDistance0 b E X + jetDistance1 b E s X) +
        Real.sqrt W * (‖(Q * passiveF b E X).trace‖ + hsSandwich Q (passiveF b E X)) := rfl
    have hsZ : 0 ≤ Real.sqrt W * (‖(Q * passiveF b E X).trace‖ + hsSandwich Q (passiveF b E X)) :=
      by have := hsSandwich_nonneg Q (passiveF b E X); positivity
    have hWδ : 0 ≤ (W : ℝ) * (jetDistance0 b E X + jetDistance1 b E s X) := by
      have : 0 ≤ jetDistance0 b E X := norm_nonneg _
      positivity
    have hΛ1 : 1 ≤ Λ := by rw [hΛe]; linarith
    have hγΛ : Q.trace.re ≤ Λ := by rw [hΛe]; linarith
    have hδΛ : jetDistance0 b E X ≤ Λ * w ^ 2 := by
      rw [hw2, ← div_eq_mul_inv, le_div_iff₀ hW0]
      have : (W : ℝ) * jetDistance0 b E X ≤ W * (jetDistance0 b E X + jetDistance1 b E s X) :=
        mul_le_mul_of_nonneg_left (by linarith) hW0.le
      rw [hΛe]; linarith
    have hTA := (re_trace_resolventWeight_le hQ ha0).trans (mul_le_mul_nn ha0 haK hγ0 hγΛ)
    have hTA0 := re_trace_resolventWeight_nonneg hQ ha0
    have hTA2 : (resolventWeight Q a).trace.re ^ 2 ≤ (K * Λ) ^ 2 := pow_le_pow_left₀ hTA0 hTA 2
    have hΛ0 : 0 ≤ Λ := by linarith
    have hΛ2 : (1 : ℝ) ≤ Λ ^ 2 := one_le_pow₀ hΛ1
    have hc1 : |stepDefect W b E qv a X Q| ≤ (2 + D0m * K ^ 2 + dStar b * Kq * K) *
        Λ ^ 2 := by
      refine hcr.trans ?_
      have hWi1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
      have h1 : transportD0 b E * (resolventWeight Q a).trace.re ^ 2 + dStar b * qv * a ≤
          (D0m * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 := by
        have e1 : transportD0 b E * (resolventWeight Q a).trace.re ^ 2 ≤
            D0m * K ^ 2 * Λ ^ 2 := by
          have := mul_le_mul_of_nonneg_left hTA2 hD
          have h' : transportD0 b E * (K * Λ) ^ 2 ≤ D0m * (K * Λ) ^ 2 :=
            mul_le_mul_of_nonneg_right hDle (sq_nonneg _)
          calc _ ≤ transportD0 b E * (K * Λ) ^ 2 := this
            _ ≤ D0m * (K * Λ) ^ 2 := h'
            _ = _ := by ring
        have e2 : dStar b * qv * a ≤ dStar b * Kq * K * Λ ^ 2 := by
          have h3 : dStar b * qv * a ≤ dStar b * Kq * K :=
            mul_le_mul_nn (mul_nonneg hd hqv0) (mul_le_mul_of_nonneg_left hqvK hd) ha0 haK
          have h4 := mul_le_mul_of_nonneg_left hΛ2 (by positivity : 0 ≤ dStar b * Kq * K)
          linarith
        have e : (D0m * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 =
            D0m * K ^ 2 * Λ ^ 2 + dStar b * Kq * K * Λ ^ 2 := by ring
        linarith
      have hy0 : 0 ≤ transportD0 b E * (resolventWeight Q a).trace.re ^ 2 +
          dStar b * qv * a := by
        have : 0 ≤ transportD0 b E * (resolventWeight Q a).trace.re ^ 2 :=
          mul_nonneg hD (sq_nonneg _)
        have : 0 ≤ dStar b * qv * a := mul_nonneg (mul_nonneg hd hqv0) ha0
        linarith
      have h2 := mul_le_mul_nn (by positivity) hWi1 hy0 h1
      have h3 : (2 : ℝ) ≤ 2 * Λ ^ 2 := by linarith
      have e : (2 + D0m * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 =
          2 * Λ ^ 2 + (D0m * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 := by ring
      linarith
    have hratio : 1 ≤ (Λ * w ^ 2 / dw) ^ 2 := by
      have : 1 ≤ Λ * w ^ 2 / dw := by rw [le_div_iff₀ hdw]; linarith
      exact one_le_pow₀ this
    have hc2 : |stepDefect W b E qv a X Q| ≤ Coff * Λ ^ 4 * w ^ 4 := by
      have h0 : 0 ≤ (2 + D0m * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hratio h0
      calc |stepDefect W b E qv a X Q| ≤ (2 + D0m * K ^ 2 + dStar b * Kq * K) *
            Λ ^ 2 * 1 := by rw [mul_one]; exact hc1
        _ ≤ (2 + D0m * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 * (Λ * w ^ 2 / dw) ^ 2 :=
            this
        _ = Coff * Λ ^ 4 * w ^ 4 := by rw [hCoff]; field_simp
    have hc3 := le_mono_bound (k := 4) (l := 4) hCoff0 hΛ1 hw0 hw1 (by norm_num) (by norm_num) hc2
    have hP0 : 0 ≤ Λ ^ 9 * w ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCdom0 : Coff ≤ Cdom + Coff) hP0
    calc |stepDefect W b E qv a X Q| ≤ Coff * Λ ^ 9 * w ^ 3 := hc3
      _ = Coff * (Λ ^ 9 * w ^ 3) := by ring
      _ ≤ (Cdom + Coff) * (Λ ^ 9 * w ^ 3) := this
      _ = _ := by ring

end DetClockBulk

end MovingEnergy

end BlockBand.Endpoints.Clock
