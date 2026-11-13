module

public import BlockBand.Endpoints.Response.PassDerivativeLimitPort
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The uniform port-wise passage bound along moving energies

Clause 2 of the pass-derivative lemma, at the moving energies of the unfolded window: the bound
holds under the path law `growthPathLaw W b`, uniformly in the microscopic energy window.

* `PathFractionalInverseEnergyUniform` — the path fractional-inverse bound uniformly for
  energies `E'` with `|E' - E| ≤ C_e W⁻²` (the window `IsNearEnergy`), with the almost-sure
  invertibility of the full path matrix that the bound presupposes; proved as
  `pathFractionalInverseEnergyUniform_of_contracts`. At `C_e = 0` it is the clause-1 hypothesis
  `PathFractionalInverse` (same fixed energy).
* `portPass_bound`: port-wise clause-1 bound at one width and one energy from the two moment
  bounds (`E(Tr B_q)² ≤ K₁`, `E(‖G₀‖/W²)^s ≤ C₂`):
  `|E[(F_i(κ) - F_i(0))/κ] - E[D_i]| ≤ C(κ^{s/2} + κ)`, `|E D_i| ≤ 4c₁η(1 + K₁)`.
* `trB_sq_moment`: `E(Tr B_q)² ≤ Q²(C τ')²` from the clock moment at one energy.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped Matrix.Norms.L2Operator ENNReal NNReal

/-- **The path fractional-inverse bound uniformly in the microscopic energy window.** Fixed
`0 < b < 1/2`, bulk `-2 < E < 2`, `τ > 0`, path lengths `j W` with `j W / W → τ`, `0 < s < 1`
and a window constant `C_e`; then there are `C = C_{s,τ}` and `W₀` such that for every `W ≥ W₀`
and every energy `E'` with `|E' - E| ≤ C_e W⁻²`, under the path law `growthPathLaw W b`:
(a) the full path matrix at energy `E'` is almost surely invertible; and
(b) `E (‖G₀(E')‖/W²)^s ≤ C` (Euclidean operator norm). -/
def PathFractionalInverseEnergyUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ τ : ℝ, 0 < τ →
    ∀ j : ℕ → ℕ, Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ) →
    ∀ s : ℝ, 0 < s → s < 1 → ∀ Ce : ℝ, ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ E' : ℝ, IsNearEnergy Ce W E E' →
      (∀ᵐ ω ∂growthPathLaw W b, IsUnit (fullPathMatrix b E' W (j W) ω).det) ∧
      ∫⁻ ω, ENNReal.ofReal ((‖fullInverse b E' W (j W) ω‖ / (W : ℝ) ^ 2) ^ s)
          ∂growthPathLaw W b ≤ ENNReal.ofReal C

/-- At `C_e = 0` the window form gives the clause-1 hypothesis. -/
theorem PathFractionalInverseEnergyUniform.fixed (h : PathFractionalInverseEnergyUniform) :
    PathFractionalInverse := by
  intro b hb0 hb1 E hE1 hE2 τ hτ j hj s hs0 hs1
  obtain ⟨C, W₀, hC⟩ := h b hb0 hb1 E hE1 hE2 τ hτ j hj s hs0 hs1 0
  exact ⟨C, W₀, fun W hW => hC W hW E (by simp [IsNearEnergy])⟩

theorem etaZ_le_one {b E : ℝ} (hb0 : 0 ≤ b) (hE1 : -2 < E) (hE2 : E < 2) : etaZ b E ≤ 1 := by
  have h4 : 0 ≤ 4 - E ^ 2 := by nlinarith
  have hs := Real.sq_sqrt h4
  have hn : Complex.normSq (matchedA E) = 1 := by
    rw [Complex.normSq_apply]
    simp only [matchedA]
    nlinarith
  simp only [etaZ, boundaryZ, Complex.add_im, Complex.inv_im, hn,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  simp only [matchedA]
  have h0 := Real.sqrt_nonneg (4 - E ^ 2)
  have h2 : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  nlinarith

/-- Moving energies stay in the bulk for large `W`. -/
theorem IsMovingEnergy.eventually_bulk {E Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e)
    (hE1 : -2 < E) (hE2 : E < 2) : ∀ᶠ W : ℕ in atTop, -2 < e W ∧ e W < 2 := by
  have hlim : Tendsto (fun W : ℕ => Ce / (W : ℝ) ^ 2) atTop (𝓝 0) := by
    have h1 := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    have h2 := h1.const_mul Ce
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h2
    refine h2.congr fun W => ?_
    rw [div_eq_mul_inv, inv_pow]
  have hd : 0 < min (E + 2) (2 - E) := lt_min (by linarith) (by linarith)
  filter_upwards [hlim.eventually (gt_mem_nhds hd), eventually_gt_atTop 0] with W hW hW0
  have h := he W hW0
  unfold IsNearEnergy at h
  rw [abs_le] at h
  have := min_le_left (E + 2) (2 - E)
  have := min_le_right (E + 2) (2 - E)
  constructor <;> linarith [h.1, h.2]

/-- **Second moment of `Tr B_q`** from the clock moment at one width and energy:
`‖W⁻¹Tr 𝒰*𝒰‖₂ ≤ C(n+1)` and `(n+1)/W ≤ τ'` give `E(Tr B_q)² ≤ Q²(Cτ')²` for `0 ≤ q ≤ Q`. -/
theorem trB_sq_moment {b E : ℝ} {W n : ℕ} (hW : (1 : ℝ) ≤ W) {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t)
    {Q : ℝ} (hQ : ∀ t, q t ≤ Q) {C τ' : ℝ} (hC : 0 ≤ C) (hn : ((n : ℝ) + 1) / W ≤ τ')
    (hclock : eLpNorm (fun ω => (W : ℂ)⁻¹ *
        ((boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω).trace)
        (ENNReal.ofReal 2) (growthPathLaw W b) ≤ ENNReal.ofReal (C * ((n : ℝ) + 1))) :
    Integrable (fun ω => (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
        (leadInclusion W n)).trace.re ^ 2) (growthPathLaw W b) ∧
      ∫ ω, (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
        (leadInclusion W n)).trace.re ^ 2 ∂growthPathLaw W b ≤ Q ^ 2 * (C * τ') ^ 2 := by
  have hQ0 : 0 ≤ Q := (hq 0).trans (hQ 0)
  have hW0 : (0 : ℝ) < W := by linarith
  have hτ' : 0 ≤ τ' := le_trans (by positivity) hn
  set μ := growthPathLaw W b
  set TrB : GrowthPath W → ℝ := fun ω => (pencilSourceGram (fullPathMatrix b E W n ω)
    (sourceRoot W n q) (leadInclusion W n)).trace.re
  have hTrB0 : ∀ ω, 0 ≤ TrB ω := fun ω => by
    simp only [TrB, pencilSourceGram]
    rw [trace_conjTranspose_mul_self_re_eq_hsSq]; exact hsSq_nonneg _
  have hK₁ : 0 ≤ Q ^ 2 * (C * τ') ^ 2 := by positivity
  refine integrable_and_integral_le_of_lintegral (measurable_pencilSourceGram_trace.pow_const 2)
    (fun ω => sq_nonneg _) hK₁ ?_
  set f : GrowthPath W → ℂ := fun ω => (W : ℂ)⁻¹ *
    ((boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω).trace
  have hfm : AEStronglyMeasurable f μ :=
    (measurable_const.mul measurable_clock).aestronglyMeasurable
  have hL : ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal (C * ((n : ℝ) + 1)) ^ (2 : ℝ) := by
    have h0 := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2) two_ne_zero hfm
    have h2 : ENNReal.ofReal 2 = ((2 : ℝ≥0) : ℝ≥0∞) := by simp
    rw [h2] at hclock
    have e2 : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num
    rw [e2] at h0
    rw [← h0]
    exact ENNReal.rpow_le_rpow hclock (by norm_num)
  have hpt : ∀ ω, ENNReal.ofReal (TrB ω ^ 2) ≤
      ENNReal.ofReal (Q ^ 2 / (W : ℝ) ^ 2) * ‖f ω‖ₑ ^ (2 : ℝ) := by
    intro ω
    have h1 := pencilSourceGram_trace_le hq hQ (fullPathMatrix b E W n ω)
    rw [trace_conjTranspose_mul_self_re_eq_hsSq] at h1
    have hf : ‖f ω‖ = hsSq (boundaryToInterior b E W n ω) / W := by
      simp only [f]
      rw [trace_conjTranspose_mul_self_eq_hsSq, norm_mul, norm_inv, Complex.norm_natCast,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsSq_nonneg _)]
      ring
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hf]
    have h3 : TrB ω ≤ Q / (W : ℝ) ^ 2 * hsSq (boundaryToInterior b E W n ω) := h1
    have h4 : TrB ω ^ 2 ≤ (Q / (W : ℝ) ^ 2 * hsSq (boundaryToInterior b E W n ω)) ^ 2 :=
      pow_le_pow_left₀ (hTrB0 ω) h3 2
    have h5 : (hsSq (boundaryToInterior b E W n ω) / W) ^ (2 : ℝ) =
        (hsSq (boundaryToInterior b E W n ω) / W) ^ 2 := by norm_cast
    rw [h5]
    calc TrB ω ^ 2 ≤ (Q / (W : ℝ) ^ 2 * hsSq (boundaryToInterior b E W n ω)) ^ 2 := h4
      _ = Q ^ 2 / (W : ℝ) ^ 2 * (hsSq (boundaryToInterior b E W n ω) / W) ^ 2 := by
          field_simp
  calc ∫⁻ ω, ENNReal.ofReal (TrB ω ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (Q ^ 2 / (W : ℝ) ^ 2) * ‖f ω‖ₑ ^ (2 : ℝ) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (Q ^ 2 / (W : ℝ) ^ 2) * ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Q ^ 2 / (W : ℝ) ^ 2) * ENNReal.ofReal (C * ((n : ℝ) + 1)) ^ (2 : ℝ) :=
        by gcongr
    _ = ENNReal.ofReal (Q ^ 2 / (W : ℝ) ^ 2 * (C * ((n : ℝ) + 1)) ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        norm_cast
    _ ≤ ENNReal.ofReal (Q ^ 2 * (C * τ') ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : Q ^ 2 / (W : ℝ) ^ 2 * (C * ((n : ℝ) + 1)) ^ 2 =
            Q ^ 2 * (C * (((n : ℝ) + 1) / W)) ^ 2 := by field_simp
        rw [e]
        have h0 : 0 ≤ ((n : ℝ) + 1) / W := by positivity
        have : C * (((n : ℝ) + 1) / W) ≤ C * τ' := mul_le_mul_of_nonneg_left hn hC
        have h6 : (C * (((n : ℝ) + 1) / W)) ^ 2 ≤ (C * τ') ^ 2 :=
          pow_le_pow_left₀ (by positivity) this 2
        exact mul_le_mul_of_nonneg_left h6 (sq_nonneg Q)

/-- **Port-wise passage bound** at one width and one energy, from `E(Tr B_q)² ≤ K₁`,
`E(‖G₀‖/W²)^s ≤ C₂` and almost-sure invertibility. -/
theorem portPass_bound {b E x y : ℝ} {W n : ℕ} (hb : b ≤ 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) {Q : ℝ}
    (hQ : ∀ t, q t ≤ Q) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {K₁ C₂ : ℝ} (hK₁ : 0 ≤ K₁)
    (hC₂ : 0 ≤ C₂)
    (hF2 : Integrable (fun ω => (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
        (leadInclusion W n)).trace.re ^ 2) (growthPathLaw W b) ∧
      ∫ ω, (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
        (leadInclusion W n)).trace.re ^ 2 ∂growthPathLaw W b ≤ K₁)
    (hF3 : ∫⁻ ω, ENNReal.ofReal ((‖fullInverse b E W n ω‖ / (W : ℝ) ^ 2) ^ s)
        ∂growthPathLaw W b ≤ ENNReal.ofReal C₂)
    (hinv : ∀ᵐ ω ∂growthPathLaw W b, IsUnit (fullPathMatrix b E W n ω).det) (i : Fin 2) :
    Integrable (fun ω => portDeriv b E x y W n q i ω) (growthPathLaw W b) ∧
    |∫ ω, portDeriv b E x y W n q i ω ∂growthPathLaw W b| ≤
      4 * ratioC1 x y * etaZ b E * (1 + K₁) ∧
    ∀ κ : ℝ, 0 < κ →
      |(∫ ω, (portRatio b E x y W n q κ i ω - portRatio b E x y W n q 0 i ω) / κ
          ∂growthPathLaw W b) - ∫ ω, portDeriv b E x y W n q i ω ∂growthPathLaw W b| ≤
        (2 * ratioC1 x y * etaZ b E * K₁ + 8 * ratioC1 x y * etaZ b E * Q ^ s * C₂ +
          (36 * ratioC1 x y + 576 * ratioC2 x y) * etaZ b E ^ 2 * K₁) * (κ ^ (s / 2) + κ) := by
  have hQ0 : 0 ≤ Q := (hq 0).trans (hQ 0)
  have hη : 0 ≤ etaZ b E := etaZ_nonneg hb hE1 hE2
  have hc₁ : 0 ≤ ratioC1 x y := ratioC1_nonneg hx hy0 hy1
  have hc₂ : 0 ≤ ratioC2 x y := ratioC2_nonneg x y
  set η := etaZ b E
  set c₁ := ratioC1 x y
  set c₂ := ratioC2 x y
  have : IsProbabilityMeasure (growthPathLaw W b) :=
    passDeriv_isProbabilityMeasure_growthPathLaw W b
  set μ := growthPathLaw W b
  set F : ℝ → GrowthPath W → ℝ := fun κ' ω => portRatio b E x y W n q κ' i ω
  set h : GrowthPath W → ℝ := fun ω => portDeriv b E x y W n q i ω
  set TrB : GrowthPath W → ℝ := fun ω => (pencilSourceGram (fullPathMatrix b E W n ω)
    (sourceRoot W n q) (leadInclusion W n)).trace.re
  set g : GrowthPath W → ℝ := fun ω => ‖fullInverse b E W n ω‖ / (W : ℝ) ^ 2
  have hTrB0 : ∀ ω, 0 ≤ TrB ω := fun ω => by
    simp only [TrB, pencilSourceGram]
    rw [trace_conjTranspose_mul_self_re_eq_hsSq]; exact hsSq_nonneg _
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by positivity
  have hF3' : Integrable (fun ω => g ω ^ s) μ ∧ ∫ ω, g ω ^ s ∂μ ≤ C₂ :=
    integrable_and_integral_le_of_lintegral
      ((measurable_fullInverse_norm.div_const _).pow_const s)
      (fun ω => Real.rpow_nonneg (hg0 ω) s) hC₂ hF3
  have hgood : ∀ᵐ ω ∂μ, (∀ k, (ω.1 k).IsHermitian) ∧ IsUnit (fullPathMatrix b E W n ω).det :=
    (ae_growthPath_isHermitian W b).and hinv
  have hhi : Integrable h μ := by
    refine Integrable.mono' ((integrable_const (4 * c₁ * η)).add (hF2.1.const_mul (4 * c₁ * η)))
      (measurable_portDeriv i).aestronglyMeasurable ?_
    refine hgood.mono fun ω hω => ?_
    obtain ⟨-, h2⟩ := portRatio_bounds hb hE1 hE2 hx hy0 hy1 hq i hω.1
    obtain ⟨-, hh⟩ := h2 hω.2
    rw [Real.norm_eq_abs]
    refine hh.trans ?_
    have : TrB ω ≤ 1 + TrB ω ^ 2 := by nlinarith [sq_nonneg (TrB ω - 1)]
    have hc : 0 ≤ 4 * c₁ * η := by positivity
    have h9 := mul_le_mul_of_nonneg_left this hc
    show c₁ * (4 * η * TrB ω) ≤ 4 * c₁ * η + 4 * c₁ * η * TrB ω ^ 2
    calc c₁ * (4 * η * TrB ω) = 4 * c₁ * η * TrB ω := by ring
      _ ≤ 4 * c₁ * η * (1 + TrB ω ^ 2) := h9
      _ = _ := by ring
  refine ⟨hhi, ?_, fun κ hκ => ?_⟩
  · -- `|E D| ≤ 4c₁η(1 + K₁)`
    have hb' : Integrable (fun ω => 4 * c₁ * η * (1 + TrB ω ^ 2)) μ :=
      ((integrable_const 1).add hF2.1).const_mul _
    calc |∫ ω, h ω ∂μ| ≤ ∫ ω, |h ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, 4 * c₁ * η * (1 + TrB ω ^ 2) ∂μ := by
          refine integral_mono_ae hhi.abs hb' (hgood.mono fun ω hω => ?_)
          obtain ⟨-, h2⟩ := portRatio_bounds hb hE1 hE2 hx hy0 hy1 hq i hω.1
          obtain ⟨-, hh⟩ := h2 hω.2
          have : TrB ω ≤ 1 + TrB ω ^ 2 := by nlinarith [sq_nonneg (TrB ω - 1)]
          have hc : 0 ≤ 4 * c₁ * η := by positivity
          calc |h ω| ≤ c₁ * (4 * η * TrB ω) := hh
            _ = 4 * c₁ * η * TrB ω := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left this hc
      _ = 4 * c₁ * η * (1 + ∫ ω, TrB ω ^ 2 ∂μ) := by
          rw [integral_const_mul, integral_add (integrable_const 1) hF2.1]
          simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
          rfl
      _ ≤ 4 * c₁ * η * (1 + K₁) := by
          have : 0 ≤ 4 * c₁ * η := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith [hF2.2]) this
  -- pointwise bound
  set l := κ ^ (s / 2)
  have hl0 : 0 ≤ l := Real.rpow_nonneg hκ.le _
  set A := 2 * c₁ * η * l + (36 * c₁ + 576 * c₂) * η ^ 2 * κ
  set B := 8 * c₁ * η * Q ^ s * l
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by have := Real.rpow_nonneg hQ0 s; positivity
  have hpt : ∀ ω, (∀ k, (ω.1 k).IsHermitian) → IsUnit (fullPathMatrix b E W n ω).det →
      |(F κ ω - F 0 ω) / κ - h ω| ≤ A * TrB ω ^ 2 + B * g ω ^ s := by
    intro ω hH hM
    obtain ⟨-, h2⟩ := portRatio_bounds hb hE1 hE2 hx hy0 hy1 hq i hH
    obtain ⟨hdiff, -⟩ := h2 hM
    have hd := hdiff κ hκ.le
    have e : (F κ ω - F 0 ω) / κ - h ω = (F κ ω - F 0 ω - κ * h ω) / κ := by
      field_simp
    rw [e, abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
    have hK := sourceKernel_norm_le hq hQ (fullPathMatrix b E W n ω)
    set k := ‖sourceKernel (fullPathMatrix b E W n ω) (sourceRoot W n q)‖
    have hk0 : 0 ≤ k := norm_nonneg _
    have hkg : k ≤ Q * g ω := by
      have : Q / (W : ℝ) ^ 2 * ‖(fullPathMatrix b E W n ω)⁻¹‖ = Q * g ω := by
        simp only [g, fullInverse]; ring
      linarith
    have hks : k ^ s ≤ Q ^ s * g ω ^ s := by
      rw [← Real.mul_rpow hQ0 (hg0 ω)]
      exact Real.rpow_le_rpow hk0 hkg hs0.le
    have hm := mul_min_two_le (t := TrB ω) hκ hk0 hs0 (by linarith)
    have hd' : |F κ ω - F 0 ω - κ * h ω| ≤ κ * (4 * c₁ * η * TrB ω * min 2 (κ * k) +
        κ * (36 * c₁ + 576 * c₂) * η ^ 2 * TrB ω ^ 2) := hd
    refine hd'.trans ?_
    have hc : 0 ≤ 4 * c₁ * η := by positivity
    have h7 : 4 * c₁ * η * TrB ω * min 2 (κ * k) ≤
        4 * c₁ * η * (l * (TrB ω ^ 2 + 4 * (Q ^ s * g ω ^ s)) / 2) := by
      rw [mul_assoc (4 * c₁ * η)]
      refine mul_le_mul_of_nonneg_left (hm.trans ?_) hc
      have : l * (TrB ω ^ 2 + 4 * k ^ s) ≤ l * (TrB ω ^ 2 + 4 * (Q ^ s * g ω ^ s)) :=
        mul_le_mul_of_nonneg_left (by linarith) hl0
      linarith
    have h8 : κ * (4 * c₁ * η * TrB ω * min 2 (κ * k) +
        κ * (36 * c₁ + 576 * c₂) * η ^ 2 * TrB ω ^ 2) ≤
        κ * (4 * c₁ * η * (l * (TrB ω ^ 2 + 4 * (Q ^ s * g ω ^ s)) / 2) +
        κ * (36 * c₁ + 576 * c₂) * η ^ 2 * TrB ω ^ 2) := by
      have := mul_le_mul_of_nonneg_left h7 hκ.le
      nlinarith
    refine h8.trans (le_of_eq ?_)
    simp only [A, B]
    ring
  have hFm : ∀ κ', Measurable (F κ') := fun κ' => measurable_portRatio hq κ' i
  have hΔm : Measurable (fun ω => (F κ ω - F 0 ω) / κ) :=
    ((hFm κ).sub (hFm 0)).div_const κ
  have hΔi : Integrable (fun ω => (F κ ω - F 0 ω) / κ) μ := by
    refine Integrable.mono' (integrable_const (2 / κ)) hΔm.aestronglyMeasurable ?_
    refine hgood.mono fun ω hω => ?_
    obtain ⟨h1, -⟩ := portRatio_bounds hb hE1 hE2 hx hy0 hy1 hq i hω.1
    have a1 := h1 κ hκ.le
    have a0 := h1 0 le_rfl
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hκ, div_le_div_iff_of_pos_right hκ]
    exact (abs_sub _ _).trans (by linarith)
  rw [← integral_sub hΔi hhi]
  have hbd : Integrable (fun ω => A * TrB ω ^ 2 + B * g ω ^ s) μ :=
    (hF2.1.const_mul A).add (hF3'.1.const_mul B)
  have hQs : 0 ≤ Q ^ s := Real.rpow_nonneg hQ0 s
  calc |∫ ω, ((F κ ω - F 0 ω) / κ - h ω) ∂μ|
      ≤ ∫ ω, |(F κ ω - F 0 ω) / κ - h ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (A * TrB ω ^ 2 + B * g ω ^ s) ∂μ :=
        integral_mono_ae (hΔi.sub hhi).abs hbd (hgood.mono fun ω hω => hpt ω hω.1 hω.2)
    _ = A * ∫ ω, TrB ω ^ 2 ∂μ + B * ∫ ω, g ω ^ s ∂μ := by
        rw [integral_add (hF2.1.const_mul A) (hF3'.1.const_mul B), integral_const_mul,
          integral_const_mul]
    _ ≤ A * K₁ + B * C₂ :=
        add_le_add (mul_le_mul_of_nonneg_left hF2.2 hA0) (mul_le_mul_of_nonneg_left hF3'.2 hB0)
    _ ≤ _ := by
        have e : A * K₁ + B * C₂ = l * (2 * c₁ * η * K₁ + 8 * c₁ * η * Q ^ s * C₂) +
            κ * ((36 * c₁ + 576 * c₂) * η ^ 2 * K₁) := by
          simp only [A, B]; ring
        rw [e]
        have h1 : 0 ≤ 2 * c₁ * η * K₁ + 8 * c₁ * η * Q ^ s * C₂ := by positivity
        have h3 : 0 ≤ (36 * c₁ + 576 * c₂) * η ^ 2 * K₁ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h3 :
            2 * c₁ * η * K₁ + 8 * c₁ * η * Q ^ s * C₂ ≤ _) hl0,
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h1 :
            (36 * c₁ + 576 * c₂) * η ^ 2 * K₁ ≤ _) hκ.le]

end BlockBand.Endpoints
