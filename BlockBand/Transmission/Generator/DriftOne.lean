module

public import BlockBand.Transmission.Generator.DriftOneL2
public import BlockBand.Transmission.LengthUniform.ConductanceUniform

/-!
# The `k = 1` drift error in `L²`, one length at a time

Proof: `driftError_one_le` and `rf_err_le` give a.s.
`|Z| ≤ K(a+1)²(t+1)(q+1)³/W^{3/2} + 8Δ(q+1)²/W` with `a = Wδ₀`, `t = √W|Tr Qf|`, `q = q(X_r)`;
then `l2_of_moments` with `∫(a+1)¹² ≤ 2¹²(C_δ¹² + 1)` (`DeltaZeroLengthUniform`),
`∫(t+1)⁶ ≤ 2⁶(C_τ⁶ + 1)` (mixing) and `∫(q+1)¹⁸ ≤ 2¹⁸(C_g/(4η_L)¹⁸ + 1)`
(`TransmissionLengthUniformContract.conductance`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- A moment from an `L^p` bound: `‖f‖_n ≤ σ/c`, `c > 0` ⇒ `∫(cf)ⁿ ≤ σⁿ`. -/
theorem moment_scaled {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (n : ℕ) (hn : 1 ≤ n) {σ c : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (h : eLpNorm f (ENNReal.ofReal (n : ℝ)) μ ≤ ENNReal.ofReal (σ / c)) :
    ∫ ω, (c * f ω) ^ n ∂μ ≤ σ ^ n := by
  have h1 := mp_integral_pow_le hf0 n hn (by positivity) h
  have e : (fun ω => (c * f ω) ^ n) = fun ω => c ^ n * f ω ^ n := by funext ω; rw [mul_pow]
  rw [e, integral_const_mul]
  calc c ^ n * ∫ ω, f ω ^ n ∂μ ≤ c ^ n * (σ / c) ^ n :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = σ ^ n := by rw [div_pow]; field_simp

/-- **`L²` bound of the `k = 1` drift error at one length.** -/
theorem driftError_one_L2 (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hMix : PassiveSourceMixingBulk) {b κ ε T : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (hε : 0 < ε) (hεT : ε < T) :
    ∃ (K₁ K₂ : ℝ) (W₀ : ℕ), 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E' ∈ bulkInterval κ,
      ∀ E : ℝ, ∀ r : ℕ, 1 ≤ r → ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (driftError b E E' W 1 r) 2 (growthPathLaw W b) ≤
          ENNReal.ofReal (K₁ / Real.sqrt W ^ 3 +
            K₂ * |transportD0 b E - transportD0 b E'| / W) := by
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  obtain ⟨C₀, W₁, hC₀, hW₁, hbd⟩ := driftError_one_le hA hb0 hb hκ
  obtain ⟨Cδ, hCδ, hδT⟩ := deltaZeroLengthUniform_holds hMT hGA hLp b hb0 hb κ ((12 : ℕ) : ℝ) hκ
    (by norm_num)
  obtain ⟨W₂, hδ⟩ := hδT T
  obtain ⟨Cτ, W₃, hτ⟩ := hMix b hb0 hb κ ε T ((6 : ℕ) : ℝ) hκ hε hεT (by norm_num)
  obtain ⟨Cg, hgT⟩ := (transmissionLengthUniform_holds hMT hGA hLp).conductance b hb0 hb κ ε
    ((18 : ℕ) : ℝ) hκ hε (by norm_num)
  obtain ⟨W₄, hg⟩ := hgT T
  set ηL := etaLow b κ
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ
  set αL := (1 - b) ^ 2 / (b * ηL)
  set K := 36 * C₀ + 4 * αL ^ 2
  have hK : 0 ≤ K := by positivity
  set Cτ' := max Cτ 0
  set Cg' := max Cg 0
  set MA := 2 ^ 12 * (Cδ ^ 12 + 1)
  set MT := 2 ^ 6 * (Cτ' ^ 6 + 1)
  set MQ := 2 ^ 18 * (Cg' / (4 * ηL) ^ 18 + 1)
  refine ⟨Real.sqrt (2 * K ^ 2 * (MA + MT + MQ)), Real.sqrt (128 * MQ),
    max (max W₁ W₂) (max W₃ W₄), Real.sqrt_nonneg _, Real.sqrt_nonneg _,
    fun W hW E' hE' E r hr1 hεr hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW3, hW4⟩ := hW
  have hW0 : 1 ≤ W := le_trans hW₁ hW1
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW0
  have h1 : -2 < E' := by have := hE'.1; linarith
  have h2 : E' < 2 := by have := hE'.2; linarith
  have hη := PassiveCovariance.etaZ_pos b E' (by linarith) h1 h2
  have hηLη : ηL ≤ etaZ b E' := etaLow_le (by linarith) hκ hE'
  set μ := growthPathLaw W b
  set s := Real.sqrt W
  have hs2 : s ^ 2 = (W : ℝ) := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
                         exact Real.sqrt_le_sqrt hWr
  have hs0 : 0 < s := by linarith
  set X := fun ω => pathX b E' W r ω
  have hXm : Measurable X := PathJet.measurable_pathX b E' r
  set δ := fun ω => jetDistance0 b E' (X ω)
  set τ := fun ω => ‖(passiveQ b E' (X ω) * passiveF b E' (X ω)).trace‖
  set q := fun ω => qc b E' (X ω)
  have hδm : Measurable δ := (measurable_jetDistance0 b E').comp hXm
  have hτm : Measurable τ := ((measurable_traceQF b E').comp hXm).norm
  have hqm : Measurable q := (measurable_qc b E').comp hXm
  have hpas := mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r
  have hq0 : ∀ ω, 0 ≤ q ω := fun ω => qc_nonneg b E' _
  have hqB : ∀ ω, q ω ≤ (4 * ηL)⁻¹ * W := fun ω => qc_le_bulk hb0 hb hκ hE' _
  have hδ0 : ∀ ω, 0 ≤ δ ω := fun ω => norm_nonneg _
  have hτ0 : ∀ ω, 0 ≤ τ ω := fun ω => norm_nonneg _
  have hδB : ∀ᵐ ω ∂μ, δ ω ≤ ηL⁻¹ + 1 := by
    filter_upwards [hpas] with ω hω
    exact (jetDistance0_le_bound hb0 hb h1 h2 hω).trans (by
      have := inv_anti₀ hηL hηLη; linarith)
  have hτB : ∀ᵐ ω ∂μ, τ ω ≤ 3 / (2 * ηL) * ((4 * ηL)⁻¹ * W) := by
    filter_upwards [hpas] with ω hω
    have h3 : τ ω ≤ ‖passiveF b E' (X ω)‖ * passiveMass b E' (X ω) := by
      simp only [τ]; rw [trace_mul_comm]
      exact PassiveCovariance.norm_trace_mul_posSemidef_le (hω.conjTranspose_mul_mul_same _) _
    have hf := PassiveCovariance.norm_passiveF_le hb0 hb h1 h2 hω
    have hf' : ‖passiveF b E' (X ω)‖ ≤ 3 / (2 * ηL) :=
      hf.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith))
    have hq' : passiveMass b E' (X ω) ≤ (4 * ηL)⁻¹ * W := by
      rw [← qc_eq hω]; exact hqB ω
    exact h3.trans (mul_le_mul hf' hq' (PassiveCovariance.passiveMass_nonneg b E' hω)
      (by positivity))
  -- the almost-sure bound
  have hZb : ∀ᵐ ω ∂μ, |driftError b E E' W 1 r ω| ≤
      K * (((s ^ 2 * δ ω) + 1) ^ 2 * ((s * τ ω) + 1) * (q ω + 1) ^ 3) / s ^ 3 +
        8 * |transportD0 b E - transportD0 b E'| * (q ω + 1) ^ 2 / s ^ 2 := by
    filter_upwards [hbd W hW1 E' hE' E r hr1, hpas] with ω hω hY
    refine hω.trans ?_
    set Δ := |transportD0 b E - transportD0 b E'|
    have hΔ : 0 ≤ Δ := abs_nonneg _
    have hqq : passiveMass b E' (X ω) = q ω := (qc_eq hY).symm
    have hE : refinedErr b E' (X ω) = (δ ω + (s ^ 2)⁻¹ ^ 2) * τ ω +
        (δ ω + (s ^ 2)⁻¹ ^ 2) ^ 2 * q ω + (δ ω + (s ^ 2)⁻¹ ^ 2) * q ω ^ 2 / s ^ 2 +
        (s ^ 2)⁻¹ ^ 2 * q ω := by
      simp only [refinedErr, hqq, hs2]; rfl
    have hR := rf_err_le hs1 (hδ0 ω) (norm_nonneg _) (hq0 ω) (τ := τ ω)
    rw [← hE] at hR
    set P := (s ^ 2 * δ ω + 1) ^ 2 * (s * τ ω + 1) * (q ω + 1) ^ 3
    have hP1 : (q ω + 1) ^ 3 ≤ P := by
      have : 1 ≤ (s ^ 2 * δ ω + 1) ^ 2 * (s * τ ω + 1) := one_le_mul_of_one_le_of_one_le
        (one_le_pow₀ (by have := hδ0 ω; nlinarith)) (by have := hτ0 ω; nlinarith)
      calc (q ω + 1) ^ 3 = 1 * (q ω + 1) ^ 3 := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right this (by have := hq0 ω; positivity)
    have hq3 : qc b E' (X ω) ^ 3 / (W : ℝ) ^ 2 ≤ P / s ^ 3 := by
      rw [← hs2, ← pow_mul]
      calc q ω ^ 3 / s ^ (2 * 2) ≤ (q ω + 1) ^ 3 / s ^ 3 :=
            div_le_div₀ (by have := hq0 ω; positivity) (pow_le_pow_left₀ (hq0 ω) (by linarith) 3)
              (by positivity) (pow_le_pow_right₀ hs1 (by norm_num))
        _ ≤ P / s ^ 3 := div_le_div_of_nonneg_right hP1 (by positivity)
    have hq2 : 8 * qc b E' (X ω) ^ 2 * Δ / (W : ℝ) ≤ 8 * Δ * (q ω + 1) ^ 2 / s ^ 2 := by
      rw [← hs2]
      have : q ω ^ 2 ≤ (q ω + 1) ^ 2 := pow_le_pow_left₀ (hq0 ω) (by linarith) 2
      have e : 8 * Δ * (q ω + 1) ^ 2 / s ^ 2 = 8 * (q ω + 1) ^ 2 * Δ / s ^ 2 := by ring
      rw [e]; gcongr
    have hαL : 0 ≤ 4 * αL ^ 2 := by positivity
    have t1 : 4 * C₀ * refinedErr b E' (X ω) ≤ 36 * C₀ * (P / s ^ 3) := by
      have := mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 4 * C₀)
      have e : 4 * C₀ * (9 * P / s ^ 3) = 36 * C₀ * (P / s ^ 3) := by ring
      linarith
    have t3 : 4 * αL ^ 2 * qc b E' (X ω) ^ 3 / (W : ℝ) ^ 2 ≤ 4 * αL ^ 2 * (P / s ^ 3) := by
      have := mul_le_mul_of_nonneg_left hq3 hαL
      rw [mul_div_assoc]; exact this
    have e2 : K * P / s ^ 3 = 36 * C₀ * (P / s ^ 3) + 4 * αL ^ 2 * (P / s ^ 3) := by
      simp only [K]; ring
    rw [e2]
    linarith
  -- moments
  have mA : ∫ ω, (s ^ 2 * δ ω + 1) ^ 12 ∂μ ≤ MA := by
    refine (moment_shift (μ := μ) (hδm.const_mul _) (ae_of_all _ fun ω => by
      have := hδ0 ω; positivity) (B := s ^ 2 * (ηL⁻¹ + 1)) (by
        filter_upwards [hδB] with ω h using mul_le_mul_of_nonneg_left h (by positivity)) 12).trans ?_
    have h := moment_scaled (μ := μ) (f := δ) (c := s ^ 2) (ae_of_all _ hδ0) 12 (by norm_num) hCδ
      (by rw [hs2]; positivity) (by rw [hs2]; exact hδ W hW2 E' hE' r hr1 (by linarith))
    simp only [MA]; gcongr
  have mT : ∫ ω, (s * τ ω + 1) ^ 6 ∂μ ≤ MT := by
    refine (moment_shift (μ := μ) (hτm.const_mul _) (ae_of_all _ fun ω => by
      have := hτ0 ω; positivity)
      (B := s * (3 / (2 * ηL) * ((4 * ηL)⁻¹ * W))) (by
        filter_upwards [hτB] with ω h using mul_le_mul_of_nonneg_left h hs0.le) 6).trans ?_
    have hτ6 : eLpNorm τ (ENNReal.ofReal ((6 : ℕ) : ℝ)) μ ≤ ENNReal.ofReal (Cτ' / s) := by
      have := hτ W hW3 E' hE' r hεr hrT
      rw [show τ = fun ω => ‖(passiveQ b E' (X ω) * passiveF b E' (X ω)).trace‖ from rfl,
        eLpNorm_norm (fun ω => (passiveQ b E' (X ω) * passiveF b E' (X ω)).trace)
          (((measurable_traceQF b E').comp hXm).aestronglyMeasurable)]
      refine (le_add_right le_rfl).trans (this.trans (ENNReal.ofReal_le_ofReal ?_))
      exact div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    have h := moment_scaled (μ := μ) (f := τ) (ae_of_all _ fun ω => norm_nonneg _) 6
      (by norm_num) (le_max_right _ _) hs0 hτ6
    simp only [MT]; gcongr
  have mQ : ∫ ω, (q ω + 1) ^ 18 ∂μ ≤ MQ := by
    refine (moment_shift (μ := μ) hqm (ae_of_all _ hq0) (ae_of_all _ hqB) 18).trans ?_
    have hgi := integral_pow_le_of_lintegral (μ := μ) (measurable_pathConductance b E' r)
      (by filter_upwards [hpas] with ω hω
          rw [pathConductance_eq_mass]
          exact mul_nonneg (by positivity) (PassiveCovariance.passiveMass_nonneg b E' hω)) 18
      (le_max_right Cg 0) ((hg W hW4 E' hE' r hεr hrT).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    have hqg : ∀ᵐ ω ∂μ, q ω ^ 18 ≤ pathConductance b E' W r ω ^ 18 / (4 * ηL) ^ 18 := by
      filter_upwards [hpas] with ω hω
      rw [pathConductance_eq_mass, ← div_pow, show q ω = passiveMass b E' (X ω) from qc_eq hω]
      refine pow_le_pow_left₀ (PassiveCovariance.passiveMass_nonneg b E' hω) ?_ 18
      rw [le_div_iff₀ (by positivity)]
      have := PassiveCovariance.passiveMass_nonneg b E' hω
      nlinarith
    have hi1 : Integrable (fun ω => q ω ^ 18) μ := integrable_of_bdd (hqm.pow_const 18)
      (B := ((4 * ηL)⁻¹ * W) ^ 18) (ae_of_all _ fun ω => by
        rw [abs_of_nonneg (pow_nonneg (hq0 ω) 18)]; exact pow_le_pow_left₀ (hq0 ω) (hqB ω) 18)
    have hi2 : Integrable (fun ω => pathConductance b E' W r ω ^ 18 / (4 * ηL) ^ 18) μ := by
      refine (integrable_of_bdd ((measurable_pathConductance b E' r).pow_const 18)
        (B := (W : ℝ) ^ 18) ?_).div_const _
      filter_upwards [pathPower_mem (W := W) (by linarith : b < 1) h1 h2] with ω hω
      obtain ⟨h0, h1', h3⟩ := hω 1 r le_rfl
      have hg0 : 0 ≤ pathConductance b E' W r ω := h0.trans h1'
      rw [abs_of_nonneg (pow_nonneg hg0 18)]; exact pow_le_pow_left₀ hg0 h3 18
    have hle : ∫ ω, q ω ^ 18 ∂μ ≤ Cg' / (4 * ηL) ^ 18 := by
      refine (integral_mono_ae hi1 hi2 hqg).trans ?_
      rw [integral_div]; exact div_le_div_of_nonneg_right hgi (by positivity)
    simp only [MQ]; gcongr
  have hL := l2_of_moments (μ := μ) (Z := driftError b E E' W 1 r)
    (a := fun ω => s ^ 2 * δ ω) (t := fun ω => s * τ ω) (q := q) ?_ (hδm.const_mul _)
    (hτm.const_mul _) hqm (ae_of_all _ fun ω => by have := hδ0 ω; positivity)
    (ae_of_all _ fun ω => by have := hτ0 ω; positivity) (ae_of_all _ hq0)
    (Ba := s ^ 2 * (ηL⁻¹ + 1)) (Bt := s * (3 / (2 * ηL) * ((4 * ηL)⁻¹ * W)))
    (by filter_upwards [hδB] with ω h using mul_le_mul_of_nonneg_left h (by positivity))
    (by filter_upwards [hτB] with ω h using mul_le_mul_of_nonneg_left h hs0.le)
    (ae_of_all _ hqB) hs1 hK (abs_nonneg _) hZb mA mT mQ
  · refine hL.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hs2]
  · exact (stronglyMeasurable_condExp.mono (growthSigma_le W r)).aestronglyMeasurable.sub
      ((measurable_drift_pathPowers b E E' 1 r).mono (growthSigma_le W r)
        le_rfl).aestronglyMeasurable

end BlockBand.Transmission.Generator
