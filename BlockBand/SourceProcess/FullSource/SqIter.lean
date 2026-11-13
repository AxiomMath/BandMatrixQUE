module

public import BlockBand.SourceProcess.FullSource.SqStep
public import BlockBand.SourceProcess.FullSource.TagFinal

/-!
# Iterating the tag-square recursion; crude growth; removing the stops

* `stopped_sq_iter`: `M_m ≤ a^m(M_0 + mDτ)` for `M_m = E[1_{G_{k+1+m}}Z^h_{k+1+m}]`,
  `a = 1 + α/W`, when `E t_{k+1+i}² ≤ τ` for `i < m`;
* `crude_sq_step`, `crude_sq_iter`: `E h_{k+1+m}² ≤ (C_N⁸)^m E h_{k+1}²` (no stopping);
* `sq_stop_removal`: `E h_j ≤ E[1_{G_j}Z^h_j] + (E h_j²)^{1/2} μ(G_jᶜ)^{1/2}` (Hölder).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PathScalar
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-- **Iteration of the stopped square step** (with the additive tag-mass term). -/
theorem stopped_sq_iter {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {k : ℕ} (hW : 1 ≤ W)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d₀ d : ℝ} (hL : TagLayerBounds b E W 2 Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : lsq Ca ≤ K * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * lsq Ca * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) {τ : ℝ≥0∞} (m : ℕ)
    (hτ : ∀ i, i < m →
      ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1 + i) k ω ^ 2) ∂growthPathLaw W b ≤ τ) :
    ∫⁻ ω, (stopEv b E W k d (k + 1 + m)).indicator (sqWeight b E W k K (k + 1 + m)) ω
        ∂growthPathLaw W b ≤
      ENNReal.ofReal (1 + alphaSq K Cm Ca Cf CN / W) ^ m *
        (∫⁻ ω, (stopEv b E W k d (k + 1)).indicator (sqWeight b E W k K (k + 1)) ω
          ∂growthPathLaw W b + m * (ENNReal.ofReal (dsq K Cm C₂ ρ) * τ)) := by
  set a := ENNReal.ofReal (1 + alphaSq K Cm Ca Cf CN / W)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ha : 1 ≤ a := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right
      (div_nonneg (alphaSq_nonneg hK hCm hCa hCN) hW0.le))
  induction m with
  | zero => simp
  | succ m ih =>
    have h := stopped_sq_step hb0 hb hE1 hE2 (k := k) (j := k + 1 + m) hW (by omega) hL hCa hC₂
      hCN hCf hCm hK hρ0 hρ1 hKL hd1 hρLd hdd₀
    rw [show k + 1 + (m + 1) = k + 1 + m + 1 by omega]
    refine h.trans ?_
    set M₀ := ∫⁻ ω, (stopEv b E W k d (k + 1)).indicator (sqWeight b E W k K (k + 1)) ω
      ∂growthPathLaw W b
    set Dτ := ENNReal.ofReal (dsq K Cm C₂ ρ) * τ
    have h1 := mul_le_mul_of_nonneg_left (ih fun i hi => hτ i (by omega)) (zero_le (a := a))
    have h2 : ENNReal.ofReal (dsq K Cm C₂ ρ) *
        ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1 + m) k ω ^ 2) ∂growthPathLaw W b ≤ Dτ :=
      mul_le_mul_of_nonneg_left (hτ m (by omega)) zero_le
    have h3 : Dτ ≤ a ^ (m + 1) * Dτ := le_mul_of_one_le_left zero_le (one_le_pow₀ ha)
    calc a * ∫⁻ ω, (stopEv b E W k d (k + 1 + m)).indicator (sqWeight b E W k K (k + 1 + m)) ω
            ∂growthPathLaw W b + ENNReal.ofReal (dsq K Cm C₂ ρ) *
          ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1 + m) k ω ^ 2) ∂growthPathLaw W b
        ≤ a * (a ^ m * (M₀ + m * Dτ)) + a ^ (m + 1) * Dτ := add_le_add h1 (h2.trans h3)
      _ = a ^ (m + 1) * (M₀ + ((m + 1 : ℕ) : ℝ≥0∞) * Dτ) := by
        rw [← mul_assoc, ← pow_succ', ← mul_add, Nat.cast_succ, add_mul, one_mul, add_assoc]

/-- **One crude square step**: `E h_{j+1}² ≤ C_N⁸ E h_j²` from `‖‖N‖‖₈ ≤ C_N`. -/
theorem crude_sq_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {k j : ℕ} (hW : 1 ≤ W) (hkj : k + 1 ≤ j) {CN : ℝ} (hCN : 0 ≤ CN)
    (hN : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * (2 * 2) : ℕ) : ℝ))
        (freshLaw W b) ≤ ENNReal.ofReal CN) :
    ∫⁻ ω, ENNReal.ofReal (tagSq b E W (j + 1) k ω ^ 2) ∂growthPathLaw W b ≤
      ENNReal.ofReal (CN ^ (2 * (2 * 2))) *
        ∫⁻ ω, ENNReal.ofReal (tagSq b E W j k ω ^ 2) ∂growthPathLaw W b := by
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℝ≥0∞ := fun q' =>
    ENNReal.ofReal (sqPlus b E (pastXX E W j q'.1) (pastS b E W j k q'.1) q'.2 ^ 2)
  set Ψ : PastSample W j → ℝ≥0∞ := fun p => ENNReal.ofReal (CN ^ (2 * (2 * 2))) *
    ENNReal.ofReal (sqOf W (pastS b E W j k p) ^ 2)
  have hmΦ : Measurable Φ := by
    have hXX : Measurable fun q' : PastSample W j × LayerSample W .oneBlockOnePort =>
        pastXX E W j q'.1 := (measurable_pastXX E j).comp measurable_fst
    have hN' := measurable_freshTransport_comp b E hXX measurable_snd
    have hSN := measurable_matrix_mul' ((measurable_pastS b E j k).comp measurable_fst) hN'
    exact ((measurable_sqOf_comp hSN).pow_const 2).ennreal_ofReal
  have hmΨ : Measurable Ψ :=
    measurable_const.mul (((measurable_sqOf_comp (measurable_pastS b E j k)).pow_const
      2).ennreal_ofReal)
  have hZ : ∀ᵐ ω ∂growthPathLaw W b, pastCoords W j ω ∈ (Set.univ : Set (PastSample W j)) →
      ENNReal.ofReal (tagSq b E W (j + 1) k ω ^ 2) ≤ Φ (pastCoords W j ω, freshSample W j ω) := by
    filter_upwards [ae_tagResponse_succ_full hb0 hb hE1 hE2 hW] with ω h1 _
    refine le_of_eq ?_
    simp only [Φ]
    have hY : tagResponse b E W (j + 1) k ω =
        (pastS b E W j k (pastCoords W j ω) * freshTransport b E (pastXX E W j (pastCoords W j ω))
          (freshSample W j ω))ᴴ * (pastS b E W j k (pastCoords W j ω) *
            freshTransport b E (pastXX E W j (pastCoords W j ω)) (freshSample W j ω)) := by
      rw [h1 j (by omega) k (by omega), tagResponse_eq_factor, transportN, pastXX_eq,
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [tagSq, hY]; rfl
  have hstep : ∀ᵐ p ∂pastLaw W j b, p ∈ (Set.univ : Set (PastSample W j)) →
      ∫⁻ f, Φ (p, f) ∂freshLaw W b ≤ Ψ p := by
    filter_upwards [ae_pastLaw_hermitian W j b] with p hp _
    obtain ⟨hi, hb'⟩ := sqStep_crude_moment (pastXX E W j p) (pastS b E W j k p) hCN
      (hN _ (pastXX_isHermitian E hp))
    simp only [Φ, Ψ]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun f =>
      sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hb'
  have h := lintegral_indicator_step (μ := growthPathLaw W b) (μP := pastLaw W j b)
    (ν := freshLaw W b) (measurable_pastCoords W j) (measurable_freshSample W j)
    (growthPathLaw_map_past_fresh W j b) MeasurableSet.univ hmΦ hmΨ hZ hstep
  simp only [Set.preimage_univ, Set.indicator_univ] at h
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_const_mul]
  · congr 1; funext ω; simp only [Ψ, tagSq_eq_past]
  · exact ((measurable_tagSq b E j k).pow_const 2).ennreal_ofReal

theorem crude_sq_iter {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {k : ℕ} (hW : 1 ≤ W) {CN : ℝ} (hCN : 0 ≤ CN)
    (hN : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * (2 * 2) : ℕ) : ℝ))
        (freshLaw W b) ≤ ENNReal.ofReal CN) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (tagSq b E W (k + 1 + m) k ω ^ 2) ∂growthPathLaw W b ≤
      ENNReal.ofReal (CN ^ (2 * (2 * 2))) ^ m *
        ∫⁻ ω, ENNReal.ofReal (tagSq b E W (k + 1) k ω ^ 2) ∂growthPathLaw W b := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show k + 1 + (m + 1) = k + 1 + m + 1 by omega]
    refine (crude_sq_step hb0 hb hE1 hE2 (k := k) (j := k + 1 + m) hW (by omega) hCN hN).trans ?_
    set c := ENNReal.ofReal (CN ^ (2 * (2 * 2)))
    rw [pow_succ c m, mul_comm (c ^ m), mul_assoc]
    exact mul_le_mul_of_nonneg_left ih zero_le

/-- **Removing the stops** for the square, by Hölder. -/
theorem sq_stop_removal (b E : ℝ) {k : ℕ} {K : ℝ} (hK : 0 ≤ K) (d : ℝ) (j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (tagSq b E W j k ω) ∂growthPathLaw W b ≤
      ∫⁻ ω, (stopEv b E W k d j).indicator (sqWeight b E W k K j) ω ∂growthPathLaw W b +
        (∫⁻ ω, ENNReal.ofReal (tagSq b E W j k ω ^ 2) ∂growthPathLaw W b) ^ (1 / 2 : ℝ) *
          growthPathLaw W b (stopEv b E W k d j)ᶜ ^ (1 / 2 : ℝ) := by
  set μ := growthPathLaw W b
  set A := stopEv b E W k d j
  set f : GrowthPath W → ℝ≥0∞ := fun ω => ENNReal.ofReal (tagSq b E W j k ω)
  have hA := measurableSet_stopEv (W := W) b E k d j
  have hmf : Measurable f := (measurable_tagSq b E j k).ennreal_ofReal
  have htm : ∀ ω, 0 ≤ tagSq b E W j k ω := tagSq_nonneg b E j k
  have hsplit : (fun ω => f ω) = fun ω => A.indicator f ω + Aᶜ.indicator f ω := by
    funext ω; rw [Set.indicator_self_add_compl_apply]
  rw [show (∫⁻ ω, ENNReal.ofReal (tagSq b E W j k ω) ∂μ) = ∫⁻ ω, f ω ∂μ from rfl, hsplit,
    lintegral_add_left (hmf.indicator hA)]
  have hle : ∀ ω, f ω ≤ sqWeight b E W k K j ω := by
    intro ω
    refine ENNReal.ofReal_le_ofReal ?_
    have hδ : 0 ≤ pathDelta b E W j ω := norm_nonneg _
    nlinarith [mul_nonneg hK hδ, htm ω]
  refine add_le_add (lintegral_mono fun ω => Set.indicator_le_indicator (hle ω)) ?_
  · have hg : Measurable (Aᶜ.indicator fun _ : GrowthPath W => (1 : ℝ≥0∞)) :=
      measurable_const.indicator hA.compl
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      hg.aemeasurable hmf.aemeasurable
    have e1 : (fun ω => Aᶜ.indicator f ω) = (Aᶜ.indicator fun _ => (1 : ℝ≥0∞)) * f := by
      funext ω; by_cases h : ω ∈ Aᶜ <;> simp [Set.indicator, h]
    have e2 : ∫⁻ ω, (Aᶜ.indicator fun _ => (1 : ℝ≥0∞)) ω ^ (2 : ℝ) ∂μ = μ Aᶜ := by
      rw [← lintegral_indicator_one hA.compl]
      congr 1; funext ω
      by_cases h : ω ∈ Aᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, ENNReal.one_rpow, Pi.one_apply]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
          ENNReal.zero_rpow_of_pos (by norm_num)]
    have e3 : ∫⁻ ω, f ω ^ (2 : ℝ) ∂μ = ∫⁻ ω, ENNReal.ofReal (tagSq b E W j k ω ^ 2) ∂μ := by
      congr 1; funext ω
      simp only [f]
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (htm ω)]
    rw [e1]
    refine hH.trans (le_of_eq ?_)
    rw [e2, e3, mul_comm]

end BlockBand.SourceProcess.FullSource
