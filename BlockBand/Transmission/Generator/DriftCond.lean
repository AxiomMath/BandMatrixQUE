module

public import BlockBand.Transmission.Generator.Discrete
public import BlockBand.Transmission.Generator.RefinedMean
public import BlockBand.Transmission.SourceMixing.MassPath
public import BlockBand.Transmission.SourceMixing.Conductance

/-!
# The one-step conditional mean of the conductance

* `condExp_fresh`: for bounded jointly measurable `Ψ`,
  `E[Ψ(X_j, fresh_j) ∣ 𝓕_j] = ∫ Ψ(X_j, y) dfresh(y)` a.s. (the fresh layer is independent of
  `𝓕_j`, and `X_j` is a function of the past coordinates: `growthPathLaw_map_past_fresh`).
* `condExp_qc_succ`: `E[qc(X_{j+1}) ∣ 𝓕_j] = m(X_j)` a.s., `m(X) = ∫ qc(X₊) dfresh`, `j ≥ 1`.
* `pathPower_one_eq`: `Tr T_r = 4η q(X_r)`.
* `driftError_one_ae`: `driftError_r (k = 1) = 4η(m(X_r) - q(X_r)) + D₀(E)(4ηq(X_r))²/(2W)` a.s.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing
open scoped ENNReal

variable {W : ℕ}

/-- **Conditional expectation over one fresh layer.** -/
theorem condExp_fresh (b E : ℝ)
    {Ψ : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort → ℝ} (hΨ : Measurable Ψ)
    {M : ℝ} (hΨM : ∀ x, |Ψ x| ≤ M) (j : ℕ) :
    (growthPathLaw W b)[fun ω => Ψ (pathX b E W j ω, freshSample W j ω) | growthSigma W j] =ᵐ[
      growthPathLaw W b] fun ω => ∫ y, Ψ (pathX b E W j ω, y) ∂freshLaw W b := by
  set μ := growthPathLaw W b
  set S := stepInput b E (fun _ => 0) W j
  have hS : Measurable S := measurable_stepInput b E _ j
  have hXS : ∀ ω, pathX b E W j ω = S (pastCoords W j ω) := fun ω =>
    (PathJet.stepInput_zero b E j ω).symm
  set G : Matrix (Fin W) (Fin W) ℂ → ℝ := fun X => ∫ y, Ψ (X, y) ∂freshLaw W b
  have hG : Measurable G := (hΨ.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  have hGM : ∀ X, |G X| ≤ M := fun X => by
    have := norm_integral_le_of_norm_le_const (μ := freshLaw W b) (f := fun y => Ψ (X, y))
      (C := M) (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hΨM _)
    simpa [Real.norm_eq_abs, Measure.real, measure_univ] using this
  have hm : growthSigma W j ≤ (inferInstance : MeasurableSpace (GrowthPath W)) :=
    growthSigma_le W j
  have hT := (measurable_pastCoords W j).prodMk (measurable_freshSample W j)
  have hXm : Measurable (pathX b E W j) := PathJet.measurable_pathX b E j
  have hf : Integrable (fun ω => Ψ (pathX b E W j ω, freshSample W j ω)) μ :=
    Integrable.of_bound ((hΨ.comp (hXm.prodMk (measurable_freshSample W j))).aestronglyMeasurable)
      M (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hΨM _)
  have hgm : Measurable[growthSigma W j] fun ω => G (pathX b E W j ω) := by
    have : (fun ω => G (pathX b E W j ω)) = (G ∘ S) ∘ pastCoords W j := by
      funext ω; simp only [Function.comp, hXS]
    rw [this]
    exact (hG.comp hS).comp (comap_measurable (pastCoords W j))
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => ?_) (fun s hs _ => ?_)
    hgm.aestronglyMeasurable).symm
  · exact (Integrable.of_bound ((hG.comp hXm).aestronglyMeasurable) M
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hGM _)).integrableOn
  obtain ⟨B, hB, rfl⟩ := hs
  show ∫ x in pastCoords W j ⁻¹' B, G (pathX b E W j x) ∂μ =
    ∫ x in pastCoords W j ⁻¹' B, Ψ (pathX b E W j x, freshSample W j x) ∂μ
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℝ :=
    fun x => B.indicator (fun _ => (1 : ℝ)) x.1 * Ψ (S x.1, x.2)
  have hΦ : Measurable Φ :=
    ((measurable_const.indicator hB).comp measurable_fst).mul
      (hΨ.comp ((hS.comp measurable_fst).prodMk measurable_snd))
  have hΦi : Integrable Φ ((pastLaw W j b).prod (freshLaw W b)) := by
    refine Integrable.of_bound hΦ.aestronglyMeasurable M (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hx : x.1 ∈ B
    · simp only [Set.indicator_of_mem hx, abs_one, one_mul]; exact hΨM _
    · simp only [Set.indicator_of_notMem hx, abs_zero, zero_mul]
      exact (abs_nonneg _).trans (hΨM (S x.1, x.2))
  have e1 : ∫ ω in pastCoords W j ⁻¹' B, Ψ (pathX b E W j ω, freshSample W j ω) ∂μ =
      ∫ x, Φ x ∂((pastLaw W j b).prod (freshLaw W b)) := by
    rw [← integral_indicator (measurable_pastCoords W j hB), ← growthPathLaw_map_past_fresh,
      integral_map hT.aemeasurable hΦ.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    by_cases hω : pastCoords W j ω ∈ B
    · simp [Φ, Set.indicator_of_mem hω, Set.indicator_of_mem (show ω ∈ pastCoords W j ⁻¹' B
        from hω), hXS]
    · simp [Φ, Set.indicator_of_notMem hω, Set.indicator_of_notMem (show ω ∉ pastCoords W j ⁻¹' B
        from hω)]
  have e2 : ∫ ω in pastCoords W j ⁻¹' B, G (pathX b E W j ω) ∂μ =
      ∫ p, B.indicator (fun _ => (1 : ℝ)) p * G (S p) ∂pastLaw W j b := by
    rw [← integral_indicator (measurable_pastCoords W j hB), ← growthPathLaw_map_pastCoords,
      integral_map (f := fun p => B.indicator (fun _ => (1 : ℝ)) p * G (S p))
        (measurable_pastCoords W j).aemeasurable
        (((measurable_const.indicator hB).mul (hG.comp hS)).aestronglyMeasurable)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    by_cases hω : pastCoords W j ω ∈ B
    · simp [Set.indicator_of_mem hω, Set.indicator_of_mem (show ω ∈ pastCoords W j ⁻¹' B
        from hω), hXS]
    · simp [Set.indicator_of_notMem hω, Set.indicator_of_notMem (show ω ∉ pastCoords W j ⁻¹' B
        from hω)]
  rw [e2, e1, integral_prod Φ hΦi]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [Φ, G]
  rw [integral_const_mul]

/-- **`E[qc(X_{j+1}) ∣ 𝓕_j] = m(X_j)`**, `m(X) = ∫ qc(X₊) dfresh`, for `j ≥ 1`. -/
theorem condExp_qc_succ {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (hW : 1 ≤ W)
    {j : ℕ} (hj : 1 ≤ j) :
    (growthPathLaw W b)[fun ω => qc b E (pathX b E W (j + 1) ω) | growthSigma W j] =ᵐ[
      growthPathLaw W b] fun ω => ∫ y, qc b E (freshSchur E (pathX b E W j ω) y) ∂freshLaw W b := by
  have hη := PassiveCovariance.etaZ_pos b E (by linarith) h1 h2
  have hΨ : Measurable fun x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      qc b E (freshSchur E x.1 x.2) := (measurable_qc b E).comp (measurable_freshSchur_prod E)
  have hΨM : ∀ x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort,
      |qc b E (freshSchur E x.1 x.2)| ≤ W / (4 * etaZ b E) := fun x => by
    rw [abs_of_nonneg (qc_nonneg b E _)]; exact qc_le (by linarith) h1 h2 _
  have hae : (fun ω => qc b E (pathX b E W (j + 1) ω)) =ᵐ[growthPathLaw W b]
      fun ω => qc b E (freshSchur E (pathX b E W j ω) (freshSample W j ω)) := by
    filter_upwards [ae_pathX_succ hb h1 h2 hW] with ω hω
    rw [hω j hj]
  exact (condExp_congr_ae hae).trans (condExp_fresh b E hΨ hΨM j)

/-- `Tr T_r = 4η q(X_r)`. -/
theorem pathPower_one_eq (b E : ℝ) (r : ℕ) (ω : GrowthPath W) :
    pathPower b E W 1 r ω = 4 * etaZ b E * passiveMass b E (pathX b E W r ω) := by
  rw [← pathConductance_eq_mass, pathPower, pow_one]; rfl

/-- `A₁(P) = -(D₀/2)P₁²`. -/
theorem transmissionDrift_one (D : ℝ) (P : ℕ → ℝ) : transmissionDrift D 1 P = -(D / 2) * P 1 ^ 2 := by
  simp [transmissionDrift]; ring

/-- **The drift error at `k = 1`**, a.s.: `4η(m(X_r) - qc(X_r)) + D₀(E)(4η qc(X_r))²/(2W)`. -/
theorem driftError_one_ae {b E E' : ℝ} (hb : b < 1 / 2) (h1 : -2 < E') (h2 : E' < 2)
    (hW : 1 ≤ W) {r : ℕ} (hr : 1 ≤ r) :
    driftError b E E' W 1 r =ᵐ[growthPathLaw W b] fun ω =>
      4 * etaZ b E' * ((∫ y, qc b E' (freshSchur E' (pathX b E' W r ω) y) ∂freshLaw W b) -
        qc b E' (pathX b E' W r ω)) +
        transportD0 b E * (4 * etaZ b E' * qc b E' (pathX b E' W r ω)) ^ 2 / (2 * W) := by
  set μ := growthPathLaw W b
  set η := etaZ b E'
  have hη := PassiveCovariance.etaZ_pos b E' (by linarith) h1 h2
  have hpas := mm_ae_passive (W := W) (b := b) (by linarith) h1 h2
  have hq : ∀ n, (fun ω => pathPower b E' W 1 n ω) =ᵐ[μ] fun ω => 4 * η * qc b E' (pathX b E' W n ω) := by
    intro n
    filter_upwards [hpas n] with ω hω
    rw [pathPower_one_eq, qc_eq hω]
  have hI : ∀ n, Integrable (fun ω => qc b E' (pathX b E' W n ω)) μ := fun n => by
    simpa using mm_integrable_qc (W := W) (b := b) (by linarith) h1 h2 1 n
  have hinc : powerIncrement b E' W 1 r =ᵐ[μ] fun ω =>
      4 * η * qc b E' (pathX b E' W (r + 1) ω) - 4 * η * qc b E' (pathX b E' W r ω) := by
    filter_upwards [hq (r + 1), hq r] with ω h1' h2'
    simp only [powerIncrement] at *; rw [h1', h2']
  have hmr : StronglyMeasurable[growthSigma W r] fun ω => 4 * η * qc b E' (pathX b E' W r ω) := by
    have hm := measurable_pathPower_adapted (W := W) b E' 1 r
    have e : (fun ω => 4 * η * qc b E' (pathX b E' W r ω)) = fun ω =>
        max (pathPower b E' W 1 r ω) 0 := by
      funext ω
      rw [pathPower_one_eq, qc, mul_max_of_nonneg _ _ (by positivity), mul_zero]
    rw [e]
    exact (hm.max measurable_const).stronglyMeasurable
  have hce : μ[powerIncrement b E' W 1 r | growthSigma W r] =ᵐ[μ] fun ω =>
      4 * η * (∫ y, qc b E' (freshSchur E' (pathX b E' W r ω) y) ∂freshLaw W b) -
        4 * η * qc b E' (pathX b E' W r ω) := by
    refine (condExp_congr_ae hinc).trans ?_
    refine (condExp_sub ((hI (r + 1)).const_mul _) ((hI r).const_mul _) _).trans ?_
    have hc1 : μ[fun ω => 4 * η * qc b E' (pathX b E' W (r + 1) ω) | growthSigma W r] =ᵐ[μ]
        fun ω => 4 * η * μ[fun ω => qc b E' (pathX b E' W (r + 1) ω) | growthSigma W r] ω := by
      have := condExp_smul (μ := μ) (4 * η) (fun ω => qc b E' (pathX b E' W (r + 1) ω))
        (growthSigma W r)
      have e : ((4 * η) • fun ω => qc b E' (pathX b E' W (r + 1) ω)) =
          fun ω => 4 * η * qc b E' (pathX b E' W (r + 1) ω) := by
        funext ω; simp [smul_eq_mul]
      rw [e] at this
      filter_upwards [this] with ω hω
      rw [hω, Pi.smul_apply, smul_eq_mul]
    have hc2 := condExp_qc_succ (W := W) (b := b) hb h1 h2 hW hr
    have hc3 : μ[fun ω => 4 * η * qc b E' (pathX b E' W r ω) | growthSigma W r] =
        fun ω => 4 * η * qc b E' (pathX b E' W r ω) :=
      condExp_of_stronglyMeasurable (growthSigma_le W r) hmr ((hI r).const_mul _)
    rw [hc3]
    filter_upwards [hc1, hc2] with ω e1 e2
    simp only [Pi.sub_apply]
    rw [e1, e2]
  filter_upwards [hce, hpas r] with ω e hω
  have : pathPowers b E' W r ω 1 = 4 * η * qc b E' (pathX b E' W r ω) := by
    simp only [pathPowers]; rw [pathPower_one_eq, qc_eq hω]
  show μ[powerIncrement b E' W 1 r | growthSigma W r] ω -
    transmissionDrift (transportD0 b E) 1 (pathPowers b E' W r ω) / W = _
  rw [e, transmissionDrift_one, this]
  have hW0 : (W : ℝ) ≠ 0 := by have : (0 : ℝ) < W := by exact_mod_cast hW
                               exact this.ne'
  field_simp
  ring

end BlockBand.Transmission.Generator
