module

public import BlockBand.Transmission.LawFractional.MassLimit
public import BlockBand.Transmission.LawFractional.Main

/-!
# `expDecay`: reduction to the exponential decay of the limit mass

* `integral_interp`: at finite `W`, `E g ≤ A` and `E Tr T^{q/2} ≤ B` give `E Tr T^q ≤ A^θB^{1-θ}`,
  with `θ = q/(2-q)` (`fracTrace_interp`).
* `limit_mass_le`: from `LimitMassDecay`'s lintegral bound to `E massFn(μ t) ≤ max(C,0)e^{-ct}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFractional

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.FractionalBulk
open scoped ENNReal

/-- **Every homogeneous critical limit has exponentially decaying mean
mass** `E μ(t)[0,1] ≤ Ce^{-ct}`, `t ≥ 2`. The constants may depend on the limit. -/
def LimitMassDecay : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
      ∃ C c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
        ∫⁻ ω, (μ t ω : Measure unitInterval) Set.univ ∂P ≤ ENNReal.ofReal (C * Real.exp (-(c * t)))

/-- **A homogeneous critical limit exists** (the `κ ≡ 0` case of the `law` field). -/
def HomogeneousLimitExists : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ

theorem isAbsorptionProfile_zero : IsAbsorptionProfile (fun _ => 0) :=
  ⟨continuous_const, fun _ => le_rfl, 0, fun _ => le_rfl⟩

/-- The `law` field type gives `HomogeneousLimitExists`. -/
theorem homogeneousLimitExists_of_law
    (hL : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
          (μ : ℝ → Ω → FiniteMeasure unitInterval),
          IsTransmissionLimit b E κ P μ ∧
          ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
            HasDualDeletionProcess (transportD0 b E) x y ∧
            DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P)) :
    HomogeneousLimitExists := fun b hb0 hb E h1 h2 => by
  obtain ⟨Ω, m, P, μ, h, -⟩ := hL b hb0 hb E h1 h2 _ isAbsorptionProfile_zero
  exact ⟨Ω, m, P, μ, h⟩

/-- **Finite-`W` interpolation in expectation.** -/
theorem integral_interp {W : ℕ} {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (r : ℕ)
    (hg : ∫ ω, pathConductance b E W r ω ∂growthPathLaw W b ≤ A)
    (hp : ∫ ω, fracTrace (q / 2) (pathTransmission b E (fun _ => 0) W r ω) ∂growthPathLaw W b ≤ B) :
    ∫ ω, fracTrace q (pathTransmission b E (fun _ => 0) W r ω) ∂growthPathLaw W b ≤
      A ^ interpExp q * B ^ (1 - interpExp q) := by
  obtain ⟨hθ0, hθ1⟩ := interpExp_mem hq0 hq1
  set θ := interpExp q
  set μ := growthPathLaw W b
  have hiq := integrable_pathFrac (W := W) hq0 hq1 hb h1 h2 r
  have hip := integrable_pathFrac (W := W) (p := q / 2) (by positivity) (by linarith) hb h1 h2 r
  have hig : Integrable (pathConductance b E W r) μ :=
    Integrable.of_bound (SourceMixing.measurable_pathConductance b E r).aestronglyMeasurable W (by
      filter_upwards [Generator.pathPower_mem (W := W) (b := b) (by linarith) h1 h2] with ω h
      obtain ⟨h0, h01, h3⟩ := h 1 r le_rfl
      rw [Real.norm_of_nonneg (h0.trans h01)]; exact h3)
  have hAB : 0 ≤ A ^ θ * B ^ (1 - θ) := by positivity
  have hR : Integrable (fun ω => A ^ θ * B ^ (1 - θ) * (θ * (pathConductance b E W r ω / A) +
      (1 - θ) * (fracTrace (q / 2) (pathTransmission b E (fun _ => 0) W r ω) / B))) μ :=
    (((hig.div_const A).const_mul θ).add ((hip.div_const B).const_mul (1 - θ))).const_mul _
  have hle := integral_mono_ae hiq hR (by
    filter_upwards [SourceMixing.mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r] with ω hω
    exact fracTrace_interp (Generator.passiveTransmission_posSemidef (by linarith) h1 h2 hω)
      hq0 hq1 hA hB)
  refine hle.trans ?_
  rw [integral_const_mul, integral_add ((hig.div_const A).const_mul θ)
    ((hip.div_const B).const_mul (1 - θ)), integral_const_mul, integral_const_mul,
    integral_div, integral_div]
  have e1 : (∫ ω, pathConductance b E W r ω ∂μ) / A ≤ 1 := by rw [div_le_one hA]; exact hg
  have e2 : (∫ ω, fracTrace (q / 2) (pathTransmission b E (fun _ => 0) W r ω) ∂μ) / B ≤ 1 := by
    rw [div_le_one hB]; exact hp
  have : θ * ((∫ ω, pathConductance b E W r ω ∂μ) / A) +
      (1 - θ) * ((∫ ω, fracTrace (q / 2) (pathTransmission b E (fun _ => 0) W r ω) ∂μ) / B) ≤ 1 := by
    nlinarith
  calc A ^ θ * B ^ (1 - θ) * _ ≤ A ^ θ * B ^ (1 - θ) * 1 := mul_le_mul_of_nonneg_left this hAB
    _ = _ := mul_one _

/-- The limit bound in real form. -/
theorem limit_mass_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} {t : ℝ} (hm : Measurable (μ t)) {D : ℝ}
    (h : ∫⁻ ω, (μ t ω : Measure unitInterval) Set.univ ∂P ≤ ENNReal.ofReal D) :
    ∫ ω, massFn (μ t ω) ∂P ≤ max D 0 := by
  have e : ∀ ω, massFn (μ t ω) = (μ t ω : Measure unitInterval).real Set.univ := fun ω => by
    simp [massFn]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => massFn_nonneg _)
    (measurable_massFn.comp hm).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (le_trans (le_of_eq ?_)
    (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  refine lintegral_congr fun ω => ?_
  rw [e, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **The field `TransmissionLawContract.expDecay`**, from the input hypotheses, a homogeneous
limit (`HomogeneousLimitExists`) and the limit decay `LimitMassDecay`.
-/
theorem expDecay_of (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hEx : HomogeneousLimitExists)
    (hDec : LimitMassDecay) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ q : ℝ, 0 < q → q < 1 → ∃ C c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
      limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
          (fracTrace q (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
          ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * Real.exp (-(c * t))) := by
  intro b hb0 hb E h1 h2 q hq0 hq1
  obtain ⟨Ω, mΩ, P, μ, hμ⟩ := hEx b hb0 hb E h1 h2
  obtain ⟨C, c, hc, hC⟩ := hDec b hb0 hb E h1 h2 Ω mΩ P μ hμ
  have hprob := hμ.prob
  have hκ : 0 < min (E + 2) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (E + 2) (2 - E)) :=
    ⟨by have := min_le_left (E + 2) (2 - E); linarith,
      by have := min_le_right (E + 2) (2 - E); linarith⟩
  obtain ⟨Cp, hCp0, hCp⟩ := fractional_bulk hMT hGA hLp hP b hb0 hb _ hκ (q / 2)
    (by positivity) (by linarith)
  obtain ⟨hθ0, hθ1⟩ := interpExp_mem hq0 hq1
  set θ := interpExp q
  set C' := max C 0 + 1
  have hC' : 0 < C' := by positivity
  refine ⟨C' ^ θ * (3 * (Cp + 1)) ^ (1 - θ), c * θ, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  set A := C' * Real.exp (-(c * t))
  set B := (Cp + 1) * (1 + t⁻¹)
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  -- the limit mass
  have hlimb : ∫ ω, massFn (μ t ω) ∂P < A := by
    have h := limit_mass_le (hμ.measurable t ht0) (hC t ht)
    have hmax : max (C * Real.exp (-(c * t))) 0 ≤ max C 0 * Real.exp (-(c * t)) :=
      max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
        (by positivity)
    have : max C 0 * Real.exp (-(c * t)) < A := by
      simp only [A, C']
      nlinarith [Real.exp_pos (-(c * t))]
    linarith
  have hT := mass_tendsto hMT hGA hLp hb0 hb hκ (e := fun _ => E) (W₁ := 0) (fun _ _ => hEb)
    (hμ.measurable t ht0) ht0 (fun Φ => hμ.fdd 1 (fun _ => t) (fun _ => ht0) Φ)
  have hev1 := hT.eventually (eventually_le_nhds hlimb)
  obtain ⟨W₀, hW₀⟩ := hCp t ht0
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hev1, eventually_ge_atTop W₀] with W hW1 hW2
  have hPp := hW₀ W hW2 E hEb
  have hip := integrable_pathFrac (W := W) (p := q / 2) (by positivity) (by linarith) hb h1 h2
    ⌊(W : ℝ) * t⌋₊
  rw [← ofReal_integral_eq_lintegral_ofReal hip
    (Eventually.of_forall fun ω => fracTrace_nonneg' _ _)] at hPp
  have hPB : ∫ ω, fracTrace (q / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω)
      ∂growthPathLaw W b ≤ B := by
    have h := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hPp
    have : Cp * (1 + t⁻¹) ≤ B := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hI := integral_interp (W := W) hb h1 h2 hq0 hq1 hA hB _ hW1 hPB
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_pathFrac (W := W) hq0 hq1 hb h1 h2 ⌊(W : ℝ) * t⌋₊)
    (Eventually.of_forall fun ω => fracTrace_nonneg' _ _)]
  refine ENNReal.ofReal_le_ofReal (hI.trans ?_)
  -- `A^θ B^{1-θ} ≤ C'^θ (3(Cp+1))^{1-θ} e^{-cθt}`
  have hAθ : A ^ θ = C' ^ θ * Real.exp (-(c * θ * t)) := by
    rw [Real.mul_rpow hC'.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2; ring
  have hB3 : B ≤ 3 * (Cp + 1) := by
    have : t⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
    have hCp1 : 0 ≤ Cp + 1 := by linarith
    simp only [B]; nlinarith
  have hBθ : B ^ (1 - θ) ≤ (3 * (Cp + 1)) ^ (1 - θ) :=
    Real.rpow_le_rpow hB.le hB3 (by linarith)
  rw [hAθ]
  have h0 : 0 ≤ C' ^ θ * Real.exp (-(c * θ * t)) := by positivity
  calc C' ^ θ * Real.exp (-(c * θ * t)) * B ^ (1 - θ) ≤
      C' ^ θ * Real.exp (-(c * θ * t)) * (3 * (Cp + 1)) ^ (1 - θ) :=
        mul_le_mul_of_nonneg_left hBθ h0
    _ = C' ^ θ * (3 * (Cp + 1)) ^ (1 - θ) * Real.exp (-(c * θ * t)) := by ring

end BlockBand.Transmission.LawFractional
