module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Weak convergence with uniformly `L²`-bounded continuous functionals

`tendsto_integral_of_sq_bound`: if `∫ Φ(X_n) dμ_n → ∫ Φ(Y) dP` for every bounded continuous `Φ`
(the fdd convergence of `IsPowerTraceLimit`), and `G` is continuous with
`∫⁻ |G(X_n)|² dμ_n ≤ C` eventually, then `∫⁻ |G(Y)|² dP ≤ C` and
`∫ G(X_n) dμ_n → ∫ G(Y) dP` (truncation `max(-M, min(M, G))`, `|G - G_M| ≤ G²/M`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open scoped ENNReal

variable {S : Type*} [TopologicalSpace S]

/-- The clamp `max(-M, min(M, G))` of a continuous `G` as a bounded continuous function. -/
def clampBCF (G : S → ℝ) (hG : Continuous G) (M : ℝ) : BoundedContinuousFunction S ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => max (-M) (min M (G x)), by fun_prop⟩ (2 * |M|)
    fun x y => by
      have h : ∀ z : S, |max (-M) (min M (G z))| ≤ |M| := fun z =>
        abs_le.mpr ⟨(neg_le_neg (le_abs_self M)).trans (le_max_left _ _),
          max_le (neg_le_abs M) ((min_le_left _ _).trans (le_abs_self M))⟩
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have := abs_sub (max (-M) (min M (G x))) (max (-M) (min M (G y)))
      linarith [h x, h y]

theorem clampBCF_apply (G : S → ℝ) (hG : Continuous G) (M : ℝ) (x : S) :
    clampBCF G hG M x = max (-M) (min M (G x)) := rfl

/-- `|g - clamp_M g| ≤ g²/M`. -/
theorem abs_sub_clamp_le {M : ℝ} (hM : 0 < M) (g : ℝ) :
    |g - max (-M) (min M g)| ≤ g ^ 2 / M := by
  rw [le_div_iff₀ hM]
  rcases le_or_gt g M with h1 | h1
  · rcases le_or_gt (-M) g with h2 | h2
    · rw [min_eq_right h1, max_eq_right h2, sub_self, abs_zero, zero_mul]; positivity
    · rw [min_eq_right h1, max_eq_left (by linarith), abs_of_neg (by linarith)]; nlinarith
  · rw [min_eq_left h1.le, max_eq_right (by linarith), abs_of_pos (by linarith)]; nlinarith

theorem enorm_sq_eq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An `L²` bound in `lintegral` form gives integrability of `f` and `f²`, and `∫ f² ≤ C`. -/
theorem of_lintegral_sq_le {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (h : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => f ω ^ 2) μ ∧ Integrable f μ ∧ ∫ ω, f ω ^ 2 ∂μ ≤ C ∧ 0 ≤ C ∨
      (Integrable (fun ω => f ω ^ 2) μ ∧ Integrable f μ ∧ ∫ ω, f ω ^ 2 ∂μ ≤ max C 0) := by
  right
  have hsq : Integrable (fun ω => f ω ^ 2) μ := by
    refine ⟨hf.pow 2, ?_⟩
    simp only [HasFiniteIntegral, enorm_pow]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  refine ⟨hsq, ?_, ?_⟩
  · exact (memLp_two_iff_integrable_sq hf).mpr hsq |>.integrable one_le_two
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
      (hf.pow 2)]
    refine ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) ?_
    refine le_trans (le_of_eq ?_) (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    exact lintegral_congr fun ω => (enorm_sq_eq (f ω)).symm

/-- Simplified form of `of_lintegral_sq_le`. -/
theorem sq_integrable_of {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (h : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => f ω ^ 2) μ ∧ Integrable f μ ∧ ∫ ω, f ω ^ 2 ∂μ ≤ max C 0 := by
  rcases of_lintegral_sq_le hf h with ⟨h1, h2, h3, h4⟩ | h'
  · exact ⟨h1, h2, h3.trans (le_max_left _ _)⟩
  · exact h'

theorem ofReal_max_zero (C : ℝ) : ENNReal.ofReal (max C 0) = ENNReal.ofReal C := by
  rcases le_total C 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

variable [MeasurableSpace S] [OpensMeasurableSpace S]

/-- Integrability of a bounded continuous function of a random variable. -/
theorem integrable_bcf_comp {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → S} (hZ : Measurable Z)
    (Φ : BoundedContinuousFunction S ℝ) : Integrable (fun ω => Φ (Z ω)) μ :=
  (memLp_top_of_bound (Φ.continuous.measurable.comp hZ).aestronglyMeasurable ‖Φ‖
    (Eventually.of_forall fun ω => Φ.norm_coe_le_norm (Z ω))).integrable le_top

/-- The truncation error `|∫ G(Z) - ∫ G_M(Z)| ≤ C/M`. -/
theorem abs_integral_sub_clamp_le {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → S}
    (hZ : Measurable Z) {G : S → ℝ} (hG : Continuous G) {M : ℝ} (hM : 0 < M) {C : ℝ}
    (h : ∫⁻ ω, ‖G (Z ω)‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal C) :
    |∫ ω, G (Z ω) ∂μ - ∫ ω, clampBCF G hG M (Z ω) ∂μ| ≤ max C 0 / M := by
  obtain ⟨hsq, hint, hle⟩ := sq_integrable_of (f := fun ω => G (Z ω))
    (hG.measurable.comp hZ).aestronglyMeasurable h
  have hcl := integrable_bcf_comp (μ := μ) hZ (clampBCF G hG M)
  rw [← integral_sub hint hcl]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ω, |G (Z ω) - clampBCF G hG M (Z ω)| ∂μ ≤ ∫ ω, G (Z ω) ^ 2 / M ∂μ := by
        refine integral_mono (hint.sub hcl).abs (hsq.div_const M) fun ω => ?_
        rw [clampBCF_apply]; exact abs_sub_clamp_le hM _
    _ = (∫ ω, G (Z ω) ^ 2 ∂μ) / M := integral_div M _
    _ ≤ max C 0 / M := div_le_div_of_nonneg_right hle hM.le

theorem iSup_ofReal_min {x : ℝ} (hx : 0 ≤ x) :
    (⨆ N : ℕ, ENNReal.ofReal (max (-(N : ℝ)) (min (N : ℝ) x))) = ENNReal.ofReal x := by
  refine le_antisymm (iSup_le fun N => ENNReal.ofReal_le_ofReal ?_) ?_
  · exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) N]) (min_le_right _ _)
  · refine le_iSup_of_le ⌈x⌉₊ (ENNReal.ofReal_le_ofReal ?_)
    rw [min_eq_right (Nat.le_ceil x)]; exact le_max_right _ _

/-- **Weak convergence with a uniformly `L²`-bounded continuous functional.** -/
theorem tendsto_integral_of_sq_bound {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    {μ : ∀ n, Measure (Ωn n)} [∀ n, IsProbabilityMeasure (μ n)] {X : ∀ n, Ωn n → S}
    (hX : ∀ n, Measurable (X n)) {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → S}
    (hY : Measurable Y)
    (hconv : ∀ Φ : BoundedContinuousFunction S ℝ,
      Tendsto (fun n => ∫ ω, Φ (X n ω) ∂μ n) atTop (𝓝 (∫ ω, Φ (Y ω) ∂P)))
    {G : S → ℝ} (hG : Continuous G) {C : ℝ}
    (hC : ∀ᶠ n in atTop, ∫⁻ ω, ‖G (X n ω)‖ₑ ^ 2 ∂μ n ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ‖G (Y ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C ∧
      Tendsto (fun n => ∫ ω, G (X n ω) ∂μ n) atTop (𝓝 (∫ ω, G (Y ω) ∂P)) := by
  have hG2 : Continuous fun x => G x ^ 2 := hG.pow 2
  -- the limit `L²` bound
  have hlim : ∫⁻ ω, ‖G (Y ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C := by
    have hmeas : ∀ N : ℕ, Measurable fun ω =>
        ENNReal.ofReal (clampBCF (fun x => G x ^ 2) hG2 N (Y ω)) := fun N =>
      ENNReal.measurable_ofReal.comp ((clampBCF _ hG2 N).continuous.measurable.comp hY)
    have hmono : Monotone fun (N : ℕ) ω =>
        ENNReal.ofReal (clampBCF (fun x => G x ^ 2) hG2 N (Y ω)) := by
      intro N N' hNN ω
      simp only [clampBCF_apply]
      have : (N : ℝ) ≤ N' := by exact_mod_cast hNN
      have h0 : ∀ K : ℕ, max (-(K : ℝ)) (min (K : ℝ) (G (Y ω) ^ 2)) = min (K : ℝ) (G (Y ω) ^ 2) :=
        fun K => max_eq_right (by
          have := le_min (Nat.cast_nonneg (α := ℝ) K) (sq_nonneg (G (Y ω)))
          linarith [Nat.cast_nonneg (α := ℝ) K])
      rw [h0, h0]
      exact ENNReal.ofReal_le_ofReal (min_le_min this le_rfl)
    calc ∫⁻ ω, ‖G (Y ω)‖ₑ ^ 2 ∂P
        = ∫⁻ ω, ⨆ N : ℕ, ENNReal.ofReal (clampBCF (fun x => G x ^ 2) hG2 N (Y ω)) ∂P := by
          refine lintegral_congr fun ω => ?_
          simp only [clampBCF_apply]
          rw [iSup_ofReal_min (sq_nonneg _), enorm_sq_eq]
      _ = ⨆ N : ℕ, ∫⁻ ω, ENNReal.ofReal (clampBCF (fun x => G x ^ 2) hG2 N (Y ω)) ∂P :=
          lintegral_iSup hmeas hmono
      _ ≤ ENNReal.ofReal C := by
          refine iSup_le fun N => ?_
          have hnn : ∀ ω, 0 ≤ clampBCF (fun x => G x ^ 2) hG2 N (Y ω) := fun ω => by
            simp only [clampBCF_apply]
            exact le_max_of_le_right (le_min (Nat.cast_nonneg _) (sq_nonneg _))
          rw [← ofReal_integral_eq_lintegral_ofReal (integrable_bcf_comp hY _)
            (Eventually.of_forall hnn), ← ofReal_max_zero C]
          refine ENNReal.ofReal_le_ofReal (le_of_tendsto (hconv _) ?_)
          filter_upwards [hC] with n hn
          obtain ⟨hsq, -, hle⟩ :=
            sq_integrable_of (f := fun ω => G (X n ω))
              (hG.measurable.comp (hX n)).aestronglyMeasurable hn
          refine le_trans (integral_mono (integrable_bcf_comp (hX n) _) hsq fun ω => ?_) hle
          simp only [clampBCF_apply]
          exact max_le (by linarith [sq_nonneg (G (X n ω)), Nat.cast_nonneg (α := ℝ) N])
            (min_le_right _ _)
  refine ⟨hlim, Metric.tendsto_atTop.mpr fun δ hδ => ?_⟩
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  set M := 4 * (C' + 1) / δ
  have hM : 0 < M := by positivity
  have hcM : C' / M ≤ δ / 4 := by
    rw [div_le_iff₀ hM]; simp only [M]; field_simp; nlinarith
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hconv (clampBCF G hG M)) (δ / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hC
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := abs_integral_sub_clamp_le (hX n) hG hM (hN₂ n (le_trans (le_max_right _ _) hn))
  have h3 := abs_integral_sub_clamp_le hY hG hM hlim
  rw [Real.dist_eq] at h1 ⊢
  calc |∫ ω, G (X n ω) ∂μ n - ∫ ω, G (Y ω) ∂P|
      ≤ |∫ ω, G (X n ω) ∂μ n - ∫ ω, clampBCF G hG M (X n ω) ∂μ n| +
        |∫ ω, clampBCF G hG M (X n ω) ∂μ n - ∫ ω, clampBCF G hG M (Y ω) ∂P| +
        |∫ ω, G (Y ω) ∂P - ∫ ω, clampBCF G hG M (Y ω) ∂P| := by
        have := abs_sub_le (∫ ω, G (X n ω) ∂μ n) (∫ ω, clampBCF G hG M (X n ω) ∂μ n)
          (∫ ω, clampBCF G hG M (Y ω) ∂P)
        have := abs_sub_le (∫ ω, G (X n ω) ∂μ n) (∫ ω, clampBCF G hG M (Y ω) ∂P)
          (∫ ω, G (Y ω) ∂P)
        rw [abs_sub_comm (∫ ω, clampBCF G hG M (Y ω) ∂P)] at this
        linarith
    _ < δ := by linarith

end BlockBand.Transmission.Generator
