module

public import BlockBand.SourceProcess.FullSourceGenerator.GenPath

/-!
# Second-moment bounds for the tested increment

* `lintegral_sq_incr_le`: `E|X₁ - X₀ - Σ_{j∈S} s g_j|² ≤ 3E|X₁|² + 3E|X₀|² + 3|s|²#S Σ E|g_j|²`;
* `lintegral_sq_stopInc_le`: for `R = Re Φ`, `I = Im Φ` along the path (`rePart`, `imPart`),
  `E|1_A ΔΦ|² ≤ E‖carreErr R‖ + E‖carreErr I‖ + W⁻¹(E|Γ(R)| + E|Γ(I)|)` (`K`-free).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory MvPolynomial Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

theorem lintegral_sq_incr_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {X₁ X₀ : Ω → ℂ} {g : ℕ → Ω → ℂ} (S : Finset ℕ) (s : ℂ) (h₁ : AEMeasurable X₁ μ)
    (h₀ : AEMeasurable X₀ μ) (hg : ∀ j, AEMeasurable (g j) μ) :
    ∫⁻ ω, ‖X₁ ω - X₀ ω - ∑ j ∈ S, s * g j ω‖ₑ ^ 2 ∂μ ≤
      3 * ∫⁻ ω, ‖X₁ ω‖ₑ ^ 2 ∂μ + 3 * ∫⁻ ω, ‖X₀ ω‖ₑ ^ 2 ∂μ +
        3 * ENNReal.ofReal (‖s‖ ^ 2 * #S) * ∑ j ∈ S, ∫⁻ ω, ‖g j ω‖ₑ ^ 2 ∂μ := by
  have hpt : ∀ ω, ‖X₁ ω - X₀ ω - ∑ j ∈ S, s * g j ω‖ₑ ^ 2 ≤
      3 * ‖X₁ ω‖ₑ ^ 2 + 3 * ‖X₀ ω‖ₑ ^ 2 +
        3 * ENNReal.ofReal (‖s‖ ^ 2 * #S) * ∑ j ∈ S, ‖g j ω‖ₑ ^ 2 := by
    intro ω
    have hsum : ‖∑ j ∈ S, s * g j ω‖ ^ 2 ≤ ‖s‖ ^ 2 * #S * ∑ j ∈ S, ‖g j ω‖ ^ 2 := by
      have h1 : ‖∑ j ∈ S, s * g j ω‖ ≤ ∑ j ∈ S, ‖s‖ * ‖g j ω‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
      have h2 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun j => ‖s‖ * ‖g j ω‖)
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      simp only [mul_pow, ← Finset.mul_sum] at h2
      have h4 : ∑ j ∈ S, ‖s‖ * ‖g j ω‖ = ‖s‖ * ∑ j ∈ S, ‖g j ω‖ := (Finset.mul_sum _ _ _).symm
      rw [h4, mul_pow] at h3
      linarith [h2, h3]
    have htri : ‖X₁ ω - X₀ ω - ∑ j ∈ S, s * g j ω‖ ≤
        ‖X₁ ω‖ + ‖X₀ ω‖ + ‖∑ j ∈ S, s * g j ω‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    have hr : ‖X₁ ω - X₀ ω - ∑ j ∈ S, s * g j ω‖ ^ 2 ≤
        3 * ‖X₁ ω‖ ^ 2 + 3 * ‖X₀ ω‖ ^ 2 + 3 * (‖s‖ ^ 2 * #S) * ∑ j ∈ S, ‖g j ω‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [sq_nonneg (‖X₁ ω‖ - ‖X₀ ω‖), sq_nonneg (‖X₁ ω‖ - ‖∑ j ∈ S, s * g j ω‖),
        sq_nonneg (‖X₀ ω‖ - ‖∑ j ∈ S, s * g j ω‖)]
    rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, enorm_sq_eq_ofReal]
    simp_rw [enorm_sq_eq_ofReal]
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, ← ENNReal.ofReal_ofNat 3,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hr
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  have m1 : AEMeasurable (fun ω => ‖X₁ ω‖ₑ ^ 2) μ := h₁.enorm.pow_const 2
  have m0' : AEMeasurable (fun ω => ‖X₀ ω‖ₑ ^ 2) μ := h₀.enorm.pow_const 2
  have mg : ∀ j, AEMeasurable (fun ω => ‖g j ω‖ₑ ^ 2) μ := fun j => (hg j).enorm.pow_const 2
  rw [lintegral_add_right' _ ((Finset.aemeasurable_fun_sum _ fun j _ => mg j).const_mul _),
    lintegral_add_right' _ (m0'.const_mul _), lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
    lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top),
    lintegral_finsetSum' _ fun j _ => mg j]

variable {W nT nI : ℕ}

/-- **The `K`-free second moment of a stopped increment** through `EarlySummed`'s second clause
for `Re Φ` and `Im Φ`. -/
theorem lintegral_sq_stopInc_le {b E : ℝ} {k : Fin nT → ℕ} {q : Fin nI → ℝ → ℝ}
    (hq : IsIntervalTests q) {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ) (A : Set (GrowthPath W))
    {j : ℕ} (hA : MeasurableSet[growthSigma W j] A)
    (hX : MemLp (fun ω => polyValue b E k q W (j + 1) ω Φ - polyValue b E k q W j ω Φ) 2
      (growthPathLaw W b)) :
    let μ := growthPathLaw W b
    let F : TracePoly nT nI → ℕ → GrowthPath W → ℂ := fun Ψ i ω => polyValue b E k q W i ω Ψ
    let cE : TracePoly nT nI → GrowthPath W → ℂ := fun Ψ => A.indicator (fun ω =>
      μ[A.indicator (fun ω => (F Ψ (j + 1) ω - F Ψ j ω) ^ 2) | growthSigma W j] ω -
        (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Ψ))
    ∫⁻ ω, ‖A.indicator (fun ω => F Φ (j + 1) ω - F Φ j ω) ω‖ₑ ^ 2 ∂μ ≤
      ∫⁻ ω, ‖cE (rePart Φ) ω‖ₑ ∂μ + ∫⁻ ω, ‖cE (imPart Φ) ω‖ₑ ∂μ +
        ENNReal.ofReal (W : ℝ)⁻¹ * (∫⁻ ω, ‖polyValue b E k q W j ω (wordCarre b E (rePart Φ))‖ₑ ∂μ +
          ∫⁻ ω, ‖polyValue b E k q W j ω (wordCarre b E (imPart Φ))‖ₑ ∂μ) := by
  intro μ F cE
  have hle := growthSigma_le' W j
  have hAm : MeasurableSet A := hle _ hA
  have hWc : Complex.ofReal ((W : ℝ)⁻¹) = (W : ℂ)⁻¹ := by push_cast; rfl
  have hRe : ∀ ω, F (rePart Φ) (j + 1) ω - F (rePart Φ) j ω =
      (((F Φ (j + 1) ω - F Φ j ω).re : ℝ) : ℂ) := fun ω => by
    simp only [F, polyValue_rePart b E k q hq _ ω hΦ, Complex.sub_re, Complex.ofReal_sub]
  have hIm : ∀ ω, F (imPart Φ) (j + 1) ω - F (imPart Φ) j ω =
      (((F Φ (j + 1) ω - F Φ j ω).im : ℝ) : ℂ) := fun ω => by
    simp only [F, polyValue_imPart b E k q hq _ ω hΦ, Complex.sub_im, Complex.ofReal_sub]
  have hmeasP : ∀ Ψ : TracePoly nT nI,
      StronglyMeasurable fun ω => polyValue b E k q W j ω (wordCarre b E Ψ) := fun Ψ =>
    ((measurable_polyValue_past b E k q le_rfl _).mono hle le_rfl).stronglyMeasurable
  have hL : ∀ (P : (GrowthPath W → ℂ)), (∀ ω, ‖P ω‖ ≤ ‖F Φ (j + 1) ω - F Φ j ω‖) →
      AEStronglyMeasurable P μ → MemLp (A.indicator P) 2 μ := fun P hP hPm =>
    (hX.of_le hPm (Filter.Eventually.of_forall hP)).indicator hAm.nullMeasurableSet
  have hR := lintegral_sq_le_carre (μ := μ) hle hA (Δ := fun ω => F (rePart Φ) (j + 1) ω -
      F (rePart Φ) j ω) (fun ω => by rw [hRe ω, Complex.ofReal_re])
    (hL _ (fun ω => by rw [hRe ω, Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
      (((measurable_polyValue_past b E k q le_rfl _).sub (measurable_polyValue_past b E k q
        (Nat.le_succ j) _)).mono (growthSigma_le' W (j + 1)) le_rfl).aestronglyMeasurable)
    (hmeasP (rePart Φ)) (inv_nonneg.mpr (Nat.cast_nonneg W))
  have hI := lintegral_sq_le_carre (μ := μ) hle hA (Δ := fun ω => F (imPart Φ) (j + 1) ω -
      F (imPart Φ) j ω) (fun ω => by rw [hIm ω, Complex.ofReal_re])
    (hL _ (fun ω => by rw [hIm ω, Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)
      (((measurable_polyValue_past b E k q le_rfl _).sub (measurable_polyValue_past b E k q
        (Nat.le_succ j) _)).mono (growthSigma_le' W (j + 1)) le_rfl).aestronglyMeasurable)
    (hmeasP (imPart Φ)) (inv_nonneg.mpr (Nat.cast_nonneg W))
  rw [hWc] at hR hI
  have hsplit : ∫⁻ ω, ‖A.indicator (fun ω => F Φ (j + 1) ω - F Φ j ω) ω‖ₑ ^ 2 ∂μ =
      ∫⁻ ω, ‖A.indicator (fun ω => F (rePart Φ) (j + 1) ω - F (rePart Φ) j ω) ω‖ₑ ^ 2 ∂μ +
      ∫⁻ ω, ‖A.indicator (fun ω => F (imPart Φ) (j + 1) ω - F (imPart Φ) j ω) ω‖ₑ ^ 2 ∂μ := by
    simp_rw [hRe, hIm]
    rw [← lintegral_add_left]
    · exact lintegral_congr fun ω => enorm_sq_indicator_eq A _ ω
    · refine ((Measurable.indicator ?_ hAm).enorm.pow_const 2)
      exact Complex.measurable_ofReal.comp (Complex.measurable_re.comp
        (((measurable_polyValue_past b E k q le_rfl _).sub (measurable_polyValue_past b E k q
          (Nat.le_succ j) _)).mono (growthSigma_le' W (j + 1)) le_rfl))
  rw [hsplit, mul_add]
  calc _ ≤ (∫⁻ ω, ‖cE (rePart Φ) ω‖ₑ ∂μ + ENNReal.ofReal (W : ℝ)⁻¹ *
          ∫⁻ ω, ‖polyValue b E k q W j ω (wordCarre b E (rePart Φ))‖ₑ ∂μ) +
        (∫⁻ ω, ‖cE (imPart Φ) ω‖ₑ ∂μ + ENNReal.ofReal (W : ℝ)⁻¹ *
          ∫⁻ ω, ‖polyValue b E k q W j ω (wordCarre b E (imPart Φ))‖ₑ ∂μ) := add_le_add hR hI
    _ = _ := by ring

end BlockBand.SourceProcess.FullSourceGenerator
