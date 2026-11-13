module

public import BlockBand.SourceProcess.SmallLeak.LeakStep
public import BlockBand.SourceProcess.SmallLeak.LeakMoments

/-!
# The mean of the one-step leakage bound

`leakBnd_mean_le`: if `‖δ_j‖₄ ≤ D`, `E g_j ≤ x`, `c_j ≤ c`, then
`E b_j ≤ K(C_m/η)(D√x + √x/W) + K((C_m²+C_f²)/η²)(D²√(Wx) + x/W) + cBx/(4η²)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer
open scoped ENNReal

variable {W : ℕ}

/-- The pointwise comparison of the step bound. -/
theorem leakBnd_le_comb {δ g K Cm Cf B c c' η w v : ℝ} (hg : 0 ≤ g) (hK : 0 ≤ K)
    (hη : 0 < η) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hv : v ^ 2 = w) (hB : 0 ≤ B)
    (hc : c ≤ c') :
    Cm * (δ + w) / η * K * Real.sqrt g +
        ((Cm * (δ + w)) ^ 2 + (Cf * (v + δ)) ^ 2) / (2 * η ^ 2) * K * g + c * B * g / (4 * η ^ 2) ≤
      K * (Cm / η) * (δ * Real.sqrt g + Real.sqrt g * w) +
        K * ((Cm ^ 2 + Cf ^ 2) / η ^ 2) * (δ ^ 2 * g + g * w) + c' * B * g / (4 * η ^ 2) := by
  have h1 : Cm * (δ + w) / η * K * Real.sqrt g =
      K * (Cm / η) * (δ * Real.sqrt g + Real.sqrt g * w) := by ring
  have h2 : (Cm * (δ + w)) ^ 2 + (Cf * (v + δ)) ^ 2 ≤ 2 * (Cm ^ 2 + Cf ^ 2) * (δ ^ 2 + w) := by
    have a : (δ + w) ^ 2 ≤ 2 * (δ ^ 2 + w) := by nlinarith [sq_nonneg (δ - w)]
    have b : (v + δ) ^ 2 ≤ 2 * (δ ^ 2 + w) := by nlinarith [sq_nonneg (v - δ)]
    have : (Cm * (δ + w)) ^ 2 + (Cf * (v + δ)) ^ 2 = Cm ^ 2 * (δ + w) ^ 2 + Cf ^ 2 * (v + δ) ^ 2 := by
      ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left a (sq_nonneg Cm), mul_le_mul_of_nonneg_left b (sq_nonneg Cf)]
  have h2' : ((Cm * (δ + w)) ^ 2 + (Cf * (v + δ)) ^ 2) / (2 * η ^ 2) * K * g ≤
      K * ((Cm ^ 2 + Cf ^ 2) / η ^ 2) * (δ ^ 2 * g + g * w) := by
    have hη2 : 0 < 2 * η ^ 2 := by positivity
    have e : K * ((Cm ^ 2 + Cf ^ 2) / η ^ 2) * (δ ^ 2 * g + g * w) =
        2 * (Cm ^ 2 + Cf ^ 2) * (δ ^ 2 + w) / (2 * η ^ 2) * K * g := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right h2 hη2.le) hK) hg
  have h3 : c * B * g / (4 * η ^ 2) ≤ c' * B * g / (4 * η ^ 2) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hB) hg)
      (by positivity)
  linarith

/-- **The mean of the one-step leakage bound.** -/
theorem leakBnd_mean_le {b E h s : ℝ} (q : ℝ → ℝ) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {j : ℕ} (hsj : ⌊(W : ℝ) * s⌋₊ ≤ j) {K Cm Cf B c D x : ℝ} (hK : 0 ≤ K)
    (hCm : 0 ≤ Cm) (hB : 0 ≤ B) (hD : 0 ≤ D) (hc0 : 0 ≤ birthWeight q W j)
    (hc : birthWeight q W j ≤ c)
    (hδ : MomBd (growthPathLaw W b) (pathDelta b E W j) ((4 : ℕ) : ℝ) D)
    (hx : ∫ ω, omittedFlux b E h s W j ω ∂growthPathLaw W b ≤ x) :
    ∫⁻ ω, ENNReal.ofReal (leakBnd b E h s q K Cm Cf B W j (pastCoords W j ω)) ∂growthPathLaw W b ≤
      ENNReal.ofReal (K * (Cm / etaZ b E) * (D * Real.sqrt x + Real.sqrt x * (W : ℝ)⁻¹) +
        K * ((Cm ^ 2 + Cf ^ 2) / etaZ b E ^ 2) * (D ^ 2 * Real.sqrt (W * x) + x * (W : ℝ)⁻¹) +
        c * B * x / (4 * etaZ b E ^ 2)) := by
  set μ := growthPathLaw W b
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) hE1 hE2
  set η := etaZ b E
  set δ := pathDelta b E W j
  set g := omittedFlux b E h s W j
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set w := (W : ℝ)⁻¹
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW)
  have hv : ((Real.sqrt W)⁻¹) ^ 2 = w := by rw [inv_pow, Real.sq_sqrt hW0.le]
  have hδ0 : ∀ ω, 0 ≤ δ ω := fun ω => norm_nonneg _
  have hg0 : ∀ ω, 0 ≤ g ω := omittedFlux_nonneg b E h s W j
  obtain ⟨⟨i1, b1⟩, ⟨i2, b2⟩, ⟨i3, b3⟩, i4⟩ := moment_bounds (μ := μ) hδ0 hg0
    (measurable_omittedFlux b E h s j).aestronglyMeasurable
    (ae_omittedFlux_le (h := h) (s := s) hb hE1 hE2 hW j) hD hδ hx
  set comb : GrowthPath W → ℝ := fun ω =>
    K * (Cm / η) * (δ ω * Real.sqrt (g ω) + Real.sqrt (g ω) * w) +
      K * ((Cm ^ 2 + Cf ^ 2) / η ^ 2) * (δ ω ^ 2 * g ω + g ω * w) + c * B * g ω / (4 * η ^ 2)
  have hcI : Integrable comb μ :=
    (((i1.add (i2.mul_const w)).const_mul _).add ((i3.add (i4.mul_const w)).const_mul _)).add
      (((i4.const_mul (c * B)).div_const _))
  have hc0' : 0 ≤ c := hc0.trans hc
  have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal (leakBnd b E h s q K Cm Cf B W j (pastCoords W j ω)) ≤
      ENNReal.ofReal (comb ω) := by
    filter_upwards [ae_omittedFlux_eq_past (h := h) (s := s) (E := E) hb hW hsj] with ω hω
    refine ENNReal.ofReal_le_ofReal ?_
    have e : leakBnd b E h s q K Cm Cf B W j (pastCoords W j ω) =
        Cm * (δ ω + w) / η * K * Real.sqrt (g ω) +
          ((Cm * (δ ω + w)) ^ 2 + (Cf * ((Real.sqrt W)⁻¹ + δ ω)) ^ 2) / (2 * η ^ 2) * K * g ω +
          birthWeight q W j * B * g ω / (4 * η ^ 2) := by
      have hδω := pathDelta_eq_past (W := W) b E j ω
      unfold leakBnd
      rw [← hω, ← hδω]
    rw [e]
    exact leakBnd_le_comb (hg0 ω) hK hη hw0 hw1 hv hB hc
  refine (lintegral_mono_ae hpt).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hcI (ae_of_all _ fun ω => by
    have := hδ0 ω; have := hg0 ω; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [comb]
  have j1 : Integrable (fun ω => δ ω * Real.sqrt (g ω) + Real.sqrt (g ω) * w) μ :=
    i1.add (i2.mul_const w)
  have j2 : Integrable (fun ω => δ ω ^ 2 * g ω + g ω * w) μ := i3.add (i4.mul_const w)
  have j3 : Integrable (fun ω => K * (Cm / η) * (δ ω * Real.sqrt (g ω) + Real.sqrt (g ω) * w)) μ :=
    j1.const_mul _
  have j4 : Integrable (fun ω => K * ((Cm ^ 2 + Cf ^ 2) / η ^ 2) * (δ ω ^ 2 * g ω + g ω * w)) μ :=
    j2.const_mul _
  have j34 : Integrable (fun ω => K * (Cm / η) * (δ ω * Real.sqrt (g ω) + Real.sqrt (g ω) * w) +
      K * ((Cm ^ 2 + Cf ^ 2) / η ^ 2) * (δ ω ^ 2 * g ω + g ω * w)) μ := j3.add j4
  have j5 : Integrable (fun ω => c * B * g ω / (4 * η ^ 2)) μ := (i4.const_mul (c * B)).div_const _
  have j6 : Integrable (fun ω => Real.sqrt (g ω) * w) μ := i2.mul_const w
  have j7 : Integrable (fun ω => g ω * w) μ := i4.mul_const w
  rw [integral_add j34 j5, integral_add j3 j4, integral_const_mul, integral_const_mul,
    integral_add i1 j6, integral_add i3 j7, integral_mul_const, integral_mul_const, integral_div,
    integral_const_mul]
  have hK1 : 0 ≤ K * (Cm / η) := by positivity
  have hK2 : 0 ≤ K * ((Cm ^ 2 + Cf ^ 2) / η ^ 2) := by positivity
  have t1 : ∫ ω, δ ω * Real.sqrt (g ω) ∂μ + (∫ ω, Real.sqrt (g ω) ∂μ) * w ≤
      D * Real.sqrt x + Real.sqrt x * w := by nlinarith
  have t2 : ∫ ω, δ ω ^ 2 * g ω ∂μ + (∫ ω, g ω ∂μ) * w ≤
      D ^ 2 * Real.sqrt (W * x) + x * w := by nlinarith
  have t3 : c * B * ∫ ω, g ω ∂μ ≤ c * B * x := mul_le_mul_of_nonneg_left hx (by positivity)
  have := mul_le_mul_of_nonneg_left t1 hK1
  have := mul_le_mul_of_nonneg_left t2 hK2
  have := div_le_div_of_nonneg_right t3 (show 0 ≤ 4 * η ^ 2 by positivity)
  linarith

end BlockBand.SourceProcess.SmallLeak
