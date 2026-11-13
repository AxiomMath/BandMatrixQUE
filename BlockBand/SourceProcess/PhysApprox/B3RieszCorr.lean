module

public import BlockBand.SourceProcess.PhysApprox.B3Riesz
public import BlockBand.SourceProcess.PhysApprox.B3MomTight
public import BlockBand.SourceProcess.PhysApprox.ClosingK
public import BlockBand.SourceProcess.PhysApprox.ClosingAnalyticAlg
public import BlockBand.SourceProcess.ClosingAux.Reflection

/-!
# The per-length correction moment from M. Riesz

**The argument.** At length `n` the correction is `corr(z) = 2iηz Vᴴ(1 − zN)⁻¹Π𝕊V`
(`b3KCorrAt`, `N = Π𝕊A`; time-`s` omitted data, `𝕊` at length `n`). Almost surely `N^k → 0`
(the proof of `closedReflection_holds` at an arbitrary length `n ≥ 1`), so for each test
vector `u = e_i + c e_k`, `|c| = 1`, `F_c(z) = u* corr(z) u` is complex differentiable on a disc
of radius `R > 1` with `F_c(0) = 0`. On `|z| = 1`, `CCᴴ = 1 + Z + Zᴴ` gives
`Im F_c = η(‖C*Vu‖² − ‖Vu‖²)`. M. Riesz at `p = 4` (`lintegral_phase_riesz_four`) and
polarization bound `E_θ|corr_ik|⁴` by phase moments of the closed and open probe column norms.
No stop, no closed-boundary jet, and no maximal (`sup` over `j`) estimate is used.

Defined here:
* `corrMat`: the correction as a function of the phase; `b3KCorrAt` is `corrMat` at `e^{iθ}`;
* `rzClosedProbe`, `rzClosedTrace`: the closed probe frame `C_n(z)ᴴV_n` (the probe columns of
  `b3ClosedFrameAt`) and its Gram trace `Re Tr(V_clᴴV_cl)`;
* **`ClosedTraceFour`**, stated as a hypothesis: the unstopped fourth moment of the closed probe
  trace, `E (Re Tr V_clᴴV_cl)⁴ ≤ C` at every length `n_s < n ≤ ⌊WT⌋`.

Proved here:
* `lintegral_phase_corr_le` (generic algebra + Riesz): pathwise
  `E_θ|corr_ik|⁴ ≤ 12288 E_θ(2η(c_i² + c_k² + a_i² + a_k²))⁴`, `c`, `a` the closed and open
  probe column norms;
* `tendsto_closingN_pow_at`: `N^k → 0` at every length `n ≥ 1`, for every time-`s` data;
* **`lintegral_kCorr_unstopped_le`**: `ClosedTraceFour + RawTagMoments ⇒` the unstopped
  per-length bound `E|corr_{j+1,ik}|⁴ ≤ C`;
* **`complexKCorrMoment_of_closedTrace`**: `ClosedTraceFour + RawTagMoments ⇒
  ComplexKCorrMoment` (the stop indicator is dropped);
* **`complexKStoppedMoment_of_closedTrace`**: the per-length stopped fourth moment
  `ComplexKStoppedMoment` from the same two inputs (`complexKStoppedMoment_of_corr`). This does not
  use any maximal form, so it does not depend circularly on `ComplexKStoppedMomentMax`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.ClosingLeak
open BlockBand.SourceProcess.ClosedPath BlockBand.Transmission.Bridge
open scoped NNReal ENNReal

/-!
## Generic algebra: the correction as a function of the phase
-/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {np : ℕ}

/-- **The closed resolvent correction as a function of the phase**:
`corr(z) = 2iηz Vᴴ(1 − zN)⁻¹Π𝕊V`, `N = Π𝕊A`. -/
def corrMat (η : ℝ) (S A Pi : Matrix ι ι ℂ) (V : Matrix ι (Fin np) ℂ) (z : ℂ) :
    Matrix (Fin np) (Fin np) ℂ :=
  (((2 * η : ℝ) : ℂ) * Complex.I * z) • (Vᴴ * (1 - z • closingN S A Pi)⁻¹ * Pi * S * V)

theorem corrMat_form (η : ℝ) (S A Pi : Matrix ι ι ℂ) (V : Matrix ι (Fin np) ℂ)
    (u : Fin np → ℂ) (z : ℂ) :
    star u ⬝ᵥ (corrMat η S A Pi V z *ᵥ u) = (((2 * η : ℝ) : ℂ) * Complex.I * z) *
      (star (V *ᵥ u) ⬝ᵥ ((1 - z • closingN S A Pi)⁻¹ *ᵥ ((Pi * S * V) *ᵥ u))) := by
  rw [corrMat, smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  rw [show Vᴴ * (1 - z • closingN S A Pi)⁻¹ * Pi * S * V =
      Vᴴ * ((1 - z • closingN S A Pi)⁻¹ * (Pi * S * V)) by simp only [Matrix.mul_assoc],
    star_dotProduct_conjTranspose_mul, ← mulVec_mulVec]

theorem corrMat_form_zero (η : ℝ) (S A Pi : Matrix ι ι ℂ) (V : Matrix ι (Fin np) ℂ)
    (u : Fin np → ℂ) : star u ⬝ᵥ (corrMat η S A Pi V 0 *ᵥ u) = 0 := by
  rw [corrMat_form]
  simp

/-- `z ↦ u* corr(z) u` is complex differentiable on the closed unit disc when `N^k → 0`. -/
theorem differentiableOn_corrForm {S A Pi : Matrix ι ι ℂ}
    (hN : Tendsto (fun n => closingN S A Pi ^ n) atTop (𝓝 0)) (η : ℝ)
    (V : Matrix ι (Fin np) ℂ) (u : Fin np → ℂ) :
    DifferentiableOn ℂ (fun z => star u ⬝ᵥ (corrMat η S A Pi V z *ᵥ u))
      (Metric.closedBall 0 1) := by
  obtain ⟨R, hR, -, hd⟩ := exists_radius_scalar hN (V *ᵥ u) ((Pi * S * V) *ᵥ u)
  have hlin : DifferentiableOn ℂ (fun z : ℂ => ((2 * η : ℝ) : ℂ) * Complex.I * z)
      (Metric.ball 0 R) := by fun_prop
  refine ((hlin.mul hd).mono (Metric.closedBall_subset_ball hR)).congr fun z _ => ?_
  exact corrMat_form η S A Pi V u z

/-- **`Im u* corr(z) u = η(‖C(z)ᴴVu‖² − ‖Vu‖²)`** on `|z| = 1`, `1 − zN` invertible. -/
theorem im_corrForm {S A Pi : Matrix ι ι ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1) {z : ℂ} (hz : z * star z = 1)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (η : ℝ) (V : Matrix ι (Fin np) ℂ)
    (u : Fin np → ℂ) :
    (star u ⬝ᵥ (corrMat η S A Pi V z *ᵥ u)).im =
      η * (l2 (((closingMap S A Pi z)ᴴ * V) *ᵥ u) ^ 2 - l2 (V *ᵥ u) ^ 2) := by
  set Z := closingZ S A Pi z
  have hCC := closingMap_mul_conj hA2 hAH hPi hS hz hU
  have hK : corrMat η S A Pi V z = (((2 * η : ℝ) : ℂ) * Complex.I) • (Vᴴ * Z * V) := by
    rw [corrMat, show Z = z • ((1 - z • closingN S A Pi)⁻¹ * (Pi * S)) from rfl,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    simp only [Matrix.mul_assoc]
  set w := V *ᵥ u
  have hF : star u ⬝ᵥ (corrMat η S A Pi V z *ᵥ u) =
      (((2 * η : ℝ) : ℂ) * Complex.I) * (star w ⬝ᵥ (Z *ᵥ w)) := by
    rw [hK, smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mul_assoc,
      star_dotProduct_conjTranspose_mul, ← mulVec_mulVec]
  have hcl : l2 (((closingMap S A Pi z)ᴴ * V) *ᵥ u) ^ 2 =
      l2 w ^ 2 + 2 * (star w ⬝ᵥ (Z *ᵥ w)).re := by
    rw [← mulVec_mulVec, l2_mulVec_sq, conjTranspose_conjTranspose, hCC, add_mulVec,
      add_mulVec, one_mulVec, dotProduct_add, dotProduct_add, Complex.add_re, Complex.add_re,
      ← l2_sq]
    have h3 : (star w ⬝ᵥ (Zᴴ *ᵥ w)).re = (star w ⬝ᵥ (Z *ᵥ w)).re := by
      rw [dotProduct_mulVec, ← star_mulVec, re_star_dotProduct_comm]
    rw [h3]
    ring
  rw [hF, hcl]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

omit [DecidableEq ι] in
theorem l2_mulVec_testVec_sq_le (M : Matrix ι (Fin np) ℂ) (i k : Fin np) {c : ℂ}
    (hc : ‖c‖ = 1) : l2 (M *ᵥ testVec i k c) ^ 2 ≤ 2 * (l2 (Mᵀ i) ^ 2 + l2 (Mᵀ k) ^ 2) := by
  have e : M *ᵥ testVec i k c = Mᵀ i + c • Mᵀ k := by
    rw [testVec, mulVec_add, mulVec_smul, mulVec_single_one, mulVec_single_one]
    rfl
  have h1 : l2 (M *ᵥ testVec i k c) ≤ l2 (Mᵀ i) + l2 (Mᵀ k) := by
    rw [e]
    refine (l2_add_le _ _).trans (le_of_eq ?_)
    rw [l2_smul, hc, one_mul]
  have h2 : l2 (M *ᵥ testVec i k c) ^ 2 ≤ (l2 (Mᵀ i) + l2 (Mᵀ k)) ^ 2 :=
    pow_le_pow_left₀ (l2_nonneg _) h1 2
  nlinarith [sq_nonneg (l2 (Mᵀ i) - l2 (Mᵀ k))]

/-- The pointwise bound `2η(c_i² + c_k² + a_i² + a_k²)` on `|Im F_c|`. -/
def corrBnd (η : ℝ) (S A Pi : Matrix ι ι ℂ) (V : Matrix ι (Fin np) ℂ) (i k : Fin np) (z : ℂ) :
    ℝ :=
  2 * η * (l2 (((closingMap S A Pi z)ᴴ * V)ᵀ i) ^ 2 + l2 (((closingMap S A Pi z)ᴴ * V)ᵀ k) ^ 2 +
    l2 (Vᵀ i) ^ 2 + l2 (Vᵀ k) ^ 2)

theorem abs_im_corrForm_le {S A Pi : Matrix ι ι ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1) {z : ℂ} (hz : z * star z = 1)
    (hU : IsUnit (1 - z • closingN S A Pi).det) {η : ℝ} (hη : 0 ≤ η)
    (V : Matrix ι (Fin np) ℂ) (i k : Fin np) {c : ℂ} (hc : ‖c‖ = 1) :
    |(star (testVec i k c) ⬝ᵥ (corrMat η S A Pi V z *ᵥ testVec i k c)).im| ≤
      corrBnd η S A Pi V i k z := by
  rw [im_corrForm hA2 hAH hPi hS hz hU, corrBnd]
  have h1 := l2_mulVec_testVec_sq_le ((closingMap S A Pi z)ᴴ * V) i k hc
  have h2 := l2_mulVec_testVec_sq_le V i k hc
  have h3 := sq_nonneg (l2 (((closingMap S A Pi z)ᴴ * V) *ᵥ testVec i k c))
  have h4 := sq_nonneg (l2 (V *ᵥ testVec i k c))
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hη, mul_le_mul_of_nonneg_left h2 hη,
    mul_nonneg hη h3, mul_nonneg hη h4]

theorem add4_pow_four_le (a b c d : ℝ≥0∞) :
    (a + b + c + d) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
  calc (a + b + c + d) ^ 4 = ((a + b) + (c + d)) ^ 4 := by ring
    _ ≤ 8 * ((a + b) ^ 4 + (c + d) ^ 4) := add_pow_four_le _ _
    _ ≤ 8 * (8 * (a ^ 4 + b ^ 4) + 8 * (c ^ 4 + d ^ 4)) := by
        gcongr <;> exact add_pow_four_le _ _
    _ = 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by ring

theorem add3_pow_four_le (a b c : ℝ≥0∞) : (a + b + c) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  have h := add4_pow_four_le a b c 0
  simpa using h

/-- **The pathwise Riesz bound for the correction** (generic data): if `N^k → 0`,
`E_θ|corr_ik(e^{iθ})|⁴ ≤ 12288 E_θ(2η(c_i² + c_k² + a_i² + a_k²))⁴`. -/
theorem lintegral_phase_corr_le {S A Pi : Matrix ι ι ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1)
    (hN : Tendsto (fun n => closingN S A Pi ^ n) atTop (𝓝 0)) {η : ℝ} (hη : 0 ≤ η)
    (V : Matrix ι (Fin np) ℂ) (i k : Fin np) :
    ∫⁻ θ, ‖corrMat η S A Pi V (phase θ) i k‖ₑ ^ 4 ∂phaseLaw ≤
      12288 * ∫⁻ θ, ENNReal.ofReal (corrBnd η S A Pi V i k (phase θ)) ^ 4 ∂phaseLaw := by
  obtain ⟨R, hR, hunit, -⟩ := exists_radius_scalar hN (0 : ι → ℂ) 0
  have hU : ∀ θ : ℝ, IsUnit (1 - phase θ • closingN S A Pi).det := fun θ =>
    hunit _ (by rw [norm_phase]; exact hR)
  have hmem : ∀ θ, phase θ ∈ Metric.closedBall (0 : ℂ) 1 := fun θ => by
    rw [Metric.mem_closedBall, dist_zero_right, norm_phase]
  set F : ℂ → ℂ → ℂ := fun c z => star (testVec i k c) ⬝ᵥ (corrMat η S A Pi V z *ᵥ testVec i k c)
  have hone : ∀ c : ℂ, ‖c‖ = 1 → Measurable (fun θ => ‖F c (phase θ)‖ₑ ^ 4) ∧
      ∫⁻ θ, ‖F c (phase θ)‖ₑ ^ 4 ∂phaseLaw ≤
        48 * ∫⁻ θ, ENNReal.ofReal (corrBnd η S A Pi V i k (phase θ)) ^ 4 ∂phaseLaw := by
    intro c hc
    have hd := differentiableOn_corrForm hN η V (testVec i k c)
    have hcont : Continuous fun θ => F c (phase θ) :=
      hd.continuousOn.comp_continuous continuous_phase hmem
    refine ⟨hcont.measurable.enorm.pow_const 4,
      (lintegral_phase_riesz_four hd (corrMat_form_zero η S A Pi V _)).trans ?_⟩
    gcongr with θ
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal
      (abs_im_corrForm_le hA2 hAH hPi hS (phase_mul_star θ) (hU θ) hη V i k hc)
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hmI : ‖-Complex.I‖ = 1 := by rw [norm_neg, Complex.norm_I]
  obtain ⟨m1, l1⟩ := hone 1 (by simp)
  obtain ⟨m2, l2'⟩ := hone Complex.I hI
  obtain ⟨m3, l3⟩ := hone (-1) (by simp)
  obtain ⟨m4, l4⟩ := hone (-Complex.I) hmI
  have hpt : ∀ θ, ‖corrMat η S A Pi V (phase θ) i k‖ₑ ^ 4 ≤
      64 * (‖F 1 (phase θ)‖ₑ ^ 4 + ‖F Complex.I (phase θ)‖ₑ ^ 4 +
        ‖F (-1) (phase θ)‖ₑ ^ 4 + ‖F (-Complex.I) (phase θ)‖ₑ ^ 4) := by
    intro θ
    set X := corrMat η S A Pi V (phase θ)
    have hpol := polarization X i k
    have hr : ‖X i k‖ ≤ ‖F 1 (phase θ)‖ + ‖F Complex.I (phase θ)‖ + ‖F (-1) (phase θ)‖ +
        ‖F (-Complex.I) (phase θ)‖ := by
      have e4 : ‖(4 : ℂ) * X i k‖ = 4 * ‖X i k‖ := by
        rw [norm_mul]
        norm_num
      have n1 : ‖Complex.I * F Complex.I (phase θ)‖ = ‖F Complex.I (phase θ)‖ := by
        rw [norm_mul, hI, one_mul]
      have n2 : ‖Complex.I * F (-Complex.I) (phase θ)‖ = ‖F (-Complex.I) (phase θ)‖ := by
        rw [norm_mul, hI, one_mul]
      have t1 := norm_add_le (F 1 (phase θ) - Complex.I * F Complex.I (phase θ) -
        F (-1) (phase θ)) (Complex.I * F (-Complex.I) (phase θ))
      have t2 := norm_sub_le (F 1 (phase θ) - Complex.I * F Complex.I (phase θ))
        (F (-1) (phase θ))
      have t3 := norm_sub_le (F 1 (phase θ)) (Complex.I * F Complex.I (phase θ))
      have h4 : ‖(4 : ℂ) * X i k‖ = ‖F 1 (phase θ) - Complex.I * F Complex.I (phase θ) -
          F (-1) (phase θ) + Complex.I * F (-Complex.I) (phase θ)‖ := by
        rw [hpol]
      linarith [norm_nonneg (X i k)]
    have he : ‖X i k‖ₑ ≤ ‖F 1 (phase θ)‖ₑ + ‖F Complex.I (phase θ)‖ₑ + ‖F (-1) (phase θ)‖ₑ +
        ‖F (-Complex.I) (phase θ)‖ₑ := by
      simp only [← ofReal_norm]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal hr
    exact (pow_le_pow_left₀ zero_le he 4).trans (add4_pow_four_le _ _ _ _)
  calc ∫⁻ θ, ‖corrMat η S A Pi V (phase θ) i k‖ₑ ^ 4 ∂phaseLaw ≤
        ∫⁻ θ, 64 * (‖F 1 (phase θ)‖ₑ ^ 4 + ‖F Complex.I (phase θ)‖ₑ ^ 4 +
          ‖F (-1) (phase θ)‖ₑ ^ 4 + ‖F (-Complex.I) (phase θ)‖ₑ ^ 4) ∂phaseLaw :=
        lintegral_mono hpt
    _ = 64 * (∫⁻ θ, ‖F 1 (phase θ)‖ₑ ^ 4 ∂phaseLaw +
          ∫⁻ θ, ‖F Complex.I (phase θ)‖ₑ ^ 4 ∂phaseLaw +
          ∫⁻ θ, ‖F (-1) (phase θ)‖ₑ ^ 4 ∂phaseLaw +
          ∫⁻ θ, ‖F (-Complex.I) (phase θ)‖ₑ ^ 4 ∂phaseLaw) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_right _ m4,
          lintegral_add_right _ m3, lintegral_add_right _ m2]
    _ ≤ 64 * (48 * ∫⁻ θ, ENNReal.ofReal (corrBnd η S A Pi V i k (phase θ)) ^ 4 ∂phaseLaw +
          48 * ∫⁻ θ, ENNReal.ofReal (corrBnd η S A Pi V i k (phase θ)) ^ 4 ∂phaseLaw +
          48 * ∫⁻ θ, ENNReal.ofReal (corrBnd η S A Pi V i k (phase θ)) ^ 4 ∂phaseLaw +
          48 * ∫⁻ θ, ENNReal.ofReal (corrBnd η S A Pi V i k (phase θ)) ^ 4 ∂phaseLaw) := by
        gcongr
    _ = 12288 * ∫⁻ θ, ENNReal.ofReal (corrBnd η S A Pi V i k (phase θ)) ^ 4 ∂phaseLaw := by
        ring

end Generic

/-!
## `N^k → 0` at every length
-/

variable {W np : ℕ}

/-- **`N^k → 0` at every length `n ≥ 1`** for every choice of the omitted data (the argument of
`closedReflection_holds`, which is stated at the final length only). -/
theorem tendsto_closingN_pow_at {b E : ℝ} (hη : 0 < etaZ b E) {h : ℝ} (hh2 : h ^ 2 < 1)
    {nS n : ℕ} (hn : 1 ≤ n) (ω : GrowthPath W)
    (hU : scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1)
    (hM : IsUnit (fullPathMatrix b E W n ω)) (hB : ∀ k, IsUnit (ω.2 k)) :
    Tendsto (fun k => closingN (scatteringMatrix b E W n ω) (farEmbed (omittedProj b E h W nS ω))
      (farEmbed (closingPairing b E h W nS ω)) ^ k) atTop (𝓝 0) :=
  tendsto_closingN_pow (by rw [farEmbed_mul, omittedProj_mul_self])
    (by rw [farEmbed_conjTranspose, omittedProj_conjTranspose])
    (by rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh2]) hU
    (phys_hinj hη h hn ω hM hB)

/-!
## The physical correction
-/

/-- **The closed probe frame at length `n`**: `C_n(e^{iθ})ᴴ V_n`, the probe columns of
`b3ClosedFrameAt` (`C_n` with the time-`s` omitted channels). -/
def rzClosedProbe (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) (y : ProbedPath W np × ℝ) :
    Matrix (Fin 2 × Fin W) (Fin np) ℂ :=
  (physClosingMapAt b E s h W n y.1.1 (phase y.2))ᴴ * probeFrame b E W n τ m y.1

/-- **The closed probe Gram trace** `Re Tr(V_clᴴV_cl)` at length `n`. -/
def rzClosedTrace (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) (y : ProbedPath W np × ℝ) : ℝ :=
  (((rzClosedProbe b E s h τ m W n y)ᴴ * rzClosedProbe b E s h τ m W n y).trace).re

/-- **`ClosedTraceFour`: the unstopped fourth moment of the closed probe trace**: on the domain,
eventually in `W`, at every length `n_s < j + 1 ≤ ⌊WT⌋`, `E (Re Tr V_clᴴV_cl)⁴ ≤ C` under
`closedLaw` (path, probes and the uniform phase). -/
def ClosedTraceFour : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → 0 < h → h < 1 → ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ →
        ∫⁻ y, ENNReal.ofReal (rzClosedTrace b E s h τ m W (j + 1) y) ^ 4 ∂closedLaw b W np ≤
          ENNReal.ofReal C

theorem l2_col_sq_le_trace {ι c : Type*} [Fintype ι] [Fintype c] (M : Matrix ι c ℂ) (i : c) :
    l2 (Mᵀ i) ^ 2 ≤ ((Mᴴ * M).trace).re := by
  have htr : ((Mᴴ * M).trace).re = ∑ d, ∑ x, ‖M x d‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [htr, l2_sq_eq_sum]
  exact Finset.single_le_sum (f := fun d => ∑ x, ‖M x d‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem measurable_rzClosedProbe (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ => rzClosedProbe b E s h τ m W n y :=
  measurable_matrix_mul' (measurable_matrix_conjTranspose' (measurable_physClosingMapAt_comp
    b E s h n (measurable_fst.comp measurable_fst) (measurable_phase.comp measurable_snd)))
    ((measurable_probeFrame b E W n τ m).comp measurable_fst)

theorem measurable_rzClosedTrace (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ => rzClosedTrace b E s h τ m W n y := by
  have hP := measurable_rzClosedProbe b E s h τ m W n
  have hG := measurable_matrix_mul' (measurable_matrix_conjTranspose' hP) hP
  unfold rzClosedTrace
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  exact Finset.measurable_sum _ fun d _ => Complex.measurable_re.comp hG.eval_matrix

/-- The constant of the physical pathwise bound. -/
def corrKc (b E : ℝ) : ℝ≥0∞ := 786432 * ENNReal.ofReal (4 * etaZ b E) ^ 4

/-- The integrand of the physical pathwise bound: the closed trace and two open columns. -/
def corrH (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) (i k : Fin np)
    (y : ProbedPath W np × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (rzClosedTrace b E s h τ m W n y) ^ 4 +
    ENNReal.ofReal (l2 ((probeFrame b E W n τ m y.1)ᵀ i) ^ 2) ^ 4 +
    ENNReal.ofReal (l2 ((probeFrame b E W n τ m y.1)ᵀ k) ^ 2) ^ 4

theorem measurable_probeCol_pow (b E : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) (i : Fin np) :
    Measurable fun y : ProbedPath W np × ℝ =>
      ENNReal.ofReal (l2 ((probeFrame b E W n τ m y.1)ᵀ i) ^ 2) ^ 4 :=
  (ENNReal.measurable_ofReal.comp ((measurable_l2_col
    ((measurable_probeFrame b E W n τ m).comp measurable_fst) i).pow_const 2)).pow_const 4

theorem measurable_trace_pow (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ =>
      ENNReal.ofReal (rzClosedTrace b E s h τ m W n y) ^ 4 :=
  (ENNReal.measurable_ofReal.comp (measurable_rzClosedTrace b E s h τ m W n)).pow_const 4

theorem measurable_corrH (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) (i k : Fin np) :
    Measurable (corrH b E s h τ m W n i k) :=
  ((measurable_trace_pow b E s h τ m W n).add (measurable_probeCol_pow b E τ m W n i)).add
    (measurable_probeCol_pow b E τ m W n k)

/-- **The physical pathwise bound**: on a path with unitary `𝕊_n`, invertible `H_n − E` and
invertible bonds, `E_θ|corr_{n,ik}|⁴ ≤ E_θ[Kc · H]`. -/
theorem lintegral_phase_b3KCorr_le {b E s h : ℝ} (hη : 0 < etaZ b E) (hh2 : h ^ 2 < 1)
    (τ m : Fin np → ℝ) {n : ℕ} (hn : 1 ≤ n) (x : ProbedPath W np)
    (hU : scatteringMatrix b E W n x.1 * (scatteringMatrix b E W n x.1)ᴴ = 1)
    (hM : IsUnit (fullPathMatrix b E W n x.1)) (hB : ∀ k, IsUnit (x.1.2 k)) (i k : Fin np) :
    ∫⁻ θ, ‖b3KCorrAt b E s h τ m W n (x, θ) i k‖ₑ ^ 4 ∂phaseLaw ≤
      ∫⁻ θ, corrKc b E * corrH b E s h τ m W n i k (x, θ) ∂phaseLaw := by
  set S := scatteringMatrix b E W n x.1
  set A := farEmbed (omittedProj b E h W (closeLen s W) x.1)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) x.1)
  set V := probeFrame b E W n τ m x
  have hA2 : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh2]
  have hN := tendsto_closingN_pow_at (nS := closeLen s W) hη hh2 hn x.1 hU hM hB
  have hgen := lintegral_phase_corr_le hA2 hAH hPi hU hN hη.le V i k
  calc ∫⁻ θ, ‖b3KCorrAt b E s h τ m W n (x, θ) i k‖ₑ ^ 4 ∂phaseLaw =
        ∫⁻ θ, ‖corrMat (etaZ b E) S A Pi V (phase θ) i k‖ₑ ^ 4 ∂phaseLaw := rfl
    _ ≤ 12288 * ∫⁻ θ, ENNReal.ofReal (corrBnd (etaZ b E) S A Pi V i k (phase θ)) ^ 4
          ∂phaseLaw := hgen
    _ = ∫⁻ θ, 12288 * ENNReal.ofReal (corrBnd (etaZ b E) S A Pi V i k (phase θ)) ^ 4
          ∂phaseLaw := (lintegral_const_mul' _ _ (by norm_num)).symm
    _ ≤ ∫⁻ θ, corrKc b E * corrH b E s h τ m W n i k (x, θ) ∂phaseLaw := by
        refine lintegral_mono fun θ => ?_
        set M := (closingMap S A Pi (phase θ))ᴴ * V
        have hM' : M = rzClosedProbe b E s h τ m W n (x, θ) := rfl
        have hci := l2_col_sq_le_trace M i
        have hck := l2_col_sq_le_trace M k
        have htr : ((Mᴴ * M).trace).re = rzClosedTrace b E s h τ m W n (x, θ) := by
          rw [hM']
          rfl
        rw [htr] at hci hck
        have ht0 : 0 ≤ rzClosedTrace b E s h τ m W n (x, θ) :=
          (sq_nonneg _).trans hci
        have hai := sq_nonneg (l2 (Vᵀ i))
        have hak := sq_nonneg (l2 (Vᵀ k))
        have hb : corrBnd (etaZ b E) S A Pi V i k (phase θ) ≤
            4 * etaZ b E * (rzClosedTrace b E s h τ m W n (x, θ) + l2 (Vᵀ i) ^ 2 +
              l2 (Vᵀ k) ^ 2) := by
          rw [corrBnd]
          nlinarith [hη.le]
        have hb' : ENNReal.ofReal (corrBnd (etaZ b E) S A Pi V i k (phase θ)) ≤
            ENNReal.ofReal (4 * etaZ b E) *
              (ENNReal.ofReal (rzClosedTrace b E s h τ m W n (x, θ)) +
                ENNReal.ofReal (l2 (Vᵀ i) ^ 2) + ENNReal.ofReal (l2 (Vᵀ k) ^ 2)) := by
          rw [← ENNReal.ofReal_add ht0 hai, ← ENNReal.ofReal_add (by positivity) hak,
            ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal hb
        have hp := (pow_le_pow_left₀ zero_le hb' 4).trans_eq (mul_pow _ _ 4)
        calc 12288 * ENNReal.ofReal (corrBnd (etaZ b E) S A Pi V i k (phase θ)) ^ 4 ≤
              12288 * (ENNReal.ofReal (4 * etaZ b E) ^ 4 *
                (64 * corrH b E s h τ m W n i k (x, θ))) := by
              gcongr
              exact hp.trans (by gcongr; exact add3_pow_four_le _ _ _)
          _ = corrKc b E * corrH b E s h τ m W n i k (x, θ) := by
              rw [corrKc]
              ring

/-!
## The per-length moment
-/

theorem rpow_four_le_sourceDataMoment (y : SourceData np) (r : Fin 4) (i j : Fin np) :
    ‖y r i j‖ ^ 4 ≤ sourceDataMoment 4 y := by
  have e : ‖y r i j‖ ^ 4 = ‖y r i j‖ ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e]
  unfold sourceDataMoment
  have h1 : ‖y r i j‖ ^ (4 : ℝ) ≤ ∑ j', ‖y r i j'‖ ^ (4 : ℝ) :=
    Finset.single_le_sum (f := fun j' => ‖y r i j'‖ ^ (4 : ℝ)) (fun _ _ => by positivity)
      (Finset.mem_univ j)
  have h2 : ∑ j', ‖y r i j'‖ ^ (4 : ℝ) ≤ ∑ i', ∑ j', ‖y r i' j'‖ ^ (4 : ℝ) :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖y r i' j'‖ ^ (4 : ℝ))
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  have h3 : ∑ i', ∑ j', ‖y r i' j'‖ ^ (4 : ℝ) ≤ ∑ r', ∑ i', ∑ j', ‖y r' i' j'‖ ^ (4 : ℝ) :=
    Finset.single_le_sum (f := fun r' => ∑ i', ∑ j', ‖y r' i' j'‖ ^ (4 : ℝ))
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.mem_univ r)
  exact h1.trans (h2.trans h3)

/-- The open column fourth moment `E‖V e_i‖⁸` from the raw tag moments at `p = 4`. -/
theorem lintegral_probeCol_pow_le {b E : ℝ} (hη : 0 < etaZ b E) {τ m : Fin np → ℝ}
    (hm : ∀ j, 0 ≤ m j) {n : ℕ} {C : ℝ} (hraw : RawTagBoundAt b E W n 4 C) (i : Fin np) :
    ∫⁻ y, ENNReal.ofReal (l2 ((probeFrame b E W n τ m y.1)ᵀ i) ^ 2) ^ 4 ∂closedLaw b W np ≤
      momentBound (etaZ b E) 4 C m := by
  refine (lintegral_prod_le _).trans ?_
  simp only [lintegral_const, measure_univ, mul_one]
  refine le_trans (lintegral_mono fun x => ?_)
    (lintegral_sourceDataMoment_le b E hη n τ m hm (by norm_num) hraw)
  rw [← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : l2 ((probeFrame b E W n τ m x)ᵀ i) ^ 2 =
      ‖complexSourceData b E W n τ m x 1 i i‖ := by
    rw [l2_sq_eq_sum]
    exact (norm_gram_diag (probeFrame b E W n τ m x) i).symm
  rw [e]
  exact rpow_four_le_sourceDataMoment _ 1 i i

/-- **The unstopped per-length correction moment** from `ClosedTraceFour` and the raw moments:
on the domain, eventually in `W`, `E|corr_{j+1,ik}|⁴ ≤ C` for `n_s ≤ j < ⌊WT⌋`. -/
theorem lintegral_kCorr_unstopped_le (hT : ClosedTraceFour) (hR : RawTagMoments) {b E : ℝ}
    {np : ℕ} {τ m : Fin np → ℝ} {T s h : ℝ} (hD : ComplexSourceLawDomain b E τ m T) (hs : 0 < s)
    (hsτ : ∀ j, s < τ j) (hh0 : 0 < h) (hh1 : h < 1) :
    ∃ C : ℝ, ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ →
      ∀ ij : Fin np × Fin np,
        ∫⁻ y, ‖b3KCorrAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np ≤
          ENNReal.ofReal C := by
  obtain ⟨CT, hCT⟩ := hT b E np τ m T s h hD hs hsτ hh0 hh1
  obtain ⟨hb0, hb1, hE0, hE1, -, -, hm, -⟩ := hD
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  obtain ⟨Cr, W₀, hCr⟩ := hR b hb0 hb1 κ hκ T 4 (by norm_num)
  have hη : 0 < etaZ b E := Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE0 hE1
  have hh2 : h ^ 2 < 1 := by nlinarith
  set MB := momentBound (etaZ b E) 4 Cr m
  have hKc : corrKc b E ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hfin : corrKc b E * (ENNReal.ofReal CT + MB + MB) ≠ ⊤ :=
    ENNReal.mul_ne_top hKc (by simp [MB, momentBound_ne_top])
  refine ⟨(corrKc b E * (ENNReal.ofReal CT + MB + MB)).toReal, ?_⟩
  filter_upwards [hCT, eventually_ge_atTop (max W₀ 1)] with W hWT hW j hj1 hj2 ij
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hn := succ_le_mul_of_lt_floor hj2
  have hraw := hCr W hW0 E hEκ (j + 1) hn
  have hgood :=
    ae_probed_of_ae (np := np) ((FullSourceStops.ae_scattering_unitary hb1 hE0 hE1 hW1).and
      ((ae_growth_isHermitian W b).and
        ((ae_isUnit_pathPencil_growth hb1 hW1 E).and (ae_isUnit_growth_bond hb0 hW1))))
  have hHm := measurable_corrH b E s h τ m W (j + 1) ij.1 ij.2
  calc ∫⁻ y, ‖b3KCorrAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np ≤
        ∫⁻ x, ∫⁻ θ, ‖b3KCorrAt b E s h τ m W (j + 1) (x, θ) ij.1 ij.2‖ₑ ^ 4 ∂phaseLaw
          ∂probedPathLaw W np b := lintegral_prod_le _
    _ ≤ ∫⁻ x, ∫⁻ θ, corrKc b E * corrH b E s h τ m W (j + 1) ij.1 ij.2 (x, θ) ∂phaseLaw
          ∂probedPathLaw W np b := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgood] with x hx
        obtain ⟨hU, hA, hF, hB⟩ := hx
        exact lintegral_phase_b3KCorr_le hη hh2 τ m (by omega) x (hU (j + 1)).1
          (isUnit_fullPathMatrix b E (j + 1) x.1 hA hη (hF (j + 1))) hB ij.1 ij.2
    _ = ∫⁻ y, corrKc b E * corrH b E s h τ m W (j + 1) ij.1 ij.2 y ∂closedLaw b W np :=
        (lintegral_prod _ (hHm.const_mul _).aemeasurable).symm
    _ = corrKc b E * (∫⁻ y, ENNReal.ofReal (rzClosedTrace b E s h τ m W (j + 1) y) ^ 4
            ∂closedLaw b W np +
          ∫⁻ y, ENNReal.ofReal (l2 ((probeFrame b E W (j + 1) τ m y.1)ᵀ ij.1) ^ 2) ^ 4
            ∂closedLaw b W np +
          ∫⁻ y, ENNReal.ofReal (l2 ((probeFrame b E W (j + 1) τ m y.1)ᵀ ij.2) ^ 2) ^ 4
            ∂closedLaw b W np) := by
        rw [lintegral_const_mul _ hHm]
        unfold corrH
        rw [lintegral_add_right _ (measurable_probeCol_pow b E τ m W (j + 1) ij.2),
          lintegral_add_right _ (measurable_probeCol_pow b E τ m W (j + 1) ij.1)]
    _ ≤ corrKc b E * (ENNReal.ofReal CT + MB + MB) := by
        gcongr
        · exact hWT j hj1 hj2
        · exact lintegral_probeCol_pow_le hη hm hraw ij.1
        · exact lintegral_probeCol_pow_le hη hm hraw ij.2
    _ = ENNReal.ofReal (corrKc b E * (ENNReal.ofReal CT + MB + MB)).toReal :=
        (ENNReal.ofReal_toReal hfin).symm

/-- **`ComplexKCorrMoment` from `ClosedTraceFour` and the raw moments** (the stop indicator is
dropped: the unstopped moment bounds the stopped one). -/
theorem complexKCorrMoment_of_closedTrace (hT : ClosedTraceFour) (hR : RawTagMoments) :
    ComplexKCorrMoment := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hD, hs, hsτ, hh0, hh1, -⟩ := hF
  obtain ⟨C, hC⟩ := lintegral_kCorr_unstopped_le hT hR hD hs hsτ hh0 hh1
  refine ⟨C, ?_⟩
  filter_upwards [hC] with W hW j hj1 hj2 ij
  exact (lintegral_mono fun y => Set.indicator_le_self _ _ y).trans (hW j hj1 hj2 ij)

/-- **The per-length stopped fourth moment `ComplexKStoppedMoment` from `ClosedTraceFour` and the raw
moments** (`complexKStoppedMoment_of_corr`). No maximal form is used. -/
theorem complexKStoppedMoment_of_closedTrace (hT : ClosedTraceFour) (hR : RawTagMoments) :
    ComplexKStoppedMoment :=
  complexKStoppedMoment_of_corr hR (complexKCorrMoment_of_closedTrace hT hR)

end BlockBand.SourceProcess.PhysApprox.B3
