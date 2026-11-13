module

public import BlockBand.SourceProcess.PhysApprox.B3JetLp
public import BlockBand.SourceProcess.PhysApprox.B3JetFam

/-!
# `ClosedJet0Fam`, and the closing shift at the closing time

* **`closedJet0Fam_of_start`**, **`closedJet0Fam_of_shift`**: `ClosedJet0Fam` from
  `closedJetLp_of`.

At the closing time `n_s` the closed cavity is diagonal in the eigenbasis `(t_k, f_k)` of the far
transmission `T_far = 1 - S_ffᴴS_ff`: `ΠS_ff = Σ_{t_k ≤ h²} √(1-t_k) f_kf_kᴴ`, and by unitarity
`|(S_ff f_k)ᴴS_fnS_nf f_k| = |(S_nf f_k)ᴴS_nn(S_nf f_k)| ≤ t_k`. Hence the closing shift of the
jet is bounded by the explicit kernel `κ(t, z) = t/(√(1-t)|1 - z√(1-t)|)`:

* **`ClosedShiftDiscTrace`** (exact algebra at `n_s`), stated as a hypothesis: uniformly on the disc
  `|w - z_∂| ≤ η/2`, `|W⁻¹Tr(w - X_cl)⁻¹ - W⁻¹Tr(w - X_open)⁻¹| ≤ 2(ηW)⁻¹ Σ_k κ(t_k, z)` a.e.;
* **`FarFracTraceMoments`** (a property of the open path law only, no closing), stated as a
  hypothesis: for every `p ≥ 1` some `α < 1/p` has `E(Σ_k t_k^α)^p ≤ C` at `n_s`, uniformly in `W`;
* `shiftKernel_le`: `κ(t, z) ≤ c_{h,α} t^α |1 - z|^{-α}`;
* `lintegral_phase_rpow_lt_top`: `E_θ|1 - e^{iθ}|^{-β} < ∞` for `0 ≤ β < 1`;
* **`closedJetShiftStartLp_of_frac`**: `ClosedShiftDiscTrace + FarFracTraceMoments ⇒
  ClosedJetShiftStartLp b3ClosedX` (Tonelli over path and phase);
* **`closedJet0Fam_of_frac`**: `ClosedJet0Fam` from `MatchedTracesContract`,
  `GaussianAbsorptionContract`, `GaussianLpGradient` and the hypotheses
  `ClosedInputPassive b3ClosedX`, `ClosedInputRecursion b3ClosedX`, `ClosedShiftDiscTrace`,
  `FarFracTraceMoments`;
* `closedShiftDisc_dominated` (for the `δ₁` shift): the disc-uniform shift has a dominating
  function `B` with `E B^p ≤ (C/W)^p`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.Closing
open scoped ENNReal ComplexOrder

/-!
## The canonical family `ClosedJet0Fam`
-/

/-- **`ClosedJet0Fam`** from passivity, the recursion and the closed start. -/
theorem closedJet0Fam_of_start (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ClosedInputPassive b3ClosedX) (hRec : ClosedInputRecursion b3ClosedX)
    (hStart : ClosedJetStartLp b3ClosedX) : ClosedJet0Fam := by
  intro b E np τ m T s h K Vs hF p hp
  obtain ⟨C, -, hC⟩ := closedJetLp_of hGA hLp (closedInputRegular_b3ClosedX hP) hRec hStart
    b E np τ m T s h K Vs hF p hp
  exact ⟨C, hC⟩

/-- **`ClosedJet0Fam`** from the contract hypotheses, passivity, the recursion and the closing shift
at `n_s`. -/
theorem closedJet0Fam_of_shift (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : ClosedInputPassive b3ClosedX)
    (hRec : ClosedInputRecursion b3ClosedX) (hSh : ClosedJetShiftStartLp b3ClosedX) :
    ClosedJet0Fam :=
  closedJet0Fam_of_start hGA hLp hP hRec
    (closedJetStartLp_of_shift (deltaZeroLengthUniform_holds hMT hGA hLp)
      (fun b E s h _ τ m _ j => measurable_b3ClosedX b E s h τ m j) hSh)

/-!
## The far spectrum, the kernel and the two estimates
-/

variable {W : ℕ}

/-- The eigenvalues `t_k` of the far transmission `T_far = 1 - S_ffᴴS_ff` at length `n`. -/
abbrev farEig (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) : Fin W → ℝ :=
  (isHermitian_farTransmission b E W n ω).eigenvalues

/-- The far fractional trace `Σ_k t_k^α` (all channels). -/
def farFracTrace (b E α : ℝ) (W n : ℕ) (ω : GrowthPath W) : ℝ :=
  ∑ k, max (farEig b E W n ω k) 0 ^ α

/-- The closing kernel at the closing time, `κ(t, z) = t/(√(1-t)|1 - z√(1-t)|)` on the omitted
channels `t ≤ h²`. -/
def shiftKernel (h t : ℝ) (z : ℂ) : ℝ :=
  if t ≤ h ^ 2 then max t 0 / (Real.sqrt (1 - t) * ‖1 - z * (Real.sqrt (1 - t) : ℂ)‖) else 0

/-- The normalized near trace `W⁻¹Tr(w - X)⁻¹` at the boundary parameter `w`. -/
def nearTraceAt (W : ℕ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  (W : ℂ)⁻¹ * ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace

theorem jetShift_eq_nearTraceAt (b E : ℝ) {np : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (r : ℕ)
    (y : ProbedPath W np × ℝ) :
    jetShift b E X r y =
      ‖nearTraceAt W (boundaryZ b E) X - nearTraceAt W (boundaryZ b E) (pathX b E W r y.1.1)‖ :=
  rfl

/-- **`ClosedShiftDiscTrace`: the closing shift at the closing time, uniformly on the
boundary disc `|w - z_∂| ≤ η/2`, is bounded by the cavity kernel** (exact algebra):
a.e., `|W⁻¹Tr(w - X_cl)⁻¹ - W⁻¹Tr(w - X_open)⁻¹| ≤ 2(ηW)⁻¹ Σ_k κ(t_k, z)`. The proof sketch
bounds the trace norm `‖R_cl - R_nn‖₁ ≤ (2η)⁻¹Σ_kκ(t_k, z)` at `w = z_∂` and moves `w` by
`(w - X)⁻¹ = R(1 + (w - z_∂)R)⁻¹`, `‖R‖, ‖R_cl‖ ≤ η⁻¹` (passivity). The disc form also feeds
the `δ₁` shift by Cauchy's estimate. -/
def ClosedShiftDiscTrace : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop, ∀ᵐ y ∂closedLaw b W np,
      ∀ w : ℂ, ‖w - boundaryZ b E‖ ≤ etaZ b E / 2 →
        ‖nearTraceAt W w (b3ClosedX b E s h τ m W (closeLen s W) y) -
            nearTraceAt W w (pathX b E W (closeLen s W) y.1.1)‖ ≤
          2 / (etaZ b E * W) *
            ∑ k, shiftKernel h (farEig b E W (closeLen s W) y.1.1 k) (phase y.2)

/-- **`FarFracTraceMoments`: fractional transmission moments at time `s`** (open path
law only): for every `p ≥ 1` there is `0 < α < 1/p` with
`E(Σ_k t_k^α)^p ≤ C` at length `n_s`, eventually in `W`. -/
def FarFracTraceMoments : Prop :=
  ∀ b E : ℝ, 0 < b → b < 1 / 2 → -2 < E → E < 2 → ∀ s : ℝ, 0 < s → ∀ p : ℝ, 1 ≤ p →
    ∃ α : ℝ, 0 < α ∧ α * p < 1 ∧ ∃ C : ℝ, ∀ᶠ W in atTop,
      ∫⁻ ω, ENNReal.ofReal (farFracTrace b E α W (closeLen s W) ω ^ p) ∂growthPathLaw W b ≤
        ENNReal.ofReal C

/-!
## The kernel bound
-/

/-- The constant of `shiftKernel_le`. -/
def kernelConst (h α : ℝ) : ℝ :=
  (2 / Real.sqrt (1 - h ^ 2)) ^ (1 - α) * (Real.sqrt (1 - h ^ 2) ^ 2) ^ (-α)

theorem norm_one_sub_mul_ge {z : ℂ} (hz : ‖z‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    1 - r ≤ ‖1 - z * (r : ℂ)‖ ∧ r * ‖1 - z‖ ≤ ‖1 - z * (r : ℂ)‖ := by
  have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at h
    nlinarith
  have hxle : z.re ≤ 1 := by nlinarith [sq_nonneg z.im]
  have hq2 : ‖1 - z * (r : ℂ)‖ ^ 2 = (1 - r * z.re) ^ 2 + (r * z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im]
    ring
  have hw2 : ‖1 - z‖ ^ 2 = (1 - z.re) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  have hq0 := norm_nonneg (1 - z * (r : ℂ))
  constructor
  · have h : (1 - r) ^ 2 ≤ ‖1 - z * (r : ℂ)‖ ^ 2 := by
      rw [hq2]; nlinarith
    exact (pow_le_pow_iff_left₀ (by linarith) hq0 (by norm_num)).1 h
  · have h : (r * ‖1 - z‖) ^ 2 ≤ ‖1 - z * (r : ℂ)‖ ^ 2 := by
      rw [hq2, mul_pow, hw2]; nlinarith [mul_nonneg hr0 (sub_nonneg.2 hr1)]
    exact (pow_le_pow_iff_left₀ (by positivity) hq0 (by norm_num)).1 h

/-- **The kernel bound**: `κ(t, z) ≤ c_{h,α} t^α |1 - z|^{-α}` for `|z| = 1`, `z ≠ 1`,
`0 < α ≤ 1`, `0 < h < 1`. -/
theorem shiftKernel_le {h α t : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    shiftKernel h t z ≤ kernelConst h α * max t 0 ^ α * ‖1 - z‖ ^ (-α) := by
  have hw : 0 < ‖1 - z‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hz1))
  have hh2 : h ^ 2 < 1 := by nlinarith
  set r₀ := Real.sqrt (1 - h ^ 2) with hr₀
  have hr₀0 : 0 < r₀ := Real.sqrt_pos.2 (by linarith)
  have hK0 : 0 ≤ kernelConst h α := by unfold kernelConst; positivity
  have hRHS : 0 ≤ kernelConst h α * max t 0 ^ α * ‖1 - z‖ ^ (-α) := by positivity
  unfold shiftKernel
  split_ifs with ht
  swap; · exact hRHS
  rcases le_or_gt t 0 with ht0 | ht0
  · rw [max_eq_right ht0, zero_div]; positivity
  rw [max_eq_left ht0.le]
  set r := Real.sqrt (1 - t) with hr
  have hr0 : r₀ ≤ r := Real.sqrt_le_sqrt (by linarith)
  have hrpos : 0 < r := lt_of_lt_of_le hr₀0 hr0
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr (by linarith) |>.trans_eq' rfl
  obtain ⟨hq1, hq2⟩ := norm_one_sub_mul_ge hz hrpos.le hr1
  set q := ‖1 - z * (r : ℂ)‖ with hq
  have hsq : r ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
  have h1r : t / 2 ≤ 1 - r := by nlinarith
  have hqpos : 0 < q := by linarith
  -- the two bounds
  have hA : t / (r * q) ≤ 2 / r₀ := by
    rw [div_le_div_iff₀ (by positivity) hr₀0]
    nlinarith [mul_le_mul hr0 (h1r.trans hq1) (by positivity) hrpos.le]
  have hB : t / (r * q) ≤ t / (r₀ ^ 2 * ‖1 - z‖) := by
    apply div_le_div_of_nonneg_left ht0.le (by positivity)
    have : r₀ ^ 2 * ‖1 - z‖ ≤ r * (r * ‖1 - z‖) := by
      have := mul_le_mul hr0 hr0 hr₀0.le hrpos.le
      nlinarith
    linarith [mul_le_mul_of_nonneg_left hq2 hrpos.le]
  -- interpolation `min(a,b) ≤ a^{1-α} b^α`
  set x := t / (r * q)
  have hx0 : 0 ≤ x := by positivity
  have hint : x ≤ (2 / r₀) ^ (1 - α) * (t / (r₀ ^ 2 * ‖1 - z‖)) ^ α := by
    calc x = x ^ (1 - α) * x ^ α := by
          rw [← Real.rpow_add' hx0 (by linarith), sub_add_cancel, Real.rpow_one]
      _ ≤ (2 / r₀) ^ (1 - α) * (t / (r₀ ^ 2 * ‖1 - z‖)) ^ α := by
          gcongr
  refine hint.trans (le_of_eq ?_)
  unfold kernelConst
  rw [← hr₀, Real.div_rpow ht0.le (by positivity), Real.mul_rpow (by positivity) hw.le,
    Real.rpow_neg (by positivity), Real.rpow_neg hw.le]
  field_simp

/-- The sum of kernels over the far spectrum. -/
theorem sum_shiftKernel_le {h α : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (t : Fin W → ℝ) :
    ∑ k, shiftKernel h (t k) z ≤ kernelConst h α * ‖1 - z‖ ^ (-α) * ∑ k, max (t k) 0 ^ α := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  calc shiftKernel h (t k) z ≤ kernelConst h α * max (t k) 0 ^ α * ‖1 - z‖ ^ (-α) :=
        shiftKernel_le hh0 hh1 hα0 hα1 hz hz1
    _ = kernelConst h α * ‖1 - z‖ ^ (-α) * max (t k) 0 ^ α := by ring

/-!
## The phase integral
-/

theorem norm_one_sub_phase (θ : ℝ) : ‖1 - phase θ‖ = |2 * Real.sin (θ / 2)| := by
  rw [norm_sub_rev, phase, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]

theorem phase_ne_one {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi)) : phase θ ≠ 1 := by
  intro h1
  have h := norm_one_sub_phase θ
  rw [h1, sub_self, norm_zero] at h
  have hs : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2])
  rw [abs_of_pos (by linarith)] at h
  linarith

theorem norm_phase (θ : ℝ) : ‖phase θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

/-- `|1 - e^{iθ}| ≥ (2/π) min(θ, 2π - θ)` on `(0, 2π)`. -/
theorem norm_one_sub_phase_ge {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    2 / Real.pi * min θ (2 * Real.pi - θ) ≤ ‖1 - phase θ‖ := by
  rw [norm_one_sub_phase]
  have hpi := Real.pi_pos
  rcases le_total θ Real.pi with hle | hle
  · have hs := Real.mul_le_sin (x := θ / 2) (by linarith [hθ.1]) (by linarith)
    have hs0 : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith)
    rw [abs_of_nonneg (by linarith)]
    have : min θ (2 * Real.pi - θ) ≤ θ := min_le_left _ _
    have h2 : 2 / Real.pi * min θ (2 * Real.pi - θ) ≤ 2 / Real.pi * θ :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : 2 / Real.pi * θ = 2 * (2 / Real.pi * (θ / 2)) := by ring
    linarith
  · have hs := Real.mul_le_sin (x := Real.pi - θ / 2) (by linarith [hθ.2]) (by linarith)
    rw [Real.sin_pi_sub] at hs
    have hs0 : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    rw [abs_of_nonneg (by linarith)]
    have : min θ (2 * Real.pi - θ) ≤ 2 * Real.pi - θ := min_le_right _ _
    have h2 : 2 / Real.pi * min θ (2 * Real.pi - θ) ≤ 2 / Real.pi * (2 * Real.pi - θ) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : 2 / Real.pi * (2 * Real.pi - θ) = 2 * (2 / Real.pi * (Real.pi - θ / 2)) := by ring
    linarith

theorem ae_phaseLaw_mem_Ioo : ∀ᵐ θ ∂phaseLaw, θ ∈ Ioo 0 (2 * Real.pi) := by
  refine Measure.ae_smul_measure ?_ _
  rw [ae_restrict_iff' measurableSet_Ico]
  have h0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, ofPred_eq_eq_singleton, Real.volume_singleton]
  filter_upwards [h0] with θ hθ hI
  exact ⟨lt_of_le_of_ne hI.1 (Ne.symm hθ), hI.2⟩

/-- **`E_θ|1 - e^{iθ}|^{-β} < ∞` for `0 ≤ β < 1`.** -/
theorem lintegral_phase_rpow_lt_top {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∫⁻ θ, ENNReal.ofReal (‖1 - phase θ‖ ^ (-β)) ∂phaseLaw < ∞ := by
  have hpi := Real.pi_pos
  set g : ℝ → ℝ := fun θ => (2 / Real.pi) ^ (-β) * (θ ^ (-β) + (2 * Real.pi - θ) ^ (-β))
  have hpt : ∀ θ ∈ Ioo 0 (2 * Real.pi), ‖1 - phase θ‖ ^ (-β) ≤ g θ := by
    intro θ hθ
    have hm : 0 < min θ (2 * Real.pi - θ) := lt_min hθ.1 (by linarith [hθ.2])
    have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) (norm_one_sub_phase_ge hθ)
      (by linarith : -β ≤ 0)
    refine h1.trans ?_
    rw [Real.mul_rpow (by positivity) hm.le]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rcases min_choice θ (2 * Real.pi - θ) with he | he <;> rw [he]
    · have := Real.rpow_nonneg (by linarith [hθ.2] : (0 : ℝ) ≤ 2 * Real.pi - θ) (-β)
      linarith
    · have := Real.rpow_nonneg hθ.1.le (-β)
      linarith
  have hgi : IntegrableOn g (Ioo 0 (2 * Real.pi)) := by
    have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-β)) volume 0 (2 * Real.pi) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h2 : IntervalIntegrable (fun x : ℝ => (2 * Real.pi - x) ^ (-β)) volume 0
        (2 * Real.pi) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 2 * Real.pi)
        (by linarith : -1 < -β)).comp_sub_left (2 * Real.pi)
      simpa using this.symm
    have h3 := (h1.add h2).const_mul ((2 / Real.pi) ^ (-β))
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)).1 h3
  have hgm : Measurable g := by
    unfold g
    exact measurable_const.mul ((measurable_id.pow_const _).add
      ((measurable_const.sub measurable_id).pow_const _))
  rw [phaseLaw, lintegral_smul_measure, setLIntegral_congr Ioo_ae_eq_Ico.symm]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  refine lt_of_le_of_lt (setLIntegral_mono hgm.ennreal_ofReal fun θ hθ =>
    ENNReal.ofReal_le_ofReal (hpt θ hθ)) ?_
  exact hgi.lintegral_lt_top

/-!
## The closing shift at the closing time in every `L^p`
-/

theorem measurable_nearTrace (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => (W : ℂ)⁻¹ * (passiveResolvent b E X).trace := by
  have hR : Measurable fun X : Matrix (Fin W) (Fin W) ℂ => passiveResolvent b E X := by
    refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
    simp only [Matrix.sub_apply]
    exact measurable_const.sub measurable_id.eval_matrix
  simp only [Matrix.trace, Matrix.diag]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hR.eval_matrix)

theorem measurable_pathX (b E : ℝ) (r : ℕ) : Measurable (pathX b E W r) := by
  have : pathX b E W r = pastX b E (fun _ => 0) W r ∘ pastCoords W r := by
    funext ω; simp only [Function.comp, pathNearSchur_eq_past]
  rw [this]
  exact (measurable_pastX b E (fun _ => 0) r).comp (measurable_pastCoords W r)

theorem measurable_jetShift_b3ClosedX (b E s h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (r : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ => jetShift b E (b3ClosedX b E s h τ m W r y) r y := by
  unfold jetShift
  exact (((measurable_nearTrace b E).comp (measurable_b3ClosedX b E s h τ m r)).sub
    ((measurable_nearTrace b E).comp
      ((measurable_pathX b E r).comp (measurable_fst.comp measurable_fst)))).norm

/-- Tonelli for a product of a path factor and a phase factor under the closed law (no
measurability needed for the upper bound). -/
theorem lintegral_closedLaw_mul_le (b : ℝ) (W np : ℕ) (G : GrowthPath W → ℝ≥0∞)
    (U : ℝ → ℝ≥0∞) (hG : ∀ ω, G ω ≠ ∞) (hU : ∫⁻ θ, U θ ∂phaseLaw ≠ ∞) :
    ∫⁻ y, G y.1.1 * U y.2 ∂closedLaw b W np ≤
      (∫⁻ ω, G ω ∂growthPathLaw W b) * ∫⁻ θ, U θ ∂phaseLaw := by
  have := isProbabilityMeasure_growthPathLaw W b
  refine (lintegral_prod_le _).trans ?_
  simp only [lintegral_const_mul' _ _ (hG _)]
  rw [lintegral_mul_const' _ _ hU]
  gcongr
  refine (lintegral_prod_le _).trans (le_of_eq ?_)
  simp only [lintegral_const, measure_univ, mul_one]

/-- **`ClosedJetShiftStartLp b3ClosedX` from the cavity-kernel bound and the fractional
moments.** -/
theorem closedJetShiftStartLp_of_frac (hA : ClosedShiftDiscTrace) (hB : FarFracTraceMoments) :
    ClosedJetShiftStartLp b3ClosedX := by
  intro b E np τ m T s h K Vs hF p hp
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, hh0, hh1, -⟩ := id hF
  obtain ⟨α, hα0, hαp, CF, hCF⟩ := hB b E hb0 hb hE1 hE2 s hs p hp
  have hp0 : 0 < p := by linarith
  have hα1 : α ≤ 1 := by nlinarith
  have hβ0 : 0 ≤ α * p := by positivity
  set Lθ := ∫⁻ θ, ENNReal.ofReal (‖1 - phase θ‖ ^ (-(α * p))) ∂phaseLaw with hLθ
  have hLθ' : Lθ < ∞ := lintegral_phase_rpow_lt_top hβ0 hαp
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  have hη : 0 < etaZ b E := lt_of_lt_of_le (etaLow_pos (by linarith : b < 1) hκ)
    (etaLow_le (by linarith : b < 1) hκ hEb)
  set kc := kernelConst h α
  have hkc : 0 ≤ kc := by unfold kc kernelConst; positivity
  set A0 := 2 / etaZ b E * kc
  have hA00 : 0 ≤ A0 := by positivity
  set X := max CF 0 * Lθ.toReal
  have hX0 : 0 ≤ X := mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg
  refine ⟨A0 * X ^ p⁻¹, ?_⟩
  filter_upwards [hA b E np τ m T s h K Vs hF, hCF, eventually_ge_atTop 1] with W hWA hWF hW1
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW1
  set n := closeLen s W
  set μ := closedLaw b W np
  set Δ : ProbedPath W np × ℝ → ℝ := fun y => jetShift b E (b3ClosedX b E s h τ m W n y) n y
  have hΔm : Measurable Δ := measurable_jetShift_b3ClosedX b E s h τ m n
  have hΔ0 : ∀ y, 0 ≤ Δ y := fun y => norm_nonneg _
  set F : GrowthPath W → ℝ := fun ω => farFracTrace b E α W n ω
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => Finset.sum_nonneg fun k _ => by positivity
  set A := A0 / W
  have hA0 : 0 ≤ A := by positivity
  -- the pointwise bound, a.e.
  have hph : ∀ᵐ y ∂μ, y.2 ∈ Ioo 0 (2 * Real.pi) := by
    rw [ae_iff]
    have : {y : ProbedPath W np × ℝ | ¬ y.2 ∈ Ioo 0 (2 * Real.pi)} =
        Set.univ ×ˢ {θ | ¬ θ ∈ Ioo 0 (2 * Real.pi)} := by ext y; simp
    rw [this, Measure.prod_prod, ← ae_iff.1 ae_phaseLaw_mem_Ioo, mul_comm]
    simp
  have hpt : ∀ᵐ y ∂μ, Δ y ≤ A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
    filter_upwards [hWA, hph] with y hy hθ
    have hy' := hy (boundaryZ b E) (by rw [sub_self, norm_zero]; positivity)
    rw [← jetShift_eq_nearTraceAt] at hy'
    refine hy'.trans ?_
    have hS := sum_shiftKernel_le hh0 hh1 hα0 hα1 (norm_phase y.2) (phase_ne_one hθ)
      (farEig b E W n y.1.1)
    have hw : 0 ≤ ‖1 - phase y.2‖ ^ (-α) := Real.rpow_nonneg (norm_nonneg _) _
    calc 2 / (etaZ b E * W) * ∑ k, shiftKernel h (farEig b E W n y.1.1 k) (phase y.2)
        ≤ 2 / (etaZ b E * W) * (kc * ‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
          gcongr; exact hS
      _ = A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
          simp only [A, A0]; field_simp
  -- the `p`-th moment
  have hpow : ∀ᵐ y ∂μ, ‖Δ y‖ₑ ^ p ≤ ENNReal.ofReal (A ^ p) *
      (ENNReal.ofReal (F y.1.1 ^ p) * ENNReal.ofReal (‖1 - phase y.2‖ ^ (-(α * p)))) := by
    filter_upwards [hpt] with y hy
    rw [Real.enorm_eq_ofReal (hΔ0 y), ENNReal.ofReal_rpow_of_nonneg (hΔ0 y) hp0.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hF0 _) p),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hA0 p)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw : 0 ≤ ‖1 - phase y.2‖ ^ (-α) := Real.rpow_nonneg (norm_nonneg _) _
    calc Δ y ^ p ≤ (A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1)) ^ p :=
          Real.rpow_le_rpow (hΔ0 y) hy hp0.le
      _ = A ^ p * (F y.1.1 ^ p * ‖1 - phase y.2‖ ^ (-(α * p))) := by
          rw [Real.mul_rpow hA0 (mul_nonneg hw (hF0 _)), Real.mul_rpow hw (hF0 _),
            ← Real.rpow_mul (norm_nonneg _), neg_mul]
          ring
  have hint : ∫⁻ y, ‖Δ y‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (A ^ p) * (ENNReal.ofReal (max CF 0) * Lθ) := by
    refine (lintegral_mono_ae hpow).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    refine (lintegral_closedLaw_mul_le b W np (fun ω => ENNReal.ofReal (F ω ^ p))
      (fun θ => ENNReal.ofReal (‖1 - phase θ‖ ^ (-(α * p)))) (fun _ => ENNReal.ofReal_ne_top)
      hLθ'.ne).trans ?_
    gcongr
    exact hWF.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hLθeq : Lθ = ENNReal.ofReal Lθ.toReal := (ENNReal.ofReal_toReal hLθ'.ne).symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
    hΔm.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  calc (∫⁻ y, ‖Δ y‖ₑ ^ p ∂μ) ^ (1 / p)
      ≤ (ENNReal.ofReal (A ^ p) * (ENNReal.ofReal (max CF 0) * Lθ)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = ENNReal.ofReal (A * X ^ p⁻¹) := by
        rw [hLθeq, ← ENNReal.ofReal_mul (le_max_right _ _), ← ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hA0,
          mul_one_div_cancel hp0.ne', Real.rpow_one, one_div]
    _ = ENNReal.ofReal (A0 * X ^ p⁻¹ / W) := by
        congr 1; simp only [A]; ring

/-- **The disc-uniform closing shift is dominated in every `L^p`** (for the `δ₁` shift by
Cauchy's estimate): there is `B` with, a.e., `|W⁻¹Tr(w - X_cl)⁻¹ - W⁻¹Tr(w - X_open)⁻¹| ≤ B` on
`|w - z_∂| ≤ η/2` and `E B^p ≤ (C/W)^p`. -/
theorem closedShiftDisc_dominated (hA : ClosedShiftDiscTrace) (hB : FarFracTraceMoments) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop,
        ∃ B : ProbedPath W np × ℝ → ℝ, (∀ y, 0 ≤ B y) ∧
          (∀ᵐ y ∂closedLaw b W np, ∀ w : ℂ, ‖w - boundaryZ b E‖ ≤ etaZ b E / 2 →
            ‖nearTraceAt W w (b3ClosedX b E s h τ m W (closeLen s W) y) -
              nearTraceAt W w (pathX b E W (closeLen s W) y.1.1)‖ ≤ B y) ∧
          ∫⁻ y, ENNReal.ofReal (B y ^ p) ∂closedLaw b W np ≤ ENNReal.ofReal ((C / W) ^ p) := by
  intro b E np τ m T s h K Vs hF p hp
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, hh0, hh1, -⟩ := id hF
  obtain ⟨α, hα0, hαp, CF, hCF⟩ := hB b E hb0 hb hE1 hE2 s hs p hp
  have hp0 : 0 < p := by linarith
  have hα1 : α ≤ 1 := by nlinarith
  have hβ0 : 0 ≤ α * p := by positivity
  set Lθ := ∫⁻ θ, ENNReal.ofReal (‖1 - phase θ‖ ^ (-(α * p))) ∂phaseLaw with hLθ
  have hLθ' : Lθ < ∞ := lintegral_phase_rpow_lt_top hβ0 hαp
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  have hη : 0 < etaZ b E := lt_of_lt_of_le (etaLow_pos (by linarith : b < 1) hκ)
    (etaLow_le (by linarith : b < 1) hκ hEb)
  set kc := kernelConst h α
  have hkc : 0 ≤ kc := by unfold kc kernelConst; positivity
  set A0 := 2 / etaZ b E * kc
  have hA00 : 0 ≤ A0 := by positivity
  set X := max CF 0 * Lθ.toReal
  have hX0 : 0 ≤ X := mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg
  refine ⟨A0 * X ^ p⁻¹, by positivity, ?_⟩
  filter_upwards [hA b E np τ m T s h K Vs hF, hCF, eventually_ge_atTop 1] with W hWA hWF hW1
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW1
  set n := closeLen s W
  set μ := closedLaw b W np
  set A := A0 / W
  have hA0 : 0 ≤ A := by positivity
  set F : GrowthPath W → ℝ := fun ω => farFracTrace b E α W n ω
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => Finset.sum_nonneg fun k _ => by positivity
  set B : ProbedPath W np × ℝ → ℝ := fun y =>
    2 / (etaZ b E * W) * ∑ k, shiftKernel h (farEig b E W n y.1.1 k) (phase y.2)
  have hker0 : ∀ t z, 0 ≤ shiftKernel h t z := fun t z => by
    unfold shiftKernel; split_ifs <;> positivity
  have hB0 : ∀ y, 0 ≤ B y := fun y =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hker0 _ _)
  refine ⟨B, hB0, hWA, ?_⟩
  have hph : ∀ᵐ y ∂μ, y.2 ∈ Ioo 0 (2 * Real.pi) := by
    rw [ae_iff]
    have : {y : ProbedPath W np × ℝ | ¬ y.2 ∈ Ioo 0 (2 * Real.pi)} =
        Set.univ ×ˢ {θ | ¬ θ ∈ Ioo 0 (2 * Real.pi)} := by ext y; simp
    rw [this, Measure.prod_prod, ← ae_iff.1 ae_phaseLaw_mem_Ioo, mul_comm]
    simp
  have hpt : ∀ᵐ y ∂μ, B y ^ p ≤ A ^ p * (F y.1.1 ^ p * ‖1 - phase y.2‖ ^ (-(α * p))) := by
    filter_upwards [hph] with y hθ
    have hS := sum_shiftKernel_le hh0 hh1 hα0 hα1 (norm_phase y.2) (phase_ne_one hθ)
      (farEig b E W n y.1.1)
    have hw : 0 ≤ ‖1 - phase y.2‖ ^ (-α) := Real.rpow_nonneg (norm_nonneg _) _
    have hBle : B y ≤ A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
      calc B y ≤ 2 / (etaZ b E * W) * (kc * ‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
            simp only [B]; gcongr; exact hS
        _ = A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
            simp only [A, A0]; field_simp
    calc B y ^ p ≤ (A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1)) ^ p :=
          Real.rpow_le_rpow (hB0 y) hBle hp0.le
      _ = A ^ p * (F y.1.1 ^ p * ‖1 - phase y.2‖ ^ (-(α * p))) := by
          rw [Real.mul_rpow hA0 (mul_nonneg hw (hF0 _)), Real.mul_rpow hw (hF0 _),
            ← Real.rpow_mul (norm_nonneg _), neg_mul]
          ring
  have hint : ∫⁻ y, ENNReal.ofReal (B y ^ p) ∂μ ≤
      ENNReal.ofReal (A ^ p) * (ENNReal.ofReal (max CF 0) * Lθ) := by
    refine (lintegral_mono_ae (hpt.mono fun y hy => (ENNReal.ofReal_le_ofReal hy).trans
      (le_of_eq (by rw [ENNReal.ofReal_mul (Real.rpow_nonneg hA0 p),
        ENNReal.ofReal_mul (Real.rpow_nonneg (hF0 _) p)]))
      )).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    refine (lintegral_closedLaw_mul_le b W np (fun ω => ENNReal.ofReal (F ω ^ p))
      (fun θ => ENNReal.ofReal (‖1 - phase θ‖ ^ (-(α * p)))) (fun _ => ENNReal.ofReal_ne_top)
      hLθ'.ne).trans ?_
    gcongr
    exact hWF.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  refine hint.trans (le_of_eq ?_)
  rw [(ENNReal.ofReal_toReal hLθ'.ne).symm, ← ENNReal.ofReal_mul (le_max_right _ _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_div_right_comm, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hX0,
    inv_mul_cancel₀ hp0.ne', Real.rpow_one]

/-- **`ClosedJet0Fam` from the contract hypotheses and four named estimates**: passivity and the
one-port recursion of `b3ClosedX`, the cavity-kernel bound at the closing time (exact algebra) and
the fractional transmission moments at time `s` (open path law). -/
theorem closedJet0Fam_of_frac (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : ClosedInputPassive b3ClosedX)
    (hRec : ClosedInputRecursion b3ClosedX) (hA : ClosedShiftDiscTrace)
    (hB : FarFracTraceMoments) : ClosedJet0Fam :=
  closedJet0Fam_of_shift hMT hGA hLp hP hRec (closedJetShiftStartLp_of_frac hA hB)

end BlockBand.SourceProcess.PhysApprox.B3.Jet
