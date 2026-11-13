module

public import BlockBand.SourceProcess.LengthCont.OneLayer.PastMoments
public import BlockBand.SourceProcess.LengthCont.OneLayer.PastArith

/-!
# The past integrals of the fresh sizes are `O(1/W)`

From the pointwise bounds of `PastArith` and the moments
`∫δ₀^q ≤ (D_q/W)^q`, `∫‖f‖^r ≤ F_r`, `∫H^p ≤ H_p` on `probedPathLaw`:

* `drift_integral`: `∫ |μ_{ik}| α ≤ C_d/W`;
* `var_integral`: `∫ (|μ_{ik}| σ)² ≤ C_v/W`,
with `C_d, C_v` explicit in the moment constants (independent of `W` and `n`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.RawTag
open scoped ENNReal

section General

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lint_cmul {c B : ℝ} (hc : 0 ≤ c) (u : α → ℝ)
    (h : ∫⁻ x, ENNReal.ofReal (u x) ∂μ ≤ ENNReal.ofReal B) :
    ∫⁻ x, ENNReal.ofReal (c * u x) ∂μ ≤ ENNReal.ofReal (c * B) := by
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul_right h _

theorem lint_add {f g : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal a)
    (h2 : ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal b) :
    ∫⁻ x, ENNReal.ofReal (f x + g x) ∂μ ≤ ENNReal.ofReal (a + b) := by
  simp_rw [ENNReal.ofReal_add (hf0 _) (hg0 _)]
  rw [lintegral_add_left hf.ennreal_ofReal, ENNReal.ofReal_add ha hb]
  exact add_le_add h1 h2

theorem lint_const [IsProbabilityMeasure μ] (c : ℝ) :
    ∫⁻ _x, ENNReal.ofReal c ∂μ = ENNReal.ofReal c := by
  rw [lintegral_const, measure_univ, mul_one]

end General

variable {W : ℕ}

theorem norm_massF_le {np : ℕ} (m : Fin np → ℝ) (hm : ∀ j, 0 ≤ m j) (i k : Fin np) :
    ‖massF m i k‖ ≤ ∑ j, m j := by
  have hi := Real.sqrt_nonneg (m i)
  have hk := Real.sqrt_nonneg (m k)
  rw [massF, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hi hk)]
  have h1 : Real.sqrt (m i) * Real.sqrt (m k) ≤ (m i + m k) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (m i) - Real.sqrt (m k)), Real.sq_sqrt (hm i),
      Real.sq_sqrt (hm k)]
  have hmi := hm i
  have hmk := hm k
  by_cases h : i = k
  · subst h
    have := Finset.single_le_sum (fun j _ => hm j) (Finset.mem_univ i)
    linarith
  · have := Finset.add_le_sum (f := m) (fun j _ => hm j) (Finset.mem_univ i)
      (Finset.mem_univ k) h
    linarith

/-- **The drift integral.** -/
theorem drift_integral {np : ℕ} (b E : ℝ) (W n : ℕ) (τ m : Fin np → ℝ) (i k : Fin np)
    {Cm Cf M D2 D4 F8 H4 : ℝ} (hW : 1 ≤ W) (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf)
    (hμM : ‖massF m i k‖ ≤ M) (hF8 : 0 ≤ F8) (hH4 : 0 ≤ H4)
    (hd2 : ∫⁻ x, ENNReal.ofReal (jetDistance0 b E (pathX b E W n x.1) ^ 2)
      ∂probedPathLaw W np b ≤ ENNReal.ofReal ((D2 / W) ^ 2))
    (hd4 : ∫⁻ x, ENNReal.ofReal (jetDistance0 b E (pathX b E W n x.1) ^ 4)
      ∂probedPathLaw W np b ≤ ENNReal.ofReal ((D4 / W) ^ 4))
    (hfi : ∫⁻ x, ENNReal.ofReal (vecNorm (frame b E W n (birth W τ i) x.1 (x.2 i)) ^ 8)
      ∂probedPathLaw W np b ≤ ENNReal.ofReal F8)
    (hfk : ∫⁻ x, ENNReal.ofReal (vecNorm (frame b E W n (birth W τ k) x.1 (x.2 k)) ^ 8)
      ∂probedPathLaw W np b ≤ ENNReal.ofReal F8)
    (hh : ∫⁻ x, ENNReal.ofReal (hFun b E W n x.1 ^ 4) ∂probedPathLaw W np b ≤
      ENNReal.ofReal H4) :
    ∫⁻ x, ENNReal.ofReal (‖massF m i k‖ * alphaFun b E W n τ i k Cm Cf x.1 x.2)
        ∂probedPathLaw W np b ≤
      ENNReal.ofReal (M * sizeK b E * (Cm + 2 * (Cm + Cf) ^ 2) *
        (3 / 2 * D2 ^ 2 + 3 / 2 * D4 ^ 4 + 3 / 2 + 128 * F8 + 1 / 4 * H4) / W) := by
  set μ := probedPathLaw W np b
  have : IsProbabilityMeasure μ := by
    rw [show μ = (growthPathLaw W b).prod (Measure.pi fun _ : Fin np =>
      BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin W)) from rfl]
    infer_instance
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hμM
  have hK : 0 ≤ sizeK b E := by unfold sizeK; positivity
  set d : ProbedPath W np → ℝ := fun x => jetDistance0 b E (pathX b E W n x.1)
  set fi : ProbedPath W np → ℝ := fun x => vecNorm (frame b E W n (birth W τ i) x.1 (x.2 i))
  set fk : ProbedPath W np → ℝ := fun x => vecNorm (frame b E W n (birth W τ k) x.1 (x.2 k))
  set H : ProbedPath W np → ℝ := fun x => hFun b E W n x.1
  have hdm : Measurable d := (measurable_delta b E n).comp measurable_fst
  have hfim : Measurable fi := by
    have := measurable_frame (W := W) b E n (birth W τ i) measurable_fst
      (show Measurable fun x : ProbedPath W np => x.2 i from
        (measurable_pi_apply i).comp measurable_snd)
    simp only [fi]; unfold vecNorm; fun_prop
  have hfkm : Measurable fk := by
    have := measurable_frame (W := W) b E n (birth W τ k) measurable_fst
      (show Measurable fun x : ProbedPath W np => x.2 k from
        (measurable_pi_apply k).comp measurable_snd)
    simp only [fk]; unfold vecNorm; fun_prop
  have hHm : Measurable H := (measurable_hFun b E n).comp measurable_fst
  have hd0 : ∀ x, 0 ≤ d x := fun x => norm_nonneg _
  have hfi0 : ∀ x, 0 ≤ fi x := fun x => vecNorm_nonneg _
  have hfk0 : ∀ x, 0 ≤ fk x := fun x => vecNorm_nonneg _
  have hH0 : ∀ x, 0 ≤ H x := fun x => by
    simp only [H, hFun]
    linarith [hsA_nonneg (boundaryResolvent b E W n x.1),
      hsB_nonneg (boundaryResolvent b E W n x.1)]
  set c := M * sizeK b E * (Cm + 2 * (Cm + Cf) ^ 2)
  have hc : 0 ≤ c := by positivity
  -- pointwise
  have hpt : ∀ x, ‖massF m i k‖ * alphaFun b E W n τ i k Cm Cf x.1 x.2 ≤
      c * (3 / 2 * ((W : ℝ) * d x ^ 2) + 3 / 2 * ((W : ℝ) * d x ^ 4) + 3 / 2 * (W : ℝ)⁻¹ +
        64 * ((W : ℝ)⁻¹ * fi x ^ 8) + 64 * ((W : ℝ)⁻¹ * fk x ^ 8) +
        1 / 4 * ((W : ℝ)⁻¹ * H x ^ 4)) := fun x =>
    drift_pointwise hWr (hd0 x) (hfi0 x) (hfk0 x) (hH0 x) hCm hCf hK (norm_nonneg _) hμM
  -- the six integrals
  have i1 := lint_cmul (μ := μ) (c := 3 / 2 * (W : ℝ)) (by positivity) (fun x => d x ^ 2) hd2
  have i2 := lint_cmul (μ := μ) (c := 3 / 2 * (W : ℝ)) (by positivity) (fun x => d x ^ 4) hd4
  have i4 := lint_cmul (μ := μ) (c := 64 * (W : ℝ)⁻¹) (by positivity) (fun x => fi x ^ 8) hfi
  have i5 := lint_cmul (μ := μ) (c := 64 * (W : ℝ)⁻¹) (by positivity) (fun x => fk x ^ 8) hfk
  have i6 := lint_cmul (μ := μ) (c := 1 / 4 * (W : ℝ)⁻¹) (by positivity) (fun x => H x ^ 4) hh
  have i3 : ∫⁻ _x, ENNReal.ofReal (3 / 2 * (W : ℝ)⁻¹) ∂μ ≤ ENNReal.ofReal (3 / 2 * (W : ℝ)⁻¹) :=
    (lint_const _).le
  have s12 := lint_add (μ := μ) (f := fun x => 3 / 2 * (W : ℝ) * d x ^ 2)
    (g := fun x => 3 / 2 * (W : ℝ) * d x ^ 4) (by fun_prop) (fun x => by have := hd0 x; positivity)
    (fun x => by have := hd0 x; positivity) (by positivity) (by positivity) i1 i2
  have s123 := lint_add (μ := μ) (by fun_prop) (fun x => by have := hd0 x; positivity)
    (fun _ => by positivity) (by positivity) (by positivity) s12 i3
  have s4 := lint_add (μ := μ) (by fun_prop) (fun x => by have := hd0 x; positivity)
    (fun x => by have := hfi0 x; positivity) (by positivity) (by positivity) s123 i4
  have s5 := lint_add (μ := μ) (by fun_prop)
    (fun x => by have := hd0 x; have := hfi0 x; positivity)
    (fun x => by have := hfk0 x; positivity) (by positivity) (by positivity) s4 i5
  have s6 := lint_add (μ := μ) (by fun_prop)
    (fun x => by have := hd0 x; have := hfi0 x; have := hfk0 x; positivity)
    (fun x => by have := hH0 x; positivity) (by positivity) (by positivity) s5 i6
  have sall := lint_cmul (μ := μ) hc _ s6
  refine (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ((hpt x).trans (le_of_eq ?_))).trans
    (sall.trans (ENNReal.ofReal_le_ofReal ?_))
  · ring
  · have e1 : 3 / 2 * (W : ℝ) * (D2 / W) ^ 2 = 3 / 2 * D2 ^ 2 / W := by field_simp
    have e2 : 3 / 2 * (W : ℝ) * (D4 / W) ^ 4 ≤ 3 / 2 * D4 ^ 4 / W := by
      have e : 3 / 2 * (W : ℝ) * (D4 / W) ^ 4 = 3 / 2 * D4 ^ 4 / (W : ℝ) ^ 3 := by
        field_simp
      rw [e]
      refine div_le_div_of_nonneg_left (by positivity) hW0 ?_
      calc (W : ℝ) = (W : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (W : ℝ) ^ 3 := pow_le_pow_right₀ hWr (by norm_num)
    rw [show M * sizeK b E * (Cm + 2 * (Cm + Cf) ^ 2) *
        (3 / 2 * D2 ^ 2 + 3 / 2 * D4 ^ 4 + 3 / 2 + 128 * F8 + 1 / 4 * H4) / W =
        c * ((3 / 2 * D2 ^ 2 + 3 / 2 * D4 ^ 4 + 3 / 2 + 128 * F8 + 1 / 4 * H4) / W) by
      simp only [c]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hc
    have e3 : (3 / 2 * D2 ^ 2 + 3 / 2 * D4 ^ 4 + 3 / 2 + 128 * F8 + 1 / 4 * H4) / W =
        3 / 2 * D2 ^ 2 / W + 3 / 2 * D4 ^ 4 / W + 3 / 2 * (W : ℝ)⁻¹ + 64 * (W : ℝ)⁻¹ * F8 +
          64 * (W : ℝ)⁻¹ * F8 + 1 / 4 * (W : ℝ)⁻¹ * H4 := by field_simp; ring
    rw [e3, e1]
    linarith

/-- **The variance integral.** -/
theorem var_integral {np : ℕ} (b E : ℝ) (W n : ℕ) (τ m : Fin np → ℝ) (i k : Fin np)
    {Cm Cf M D4 D8 F16 H8 : ℝ} (hW : 1 ≤ W) (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf)
    (hμM : ‖massF m i k‖ ≤ M) (hD4 : 0 ≤ D4) (hD8 : 0 ≤ D8) (hF16 : 0 ≤ F16) (hH8 : 0 ≤ H8)
    (hd4 : ∫⁻ x, ENNReal.ofReal (jetDistance0 b E (pathX b E W n x.1) ^ 4)
      ∂probedPathLaw W np b ≤ ENNReal.ofReal ((D4 / W) ^ 4))
    (hd8 : ∫⁻ x, ENNReal.ofReal (jetDistance0 b E (pathX b E W n x.1) ^ 8)
      ∂probedPathLaw W np b ≤ ENNReal.ofReal ((D8 / W) ^ 8))
    (hfi : ∫⁻ x, ENNReal.ofReal (vecNorm (frame b E W n (birth W τ i) x.1 (x.2 i)) ^ 16)
      ∂probedPathLaw W np b ≤ ENNReal.ofReal F16)
    (hfk : ∫⁻ x, ENNReal.ofReal (vecNorm (frame b E W n (birth W τ k) x.1 (x.2 k)) ^ 16)
      ∂probedPathLaw W np b ≤ ENNReal.ofReal F16)
    (hh : ∫⁻ x, ENNReal.ofReal (hFun b E W n x.1 ^ 8) ∂probedPathLaw W np b ≤
      ENNReal.ofReal H8) :
    ∫⁻ x, ENNReal.ofReal ((‖massF m i k‖ * sigmaFun b E W n τ i k Cm Cf x.1 x.2) ^ 2)
        ∂probedPathLaw W np b ≤
      ENNReal.ofReal (3 * M ^ 2 * sizeK b E ^ 2 * (Cf + 2 * (Cm + Cf) ^ 2) ^ 2 *
        (3 / 2 + 3 / 2 * D4 ^ 4 + 3 / 2 * D8 ^ 8 + 2 ^ 15 * F16 + 1 / 4 * H8) / W) := by
  set μ := probedPathLaw W np b
  have : IsProbabilityMeasure μ := by
    rw [show μ = (growthPathLaw W b).prod (Measure.pi fun _ : Fin np =>
      BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin W)) from rfl]
    infer_instance
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set d : ProbedPath W np → ℝ := fun x => jetDistance0 b E (pathX b E W n x.1)
  set fi : ProbedPath W np → ℝ := fun x => vecNorm (frame b E W n (birth W τ i) x.1 (x.2 i))
  set fk : ProbedPath W np → ℝ := fun x => vecNorm (frame b E W n (birth W τ k) x.1 (x.2 k))
  set H : ProbedPath W np → ℝ := fun x => hFun b E W n x.1
  have hdm : Measurable d := (measurable_delta b E n).comp measurable_fst
  have hfim : Measurable fi := by
    have := measurable_frame (W := W) b E n (birth W τ i) measurable_fst
      (show Measurable fun x : ProbedPath W np => x.2 i from
        (measurable_pi_apply i).comp measurable_snd)
    simp only [fi]; unfold vecNorm; fun_prop
  have hHm : Measurable H := (measurable_hFun b E n).comp measurable_fst
  have hd0 : ∀ x, 0 ≤ d x := fun x => norm_nonneg _
  have hfi0 : ∀ x, 0 ≤ fi x := fun x => vecNorm_nonneg _
  have hfk0 : ∀ x, 0 ≤ fk x := fun x => vecNorm_nonneg _
  have hH0 : ∀ x, 0 ≤ H x := fun x => by
    simp only [H, hFun]
    linarith [hsA_nonneg (boundaryResolvent b E W n x.1),
      hsB_nonneg (boundaryResolvent b E W n x.1)]
  set c := 3 * M ^ 2 * sizeK b E ^ 2 * (Cf + 2 * (Cm + Cf) ^ 2) ^ 2
  have hc : 0 ≤ c := by positivity
  have hpt : ∀ x, (‖massF m i k‖ * sigmaFun b E W n τ i k Cm Cf x.1 x.2) ^ 2 ≤
      c * (3 / 2 * (W : ℝ)⁻¹ + 3 / 2 * ((W : ℝ) * d x ^ 4) + 3 / 2 * ((W : ℝ) * d x ^ 8) +
        2 ^ 14 * ((W : ℝ)⁻¹ * fi x ^ 16) + 2 ^ 14 * ((W : ℝ)⁻¹ * fk x ^ 16) +
        1 / 4 * ((W : ℝ)⁻¹ * H x ^ 8)) := fun x =>
    var_pointwise hWr (hd0 x) (hfi0 x) (hfk0 x) hCm hCf (norm_nonneg _) hμM
  have i1 : ∫⁻ _x, ENNReal.ofReal (3 / 2 * (W : ℝ)⁻¹) ∂μ ≤ ENNReal.ofReal (3 / 2 * (W : ℝ)⁻¹) :=
    (lint_const _).le
  have i2 := lint_cmul (μ := μ) (c := 3 / 2 * (W : ℝ)) (by positivity) (fun x => d x ^ 4) hd4
  have i3 := lint_cmul (μ := μ) (c := 3 / 2 * (W : ℝ)) (by positivity) (fun x => d x ^ 8) hd8
  have i4 := lint_cmul (μ := μ) (c := 2 ^ 14 * (W : ℝ)⁻¹) (by positivity) (fun x => fi x ^ 16) hfi
  have i5 := lint_cmul (μ := μ) (c := 2 ^ 14 * (W : ℝ)⁻¹) (by positivity) (fun x => fk x ^ 16) hfk
  have i6 := lint_cmul (μ := μ) (c := 1 / 4 * (W : ℝ)⁻¹) (by positivity) (fun x => H x ^ 8) hh
  have s12 := lint_add (μ := μ) (f := fun _ => 3 / 2 * (W : ℝ)⁻¹)
    (g := fun x => 3 / 2 * (W : ℝ) * d x ^ 4) measurable_const (fun _ => by positivity)
    (fun x => by have := hd0 x; positivity) (by positivity) (by positivity) i1 i2
  have s123 := lint_add (μ := μ) (by fun_prop) (fun x => by have := hd0 x; positivity)
    (fun x => by have := hd0 x; positivity) (by positivity) (by positivity) s12 i3
  have s4 := lint_add (μ := μ) (by fun_prop) (fun x => by have := hd0 x; positivity)
    (fun x => by have := hfi0 x; positivity) (by positivity) (by positivity) s123 i4
  have s5 := lint_add (μ := μ) (by fun_prop)
    (fun x => by have := hd0 x; have := hfi0 x; positivity)
    (fun x => by have := hfk0 x; positivity) (by positivity) (by positivity) s4 i5
  have hfkm : Measurable fk := by
    have := measurable_frame (W := W) b E n (birth W τ k) measurable_fst
      (show Measurable fun x : ProbedPath W np => x.2 k from
        (measurable_pi_apply k).comp measurable_snd)
    simp only [fk]; unfold vecNorm; fun_prop
  have s6 := lint_add (μ := μ) (by fun_prop)
    (fun x => by have := hd0 x; have := hfi0 x; have := hfk0 x; positivity)
    (fun x => by have := hH0 x; positivity) (by positivity) (by positivity) s5 i6
  have sall := lint_cmul (μ := μ) hc _ s6
  refine (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ((hpt x).trans (le_of_eq ?_))).trans
    (sall.trans (ENNReal.ofReal_le_ofReal ?_))
  · ring
  · have e2 : ∀ (D : ℝ) (q : ℕ), 2 ≤ q → 0 ≤ D →
        3 / 2 * (W : ℝ) * (D / W) ^ q ≤ 3 / 2 * D ^ q / W := by
      intro D q hq hD
      have e : 3 / 2 * (W : ℝ) * (D / W) ^ q = 3 / 2 * D ^ q / (W : ℝ) ^ (q - 1) := by
        rw [div_pow]
        have : (W : ℝ) ^ q = (W : ℝ) * (W : ℝ) ^ (q - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [this]; field_simp
      rw [e]
      refine div_le_div_of_nonneg_left (by positivity) hW0 ?_
      calc (W : ℝ) = (W : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (W : ℝ) ^ (q - 1) := pow_le_pow_right₀ hWr (Nat.le_sub_of_add_le hq)
    have hD4' := e2 D4 4 (by norm_num) hD4
    have hD8' := e2 D8 8 (by norm_num) hD8
    rw [show 3 * M ^ 2 * sizeK b E ^ 2 * (Cf + 2 * (Cm + Cf) ^ 2) ^ 2 *
        (3 / 2 + 3 / 2 * D4 ^ 4 + 3 / 2 * D8 ^ 8 + 2 ^ 15 * F16 + 1 / 4 * H8) / W =
        c * ((3 / 2 + 3 / 2 * D4 ^ 4 + 3 / 2 * D8 ^ 8 + 2 ^ 15 * F16 + 1 / 4 * H8) / W) by
      simp only [c]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hc
    have e3 : (3 / 2 + 3 / 2 * D4 ^ 4 + 3 / 2 * D8 ^ 8 + 2 ^ 15 * F16 + 1 / 4 * H8) / W =
        3 / 2 * (W : ℝ)⁻¹ + 3 / 2 * D4 ^ 4 / W + 3 / 2 * D8 ^ 8 / W + 2 ^ 14 * (W : ℝ)⁻¹ * F16 +
          2 ^ 14 * (W : ℝ)⁻¹ * F16 + 1 / 4 * (W : ℝ)⁻¹ * H8 := by field_simp; ring
    rw [e3]
    linarith

end BlockBand.SourceProcess.LengthCont.OneLayer
