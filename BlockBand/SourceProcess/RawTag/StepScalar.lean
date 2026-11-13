module

public import BlockBand.SourceProcess.RawTag.StepBound
public import BlockBand.SourceProcess.RawTag.StepArith

/-!
# The scalar recursion `e_{l+1} ≤ e^{α/W}e_l + β/W`

`step_scalar`: if the raw form is updated at step `l` by `nearL*Δ nearR`, the fresh mean of `Δ`
is `O(δ₀ + W⁻¹)` and its centred bilinear forms are `O(W^{-1/2} + δ₀)` in `L^{4m}`, then the
`4m`-th moments `e_l` of the raw form satisfy `e_{l+1} ≤ e^{α/W}e_l + β/W` with `β = stepBeta`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource
open scoped Matrix ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The constant `β` of the scalar recursion. -/
def stepBeta (m : ℕ) (Cm Cf Cδ A : ℝ) : ℝ :=
  ((1 + stepK (2 * m)) * 2 ^ (4 * m) * Cm ^ (4 * m) + stepK (2 * m) * Cf ^ (4 * m)) *
    ((Cδ + 1) * A * A) ^ (4 * m)

theorem lintegral_pow_le_of_momBd' {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {n : ℕ} (hn : 1 ≤ n) {C : ℝ} (hf : MomBd μ f n C) (hC : 0 ≤ C) (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x ^ n) ∂μ ≤ ENNReal.ofReal (C ^ n) := by
  have h := lintegral_rpow_le_of_momBd hf (by exact_mod_cast hn) hC
  simp only [abs_of_nonneg (hf0 _), Real.rpow_natCast] at h
  exact h

/-- **The scalar recursion.** -/
theorem step_scalar {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {l β₁ β₂ : ℕ}
    {Γ : Type} [MeasurableSpace Γ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    {g₁ g₂ : Γ → Fin W → ℂ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) {m : ℕ} (hm : 1 ≤ m)
    (hW : (1 : ℝ) ≤ W) {Cm Cf Cδ A : ℝ} (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf) (hCδ : 0 ≤ Cδ) (hA : 0 ≤ A)
    (hupd : ∀ᵐ ω ∂growthPathLaw W b, ∀ g h : Fin W → ℂ,
      rawForm b E W (l + 1) β₁ β₂ ω g h = rawForm b E W l β₁ β₂ ω g h +
        bilinear (nearL b E W l β₁ ω g) (stepDelta b E W l ω) (nearR b E W l β₂ ω h))
    (hI : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ x y, Integrable (fun f => freshDelta b E X f x y) (freshLaw W b))
    (hmean : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤ Cm * (jetDistance0 b E X + (W : ℝ)⁻¹))
    (hF : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
      eLpNorm (fun f => bilinear u (freshDelta b E X f -
          matrixExpect (freshLaw W b) (freshDelta b E X)) v) (ENNReal.ofReal (4 * m))
          (freshLaw W b) ≤
        ENNReal.ofReal (Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E X) * vecNorm u * vecNorm v))
    (hδ : MomBd ((growthPathLaw W b).prod ν)
      (fun w => jetDistance0 b E (pathX b E W l w.1)) (16 * m) (Cδ / W))
    (ha : MomBd ((growthPathLaw W b).prod ν)
      (fun w => vecNorm (nearL b E W l β₁ w.1 (g₁ w.2))) (16 * m) A)
    (hc : MomBd ((growthPathLaw W b).prod ν)
      (fun w => vecNorm (nearR b E W l β₂ w.1 (g₂ w.2))) (16 * m) A) :
    ∫⁻ w, ENNReal.ofReal ((‖rawForm b E W (l + 1) β₁ β₂ w.1 (g₁ w.2) (g₂ w.2)‖ ^ 2) ^ (2 * m))
        ∂((growthPathLaw W b).prod ν) ≤
      ENNReal.ofReal (Real.exp ((stepK (2 * m) + 4 * m) / W)) *
        ∫⁻ w, ENNReal.ofReal ((‖rawForm b E W l β₁ β₂ w.1 (g₁ w.2) (g₂ w.2)‖ ^ 2) ^ (2 * m))
          ∂((growthPathLaw W b).prod ν) +
      ENNReal.ofReal (stepBeta m Cm Cf Cδ A / W) := by
  set μΩ := (growthPathLaw W b).prod ν
  have hW0 : (0 : ℝ) < W := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set K := stepK (2 * m)
  have hK : 0 ≤ K := (stepK_pos _).le
  have hstep := step_bound hb hE1 hE2 ν hg₁ hg₂ hm hW hCf hupd hI hF
  set δ : GrowthPath W × Γ → ℝ := fun w => jetDistance0 b E (pathX b E W l w.1)
  set na : GrowthPath W × Γ → ℝ := fun w => vecNorm (nearL b E W l β₁ w.1 (g₁ w.2))
  set nc : GrowthPath W × Γ → ℝ := fun w => vecNorm (nearR b E W l β₂ w.1 (g₂ w.2))
  set Z₁ : GrowthPath W × Γ → ℝ := fun w => (W * δ w + 1) * na w * nc w
  set Z₂ : GrowthPath W × Γ → ℝ := fun w => (1 + Real.sqrt W * δ w) * na w * nc w
  have hδ0 : ∀ w, 0 ≤ δ w := fun w => norm_nonneg _
  have hna : ∀ w, 0 ≤ na w := fun w => vecNorm_nonneg _
  have hnc : ∀ w, 0 ≤ nc w := fun w => vecNorm_nonneg _
  have hZ₁ : ∀ w, 0 ≤ Z₁ w := fun w => by have := hδ0 w; have := hna w; have := hnc w; positivity
  have hZ₂ : ∀ w, 0 ≤ Z₂ w := fun w => by have := hδ0 w; have := hna w; have := hnc w; positivity
  -- the moments of `Z₁, Z₂`
  have hm8 : (0 : ℝ) < 8 * m := by linarith
  have hm4 : (0 : ℝ) < 4 * m := by linarith
  have hB : 0 ≤ (Cδ + 1) * A * A := by positivity
  have hZ₁m : MomBd μΩ Z₁ (4 * m) ((Cδ + 1) * A * A) := by
    have h1 : MomBd μΩ (fun w => W * δ w) (16 * m) Cδ := by
      have := hδ.const_mul (c := (W : ℝ)) hW0.le
      exact this.of_le (le_of_eq (by field_simp))
    have h2 := h1.add (by linarith) (MomBd.const (μ := μΩ) (1 : ℝ) (16 * m) (by linarith)) hCδ
      (abs_nonneg _)
    rw [abs_one] at h2
    have h3 := (show MomBd μΩ (fun w => W * δ w + 1) (2 * (8 * m)) (Cδ + 1) by
      rw [show (2 : ℝ) * (8 * m) = 16 * m by ring]; exact h2).mul hm8
      (show MomBd μΩ na (2 * (8 * m)) A by rw [show (2 : ℝ) * (8 * m) = 16 * m by ring]; exact ha)
      (by linarith)
    exact (show MomBd μΩ _ (2 * (4 * m)) _ by
      rw [show (2 : ℝ) * (4 * m) = 8 * m by ring]; exact h3).mul hm4
      (show MomBd μΩ nc (2 * (4 * m)) A by
        rw [show (2 : ℝ) * (4 * m) = 8 * m by ring]; exact hc.exponent_mono (by linarith))
      (by positivity)
  have hZ₂m : MomBd μΩ Z₂ (4 * m) ((Cδ + 1) * A * A) := by
    have hsW : Real.sqrt W ≤ W := by
      rw [Real.sqrt_le_left hW0.le]; nlinarith
    have h1 : MomBd μΩ (fun w => Real.sqrt W * δ w) (16 * m) Cδ := by
      have := hδ.const_mul (c := Real.sqrt W) (Real.sqrt_nonneg _)
      refine this.of_le ?_
      rw [mul_div_assoc', div_le_iff₀ hW0]; nlinarith
    have h2 := (MomBd.const (μ := μΩ) (1 : ℝ) (16 * m) (by linarith)).add (by linarith) h1
      (abs_nonneg _) hCδ
    rw [abs_one, add_comm (1 : ℝ) Cδ] at h2
    have h3 := (show MomBd μΩ (fun w => 1 + Real.sqrt W * δ w) (2 * (8 * m)) (Cδ + 1) by
      rw [show (2 : ℝ) * (8 * m) = 16 * m by ring]; exact h2).mul hm8
      (show MomBd μΩ na (2 * (8 * m)) A by rw [show (2 : ℝ) * (8 * m) = 16 * m by ring]; exact ha)
      (by linarith)
    exact (show MomBd μΩ _ (2 * (4 * m)) _ by
      rw [show (2 : ℝ) * (4 * m) = 8 * m by ring]; exact h3).mul hm4
      (show MomBd μΩ nc (2 * (4 * m)) A by
        rw [show (2 : ℝ) * (4 * m) = 8 * m by ring]; exact hc.exponent_mono (by linarith))
      (by positivity)
  have hI₁ := lintegral_pow_le_of_momBd' (n := 4 * m) (by omega)
    (by exact_mod_cast hZ₁m) hB hZ₁
  have hI₂ := lintegral_pow_le_of_momBd' (n := 4 * m) (by omega)
    (by exact_mod_cast hZ₂m) hB hZ₂
  -- the pointwise bound
  set c₃ := (1 + K) * 2 ^ (4 * m) * Cm ^ (4 * m)
  set c₄ := K * Cf ^ (4 * m)
  have hpas : ∀ᵐ w ∂μΩ, (passiveY (pathX b E W l w.1)).PosSemidef := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b) (ν := ν)).ae
      (ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb hE1 hE2)] with w hw
    exact pathNearSchur_passive hw l
  have hpt : ∀ᵐ w ∂μΩ,
      ENNReal.ofReal ((1 + K / W) *
          (‖rawForm b E W l β₁ β₂ w.1 (g₁ w.2) (g₂ w.2) +
            bilinear (nearL b E W l β₁ w.1 (g₁ w.2))
              (matrixExpect (freshLaw W b) (freshDelta b E (pathX b E W l w.1)))
              (nearR b E W l β₂ w.1 (g₂ w.2))‖ ^ 2) ^ (2 * m)) +
        ENNReal.ofReal (K * (W : ℝ) ^ (2 * m - 1)) *
          ENNReal.ofReal ((Cf * ((Real.sqrt W)⁻¹ + δ w) * na w * nc w) ^ (4 * m)) ≤
      ENNReal.ofReal (Real.exp ((K + 4 * m) / W)) *
          ENNReal.ofReal ((‖rawForm b E W l β₁ β₂ w.1 (g₁ w.2) (g₂ w.2)‖ ^ 2) ^ (2 * m)) +
        (ENNReal.ofReal (c₃ / W) * ENNReal.ofReal (Z₁ w ^ (4 * m)) +
          ENNReal.ofReal (c₄ / W) * ENNReal.ofReal (Z₂ w ^ (4 * m))) := by
    filter_upwards [hpas] with w hw
    have hμ : ‖bilinear (nearL b E W l β₁ w.1 (g₁ w.2))
        (matrixExpect (freshLaw W b) (freshDelta b E (pathX b E W l w.1)))
        (nearR b E W l β₂ w.1 (g₂ w.2))‖ ≤ Cm * Z₁ w / W := by
      refine (norm_bilinear_le _ _ _).trans ?_
      have := hmean _ hw
      have e : Cm * Z₁ w / W = na w * (Cm * (δ w + (W : ℝ)⁻¹)) * nc w := by
        simp only [Z₁]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (hna w)) (hnc w)
    have h1 := step_pointwise_scalar (x := rawForm b E W l β₁ β₂ w.1 (g₁ w.2) (g₂ w.2)) hm hK
      hCm (hZ₁ w) hW hμ
    have h2 : K * (W : ℝ) ^ (2 * m - 1) * (Cf * ((Real.sqrt W)⁻¹ + δ w) * na w * nc w) ^ (4 * m) =
        c₄ / W * Z₂ w ^ (4 * m) := by
      have hs : Cf * ((Real.sqrt W)⁻¹ + δ w) * na w * nc w = Cf * Z₂ w / Real.sqrt W := by
        simp only [Z₂]
        have : Real.sqrt W ≠ 0 := (Real.sqrt_pos.mpr hW0).ne'
        field_simp
      have hsq : Real.sqrt W ^ (4 * m) = (W : ℝ) ^ (2 * m) := by
        rw [show 4 * m = 2 * (2 * m) by ring, pow_mul, Real.sq_sqrt hW0.le]
      have hWm : (W : ℝ) ^ (2 * m) = W ^ (2 * m - 1) * W := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hs, div_pow, mul_pow, hsq, hWm]; simp only [c₄]; field_simp
    have hA0 : 0 ≤ (1 + K / W) *
        (‖rawForm b E W l β₁ β₂ w.1 (g₁ w.2) (g₂ w.2) +
          bilinear (nearL b E W l β₁ w.1 (g₁ w.2))
            (matrixExpect (freshLaw W b) (freshDelta b E (pathX b E W l w.1)))
            (nearR b E W l β₂ w.1 (g₂ w.2))‖ ^ 2) ^ (2 * m) := by positivity
    have hB0 : 0 ≤ K * (W : ℝ) ^ (2 * m - 1) := by positivity
    have hC0 : 0 ≤ (Cf * ((Real.sqrt W)⁻¹ + δ w) * na w * nc w) ^ (4 * m) := by
      have := hδ0 w; have := hna w; have := hnc w; positivity
    have hZ1 : 0 ≤ Z₁ w ^ (4 * m) := pow_nonneg (hZ₁ w) _
    have hZ2 : 0 ≤ Z₂ w ^ (4 * m) := pow_nonneg (hZ₂ w) _
    have hc3 : 0 ≤ c₃ / W := by positivity
    have hc4 : 0 ≤ c₄ / W := by positivity
    rw [← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_add hA0 (mul_nonneg hB0 hC0),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hc3,
      ← ENNReal.ofReal_mul hc4, ← ENNReal.ofReal_add (mul_nonneg hc3 hZ1) (mul_nonneg hc4 hZ2),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (1 + K) * 2 ^ (4 * m) * Cm ^ (4 * m) / W * Z₁ w ^ (4 * m) =
        c₃ / W * Z₁ w ^ (4 * m) := by simp only [c₃]
    linarith
  -- integrate
  have hZm₁ : Measurable fun w => ENNReal.ofReal (Z₁ w ^ (4 * m)) := by
    have := measurable_nearL (W := W) b E l β₁ measurable_fst (hg₁.comp measurable_snd)
    have := measurable_nearR (W := W) b E l β₂ measurable_fst (hg₂.comp measurable_snd)
    have : Measurable δ := (measurable_jetDistance0 (W := W) b E).comp
      ((BlockBand.Transmission.PathJet.measurable_pathX b E l).comp measurable_fst)
    simp only [Z₁, na, nc, vecNorm]
    fun_prop
  have hxm : Measurable fun w : GrowthPath W × Γ =>
      ENNReal.ofReal ((‖rawForm b E W l β₁ β₂ w.1 (g₁ w.2) (g₂ w.2)‖ ^ 2) ^ (2 * m)) :=
    ((measurable_rawForm b E l β₁ β₂ measurable_fst (hg₁.comp measurable_snd)
      (hg₂.comp measurable_snd)).norm.pow_const 2 |>.pow_const _).ennreal_ofReal
  have hZm₂ : Measurable fun w => ENNReal.ofReal (Z₂ w ^ (4 * m)) := by
    have := measurable_nearL (W := W) b E l β₁ measurable_fst (hg₁.comp measurable_snd)
    have := measurable_nearR (W := W) b E l β₂ measurable_fst (hg₂.comp measurable_snd)
    have : Measurable δ := (measurable_jetDistance0 (W := W) b E).comp
      ((BlockBand.Transmission.PathJet.measurable_pathX b E l).comp measurable_fst)
    simp only [Z₂, na, nc, vecNorm]
    fun_prop
  refine hstep.trans ((lintegral_mono_ae hpt).trans ?_)
  rw [lintegral_add_left (hxm.const_mul _), lintegral_add_left (hZm₁.const_mul _),
    lintegral_const_mul _ hxm, lintegral_const_mul _ hZm₁, lintegral_const_mul _ hZm₂]
  refine add_le_add le_rfl ((add_le_add (mul_le_mul_right hI₁ _) (mul_le_mul_right hI₂ _)).trans
    (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [stepBeta, c₃, c₄, K]; ring

end BlockBand.SourceProcess.RawTag
