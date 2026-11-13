module

public import BlockBand.QUE.Assembly.PairResidual
public import BlockBand.Internal.Contracts.WindowAngular

/-!
# The mode bound from the physical centre and angular statements

`modeBound_of_contracts`: the mode bound from `QUE.PhysicalCenterContract` and
`QUE.PhysicalAngularModeContract` for one centre family `w`, under the physical law,
`4 ≤ n ≤ TW`, for `ϑ`-bulk ranks and every nonzero mode, with `C` depending on `(b, ϑ, T)` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.ModeBoundOfContracts

open MeasureTheory BlockBand.Model.Construction BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.WindowAngular
open BlockBand.QUE.PairResidual

/-- `d_m ≤ 2`. -/
theorem modeSeparation_le_two (p : Parameters) (m : ZMod p.n) : modeSeparation p m ≤ 2 := by
  unfold modeSeparation
  calc ‖(1 : ℂ) - ZMod.stdAddChar m‖ ≤ ‖(1 : ℂ)‖ + ‖(ZMod.stdAddChar m : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      rw [norm_one, ZMod.stdAddChar_apply, Circle.norm_coe]
      norm_num

/-- `γ_m ≤ 1` under the physical law. -/
theorem modeVariance_le_one (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (m : ZMod p.n) :
    (∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix)) ≤ 1 := by
  have h : (∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix)) ≤
      ∫ _H, (1 : ℝ) ∂(model.law : Measure p.SiteMatrix) := by
    apply integral_mono_ae (integrable_physicalMode_sq p model α m) (integrable_const _)
    filter_upwards [physicalMode_norm_le_one_ae p model α m] with H hH
    have h0 : 0 ≤ ‖physicalMode p α m H‖ := norm_nonneg _
    nlinarith
  simpa using h

/-- **The mode bound** from `QUE.PhysicalCenterContract` and `QUE.PhysicalAngularModeContract`
for one centre family `w`. Physical law, `4 ≤ n ≤ TW`, `ϑ`-bulk ranks, every nonzero mode; `C`
depends on `(b, ϑ, T)` only. -/
theorem modeBound_of_contracts (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (w : PairCenterFamily) (hc : PhysicalCenterContract b θ T hb hb' w)
    (ha : PhysicalAngularModeContract b θ T hb hb' w) :
    ModeBoundContract b θ T hb hb' := by
  obtain ⟨A, B, W₀, hA, hB, hres⟩ := pairResidual_of_contracts b θ T hb hb' w hc ha
  set C : ℝ := 4 * A + 4 * B + 2 * max W₀ 0 with hCdef
  have hW₀ : 0 ≤ max W₀ 0 := le_max_right _ _
  refine ⟨C, by positivity, ?_⟩
  intro n W hn hW hnW p model α hα m hm
  have : NeZero p.n := ⟨p.n_pos.ne'⟩
  have hn' : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hW' : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hd4 : 4 / (p.n : ℝ) ≤ modeSeparation p m := four_div_le_norm_one_sub_stdAddChar hm
  have hd : 0 < modeSeparation p m := lt_of_lt_of_le (by positivity) hd4
  have hd2 := modeSeparation_le_two p m
  have hsn : 0 < Real.sqrt (p.n : ℝ) := Real.sqrt_pos.mpr hn'
  have hsw : 0 < Real.sqrt (p.W : ℝ) := Real.sqrt_pos.mpr hW'
  have hratio : 0 ≤ ((n : ℝ) / W) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hT1 : 0 ≤ 1 / ((W : ℝ) * modeSeparation p m) := by positivity
  have hT2 : 0 ≤ 1 / (Real.sqrt n * ((W : ℝ) * Real.sqrt W) * modeSeparation p m ^ 2) := by
    positivity
  rcases lt_or_ge W₀ (W : ℝ) with hlarge | hsmall
  · obtain ⟨i, X, center, ⟨hj, hj2, hX⟩, hang⟩ := hres n W hn hW hnW hlarge model α hα
    have hγ := mode_variance_le_of_pair p model α i m hm X center hj hj2 hX (hang m hm)
    refine ⟨?_, ?_⟩
    · have e1 : 4 * (A / (p.W : ℝ)) / ‖(1 : ℂ) - ZMod.stdAddChar m‖ =
          4 * A * (1 / ((W : ℝ) * modeSeparation p m)) := by
        unfold modeSeparation; field_simp; rfl
      have e2 : 4 * (B / (Real.sqrt (p.n : ℝ) * ((p.W : ℝ) * Real.sqrt (p.W : ℝ)))) /
            ‖(1 : ℂ) - ZMod.stdAddChar m‖ ^ 2 =
          4 * B * (1 / (Real.sqrt n * ((W : ℝ) * Real.sqrt W) * modeSeparation p m ^ 2)) := by
        unfold modeSeparation; field_simp; rfl
      rw [e1, e2] at hγ
      calc _ ≤ _ := hγ
        _ ≤ C * (1 / ((W : ℝ) * modeSeparation p m)) +
            C * (1 / (Real.sqrt n * ((W : ℝ) * Real.sqrt W) * modeSeparation p m ^ 2)) := by
          gcongr
          · rw [hCdef]; nlinarith
          · rw [hCdef]; nlinarith
        _ = _ := by ring
    · have hms := mode_scale hn' hW' hA hB hd4 hγ
      calc _ ≤ _ := hms
        _ ≤ C * ((n : ℝ) / W + ((n : ℝ) / W) ^ (3 / 2 : ℝ)) := by
          gcongr
          rw [hCdef]
          apply max_le <;> nlinarith
  · have hγ1 := modeVariance_le_one p model α m
    have hWle : (W : ℝ) ≤ max W₀ 0 := le_trans hsmall (le_max_left _ _)
    have hCW : 2 * (W : ℝ) ≤ C := by rw [hCdef]; nlinarith
    refine ⟨?_, ?_⟩
    · have h1 : 1 ≤ C * (1 / ((W : ℝ) * modeSeparation p m)) := by
        rw [mul_one_div, le_div_iff₀ (by positivity)]
        nlinarith
      nlinarith
    · have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
      have h1 : 1 ≤ C * ((n : ℝ) / W) := by
        rw [mul_div_assoc', le_div_iff₀ hW']
        nlinarith
      have hC0 : 0 ≤ C := by positivity
      nlinarith [mul_nonneg hC0 hratio]

end BlockBand.QUE.ModeBoundOfContracts
