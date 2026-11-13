module

public import BlockBand.SourceProcess.PhysApprox.B3FracMomStep
public import BlockBand.SourceProcess.PhysApprox.B3FracMomBound

/-!
# `FracPowStep α 4` and `FarFracTraceMomentsAt 4` from the contract hypotheses

The fractional moment bound for homogeneous transmission at `q = 4`.

* **`fracPowStep_four`**: `GaussianAbsorptionContract`, `GaussianLpGradient` and
  `GaussianPoincare` give `FracPowStep α 4` for every `0 < α < 1`.
  Regular states (`δ₀, δ₁ ≤ d`, `g ≤ γW`, `d ≤ 1`): `step4_onDomain` + `step4_alg`;
  irregular states: `E P'⁴ ≤ W⁴ ≤ W⁴((δ₀/d)⁸ + (δ₁/d)⁸ + (g/(γW))⁸)`.
* **`farFracTraceMomentsAt_four`**: with `MatchedTracesContract` in addition,
  `Jet.FarFracTraceMomentsAt 4` (with `α = 1/8`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.FracMom

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.FractionalBulk BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- The bracket of `step4_onDomain` is at most `H(δ₀ + 1/W)` on regular states. -/
theorem step4_bracket_le {C κ Cf2 Cf4 δ₀ Wr : ℝ} (hC : 0 ≤ C) (hW : 1 ≤ Wr) (hδ0 : 0 ≤ δ₀)
    (hδ1 : δ₀ ≤ 1) :
    4 * C * (δ₀ + Wr⁻¹ ^ 2) + 17 * C ^ 2 * (δ₀ + Wr⁻¹ ^ 2) ^ 2 +
        24 * C ^ 4 * (δ₀ + Wr⁻¹ ^ 2) ^ 4 + 17 * κ ^ 2 * (Cf2 ^ 2 / Wr) +
        24 * κ ^ 4 * (Cf4 ^ 4 / Wr ^ 2) ≤
      (4 * C + 34 * C ^ 2 + 192 * C ^ 4 + 17 * κ ^ 2 * Cf2 ^ 2 + 24 * κ ^ 4 * Cf4 ^ 4) *
        (δ₀ + 1 / Wr) := by
  have hW0 : 0 < Wr := by linarith
  have hi1 : Wr⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW
  have hi0 : 0 ≤ Wr⁻¹ := inv_nonneg.2 hW0.le
  set e := δ₀ + Wr⁻¹ ^ 2 with he
  set f := δ₀ + 1 / Wr with hf
  have hef : e ≤ f := by
    rw [he, hf, one_div]; have : Wr⁻¹ ^ 2 ≤ Wr⁻¹ := by nlinarith
    linarith
  have he0 : 0 ≤ e := by positivity
  have he2 : e ≤ 2 := by rw [he]; nlinarith
  have hf0 : 0 ≤ f := le_trans he0 hef
  have hWf : 1 / Wr ≤ f := by rw [hf]; linarith
  have hW2f : 1 / Wr ^ 2 ≤ f := by
    have : 1 / Wr ^ 2 ≤ 1 / Wr := by
      rw [div_le_div_iff₀ (by positivity) hW0]; nlinarith
    linarith
  have hk2 : 0 ≤ κ ^ 2 * Cf2 ^ 2 := by positivity
  have hk4 : 0 ≤ κ ^ 4 * Cf4 ^ 4 := by positivity
  have t1 : 4 * C * e ≤ 4 * C * f := by gcongr
  have t2 : 17 * C ^ 2 * e ^ 2 ≤ 34 * C ^ 2 * f := by
    have : e ^ 2 ≤ 2 * f := by nlinarith
    nlinarith [sq_nonneg C]
  have t3 : 24 * C ^ 4 * e ^ 4 ≤ 192 * C ^ 4 * f := by
    have h3 : e ^ 3 ≤ 8 := by
      have := pow_le_pow_left₀ he0 he2 3; norm_num at this; linarith
    have : e ^ 4 ≤ 8 * f := by
      have : e ^ 4 = e ^ 3 * e := by ring
      rw [this]; nlinarith [pow_nonneg he0 3]
    have hC4 : 0 ≤ C ^ 4 := by positivity
    nlinarith
  have t4 : 17 * κ ^ 2 * (Cf2 ^ 2 / Wr) ≤ 17 * κ ^ 2 * Cf2 ^ 2 * f := by
    have := mul_le_mul_of_nonneg_left hWf hk2
    have e2 : 17 * κ ^ 2 * (Cf2 ^ 2 / Wr) = 17 * (κ ^ 2 * Cf2 ^ 2 * (1 / Wr)) := by ring
    rw [e2]; linarith
  have t5 : 24 * κ ^ 4 * (Cf4 ^ 4 / Wr ^ 2) ≤ 24 * κ ^ 4 * Cf4 ^ 4 * f := by
    have := mul_le_mul_of_nonneg_left hW2f hk4
    have e2 : 24 * κ ^ 4 * (Cf4 ^ 4 / Wr ^ 2) = 24 * (κ ^ 4 * Cf4 ^ 4 * (1 / Wr ^ 2)) := by ring
    rw [e2]; linarith
  nlinarith

/-- `x ≤ d` fails gives `1 ≤ (x/d)^n`. -/
theorem one_le_div_pow_of_lt {x d : ℝ} (hd : 0 < d) (h : d < x) (n : ℕ) : 1 ≤ (x / d) ^ n :=
  one_le_pow₀ ((one_le_div hd).2 h.le)

/-- **`FracPowStep α 4`** from `GaussianAbsorptionContract`, `GaussianLpGradient` and
`GaussianPoincare`. -/
theorem fracPowStep_four (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : FracPowStep α 4 := by
  intro b E hb0 hb h1 h2
  obtain ⟨hκb, hEκ⟩ := bulk_of_lt' h1 h2
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  obtain ⟨C₀, Cl, cl, dl, γl, Wl, -, hCl0, hcl, hdl, hγl, hL⟩ :=
    layerStep_bulk hGA hLp hP hα0 hα1 hb0 hb hκb
  obtain ⟨Cm, dm, Wm, -, hdm, hM⟩ := meanForm_bulk hA hb0 hb hκb
  obtain ⟨Cf2, Wf2, hF2⟩ := oneStepFluctuation_holds hGA hLp b hb0 hb E h1 h2 2 (by norm_num)
  obtain ⟨Cf4, Wf4, hF4⟩ := oneStepFluctuation_holds hGA hLp b hb0 hb E h1 h2 4 (by norm_num)
  obtain ⟨WI, hI⟩ := LengthUniform.ml_integrable_U_bulk hA hb0 hb hκb
  set κ := cP α * jP α with hκdef
  set C := max (κ * Cm) Cl with hCdef
  have hC0 : 0 ≤ C := le_trans hCl0 (le_max_right _ _)
  set Cf2' := max Cf2 0
  set Cf4' := max Cf4 0
  set H := 4 * C + 34 * C ^ 2 + 192 * C ^ 4 + 17 * κ ^ 2 * Cf2' ^ 2 + 24 * κ ^ 4 * Cf4' ^ 4
  have hH0 : 0 ≤ H := by positivity
  set d := min (min dl dm) 1 with hddef
  have hd0 : 0 < d := lt_min (lt_min hdl hdm) one_pos
  have hddl : d ≤ dl := (min_le_left _ _).trans (min_le_left _ _)
  have hddm : d ≤ dm := (min_le_left _ _).trans (min_le_right _ _)
  have hd1 : d ≤ 1 := min_le_right _ _
  set c := min (3 * cl / 128) 1 with hcdef
  have hc0 : 0 < c := lt_min (by positivity) one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcc : c ≤ 3 * cl / 128 := min_le_left _ _
  have hA0 : 0 ≤ step4A H cl := le_trans (by positivity) (le_max_right _ _)
  refine ⟨c, step4A H cl, 1, d, γl, max (max (max Wl Wm) (max Wf2 Wf4)) (max WI 1), hc0, hA0,
    zero_le_one, hd0, hγl, fun W hW s hs X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWl, hWm⟩, hWf2, hWf4⟩, hWI, hW1⟩ := hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWp : (0 : ℝ) < W := by linarith
  have hT := passiveTransmission_posSemidef (by linarith : b < 1) h1 h2 hX
  have hT1 := one_sub_passiveTransmission_posSemidef b E X
  set P := fracTrace α (passiveTransmission b E X) with hPdef
  set g := conductanceOf (passiveTransmission b E X) with hgdef
  set δ₀ := jetDistance0 b E X with hδ0def
  set δ₁ := jetDistance1 b E s X with hδ1def
  have hP0 : 0 ≤ P := fracTrace_nonneg' _ _
  have hPW : P ≤ W := by have := fracTrace_le_card hT hT1 hα0; rwa [Fintype.card_fin] at this
  have hg0 : 0 ≤ g := by
    rw [hgdef, conductanceOf, ← ts_sum_lam hT]
    exact Finset.sum_nonneg fun i _ => ts_lam_nonneg hT i
  have hδ00 : 0 ≤ δ₀ := norm_nonneg _
  -- the irregular majorant and the baseline
  have hev : ∀ x : ℝ, 0 ≤ x ^ (2 * 4) := fun x => by rw [pow_mul]; positivity
  have hM0 : 0 ≤ (δ₀ / d) ^ (2 * 4) + (δ₁ / d) ^ (2 * 4) + (g / (γl * W)) ^ (2 * 4) :=
    add_nonneg (add_nonneg (hev _) (hev _)) (hev _)
  have hbase : 0 ≤ P ^ 4 - c / W * P ^ (4 + 1) := by
    have : c / W * P ^ (4 + 1) ≤ P ^ 4 := by
      rw [pow_succ]
      have h' : c / W * P ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one hWp]
        nlinarith
      have := mul_le_mul_of_nonneg_left h' (by positivity : (0 : ℝ) ≤ P ^ 4)
      nlinarith
    linarith
  have hrest : 0 ≤ step4A H cl * (W : ℝ) ^ 4 * δ₀ ^ (4 + 1) + step4A H cl / W +
      step4A H cl / W * g ^ (4 + 1) := by positivity
  set ν := freshLaw W b
  have hS4 : ∫ y, stepFrac α b E X y ^ 4 ∂ν ≤ (W : ℝ) ^ 4 := by
    calc ∫ y, stepFrac α b E X y ^ 4 ∂ν ≤ ∫ _y, (W : ℝ) ^ 4 ∂ν :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
            pow_nonneg (stepFrac_nonneg _ _ _ _ _) _) (integrable_const _)
            (Filter.Eventually.of_forall fun y =>
              pow_le_pow_left₀ (stepFrac_nonneg _ _ _ _ _) (stepFrac_le _ _ _ _ _) 4)
      _ = (W : ℝ) ^ 4 := by simp
  by_cases hdom : δ₀ ≤ d ∧ δ₁ ≤ d ∧ g ≤ γl * W
  · obtain ⟨hd0d, hd1d, hgd⟩ := hdom
    have hstep := (hL W hWl E hEκ s hs X hX).2 (hd0d.trans hddl) (hd1d.trans hddl) hgd
    have hmean := hM W hWm E hEκ X hX (hd0d.trans hddm)
    have hU := hI W hWI E hEκ X hX
    have hfl : ∀ (Cf : ℝ) (pp : ℝ), (∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u
        (freshU b E X ω - matrixExpect ν (freshU b E X)) v) (ENNReal.ofReal pp) ν ≤
        ENNReal.ofReal (Cf / Real.sqrt W * vecNorm u * vecNorm v)) →
        ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u
        (freshU b E X ω - matrixExpect ν (freshU b E X)) v) (ENNReal.ofReal pp) ν ≤
        ENNReal.ofReal (max Cf 0 / Real.sqrt W * vecNorm u * vecNorm v) := by
      intro Cf pp h u v
      refine (h u v).trans (ENNReal.ofReal_le_ofReal ?_)
      have hu := vecNorm_nonneg u
      have hv := vecNorm_nonneg v
      gcongr
      exact le_max_left _ _
    have h4 := step4_onDomain hα0 hα1 hb0 hb h1 h2 hW1 hX (C := C) (Cm := Cm) (Cl := Cl)
      (cl := cl) (le_max_left _ _) (le_max_right _ _) (le_max_right Cf2 0)
      (le_max_right Cf4 0) hU hmean hstep
      (hfl Cf2 2 fun u v => (hF2 W hWf2 X hX u v).1) (hfl Cf4 4 fun u v => (hF4 W hWf4 X hX u v).1)
    have hbr := step4_bracket_le (κ := κ) (Cf2 := Cf2') (Cf4 := Cf4') hC0 hWr hδ00 (hd0d.trans hd1)
    have hP4 : 0 ≤ P ^ 4 := by positivity
    have hh : ∫ y, stepFrac α b E X y ^ 4 ∂ν ≤
        P ^ 4 + H * (δ₀ + 1 / W) * P ^ 4 - cl / (8 * W) * P ^ 3 *
          lowFrac α (passiveTransmission b E X) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hbr hP4
      linarith
    have halg := step4_alg hP0 hδ00 hg0 hWr hH0 hcl (lowFrac_ge hα0 hT hT1) hh
    have hc5 : c / W * P ^ (4 + 1) ≤ 3 * cl / 128 / W * P ^ 5 := by
      have := div_le_div_of_nonneg_right hcc hWp.le
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hBM : 0 ≤ 1 * (W : ℝ) ^ 4 *
        ((δ₀ / d) ^ (2 * 4) + (δ₁ / d) ^ (2 * 4) + (g / (γl * W)) ^ (2 * 4)) :=
      mul_nonneg (by positivity) hM0
    linarith
  · have hM1 : 1 ≤ (δ₀ / d) ^ (2 * 4) + (δ₁ / d) ^ (2 * 4) + (g / (γl * W)) ^ (2 * 4) := by
      rcases not_and_or.1 hdom with h | h
      · have := one_le_div_pow_of_lt hd0 (lt_of_not_ge h) (2 * 4)
        have := hev (δ₁ / d)
        have := hev (g / (γl * W))
        linarith
      rcases not_and_or.1 h with h' | h'
      · have := one_le_div_pow_of_lt hd0 (lt_of_not_ge h') (2 * 4)
        have := hev (δ₀ / d)
        have := hev (g / (γl * W))
        linarith
      · have := one_le_div_pow_of_lt (mul_pos hγl hWp) (lt_of_not_ge h') (2 * 4)
        have := hev (δ₀ / d)
        have := hev (δ₁ / d)
        linarith
    have hWM : (W : ℝ) ^ 4 ≤ 1 * (W : ℝ) ^ 4 *
        ((δ₀ / d) ^ (2 * 4) + (δ₁ / d) ^ (2 * 4) + (g / (γl * W)) ^ (2 * 4)) := by
      rw [one_mul]; exact le_mul_of_one_le_right (by positivity) hM1
    linarith

/-- **`FarFracTraceMomentsAt 4`** (`α = 1/8`) from `MatchedTracesContract`,
`GaussianAbsorptionContract`, `GaussianLpGradient` and `GaussianPoincare`. -/
theorem farFracTraceMomentsAt_four (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    Jet.FarFracTraceMomentsAt 4 :=
  farFracTraceMomentsAt_four_of_step hMT hGA hLp
    (fracPowStep_four hGA hLp hP (by norm_num) (by norm_num))

end BlockBand.SourceProcess.PhysApprox.B3.FracMom
