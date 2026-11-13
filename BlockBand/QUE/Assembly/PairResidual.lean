module

public import BlockBand.QUE.Fourier.PhysicalFiniteTest
public import BlockBand.QUE.Assembly.ModeScale
public import BlockBand.QUE.Assembly.FiniteWidth
public import BlockBand.Model.Construction.SpectralFiniteRealization
public import BlockBand.Internal.Contracts.QUE
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# QUE reduced to the centre and angular statements

The QUE bound follows from a large-width pair residual `QUEPairResidual` (`que_of_pairResidual`),
and this residual follows from the physical centre statement `QUE.PhysicalCenterContract` and the
physical angular statement `QUE.PhysicalAngularModeContract` for one shared centre family
(`pairResidual_of_contracts`, `que_of_contracts`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.PairResidual

open MeasureTheory BlockBand.Model.Construction BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.QUE
open scoped ENNReal NNReal

theorem two_div_le_sin_pi_mul_div {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    2 / (n : ℝ) ≤ Real.sin (Real.pi * k / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hkn)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hkn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
  rcases le_or_gt (2 * k) n with h2 | h2
  · have h2' : (2 * k : ℝ) ≤ n := by exact_mod_cast h2
    have hx0 : 0 ≤ Real.pi * k / n := by positivity
    have hx1 : Real.pi * k / n ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hn (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin hx0 hx1
    have heq : 2 / Real.pi * (Real.pi * k / n) = 2 * k / n := by
      field_simp
    rw [heq] at hs
    calc 2 / (n : ℝ) ≤ 2 * k / n := by gcongr; linarith
      _ ≤ _ := hs
  · have h2' : (n : ℝ) < 2 * k := by exact_mod_cast h2
    have href : Real.pi * ((n : ℝ) - k) / n = Real.pi - Real.pi * k / n := by
      field_simp
    have hy0 : 0 ≤ Real.pi * ((n : ℝ) - k) / n := by
      apply div_nonneg _ hn.le
      nlinarith [Real.pi_pos]
    have hy1 : Real.pi * ((n : ℝ) - k) / n ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hn (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin hy0 hy1
    rw [href, Real.sin_pi_sub] at hs
    have heq : 2 / Real.pi * (Real.pi - Real.pi * k / n) = 2 * ((n : ℝ) - k) / n := by
      field_simp
    rw [heq] at hs
    calc 2 / (n : ℝ) ≤ 2 * ((n : ℝ) - k) / n := by gcongr; linarith
      _ ≤ _ := hs

theorem four_div_le_norm_one_sub_stdAddChar {n : ℕ} [NeZero n] {m : ZMod n} (hm : m ≠ 0) :
    4 / (n : ℝ) ≤ ‖(1 : ℂ) - ZMod.stdAddChar m‖ := by
  have hk0 : 0 < m.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero m).2 hm)
  have hkn : m.val < n := ZMod.val_lt m
  have hexp : (2 * (Real.pi : ℂ) * Complex.I * (m.val : ℂ) / (n : ℂ)) =
      Complex.I * ((2 * Real.pi * m.val / n : ℝ) : ℂ) := by
    push_cast; ring
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, hexp, norm_sub_rev,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have hhalf : 2 * Real.pi * (m.val : ℝ) / n / 2 = Real.pi * m.val / n := by ring
  rw [hhalf]
  have hs := two_div_le_sin_pi_mul_div hk0 hkn
  calc 4 / (n : ℝ) = 2 * (2 / n) := by ring
    _ ≤ 2 * |Real.sin (Real.pi * m.val / n)| := by
      gcongr; exact hs.trans (le_abs_self _)
theorem amgm_div {a b d : ℝ} (hd : 0 < d) : a * b ≤ a ^ 2 / d + d / 4 * b ^ 2 := by
  have h : a ^ 2 / d + d / 4 * b ^ 2 - a * b = (a - d / 2 * b) ^ 2 / d := by
    field_simp
    ring
  have h0 : 0 ≤ (a - d / 2 * b) ^ 2 / d := div_nonneg (sq_nonneg _) hd.le
  linarith

theorem absorb_quarter {γ d A X : ℝ} (hd : 0 < d)
    (h : d / 2 * γ ≤ A + (X / d + d / 4 * γ)) :
    γ ≤ 4 * A / d + 4 * X / d ^ 2 := by
  have h1 : d / 4 * γ ≤ A + X / d := by linarith
  have h2 : γ = 4 / d * (d / 4 * γ) := by
    field_simp
  calc γ = 4 / d * (d / 4 * γ) := h2
    _ ≤ 4 / d * (A + X / d) := by gcongr
    _ = 4 * A / d + 4 * X / d ^ 2 := by
      field_simp

theorem mode_scale {n W A B d γ : ℝ} (hn : 0 < n) (hW : 0 < W) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd : 4 / n ≤ d)
    (h : γ ≤ 4 * (A / W) / d + 4 * (B / (Real.sqrt n * (W * Real.sqrt W))) / d ^ 2) :
    γ ≤ max A (B / 4) * (n / W + (n / W) ^ (3 / 2 : ℝ)) := by
  have h4n : 0 < 4 / n := by positivity
  have hX : 0 ≤ B / (Real.sqrt n * (W * Real.sqrt W)) := by positivity
  have h1 : 4 * (A / W) / d ≤ 4 * (A / W) / (4 / n) :=
    div_le_div_of_nonneg_left (by positivity) h4n hd
  have h2 : 4 * (B / (Real.sqrt n * (W * Real.sqrt W))) / d ^ 2 ≤
      4 * (B / (Real.sqrt n * (W * Real.sqrt W))) / (4 / n) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ h4n.le hd 2)
  have hratio : 0 < n / W := div_pos hn hW
  have hpow : (n / W) ^ (3 / 2 : ℝ) = (n / W) * Real.sqrt (n / W) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hratio, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hsn : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hsw : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW.le
  have hsnp : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hswp : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have e1 : 4 * (A / W) / (4 / n) = A * (n / W) := by
    field_simp
  have e2 : 4 * (B / (Real.sqrt n * (W * Real.sqrt W))) / (4 / n) ^ 2 =
      B / 4 * (n / W) ^ (3 / 2 : ℝ) := by
    rw [hpow, Real.sqrt_div hn.le]
    field_simp
    nlinarith [hsn, hsw]
  have hpow0 : 0 ≤ (n / W) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hratio.le _
  calc γ ≤ A * (n / W) + B / 4 * (n / W) ^ (3 / 2 : ℝ) := by linarith
    _ ≤ max A (B / 4) * (n / W) + max A (B / 4) * (n / W) ^ (3 / 2 : ℝ) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = _ := by ring

/-- Every physical neighboring contrast has absolute value at most one. -/
theorem abs_physicalPairContrast_le_one (p : Parameters) (α : Fin p.N) (i : ZMod p.n)
    (H : p.SiteMatrix) : |physicalPairContrast p α i H| ≤ 1 := by
  unfold physicalPairContrast
  have ha := physicalOrderedBlockMass_nonneg p H α i
  have hb := physicalOrderedBlockMass_nonneg p H α (i + 1)
  rw [abs_div, abs_of_nonneg (add_nonneg ha hb)]
  exact div_le_one_of_le₀ (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩) (add_nonneg ha hb)

theorem measurable_physicalPairContrast (p : Parameters) (α : Fin p.N) (i : ZMod p.n) :
    Measurable (physicalPairContrast p α i) := by
  unfold physicalPairContrast
  exact ((measurable_physicalOrderedBlockMass p α i).sub
    (measurable_physicalOrderedBlockMass p α (i + 1))).div
    ((measurable_physicalOrderedBlockMass p α i).add
      (measurable_physicalOrderedBlockMass p α (i + 1)))

theorem nonempty_pairExtension (p : Parameters) (model : p.GaussianRingModel) :
    Nonempty (PairExtension p model) :=
  ⟨PairExtension.ofLaw p model⟩

theorem integral_extendedPairMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n)
    (X : PairExtension p model) (F : p.SiteMatrix → E)
    (hF : AEStronglyMeasurable F (model.law : Measure p.SiteMatrix)) :
    (∫ ω, F (X.Hm ω) ∂extendedPairMeasure p α i X.P X.Hm) =
      ∫ H, F H ∂physicalPairMeasure p model α i := by
  unfold extendedPairMeasure physicalPairMeasure
  rw [integral_withDensity_eq_integral_smul (f := fun ω => physicalPairWeight p α i (X.Hm ω))
      ((measurable_physicalPairWeight p α i).comp X.measurable_Hm),
    integral_withDensity_eq_integral_smul (measurable_physicalPairWeight p α i)]
  have hsm : AEStronglyMeasurable (fun H => physicalPairWeight p α i H • F H)
      (X.P.map X.Hm) := by
    rw [X.map_eq]
    exact (measurable_physicalPairWeight p α i).aestronglyMeasurable.smul hF
  rw [← X.map_eq, integral_map X.measurable_Hm.aemeasurable hsm]

theorem ae_extendedPairMeasure (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n) (X : PairExtension p model) {q : p.SiteMatrix → Prop}
    (h : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), q H) :
    ∀ᵐ ω ∂extendedPairMeasure p α i X.P X.Hm, q (X.Hm ω) := by
  have h' : ∀ᵐ H ∂(X.P.map X.Hm), q H := by rw [X.map_eq]; exact h
  unfold extendedPairMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_of_ae_map X.measurable_Hm.aemeasurable h')

theorem extendedPairMeasure_isProbability (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n) (X : PairExtension p model) :
    IsProbabilityMeasure (extendedPairMeasure p α i X.P X.Hm) := by
  have h1 := (physicalPairMeasure_isProbability p model α i).measure_univ
  unfold physicalPairMeasure at h1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← X.map_eq,
    lintegral_map (measurable_physicalPairWeight p α i).coe_nnreal_ennreal X.measurable_Hm] at h1
  constructor
  unfold extendedPairMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact h1

/-- The physical centre estimate at one adjacent pair `S = {i, i+1}` under the pair law on the
enlarged space: the centre is measurable, square integrable and `E♯ j² ≤ B/(√n W^(3/2))`. -/
def CenterSecondMoment (p : Parameters) (α : Fin p.N) (i : ZMod p.n) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (Hm : Ω → p.SiteMatrix) (center : Ω → ℝ)
    (B : ℝ) : Prop :=
  AEStronglyMeasurable center (extendedPairMeasure p α i P Hm) ∧
    Integrable (fun ω => center ω ^ 2) (extendedPairMeasure p α i P Hm) ∧
    (∫ ω, center ω ^ 2 ∂extendedPairMeasure p α i P Hm) ≤
      B / (Real.sqrt (p.n : ℝ) * ((p.W : ℝ) * Real.sqrt (p.W : ℝ)))

/-- Large-width residual: the constants are chosen from `(b, θ, T)` before `n, W`, the model and
the bulk rank. -/
def QUEPairResidual (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) : Prop :=
  ∃ A B W₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
    ∀ (n W : ℕ) (hn : 4 ≤ n) (hW : 0 < W), (n : ℝ) ≤ T * (W : ℝ) → W₀ < (W : ℝ) →
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p θ α →
        ∃ (i : ZMod p.n) (X : PairExtension p model) (center : X.Ω → ℝ),
          CenterSecondMoment p α i X.P X.Hm center B ∧
            AngularModeComparison p α i X.P X.Hm center A

/-- One nonzero mode: signed pair identity, triangle inequality and the
AM-GM form of Cauchy-Schwarz plus Young (the mode bound). -/
theorem mode_variance_le_of_pair (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i m : ZMod p.n) (hm : m ≠ 0) (X : PairExtension p model)
    (center : X.Ω → ℝ) {A Y : ℝ}
    (hj : AEStronglyMeasurable center (extendedPairMeasure p α i X.P X.Hm))
    (hj2 : Integrable (fun ω => center ω ^ 2) (extendedPairMeasure p α i X.P X.Hm))
    (hY : (∫ ω, center ω ^ 2 ∂extendedPairMeasure p α i X.P X.Hm) ≤ Y)
    (hang : ‖∫ ω, ((physicalPairContrast p α i (X.Hm ω) - center ω : ℝ) : ℂ) *
        starRingEnd ℂ (physicalMode p α m (X.Hm ω)) ∂extendedPairMeasure p α i X.P X.Hm‖ ≤ A) :
    (∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix)) ≤
      4 * A / ‖(1 : ℂ) - ZMod.stdAddChar m‖ +
        4 * Y / ‖(1 : ℂ) - ZMod.stdAddChar m‖ ^ 2 := by
  have := extendedPairMeasure_isProbability p model α i X
  have hd4 := four_div_le_norm_one_sub_stdAddChar hm
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hdpos : 0 < ‖(1 : ℂ) - ZMod.stdAddChar m‖ := lt_of_lt_of_le (by positivity) hd4
  have hγ0 : 0 ≤ ∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix) :=
    integral_nonneg (fun H => sq_nonneg _)
  have hAm : Measurable (fun ω => physicalMode p α m (X.Hm ω)) :=
    (measurable_physicalMode p α m).comp X.measurable_Hm
  have hconj : Measurable (fun ω => starRingEnd ℂ (physicalMode p α m (X.Hm ω))) :=
    Complex.continuous_conj.measurable.comp hAm
  have hAe : ∀ᵐ ω ∂extendedPairMeasure p α i X.P X.Hm, ‖physicalMode p α m (X.Hm ω)‖ ≤ 1 :=
    ae_extendedPairMeasure p model α i X (q := fun H => ‖physicalMode p α m H‖ ≤ 1)
      (physicalMode_norm_le_one_ae p model α m)
  have hA2 : Integrable (fun ω => ‖physicalMode p α m (X.Hm ω)‖ ^ 2)
      (extendedPairMeasure p α i X.P X.Hm) := by
    apply (integrable_const (1 : ℝ)).mono' (hAm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hAe] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (physicalMode p α m (X.Hm ω))]
  have hint1 : Integrable (fun ω => (physicalPairContrast p α i (X.Hm ω) : ℂ) *
      starRingEnd ℂ (physicalMode p α m (X.Hm ω))) (extendedPairMeasure p α i X.P X.Hm) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((Complex.measurable_ofReal.comp
        ((measurable_physicalPairContrast p α i).comp X.measurable_Hm)).mul
        hconj).aestronglyMeasurable ?_
    filter_upwards [hAe] with ω hω
    rw [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    have hc := abs_physicalPairContrast_le_one p α i (X.Hm ω)
    nlinarith [abs_nonneg (physicalPairContrast p α i (X.Hm ω)),
      norm_nonneg (physicalMode p α m (X.Hm ω))]
  have hpt : ∀ ω, ‖(center ω : ℂ) * starRingEnd ℂ (physicalMode p α m (X.Hm ω))‖ ≤
      center ω ^ 2 / ‖(1 : ℂ) - ZMod.stdAddChar m‖ +
        ‖(1 : ℂ) - ZMod.stdAddChar m‖ / 4 * ‖physicalMode p α m (X.Hm ω)‖ ^ 2 := by
    intro ω
    rw [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, ← sq_abs (center ω)]
    exact amgm_div hdpos
  have hg : Integrable (fun ω => center ω ^ 2 / ‖(1 : ℂ) - ZMod.stdAddChar m‖ +
      ‖(1 : ℂ) - ZMod.stdAddChar m‖ / 4 * ‖physicalMode p α m (X.Hm ω)‖ ^ 2)
      (extendedPairMeasure p α i X.P X.Hm) :=
    (hj2.div_const _).add (hA2.const_mul _)
  have hint2 : Integrable (fun ω => (center ω : ℂ) * starRingEnd ℂ (physicalMode p α m (X.Hm ω)))
      (extendedPairMeasure p α i X.P X.Hm) :=
    hg.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hj).mul
      hconj.aestronglyMeasurable) (Filter.Eventually.of_forall hpt)
  have hvar : (∫ ω, ‖physicalMode p α m (X.Hm ω)‖ ^ 2 ∂extendedPairMeasure p α i X.P X.Hm) =
      ∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix) :=
    (integral_extendedPairMeasure p model α i X (fun H => ‖physicalMode p α m H‖ ^ 2)
      ((measurable_physicalMode p α m).norm.pow_const 2).aestronglyMeasurable).trans
      (physical_pair_variance_identity p model α m i)
  have hS2 : ‖∫ ω, (center ω : ℂ) * starRingEnd ℂ (physicalMode p α m (X.Hm ω))
      ∂extendedPairMeasure p α i X.P X.Hm‖ ≤
      Y / ‖(1 : ℂ) - ZMod.stdAddChar m‖ + ‖(1 : ℂ) - ZMod.stdAddChar m‖ / 4 *
        ∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix) := by
    calc _ ≤ ∫ ω, (center ω ^ 2 / ‖(1 : ℂ) - ZMod.stdAddChar m‖ +
          ‖(1 : ℂ) - ZMod.stdAddChar m‖ / 4 * ‖physicalMode p α m (X.Hm ω)‖ ^ 2)
            ∂extendedPairMeasure p α i X.P X.Hm :=
          norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpt)
      _ = (∫ ω, center ω ^ 2 ∂extendedPairMeasure p α i X.P X.Hm) /
            ‖(1 : ℂ) - ZMod.stdAddChar m‖ + ‖(1 : ℂ) - ZMod.stdAddChar m‖ / 4 *
            ∫ ω, ‖physicalMode p α m (X.Hm ω)‖ ^ 2 ∂extendedPairMeasure p α i X.P X.Hm := by
          rw [integral_add (hj2.div_const _) (hA2.const_mul _), integral_div,
            integral_const_mul]
      _ = (∫ ω, center ω ^ 2 ∂extendedPairMeasure p α i X.P X.Hm) /
            ‖(1 : ℂ) - ZMod.stdAddChar m‖ + ‖(1 : ℂ) - ZMod.stdAddChar m‖ / 4 *
            ∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix) := by
          rw [hvar]
      _ ≤ _ := by gcongr
  have hsplit : (∫ ω, (physicalPairContrast p α i (X.Hm ω) : ℂ) *
        starRingEnd ℂ (physicalMode p α m (X.Hm ω)) ∂extendedPairMeasure p α i X.P X.Hm) =
      (∫ ω, ((physicalPairContrast p α i (X.Hm ω) - center ω : ℝ) : ℂ) *
        starRingEnd ℂ (physicalMode p α m (X.Hm ω)) ∂extendedPairMeasure p α i X.P X.Hm) +
      ∫ ω, (center ω : ℂ) * starRingEnd ℂ (physicalMode p α m (X.Hm ω))
        ∂extendedPairMeasure p α i X.P X.Hm := by
    have h2 : (∫ ω, ((physicalPairContrast p α i (X.Hm ω) - center ω : ℝ) : ℂ) *
          starRingEnd ℂ (physicalMode p α m (X.Hm ω)) ∂extendedPairMeasure p α i X.P X.Hm) =
        (∫ ω, (physicalPairContrast p α i (X.Hm ω) : ℂ) *
          starRingEnd ℂ (physicalMode p α m (X.Hm ω)) ∂extendedPairMeasure p α i X.P X.Hm) -
        ∫ ω, (center ω : ℂ) * starRingEnd ℂ (physicalMode p α m (X.Hm ω))
          ∂extendedPairMeasure p α i X.P X.Hm := by
      rw [← integral_sub hint1 hint2]
      apply integral_congr_ae
      filter_upwards [] with ω
      push_cast
      ring
    rw [h2]
    ring
  have hT : (∫ ω, (physicalPairContrast p α i (X.Hm ω) : ℂ) *
        starRingEnd ℂ (physicalMode p α m (X.Hm ω)) ∂extendedPairMeasure p α i X.P X.Hm) =
      ∫ H, (physicalPairContrast p α i H : ℂ) * starRingEnd ℂ (physicalMode p α m H)
        ∂physicalPairMeasure p model α i :=
    integral_extendedPairMeasure p model α i X
      (fun H => (physicalPairContrast p α i H : ℂ) * starRingEnd ℂ (physicalMode p α m H))
      ((Complex.measurable_ofReal.comp (measurable_physicalPairContrast p α i)).mul
        (Complex.continuous_conj.measurable.comp
          (measurable_physicalMode p α m))).aestronglyMeasurable
  have hunit : ‖(ZMod.stdAddChar (i * m) : ℂ)‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hSnorm : ‖∫ ω, (physicalPairContrast p α i (X.Hm ω) : ℂ) *
        starRingEnd ℂ (physicalMode p α m (X.Hm ω)) ∂extendedPairMeasure p α i X.P X.Hm‖ =
      ‖(1 : ℂ) - ZMod.stdAddChar m‖ / 2 *
        ∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix) := by
    rw [hT, physical_signed_pair_identity_variance, norm_mul, norm_mul, norm_div, hunit,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγ0]
    norm_num
  have htri := norm_add_le
    (∫ ω, ((physicalPairContrast p α i (X.Hm ω) - center ω : ℝ) : ℂ) *
        starRingEnd ℂ (physicalMode p α m (X.Hm ω)) ∂extendedPairMeasure p α i X.P X.Hm)
    (∫ ω, (center ω : ℂ) * starRingEnd ℂ (physicalMode p α m (X.Hm ω))
        ∂extendedPairMeasure p α i X.P X.Hm)
  rw [← hsplit, hSnorm] at htri
  exact absorb_quarter hdpos (by linarith)

/-- The QUE bound from `QUEPairResidual`, the Fourier and Haar reductions and the finite-width
payment. -/
theorem que_of_pairResidual (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (h : QUEPairResidual b θ T hb hb') :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n W : ℕ) (hn : 4 ≤ n) (hW : 0 < W) (_hnW : (n : ℝ) ≤ T * (W : ℝ)),
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      Nonempty (FiniteRealization p) ∧
        ∀ (R : FiniteRealization p) (α : Fin p.N),
          IsBulkRank p θ α →
        ∀ v : p.Site → ℝ, (∀ x, |v x| ≤ 1) →
          R.spectral.queStatistic α v ≤
            C * (p.ratio + Real.rpow p.ratio (3 / 2 : ℝ)) +
              1 / ((W : ℝ) + 1) := by
  obtain ⟨A, B, W₀, hA, hB, hres⟩ := h
  refine ⟨max (max A (B / 4)) W₀,
    le_trans hA (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro n W hn hW hnW p
  refine ⟨nonempty_finiteRealization p, ?_⟩
  intro R α hα v hv
  have hn' : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hW' : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have key := BlockBand.QUE.Assembly.all_width_payment_of_large_width R.spectral α v hv
    (max A (B / 4)) W₀ (fun hlarge => by
      obtain ⟨i, X, center, ⟨hj, hj2, hX⟩, hang⟩ := hres n W hn hW hnW hlarge R.model α hα
      have hscale : 0 ≤ max A (B / 4) *
          ((p.n : ℝ) / p.W + ((p.n : ℝ) / p.W) ^ (3 / 2 : ℝ)) := by
        have := Real.rpow_nonneg (div_pos hn' hW').le (3 / 2 : ℝ)
        have : 0 ≤ max A (B / 4) := le_trans hA (le_max_left _ _)
        positivity
      refine physical_site_test_bound R.spectral α v hv _ hscale (fun m hm => ?_)
      exact mode_scale hn' hW' hA hB (@four_div_le_norm_one_sub_stdAddChar p.n ⟨p.n_pos.ne'⟩ m hm)
        (mode_variance_le_of_pair p R.model α i m hm X center hj hj2 hX (hang m hm)))
  exact key

/-- The physical centre and angular statements, for one shared centre family, give the residual
(pair `i = 0`, width threshold the larger of the two). -/
theorem pairResidual_of_contracts (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (w : PairCenterFamily) (hc : PhysicalCenterContract b θ T hb hb' w)
    (ha : PhysicalAngularModeContract b θ T hb hb' w) : QUEPairResidual b θ T hb hb' := by
  obtain ⟨B, W₁, hB, hcB⟩ := hc
  obtain ⟨A, W₂, hA, haA⟩ := ha
  refine ⟨A, B, max W₁ W₂, hA, hB, ?_⟩
  intro n W hn hW hnW hlarge p model α hα
  have h₁ : W₁ < (W : ℝ) := lt_of_le_of_lt (le_max_left _ _) hlarge
  have h₂ : W₂ < (W : ℝ) := lt_of_le_of_lt (le_max_right _ _) hlarge
  have hcen := hcB n W hn hW hnW h₁ model α hα 0
  have hang := haA n W hn hW hnW h₂ model α hα 0
  exact ⟨0, (w _ model α 0).X, (w _ model α 0).center,
    ⟨(w _ model α 0).aesm, (w _ model α 0).sq_integrable, hcen⟩, hang⟩

/-- **The QUE theorem from the centre and angular statements.** The conclusion is the body of
`BlockBand.que`; the hypotheses are the centre and angular statements for one centre family. -/
theorem que_of_contracts (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (w : PairCenterFamily) (hc : PhysicalCenterContract b θ T hb hb' w)
    (ha : PhysicalAngularModeContract b θ T hb hb' w) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n W : ℕ) (hn : 4 ≤ n) (hW : 0 < W) (_hnW : (n : ℝ) ≤ T * (W : ℝ)),
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      Nonempty (FiniteRealization p) ∧
        ∀ (R : FiniteRealization p) (α : Fin p.N),
          IsBulkRank p θ α →
        ∀ v : p.Site → ℝ, (∀ x, |v x| ≤ 1) →
          R.spectral.queStatistic α v ≤
            C * (p.ratio + Real.rpow p.ratio (3 / 2 : ℝ)) +
              1 / ((W : ℝ) + 1) :=
  que_of_pairResidual b θ T hb hb' (pairResidual_of_contracts b θ T hb hb' w hc ha)

end BlockBand.QUE.PairResidual
