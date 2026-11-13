module

public import BlockBand.Transmission.Dual.GNegCalc
public import BlockBand.Transmission.Dual.GPairBase
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionSuper
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract

/-!
# Negative moments by a parabolic supersolution: the small-ball bound

Measure `P₁`, filtration `𝓖₁`, the pair base SDE solution `X` (`exists_pairBase_sde`) and
its flat image `Y = toFlat ∘ X` (a continuous semimartingale with the base characteristics,
`isCSM_pairBase`), from any start.
* **`lintegral_exp_gapG_le`** (Laplace bound): for `T, s₁ > 0` and `q₁ = e^{−D₀ s₁}`,
  `E[exp(−(2q₁/(1−q₁)) g(Y_T))] ≤ (1−q₁)² / (1 − e^{−D₀T})²`. Proof: Itô's formula for
  `negPhi D₀ s₁ T` on `ℝ × {x > 0}`, stopped at the constant time `T`; the drift is `≤ 0` up to
  `T` (`itoDrift_negPhi_nonpos`), so `lintegral_le_of_nonpos_drift` applies.
* **`measure_gapG_lt_le`** (small-ball bound, the negative-moment estimate in the form used for
  the atomlessness of the lifetime): `P₁(g(Y_T) < η) ≤ 4e η² / (1 − e^{−D₀T})²` for every
  `η > 0` (Chernoff with `N = 1/η`, i.e. `q₁ = 1/(1+2η)`). Since `g ≤ x + y`, this bounds
  `P₁(X_T + Y_T < η)`.

No comparison process, no Gaussian law and no strong Markov property is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {D0 : ℝ} {z : Fin 2 → ℝ} {X : ℝ≥0 → Ω₁ → Fin 2 → ℝ}

theorem toFlat_mem_posU (w : Fin 2 → ℝ) : toFlat w ∈ posU := by
  show 0 < toFlat w 0
  rw [toFlat_zero]; exact exp_pos _

theorem gapG_toFlat_pos (w : Fin 2 → ℝ) : 0 < gapG (toFlat w) :=
  gapG_pos (toFlat_mem_posU w) (by rw [toFlat_one]; exact lgt_pos _)

/-- **Supermartingale bound** for `negPhi` at the horizon `T`. -/
theorem lintegral_negPhi_le (hD0 : 0 < D0)
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) {s₁ : ℝ}
    (hs : 0 < s₁) (T : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (negPhi D0 s₁ T ((T : ℝ), toFlat (X T ω))) ∂P₁ ≤
      ENNReal.ofReal (Af D0 s₁ T 0) := by
  have H1 := isCSM_pairBase hD0 hX
  have H2 := SemimartingaleIto.semimartingaleItoFormula_holds 2 Ω₁ P₁ 𝓖₁ _ _ _ H1 posU
    isOpen_posU (Eventually.of_forall fun ω t => toFlat_mem_posU _) (negPhi D0 s₁ T)
    (measurable_negPhi hD0 hs) (contDiffOn_negPhi hD0 hs)
  have H3 := Semimartingale.stoppedSemimartingale_holds 1 Ω₁ P₁ 𝓖₁ _ _ _ H2
    (fun _ => (T : WithTop ℝ≥0)) (isStoppingTime_const 𝓖₁ T)
  have hβ : ∀ᵐ ω ∂P₁, ∀ s : ℝ≥0, switchAfter (fun _ => (T : WithTop ℝ≥0))
      (fun t ω (_ : Fin 1) => itoDrift (negPhi D0 s₁ T) (toFlat (X t ω)) t
        (flatBaseDrift D0 1 (toFlat (X t ω))) (flatDiff D0 1 (toFlat (X t ω)))) s ω 0 ≤ 0 := by
    refine Eventually.of_forall fun ω s => ?_
    unfold switchAfter
    split_ifs with h
    · have hsT : (s : ℝ) ≤ T := NNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 h)
      exact itoDrift_negPhi_nonpos hD0 hs (by linarith) (toFlat_mem_posU _)
    · exact le_rfl
  have hZ : ∀ᵐ ω ∂P₁, ∀ t, 0 ≤ stoppedProcess (fun (t : ℝ≥0) (ω : Ω₁) (_ : Fin 1) =>
      negPhi D0 s₁ T ((t : ℝ), toFlat (X t ω))) (fun _ => (T : WithTop ℝ≥0)) t ω 0 :=
    Eventually.of_forall fun ω t => negPhi_nonneg hD0 hs _
  have h0 : (min ((0 : ℝ≥0) : WithTop ℝ≥0) (T : WithTop ℝ≥0)).untopA = 0 := by
    rw [min_eq_left (by rw [WithTop.coe_zero]; exact bot_le)]; rfl
  have hR : ∀ ω, stoppedProcess (fun (t : ℝ≥0) (ω : Ω₁) (_ : Fin 1) =>
      negPhi D0 s₁ T ((t : ℝ), toFlat (X t ω))) (fun _ => (T : WithTop ℝ≥0)) 0 ω 0 ≤
      Af D0 s₁ T 0 := fun ω => by
    simp only [stoppedProcess, h0, NNReal.coe_zero]
    exact negPhi_le hD0 hs (gapG_toFlat_pos _).le
  have hL : ∀ ω, stoppedProcess (fun (t : ℝ≥0) (ω : Ω₁) (_ : Fin 1) =>
      negPhi D0 s₁ T ((t : ℝ), toFlat (X t ω))) (fun _ => (T : WithTop ℝ≥0)) T ω 0 =
      negPhi D0 s₁ T ((T : ℝ), toFlat (X T ω)) := fun ω => by
    simp only [stoppedProcess, min_self]
    rfl
  have h := lintegral_le_of_nonpos_drift H3 hβ hZ (A := univ) MeasurableSet.univ
    (B := Af D0 s₁ T 0) (fun ω _ => hR ω) T
  try simp only [Measure.restrict_univ] at h
  simp_rw [hL] at h
  refine h.trans ((lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hR ω)).trans ?_)
  simp

theorem kap_self {s₁ T : ℝ} (hs : 0 < s₁) : kap s₁ T T = s₁ := by
  rw [kap_eq hs (by linarith)]; ring

theorem kap_zero {s₁ T : ℝ} (hs : 0 < s₁) (hT : 0 ≤ T) : kap s₁ T 0 = s₁ + T := by
  rw [kap_eq hs (by linarith)]; ring

/-- **Laplace bound** at the horizon `T`. -/
theorem lintegral_exp_gapG_le (hD0 : 0 < D0)
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) {s₁ : ℝ}
    (hs : 0 < s₁) {T : ℝ≥0} (hT : 0 < T) :
    ∫⁻ ω, ENNReal.ofReal (exp (-(2 * exp (-(D0 * s₁)) / (1 - exp (-(D0 * s₁))) *
      gapG (toFlat (X T ω))))) ∂P₁ ≤
      ENNReal.ofReal ((1 - exp (-(D0 * s₁))) ^ 2 / (1 - exp (-(D0 * T))) ^ 2) := by
  set q₁ := exp (-(D0 * s₁))
  have hq1 : q₁ < 1 := by
    have := qf_lt_one (T := (T : ℝ)) hD0 hs T
    rwa [qf, kap_self hs] at this
  have hc0 : 0 < (1 - q₁) ^ 2 := pow_pos (by linarith) 2
  have hAT : Af D0 s₁ T T = ((1 - q₁) ^ 2)⁻¹ := by rw [Af, qf, kap_self hs]
  have hT' : (0 : ℝ) < T := hT
  have hb : 0 < 1 - exp (-(D0 * T)) := by
    have : exp (-(D0 * T)) < 1 := by
      calc exp (-(D0 * T)) < exp 0 := exp_lt_exp.2 (by nlinarith)
        _ = 1 := exp_zero
    linarith
  have hA0 : Af D0 s₁ T 0 ≤ ((1 - exp (-(D0 * T))) ^ 2)⁻¹ := by
    rw [Af, qf, kap_zero hs hT'.le]
    have h1 : exp (-(D0 * (s₁ + T))) ≤ exp (-(D0 * T)) := exp_le_exp.2 (by nlinarith)
    have h2 : 0 < 1 - exp (-(D0 * (s₁ + T))) := by linarith
    exact inv_anti₀ (pow_pos hb 2) (pow_le_pow_left₀ hb.le (by linarith) 2)
  have key := lintegral_negPhi_le hD0 hX hs T
  have e : ∀ ω, ENNReal.ofReal (negPhi D0 s₁ T ((T : ℝ), toFlat (X T ω))) =
      ENNReal.ofReal ((1 - q₁) ^ 2)⁻¹ * ENNReal.ofReal (exp (-(2 * q₁ / (1 - q₁) *
        gapG (toFlat (X T ω))))) := fun ω => by
    rw [← ENNReal.ofReal_mul (inv_pos.2 hc0).le, negPhi, hAT]
    simp only [Nf, qf, kap_self hs]; rfl
  simp_rw [e] at key
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at key
  have hne : ENNReal.ofReal ((1 - q₁) ^ 2)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc0)).ne'
  calc _ ≤ ENNReal.ofReal (Af D0 s₁ T 0) / ENNReal.ofReal ((1 - q₁) ^ 2)⁻¹ := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact key
    _ ≤ _ := by
        rw [← ENNReal.ofReal_div_of_pos (inv_pos.2 hc0)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_inv_eq_mul, div_eq_mul_inv, mul_comm]
        exact mul_le_mul_of_nonneg_left hA0 hc0.le

/-- **The small-ball bound** `P₁(g(Y_T) < η) ≤ 4e η² / (1 − e^{−D₀T})²`. -/
theorem measure_gapG_lt_le (hD0 : 0 < D0)
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) {T : ℝ≥0}
    (hT : 0 < T) {η : ℝ} (hη : 0 < η) :
    P₁ {ω | gapG (toFlat (X T ω)) < η} ≤
      ENNReal.ofReal (4 * exp 1 * η ^ 2 / (1 - exp (-(D0 * T))) ^ 2) := by
  set s₁ := Real.log (1 + 2 * η) / D0
  have h12 : 0 < 1 + 2 * η := by linarith
  have hs : 0 < s₁ := div_pos (Real.log_pos (by linarith)) hD0
  have hq : exp (-(D0 * s₁)) = (1 + 2 * η)⁻¹ := by
    rw [show D0 * s₁ = Real.log (1 + 2 * η) from mul_div_cancel₀ _ hD0.ne', exp_neg, exp_log h12]
  have hN : 2 * exp (-(D0 * s₁)) / (1 - exp (-(D0 * s₁))) = η⁻¹ := by
    rw [hq]; field_simp; ring
  have hL := lintegral_exp_gapG_le hD0 hX hs hT
  rw [hN, hq] at hL
  have hT' : (0 : ℝ) < T := hT
  have hb : 0 < (1 - exp (-(D0 * T))) ^ 2 := by
    have : exp (-(D0 * T)) < 1 := by
      calc exp (-(D0 * T)) < exp 0 := exp_lt_exp.2 (by nlinarith)
        _ = 1 := exp_zero
    exact pow_pos (by linarith) 2
  have hm : Measurable fun ω => exp (-(η⁻¹ * gapG (toFlat (X T ω)))) := by
    have : Measurable fun ω => toFlat (X T ω) :=
      contDiff_toFlat.continuous.measurable.comp ((hX.1.adapted T).mono (𝓖₁.le T)).measurable
    exact ((measurable_gapG.comp this).const_mul _).neg.exp
  have hcheb := mul_meas_ge_le_lintegral₀ (μ := P₁) hm.ennreal_ofReal.aemeasurable
    (ENNReal.ofReal (exp (-1)))
  have hsub : {ω | gapG (toFlat (X T ω)) < η} ⊆
      {ω | ENNReal.ofReal (exp (-1)) ≤ ENNReal.ofReal (exp (-(η⁻¹ * gapG (toFlat (X T ω)))))} := by
    intro ω hω
    refine ENNReal.ofReal_le_ofReal (exp_le_exp.2 (neg_le_neg ?_))
    have : η⁻¹ * gapG (toFlat (X T ω)) ≤ η⁻¹ * η :=
      mul_le_mul_of_nonneg_left (le_of_lt hω) (inv_pos.2 hη).le
    rwa [inv_mul_cancel₀ hη.ne'] at this
  have h1 : ENNReal.ofReal (exp (-1)) * P₁ {ω | gapG (toFlat (X T ω)) < η} ≤
      ENNReal.ofReal ((1 - (1 + 2 * η)⁻¹) ^ 2 / (1 - exp (-(D0 * T))) ^ 2) :=
    ((mul_le_mul_right (measure_mono hsub) _)).trans (hcheb.trans hL)
  have hne : ENNReal.ofReal (exp (-1)) ≠ 0 := (ENNReal.ofReal_pos.2 (exp_pos _)).ne'
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_div_of_pos (exp_pos _)] at h1
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have hq2 : 1 - (1 + 2 * η)⁻¹ ≤ 2 * η := by
    rw [sub_le_iff_le_add]
    have : 1 ≤ (1 + 2 * η)⁻¹ + 2 * η := by
      have hi : 0 < (1 + 2 * η)⁻¹ := inv_pos.2 h12
      have : (1 + 2 * η)⁻¹ * (1 + 2 * η) = 1 := inv_mul_cancel₀ h12.ne'
      nlinarith
    linarith
  have hq3 : 0 ≤ 1 - (1 + 2 * η)⁻¹ := by
    have : (1 + 2 * η)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  rw [div_right_comm, div_le_div_iff_of_pos_right hb]
  have hsq : (1 - (1 + 2 * η)⁻¹) ^ 2 ≤ (2 * η) ^ 2 := pow_le_pow_left₀ hq3 hq2 2
  have hexp : (exp (-1))⁻¹ = exp 1 := by rw [← exp_neg, neg_neg]
  rw [div_eq_mul_inv, hexp]
  nlinarith [exp_pos 1]

end BlockBand.Transmission.Dual.G
