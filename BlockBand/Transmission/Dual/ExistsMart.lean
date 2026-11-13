module

public import BlockBand.Transmission.Dual.ExistsSDE
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionSuper
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionCalculus
public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblemConverse

/-!
# `exists_` at `p = 1`: martingales and supermartingales along the exit-time solutions

Measure `P₁`, filtration `𝓖₁`, the flat paths `Yf n` of a `SolFamily D₀ z` (`ExistsSDE`), and
`L₁ = mpGenerator (flatDrift D₀ 1) (flatDiff D₀ 1)` (the flat `𝒟₁`, `mpGenerator_flat`). For
`G` measurable and `C²` on the open chamber `𝒞₁`:
* `isCSM_G`: `G(Yf n)` is a continuous semimartingale with drift `1{t ≤ e_n} L₁G(Yf n)`
  (the Itô formula on `U = 𝒞₁`);
* `hasMart_G`: if `L₁G` is continuous on `𝒞₁`, then
  `G(Yf n t) − G(Yf n 0) − ∫_(0,t] 1{s ≤ e_n} L₁G(Yf n s) ds` has a `𝓖₁`-martingale
  modification (the path stays in the compact `Kset z n`, so localization is removed by
  domination);
* `lintegral_discount_le`: if `G ≥ 0` and `L₁G ≤ cG` on `𝒞₁` (`c ≥ 0`), then for every
  `𝓖₁`-stopping time `θ` and `T`, `E[e^{−c(T∧θ)} G(Yf n (T∧θ))] ≤ G(z)` (lower integral; the
  discounted process is a nonnegative semimartingale with nonpositive drift, stopped at `θ`);
  `measure_discount_le` is the Markov form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.NativeSDE
open scoped NNReal ENNReal

/-- The flat level-one dual generator. -/
abbrev L₁ (D0 : ℝ) (G : (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → ℝ :=
  mpGenerator (flatDrift D0 1) (flatDiff D0 1) G

variable {D0 : ℝ} {z : Fin 2 → ℝ}

namespace SolFamily

variable (F : SolFamily D0 z)

theorem mpGenerator_switchOff (n : ℕ) {G : (Fin 2 → ℝ) → ℝ} (t : ℝ≥0) (ω : Ω₁) :
    mpGenerator (fun _ => switchOff (F.e n) (fun t ω => flatDrift D0 1 (F.Yf n t ω)) t ω)
      (fun _ => switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω) G (F.Yf n t ω) =
      switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) t ω := by
  unfold switchOff
  split_ifs
  · rfl
  · simp [mpGenerator]

/-- **`G(Yf n)` is a continuous semimartingale** with drift `1{t ≤ e_n} L₁G(Yf n)`. -/
theorem isCSM_G (hD0 : 0 < D0) (n : ℕ) {G : (Fin 2 → ℝ) → ℝ} (hGm : Measurable G)
    (hG : ContDiffOn ℝ 2 G (flatChamber 1)) :
    IsContinuousSemimartingale (d := 1) P₁ 𝓖₁ (fun t ω (_ : Fin 1) => G (F.Yf n t ω))
      (fun t ω (_ : Fin 1) => switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) t ω)
      (fun t ω => Matrix.of fun (_ _ : Fin 1) => itoBracket (fun q : ℝ × (Fin 2 → ℝ) => G q.2)
        (F.Yf n t ω) t (switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω)) := by
  have hφ : ContDiffOn ℝ 2 (fun q : ℝ × (Fin 2 → ℝ) => G q.2) (univ ×ˢ flatChamber 1) :=
    hG.comp contDiffOn_snd fun q hq => hq.2
  have H := SemimartingaleIto.semimartingaleItoFormula_holds 2 Ω₁ P₁ 𝓖₁ (F.Yf n) _ _
    (F.isCSM_Yf hD0 n) (flatChamber 1) (isOpen_flatChamber 1)
    (Eventually.of_forall fun ω t => F.Yf_mem n t ω) (fun q : ℝ × (Fin 2 → ℝ) => G q.2)
    (hGm.comp measurable_snd) hφ
  have e : (fun (t : ℝ≥0) (ω : Ω₁) (_ : Fin 1) => itoDrift (fun q : ℝ × (Fin 2 → ℝ) => G q.2)
      (F.Yf n t ω) t (switchOff (F.e n) (fun t ω => flatDrift D0 1 (F.Yf n t ω)) t ω)
      (switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω)) =
      fun t ω _ => switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) t ω := by
    funext t ω _
    rw [itoDrift_comp_snd ((hG.contDiffAt ((isOpen_flatChamber 1).mem_nhds (F.Yf_mem n t ω))))]
    exact F.mpGenerator_switchOff n t ω
  rw [e] at H
  exact H

/-- A continuous function on the chamber is bounded on the `n`-th compact. -/
theorem exists_bound_K (n : ℕ) {G : (Fin 2 → ℝ) → ℝ} (hG : ContinuousOn G (flatChamber 1)) :
    ∃ C, 0 ≤ C ∧ ∀ t ω, |G (F.Yf n t ω)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Kset z n).exists_bound_of_continuousOn
    (hG.mono (Kset_subset z n))
  exact ⟨max C 0, le_max_right _ _, fun t ω =>
    (Real.norm_eq_abs _ ▸ hC _ (F.Yf_mem_K n t ω)).trans (le_max_left _ _)⟩

/-- **The compensated process of `G(Yf n)` has a martingale modification.** -/
theorem hasMart_G (hD0 : 0 < D0) (n : ℕ) {G : (Fin 2 → ℝ) → ℝ} (hGm : Measurable G)
    (hG : ContDiffOn ℝ 2 G (flatChamber 1)) (hL : ContinuousOn (L₁ D0 G) (flatChamber 1)) :
    HasMartingaleModification P₁ 𝓖₁ (fun t ω => G (F.Yf n t ω) - G (F.Yf n 0 ω) -
      ∫ s in Ioc (0 : ℝ) t, switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) s.toNNReal ω) := by
  obtain ⟨τ, -, hτlim, hm⟩ := (F.isCSM_G hD0 n hGm hG).localizing
  obtain ⟨CG, hCG0, hCG⟩ := F.exists_bound_K n hG.continuousOn
  obtain ⟨CL, hCL0, hCL⟩ := F.exists_bound_K n hL
  refine Bridges.hasMartingaleModification_of_localized hτlim (fun k => (hm k).1 0)
    fun t => ⟨2 * CG + CL * t, Eventually.of_forall fun ω s hs => ?_⟩
  have hint : |∫ u in Ioc (0 : ℝ) s,
      switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) u.toNNReal ω| ≤ CL * t := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := CL)
      (s := Ioc (0 : ℝ) (s : ℝ))
      (f := fun u : ℝ => switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) u.toNNReal ω)
      measure_Ioc_lt_top fun u _ => by
        unfold switchOff; split_ifs
        · exact hCL _ _
        · simpa using hCL0
    rw [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by simp)] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCL0)
    simpa using (NNReal.coe_le_coe.2 hs)
  have h1 := hCG s ω
  have h2 := hCG 0 ω
  show |G (F.Yf n s ω) - G (F.Yf n 0 ω) - _| ≤ _
  calc _ ≤ |G (F.Yf n s ω)| + |G (F.Yf n 0 ω)| + |∫ u in Ioc (0 : ℝ) s,
        switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) u.toNNReal ω| := by
          refine (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _) |>.trans ?_
          linarith
    _ ≤ _ := by linarith

/-- The discount `(t, z) ↦ e^{−ct} z₀` on `ℝ × ℝ¹`, as a `lyapFun`. -/
def discount (c : ℝ) : ℝ × (Fin 1 → ℝ) → ℝ :=
  lyapFun (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ)) (fun y => y 0 - 1) c

theorem contDiff_shift1 : ContDiff ℝ 2 fun y : Fin 1 → ℝ => y 0 - 1 :=
  (contDiff_apply ℝ ℝ 0).sub contDiff_const

theorem discount_apply (c : ℝ) (p : ℝ × (Fin 1 → ℝ)) : discount c p = exp (-c * p.1) * p.2 0 := by
  simp only [discount, lyapFun, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl',
    id_eq]
  ring

theorem itoDrift_discount (c : ℝ) (y : Fin 1 → ℝ) (t : ℝ≥0) (β : Fin 1 → ℝ)
    (α : Matrix (Fin 1) (Fin 1) ℝ) :
    itoDrift (discount c) y t β α = exp (-c * t) * (-c * y 0 + β 0) := by
  have hd : ∀ w, fderiv ℝ (fun y : Fin 1 → ℝ => y 0 - 1) w =
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0 := fun w =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt.sub_const
      1).fderiv
  have hdd : ∀ w, fderiv ℝ (fderiv ℝ fun y : Fin 1 → ℝ => y 0 - 1) w = 0 := fun w => by
    rw [show (fderiv ℝ fun y : Fin 1 → ℝ => y 0 - 1) = fun _ =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0 from funext hd]
    exact fderiv_const_apply _
  unfold itoDrift partialTime partialSpace partialSpace2 discount
  simp only [fderiv_lyapFun_time _ c contDiff_shift1, fderiv_lyapFun_space _ c contDiff_shift1,
    fderiv_fderiv_lyapFun_space _ c contDiff_shift1, hd, hdd, Fin.sum_univ_one,
    ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl', id_eq,
    ContinuousLinearMap.proj_apply, Pi.single_eq_same]
  have h0 : ∀ u v : Fin 1 → ℝ, (0 : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) →L[ℝ] ℝ) u v = 0 :=
    fun _ _ => rfl
  rw [h0]
  ring

/-- **Discounted supermartingale bound** at a stopping time. -/
theorem lintegral_discount_le (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) (n : ℕ)
    {G : (Fin 2 → ℝ) → ℝ} (hGm : Measurable G) (hG : ContDiffOn ℝ 2 G (flatChamber 1))
    (hG0 : ∀ y ∈ flatChamber 1, 0 ≤ G y) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ y ∈ flatChamber 1, L₁ D0 G y ≤ c * G y) {θ : Ω₁ → WithTop ℝ≥0}
    (hθ : IsStoppingTime 𝓖₁ θ) (T : ℝ≥0) :
    Measurable (fun ω => exp (-c * (min (T : WithTop ℝ≥0) (θ ω)).untopA) *
      G (F.Yf n (min (T : WithTop ℝ≥0) (θ ω)).untopA ω)) ∧
    ∫⁻ ω, ENNReal.ofReal (exp (-c * (min (T : WithTop ℝ≥0) (θ ω)).untopA) *
      G (F.Yf n (min (T : WithTop ℝ≥0) (θ ω)).untopA ω)) ∂P₁ ≤ ENNReal.ofReal (G z) := by
  have H1 := F.isCSM_G hD0 n hGm hG
  have H2 := SemimartingaleIto.semimartingaleItoFormula_holds 1 Ω₁ P₁ 𝓖₁ _ _ _ H1 univ
    isOpen_univ (Eventually.of_forall fun _ _ => mem_univ _) (discount c)
    ((contDiff_lyapFun _ c contDiff_shift1).continuous.measurable)
    (contDiff_lyapFun _ c contDiff_shift1).contDiffOn
  have H3 := Semimartingale.stoppedSemimartingale_holds 1 Ω₁ P₁ 𝓖₁ _ _ _ H2 θ hθ
  have hβ : ∀ᵐ ω ∂P₁, ∀ s : ℝ≥0, switchAfter θ (fun t ω (_ : Fin 1) => itoDrift (discount c)
      (fun _ => G (F.Yf n t ω)) t (fun _ => switchOff (F.e n)
        (fun t ω => L₁ D0 G (F.Yf n t ω)) t ω) (Matrix.of fun (_ _ : Fin 1) =>
          itoBracket (fun q : ℝ × (Fin 2 → ℝ) => G q.2) (F.Yf n t ω) t
            (switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω))) s ω 0 ≤ 0 := by
    refine Eventually.of_forall fun ω s => ?_
    unfold switchAfter
    split_ifs
    · dsimp only
      rw [itoDrift_discount]
      refine mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le ?_
      have hy := F.Yf_mem n s ω
      unfold switchOff
      split_ifs
      · nlinarith [hc _ hy, hG0 _ hy]
      · nlinarith [hG0 _ hy]
    · exact le_rfl
  have hZ : ∀ᵐ ω ∂P₁, ∀ t, 0 ≤ stoppedProcess (fun (t : ℝ≥0) (ω : Ω₁) (_ : Fin 1) =>
      discount c ((t : ℝ), fun _ => G (F.Yf n t ω))) θ t ω 0 := by
    refine Eventually.of_forall fun ω t => ?_
    simp only [stoppedProcess, discount_apply]
    exact mul_nonneg (exp_pos _).le (hG0 _ (F.Yf_mem n _ ω))
  have h := lintegral_le_of_nonpos_drift H3 hβ hZ (A := univ) MeasurableSet.univ
    (B := G z) (fun ω _ => by
      simp only [stoppedProcess, discount_apply]
      rw [min_eq_left (by rw [WithTop.coe_zero]; exact bot_le)]
      simp [F.Yf_zero hz]) T
  have hm : Measurable fun ω => stoppedProcess (fun (t : ℝ≥0) (ω : Ω₁) (_ : Fin 1) =>
      discount c ((t : ℝ), fun _ => G (F.Yf n t ω))) θ T ω 0 :=
    (measurable_pi_apply 0).comp (((H3.adapted T).mono (𝓖₁.le T)).measurable)
  simp only [stoppedProcess, discount_apply] at hm
  refine ⟨hm, ?_⟩
  simp only [Measure.restrict_univ, stoppedProcess, discount_apply] at h
  refine h.trans (le_of_eq ?_)
  have h0 : ∀ ω, (min ((0 : ℝ≥0) : WithTop ℝ≥0) (θ ω)).untopA = 0 := fun ω => by
    rw [min_eq_left (by rw [WithTop.coe_zero]; exact bot_le)]; rfl
  simp only [h0, F.Yf_zero hz, NNReal.coe_zero, mul_zero, exp_zero, one_mul, lintegral_const,
    measure_univ, mul_one]

/-- **Markov form of the discounted bound.** -/
theorem measure_discount_le (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) (n : ℕ)
    {G : (Fin 2 → ℝ) → ℝ} (hGm : Measurable G) (hG : ContDiffOn ℝ 2 G (flatChamber 1))
    (hG0 : ∀ y ∈ flatChamber 1, 0 ≤ G y) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ y ∈ flatChamber 1, L₁ D0 G y ≤ c * G y) {θ : Ω₁ → WithTop ℝ≥0}
    (hθ : IsStoppingTime 𝓖₁ θ) (T : ℝ≥0) (A : Set Ω₁) (b : ℝ)
    (hA : ∀ ω ∈ A, b ≤ exp (-c * (min (T : WithTop ℝ≥0) (θ ω)).untopA) *
      G (F.Yf n (min (T : WithTop ℝ≥0) (θ ω)).untopA ω)) :
    ENNReal.ofReal b * P₁ A ≤ ENNReal.ofReal (G z) := by
  obtain ⟨hm, hle⟩ := F.lintegral_discount_le hD0 hz n hGm hG hG0 hc0 hc hθ T
  refine le_trans ?_ ((mul_meas_ge_le_lintegral₀ hm.ennreal_ofReal.aemeasurable
    (ENNReal.ofReal b)).trans hle)
  exact mul_le_mul_right (measure_mono fun ω hω => ENNReal.ofReal_le_ofReal (hA ω hω)) _

end SolFamily

end BlockBand.Transmission.Dual.Exists
