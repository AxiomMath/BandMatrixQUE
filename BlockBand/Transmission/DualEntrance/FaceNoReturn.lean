module

public import BlockBand.Transmission.DualEntrance.FaceOcc
public import BlockBand.Transmission.Dual.Hitting
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract

/-!
# Generic one-dimensional entrance lemma, part (ii): no return to the face

Setting of `IsEntranceFace Q 𝓖 z β α τ c K M B`. Fix a deterministic time `s`. For a level
`η ∈ (0, 1)` let `ρ = inf{u ≥ s : z_u ≤ η}`, the hitting time `hitLe V η` of the
right-continuous, lower semicontinuous process `V_u = z_u + 1{u < s}` (a stopping time).
On `A = {η₁ ≤ z_s ≤ m} ∈ 𝓖_s`, the process `faceFun η C T (u∧ρ, z_{u∧ρ})` is nonnegative on
`[0, T]` with drift `≤ 0`, so the restarted bound (`lintegral_restart_le`) gives
`log(1/(2η)) Q(A ∩ {ρ ≤ T}) ≤ −log η₁ + m + 1 + CT`. With
`η = η₁ e^{−(i+1)}/2` this is `(i+1) Q(A ∩ {ρ ≤ T}) ≤ B'`, so a return to `0` in `[s, T]`
has probability `0` on `A` (`measure_return_eq_zero`). Union over `η₁ = 1/(j+1)`, `m`, `T`:
**`ae_noReturn`**: a.s., `z_s > 0` implies `z_t > 0` for every `t ≥ s`. The argument stops at
levels.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualEntrance

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic
  BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- `z_u + 1{u < s}`: its first passage below a level `η < 1` happens after `s`. -/
def postV (z : ℝ≥0 → Ω → Fin 1 → ℝ) (s : ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  z u ω 0 + (Iio s).indicator (fun _ => (1 : ℝ)) u

namespace IsEntranceFace

variable {z β : ℝ≥0 → Ω → Fin 1 → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ}
  {τ : Ω → WithTop ℝ≥0} {c K M B : ℝ} (hF : IsEntranceFace Q 𝓖 z β α τ c K M B)
include hF

theorem postV_rc (s : ℝ≥0) (ω : Ω) (u : ℝ≥0) :
    Tendsto (fun v => postV z s v ω) (𝓝[≥] u) (𝓝 (postV z s u ω)) := by
  have h1 : Tendsto (fun v => z v ω 0) (𝓝[≥] u) (𝓝 (z u ω 0)) :=
    ((hF.cont ω).tendsto u).mono_left nhdsWithin_le_nhds
  have h2 : (fun v => (Iio s).indicator (fun _ => (1 : ℝ)) v) =ᶠ[𝓝[≥] u]
      fun _ => (Iio s).indicator (fun _ => (1 : ℝ)) u := by
    rcases lt_or_ge u s with hus | hsu
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds hus)] with v hv
      simp [indicator_of_mem hv, indicator_of_mem (show u ∈ Iio s from hus)]
    · filter_upwards [self_mem_nhdsWithin] with v (hv : u ≤ v)
      rw [indicator_of_notMem (show v ∉ Iio s from not_lt.2 (hsu.trans hv)),
        indicator_of_notMem (show u ∉ Iio s from not_lt.2 hsu)]
  exact h1.add (tendsto_const_nhds.congr' h2.symm)

theorem postV_lsc (s : ℝ≥0) (ω : Ω) : LowerSemicontinuous fun u => postV z s u ω :=
  (hF.cont ω).lowerSemicontinuous.add (isOpen_Iio.lowerSemicontinuous_indicator zero_le_one)

theorem isStoppingTime_post (s : ℝ≥0) (η : ℝ) : IsStoppingTime 𝓖 (hitLe (postV z s) η) :=
  isStoppingTime_hitLe (fun u => ((continuous_apply 0).measurable.comp
    (hF.csm.adapted u).measurable).add measurable_const) (fun ω u => hF.postV_rc s ω u)
    (fun ω => hF.postV_lsc s ω) η

theorem le_post {s : ℝ≥0} {η : ℝ} (hη : η < 1) (ω : Ω) :
    (s : WithTop ℝ≥0) ≤ hitLe (postV z s) η ω := by
  refine le_iInf₂ fun u hu => WithTop.coe_le_coe.2 ?_
  by_contra h
  have h' : u ∈ Iio s := not_le.1 h
  have : postV z s u ω = z u ω 0 + 1 := by simp [postV, indicator_of_mem h']
  linarith [hF.nonneg u ω]

omit [MeasurableSpace Ω] hF in
theorem post_le_of_zero {s : ℝ≥0} {η : ℝ} (hη : 0 ≤ η) {ω : Ω} {u : ℝ≥0} (hsu : s ≤ u)
    (hz : z u ω 0 = 0) : hitLe (postV z s) η ω ≤ u := by
  refine iInf₂_le u ?_
  simp [postV, indicator_of_notMem (show u ∉ Iio s from not_lt.2 hsu), hz, hη]

theorem z_post_le {s : ℝ≥0} {η : ℝ} (hη : η < 1) {ω : Ω} {r : ℝ≥0}
    (hr : hitLe (postV z s) η ω = r) : z r ω 0 ≤ η := by
  have h := hitLe_attained (hF.postV_rc s ω) hr
  have hsr : s ≤ r := WithTop.coe_le_coe.1 (hr ▸ hF.le_post hη ω)
  simpa [postV, indicator_of_notMem (show r ∉ Iio s from not_lt.2 hsr)] using h

/-- **No return in `[s, T]` on `{η₁ ≤ z_s ≤ m}`.** -/
theorem measure_return_eq_zero [IsProbabilityMeasure Q] (s T : ℝ≥0) (j m : ℕ) :
    Q ({ω | 1 / ((j : ℝ) + 1) ≤ z s ω 0 ∧ z s ω 0 ≤ m} ∩
      {ω | ∃ u : ℝ≥0, s ≤ u ∧ u ≤ T ∧ z u ω 0 = 0}) = 0 := by
  rcases lt_or_ge T s with hTs | hsT
  · refine measure_mono_null (fun ω hω => ?_) measure_empty
    obtain ⟨u, h1, h2, -⟩ := hω.2
    exact absurd (h1.trans h2) (not_le.2 hTs)
  set η₁ : ℝ := 1 / ((j : ℝ) + 1) with hη₁
  have hj : (1 : ℝ) ≤ j + 1 := by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith
  have hη₁0 : 0 < η₁ := by positivity
  have hη₁1 : η₁ ≤ 1 := by rw [hη₁, div_le_one (by linarith)]; exact hj
  set A := {ω | η₁ ≤ z s ω 0 ∧ z s ω 0 ≤ m} with hAdef
  have hA : MeasurableSet[𝓖 s] A := by
    have hm : Measurable[𝓖 s] fun ω => z s ω 0 :=
      (continuous_apply 0).measurable.comp (hF.csm.adapted s).measurable
    exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  set C := cst K M B
  set B' : ℝ := -Real.log η₁ + m + 1 + C * T
  refine eq_zero_of_le_div (E := B') fun i => ?_
  set η : ℝ := η₁ * Real.exp (-((i : ℝ) + 1)) / 2 with hηdef
  have hexp : Real.exp (-((i : ℝ) + 1)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [i.cast_nonneg (α := ℝ)])
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 := by
    have : η₁ * Real.exp (-((i : ℝ) + 1)) ≤ 1 := by nlinarith [Real.exp_pos (-((i : ℝ) + 1))]
    rw [hηdef]; linarith
  set ρ := hitLe (postV z s) η
  have hρ : IsStoppingTime 𝓖 ρ := hF.isStoppingTime_post s η
  have H := Semimartingale.stoppedSemimartingale_holds 1 Ω Q 𝓖 _ _ _ (hF.isCSM_face hη0 T) ρ hρ
  set W := stoppedProcess (fun (t : ℝ≥0) ω (_ : Fin 1) => faceFun η C T ((t : ℝ), z t ω)) ρ
  have hWs : ∀ ω, W s ω 0 = faceFun η C T ((s : ℝ), z s ω) := fun ω => by
    simp only [W, stoppedProcess]; rw [min_eq_left (hF.le_post hη1 ω)]; rfl
  have hB : ∀ ω ∈ A, W s ω 0 ≤ B' := by
    intro ω hω
    rw [hWs]
    have hl : Real.log η₁ ≤ Real.log (z s ω 0 + η) := Real.log_le_log hη₁0 (by linarith [hω.1])
    have hCs : C * (T - s) ≤ C * T := mul_le_mul_of_nonneg_left (by linarith [s.coe_nonneg])
      hF.cst_nonneg
    simp only [faceFun]
    linarith [hω.2]
  have hR := lintegral_restart_le H hsT hA hB (fun _ _ => 0) (fun _ _ => le_rfl)
    (Eventually.of_forall fun ω _ u hu _ => by
      unfold switchAfter; split_ifs
      · exact (hF.itoDrift_le hη0 T (lt_of_le_of_lt (zero_le) hu) ω).trans
          (by linarith [hF.occ_nonneg hη0 u ω])
      · simp)
    (Eventually.of_forall fun ω _ u hu => by
      show 0 ≤ faceFun η C T (((min (u : WithTop ℝ≥0) (ρ ω)).untopA : ℝ),
        z (min (u : WithTop ℝ≥0) (ρ ω)).untopA ω)
      have hr := untopA_min_le u (ρ ω)
      have := faceFun_ge (δ := η) (C := C) (T := T)
        (p := (((min (u : WithTop ℝ≥0) (ρ ω)).untopA : ℝ),
          z (min (u : WithTop ℝ≥0) (ρ ω)).untopA ω)) (hF.pos_add hη0 _ ω)
      have h2 : 0 ≤ C * ((T : ℝ) - (min (u : WithTop ℝ≥0) (ρ ω)).untopA) :=
        mul_nonneg hF.cst_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 (hr.trans hu)))
      simp only at this
      linarith)
  -- the lower bound on `{ρ ≤ T}`
  have hlow : ∀ ω, ρ ω ≤ T → ENNReal.ofReal ((i : ℝ) + 1) ≤ ENNReal.ofReal (W T ω 0) := by
    intro ω hρT
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hρT)
    have hrT : r ≤ T := WithTop.coe_le_coe.1 (hr ▸ hρT)
    have hW : W T ω 0 = faceFun η C T ((r : ℝ), z r ω) := by
      simp only [W, stoppedProcess, ← hr]; rw [min_eq_right (WithTop.coe_le_coe.2 hrT)]; rfl
    have hzr := hF.z_post_le hη1 hr.symm
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hW]
    have h1 := neg_log_le_faceFun (δ := η) (C := C) (T := T) (p := ((r : ℝ), z r ω))
      (hF.pos_add hη0 r ω) (mul_nonneg hF.cst_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hrT)))
    have h2 : Real.log (z r ω 0 + η) ≤ Real.log (2 * η) :=
      Real.log_le_log (hF.pos_add hη0 r ω) (by linarith)
    have h3 : Real.log (2 * η) = Real.log η₁ - ((i : ℝ) + 1) := by
      rw [show 2 * η = η₁ * Real.exp (-((i : ℝ) + 1)) by rw [hηdef]; ring,
        Real.log_mul hη₁0.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    have h4 : Real.log η₁ ≤ 0 := Real.log_nonpos hη₁0.le hη₁1
    simp only at h1
    linarith
  have hρm : MeasurableSet {ω | ρ ω ≤ T} := 𝓖.le T _ (hρ T)
  have hmain : ENNReal.ofReal ((i : ℝ) + 1) * Q ({ω | ρ ω ≤ T} ∩ A) ≤ ENNReal.ofReal B' := by
    calc ENNReal.ofReal ((i : ℝ) + 1) * Q ({ω | ρ ω ≤ T} ∩ A)
        = ∫⁻ ω in A, {ω | ρ ω ≤ T}.indicator (fun _ => ENNReal.ofReal ((i : ℝ) + 1)) ω ∂Q := by
          rw [lintegral_indicator_const hρm, Measure.restrict_apply hρm]
      _ ≤ ∫⁻ ω in A, (ENNReal.ofReal (W T ω 0) +
          ∫⁻ u in Ioc (s : ℝ) T, ENNReal.ofReal ((fun _ _ => (0 : ℝ)) u.toNNReal ω)) ∂Q := by
          refine lintegral_mono fun ω => ?_
          by_cases h : ρ ω ≤ T
          · rw [indicator_of_mem (show ω ∈ {ω | ρ ω ≤ T} from h)]
            exact (hlow ω h).trans le_self_add
          · rw [indicator_of_notMem (show ω ∉ {ω | ρ ω ≤ T} from h)]; exact bot_le
      _ ≤ ∫⁻ ω in A, ENNReal.ofReal (W s ω 0) ∂Q := hR
      _ ≤ ∫⁻ _ in A, ENNReal.ofReal B' ∂Q :=
          setLIntegral_mono_ae' (𝓖.le s _ hA) (Eventually.of_forall fun ω hω =>
            ENNReal.ofReal_le_ofReal (hB ω hω))
      _ ≤ _ := by rw [setLIntegral_const]; exact mul_le_of_le_one_right' prob_le_one
  have hsub : A ∩ {ω | ∃ u : ℝ≥0, s ≤ u ∧ u ≤ T ∧ z u ω 0 = 0} ⊆ {ω | ρ ω ≤ T} ∩ A := by
    intro ω hω
    obtain ⟨u, hsu, huT, hz⟩ := hω.2
    exact ⟨(post_le_of_zero (z := z) hη0.le hsu hz).trans (WithTop.coe_le_coe.2 huT), hω.1⟩
  exact (measure_mono hsub).trans (le_ofReal_div (by positivity) hmain)

/-- **No return**: a.s., if `z_s > 0` then `z_t > 0` for all `t ≥ s`. -/
theorem ae_noReturn [IsProbabilityMeasure Q] (s : ℝ≥0) :
    ∀ᵐ ω ∂Q, 0 < z s ω 0 → ∀ t : ℝ≥0, s ≤ t → 0 < z t ω 0 := by
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null fun j : ℕ =>
    measure_iUnion_null fun m : ℕ => measure_iUnion_null fun T : ℕ =>
      hF.measure_return_eq_zero s T j m)
  have hω' : ¬ (0 < z s ω 0 → ∀ t : ℝ≥0, s ≤ t → 0 < z t ω 0) := hω
  push Not at hω'
  obtain ⟨hs, t, hst, ht⟩ := hω'
  have hzt : z t ω 0 = 0 := le_antisymm ht (hF.nonneg t ω)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hs
  obtain ⟨m, hm⟩ := exists_nat_ge (z s ω 0)
  obtain ⟨T, hT⟩ := exists_nat_ge (t : ℝ)
  refine mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨T, ⟨hj.le, by linarith⟩,
    ⟨t, hst, ?_, hzt⟩⟩⟩⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact hT

end IsEntranceFace

end BlockBand.Transmission.DualEntrance
