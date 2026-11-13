module

public import BlockBand.Native.CEH.LocalLaw.GoodEvent
public import BlockBand.Native.CEH.Martingale.ExpTail

/-!
# CEH local law, assembly: tail events of the flow martingales

The sample paths of the flow resolvent satisfy the deterministic path hypotheses, and the
martingale parts of the observables `Re tr(K R)` have exponential tails.

* `pathR`: the sample path `t ↦ R_{t⁺}(ω)` on `ℝ` (`t⁺ = t.toNNReal`).
* `flowPath_pathR`: for `M` solving the MDE at `(s, F, z)` and `m = ⟨M⟩`, every sample
  path satisfies the deterministic hypotheses `FlowPath` with `η = |Im z|`, `c = |Im m|` (`R_0 = M`,
  `|Im z_t| = η + c (s - t)`, continuity from the continuity of `G` and of the matrix inverse).
* `tailEvent K a b`: the event `∃ t ≤ s, a ≤ |Re tr(K R_t) - Re tr(K R_0) - ∫_0^t drift|` with
  bracket integral `≤ b`; `measure_tailEvent_le`: probability `≤ 2 exp(-a²/(2b))` (from
  `isContinuousSemimartingale_reTr_flowResolvent` and `measure_abs_compensated_ge_le`).
* `martGood_of_not_mem`: off `tailEvent K a b ∪ tailEvent (-i K) a b`, the path satisfies
  `MartGood K M m (pathR ω) s a b`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.LocalLaw

open Matrix MeasureTheory ProbabilityTheory Set
open BlockBand.External.CEH BlockBand.Native.CEH.Phase1 BlockBand.Native.CEH.Flow
open BlockBand.Native.CEH.Zig BlockBand.Native.CEH.Martingale
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Dyson
open scoped NNReal ENNReal

variable {Ω : Type} {N : ℕ}

/-- The sample path `t ↦ R_{t⁺}(ω)` of the flow resolvent. -/
def pathR (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ)
    (s : ℝ≥0) (ω : Ω) : ℝ → Matrix (Fin N) (Fin N) ℂ :=
  fun t => flowResolvent F G z m s t.toNNReal ω

/-- The process `Re tr(K R_{t ∧ s})`, in variance time `t ≥ 0`, stopped at `s`. -/
def tailY (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ)
    (s : ℝ≥0) (K : Matrix (Fin N) (Fin N) ℂ) : ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun t ω _ => reTr K (flowResolvent F G z m s (min t s) ω)

/-- Its drift `1_{t ≤ s} Re tr(K (⟨R_t⟩ − m) R_t²)`, from the flow Itô formula. -/
def tailβ (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ)
    (s : ℝ≥0) (K : Matrix (Fin N) (Fin N) ℂ) : ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun t ω _ => if t ≤ s then
    reTr K ((normalizedTrace (flowResolvent F G z m s t ω) - m) •
      (flowResolvent F G z m s t ω * flowResolvent F G z m s t ω)) else 0

/-- Its bracket density `1_{t ≤ s} N⁻¹ Σ_x Re tr(K R_t E_x R_t)²`, from the flow Itô formula. -/
def tailα (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ)
    (s : ℝ≥0) (K : Matrix (Fin N) (Fin N) ℂ) : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ :=
  fun t ω => Matrix.of fun _ _ => if t ≤ s then
    1 / (N : ℝ) * ∑ x, reTr K (flowResolvent F G z m s t ω * hermBasis x *
      flowResolvent F G z m s t ω) ^ 2 else 0

/-- The exponential-tail event of `Re tr(K R)`. -/
def tailEvent (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ)
    (s : ℝ≥0) (K : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) : Set Ω :=
  {ω | ∃ t ≤ s, a ≤ |smCompensated (tailY F G z m s K) (tailβ F G z m s K) 0 t ω| ∧
    ∫ r in Ioc 0 (t : ℝ), tailα F G z m s K r.toNNReal ω 0 0 ≤ b}

section Measure

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Matrix (Fin N) (Fin N) ℂ}

/-- **Exponential tail.** `Q(tailEvent K a b) ≤ 2 exp(-a²/(2b))`. -/
theorem measure_tailEvent_le (hG : IsHermitianBrownian Q 𝓖 N G) (hF : F.IsHermitian) {z m : ℂ}
    (hz : z.im ≠ 0) (hm : 0 ≤ z.im * m.im) (s : ℝ≥0) (K : Matrix (Fin N) (Fin N) ℂ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Q (tailEvent F G z m s K a b) ≤ ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * b))) :=
  measure_abs_compensated_ge_le (isContinuousSemimartingale_reTr_flowResolvent hG hF hz hm s K)
    s ha hb

end Measure

/-!
## The sample paths
-/

section Path

variable [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}

theorem continuous_flowSpectral_toNNReal (z m : ℂ) (s : ℝ≥0) :
    Continuous fun t : ℝ => flowSpectral z m s t.toNNReal := by
  unfold flowSpectral
  exact continuous_const.add ((Complex.continuous_ofReal.comp
    (continuous_const.sub (NNReal.continuous_coe.comp continuous_real_toNNReal))).mul
    continuous_const)

/-- **Every sample path satisfies `FlowPath`.** -/
theorem flowPath_pathR (hG : IsHermitianBrownian Q 𝓖 N G) (hN : 0 < N)
    {F : SourceHermitian N} {s : ℝ≥0} {z : ℂ} {Mz : Matrix (Fin N) (Fin N) ℂ}
    (hMDE : BlockBand.Internal.Contracts.Inputs.IsManuscriptMDE (s : ℝ) F z Mz) (hz : z.im ≠ 0)
    (ω : Ω) :
    FlowPath (pathR F.1 G z (normalizedTrace Mz) s ω) (fun t => F.1 + G t.toNNReal ω)
      (fun t => flowSpectral z (normalizedTrace Mz) s t.toNNReal) Mz (normalizedTrace Mz)
      |z.im| |(normalizedTrace Mz).im| s where
  herm t := F.2.add (hG.hermitian _ ω)
  res t := rfl
  height t ht := by
    rw [flowSpectral_im, Real.coe_toNNReal _ ht.1, zigHeight,
      abs_add_mul_of_mul_nonneg (l := (s : ℝ) - t) (mde_im_mul_im_nonneg hMDE)
        (by linarith [ht.2])]
    ring
  init := by
    have h := mde_eq_resolvent hMDE
    simp only [pathR, flowResolvent, Real.toNNReal_zero, hG.zero, add_zero, flowSpectral,
      NNReal.coe_zero, sub_zero]
    exact h.symm
  cont := by
    set m := normalizedTrace Mz
    have hA : Continuous fun t : ℝ => F.1 + G t.toNNReal ω -
        flowSpectral z m s t.toNNReal • (1 : Matrix (Fin N) (Fin N) ℂ) :=
      (continuous_const.add ((hG.continuous ω).comp continuous_real_toNNReal)).sub
        ((continuous_flowSpectral_toNNReal z m s).smul continuous_const)
    intro t ht
    have hσ : ((t.toNNReal : ℝ≥0) : ℝ) ≤ (s : ℝ) := by
      rw [Real.coe_toNNReal _ ht.1]; exact ht.2
    have hdet := (isUnit_det_sub_smul (F.2.add (hG.hermitian t.toNNReal ω))
      (flowSpectral_im_ne_zero hz (mde_im_mul_im_nonneg hMDE) hσ)).ne_zero
    have hinv := continuousAt_matrix_inv (F.1 + G t.toNNReal ω -
        flowSpectral z m s t.toNNReal • (1 : Matrix (Fin N) (Fin N) ℂ))
      (NormedRing.inverse_continuousAt (Units.mk0 _ hdet))
    exact (ContinuousAt.comp (g := fun X : Matrix (Fin N) (Fin N) ℂ => X⁻¹)
      (f := fun t : ℝ => F.1 + G t.toNNReal ω -
        flowSpectral z m s t.toNNReal • (1 : Matrix (Fin N) (Fin N) ℂ)) (x := t) hinv
      hA.continuousAt).continuousWithinAt
  trace_init := rfl
  c_eq := rfl
  η_pos := abs_pos.2 hz
  c_pos := abs_pos.2 fun h0 => by
    have := mde_im_mul_im_pos hN hMDE
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this
  s_nonneg := s.2

end Path

/-!
## The link between the semimartingale and the path observables
-/

theorem obsM_negI (K Mz : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (t : ℝ) : obsM ((-Complex.I) • K) Mz m R t = -Complex.I * obsM K Mz m R t := by
  have hD : obsD ((-Complex.I) • K) m R = fun r => -Complex.I * obsD K m R r := by
    funext r
    simp only [obsD, Matrix.smul_mul, trace_smul, smul_eq_mul]
    ring
  rw [obsM, obsM, hD, intervalIntegral.integral_const_mul, obsX, obsX, Matrix.smul_mul,
    trace_smul, smul_eq_mul]
  ring

section Link

variable {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Matrix (Fin N) (Fin N) ℂ} {z m : ℂ}
  {s : ℝ≥0} {K Mz : Matrix (Fin N) (Fin N) ℂ} {ω : Ω}

theorem toNNReal_le_of_mem {t : ℝ} (ht : t ∈ Icc 0 (s : ℝ)) : t.toNNReal ≤ s := by
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht.1]; exact ht.2

theorem smCompensated_tailY (hR0 : pathR F G z m s ω 0 = Mz)
    (hint : IntervalIntegrable (obsD K m (pathR F G z m s ω)) volume 0 s) {t : ℝ}
    (ht : t ∈ Icc 0 (s : ℝ)) :
    smCompensated (tailY F G z m s K) (tailβ F G z m s K) 0 t.toNNReal ω =
      (obsM K Mz m (pathR F G z m s ω) t).re := by
  have hts := toNNReal_le_of_mem ht
  have e0 : flowResolvent F G z m s 0 ω = Mz := by
    rw [← hR0]; simp [pathR]
  have hint' : IntervalIntegrable (obsD K m (pathR F G z m s ω)) volume 0 t :=
    hint.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
      exact Icc_subset_Icc_right ht.2)
  have eβ : ∫ r in Ioc 0 ((t.toNNReal : ℝ≥0) : ℝ), tailβ F G z m s K r.toNNReal ω 0 =
      ∫ r in (0 : ℝ)..t, (obsD K m (pathR F G z m s ω) r).re := by
    rw [Real.coe_toNNReal _ ht.1, intervalIntegral.integral_of_le ht.1]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hr' : r.toNNReal ≤ s := toNNReal_le_of_mem ⟨hr.1.le, hr.2.trans ht.2⟩
    simp only [tailβ, hr', ↓reduceIte, obsD, pathR, reTr, Matrix.mul_smul, trace_smul, smul_eq_mul]
  have hre : (∫ r in (0 : ℝ)..t, obsD K m (pathR F G z m s ω) r).re =
      ∫ r in (0 : ℝ)..t, (obsD K m (pathR F G z m s ω) r).re := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint']
    rfl
  unfold smCompensated
  rw [eβ]
  simp only [tailY, min_eq_left hts, min_eq_left (zero_le : (0 : ℝ≥0) ≤ s)]
  rw [e0, obsM, Complex.sub_re, hre, obsX, Matrix.mul_sub, trace_sub, Complex.sub_re]
  rfl

theorem bracket_tailα {t : ℝ} (ht : t ∈ Icc 0 (s : ℝ)) :
    ∫ r in Ioc 0 ((t.toNNReal : ℝ≥0) : ℝ), tailα F G z m s K r.toNNReal ω 0 0 =
      ∫ r in Ioc 0 t, brk K (pathR F G z m s ω) r := by
  rw [Real.coe_toNNReal _ ht.1]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hr' : r.toNNReal ≤ s := toNNReal_le_of_mem ⟨hr.1.le, hr.2.trans ht.2⟩
  simp only [tailα, Matrix.of_apply, hr', ↓reduceIte, brk, pathR]

/-- **Off the two tail events, the path is `MartGood`.** -/
theorem martGood_of_not_mem (hR0 : pathR F G z m s ω 0 = Mz)
    (hint : ∀ K' : Matrix (Fin N) (Fin N) ℂ,
      IntervalIntegrable (obsD K' m (pathR F G z m s ω)) volume 0 s) {a b : ℝ}
    (h1 : ω ∉ tailEvent F G z m s K a b) (h2 : ω ∉ tailEvent F G z m s ((-Complex.I) • K) a b) :
    MartGood K Mz m (pathR F G z m s ω) s a b := by
  intro t ht
  have hts := toNNReal_le_of_mem ht
  constructor
  · intro hA
    by_contra hlt
    push Not at hlt
    refine h1 ⟨t.toNNReal, hts, ?_, ?_⟩
    · rw [smCompensated_tailY hR0 (hint K) ht]; exact hlt
    · rw [bracket_tailα ht]; exact hA
  · intro hA
    by_contra hlt
    push Not at hlt
    refine h2 ⟨t.toNNReal, hts, ?_, ?_⟩
    · rw [smCompensated_tailY hR0 (hint _) ht, obsM_negI]
      simpa [Complex.mul_re] using hlt
    · rw [bracket_tailα ht]; exact hA

end Link

end BlockBand.Native.CEH.LocalLaw
