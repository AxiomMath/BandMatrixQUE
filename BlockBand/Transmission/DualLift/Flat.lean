module

public import BlockBand.Transmission.DualLift.SDE
public import BlockBand.Transmission.DualLift.CSMCongr

/-!
# The flat paths of the lift and their semimartingale characteristics

Setting: `(LΩ S, L𝓖 μ, LP μ)`, a start `ξ` with `IsLiftStart μ ξ`, `D₀ > 0`, a
`LiftFamily μ D₀ ξ`.

* Deterministic: the open flat domain `flatU = {x + y > 0, x > −1}` (it contains the closed
  strip minus the corner `(0, 0)`) and its compacts `flatK R`; `π` maps the part of `liftM` in
  the ball of radius `R ≥ 1` into `flatK R` (`liftProj_mem_flatK`); on `liftM` the lifted
  characteristics of `π` are the flat dual ones (`vecGen_liftProj_eq`, `liftCov_eq`).
* `good`: a measurable set of full measure on which every `X n` stays in `liftM` and the radii
  are consistent; it lies in every `L𝓖 μ t` (augmentation).
* `Yf n`: the flat path `π(X n)` on `good`, the constant start `π(ξ)` off `good`. It is
  continuous and adapted at every `ω`, starts at `π(ξ)`, and stays in
  `flatK (max (max n ‖ξ‖) 1) ⊆ flatU` (`Yf_mem_flatK`).
* **`isCSM_Yf`**: `Yf n` is a continuous semimartingale with the flat `p = 1` dual
  characteristics `flatDrift D₀ 1`, `flatDiff D₀ 1` switched off after `e n` (from `isCSM_proj`
  and the invariance of `liftM`, through `IsContinuousSemimartingale.congr_ae`). With Itô's
  formula on `U = flatU` this is the input of the Lyapunov, optional-stopping and
  martingale-problem steps at boundary starts (`x = 0`, `y = 0`, `y = 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal

/-!
## Deterministic part
-/

/-- The open flat domain `{x + y > 0, x > −1}`. -/
def flatU : Set (Fin 2 → ℝ) := {z | 0 < z 0 + z 1 ∧ -1 < z 0}

theorem c0 : Continuous fun z : Fin 2 → ℝ => z 0 := continuous_apply 0
theorem c1 : Continuous fun z : Fin 2 → ℝ => z 1 := continuous_apply 1

theorem isOpen_flatU : IsOpen flatU :=
  (isOpen_lt continuous_const (c0.add c1)).inter (isOpen_lt continuous_const c0)

/-- The compact pieces `{x + y ≥ 1/R, 0 ≤ x ≤ 2R², 0 ≤ y ≤ 1}`. -/
def flatK (R : ℝ) : Set (Fin 2 → ℝ) :=
  {z | 1 / R ≤ z 0 + z 1 ∧ 0 ≤ z 0 ∧ z 0 ≤ 2 * R * R ∧ 0 ≤ z 1 ∧ z 1 ≤ 1}

theorem isCompact_flatK (R : ℝ) : IsCompact (flatK R) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const (c0.add c1)).inter ((isClosed_le continuous_const
      c0).inter ((isClosed_le c0 continuous_const).inter ((isClosed_le
      continuous_const c1).inter (isClosed_le c1 continuous_const))))
  · refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 2 * R * R + 1)).subset ?_
    intro z hz
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by nlinarith [mul_self_nonneg R])]
    intro i
    fin_cases i
    · simp only [Real.norm_eq_abs, Fin.zero_eta]
      rw [abs_of_nonneg hz.2.1]; linarith [hz.2.2.1]
    · simp only [Real.norm_eq_abs, Fin.mk_one]
      rw [abs_of_nonneg hz.2.2.2.1]; nlinarith [hz.2.2.2.2, mul_self_nonneg R]

theorem flatK_subset {R : ℝ} (hR : 0 < R) : flatK R ⊆ flatU := fun z hz =>
  ⟨lt_of_lt_of_le (by positivity) hz.1, by linarith [hz.2.1]⟩

theorem liftProj_mem_flatK {ξ : Fin 6 → ℝ} (h : ξ ∈ liftM) {R : ℝ} (hR : 1 ≤ R)
    (hn : ‖ξ‖ ≤ R) : liftProj ξ ∈ flatK R := by
  have hS := lS_pos h
  have hs := h.2
  have hy := ly_mem_of_mem h
  have hb : ∀ i, |ξ i| ≤ R := fun i => (Real.norm_eq_abs _ ▸ norm_le_pi_norm ξ i).trans hn
  have h5 : ξ 5 ≤ R := (le_abs_self _).trans (hb 5)
  have h5p : 0 < ξ 5 := by
    by_contra hc; have hc' := not_lt.1 hc; nlinarith
  have h0 := abs_le.1 (hb 0)
  have h1 := abs_le.1 (hb 1)
  refine ⟨?_, lx_nonneg ξ, ?_, hy.1, hy.2⟩
  · simp only [liftProj_zero, liftProj_one]
    rw [div_le_iff₀ (by linarith)]
    unfold lS at hs
    nlinarith
  · simp only [liftProj_zero]; unfold lx; nlinarith

/-- `flatDrift D₀ 1` in closed form. -/
theorem flatDrift_one_eq (D0 : ℝ) : flatDrift D0 1 = fun z : Fin 2 → ℝ =>
    ![D0 / 2 * (1 + 2 * z 0 - 2 * z 0 * (1 + z 0) / (z 0 + z 1)),
      D0 / 2 * (1 - 2 * z 1 - 2 * z 1 * (1 - z 1) / (z 0 + z 1))] := by
  funext z i
  fin_cases i
  · exact flatDrift_one_zero D0 z
  · exact flatDrift_one_one D0 z

theorem flatDiff_one_eq (D0 : ℝ) : flatDiff D0 1 = fun z : Fin 2 → ℝ =>
    Matrix.diagonal ![D0 * (z 0 * (1 + z 0)), D0 * (z 1 * (1 - z 1))] := by
  funext z
  unfold flatDiff
  congr 1
  funext i
  fin_cases i
  · exact flatDiffDiag_one_zero D0 z
  · exact flatDiffDiag_one_one D0 z

theorem measurable_flatDrift_one (D0 : ℝ) : Measurable (flatDrift D0 1) := by
  rw [flatDrift_one_eq]
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> fun_prop

theorem continuous_flatDiff_one (D0 : ℝ) : Continuous (flatDiff D0 1) := by
  rw [flatDiff_one_eq]
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  fin_cases i
  · exact continuous_const.mul (c0.mul (continuous_const.add c0))
  · exact continuous_const.mul (c1.mul (continuous_const.sub c1))

variable {D0 : ℝ}

theorem vecGen_liftProj_eq (hD0 : 0 ≤ D0) {ξ : Fin 6 → ℝ} (h : ξ ∈ liftM) :
    SourceSDE.vecGen (liftDrift D0) (liftSigma D0) liftProj ξ = flatDrift D0 1 (liftProj ξ) := by
  rw [vecGen_liftProj hD0, flatDrift_one_eq, s_eq_inv h]
  have hS := lS_pos h
  unfold lS at hS ⊢
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, liftProj_zero, liftProj_one]
    field_simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, liftProj_zero,
      liftProj_one]
    field_simp

theorem liftCov_eq (hD0 : 0 ≤ D0) {ξ : Fin 6 → ℝ} (h : ξ ∈ liftM) :
    LiftFamily.liftCov D0 ξ = flatDiff D0 1 (liftProj ξ) := by
  rw [flatDiff_one_eq]
  ext i j
  simp only [LiftFamily.liftCov, Matrix.of_apply, fderiv_liftProj hD0, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, liftProj_zero, liftProj_one, Fin.isValue, ite_true,
    show ((0 : Fin 2) = 1) ↔ False by decide, show ((1 : Fin 2) = 0) ↔ False by decide, ite_false]
  · exact gx_cov hD0 ξ
  · exact gxy_cov ξ
  · exact gyx_cov ξ
  · exact gy_cov hD0 h

/-!
## The flat paths
-/

variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ)

/-- The pathwise good event: invariance and radius consistency. -/
def IsGood (ω : LΩ S) : Prop := (∀ n : ℕ, ∀ t, F.X n t ω ∈ liftM) ∧
  ∀ n m : ℕ, n ≤ m → F.e n ω ≤ F.e m ω ∧ ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ F.e n ω →
    F.X n t ω = F.X m t ω

/-- The good set. -/
def good : Set (LΩ S) := (toMeasurable (LP μ) {ω | ¬F.IsGood ω})ᶜ

theorem measurableSet_good : MeasurableSet F.good := (measurableSet_toMeasurable _ _).compl

theorem measure_good_compl (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) : LP μ F.goodᶜ = 0 := by
  rw [good, compl_compl, measure_toMeasurable]
  exact ae_iff.1 ((F.ae_mem_liftM hD0 hξ).and (F.ae_consistent hD0))

theorem good_spec {ω : LΩ S} (hω : ω ∈ F.good) : F.IsGood ω := by
  by_contra h; exact hω (subset_toMeasurable _ _ h)

theorem measurableSet_good_aug (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (t : ℝ≥0) :
    MeasurableSet[L𝓖 μ t] F.good :=
  measurableSet_aug_of_full μ F.measurableSet_good (F.measure_good_compl hD0 hξ) t

open scoped Classical in
/-- The flat path: `π(X n)` on `good`, the constant start off `good`. -/
def Yf (n : ℕ) (t : ℝ≥0) (ω : LΩ S) : Fin 2 → ℝ :=
  if ω ∈ F.good then F.Zp n t ω else liftProj (ξ ω)

theorem Yf_of_good {ω : LΩ S} (hω : ω ∈ F.good) (n : ℕ) (t : ℝ≥0) :
    F.Yf n t ω = F.Zp n t ω := by simp [Yf, hω]

theorem Yf_zero (n : ℕ) (ω : LΩ S) : F.Yf n 0 ω = liftProj (ξ ω) := by
  unfold Yf Zp; split_ifs <;> simp [F.X_zero]

theorem continuous_Yf (n : ℕ) (ω : LΩ S) : Continuous fun t => F.Yf n t ω := by
  unfold Yf; split_ifs
  · exact F.continuous_Zp n ω
  · exact continuous_const

theorem measurable_Zp (n : ℕ) (t : ℝ≥0) : Measurable[L𝓖 μ t] (F.Zp n t) :=
  contDiff_liftProj.continuous.measurable.comp ((F.strong n).sol.1.adapted t).measurable

theorem measurable_Yf (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) (t : ℝ≥0) :
    Measurable[L𝓖 μ t] (F.Yf n t) := by
  have h0 : Measurable[L𝓖 μ t] fun ω => liftProj (ξ ω) :=
    contDiff_liftProj.continuous.measurable.comp ((hξ.meas.mono ((L𝓖 μ).mono
      (zero_le : (0 : ℝ≥0) ≤ t))).measurable)
  exact Measurable.ite (F.measurableSet_good_aug hD0 hξ t) (F.measurable_Zp n t) h0

/-- The flat path stays in a compact subset of `flatU`. -/
theorem Yf_mem_flatK (hξ : IsLiftStart μ ξ) (n : ℕ) (t : ℝ≥0) (ω : LΩ S) :
    F.Yf n t ω ∈ flatK (max (max (n : ℝ) ‖ξ ω‖) 1) := by
  have hR : (1 : ℝ) ≤ max (max (n : ℝ) ‖ξ ω‖) 1 := le_max_right _ _
  unfold Yf; split_ifs with hω
  · exact liftProj_mem_flatK ((F.good_spec hω).1 n t) hR
      ((F.norm_X_le n t ω).trans (le_max_left _ _))
  · exact liftProj_mem_flatK (hξ.mem ω) hR ((le_max_right _ _).trans (le_max_left _ _))

theorem Yf_mem_flatU (hξ : IsLiftStart μ ξ) (n : ℕ) (t : ℝ≥0) (ω : LΩ S) :
    F.Yf n t ω ∈ flatU :=
  flatK_subset (lt_of_lt_of_le one_pos (le_max_right _ _)) (F.Yf_mem_flatK hξ n t ω)

/-- **The flat paths are continuous semimartingales with the flat dual characteristics.** -/
theorem isCSM_Yf (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) :
    IsContinuousSemimartingale (LP μ) (L𝓖 μ) (F.Yf n)
      (fun t ω => switchOff (F.e n) (fun t ω => flatDrift D0 1 (F.Yf n t ω)) t ω)
      (fun t ω => switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω) := by
  have hYa : ∀ t, StronglyMeasurable[L𝓖 μ t] (F.Yf n t) := fun t =>
    (F.measurable_Yf hD0 hξ n t).stronglyMeasurable
  have hYp : IsStronglyProgressive (L𝓖 μ) (F.Yf n) :=
    StronglyAdapted.isStronglyProgressive_of_continuous hYa (F.continuous_Yf n)
  have hv : Continuous fun z : Fin 2 → ℝ => (![D0 * (z 0 * (1 + z 0)), D0 * (z 1 * (1 - z 1))] :
      Fin 2 → ℝ) := continuous_pi fun i => by
    fin_cases i
    · exact continuous_const.mul (c0.mul (continuous_const.add c0))
    · exact continuous_const.mul (c1.mul (continuous_const.sub c1))
  have h1 : IsStronglyProgressive (L𝓖 μ) (switchOff (F.e n) fun t ω =>
      (![D0 * (F.Yf n t ω 0 * (1 + F.Yf n t ω 0)), D0 * (F.Yf n t ω 1 * (1 - F.Yf n t ω 1))] :
        Fin 2 → ℝ)) :=
    isStronglyProgressive_switchOff (F.isStoppingTime_e n) fun i => hv.comp_stronglyMeasurable (hYp i)
  have hα : IsStronglyProgressive (L𝓖 μ)
      (fun t ω => switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω) := by
    have e : (fun t ω => switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω) =
        fun t ω => Matrix.diagonal (switchOff (F.e n) (fun t ω =>
          (![D0 * (F.Yf n t ω 0 * (1 + F.Yf n t ω 0)), D0 * (F.Yf n t ω 1 * (1 - F.Yf n t ω 1))] :
            Fin 2 → ℝ)) t ω) := by
      funext t ω; unfold switchOff; split_ifs
      · rw [flatDiff_one_eq]
      · simp
    rw [e]
    intro i
    exact (continuous_id.matrix_diagonal).comp_stronglyMeasurable (h1 i)
  refine (F.isCSM_proj n).congr_ae hYa hYp
    (isStronglyProgressive_switchOff (F.isStoppingTime_e n) fun i =>
      ((measurable_flatDrift_one D0).comp (hYp i).measurable).stronglyMeasurable)
    hα ?_
  have hG : ∀ᵐ ω ∂LP μ, ω ∈ F.good := by
    rw [ae_iff]; exact F.measure_good_compl hD0 hξ
  filter_upwards [hG] with ω hω t
  have hM := (F.good_spec hω).1 n t
  refine ⟨F.Yf_of_good hω n t, ?_, ?_⟩
  · unfold switchOff; split_ifs
    · beta_reduce; rw [F.Yf_of_good hω, Zp, vecGen_liftProj_eq hD0.le hM]
    · rfl
  · unfold switchOff; split_ifs
    · beta_reduce; rw [F.Yf_of_good hω, Zp, liftCov_eq hD0.le hM]
    · rfl

end LiftFamily

end BlockBand.Transmission.DualLift
