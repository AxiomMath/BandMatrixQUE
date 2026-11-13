module

public import BlockBand.Endpoints.Poisson.SingleCollarTonelli
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# `ScStageLogDetIntegrable` holds, for every configuration

The isolated statement `ScStageLogDetIntegrable` is proved here by real analyticity of the
stage determinant in the energy.

* `sca_analyticAt_boundaryZ`: `e ↦ z_b(e) = boundaryZ b e` is real-analytic on `(-2, 2)`
  (`√(4 - e²) = exp (log (4 - e²) / 2)` there, and `matchedA e ≠ 0` since `Im matchedA e < 0`).
* `sca_analyticAt_stageMatrix_apply`: every entry of the stage matrix with matched leads
  `z_b(e)` is real-analytic in `e` on `(-2, 2)` (it is affine in `e`, `Re z_b(e)`, `Im z_b(e)`).
* `sca_analyticOnNhd_det_stageMatrix`: hence so is its determinant (a polynomial in the entries).
* `scStageLogDetIntegrable_holds : ScStageLogDetIntegrable`, from Mathlib's
  `MeromorphicOn.intervalIntegrable_log_norm`. The statement holds for **every** configuration
  `v` (no Hermiticity, no almost-sure argument; the determinant may even vanish identically).
* `svSingleCollarLogError_of_pointwise'`: `ScStageLogErrorPointwise → SvSingleCollarLogError`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Matrix
open BlockBand.Internal.Contracts.Layers (boundaryZ matchedA)
open scoped Interval

/-!
## 1. The matched lead is real-analytic in the energy
-/

theorem sca_four_sub_sq_pos {e : ℝ} (he : e ∈ Ioo (-2 : ℝ) 2) : 0 < 4 - e ^ 2 := by
  nlinarith [he.1, he.2]

/-- `e ↦ ((g e : ℝ) : ℂ)` is analytic where `g` is. -/
theorem sca_analyticAt_ofReal {g : ℝ → ℝ} {e₀ : ℝ} (hg : AnalyticAt ℝ g e₀) :
    AnalyticAt ℝ (fun e => ((g e : ℝ) : ℂ)) e₀ :=
  (Complex.ofRealCLM.analyticAt _).comp hg

/-- `√(4 - e²)` is real-analytic on `(-2, 2)`. -/
theorem sca_analyticAt_sqrt {e₀ : ℝ} (he₀ : e₀ ∈ Ioo (-2 : ℝ) 2) :
    AnalyticAt ℝ (fun e : ℝ => Real.sqrt (4 - e ^ 2)) e₀ := by
  have hl : AnalyticAt ℝ (fun e : ℝ => Real.log (4 - e ^ 2)) e₀ :=
    AnalyticAt.log (by fun_prop) (sca_four_sub_sq_pos he₀)
  have hA : AnalyticAt ℝ (fun e : ℝ => Real.exp (Real.log (4 - e ^ 2) * (1 / 2))) e₀ :=
    (hl.mul analyticAt_const).rexp'
  refine hA.congr ?_
  filter_upwards [isOpen_Ioo.mem_nhds he₀] with e he
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (sca_four_sub_sq_pos he)]

theorem sca_matchedA_eq (e : ℝ) :
    matchedA e = ((-e / 2 : ℝ) : ℂ) + ((-Real.sqrt (4 - e ^ 2) / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [matchedA]

theorem sca_analyticAt_matchedA {e₀ : ℝ} (he₀ : e₀ ∈ Ioo (-2 : ℝ) 2) :
    AnalyticAt ℝ (fun e => matchedA e) e₀ := by
  simp_rw [sca_matchedA_eq]
  have h1 : AnalyticAt ℝ (fun e : ℝ => ((-e / 2 : ℝ) : ℂ)) e₀ :=
    sca_analyticAt_ofReal (by fun_prop)
  have h2 : AnalyticAt ℝ (fun e : ℝ => ((-Real.sqrt (4 - e ^ 2) / 2 : ℝ) : ℂ)) e₀ :=
    sca_analyticAt_ofReal (sca_analyticAt_sqrt he₀).neg.div_const
  exact h1.add (h2.mul analyticAt_const)

theorem sca_matchedA_ne_zero {e : ℝ} (he : e ∈ Ioo (-2 : ℝ) 2) : matchedA e ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hs : 0 < Real.sqrt (4 - e ^ 2) := Real.sqrt_pos.mpr (sca_four_sub_sq_pos he)
  simp [matchedA] at him
  linarith

/-- **`z_b(e)` is real-analytic on `(-2, 2)`.** -/
theorem sca_analyticAt_boundaryZ (b : ℝ) {e₀ : ℝ} (he₀ : e₀ ∈ Ioo (-2 : ℝ) 2) :
    AnalyticAt ℝ (fun e => boundaryZ b e) e₀ := by
  have hA := sca_analyticAt_matchedA he₀
  exact (hA.inv (sca_matchedA_ne_zero he₀)).add (analyticAt_const.mul hA)

theorem sca_analyticAt_boundaryZ_re (b : ℝ) {e₀ : ℝ} (he₀ : e₀ ∈ Ioo (-2 : ℝ) 2) :
    AnalyticAt ℝ (fun e => (((boundaryZ b e).re : ℝ) : ℂ)) e₀ :=
  sca_analyticAt_ofReal ((Complex.reCLM.analyticAt _).comp (sca_analyticAt_boundaryZ b he₀))

theorem sca_analyticAt_boundaryZ_im (b : ℝ) {e₀ : ℝ} (he₀ : e₀ ∈ Ioo (-2 : ℝ) 2) :
    AnalyticAt ℝ (fun e => (((boundaryZ b e).im : ℝ) : ℂ)) e₀ :=
  sca_analyticAt_ofReal ((Complex.imCLM.analyticAt _).comp (sca_analyticAt_boundaryZ b he₀))

/-!
## 2. The stage matrix and its determinant
-/

/-- The determinant of a matrix with analytic entries is analytic. -/
theorem sca_analyticAt_det {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℝ → Matrix ι ι ℂ}
    {e₀ : ℝ} (hM : ∀ i j, AnalyticAt ℝ (fun e => M e i j) e₀) :
    AnalyticAt ℝ (fun e => (M e).det) e₀ := by
  simp_rw [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul ?_
  exact Finset.analyticAt_fun_prod _ fun i _ => hM (σ i) i

/-- **Every entry of the stage matrix with matched leads `z_b(e)` is real-analytic on
`(-2, 2)`**: the energy enters only through `-e`, `Re z_b(e)` and `Im z_b(e)`. -/
theorem sca_analyticAt_stageMatrix_apply {m n W : ℕ} (L : Fin m → ℕ) (s : ZMod n) (π : Pairing)
    (S : Finset (Fin m)) (b : ℝ) (buf : ℕ) (κ : ℝ) (v : RingCoords n W) {e₀ : ℝ}
    (he₀ : e₀ ∈ Ioo (-2 : ℝ) 2) (x y : StageSite L s S W) :
    AnalyticAt ℝ (fun e => stageMatrix L s π S e (boundaryZ b e) buf κ v x y) e₀ := by
  have hre := sca_analyticAt_boundaryZ_re b he₀
  have him := sca_analyticAt_boundaryZ_im b he₀
  have hid : AnalyticAt ℝ (fun e : ℝ => ((e : ℝ) : ℂ)) e₀ := sca_analyticAt_ofReal analyticAt_id
  simp only [stageMatrix, submatrix_apply, stageFull, Matrix.add_apply, stageHerm, diagonal_apply,
    stageAbsorption]
  split_ifs <;> push_cast <;> fun_prop

/-- **The stage determinant is real-analytic on `(-2, 2)`**, for every configuration. -/
theorem sca_analyticOnNhd_det_stageMatrix {m n W : ℕ} [NeZero n] (L : Fin m → ℕ) (s : ZMod n)
    (π : Pairing) (S : Finset (Fin m)) (b : ℝ) (buf : ℕ) (κ : ℝ) (v : RingCoords n W) :
    AnalyticOnNhd ℝ (fun e => (stageMatrix L s π S e (boundaryZ b e) buf κ v).det)
      (Ioo (-2 : ℝ) 2) := fun _ he₀ =>
  sca_analyticAt_det fun x y => sca_analyticAt_stageMatrix_apply L s π S b buf κ v he₀ x y

/-- `log ‖det‖` of the stage matrix is integrable on every `[e₁, e₂] ⊂ (-2, 2)`, for every
configuration. -/
theorem sca_integrableOn_log_det {m n W : ℕ} [NeZero n] (L : Fin m → ℕ) (s : ZMod n)
    (π : Pairing) (S : Finset (Fin m)) (b : ℝ) (buf : ℕ) (κ : ℝ) (v : RingCoords n W)
    {e₁ e₂ : ℝ} (h₁ : -2 < e₁) (h₂ : e₂ < 2) :
    IntegrableOn
      (fun e => Real.log ‖(stageMatrix L s π S e (boundaryZ b e) buf κ v).det‖) (Icc e₁ e₂) := by
  rcases le_or_gt e₁ e₂ with h | h
  · have hsub : [[e₁, e₂]] ⊆ Ioo (-2 : ℝ) 2 := by
      rw [uIcc_of_le h]
      exact Icc_subset_Ioo h₁ h₂
    have hmero :=
      ((sca_analyticOnNhd_det_stageMatrix L s π S b buf κ v).mono hsub).meromorphicOn
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le h).mp hmero.intervalIntegrable_log_norm
  · rw [Icc_eq_empty (not_le.mpr h)]
    exact integrableOn_empty

/-!
## 3. The Prop and the corollary
-/

/-- **`ScStageLogDetIntegrable` holds**: in fact for every configuration. -/
theorem scStageLogDetIntegrable_holds : ScStageLogDetIntegrable := by
  intro n W _ b _ _ m L _ π S buf κ _ e₁ e₂ h₁ h₂
  exact ae_of_all _ fun v => sca_integrableOn_log_det L 0 π S b buf κ v h₁ h₂

/-- **`SvSingleCollarLogError` from the pointwise stage error alone.** -/
theorem svSingleCollarLogError_of_pointwise' (hP : ScStageLogErrorPointwise) :
    SvSingleCollarLogError :=
  svSingleCollarLogError_of_pointwise hP scStageLogDetIntegrable_holds

end BlockBand.Endpoints
