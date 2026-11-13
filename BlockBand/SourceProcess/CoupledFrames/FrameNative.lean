module

public import BlockBand.SourceProcess.CoupledFrames.ShiftMain
public import BlockBand.SourceProcess.CoupledFrames.NativeSum
public import BlockBand.SourceProcess.CoupledFrames.FrameAlg2
public import BlockBand.SourceProcess.RankFree.BirthProcess

/-!
# The born frame without its jumps is an Itô process

For an Itô process `Y` (frames `Matrix ι c'`), a constant `Lc`, stopping times `τ_k`,
columns `col k` and `𝓕_{τ_k}`-measurable vectors `a_k`, the process
`N_t = Y_t Lc + Σ_k birthMat (col k) ((Y_t − Y_{t∧τ_k}) a_k)` is an Itô process
(`isNativeItoProcess_frameN`): writing `a_k = Σ_y Σ_r reIm_r(a_k(y)) c_r e_y` (`sum_reIm`),
each term is a fixed real-linear image of `reIm_r(a_k(y)) (Y − Y^{τ_k})`, which is Itô by
`isNativeItoProcess_shift`; sums by `isNativeItoProcess_finsetSum`. `frameN_eq'`, `frameNc_eq'` (`FrameForm`):
the process and its coefficients in closed form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c' c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c'] [DecidableEq c'] [Fintype c]
  [DecidableEq c]

/-- `V ↦ V L` as a continuous real-linear map. -/
def mulRightCLM (L : Matrix c' c ℂ) : Matrix ι c' ℂ →L[ℝ] Matrix ι c ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun V => V * L
      map_add' := fun U V => Matrix.add_mul U V L
      map_smul' := fun r V => by simp only [RingHom.id_apply, Matrix.smul_mul] }

/-- `V ↦ birthMat j (V v)` as a continuous real-linear map. -/
def colCLM (j : c) (v : c' → ℂ) : Matrix ι c' ℂ →L[ℝ] Matrix ι c ℂ :=
  (birthCLM j).comp (LinearMap.toContinuousLinearMap
    { toFun := fun V : Matrix ι c' ℂ => V *ᵥ v
      map_add' := fun U V => Matrix.add_mulVec U V v
      map_smul' := fun r V => by simp only [RingHom.id_apply, Matrix.smul_mulVec] })

omit [DecidableEq ι] [DecidableEq c'] [Fintype c] in
theorem colCLM_apply (j : c) (v : c' → ℂ) (V : Matrix ι c' ℂ) :
    colCLM j v V = birthMat j (V *ᵥ v) := rfl

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {κ : Type*}
  [Fintype κ] {n : ℕ}

/-- The born frame without its jumps. -/
def frameN (Y : ℝ≥0 → DriverSample S κ → Matrix ι c' ℂ) (Lc : Matrix c' c ℂ)
    (τ : Fin n → DriverSample S κ → ℝ≥0) (col : Fin n → c)
    (a : Fin n → DriverSample S κ → c' → ℂ) (t : ℝ≥0) (x : DriverSample S κ) : Matrix ι c ℂ :=
  mulRightCLM Lc (Y t x) + ∑ i : Fin n × c' × Fin 2, colCLM (col i.1) (cr i.2.2 • Pi.single i.2.1 1)
    (shiftProc Y (fun x => ((τ i.1 x : ℝ≥0) : WithTop ℝ≥0)) (fun x => reIm i.2.2 (a i.1 x i.2.1)) t x)

/-- Its coefficients, for coefficients `f` of `Y`. -/
def frameNc (f : ℝ≥0 → DriverSample S κ → Matrix ι c' ℂ) (Lc : Matrix c' c ℂ)
    (τ : Fin n → DriverSample S κ → ℝ≥0) (col : Fin n → c)
    (a : Fin n → DriverSample S κ → c' → ℂ) (t : ℝ≥0) (x : DriverSample S κ) : Matrix ι c ℂ :=
  mulRightCLM Lc (f t x) + ∑ i : Fin n × c' × Fin 2, colCLM (col i.1) (cr i.2.2 • Pi.single i.2.1 1)
    (onAfter (fun x => ((τ i.1 x : ℝ≥0) : WithTop ℝ≥0)) (fun x => reIm i.2.2 (a i.1 x i.2.1)) f t x)

omit [DecidableEq ι] in
/-- **The born frame without jumps is Itô.** -/
theorem isNativeItoProcess_frameN {Y b : ℝ≥0 → DriverSample S κ → Matrix ι c' ℂ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Matrix ι c' ℂ} (hY : IsNativeItoProcess μ Y b σ)
    (Lc : Matrix c' c ℂ) {τ : Fin n → DriverSample S κ → ℝ≥0}
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := κ) μ) (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)))
    (col : Fin n → c) {a : Fin n → DriverSample S κ → c' → ℂ}
    (ha : ∀ k, StronglyMeasurable[(hτ k).measurableSpace] (a k)) :
    IsNativeItoProcess μ (frameN Y Lc τ col a) (frameNc b Lc τ col a)
      (fun e => frameNc (σ e) Lc τ col a) := by
  have hξ : ∀ i : Fin n × c' × Fin 2, StronglyMeasurable[(hτ i.1).measurableSpace]
      (fun x => reIm i.2.2 (a i.1 x i.2.1)) := by
    intro i
    have h1 : StronglyMeasurable[(hτ i.1).measurableSpace] (fun x => a i.1 x i.2.1) :=
      (continuous_apply i.2.1).comp_stronglyMeasurable (ha i.1)
    by_cases hr : i.2.2 = 0
    · simp only [reIm, hr, ↓reduceIte]
      exact Complex.continuous_re.comp_stronglyMeasurable h1
    · simp only [reIm, hr, ↓reduceIte]
      exact Complex.continuous_im.comp_stronglyMeasurable h1
  exact isNativeItoProcess_add (hY.map_clm (mulRightCLM Lc)) (isNativeItoProcess_finsetSum Finset.univ
    fun i _ => (isNativeItoProcess_shift hY (hτ i.1) (hξ i)).map_clm (colCLM (col i.1) (cr i.2.2 • Pi.single i.2.1 1)))

omit [DecidableEq ι] [Fintype c] in
theorem sum_colCLM (j : c) (V : Matrix ι c' ℂ) (a : c' → ℂ) :
    ∑ y : c', ∑ r : Fin 2, colCLM j (cr r • Pi.single y 1) (reIm r (a y) • V) =
      birthMat j (V *ᵥ a) := by
  calc _ = birthCLM j (∑ y, ∑ r : Fin 2, reIm r (a y) • (V *ᵥ (cr r • Pi.single y 1))) := by
        simp only [map_sum, map_smul, colCLM_apply, birthCLM_apply]
    _ = _ := by rw [sum_reIm, birthCLM_apply]

end BlockBand.SourceProcess.CoupledFrames
