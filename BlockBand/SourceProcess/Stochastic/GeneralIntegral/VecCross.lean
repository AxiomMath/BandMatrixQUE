module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.VecMeasure
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Cross isometry for general integrands

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, finite `ι`,
`h : IsL2IntegratorVec Q 𝓖 N a` with **symmetric** `a` (`hs`; WLOG by `symmetrize`), horizon
`T`, `ν̄ = barMeasure Q a T = (tr a) ds ⊗ Q`, integrands `H, K ∈ PredL2 𝓖 ν̄` with canonical
representatives `H̃, K̃`.

* `simpleLin 𝓖 T μ`: simple integrands to `PredL2 𝓖 μ` (any finite `μ`); `simpleLin_ae`
  (representative `elemFun x`), `denseRange_simpleLin` (`μ` concentrated on `(0,T] × Ω`).
* `restr h T i = predRestrict` from `PredL2(ν̄)` to `PredL2(ν^{ii})` (`ν^{ii} ≤ ν̄`) and
  `coordInt h T i H = ∫_0^T H dN^i := stochIntegral (restr H)`, a CLM to `L²(Q)`;
  `coordInt_simple_ae`: for simple `x`, `coordInt i x = elemProc (N i) x T` a.s.
* `crossInt h i j H K = ∫ ρ^{ij} H̃ K̃ dν̄` (`ρ^{ij} = a^{ij}/tr a`).
* **`inner_coordInt`** (cross isometry): `E[∫_0^T H dN^i · ∫_0^T K dN^j] = crossInt i j H K`,
  by bilinear density from `integral_elemProc_mul`.
* **`integral_coordInt_mul`**: the same as `∫ H̃ K̃ a^{ij} d(dt ⊗ Q)` (integrable), and
  `integral_coordInt_mul_fubini`: `= E ∫_{(0,T]} H̃ K̃ a^{ij} ds`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}

section Simple

variable (𝓖) (T : ℝ≥0) (μ : Measure (ℝ × Ω)) [IsFiniteMeasure μ]

/-- Simple integrands to their class in `PredL2 𝓖 μ`. -/
def simpleLin : (Rect 𝓖 T →₀ ℝ) →ₗ[ℝ] PredL2 𝓖 μ :=
  Finsupp.linearCombination ℝ (rectL2 𝓖 T μ)

variable {𝓖 T μ}

theorem simpleLin_ae (x : Rect 𝓖 T →₀ ℝ) :
    ((simpleLin 𝓖 T μ x : PredL2 𝓖 μ) : ℝ × Ω → ℝ) =ᵐ[μ] elemFun x := by
  induction x using Finsupp.induction_linear with
  | zero => simpa using Lp.coeFn_zero ℝ 2 μ
  | add x y hx hy =>
      simp only [map_add]
      exact (Lp.coeFn_add _ _).trans (hx.add hy)
  | single r c =>
      simp only [simpleLin, Finsupp.linearCombination_single, elemFun_single]
      refine (Lp.coeFn_smul _ _).trans (EventuallyEq.const_smul ?_ c)
      exact indicatorConstLp_coeFn (hs := r.measurableSet) (hμs := measure_ne_top _ _)

theorem denseRange_simpleLin (hμ : ∀ᵐ x ∂μ, x.1 ∈ Ioc (0 : ℝ) T) :
    DenseRange (simpleLin 𝓖 T μ) := by
  change Dense (range (simpleLin 𝓖 T μ))
  rw [← LinearMap.coe_range, simpleLin, Finsupp.range_linearCombination]
  exact rectSpan_dense 𝓖 T hμ

end Simple

omit mΩ in
theorem real_inner_Lp_eq {X : Type*} [MeasurableSpace X] {μ : Measure X} (f g : Lp ℝ 2 μ) :
    ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

variable [IsFiniteMeasure Q] {ι : Type*} [Fintype ι] {N : ι → ℝ≥0 → Ω → ℝ}
  {a : ι → ι → ℝ≥0 → Ω → ℝ}

/-- The cross form `∫ ρ^{ij} H̃ K̃ dν̄`. -/
def crossInt (Q : Measure Ω) (a : ι → ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (i j : ι)
    (H K : PredL2 𝓖 (barMeasure Q a T)) : ℝ :=
  ∫ p, crossRatio a i j p.1.toNNReal p.2 *
    (((H : Lp ℝ 2 (barMeasure Q a T)) p) * ((K : Lp ℝ 2 (barMeasure Q a T)) p)) ∂barMeasure Q a T

namespace IsL2IntegratorVec

variable (h : IsL2IntegratorVec Q 𝓖 N a) (T : ℝ≥0)

/-- Restriction `PredL2(ν̄) → PredL2(ν^{ii})`. -/
def restr (i : ι) : PredL2 𝓖 (barMeasure Q a T) →L[ℝ] PredL2 𝓖 (bracketMeasure Q (a i i) T) :=
  predRestrict 𝓖 (h.coord_le_bar T i)

/-- The coordinate integral `H ↦ ∫_0^T H dN^i` on `PredL2(ν̄)`. -/
def coordInt (i : ι) : PredL2 𝓖 (barMeasure Q a T) →L[ℝ] Lp ℝ 2 Q :=
  ((h.coord i).stochIntegral T).toContinuousLinearMap.comp (h.restr T i)

omit [IsFiniteMeasure Q] in
theorem restr_coeFn (i : ι) (H : PredL2 𝓖 (barMeasure Q a T)) :
    (((h.restr T i H : PredL2 𝓖 (bracketMeasure Q (a i i) T)) :
      Lp ℝ 2 (bracketMeasure Q (a i i) T)) : ℝ × Ω → ℝ) =ᵐ[bracketMeasure Q (a i i) T]
      ((H : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ) :=
  predRestrict_coeFn 𝓖 _ H

theorem restr_simpleLin (i : ι) (x : Rect 𝓖 T →₀ ℝ) :
    haveI := h.isFiniteMeasure_bar T
    h.restr T i (simpleLin 𝓖 T (barMeasure Q a T) x) = (h.coord i).integrandLin T x := by
  have := h.isFiniteMeasure_bar T
  refine predL2_ext 𝓖 ?_
  filter_upwards [h.restr_coeFn T i _, (Measure.absolutelyContinuous_of_le
    (h.coord_le_bar T i)).ae_le (simpleLin_ae x), integrandLin_ae (h.coord i) x] with p h1 h2 h3
  rw [h1, h2, h3]

theorem coordInt_simple_ae (i : ι) (x : Rect 𝓖 T →₀ ℝ) :
    haveI := h.isFiniteMeasure_bar T
    (h.coordInt T i (simpleLin 𝓖 T (barMeasure Q a T) x) : Ω → ℝ) =ᵐ[Q] elemProc (N i) x T := by
  have := h.isFiniteMeasure_bar T
  simp only [coordInt, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, h.restr_simpleLin T i x]
  exact (h.coord i).stochIntegral_integrandLin_ae T x

variable (hs : ∀ i j t ω, a i j t ω = a j i t ω)

omit [IsFiniteMeasure Q] in
include h hs in
theorem memLp_rhoMul (i j : ι) (F : Lp ℝ 2 (barMeasure Q a T)) :
    MemLp (fun p => crossRatio a i j p.1.toNNReal p.2 * F p) 2 (barMeasure Q a T) :=
  MemLp.of_le (Lp.memLp F) ((h.measurable_crossRatio i j).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable F)) (Eventually.of_forall fun p => by
      show ‖crossRatio a i j p.1.toNNReal p.2 * F p‖ ≤ ‖F p‖
      rw [norm_mul, Real.norm_eq_abs (crossRatio _ _ _ _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (h.abs_crossRatio_le hs i j _ _))

/-- Multiplication by `ρ^{ij}` on `L²(ν̄)` (`|ρ^{ij}| ≤ 1`). -/
def rhoMul (i j : ι) (F : PredL2 𝓖 (barMeasure Q a T)) : Lp ℝ 2 (barMeasure Q a T) :=
  (h.memLp_rhoMul T hs i j (F : Lp ℝ 2 (barMeasure Q a T))).toLp _

omit [IsFiniteMeasure Q] in
theorem inner_rhoMul_left (i j : ι) (H K : PredL2 𝓖 (barMeasure Q a T)) :
    ⟪(H : Lp ℝ 2 (barMeasure Q a T)), h.rhoMul T hs i j K⟫_ℝ = crossInt Q a T i j H K := by
  rw [real_inner_Lp_eq, crossInt]
  refine integral_congr_ae ?_
  filter_upwards [(h.memLp_rhoMul T hs i j K).coeFn_toLp] with p hp
  rw [rhoMul, hp]
  ring

omit [IsFiniteMeasure Q] in
theorem inner_rhoMul_right (i j : ι) (H K : PredL2 𝓖 (barMeasure Q a T)) :
    ⟪(K : Lp ℝ 2 (barMeasure Q a T)), h.rhoMul T hs i j H⟫_ℝ = crossInt Q a T i j H K := by
  rw [inner_rhoMul_left, crossInt, crossInt]
  simp only [mul_comm ((K : Lp ℝ 2 (barMeasure Q a T)) _)]

include hs in
theorem crossInt_simple (i j : ι) (x y : Rect 𝓖 T →₀ ℝ) :
    haveI := h.isFiniteMeasure_bar T
    ⟪h.coordInt T i (simpleLin 𝓖 T (barMeasure Q a T) x),
      h.coordInt T j (simpleLin 𝓖 T (barMeasure Q a T) y)⟫_ℝ =
      crossInt Q a T i j (simpleLin 𝓖 T (barMeasure Q a T) x)
        (simpleLin 𝓖 T (barMeasure Q a T) y) := by
  have := h.isFiniteMeasure_bar T
  obtain ⟨C₁, hC₁⟩ := elemFun_bound x
  obtain ⟨C₂, hC₂⟩ := elemFun_bound y
  have hF : Integrable (fun p => elemFun x p * elemFun y p) (barMeasure Q a T) :=
    (integrable_const (C₁ * C₂)).mono'
      ((measurable_elemFun x).mul (measurable_elemFun y)).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul (hC₁ p) (hC₂ p) (abs_nonneg _) ((abs_nonneg _).trans (hC₁ p)))
  obtain ⟨hI, hEq⟩ := h.integral_bar_crossRatio hs T i j hF
  calc _ = ∫ ω, elemProc (N i) x T ω * elemProc (N j) y T ω ∂Q := by
        rw [real_inner_Lp_eq]
        refine integral_congr_ae ?_
        filter_upwards [h.coordInt_simple_ae T i x, h.coordInt_simple_ae T j y] with ω h1 h2
        rw [h1, h2]
    _ = ∫ ω, crossForm a i j T x y ω ∂Q := (h.integral_elemProc_mul i j x y).2
    _ = ∫ p, elemFun x p * elemFun y p * a i j p.1.toNNReal p.2 ∂timeProbMeasure T Q := by
        rw [timeProbMeasure, integral_prod_symm _ hI]; rfl
    _ = _ := hEq.symm
    _ = _ := by
        rw [crossInt]
        refine integral_congr_ae ?_
        filter_upwards [simpleLin_ae (μ := barMeasure Q a T) x,
          simpleLin_ae (μ := barMeasure Q a T) y] with p h1 h2
        rw [h1, h2]

include hs in
/-- **Cross isometry for general integrands** `E[∫H dN^i ∫K dN^j] = ∫ ρ^{ij} H̃ K̃ dν̄`. -/
theorem inner_coordInt (i j : ι) (H K : PredL2 𝓖 (barMeasure Q a T)) :
    ⟪h.coordInt T i H, h.coordInt T j K⟫_ℝ = crossInt Q a T i j H K := by
  have := h.isFiniteMeasure_bar T
  have hd := denseRange_simpleLin (𝓖 := 𝓖) (μ := barMeasure Q a T) (IsL2Integrator.bracketMeasure_ae_mem Q (traceA a) T)
  have hcv : Continuous fun F : PredL2 𝓖 (barMeasure Q a T) => (F : Lp ℝ 2 (barMeasure Q a T)) :=
    continuous_subtype_val
  have step2 : ∀ (H : PredL2 𝓖 (barMeasure Q a T)) (y : Rect 𝓖 T →₀ ℝ),
      ⟪h.coordInt T i H, h.coordInt T j (simpleLin 𝓖 T (barMeasure Q a T) y)⟫_ℝ =
        crossInt Q a T i j H (simpleLin 𝓖 T (barMeasure Q a T) y) := by
    intro H y
    have he := hd.equalizer
      (g := fun H => ⟪h.coordInt T i H, h.coordInt T j (simpleLin 𝓖 T (barMeasure Q a T) y)⟫_ℝ)
      (h := fun H => ⟪(H : Lp ℝ 2 (barMeasure Q a T)),
        h.rhoMul T hs i j (simpleLin 𝓖 T (barMeasure Q a T) y)⟫_ℝ)
      ((h.coordInt T i).continuous.inner continuous_const) (hcv.inner continuous_const)
      (funext fun x => by
        simp only [Function.comp_apply, inner_rhoMul_left]
        exact h.crossInt_simple T hs i j x y)
    have := congrFun he H
    simp only [inner_rhoMul_left] at this
    exact this
  have he := hd.equalizer (g := fun K => ⟪h.coordInt T i H, h.coordInt T j K⟫_ℝ)
    (h := fun K => ⟪(K : Lp ℝ 2 (barMeasure Q a T)), h.rhoMul T hs i j H⟫_ℝ)
    (continuous_const.inner (h.coordInt T j).continuous) (hcv.inner continuous_const)
    (funext fun y => by
      simp only [Function.comp_apply, inner_rhoMul_right]
      exact step2 H y)
  have := congrFun he K
  simp only [inner_rhoMul_right] at this
  exact this

include hs in
/-- **Cross isometry, `dt ⊗ Q` form**: `E[∫H dN^i ∫K dN^j] = ∫ H̃ K̃ a^{ij} d(dt ⊗ Q)`. -/
theorem integral_coordInt_mul (i j : ι) (H K : PredL2 𝓖 (barMeasure Q a T)) :
    Integrable (fun p => (H : Lp ℝ 2 (barMeasure Q a T)) p * (K : Lp ℝ 2 (barMeasure Q a T)) p *
      a i j p.1.toNNReal p.2) (timeProbMeasure T Q) ∧
    ∫ ω, h.coordInt T i H ω * h.coordInt T j K ω ∂Q =
      ∫ p, (H : Lp ℝ 2 (barMeasure Q a T)) p * (K : Lp ℝ 2 (barMeasure Q a T)) p *
        a i j p.1.toNNReal p.2 ∂timeProbMeasure T Q := by
  have hF := (Lp.memLp (H : Lp ℝ 2 (barMeasure Q a T))).integrable_mul
    (Lp.memLp (K : Lp ℝ 2 (barMeasure Q a T)))
  obtain ⟨hI, hEq⟩ := h.integral_bar_crossRatio hs T i j hF
  refine ⟨hI, ?_⟩
  rw [← real_inner_Lp_eq, h.inner_coordInt T hs i j H K, crossInt]
  exact hEq

include hs in
/-- **Cross isometry, Fubini form**: `E[∫H dN^i ∫K dN^j] = E ∫_{(0,T]} H̃ K̃ a^{ij} ds`. -/
theorem integral_coordInt_mul_fubini (i j : ι) (H K : PredL2 𝓖 (barMeasure Q a T)) :
    ∫ ω, h.coordInt T i H ω * h.coordInt T j K ω ∂Q =
      ∫ ω, (∫ r in Ioc (0 : ℝ) T, (H : Lp ℝ 2 (barMeasure Q a T)) (r, ω) *
        (K : Lp ℝ 2 (barMeasure Q a T)) (r, ω) * a i j r.toNNReal ω) ∂Q := by
  obtain ⟨hI, hEq⟩ := h.integral_coordInt_mul T hs i j H K
  rw [hEq, timeProbMeasure, integral_prod_symm _ hI]

end IsL2IntegratorVec

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
