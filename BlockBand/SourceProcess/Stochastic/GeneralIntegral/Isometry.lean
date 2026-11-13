module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Density
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Elementary
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The `L²` stochastic integral against a general integrator

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, `h : IsL2Integrator Q 𝓖 N α`,
horizon `T`. Integrand space `PredL2 𝓖 ν_T` (predictable classes in `L²(ν_T)`,
`ν_T = bracketMeasure Q α T = α ds ⊗ Q` on `(0,T] × Ω`); value space `L²(Q)`.

* `integrandLin h T`, `valueLin h T`: simple integrands `x : Rect 𝓖 T →₀ ℝ` to their class in
  `PredL2` and to their elementary integral `∑ c_r 1_{A_r} (M_{t_r} - M_{s_r})` in `L²(Q)`.
* `inner_valueLin`: `E[I(x) I(y)] = ⟪x, y⟫_{L²(ν_T)}` (from `setIntegral_incr_mul_incr`).
* `stochIntegral h T : PredL2 𝓖 ν_T →ₗᵢ[ℝ] L²(Q)`: the unique continuous extension, a linear
  isometry (`rectSpan_dense`).
* `stochIntegral_rect`: `I(1_{(s,t] × A}) = 1_A (N_t - N_s)` a.s.
* `integral_sq_stochIntegral`: `E[I(H)²] = ∫ H² dν_T = E ∫_0^T H_s² α_s ds`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {N α : ℝ≥0 → Ω → ℝ}

namespace IsL2Integrator

/-- `ν_T` of a possibly empty rectangle `(a,b] × D`, `b ≤ T`. -/
theorem bracketMeasure_rect' (h : IsL2Integrator Q 𝓖 N α) {T a b : ℝ≥0} (hbT : b ≤ T)
    {D : Set Ω} (hD : MeasurableSet D) :
    (bracketMeasure Q α T).real (Ioc (a : ℝ) b ×ˢ D) = ∫ ω in D, bracketIntegral α a b ω ∂Q := by
  by_cases hab : a ≤ b
  · rw [measureReal_def, h.bracketMeasure_rect hab hbT hD,
      ENNReal.toReal_ofReal (setIntegral_nonneg hD fun ω _ => h.bracketIntegral_nonneg a b ω)]
  · have he : Ioc (a : ℝ) b = ∅ := Ioc_eq_empty_of_le (by exact_mod_cast (not_le.1 hab).le)
    have h0 : ∀ ω, bracketIntegral α a b ω = 0 := fun ω => by
      rw [bracketIntegral, he, Measure.restrict_empty, integral_zero_measure]
    simp [he, h0]

variable (h : IsL2Integrator Q 𝓖 N α) (T : ℝ≥0)

/-- Elementary integral of a rectangle, as an element of `L²(Q)`. -/
def rectLp (r : Rect 𝓖 T) : Lp ℝ 2 Q :=
  (rectProc_memLp h.mart_memLp r T).toLp _

/-- Simple integrands to their class in `PredL2 𝓖 ν_T`. -/
def integrandLin : (Rect 𝓖 T →₀ ℝ) →ₗ[ℝ] PredL2 𝓖 (bracketMeasure Q α T) :=
  haveI := h.isFiniteMeasure_bracketMeasure T
  Finsupp.linearCombination ℝ (rectL2 𝓖 T (bracketMeasure Q α T))

/-- Simple integrands to their elementary integral in `L²(Q)`. -/
def valueLin : (Rect 𝓖 T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 Q :=
  Finsupp.linearCombination ℝ (h.rectLp T)

theorem inner_rectLp (r₁ r₂ : Rect 𝓖 T) :
    ⟪h.rectLp T r₁, h.rectLp T r₂⟫_ℝ = (bracketMeasure Q α T).real (r₁.set ∩ r₂.set) := by
  have hD : MeasurableSet[𝓖 (max r₁.s r₂.s)] (r₁.A ∩ r₂.A) :=
    (𝓖.mono (le_max_left _ _) _ r₁.hA).inter (𝓖.mono (le_max_right _ _) _ r₂.hA)
  have hset : r₁.set ∩ r₂.set = Ioc ((max r₁.s r₂.s : ℝ≥0) : ℝ) (min r₁.t r₂.t : ℝ≥0) ×ˢ
      (r₁.A ∩ r₂.A) := by
    simp only [Rect.set, prod_inter_prod, Ioc_inter_Ioc, NNReal.coe_max, NNReal.coe_min]
  rw [hset, h.bracketMeasure_rect' ((min_le_left _ _).trans r₁.htT) (𝓖.le _ _ hD),
    ← h.setIntegral_incr_mul_incr r₁.hst r₂.hst hD, L2.inner_def,
    ← integral_indicator (𝓖.le _ _ hD)]
  refine integral_congr_ae ?_
  filter_upwards [(rectProc_memLp h.mart_memLp r₁ T).coeFn_toLp,
    (rectProc_memLp h.mart_memLp r₂ T).coeFn_toLp] with ω h1 h2
  change ⟪h.rectLp T r₁ ω, h.rectLp T r₂ ω⟫_ℝ = _
  rw [rectLp, rectLp, h1, h2, rectProc_T, rectProc_T]
  by_cases hω₁ : ω ∈ r₁.A <;> by_cases hω₂ : ω ∈ r₂.A <;>
    simp [hω₁, hω₂, mul_comm]

omit [IsFiniteMeasure Q] in
theorem inner_rectL2 (r₁ r₂ : Rect 𝓖 T) [IsFiniteMeasure (bracketMeasure Q α T)] :
    ⟪rectL2 𝓖 T (bracketMeasure Q α T) r₁, rectL2 𝓖 T (bracketMeasure Q α T) r₂⟫_ℝ =
      (bracketMeasure Q α T).real (r₁.set ∩ r₂.set) := by
  rw [Submodule.coe_inner, rectL2_coe, rectL2_coe, indLp, L2.inner_indicatorConstLp_one]
  have : ∀ᵐ x ∂(bracketMeasure Q α T).restrict r₁.set,
      indLp (bracketMeasure Q α T) r₂.measurableSet 1 x = r₂.set.indicator 1 x :=
    ae_restrict_of_ae indicatorConstLp_coeFn
  rw [integral_congr_ae this, integral_indicator_one r₂.measurableSet,
    measureReal_restrict_apply r₂.measurableSet, inter_comm]

/-- **Polarized isometry on simple integrands.** -/
theorem inner_valueLin (x y : Rect 𝓖 T →₀ ℝ) :
    ⟪h.valueLin T x, h.valueLin T y⟫_ℝ = ⟪h.integrandLin T x, h.integrandLin T y⟫_ℝ := by
  have := h.isFiniteMeasure_bracketMeasure T
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']
  | single r c =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
      | single r' c' =>
          simp only [valueLin, integrandLin, Finsupp.linearCombination_single,
            real_inner_smul_left, real_inner_smul_right, inner_rectLp, inner_rectL2]

theorem norm_valueLin (x : Rect 𝓖 T →₀ ℝ) : ‖h.valueLin T x‖ = ‖h.integrandLin T x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner (F := PredL2 𝓖 (bracketMeasure Q α T)),
    inner_valueLin]

theorem denseRange_integrandLin : DenseRange (h.integrandLin T) := by
  have := h.isFiniteMeasure_bracketMeasure T
  change Dense (range (h.integrandLin T))
  rw [← LinearMap.coe_range, integrandLin, Finsupp.range_linearCombination]
  exact rectSpan_dense 𝓖 T (bracketMeasure_ae_mem Q α T)

/-- **The stochastic integral** `H ↦ ∫_0^T H dN`, a linear isometry
`PredL2 𝓖 ν_T → L²(Q)`. -/
def stochIntegral : PredL2 𝓖 (bracketMeasure Q α T) →ₗᵢ[ℝ] Lp ℝ 2 Q :=
  (h.valueLin T).extendOfIsometry (h.denseRange_integrandLin T) (h.norm_valueLin T)

theorem stochIntegral_integrandLin (x : Rect 𝓖 T →₀ ℝ) :
    h.stochIntegral T (h.integrandLin T x) = h.valueLin T x :=
  LinearMap.extendOfIsometry_eq _ _ _ x

omit [IsFiniteMeasure Q] in
theorem valueLin_ae (x : Rect 𝓖 T →₀ ℝ) :
    (h.valueLin T x : Ω → ℝ) =ᵐ[Q] elemProc h.mart x T := by
  induction x using Finsupp.induction_linear with
  | zero => simpa using Lp.coeFn_zero ℝ 2 Q
  | add x y hx hy =>
      simp only [map_add, Pi.add_apply]
      exact (Lp.coeFn_add _ _).trans (hx.add hy)
  | single r c =>
      simp only [valueLin, Finsupp.linearCombination_single, elemProc_single]
      exact (Lp.coeFn_smul _ _).trans ((rectProc_memLp h.mart_memLp r T).coeFn_toLp.const_smul c)

/-- The integral of a simple integrand is the elementary sum against `N`, a.s. -/
theorem stochIntegral_integrandLin_ae (x : Rect 𝓖 T →₀ ℝ) :
    (h.stochIntegral T (h.integrandLin T x) : Ω → ℝ) =ᵐ[Q] elemProc N x T := by
  rw [stochIntegral_integrandLin]
  exact (h.valueLin_ae T x).trans (elemProc_ae h.mart_ae x T)

/-- **Elementary integral of a rectangle**: `I(1_{(s,t] × A}) = 1_A (N_t - N_s)` a.s. -/
theorem stochIntegral_rect [IsFiniteMeasure (bracketMeasure Q α T)] (r : Rect 𝓖 T) :
    (h.stochIntegral T (rectL2 𝓖 T (bracketMeasure Q α T) r) : Ω → ℝ) =ᵐ[Q]
      r.A.indicator fun ω => N r.t ω - N r.s ω := by
  have hx : rectL2 𝓖 T (bracketMeasure Q α T) r = h.integrandLin T (Finsupp.single r 1) := by
    simp [integrandLin]
  rw [hx]
  refine (h.stochIntegral_integrandLin_ae T _).trans (Eventually.of_forall fun ω => ?_)
  simp [rectProc_T]

/-- **Itô isometry**: `E[(∫_0^T H dN)²] = ∫ H² dν_T`. -/
theorem integral_sq_stochIntegral (H : PredL2 𝓖 (bracketMeasure Q α T)) :
    ∫ ω, (h.stochIntegral T H ω) ^ 2 ∂Q =
      ∫ p, ((H : Lp ℝ 2 (bracketMeasure Q α T)) p) ^ 2 ∂bracketMeasure Q α T := by
  have h1 := real_inner_self_eq_norm_sq (h.stochIntegral T H)
  have h2 := real_inner_self_eq_norm_sq (H : Lp ℝ 2 (bracketMeasure Q α T))
  rw [LinearIsometry.norm_map] at h1
  have h3 : ‖H‖ = ‖(H : Lp ℝ 2 (bracketMeasure Q α T))‖ := rfl
  rw [L2.inner_def] at h1 h2
  simp only [RCLike.inner_apply, conj_trivial] at h1 h2
  simp only [sq]
  rw [h1, h2, h3]

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
