module

public import BlockBand.SourceProcess.CoupledFrames.StopMult

/-!
# Bounded `𝓕_θ`-measurable multipliers after a stopping time

`MultProp hg H`: `H g` is an integrand with `I(H g) = H I(g)` a.s. It is stable under sums
and scalar multiples, holds for `𝓕_θ`-simple `H` when `g` vanishes on `{s ≤ θ}`
(`multProp_simple`, from `indicator_mult`), and for bounded `𝓕_θ`-measurable `H` (`stopMult`,
by the bounded simple approximation `approxBounded`, dominated convergence and
`ae_eq_nativeIntegralOf_of_tendsto`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}
variable {g : κ → ℝ × DriverSample S κ → ℝ}

/-- `H g` is an integrand and `I(H g) = H I(g)` a.s. -/
def MultProp (hg : NativeIntegrand μ T g) (H : DriverSample S κ → ℝ) : Prop :=
  ∃ hs : NativeIntegrand μ T (fun c p => H p.2 * g c p),
    (nativeIntegralOf hs : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
      fun x => H x * (nativeIntegralOf hg : DriverSample S κ → ℝ) x

theorem multProp_add {hg : NativeIntegrand μ T g} {H₁ H₂ : DriverSample S κ → ℝ}
    (h₁ : MultProp hg H₁) (h₂ : MultProp hg H₂) : MultProp hg (fun x => H₁ x + H₂ x) := by
  obtain ⟨hs₁, e₁⟩ := h₁
  obtain ⟨hs₂, e₂⟩ := h₂
  have hpt : (fun c (p : ℝ × DriverSample S κ) => (H₁ p.2 + H₂ p.2) * g c p) =
      fun c p => H₁ p.2 * g c p + H₂ p.2 * g c p := by
    funext c p; ring
  have hs : NativeIntegrand μ T (fun c (p : ℝ × DriverSample S κ) => (H₁ p.2 + H₂ p.2) * g c p) :=
    by rw [hpt]; exact nativeIntegrand_add hs₁ hs₂
  refine ⟨hs, ?_⟩
  have he : nativeIntegralOf hs = nativeIntegralOf hs₁ + nativeIntegralOf hs₂ := by
    rw [← nativeIntegralOf_add]
    exact nativeIntegralOf_congr _ _ fun c => Eventually.of_forall fun p =>
      congrFun (congrFun hpt c) p
  filter_upwards [he ▸ Lp.coeFn_add (nativeIntegralOf hs₁) (nativeIntegralOf hs₂), e₁, e₂]
    with x h h1 h2
  rw [h, Pi.add_apply, h1, h2]
  ring

theorem multProp_const_mul {hg : NativeIntegrand μ T g} {H : DriverSample S κ → ℝ}
    (h : MultProp hg H) (r : ℝ) : MultProp hg (fun x => r * H x) := by
  obtain ⟨hs₁, e₁⟩ := h
  have hpt : (fun c (p : ℝ × DriverSample S κ) => r * H p.2 * g c p) =
      fun c p => r * (H p.2 * g c p) := by
    funext c p; ring
  have hs : NativeIntegrand μ T (fun c (p : ℝ × DriverSample S κ) => r * H p.2 * g c p) := by
    rw [hpt]; exact nativeIntegrand_const_mul hs₁ r
  refine ⟨hs, ?_⟩
  have he : nativeIntegralOf hs = r • nativeIntegralOf hs₁ := by
    rw [← nativeIntegralOf_const_mul]
    exact nativeIntegralOf_congr _ _ fun c => Eventually.of_forall fun p =>
      congrFun (congrFun hpt c) p
  filter_upwards [he ▸ Lp.coeFn_smul r (nativeIntegralOf hs₁), e₁] with x h h1
  rw [h, Pi.smul_apply, h1, smul_eq_mul]
  ring

theorem multProp_congr {hg : NativeIntegrand μ T g} {H H' : DriverSample S κ → ℝ}
    (h : MultProp hg H) (e : H = H') : MultProp hg H' := e ▸ h

/-- **Simple `𝓕_θ`-measurable multipliers.** -/
theorem multProp_simple (hg : NativeIntegrand μ T g) {θ : DriverSample S κ → WithTop ℝ≥0}
    (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ) (hv : VanishBefore θ g)
    (f : @SimpleFunc (DriverSample S κ) hθ.measurableSpace ℝ) : MultProp hg f := by
  refine @SimpleFunc.induction (DriverSample S κ) ℝ hθ.measurableSpace _
    (motive := fun f => MultProp hg f) (fun r s hs => ?_) (fun f₁ f₂ _ h₁ h₂ => ?_) f
  · obtain ⟨hs', e'⟩ := indicator_mult hg hθ hv hs
    refine multProp_congr (multProp_const_mul ⟨hs', e'⟩ r) ?_
    funext x
    rw [@SimpleFunc.piecewise_apply _ _ hθ.measurableSpace]
    by_cases hx : x ∈ s
    · simp [hx]
    · simp [hx]
  · exact multProp_congr (multProp_add h₁ h₂) (by funext x; rfl)

/-- **Bounded `𝓕_θ`-measurable multipliers.** -/
theorem stopMult (hg : NativeIntegrand μ T g) {θ : DriverSample S κ → WithTop ℝ≥0}
    (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ) (hv : VanishBefore θ g)
    {H : DriverSample S κ → ℝ} (hH : StronglyMeasurable[hθ.measurableSpace] H) {C : ℝ}
    (hC : ∀ x, |H x| ≤ C) : MultProp hg H := by
  set Hn : ℕ → DriverSample S κ → ℝ := fun n => hH.approxBounded |C| n
  have hHn : ∀ n, MultProp hg (Hn n) := fun n => multProp_simple hg hθ hv _
  have hle : ∀ n x, |Hn n x| ≤ |C| := fun n x =>
    StronglyMeasurable.norm_approxBounded_le hH (abs_nonneg C) n x
  have hlim : ∀ x, Tendsto (fun n => Hn n x) atTop (𝓝 (H x)) := fun x =>
    StronglyMeasurable.tendsto_approxBounded_of_norm_le hH ((hC x).trans (le_abs_self C))
  choose hs hse using hHn
  have hpred : ∀ c, AEStronglyMeasurable[predictableSpace
      (enlargedPredictableFiltration (S := S) (κ := κ))] (fun p : ℝ × DriverSample S κ =>
        H p.2 * g c p) (timeProbMeasure T (driverLaw (κ := κ) μ)) := fun c =>
    aestronglyMeasurable_sub_of_tendsto_ae (fun n => (hs n c).1)
      (ae_of_all _ fun p => (hlim p.2).mul_const _)
  have hmem : ∀ c, MemLp (fun p : ℝ × DriverSample S κ => H p.2 * g c p) 2
      (timeProbMeasure T (driverLaw (κ := κ) μ)) := fun c =>
    MemLp.of_le ((hg c).2.const_mul |C|) ((hpred c).mono (predictableSpace_le _))
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_abs]
        exact mul_le_mul_of_nonneg_right ((hC p.2).trans (le_abs_self C)) (abs_nonneg _))
  let hs0 : NativeIntegrand μ T (fun c p => H p.2 * g c p) := fun c => ⟨hpred c, hmem c⟩
  refine ⟨hs0, ae_eq_nativeIntegralOf_of_tendsto hs hs0 (fun c => ?_) hse
    (ae_of_all _ fun x => (hlim x).mul_const _)⟩
  refine tendsto_integral_sq_of_dominated (B := fun p => 2 * |C| * |g c p|)
    (fun n => ((hs n c).1).mono (predictableSpace_le _)) ((hpred c).mono (predictableSpace_le _))
    (((hg c).2.integrable_sq.const_mul ((2 * |C|) ^ 2)).congr (ae_of_all _ fun p => by
      simp only [mul_pow, sq_abs]))
    (fun n p => ?_) (ae_of_all _ fun p => (hlim p.2).mul_const _)
  rw [← sub_mul, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  calc |Hn n p.2 - H p.2| ≤ |Hn n p.2| + |H p.2| := abs_sub _ _
    _ ≤ |C| + |C| := add_le_add (hle n p.2) ((hC p.2).trans (le_abs_self C))
    _ = 2 * |C| := by ring

end BlockBand.SourceProcess.CoupledFrames
