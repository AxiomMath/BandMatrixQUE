module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.Analysis.Complex.Basic

/-!
# One step of a complex coordinate: real drift and variance from the complex errors

For a complex coordinate step `Δ = Z₁ - Z₀` on an `F`-event `A` and a unit phase `u`, the real
increment `d = 1_A Re(uΔ)` satisfies, almost everywhere,
* `stepCond_drift`: `|E[d|F]| ≤ s C_b + ‖1_A(E[1_AΔ|F] - s P_b)‖`;
* `stepCond_var`: `E[d²|F] ≤ s C_c + ‖1_A(E[1_A ΔΔ̄|F] - s P_c)‖`;
where `P_b, P_c` are any predictions bounded by `C_b, C_c` on `A`. These are the integrands of
`ClosedSummed` (drift with `e`, bracket with `(e, swapE e)`, `Δ̄ = ΔG_{swapE e}`). Integrability
comes from the fourth moment `E‖1_AΔ‖⁴ < ∞` (`ClosedFourth`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory

variable {Ω : Type*} {F : MeasurableSpace Ω} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ]

/-- The real functional `z ↦ Re(u z)`. -/
def reMul (u : ℂ) : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.lsmul ℝ ℂ u)

theorem reMul_apply (u z : ℂ) : reMul u z = (u * z).re := rfl

theorem abs_reMul_le {u : ℂ} (hu : ‖u‖ = 1) (z : ℂ) : |reMul u z| ≤ ‖z‖ := by
  rw [reMul_apply]
  exact (Complex.abs_re_le_norm _).trans (by rw [norm_mul, hu, one_mul])

theorem integrable_of_pow4 {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ)
    (h4 : Integrable (fun ω => ‖f ω‖ ^ 4) μ) : Integrable f μ := by
  refine Integrable.mono' ((integrable_const 1).add h4) hf (Filter.Eventually.of_forall fun ω => ?_)
  have := norm_nonneg (f ω)
  show ‖f ω‖ ≤ 1 + ‖f ω‖ ^ 4
  nlinarith [sq_nonneg (‖f ω‖ ^ 2 - 1), sq_nonneg (‖f ω‖ - 1)]

theorem integrable_sq_of_pow4 {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ)
    (h4 : Integrable (fun ω => ‖f ω‖ ^ 4) μ) : Integrable (fun ω => ‖f ω‖ ^ 2) μ := by
  refine Integrable.mono' ((integrable_const 1).add h4) (hf.norm.pow 2)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  show ‖f ω‖ ^ 2 ≤ 1 + ‖f ω‖ ^ 4
  nlinarith [sq_nonneg (‖f ω‖ ^ 2 - 1)]

omit [IsFiniteMeasure μ] in
/-- Off the `F`-event `A`, the conditional expectation of `1_A X` vanishes. -/
theorem ae_condExp_indicator_eq {A : Set Ω} (hA : MeasurableSet[F] A) {X : Ω → ℂ}
    (hX : Integrable (A.indicator X) μ) :
    μ[A.indicator X | F] =ᵐ[μ] A.indicator (μ[A.indicator X | F]) := by
  have := MeasureTheory.condExp_indicator (m := F) hX hA
  rwa [Set.indicator_indicator, Set.inter_self] at this

/-- The pointwise bound behind both transfers. -/
theorem norm_le_of_indicator {A : Set Ω} {Y : Ω → ℂ} {ω : Ω}
    (hY : Y ω = A.indicator Y ω) {P : Ω → ℂ} {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hP : ω ∈ A → ‖P ω‖ ≤ C) :
    ‖Y ω‖ ≤ s * C + ‖A.indicator (fun ω => Y ω - (s : ℂ) * P ω) ω‖ := by
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω]
    have h1 : ‖(s : ℂ) * P ω‖ ≤ s * C := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
      exact mul_le_mul_of_nonneg_left (hP hω) hs
    have := norm_sub_norm_le (Y ω) ((s : ℂ) * P ω)
    linarith
  · rw [hY, Set.indicator_of_notMem hω, norm_zero]
    exact add_nonneg (mul_nonneg hs hC) (norm_nonneg _)

variable {A : Set Ω} {Δ : Ω → ℂ}

theorem indicator_reMul (u : ℂ) (A : Set Ω) (Δ : Ω → ℂ) :
    A.indicator (fun ω => reMul u (Δ ω)) = fun ω => reMul u (A.indicator Δ ω) := by
  funext ω; by_cases h : ω ∈ A <;> simp [h]

omit [IsFiniteMeasure μ] in
/-- **The drift transfer.** -/
theorem stepCond_drift (hA : MeasurableSet[F] A) {u : ℂ} (hu : ‖u‖ = 1)
    (hΔ : Integrable (A.indicator Δ) μ) {P : Ω → ℂ} {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hP : ∀ ω ∈ A, ‖P ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, |μ[A.indicator (fun ω => reMul u (Δ ω)) | F] ω| ≤ s * C +
      ‖A.indicator (fun ω => μ[A.indicator Δ | F] ω - (s : ℂ) * P ω) ω‖ := by
  rw [indicator_reMul]
  filter_upwards [(reMul u).comp_condExp_comm (m := F) hΔ, ae_condExp_indicator_eq hA hΔ]
    with ω h1 h2
  change |μ[(reMul u) ∘ A.indicator Δ | F] ω| ≤ _
  rw [← h1]
  exact (abs_reMul_le hu _).trans (norm_le_of_indicator h2 hs hC (hP ω))

/-- **The variance transfer**, with `Δ' = Δ̄` pointwise. -/
theorem stepCond_var (hA : MeasurableSet[F] A) {u : ℂ} (hu : ‖u‖ = 1) {Δ' : Ω → ℂ}
    (hstar : ∀ ω, Δ' ω = star (Δ ω)) (hm : AEStronglyMeasurable (A.indicator Δ) μ)
    (h4 : Integrable (fun ω => ‖A.indicator Δ ω‖ ^ 4) μ) {P : Ω → ℂ} {s C : ℝ} (hs : 0 ≤ s)
    (hC : 0 ≤ C) (hP : ∀ ω ∈ A, ‖P ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, μ[fun ω => A.indicator (fun ω => reMul u (Δ ω)) ω ^ 2 | F] ω ≤ s * C +
      ‖A.indicator (fun ω => μ[A.indicator (fun ω => Δ ω * Δ' ω) | F] ω - (s : ℂ) * P ω) ω‖ := by
  set Y : Ω → ℂ := A.indicator fun ω => Δ ω * Δ' ω with hYdef
  have hY : ∀ ω, Y ω = ((‖A.indicator Δ ω‖ ^ 2 : ℝ) : ℂ) := fun ω => by
    by_cases h : ω ∈ A
    · simp only [hYdef, Set.indicator_of_mem h, hstar, Complex.ofReal_pow]
      exact Complex.mul_conj' (Δ ω)
    · simp [hYdef, h]
  have hsq : Integrable (fun ω => ‖A.indicator Δ ω‖ ^ 2) μ := integrable_sq_of_pow4 hm h4
  have hYi : Integrable Y μ := by
    have : Y = fun ω => ((‖A.indicator Δ ω‖ ^ 2 : ℝ) : ℂ) := funext hY
    rw [this]; exact hsq.ofReal
  have hYi' : Integrable (A.indicator Y) μ := by
    rwa [hYdef, Set.indicator_indicator, Set.inter_self]
  have hYA : A.indicator Y = Y := by rw [hYdef, Set.indicator_indicator, Set.inter_self]
  have hd2 : Integrable (fun ω => A.indicator (fun ω => reMul u (Δ ω)) ω ^ 2) μ := by
    refine Integrable.mono' hsq ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · rw [indicator_reMul]
      exact ((reMul u).continuous.comp_aestronglyMeasurable hm).pow 2
    · rw [indicator_reMul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := abs_reMul_le hu (A.indicator Δ ω)
      have h0 := abs_nonneg (reMul u (A.indicator Δ ω))
      rw [← sq_abs]; nlinarith
  have hmono : μ[fun ω => A.indicator (fun ω => reMul u (Δ ω)) ω ^ 2 | F] ≤ᵐ[μ]
      μ[fun ω => ‖A.indicator Δ ω‖ ^ 2 | F] := by
    refine condExp_mono hd2 hsq (Filter.Eventually.of_forall fun ω => ?_)
    simp only [indicator_reMul]
    have := abs_reMul_le hu (A.indicator Δ ω)
    have h0 := abs_nonneg (reMul u (A.indicator Δ ω))
    rw [← sq_abs]; nlinarith
  have hre : (fun ω => Complex.reCLM (μ[Y | F] ω)) =ᵐ[μ] μ[fun ω => Complex.reCLM (Y ω) | F] :=
    Complex.reCLM.comp_condExp_comm hYi
  have hre' : (fun ω => Complex.reCLM (Y ω)) = fun ω => ‖A.indicator Δ ω‖ ^ 2 := by
    funext ω; rw [hY]; norm_cast
  rw [hre'] at hre
  have hind := ae_condExp_indicator_eq (μ := μ) hA hYi'
  rw [hYA] at hind
  filter_upwards [hmono, hre, hind] with ω h1 h2 h3
  refine h1.trans ?_
  rw [← h2]
  exact (Complex.re_le_norm _).trans (norm_le_of_indicator h3 hs hC (hP ω))

end BlockBand.SourceProcess.ClosedSumProof
