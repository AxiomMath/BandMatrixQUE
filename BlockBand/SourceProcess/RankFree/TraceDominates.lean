module

public import BlockBand.SourceProcess.RankFree.TraceProcess

/-!
# The trace process dominates the trace

* `norm_sq_le_traceProc`: a.s., `‖X_t‖² ≤ traceProc X t` for all `t` (births are orthogonal to
  each other and to the frame column they enter, which is zero before the birth:
  `sharpFrame_mul_single_zero`; a pending birth contributes `β_k ≥ 0`).
* `traceProc_zero_le`: a.s., `traceProc X 0 ≤ ‖ξ‖² + ∑_k β_k`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {nb : ℕ}

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
theorem beta_nonneg {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {w : Ω → ι → ℂ} {β : ℝ} (h : ∀ᵐ x ∂Q, ∑ i, ‖w x i‖ ^ 2 = β) : 0 ≤ β := by
  obtain ⟨x, hx⟩ := h.exists
  exact hx ▸ Finset.sum_nonneg fun i _ => sq_nonneg _

omit [DecidableEq ι] in
theorem reInner_birthMat_eq_zero {j : c} {v : ι → ℂ} {Y : Matrix ι c ℂ}
    (hY : Y * Matrix.single j j (1 : ℂ) = 0) : reInner (birthMat j v) Y = 0 := by
  rw [reInner_birthMat]
  have h : ∀ i, Y i j = 0 := fun i => by
    have := congrFun (congrFun hY i) j
    rw [mul_single_diag_apply] at this
    simpa using this
  simp [h]

/-- **The trace process dominates `‖X_t‖²`.** -/
theorem norm_sq_le_traceProc {D0 : ℝ} (hD0 : 0 < D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξ0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x))
    {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → c}
    {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ} {β : Fin nb → ℝ}
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)))
    (hw : ∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k))
    (hcol : Function.Injective col) (hDcol : ∀ k j, D (col k) j = 0 ∧ D j (col k) = 0)
    (hξcol : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i, ξ x i (col k) = 0)
    (hwβ : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∑ i, ‖w k x i‖ ^ 2 = β k)
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsBornSDESolution μ D0 Naux P D ξ (frameBirthJump τ col w) X) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, ‖X t x‖ ^ 2 ≤ traceProc X τ col w β t x := by
  have hZB := fun k => sharpFrame_mul_single_zero hD0 hP hD hξ hξ0 hτ hw hcol hDcol hξcol hX k
  filter_upwards [ae_all_iff.2 hZB, ae_all_iff.2 hwβ] with x hz hb t
  set a : Fin nb → Matrix ι c ℂ :=
    fun k => if τ k x ≤ t then birthMat (col k) (posW τ w k x) else 0
  have horth : ∀ k ∈ (Finset.univ : Finset (Fin nb)), ∀ l ∈ (Finset.univ : Finset (Fin nb)),
      k ≠ l → reInner (a k) (a l) = 0 := fun k _ l _ hkl => by
    simp only [a]
    split_ifs
    · exact reInner_birthMat_of_ne (hcol.ne hkl) _ _
    · simp
    · simp
    · simp
  rw [X_eq_sharpFrame_add X τ col w t x, norm_sq_add_sum_orth Finset.univ _ a horth, traceProc]
  refine add_le_add le_rfl (Finset.sum_le_sum fun k _ => ?_)
  have hβ0 : 0 ≤ β k := beta_nonneg (hwβ k)
  by_cases h : τ k x ≤ t
  · have hst : stoppedProcess (sharpFrame X τ col w) (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)) t x =
        sharpFrame X τ col w (τ k x) x := by
      rw [stoppedProcess_eq_of_ge (τ := fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0))
        (WithTop.coe_le_coe.2 h)]
      rfl
    simp only [a, h, ↓reduceIte, hst, map_sub, reInner_birthMat_eq_zero (hz k),
      sub_zero, norm_sq_birthMat, posW]
    split_ifs
    · rw [hb k]
    · simp
  · have hst : stoppedProcess (sharpFrame X τ col w) (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)) t x =
        sharpFrame X τ col w t x :=
      stoppedProcess_eq_of_le (τ := fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0))
        (WithTop.coe_le_coe.2 (not_le.1 h).le)
    simp only [a, h, ↓reduceIte, hst, sub_self, map_zero, _root_.zero_apply, norm_zero]
    split_ifs <;> simp [hβ0]

/-- **The initial trace.** -/
theorem traceProc_zero_le {D0 : ℝ} {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → c}
    {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ} {β : Fin nb → ℝ}
    (hwβ : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∑ i, ‖w k x i‖ ^ 2 = β k)
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsBornSDESolution μ D0 Naux P D ξ (frameBirthJump τ col w) X) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      traceProc X τ col w β 0 x ≤ ‖ξ x‖ ^ 2 + ∑ k, β k := by
  filter_upwards [sharpFrame_zero hX] with x hx
  have h0 : ∀ k, stoppedProcess (sharpFrame X τ col w) (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0))
      0 x = sharpFrame X τ col w 0 x := fun k =>
    stoppedProcess_eq_of_le (τ := fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0))
      (WithTop.coe_le_coe.2 zero_le)
  simp only [traceProc, h0, sub_self, map_zero, mul_zero, zero_add, hx]
  refine add_le_add le_rfl (Finset.sum_le_sum fun k _ => ?_)
  split_ifs
  · rfl
  · exact beta_nonneg (hwβ k)

end BlockBand.SourceProcess.RankFree
