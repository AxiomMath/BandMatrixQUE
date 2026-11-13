module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegCompX
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The regularization errors vanish

Setting: a `DegSetup c W P` (`DegSetup`), the errors `degErr S n N` (`DegCompY`) and
`degErrX S n n' N` (`DegCompX`).

* **`tendsto_degErr`**: `degErr S n N → 0` as `n → ∞` (dominated convergence twice: the
  integrand `1_{[[0,τ]]} 2d²M² frob(tikX(s) ε_n - pinvX(s))` tends to `0` pointwise by
  `tendsto_tikX` and is bounded by `2d²M² · 4d`).
* `degErrX_le`: `degErrX S n n' N ≤ 2 degErr S n N + 2 degErr S n' N`.
* `nSel S m`, **`degErr_nSel_le`**: a level with `degErr S (nSel S m) N ≤ 2^{-m}` for all
  `N ≤ m`.
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Uniqueness
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {d : ℕ} {c : LipCoef d} {W : Set (Fin d → ℝ)} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The error integrand along a version `y` of the solution. -/
def errAt (c : LipCoef d) (s t : Matrix (Fin d) (Fin d) ℝ → Fin d → Fin d ⊕ Fin (d + d) → ℝ)
    (y : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 * frob (fun k c' => s (c.σ y) k c' + -t (c.σ y) k c'))

theorem tendsto_frob_tikX (s : Matrix (Fin d) (Fin d) ℝ) :
    Tendsto (fun n => frob (fun k c' => tikX s (regSeq n) k c' + -pinvX s k c')) atTop (𝓝 0) := by
  have h : Tendsto (fun n => frob (fun k c' => tikX s (regSeq n) k c' + -pinvX s k c')) atTop
      (𝓝 (∑ k : Fin d, ∑ c' : Fin d ⊕ Fin (d + d), (pinvX s k c' + -pinvX s k c') ^ 2)) :=
    tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun c' _ =>
      ((tendsto_tikX s k c').add_const _).pow 2
  simpa using h

theorem errAt_le (c : LipCoef d) (n : ℕ) (y : Fin d → ℝ) :
    errAt c (fun s => tikX s (regSeq n)) pinvX y ≤
      ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 * (4 * d)) :=
  ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (frob_tikX_sub_pinvX_le _ (regSeq_pos n)) (by positivity))

theorem degErr_eq (S : DegSetup c W P) {A : Set Ω} (hAP : P Aᶜ = 0) (n N : ℕ) :
    degErr S n N = ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, (stopSet S.τ).indicator (fun p =>
      errAt c (fun s => tikX s (regSeq n)) pinvX (jointVersion S.Y A p)) (r, ω)) ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hAP] with ω hω
  have hω' : ω ∈ A := by simpa using hω
  refine lintegral_congr fun r => ?_
  classical
  by_cases h : (r, ω) ∈ stopSet S.τ
  · simp only [indicator_of_mem h, errAt, jointVersion_of_mem hω']
  · simp only [indicator_of_notMem h]

theorem degErrX_eq (S : DegSetup c W P) {A : Set Ω} (hAP : P Aᶜ = 0) (n n' N : ℕ) :
    degErrX S n n' N = ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, (stopSet S.τ).indicator (fun p =>
      errAt c (fun s => tikX s (regSeq n)) (fun s => tikX s (regSeq n'))
        (jointVersion S.Y A p)) (r, ω)) ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hAP] with ω hω
  have hω' : ω ∈ A := by simpa using hω
  refine lintegral_congr fun r => ?_
  classical
  by_cases h : (r, ω) ∈ stopSet S.τ
  · simp only [indicator_of_mem h, errAt, jointVersion_of_mem hω']
  · simp only [indicator_of_notMem h]

theorem measurable_errV (S : DegSetup c W P) {A : Set Ω} (hA : MeasurableSet A)
    (hAc : ∀ ω ∈ A, Continuous fun t => S.Y t ω) (n : ℕ) :
    Measurable ((stopSet S.τ).indicator (fun p =>
      errAt c (fun s => tikX s (regSeq n)) pinvX (jointVersion S.Y A p))) := by
  have hYv : Measurable (jointVersion S.Y A) := measurable_jointVersion S.hYm hA hAc
  have hSm : MeasurableSet (stopSet S.τ) :=
    predictableSpace_le _ _ (measurableSet_stopSet S.𝓕 S.hτ)
  exact Measurable.indicator (((measurable_tikXerr_comp
    (fun i j => sigma_entry_measurable c hYv i j) (regSeq_pos n)).const_mul _).ennreal_ofReal) hSm

/-- **The regularization error vanishes.** -/
theorem tendsto_degErr (S : DegSetup c W P) (N : ℕ) :
    Tendsto (fun n => degErr S n N) atTop (𝓝 0) := by
  classical
  obtain ⟨A, hA, hAP, hAc⟩ := exists_good_set S.hYc
  simp_rw [degErr_eq S hAP]
  set C : ℝ≥0∞ := ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 * (4 * d))
  set F : ℕ → ℝ × Ω → ℝ≥0∞ := fun n => (stopSet S.τ).indicator (fun p =>
      errAt c (fun s => tikX s (regSeq n)) pinvX (jointVersion S.Y A p))
  have hF : ∀ n, Measurable (F n) := measurable_errV S hA hAc
  have hFb : ∀ n p, F n p ≤ C := fun n p => by
    simp only [F, indicator_apply]
    split_ifs
    · exact errAt_le c n _
    · exact zero_le
  have hFl : ∀ p, Tendsto (fun n => F n p) atTop (𝓝 0) := fun p => by
    simp only [F, indicator_apply]
    split_ifs
    · have h := (ENNReal.continuous_ofReal.tendsto _).comp
        ((tendsto_frob_tikX (c.σ (jointVersion S.Y A p))).const_mul (2 * d ^ 2 * c.M ^ 2))
      simpa [errAt, Function.comp_def] using h
    · exact tendsto_const_nhds
  have hin : ∀ ω, Tendsto (fun n => ∫⁻ r in Ioc (0 : ℝ) N, F n (r, ω)) atTop (𝓝 0) := fun ω => by
    have h := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) N))
      (F := fun n r => F n (r, ω)) (f := fun _ => 0) (fun _ => C)
      (fun n => (hF n).comp (measurable_id.prodMk measurable_const))
      (fun n => Eventually.of_forall fun r => hFb n _)
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))
      (Eventually.of_forall fun r => hFl _)
    simpa using h
  have h := tendsto_lintegral_of_dominated_convergence (μ := P)
    (F := fun n ω => ∫⁻ r in Ioc (0 : ℝ) N, F n (r, ω)) (f := fun _ => 0)
    (fun _ => ∫⁻ _r in Ioc (0 : ℝ) N, C) (fun n => (hF n).lintegral_prod_left')
    (fun n => Eventually.of_forall fun ω => lintegral_mono fun r => hFb n _)
    (by
      rw [lintegral_const]
      refine ENNReal.mul_ne_top ?_ (by simp)
      rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))
    (Eventually.of_forall hin)
  simpa using h

theorem degErr_mono (S : DegSetup c W P) (n : ℕ) {N N' : ℕ} (h : N ≤ N') :
    degErr S n N ≤ degErr S n N' :=
  lintegral_mono fun _ => lintegral_mono_set (Ioc_subset_Ioc_right (by exact_mod_cast h))

theorem degErrX_le (S : DegSetup c W P) (n n' N : ℕ) :
    degErrX S n n' N ≤ 2 * degErr S n N + 2 * degErr S n' N := by
  classical
  obtain ⟨A, hA, hAP, hAc⟩ := exists_good_set S.hYc
  rw [degErrX_eq S hAP, degErr_eq S hAP, degErr_eq S hAP]
  set F : ℕ → ℝ × Ω → ℝ≥0∞ := fun n => (stopSet S.τ).indicator (fun p =>
      errAt c (fun s => tikX s (regSeq n)) pinvX (jointVersion S.Y A p))
  have hF : ∀ n, Measurable (F n) := measurable_errV S hA hAc
  have hpt : ∀ p, (stopSet S.τ).indicator (fun p => errAt c (fun s => tikX s (regSeq n))
      (fun s => tikX s (regSeq n')) (jointVersion S.Y A p)) p ≤ 2 * F n p + 2 * F n' p := by
    intro p
    simp only [F, indicator_apply]
    split_ifs
    · simp only [errAt]
      set s := c.σ (jointVersion S.Y A p)
      have h1 := frob_tikX_sub_le s (regSeq n) (regSeq n')
      have h2 := frob_nonneg fun k c' => tikX s (regSeq n) k c' + -pinvX s k c'
      have h3 := frob_nonneg fun k c' => tikX s (regSeq n') k c' + -pinvX s k c'
      have hC : (0 : ℝ) ≤ 2 * d ^ 2 * c.M ^ 2 := by positivity
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [mul_le_mul_of_nonneg_left h1 hC]
    · simp
  have hmeas : ∀ n, Measurable fun ω => ∫⁻ r in Ioc (0 : ℝ) N, F n (r, ω) := fun n =>
    (hF n).lintegral_prod_left'
  calc _ ≤ ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, (2 * F n (r, ω) + 2 * F n' (r, ω))) ∂P :=
        lintegral_mono fun ω => lintegral_mono fun r => hpt _
    _ = ∫⁻ ω, ((2 * ∫⁻ r in Ioc (0 : ℝ) N, F n (r, ω)) +
          2 * ∫⁻ r in Ioc (0 : ℝ) N, F n' (r, ω)) ∂P := by
        refine lintegral_congr fun ω => ?_
        have h1 : Measurable fun r => F n (r, ω) :=
          (hF n).comp (measurable_id.prodMk measurable_const)
        have h2 : Measurable fun r => F n' (r, ω) :=
          (hF n').comp (measurable_id.prodMk measurable_const)
        rw [lintegral_add_left (h1.const_mul 2), lintegral_const_mul _ h1,
          lintegral_const_mul _ h2]
    _ = _ := by
        rw [lintegral_add_left ((hmeas n).const_mul 2), lintegral_const_mul _ (hmeas n),
          lintegral_const_mul _ (hmeas n')]

theorem exists_degErr_le (S : DegSetup c W P) (m : ℕ) :
    ∃ n, degErr S n m ≤ ENNReal.ofReal (1 / 2 ^ m) := by
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2 ^ m) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨n, hn⟩ := ((tendsto_order.1 (tendsto_degErr S m)).2 _ hpos).exists
  exact ⟨n, hn.le⟩

/-- A regularization level adapted to the Euler grid `m`. -/
def nSel (S : DegSetup c W P) (m : ℕ) : ℕ := Classical.choose (exists_degErr_le S m)

theorem degErr_nSel_le (S : DegSetup c W P) {N m : ℕ} (h : N ≤ m) :
    degErr S (nSel S m) N ≤ ENNReal.ofReal (1 / 2 ^ m) :=
  (degErr_mono S _ h).trans (Classical.choose_spec (exists_degErr_le S m))

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
