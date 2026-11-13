module

public import BlockBand.Endpoints.Response.NearSchattenProkhorovGrid
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuous-path realization with fdd convergence at all real times (pure probability)

A proof of `NsProkhorovRealization`. Pure probability, no random-matrix objects.

Main result: `nsp_realization`. For a countable index type `ι`, probability spaces `(Ω n, P n)`
and processes `X n i t`, measurable in `ω` for every `(n, i, t)`, tight at every `t ≥ t₀`
(`NspTightAt`) and with asymptotically small sup-modulus on every `[t₀, T]` (`NspModulus`, outer
probability), every sequence has a strictly increasing `φ` and a probability measure `ν` on
`ι × ℕ × ℕ → ℂ` such that the canonical processes `nspZ t₀ i t` are measurable, a.s. continuous
on `[t₀, ∞)`, and the fdd of `X (φ n)` at all real times `≥ t₀` converge to those of `nspZ`
under `ν` (bounded continuous tests).

Steps (with dyadic grid values in place of interpolation; Billingsley Thm 7.3 is not needed in
this form):
* grid fdd (`nsp_grid_fdd`): Prokhorov limit `ν` of the dyadic grid laws (`NearSchattenProkhorovGrid`);
* limit side (`nsp_limit_grid_tendsto`): dominated convergence along the dyadic lower
  approximations on the a.s. good paths;
* finite-width side (`nsp_finite_grid_close`, a Slutsky step): the step values at `t` and at its
  dyadic approximation differ by at most the modulus at `2^{-j}`; with tightness at `t` and
  uniform continuity of the test on a compact ball, the integrals are uniformly close.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

variable {ι : Type} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

theorem nsp_integrable_bcf_comp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {m : ℕ} (Ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ)
    {A : α → Fin m → ℂ} (hA : Measurable A) : Integrable (fun ω => Ψ (A ω)) μ :=
  (integrable_const ‖Ψ‖).mono' (Ψ.continuous.measurable.comp hA).aestronglyMeasurable
    (ae_of_all _ fun _ => Ψ.norm_coe_le_norm _)

/-- **Finite-width Slutsky step.** The test integrals at the times `ts` and at their dyadic
lower approximations of level `j` are uniformly close for large `j` and `n`. -/
theorem nsp_finite_grid_close {t₀ : ℝ} {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : ∀ n, ι → ℝ → Ω n → ℂ} (hX : ∀ n i t, Measurable (X n i t))
    (hT : NspTightAt t₀ P X) (hC : NspModulus t₀ P X) {m : ℕ} (is : Fin m → ι)
    (ts : Fin m → ℝ) (hts : ∀ l, t₀ ≤ ts l) (Ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      |∫ ω, Ψ (fun l => X n (is l) (ts l) ω) ∂P n -
        ∫ ω, Ψ (fun l => X n (is l) (nspTime t₀ (nspIdx t₀ (ts l) j) j) ω) ∂P n| ≤ ε := by
  set C := ‖Ψ‖ with hCdef
  have hC0 : 0 ≤ C := norm_nonneg _
  set θ : ℝ := ε / (8 * ((m : ℝ) + 1) * (C + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  -- tightness at the times `ts l`
  have hM : ∀ l, ∃ (M : ℝ) (n₀ : ℕ), ∀ n, n₀ ≤ n →
      P n {ω | M < ‖X n (is l) (ts l) ω‖} ≤ ENNReal.ofReal θ := fun l =>
    hT (is l) (ts l) (hts l) θ hθ
  choose Ml nl hMl using hM
  set M : ℝ := ∑ l, |Ml l| with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun l _ => abs_nonneg _
  have hMl_le : ∀ l, Ml l ≤ M := fun l =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun l => |Ml l|)
      (fun l _ => abs_nonneg _) (Finset.mem_univ l))
  -- uniform continuity of `Ψ` on the ball of radius `M + 1`
  have hUC : UniformContinuousOn Ψ (Metric.closedBall 0 (M + 1)) :=
    (isCompact_closedBall (0 : Fin m → ℂ) (M + 1)).uniformContinuousOn_of_continuous
      Ψ.continuous.continuousOn
  obtain ⟨δ', hδ', hUC'⟩ := Metric.uniformContinuousOn_iff_le.1 hUC (ε / 2) (by positivity)
  set η : ℝ := min δ' 1 with hηdef
  have hη : 0 < η := lt_min hδ' one_pos
  -- the modulus on `[t₀, T]`
  set T : ℝ := t₀ + ∑ l, |ts l - t₀| + 1 with hTdef
  have hT₀ : t₀ < T := by
    have : 0 ≤ ∑ l, |ts l - t₀| := Finset.sum_nonneg fun l _ => abs_nonneg _
    linarith
  have htsT : ∀ l, ts l ≤ T := fun l => by
    have h1 : |ts l - t₀| ≤ ∑ l, |ts l - t₀| :=
      Finset.single_le_sum (f := fun l => |ts l - t₀|) (fun l _ => abs_nonneg _)
        (Finset.mem_univ l)
    have := le_abs_self (ts l - t₀)
    linarith
  have hD : ∀ l, ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      P n {ω | ∃ t ∈ Icc t₀ T, ∃ t' ∈ Icc t₀ T, |t - t'| ≤ δ ∧
        η < ‖X n (is l) t ω - X n (is l) t' ω‖} ≤ ENNReal.ofReal θ := fun l =>
    hC (is l) T hT₀ η θ hη hθ
  choose δl hδl nl' hδl' using hD
  have hj : ∀ᶠ j in atTop, ∀ l, (1 / 2 : ℝ) ^ j < δl l :=
    eventually_all.2 fun l => nsp_eventually_half_pow_lt (hδl l)
  filter_upwards [hj] with j hj
  have hn : ∀ᶠ n in atTop, ∀ l, nl l ≤ n ∧ nl' l ≤ n :=
    eventually_all.2 fun l => (eventually_ge_atTop _).and (eventually_ge_atTop _)
  filter_upwards [hn] with n hn
  -- the two vectors and the bad event
  set A : Ω n → Fin m → ℂ := fun ω l => X n (is l) (ts l) ω with hAdef
  set B : Ω n → Fin m → ℂ := fun ω l => X n (is l) (nspTime t₀ (nspIdx t₀ (ts l) j) j) ω
    with hBdef
  have hA : Measurable A := Measurable.of_eval fun l => hX n _ _
  have hB : Measurable B := Measurable.of_eval fun l => hX n _ _
  set Bad : Set (Ω n) := {ω | M < ‖A ω‖} ∪ {ω | η < ‖A ω - B ω‖} with hBaddef
  have hBad : MeasurableSet Bad :=
    (measurableSet_lt measurable_const hA.norm).union
      (measurableSet_lt measurable_const (hA.sub hB).norm)
  -- the bad event is small
  have hBadsub : Bad ⊆ ⋃ l, ({ω | Ml l < ‖X n (is l) (ts l) ω‖} ∪
      {ω | ∃ t ∈ Icc t₀ T, ∃ t' ∈ Icc t₀ T, |t - t'| ≤ δl l ∧
        η < ‖X n (is l) t ω - X n (is l) t' ω‖}) := by
    intro ω hω
    rcases hω with hω | hω
    · have : ¬ ‖A ω‖ ≤ M := not_le.2 hω
      rw [pi_norm_le_iff_of_nonneg hM0] at this
      simp only [not_forall, not_le] at this
      obtain ⟨l, hl⟩ := this
      exact mem_iUnion.2 ⟨l, Or.inl (lt_of_le_of_lt (hMl_le l) hl)⟩
    · have : ¬ ‖A ω - B ω‖ ≤ η := not_le.2 hω
      rw [pi_norm_le_iff_of_nonneg hη.le] at this
      simp only [not_forall, not_le] at this
      obtain ⟨l, hl⟩ := this
      refine mem_iUnion.2 ⟨l, Or.inr ⟨ts l, ⟨hts l, htsT l⟩, _,
        ⟨nsp_le_time t₀ _ _, (nsp_time_idx_le (hts l) j).trans (htsT l)⟩, ?_, hl⟩⟩
      have h1 := nsp_time_idx_le (hts l) j
      have h2 := nsp_sub_lt_time_idx t₀ (ts l) j
      rw [abs_le]; constructor <;> linarith [hj l]
  have hPBad : P n Bad ≤ ENNReal.ofReal (2 * m * θ) := by
    refine (measure_mono hBadsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
    have : ∀ l : Fin m, P n ({ω | Ml l < ‖X n (is l) (ts l) ω‖} ∪
        {ω | ∃ t ∈ Icc t₀ T, ∃ t' ∈ Icc t₀ T, |t - t'| ≤ δl l ∧
          η < ‖X n (is l) t ω - X n (is l) t' ω‖}) ≤ ENNReal.ofReal (2 * θ) := fun l => by
      refine (measure_union_le _ _).trans ?_
      rw [show 2 * θ = θ + θ by ring, ENNReal.ofReal_add hθ.le hθ.le]
      exact add_le_add (hMl l n (hn l).1) (hδl' l n (hn l).2)
    refine (Finset.sum_le_sum fun l _ => this l).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show 2 * (m : ℝ) * θ = (m : ℝ) * (2 * θ) by ring, ENNReal.ofReal_mul (Nat.cast_nonneg m),
      ENNReal.ofReal_natCast]
  have hPBad' : (P n).real Bad ≤ 2 * m * θ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hPBad
  -- pointwise bound
  have hpt : ∀ ω, |Ψ (A ω) - Ψ (B ω)| ≤ ε / 2 + 2 * C * Bad.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ Bad
    · rw [indicator_of_mem hω, Pi.one_apply, mul_one]
      have := Ψ.dist_le_two_norm (A ω) (B ω)
      rw [Real.dist_eq] at this
      linarith
    · rw [indicator_of_notMem hω, mul_zero, add_zero]
      simp only [hBaddef, mem_union, mem_ofPred_eq, not_or, not_lt] at hω
      have hAm : A ω ∈ Metric.closedBall (0 : Fin m → ℂ) (M + 1) := by
        rw [mem_closedBall_zero_iff]; linarith [hω.1]
      have hBm : B ω ∈ Metric.closedBall (0 : Fin m → ℂ) (M + 1) := by
        rw [mem_closedBall_zero_iff]
        have h1 := norm_sub_norm_le (B ω) (A ω)
        rw [norm_sub_rev] at h1
        linarith [hω.1, hω.2, min_le_right δ' 1]
      have := hUC' _ hAm _ hBm (by rw [dist_eq_norm]; exact hω.2.trans (min_le_left _ _))
      rwa [Real.dist_eq] at this
  -- integrate
  have hIA := nsp_integrable_bcf_comp (μ := P n) Ψ hA
  have hIB := nsp_integrable_bcf_comp (μ := P n) Ψ hB
  have hInd : Integrable (Bad.indicator (1 : Ω n → ℝ)) (P n) :=
    (integrable_const (1 : ℝ)).indicator hBad
  have hIR : Integrable (fun ω => ε / 2 + 2 * C * Bad.indicator 1 ω) (P n) :=
    (integrable_const _).add (hInd.const_mul _)
  rw [← integral_sub hIA hIB]
  refine (abs_integral_le_integral_abs).trans ?_
  refine (integral_mono (hIA.sub hIB).abs hIR hpt).trans ?_
  rw [integral_add (integrable_const _) (hInd.const_mul _),
    integral_const, integral_const_mul, integral_indicator_one hBad]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have key : 2 * C * (2 * m * θ) ≤ ε / 2 := by
    have e : 2 * C * (2 * m * θ) = ε / 2 * (C * m / (((m : ℝ) + 1) * (C + 1))) := by
      rw [hθdef]; field_simp; ring
    rw [e]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [div_le_one (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  nlinarith [mul_le_mul_of_nonneg_left hPBad' (by positivity : (0 : ℝ) ≤ 2 * C)]

/-- Grid fdd convergence along the Prokhorov subsequence. -/
theorem nsp_grid_fdd [Countable ι] {t₀ : ℝ} {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {X : ∀ n, ι → ℝ → Ω n → ℂ}
    (hX : ∀ n i t, Measurable (X n i t)) {φ : ℕ → ℕ} {ν : ProbabilityMeasure (ι × ℕ × ℕ → ℂ)}
    (hν : Tendsto (fun n => nspGridLaw t₀ P X (φ n)) atTop (𝓝 ν)) {m : ℕ} (c : Fin m → ι × ℕ × ℕ)
    (Ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ) :
    Tendsto (fun n => ∫ ω, Ψ (fun l => X (φ n) (c l).1 (nspTime t₀ (c l).2.1 (c l).2.2) ω)
      ∂P (φ n)) atTop (𝓝 (∫ x, Ψ (fun l => x (c l)) ∂(ν : Measure (ι × ℕ × ℕ → ℂ)))) := by
  let g : BoundedContinuousFunction (ι × ℕ × ℕ → ℂ) ℝ :=
    Ψ.compContinuous ⟨fun x l => x (c l), by fun_prop⟩
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν g
  refine h.congr fun n => ?_
  change ∫ x, g x ∂((P (φ n)).map (nspGrid t₀ X (φ n))) = _
  rw [integral_map (nsp_measurable_grid t₀ hX (φ n)).aemeasurable
    g.continuous.aestronglyMeasurable]
  rfl

/-- Limit side: the grid values along the dyadic lower approximations converge in the test
integrals to the canonical process. -/
theorem nsp_limit_grid_tendsto [Countable ι] {t₀ : ℝ} {ν : Measure (ι × ℕ × ℕ → ℂ)}
    [IsProbabilityMeasure ν] (hgood : ∀ᵐ x ∂ν, ∀ i, NspGridGood t₀ fun p => x (i, p))
    {m : ℕ} (is : Fin m → ι) (ts : Fin m → ℝ) (hts : ∀ l, t₀ ≤ ts l)
    (Ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ) :
    Tendsto (fun j => ∫ x, Ψ (fun l => x (is l, nspIdx t₀ (ts l) j, j)) ∂ν) atTop
      (𝓝 (∫ x, Ψ (fun l => nspZ t₀ (is l) (ts l) x) ∂ν)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖Ψ‖) (fun j => ?_)
    (integrable_const _) (fun j => ae_of_all _ fun x => Ψ.norm_coe_le_norm _) ?_
  · exact (Ψ.continuous.measurable.comp
      (Measurable.of_eval fun l => measurable_pi_apply _)).aestronglyMeasurable
  · filter_upwards [hgood] with x hx
    exact (Ψ.continuous.tendsto _).comp
      (tendsto_pi_nhds.2 fun l => nsp_tendsto_nspZ (hx (is l)) (hts l))

/-- **Continuous-path realization with fdd convergence at all real times `≥ t₀`** (pure
probability; the Prokhorov realization). -/
theorem nsp_realization [Countable ι] {t₀ : ℝ} {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {X : ∀ n, ι → ℝ → Ω n → ℂ}
    (hX : ∀ n i t, Measurable (X n i t)) (hT : NspTightAt t₀ P X) (hC : NspModulus t₀ P X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : Measure (ι × ℕ × ℕ → ℂ), IsProbabilityMeasure ν ∧
      (∀ (i : ι) (t : ℝ), Measurable (nspZ t₀ i t)) ∧
      (∀ i : ι, ∀ᵐ x ∂ν, ContinuousOn (fun t => nspZ t₀ i t x) (Ici t₀)) ∧
      ∀ (m : ℕ) (is : Fin m → ι) (ts : Fin m → ℝ), (∀ l, t₀ ≤ ts l) →
        ∀ Ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ,
          Tendsto (fun n => ∫ ω, Ψ (fun l => X (φ n) (is l) (ts l) ω) ∂P (φ n)) atTop
            (𝓝 (∫ x, Ψ (fun l => nspZ t₀ (is l) (ts l) x) ∂ν)) := by
  obtain ⟨φ, hφ, ν, hν⟩ := nsp_exists_tendsto_gridLaw hX hT
  have hgood := nsp_ae_gridGood hX hC hφ hν
  refine ⟨φ, hφ, ν, inferInstance, nsp_measurable_nspZ t₀, fun i => ?_, ?_⟩
  · filter_upwards [hgood] with x hx
    exact nsp_continuousOn_nspZ (hx i)
  intro m is ts hts Ψ
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 4 := by positivity
  have h1 := nsp_finite_grid_close hX hT hC is ts hts Ψ hε3
  have h2 := (Metric.tendsto_nhds.1 (nsp_limit_grid_tendsto hgood is ts hts Ψ)) _ hε3
  obtain ⟨j, hj1, hj2⟩ := (h1.and h2).exists
  have h3 := (Metric.tendsto_nhds.1 (nsp_grid_fdd hX hν
    (fun l => (is l, nspIdx t₀ (ts l) j, j)) Ψ)) _ hε3
  filter_upwards [hφ.tendsto_atTop.eventually hj1, h3] with n hn1 hn3
  rw [Real.dist_eq] at hj2 hn3 ⊢
  have e := abs_sub_lt_iff.1 hj2
  have e3 := abs_sub_lt_iff.1 hn3
  have e1 := abs_le.1 hn1
  rw [abs_lt]; constructor <;> linarith [e.1, e.2, e3.1, e3.2, e1.1, e1.2]

end BlockBand.Endpoints
