module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegCompY
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The regularized Euler scheme approximates the degenerate stopped solution

See `DegCompY` for the setting.

**`lintegral_degX_stop_sub_le`**: for `t ≤ N`,
`E |X^{m,n}_{t∧τ} - Y_{t∧τ}|² ≤ gronCI(N, degLip c) (N δ_c 2^{-m} + degErr S n N)`.
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

/-- **The regularized Euler scheme approximates the stopped solution.** -/
theorem lintegral_degX_stop_sub_le (S : DegSetup c W P) (m n N : ℕ) :
    ∀ t ≤ (N : ℝ≥0), ∫⁻ ω, ∑ i, ‖eulX c m S.ξ (S.Bd n) (stopTime (S.τ ω) t) ω i -
      S.Y (stopTime (S.τ ω) t) ω i‖ₑ ^ 2 ∂P ≤
        ENNReal.ofReal (gronCI N (degLip c)) *
          (ENNReal.ofReal (N * (eulDelta c / 2 ^ m)) + degErr S n N) := by
  classical
  have := S.hZ.isFiniteMeasure_bar (N : ℝ≥0)
  set B := S.Bd n
  have hBm := S.measW n
  have hBm' : ∀ t, Measurable (B t) := fun t => (hBm t).mono (S.𝓕.le t) le_rfl
  obtain ⟨A, hA, hAP, hAc⟩ := exists_good_set (S.hBd n).continuous
  obtain ⟨A', hA', hAP', hAc'⟩ := exists_good_set S.hYc
  have hE : ∀ j, Measurable (eulE c m S.ξ B j) := fun j =>
    (measurable_eulE c m hBm S.hξ j).mono (S.𝓕.le _) le_rfl
  have hτm : Measurable S.τ := S.hτ.measurable'
  set Yv := jointVersion S.Y A'
  have hYv : Measurable Yv := measurable_jointVersion S.hYm hA' hAc'
  have hS := measurableSet_stopSet S.𝓕 S.hτ
  have hSm : MeasurableSet (stopSet S.τ) := predictableSpace_le _ _ hS
  set J := N * 2 ^ m
  have hn : gridT m J = N := gridT_mul_pow m N
  have hεn := regSeq_pos n
  set β : Fin d → ℝ × Ω → ℝ := fun i p => (stopSet S.τ).indicator (eulDrift c m S.ξ B J i) p -
    (stopSet S.τ).indicator (fun q => c.b (Yv q) i) p
  have hβ : ∀ i, Measurable (β i) := fun i =>
    ((measurable_eulDrift c m hBm S.hξ J i).indicator hSm).sub
      ((((measurable_pi_apply i).comp c.continuous_b.measurable).comp hYv).indicator hSm)
  have hβb : ∀ i p, |β i p| ≤ 2 * c.M := fun i p => by
    have a1 : |(stopSet S.τ).indicator (eulDrift c m S.ξ B J i) p| ≤ c.M := by
      rw [indicator_apply]; split_ifs
      · exact abs_eulDrift_le c m J i p
      · simp [c.M_nonneg]
    have a2 : |(stopSet S.τ).indicator (fun q => c.b (Yv q) i) p| ≤ c.M := by
      rw [indicator_apply]; split_ifs
      · exact c.bd_b _ _
      · simp [c.M_nonneg]
    exact (abs_sub _ _).trans (by linarith)
  have hK := fun i k => (isBddPred_eulDiff c m hBm S.hξ J i k).indicator hS
  have hX := fun i c' => S.zBdd n (hK i) c'
  have hU := fun (i : Fin d) (c' : Fin d ⊕ Fin (d + d)) =>
    isBddPred_unitStop S.hτ (Sum.inl i) c'
  have hf := fun i c' => isBddPred_sub (hX i c') (hU i c')
  set f : Fin d → Fin d ⊕ Fin (d + d) → ℝ × Ω → ℝ := fun i c' p =>
    (∑ k, S.H n k c' p * (stopSet S.τ).indicator (eulDiff c m S.ξ B J i k) p) -
      (if c' = Sum.inl i then (stopSet S.τ).indicator (fun _ => (1 : ℝ)) p else 0)
  set Mt : Fin d → ℝ≥0 → Ω → ℝ := fun i t =>
    S.hZ.vecCont (N : ℝ≥0) (fun c' => bpL2 _ (hf i c')) t
  have hMm : ∀ i t, AEMeasurable (Mt i t) P := fun i t =>
    ((S.hZ.vecCont_spec (N : ℝ≥0) _).2.1 t).aestronglyMeasurable.aemeasurable
  set q : Fin d → ℝ × Ω → ℝ≥0∞ := fun i p =>
    ENNReal.ofReal (∑ c₁, ∑ c₂, f i c₁ p * f i c₂ p * S.aZ c₁ c₂ p.1.toNNReal p.2)
  have hfm : ∀ i c', Measurable (f i c') := fun i c' =>
    ((hf i c').sm.mono (predictableSpace_le _)).measurable
  have hq : ∀ i, Measurable (q i) := fun i =>
    (Finset.measurable_sum _ fun c₁ _ => Finset.measurable_sum _ fun c₂ _ =>
      ((hfm i c₁).mul (hfm i c₂)).mul (S.hZ.measurable c₁ c₂)).ennreal_ofReal
  set D' : ℝ × Ω → Fin d → ℝ := fun p =>
    eulXv c m S.ξ B A (stopR S.τ p, p.2) - Yv (stopR S.τ p, p.2)
  have hD' : Measurable D' :=
    ((measurable_eulXv c m hBm' hE hA hAc).comp (measurable_stopR hτm)).sub
      (hYv.comp (measurable_stopR hτm))
  have hAA : ∀ᵐ ω ∂P, ω ∈ A ∧ ω ∈ A' := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hAP,
      measure_eq_zero_iff_ae_notMem.1 hAP'] with ω h1 h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  have hDD : ∀ s : ℝ≥0, s ≤ (N : ℝ≥0) → ∀ᵐ ω ∂P,
      (fun i => eulX c m S.ξ B (stopTime (S.τ ω) s) ω i - S.Y (stopTime (S.τ ω) s) ω i) =
        D' ((s : ℝ), ω) := by
    intro s _
    filter_upwards [hAA] with ω hω
    simp only [D', eulXv_of_mem c m hω.1, jointVersion_of_mem hω.2, stopR, Real.toNNReal_coe,
      Yv]
    rfl
  set err : ℝ × Ω → ℝ≥0∞ := (stopSet S.τ).indicator fun p => ENNReal.ofReal
    (2 * d ^ 2 * c.M ^ 2 * frob (fun k c' => tikX (c.σ (Yv p)) (regSeq n) k c' +
      -pinvX (c.σ (Yv p)) k c'))
  have herr : Measurable err := Measurable.indicator (((measurable_tikXerr_comp
    (fun i j => sigma_entry_measurable c hYv i j) hεn).const_mul _).ennreal_ofReal) hSm
  set ε : ℝ × Ω → ℝ≥0∞ := fun p => eulEps c m S.ξ B A p + err p
  have hε : Measurable ε := (measurable_eulEps c m hBm' hE hA hAc).add herr
  -- the pointwise identification at good points
  have hpt : ∀ᵐ ω ∂P, ∀ r ∈ Ioc (0 : ℝ) N,
      ((r, ω) ∈ stopSet S.τ → (∀ i, β i (r, ω) =
          c.b (eulE c m S.ξ B (gridIdx m r.toNNReal) ω) i - c.b (Yv (r, ω)) i) ∧
        ∀ i, q i (r, ω) = ENNReal.ofReal (∑ c₁, ∑ c₂,
          gY (c.σ (Yv (r, ω))) (c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω)) (regSeq n) i c₁ *
          gY (c.σ (Yv (r, ω))) (c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω)) (regSeq n) i c₂ *
            zDens (c.σ (Yv (r, ω))) c₁ c₂)) ∧
      ((r, ω) ∉ stopSet S.τ → (∀ i, β i (r, ω) = 0) ∧ ∀ i, q i (r, ω) = 0) := by
    filter_upwards [hAA, S.haZ, S.hHv] with ω hω haZ hHv r hr
    have hrn : r ≤ gridT m J := by rw [hn]; exact hr.2
    have hY : Yv (r, ω) = S.Y r.toNNReal ω := jointVersion_of_mem hω.2 r
    refine ⟨fun hS' => ⟨fun i => ?_, fun i => ?_⟩, fun hS' => ⟨fun i => ?_, fun i => ?_⟩⟩
    · simp only [β, indicator_of_mem hS', eulDrift_eq c m hr.1 hrn]
    · simp only [q]
      congr 1
      refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
      have hfv : ∀ c', f i c' (r, ω) = gY (c.σ (Yv (r, ω)))
          (c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω)) (regSeq n) i c' := fun c' => by
        simp only [f, gY, indicator_of_mem hS', eulDiff_eq c m hr.1 hrn, hHv r hr.1, ite_eq_left hS',
          hY]
        congr 1
        · exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [hfv, hfv, haZ r hr.1, ite_eq_left hS', hY]
    · simp only [β, indicator_of_notMem hS', sub_self]
    · have hf0 : ∀ c', f i c' (r, ω) = 0 := fun c' => by
        simp [f, indicator_of_notMem hS']
      simp only [q, hf0, zero_mul, Finset.sum_const_zero, ENNReal.ofReal_zero]
  set Cq : ℝ≥0∞ := ENNReal.ofReal (2 * (d ^ 2 * (2 * c.M) ^ 2) + 2 * (d ^ 2 * c.M ^ 2 * (4 * d)))
  have hsumq : ∀ (s Γ : Matrix (Fin d) (Fin d) ℝ), (∀ i, 0 ≤ ∑ c₁, ∑ c₂,
      gY s Γ (regSeq n) i c₁ * gY s Γ (regSeq n) i c₂ * zDens s c₁ c₂) →
      (∑ i, ENNReal.ofReal (∑ c₁, ∑ c₂, gY s Γ (regSeq n) i c₁ * gY s Γ (regSeq n) i c₂ *
        zDens s c₁ c₂)) = ENNReal.ofReal (∑ i, ∑ c₁, ∑ c₂, gY s Γ (regSeq n) i c₁ *
          gY s Γ (regSeq n) i c₂ * zDens s c₁ c₂) := fun s Γ h =>
    (ENNReal.ofReal_sum_of_nonneg fun i _ => h i).symm
  refine lintegral_sq_le_gronwall_abs (D := fun s ω i =>
    eulX c m S.ξ B (stopTime (S.τ ω) s) ω i - S.Y (stopTime (S.τ ω) s) ω i)
    hD' hDD hβ hβb hMm hq (Cq := Cq) ENNReal.ofReal_ne_top ?_ ?_ ?_ hε
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, degErr_ne_top S n N⟩) ?_ ?_
  · -- a priori bound on `q`
    filter_upwards [hpt] with ω hω r hr i
    by_cases hS' : (r, ω) ∈ stopSet S.τ
    · rw [((hω r hr).1 hS').2 i]
      set s := c.σ (Yv (r, ω))
      set Γ := c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω)
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := Finset.single_le_sum (f := fun i => ∑ c₁, ∑ c₂, gY s Γ (regSeq n) i c₁ *
        gY s Γ (regSeq n) i c₂ * zDens s c₁ c₂) (fun i _ => quad_nonneg_zDens s _)
        (Finset.mem_univ i)
      have h2 := quad_sum_vsY_le s Γ hεn
      have h3 := sq2_sub_le c (eulE c m S.ξ B (gridIdx m r.toNNReal) ω) (Yv (r, ω))
      have h4 := sq2_sigma_le c (Yv (r, ω))
      have h5 := frob_tikX_sub_pinvX_le s hεn
      have h6 := frob_nonneg (fun k c' => tikX s (regSeq n) k c' + -pinvX s k c')
      have h7 : sq2 s * frob (fun k c' => tikX s (regSeq n) k c' + -pinvX s k c') ≤
          d ^ 2 * c.M ^ 2 * (4 * d) :=
        mul_le_mul h4 h5 h6 (by positivity)
      exact h1.trans (h2.trans (by linarith))
    · rw [((hω r hr).2 hS').2 i]; exact zero_le
  · -- the isometry
    intro t ht i
    exact (lintegral_sq_vecCont_gen S.hZ S.hZs (hf i) ht).le
  · -- the representation
    intro t ht i
    have e : (fun c' => bpL2 (barMeasure P S.aZ N) (hf i c')) =
        (fun c' => bpL2 (barMeasure P S.aZ N) (hX i c')) -
          fun c' => bpL2 (barMeasure P S.aZ N) (hU i c') :=
      funext fun c' => bpL2_sub' (hX i c') (hU i c')
    filter_upwards [S.eulZ_rep_stop m n N, S.hrep N, hAA,
      vecCont_sub_ae S.hZ (N : ℝ≥0) (fun c' => bpL2 (barMeasure P S.aZ N) (hX i c'))
        (fun c' => bpL2 (barMeasure P S.aZ N) (hU i c')) t] with ω e1 e2 hω e3
    simp only [Mt]
    rw [e1 t ht i, e2 t ht i, e, e3]
    have hi1 : IntegrableOn (fun r => (stopSet S.τ).indicator (eulDrift c m S.ξ B J i) (r, ω))
        (Ioc (0 : ℝ) t) :=
      Measure.integrableOn_of_bounded (M := c.M) (by simp)
        (((measurable_eulDrift c m hBm S.hξ J i).indicator hSm).comp (measurable_id.prodMk
          measurable_const)).aestronglyMeasurable
        (Eventually.of_forall fun r => by
          rw [Real.norm_eq_abs, indicator_apply]; split_ifs
          · exact abs_eulDrift_le c m J i _
          · simp [c.M_nonneg])
    have hi2 : IntegrableOn (fun r => (stopSet S.τ).indicator (fun q => c.b (Yv q) i) (r, ω))
        (Ioc (0 : ℝ) t) :=
      Measure.integrableOn_of_bounded (M := c.M) (by simp)
        (((((measurable_pi_apply i).comp c.continuous_b.measurable).comp hYv).indicator
          hSm).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (Eventually.of_forall fun r => by
          rw [Real.norm_eq_abs, indicator_apply]; split_ifs
          · exact c.bd_b _ _
          · simp [c.M_nonneg])
    have e4 : ∫ r in Ioc (0 : ℝ) t, (stopSet S.τ).indicator
        (fun p => c.b (S.Y p.1.toNNReal p.2) i) (r, ω) =
        ∫ r in Ioc (0 : ℝ) t, (stopSet S.τ).indicator (fun q => c.b (Yv q) i) (r, ω) := by
      congr 1
      funext r
      by_cases hr : (r, ω) ∈ stopSet S.τ
      · rw [indicator_of_mem hr, indicator_of_mem hr]
        exact congrArg (fun y => c.b y i) (jointVersion_of_mem hω.2 r).symm
      · rw [indicator_of_notMem hr, indicator_of_notMem hr]
    simp only [β]
    rw [e4, integral_sub hi1 hi2]
    ring
  · -- the integrated error
    have hm1 : Measurable fun p : ℝ × Ω => eulEps c m S.ξ B A p :=
      measurable_eulEps c m hBm' hE hA hAc
    calc ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, ε (r, ω)) ∂P
        = ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, eulEps c m S.ξ B A (r, ω)) ∂P +
            ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, err (r, ω)) ∂P := by
          rw [← lintegral_add_left' hm1.lintegral_prod_left'.aemeasurable]
          refine lintegral_congr fun ω => ?_
          have hr1 : Measurable fun r => eulEps c m S.ξ B A (r, ω) :=
            hm1.comp (measurable_id.prodMk measurable_const)
          rw [← lintegral_add_left' hr1.aemeasurable]
      _ ≤ ENNReal.ofReal (N * (eulDelta c / 2 ^ m)) + degErr S n N := by
          gcongr
          · rw [lintegral_lintegral_swap (f := fun ω r => eulEps c m S.ξ B A (r, ω))
              (hm1.comp measurable_swap).aemeasurable]
            calc ∫⁻ r in Ioc (0 : ℝ) N, (∫⁻ ω, eulEps c m S.ξ B A (r, ω) ∂P)
                ≤ ∫⁻ _r in Ioc (0 : ℝ) N, ENNReal.ofReal (eulDelta c / 2 ^ m) :=
                  setLIntegral_mono' measurableSet_Ioc fun r hr =>
                    lintegral_eulEps_le (S.hBd n) c m hAP hr.1.le
              _ = ENNReal.ofReal (N * (eulDelta c / 2 ^ m)) := by
                  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
                    Real.volume_Ioc, sub_zero, mul_comm, ← ENNReal.ofReal_mul
                    (by have := eulDelta_nonneg c; positivity)]
          · refine le_of_eq (lintegral_congr_ae ?_)
            filter_upwards [hAA] with ω hω
            refine lintegral_congr fun r => ?_
            by_cases h : (r, ω) ∈ stopSet S.τ
            · simp only [err, indicator_of_mem h, Yv, jointVersion_of_mem hω.2]
            · simp only [err, indicator_of_notMem h]
  · -- the pointwise bound
    filter_upwards [hpt, hAA] with ω hω hAω r hr
    by_cases hS' : (r, ω) ∈ stopSet S.τ
    · obtain ⟨eb, eq⟩ := (hω r hr).1 hS'
      unfold coefSqA
      simp only [eb, eq]
      rw [hsumq _ _ fun i => quad_nonneg_zDens _ _]
      have hD'r : D' (r, ω) = eulXv c m S.ξ B A (r, ω) - Yv (r, ω) := by
        simp only [D', stopR_of_mem hr.1 hS']
      have hb := coefSq_vsY c (eulE c m S.ξ B (gridIdx m r.toNNReal) ω) (Yv (r, ω))
        (eulXv c m S.ξ B A (r, ω)) hεn
      simp only [ε, err, indicator_of_mem hS', hD'r]
      refine hb.trans (le_of_eq ?_)
      unfold eulEps
      ring
    · obtain ⟨eb, eq⟩ := (hω r hr).2 hS'
      unfold coefSqA
      simp only [eb, eq, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, add_zero]
      exact zero_le

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
