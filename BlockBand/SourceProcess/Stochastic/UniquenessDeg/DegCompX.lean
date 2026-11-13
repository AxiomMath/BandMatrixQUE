module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegCompY
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Two regularized Euler schemes are close

**`lintegral_degX_sub_le`**: for `t ≤ N`, the Euler schemes of grids `m, m'` driven by
`Bd n, Bd n'` satisfy `E |X^{m,n}_t - X^{m',n'}_t|² ≤ gronCI(N, degLip c) ·
(N δ_c 2^{-m} + N δ_c 2^{-m'} + 2 degErr S n N + 2 degErr S n' N)`
(`lintegral_sq_le_gronwall_abs` against the joint integrator, pointwise bounds `coefSq_vsX`
inside and `coefSq_off` outside the stochastic interval).
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

theorem frob_tikX_tikX_le (s : Matrix (Fin d) (Fin d) ℝ) {ε ε' : ℝ} (hε : 0 < ε)
    (hε' : 0 < ε') : frob (fun k c' => tikX s ε k c' + -tikX s ε' k c') ≤ 4 * d := by
  refine (frob_add_le _ _).trans ?_
  rw [frob_neg, frob_orth_eq (tikX_orth s hε), frob_orth_eq (tikX_orth s hε')]
  ring_nf; rfl

/-- The mutual regularization error of levels `n, n'` up to the horizon `N`. -/
def degErrX (S : DegSetup c W P) (n n' N : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, (stopSet S.τ).indicator (fun p => ENNReal.ofReal
    (2 * d ^ 2 * c.M ^ 2 * frob (fun k c' => tikX (c.σ (S.Y p.1.toNNReal p.2)) (regSeq n) k c' +
      -tikX (c.σ (S.Y p.1.toNNReal p.2)) (regSeq n') k c'))) (r, ω)) ∂P

theorem degErrX_ne_top (S : DegSetup c W P) (n n' N : ℕ) : degErrX S n n' N ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _ω, (∫⁻ _r in Ioc (0 : ℝ) N,
    ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 * (4 * d))) ∂P) ?_ (lintegral_mono fun ω =>
      lintegral_mono fun r => ?_)
  · simp [lintegral_const, ENNReal.mul_eq_top]
  · classical
    rw [indicator_apply]
    split_ifs
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (frob_tikX_tikX_le _ (regSeq_pos n) (regSeq_pos n')) (by positivity))
    · exact zero_le

omit [IsProbabilityMeasure P] in
theorem lintegral_lintegral_add {g₁ g₂ : ℝ × Ω → ℝ≥0∞} (h₁ : Measurable g₁) (s : Set ℝ) :
    ∫⁻ ω, (∫⁻ r in s, (g₁ (r, ω) + g₂ (r, ω))) ∂P =
      ∫⁻ ω, (∫⁻ r in s, g₁ (r, ω)) ∂P + ∫⁻ ω, (∫⁻ r in s, g₂ (r, ω)) ∂P := by
  rw [← lintegral_add_left' h₁.lintegral_prod_left'.aemeasurable]
  refine lintegral_congr fun ω => ?_
  have hr1 : Measurable fun r => g₁ (r, ω) := h₁.comp (measurable_id.prodMk measurable_const)
  rw [← lintegral_add_left' hr1.aemeasurable]

theorem lintegral_eulEps_Ioc_le (S : DegSetup c W P) (m n N : ℕ) {A : Set Ω} (hAP : P Aᶜ = 0)
    (hm : Measurable (eulEps c m S.ξ (S.Bd n) A)) :
    ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, eulEps c m S.ξ (S.Bd n) A (r, ω)) ∂P ≤
      ENNReal.ofReal (N * (eulDelta c / 2 ^ m)) := by
  rw [lintegral_lintegral_swap (f := fun ω r => eulEps c m S.ξ (S.Bd n) A (r, ω))
    (hm.comp measurable_swap).aemeasurable]
  calc ∫⁻ r in Ioc (0 : ℝ) N, (∫⁻ ω, eulEps c m S.ξ (S.Bd n) A (r, ω) ∂P)
      ≤ ∫⁻ _r in Ioc (0 : ℝ) N, ENNReal.ofReal (eulDelta c / 2 ^ m) :=
        setLIntegral_mono' measurableSet_Ioc fun r hr =>
          lintegral_eulEps_le (S.hBd n) c m hAP hr.1.le
    _ = ENNReal.ofReal (N * (eulDelta c / 2 ^ m)) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
          Real.volume_Ioc, sub_zero, mul_comm, ← ENNReal.ofReal_mul
          (by have := eulDelta_nonneg c; positivity)]

/-- **Two regularized Euler schemes are close.** -/
theorem lintegral_degX_sub_le (S : DegSetup c W P) (m m' n n' N : ℕ) :
    ∀ t ≤ (N : ℝ≥0), ∫⁻ ω, ∑ i, ‖eulX c m S.ξ (S.Bd n) t ω i -
      eulX c m' S.ξ (S.Bd n') t ω i‖ₑ ^ 2 ∂P ≤
        ENNReal.ofReal (gronCI N (degLip c)) *
          ((ENNReal.ofReal (N * (eulDelta c / 2 ^ m)) +
            ENNReal.ofReal (N * (eulDelta c / 2 ^ m'))) + degErrX S n n' N) := by
  classical
  have := S.hZ.isFiniteMeasure_bar (N : ℝ≥0)
  set B := S.Bd n
  set B' := S.Bd n'
  have hBm := S.measW n
  have hBm2 := S.measW n'
  have hBm' : ∀ t, Measurable (B t) := fun t => (hBm t).mono (S.𝓕.le t) le_rfl
  have hBm2' : ∀ t, Measurable (B' t) := fun t => (hBm2 t).mono (S.𝓕.le t) le_rfl
  obtain ⟨A, hA, hAP, hAc⟩ := exists_good_set (S.hBd n).continuous
  obtain ⟨A2, hA2, hAP2, hAc2⟩ := exists_good_set (S.hBd n').continuous
  obtain ⟨A', hA', hAP', hAc'⟩ := exists_good_set S.hYc
  have hE : ∀ j, Measurable (eulE c m S.ξ B j) := fun j =>
    (measurable_eulE c m hBm S.hξ j).mono (S.𝓕.le _) le_rfl
  have hE2 : ∀ j, Measurable (eulE c m' S.ξ B' j) := fun j =>
    (measurable_eulE c m' hBm2 S.hξ j).mono (S.𝓕.le _) le_rfl
  set Yv := jointVersion S.Y A'
  have hYv : Measurable Yv := measurable_jointVersion S.hYm hA' hAc'
  have hS := measurableSet_stopSet S.𝓕 S.hτ
  have hSm : MeasurableSet (stopSet S.τ) := predictableSpace_le _ _ hS
  set J := N * 2 ^ m
  set J' := N * 2 ^ m'
  have hn : gridT m J = N := gridT_mul_pow m N
  have hn' : gridT m' J' = N := gridT_mul_pow m' N
  have hεn := regSeq_pos n
  have hεn' := regSeq_pos n'
  set β : Fin d → ℝ × Ω → ℝ := fun i p => eulDrift c m S.ξ B J i p - eulDrift c m' S.ξ B' J' i p
  have hβ : ∀ i, Measurable (β i) := fun i =>
    (measurable_eulDrift c m hBm S.hξ J i).sub (measurable_eulDrift c m' hBm2 S.hξ J' i)
  have hβb : ∀ i p, |β i p| ≤ 2 * c.M := fun i p => by
    have h1 := abs_eulDrift_le (ξ := S.ξ) (B := B) c m J i p
    have h2 := abs_eulDrift_le (ξ := S.ξ) (B := B') c m' J' i p
    exact (abs_sub _ _).trans (by linarith)
  have hX := fun i c' => S.zBdd n (fun k => isBddPred_eulDiff c m hBm S.hξ J i k) c'
  have hX' := fun i c' => S.zBdd n' (fun k => isBddPred_eulDiff c m' hBm2 S.hξ J' i k) c'
  have hf := fun i c' => isBddPred_sub (hX i c') (hX' i c')
  set f : Fin d → Fin d ⊕ Fin (d + d) → ℝ × Ω → ℝ := fun i c' p =>
    (∑ k, S.H n k c' p * eulDiff c m S.ξ B J i k p) -
      ∑ k, S.H n' k c' p * eulDiff c m' S.ξ B' J' i k p
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
  set D' : ℝ × Ω → Fin d → ℝ := fun p => eulXv c m S.ξ B A p - eulXv c m' S.ξ B' A2 p
  have hD' : Measurable D' :=
    (measurable_eulXv c m hBm' hE hA hAc).sub (measurable_eulXv c m' hBm2' hE2 hA2 hAc2)
  have hAA : ∀ᵐ ω ∂P, ω ∈ A ∧ ω ∈ A2 ∧ ω ∈ A' := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hAP,
      measure_eq_zero_iff_ae_notMem.1 hAP2, measure_eq_zero_iff_ae_notMem.1 hAP'] with ω h1 h2 h3
    exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
  have hDD : ∀ s : ℝ≥0, s ≤ (N : ℝ≥0) → ∀ᵐ ω ∂P,
      (fun i => eulX c m S.ξ B s ω i - eulX c m' S.ξ B' s ω i) = D' ((s : ℝ), ω) := by
    intro s _
    filter_upwards [hAA] with ω hω
    simp only [D', eulXv_of_mem c m hω.1, eulXv_of_mem c m' hω.2.1, Real.toNNReal_coe]
    rfl
  set err : ℝ × Ω → ℝ≥0∞ := (stopSet S.τ).indicator fun p => ENNReal.ofReal
    (2 * d ^ 2 * c.M ^ 2 * frob (fun k c' => tikX (c.σ (Yv p)) (regSeq n) k c' +
      -tikX (c.σ (Yv p)) (regSeq n') k c'))
  have hσv : ∀ k l, Measurable fun p => c.σ (Yv p) k l := sigma_entry_measurable c hYv
  have herr : Measurable err := by
    refine Measurable.indicator (Measurable.ennreal_ofReal (Measurable.const_mul ?_ _)) hSm
    exact Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun c' _ =>
      ((((continuous_tikX hεn k c').measurable.comp (measurable_pi_iff.2 fun i =>
        measurable_pi_iff.2 fun j => hσv i j))).add (((continuous_tikX hεn' k c').measurable.comp
          (measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hσv i j))).neg).pow_const 2
  set ε : ℝ × Ω → ℝ≥0∞ := fun p =>
    eulEps c m S.ξ B A p + eulEps c m' S.ξ B' A2 p + err p
  have hm1 := measurable_eulEps c m hBm' hE hA hAc
  have hm2 := measurable_eulEps c m' hBm2' hE2 hA2 hAc2
  have hε : Measurable ε := (hm1.add hm2).add herr
  have hpt : ∀ᵐ ω ∂P, ∀ r ∈ Ioc (0 : ℝ) N,
      (∀ i, β i (r, ω) = c.b (eulE c m S.ξ B (gridIdx m r.toNNReal) ω) i -
          c.b (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω) i) ∧
      ((r, ω) ∈ stopSet S.τ → ∀ i, q i (r, ω) = ENNReal.ofReal (∑ c₁, ∑ c₂,
          gX (c.σ (Yv (r, ω))) (c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω))
            (c.σ (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω)) (regSeq n) (regSeq n') i c₁ *
          gX (c.σ (Yv (r, ω))) (c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω))
            (c.σ (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω)) (regSeq n) (regSeq n') i c₂ *
            zDens (c.σ (Yv (r, ω))) c₁ c₂)) ∧
      ((r, ω) ∉ stopSet S.τ → ∀ i, q i (r, ω) = ENNReal.ofReal (∑ c₁, ∑ c₂,
          (∑ k, c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω) i k * offval k c₁ -
            ∑ k, c.σ (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω) i k * offval k c₁) *
          (∑ k, c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω) i k * offval k c₂ -
            ∑ k, c.σ (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω) i k * offval k c₂) *
            zDens 0 c₁ c₂)) := by
    filter_upwards [hAA, S.haZ, S.hHv] with ω hω haZ hHv r hr
    have hrn : r ≤ gridT m J := by rw [hn]; exact hr.2
    have hrn' : r ≤ gridT m' J' := by rw [hn']; exact hr.2
    have hY : Yv (r, ω) = S.Y r.toNNReal ω := jointVersion_of_mem hω.2.2 r
    refine ⟨fun i => ?_, fun hS' i => ?_, fun hS' i => ?_⟩
    · simp only [β, eulDrift_eq c m hr.1 hrn, eulDrift_eq c m' hr.1 hrn']
    · simp only [q]
      congr 1
      refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
      have hfv : ∀ c', f i c' (r, ω) = gX (c.σ (Yv (r, ω)))
          (c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω))
          (c.σ (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω)) (regSeq n) (regSeq n') i c' :=
        fun c' => by
          simp only [f, gX, eulDiff_eq c m hr.1 hrn, eulDiff_eq c m' hr.1 hrn', hHv r hr.1,
            ite_eq_left hS', hY]
          congr 1 <;> exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [hfv, hfv, haZ r hr.1, ite_eq_left hS', hY]
    · simp only [q]
      congr 1
      refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
      have hfv : ∀ c', f i c' (r, ω) =
          ∑ k, c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω) i k * offval k c' -
            ∑ k, c.σ (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω) i k * offval k c' :=
        fun c' => by
          simp only [f, eulDiff_eq c m hr.1 hrn, eulDiff_eq c m' hr.1 hrn', hHv r hr.1,
            ite_eq_right hS']
          congr 1 <;> exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [hfv, hfv, haZ r hr.1, ite_eq_right hS']
  set Cq : ℝ≥0∞ := ENNReal.ofReal (2 * (d ^ 2 * (2 * c.M) ^ 2) + 2 * (d ^ 2 * c.M ^ 2 * (4 * d)))
  refine lintegral_sq_le_gronwall_abs (D := fun s ω i =>
    eulX c m S.ξ B s ω i - eulX c m' S.ξ B' s ω i)
    hD' hDD hβ hβb hMm hq (Cq := Cq) ENNReal.ofReal_ne_top ?_ ?_ ?_ hε
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
      degErrX_ne_top S n n' N⟩) ?_ ?_
  · -- a priori bound on `q`
    filter_upwards [hpt] with ω hω r hr i
    set Γ := c.σ (eulE c m S.ξ B (gridIdx m r.toNNReal) ω)
    set Γ' := c.σ (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω)
    have h3 : sq2 (fun i k => Γ i k - Γ' i k) ≤ d ^ 2 * (2 * c.M) ^ 2 := sq2_sub_le c _ _
    have h0 : 0 ≤ d ^ 2 * c.M ^ 2 * (4 * d) := by positivity
    by_cases hS' : (r, ω) ∈ stopSet S.τ
    · rw [(hω r hr).2.1 hS' i]
      set s := c.σ (Yv (r, ω))
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := Finset.single_le_sum (f := fun i => ∑ c₁, ∑ c₂,
        gX s Γ Γ' (regSeq n) (regSeq n') i c₁ * gX s Γ Γ' (regSeq n) (regSeq n') i c₂ *
          zDens s c₁ c₂) (fun i _ => quad_nonneg_zDens s _) (Finset.mem_univ i)
      have h2 := quad_sum_vsX_le s Γ Γ' (ε' := regSeq n') hεn
      have h4 := sq2_sigma_le c (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω)
      have h5 := frob_tikX_tikX_le s hεn hεn'
      have h6 := frob_nonneg (fun k c' => tikX s (regSeq n) k c' + -tikX s (regSeq n') k c')
      have h7 : sq2 Γ' * frob (fun k c' => tikX s (regSeq n) k c' + -tikX s (regSeq n') k c') ≤
          d ^ 2 * c.M ^ 2 * (4 * d) :=
        mul_le_mul h4 h5 h6 (by positivity)
      exact h1.trans (h2.trans (by linarith))
    · rw [(hω r hr).2.2 hS' i]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := Finset.single_le_sum (f := fun i => ∑ c₁, ∑ c₂,
        (∑ k, Γ i k * offval k c₁ - ∑ k, Γ' i k * offval k c₁) *
          (∑ k, Γ i k * offval k c₂ - ∑ k, Γ' i k * offval k c₂) * zDens 0 c₁ c₂)
        (fun i _ => quad_nonneg_zDens 0 _) (Finset.mem_univ i)
      have h2 := quad_sum_off Γ Γ'
      rw [h2] at h1
      have h8 : (0 : ℝ) ≤ d ^ 2 * (2 * c.M) ^ 2 := by positivity
      exact h1.trans (h3.trans (by linarith))
  · -- the isometry
    intro t ht i
    exact (lintegral_sq_vecCont_gen S.hZ S.hZs (hf i) ht).le
  · -- the representation
    intro t ht i
    have e : (fun c' => bpL2 (barMeasure P S.aZ N) (hf i c')) =
        (fun c' => bpL2 (barMeasure P S.aZ N) (hX i c')) -
          fun c' => bpL2 (barMeasure P S.aZ N) (hX' i c') :=
      funext fun c' => bpL2_sub' (hX i c') (hX' i c')
    filter_upwards [S.eulZ_rep_all m n N, S.eulZ_rep_all m' n' N,
      vecCont_sub_ae S.hZ (N : ℝ≥0) (fun c' => bpL2 (barMeasure P S.aZ N) (hX i c'))
        (fun c' => bpL2 (barMeasure P S.aZ N) (hX' i c')) t] with ω e1 e2 e3
    simp only [Mt]
    rw [e1 t ht i, e2 t ht i, e, e3]
    have hi : ∀ (m₀ : ℕ) (B₀ : ℝ≥0 → Ω → Fin d → ℝ) (hB₀ : ∀ t, Measurable[S.𝓕 t] (B₀ t)),
        IntegrableOn (fun r => eulDrift c m₀ S.ξ B₀ (N * 2 ^ m₀) i (r, ω)) (Ioc (0 : ℝ) t) :=
      fun m₀ B₀ hB₀ => Measure.integrableOn_of_bounded (M := c.M) (by simp)
        ((measurable_eulDrift c m₀ hB₀ S.hξ _ i).comp (measurable_id.prodMk
          measurable_const)).aestronglyMeasurable
        (Eventually.of_forall fun r => by
          rw [Real.norm_eq_abs]; exact abs_eulDrift_le c m₀ _ i _)
    simp only [β]
    rw [integral_sub (hi m B hBm) (hi m' B' hBm2)]
    ring
  · -- the integrated error
    have hm12 : Measurable fun p => eulEps c m S.ξ B A p + eulEps c m' S.ξ B' A2 p :=
      hm1.add hm2
    calc ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, ε (r, ω)) ∂P
        = (∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, eulEps c m S.ξ B A (r, ω)) ∂P +
            ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, eulEps c m' S.ξ B' A2 (r, ω)) ∂P) +
            ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, err (r, ω)) ∂P := by
          rw [lintegral_lintegral_add hm12, lintegral_lintegral_add hm1]
      _ ≤ _ := by
          gcongr
          · exact lintegral_eulEps_Ioc_le S m n N hAP hm1
          · exact lintegral_eulEps_Ioc_le S m' n' N hAP2 hm2
          · refine le_of_eq (lintegral_congr_ae ?_)
            filter_upwards [hAA] with ω hω
            refine lintegral_congr fun r => ?_
            by_cases h : (r, ω) ∈ stopSet S.τ
            · simp only [err, indicator_of_mem h, Yv, jointVersion_of_mem hω.2.2]
            · simp only [err, indicator_of_notMem h]
  · -- the pointwise bound
    filter_upwards [hpt] with ω hω r hr
    have eb := (hω r hr).1
    unfold coefSqA
    simp only [eb]
    by_cases hS' : (r, ω) ∈ stopSet S.τ
    · simp only [(hω r hr).2.1 hS']
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => quad_nonneg_zDens _ _]
      have hb := coefSq_vsX c (eulE c m S.ξ B (gridIdx m r.toNNReal) ω)
        (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω) (eulXv c m S.ξ B A (r, ω))
        (eulXv c m' S.ξ B' A2 (r, ω)) (Yv (r, ω)) (ε' := regSeq n') hεn
      simp only [ε, err, indicator_of_mem hS', D']
      refine hb.trans (le_of_eq ?_)
      unfold eulEps
      ring
    · simp only [(hω r hr).2.2 hS']
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => quad_nonneg_zDens _ _, quad_sum_off]
      have hb := coefSq_off c (eulE c m S.ξ B (gridIdx m r.toNNReal) ω)
        (eulE c m' S.ξ B' (gridIdx m' r.toNNReal) ω) (eulXv c m S.ξ B A (r, ω))
        (eulXv c m' S.ξ B' A2 (r, ω))
      simp only [ε, err, indicator_of_notMem hS', add_zero, D']
      refine hb.trans (le_of_eq ?_)
      unfold eulEps
      rfl

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
