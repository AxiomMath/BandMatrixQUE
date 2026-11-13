module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramOff

/-!
# Optional stopping for tested increments

Abstract (no RBM content). Measure: a finite measure `Q`; filtration: the raw natural filtration
`pastFiltration obs` of observables `obs`. No adaptedness of the process is assumed.

* `integral_smul_eq_zero_of_tested`: tested increments integrate to `0` against every bounded
  `pastSigma obs a`-measurable real test (conditional expectation and the pull-out property).
* `gridPt`, `gridIdx`: the grid `s = r_0 < … < r_{n+1} = t` and the first grid index at or after
  the stop; `sum_range_lt_sub` (telescoping).
* **`isTestedMart_stoppedProcess_of_tested`**: a process with tested increments, continuous for
  every `ω` and a.s. bounded on every `[0, t]`, stopped at a stopping time of the raw natural
  filtration, has tested increments (`X^ρ_t − X^ρ_s` is the limit of
  `Σ_k 1{r_k < ρ}(X_{r_{k+1}} − X_{r_k})`; dominated convergence).
* `continuous_primitive_Ioc`: `t ↦ ∫_{(0,t]} h` is continuous for measurable `h` bounded on every
  half-line `(-∞, T]`.
* `exists_bound_finite_compact`: a continuous function is bounded on (finite set) × (compact set).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.ClosedLimit
open scoped NNReal ENNReal

section Abstract

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {I : Type*} {Q : Measure Ω}
  {obs : I → ℝ≥0 → Ω → ℂ} {X : ℝ≥0 → Ω → ℂ}

/-- **Tested increments against bounded past-measurable real tests.** -/
theorem integral_smul_eq_zero_of_tested [IsFiniteMeasure Q] (hobs : ∀ i u, Measurable (obs i u))
    (hX : IsTestedMart Q obs X) {a b : ℝ≥0} (hab : a ≤ b) {g : Ω → ℝ}
    (hg : StronglyMeasurable[pastSigma obs a] g) {C : ℝ} (hC : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, g ω • (X b ω - X a ω) ∂Q = 0 := by
  have hle : pastSigma obs a ≤ mΩ := (pastFiltration obs hobs).le a
  have hint : Integrable (fun ω => X b ω - X a ω) Q := (hX.1 b).sub (hX.1 a)
  have h0 : Q[fun ω => X b ω - X a ω | pastSigma obs a] =ᵐ[Q] 0 := by
    refine (ae_eq_condExp_of_forall_setIntegral_eq hle hint
      (fun _ _ _ => integrableOn_zero) (fun A hA _ => ?_)
      stronglyMeasurable_const.aestronglyMeasurable).symm
    rw [setIntegral_eq_zero_of_tested hX hobs hab hA]
    simp
  have hfg : Integrable (g • fun ω => X b ω - X a ω) Q :=
    hint.bdd_smul C (hg.mono hle).aestronglyMeasurable (Eventually.of_forall hC)
  have hpull := condExp_smul_of_aestronglyMeasurable_left hg.aestronglyMeasurable hfg hint
  have h1 : Q[g • fun ω => X b ω - X a ω | pastSigma obs a] =ᵐ[Q] 0 := by
    filter_upwards [hpull, h0] with ω h1 h2
    simp only [h1, Pi.smul_apply', h2, Pi.zero_apply, smul_zero]
  have h2 := integral_condExp (μ := Q) (f := g • fun ω => X b ω - X a ω) hle
  rw [integral_congr_ae h1] at h2
  simpa using h2.symm

end Abstract

/-!
## The grid and the first grid index after the stop
-/

/-- The grid point `r_k = s + (t − s) k / (n + 1)`. -/
def gridPt (s t : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  ((s : ℝ) + ((t : ℝ) - s) * k / ((n : ℝ) + 1)).toNNReal

theorem coe_gridPt {s t : ℝ≥0} (hst : s ≤ t) (n k : ℕ) :
    (gridPt s t n k : ℝ) = (s : ℝ) + ((t : ℝ) - s) * k / ((n : ℝ) + 1) := by
  have hst' : (s : ℝ) ≤ t := hst
  refine Real.coe_toNNReal _ (add_nonneg s.2 (div_nonneg (mul_nonneg (sub_nonneg.2 hst')
    (Nat.cast_nonneg k)) (by positivity)))

theorem gridPt_zero (s t : ℝ≥0) (n : ℕ) : gridPt s t n 0 = s := by
  simp [gridPt]

theorem gridPt_last {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) : gridPt s t n (n + 1) = t := by
  apply NNReal.eq
  rw [coe_gridPt hst]
  push_cast
  field_simp
  ring

theorem gridPt_mono {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    gridPt s t n k ≤ gridPt s t n k' := by
  rw [← NNReal.coe_le_coe, coe_gridPt hst, coe_gridPt hst]
  have hst' : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 hst
  have hk' : (k : ℝ) ≤ k' := Nat.cast_le.2 hk
  have h1 : ((t : ℝ) - s) * k ≤ ((t : ℝ) - s) * k' := mul_le_mul_of_nonneg_left hk' hst'
  have h2 := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
  linarith

theorem coe_gridPt_succ {s t : ℝ≥0} (hst : s ≤ t) (n k : ℕ) :
    (gridPt s t n (k + 1) : ℝ) = gridPt s t n k + ((t : ℝ) - s) / ((n : ℝ) + 1) := by
  rw [coe_gridPt hst, coe_gridPt hst]
  push_cast
  ring

open Classical in
/-- The first grid index `k ≤ n + 1` with `ρ ≤ r_k` (or `n + 1`). -/
def gridIdx (s t : ℝ≥0) (n : ℕ) (ρ : WithTop ℝ≥0) : ℕ :=
  Nat.find (⟨n + 1, Or.inl rfl⟩ :
    ∃ k, k = n + 1 ∨ ¬ ((gridPt s t n k : WithTop ℝ≥0) < ρ))

theorem gridIdx_le (s t : ℝ≥0) (n : ℕ) (ρ : WithTop ℝ≥0) : gridIdx s t n ρ ≤ n + 1 := by
  classical
  exact Nat.find_min' _ (Or.inl rfl)

theorem lt_of_lt_gridIdx {s t : ℝ≥0} {n : ℕ} {ρ : WithTop ℝ≥0} {k : ℕ}
    (hk : k < gridIdx s t n ρ) : (gridPt s t n k : WithTop ℝ≥0) < ρ := by
  classical
  have h := Nat.find_min _ hk
  push Not at h
  exact h.2

theorem gridIdx_spec (s t : ℝ≥0) (n : ℕ) (ρ : WithTop ℝ≥0) :
    gridIdx s t n ρ = n + 1 ∨ ¬ ((gridPt s t n (gridIdx s t n ρ) : WithTop ℝ≥0) < ρ) := by
  classical
  exact Nat.find_spec (⟨n + 1, Or.inl rfl⟩ :
    ∃ k, k = n + 1 ∨ ¬ ((gridPt s t n k : WithTop ℝ≥0) < ρ))

theorem lt_iff_lt_gridIdx {s t : ℝ≥0} (hst : s ≤ t) {n : ℕ} {ρ : WithTop ℝ≥0} {k : ℕ}
    (hkn : k ≤ n) : (gridPt s t n k : WithTop ℝ≥0) < ρ ↔ k < gridIdx s t n ρ := by
  refine ⟨fun h => ?_, lt_of_lt_gridIdx⟩
  by_contra hle
  push Not at hle
  rcases gridIdx_spec s t n ρ with h1 | h1
  · omega
  · exact h1 (lt_of_le_of_lt (WithTop.coe_le_coe.2 (gridPt_mono hst n hle)) h)

/-- Telescoping a sum truncated at `κ`. -/
theorem sum_range_lt_sub (f : ℕ → ℂ) {κ n : ℕ} (hκ : κ ≤ n) :
    ∑ k ∈ Finset.range n, (if k < κ then f (k + 1) - f k else 0) = f κ - f 0 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : (Finset.range n).filter (fun k => k < κ) = Finset.range κ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.sum_range_sub]

theorem coe_untopA_min' (t : ℝ≥0) (a : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) a).untopA : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) a := by
  have hne : min (t : WithTop ℝ≥0) a ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]

/-- The grid point at the first index after the stop is within one mesh of `t ∧ ρ`. -/
theorem gridIdx_bounds {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) {ρ : WithTop ℝ≥0}
    (hs : (s : WithTop ℝ≥0) < ρ) :
    (min (t : WithTop ℝ≥0) ρ).untopA ≤ gridPt s t n (gridIdx s t n ρ) ∧
      (gridPt s t n (gridIdx s t n ρ) : ℝ) ≤
        ((min (t : WithTop ℝ≥0) ρ).untopA : ℝ) + ((t : ℝ) - s) / ((n : ℝ) + 1) := by
  set κ := gridIdx s t n ρ with hκ
  set v := (min (t : WithTop ℝ≥0) ρ).untopA with hv
  have hvc : (v : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) ρ := coe_untopA_min' t ρ
  have hκ1 : 1 ≤ κ := by
    by_contra h0
    have h0' : κ = 0 := by omega
    rcases gridIdx_spec s t n ρ with h1 | h1
    · omega
    · rw [← hκ, h0', gridPt_zero] at h1
      exact h1 hs
  have hκn := gridIdx_le s t n ρ
  have hprev : (gridPt s t n (κ - 1) : WithTop ℝ≥0) < ρ := lt_of_lt_gridIdx (by omega)
  have hprevt : gridPt s t n (κ - 1) ≤ t :=
    (gridPt_mono hst n (by omega)).trans_eq (gridPt_last hst n)
  have hprev_v : gridPt s t n (κ - 1) ≤ v := by
    rw [← WithTop.coe_le_coe, hvc]
    exact le_min (WithTop.coe_le_coe.2 hprevt) hprev.le
  have hsucc : (gridPt s t n κ : ℝ) = gridPt s t n (κ - 1) + ((t : ℝ) - s) / ((n : ℝ) + 1) := by
    have := coe_gridPt_succ hst n (κ - 1)
    rwa [Nat.sub_add_cancel hκ1] at this
  refine ⟨?_, ?_⟩
  · rcases gridIdx_spec s t n ρ with h1 | h1
    · rw [show κ = n + 1 from h1, gridPt_last hst n, ← WithTop.coe_le_coe, hvc]
      exact min_le_left _ _
    · have h1' : ¬ ((gridPt s t n κ : WithTop ℝ≥0) < ρ) := h1
      push Not at h1'
      rw [← WithTop.coe_le_coe, hvc]
      exact (min_le_right _ _).trans h1'
  · rw [hsucc]
    have : (gridPt s t n (κ - 1) : ℝ) ≤ v := hprev_v
    linarith

section Stop

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {I : Type*} {Q : Measure Ω}
  {obs : I → ℝ≥0 → Ω → ℂ} {X : ℝ≥0 → Ω → ℂ}

/-- The grid approximation `Σ_k 1{r_k < ρ}(X_{r_{k+1}} − X_{r_k})` of `X^ρ_t − X^ρ_s`. -/
def gridSum (X : ℝ≥0 → Ω → ℂ) (ρ : Ω → WithTop ℝ≥0) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω}.indicator
    (fun ω => X (gridPt s t n (k + 1)) ω - X (gridPt s t n k) ω) ω

omit mΩ in
theorem gridSum_eq {ρ : Ω → WithTop ℝ≥0} {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) (ω : Ω) :
    gridSum X ρ s t n ω =
      X (gridPt s t n (gridIdx s t n (ρ ω))) ω - X (gridPt s t n 0) ω := by
  have h := sum_range_lt_sub (fun k => X (gridPt s t n k) ω) (gridIdx_le s t n (ρ ω))
  rw [← h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by simp only [Finset.mem_range] at hk; omega
  by_cases hlt : (gridPt s t n k : WithTop ℝ≥0) < ρ ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω} from hlt)]
    simp only [(lt_iff_lt_gridIdx hst hkn).1 hlt, ↓reduceIte]
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω} from hlt)]
    simp only [show ¬ k < gridIdx s t n (ρ ω) from fun h => hlt ((lt_iff_lt_gridIdx hst hkn).2 h),
      ↓reduceIte]

omit mΩ in
theorem tendsto_gridSum {ρ : Ω → WithTop ℝ≥0} {s t : ℝ≥0} (hst : s ≤ t) {ω : Ω}
    (hc : Continuous fun t => X t ω) :
    Tendsto (fun n => gridSum X ρ s t n ω) atTop
      (𝓝 (stoppedProcess X ρ t ω - stoppedProcess X ρ s ω)) := by
  have e : ∀ n, gridSum X ρ s t n ω =
      X (gridPt s t n (gridIdx s t n (ρ ω))) ω - X s ω := fun n => by
    rw [gridSum_eq hst, gridPt_zero]
  refine Tendsto.congr (fun n => (e n).symm) ?_
  by_cases hs : (s : WithTop ℝ≥0) < ρ ω
  · have hsσ : stoppedProcess X ρ s ω = X s ω := stoppedProcess_eq_of_le hs.le
    rw [hsσ]
    refine Tendsto.sub ?_ tendsto_const_nhds
    set v := (min (t : WithTop ℝ≥0) (ρ ω)).untopA
    have hmesh : Tendsto (fun n : ℕ => ((t : ℝ) - s) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((t : ℝ) - s)
      rw [mul_zero] at this
      exact this.congr fun n => mul_one_div _ _
    have hb1 : ∀ n, (v : ℝ) ≤ gridPt s t n (gridIdx s t n (ρ ω)) := fun n =>
      NNReal.coe_le_coe.2 (gridIdx_bounds hst n hs).1
    have hb2 : ∀ n, (gridPt s t n (gridIdx s t n (ρ ω)) : ℝ) ≤
        (v : ℝ) + ((t : ℝ) - s) / ((n : ℝ) + 1) := fun n => (gridIdx_bounds hst n hs).2
    have hup : Tendsto (fun n : ℕ => (v : ℝ) + ((t : ℝ) - s) / ((n : ℝ) + 1)) atTop
        (𝓝 (v : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (v : ℝ))).add hmesh
    have hpt : Tendsto (fun n => gridPt s t n (gridIdx s t n (ρ ω))) atTop (𝓝 v) := by
      rw [← NNReal.tendsto_coe]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hb1 hb2
    exact ((hc.tendsto v).comp hpt)
  · push Not at hs
    have hκ : ∀ n, gridIdx s t n (ρ ω) = 0 := fun n => by
      by_contra h0
      have := lt_of_lt_gridIdx (k := 0) (Nat.pos_of_ne_zero h0)
      rw [gridPt_zero] at this
      exact absurd hs (not_le.2 this)
    have h1 : stoppedProcess X ρ t ω = X (ρ ω).untopA ω :=
      stoppedProcess_eq_of_ge (hs.trans (WithTop.coe_le_coe.2 hst))
    have h2 : stoppedProcess X ρ s ω = X (ρ ω).untopA ω := stoppedProcess_eq_of_ge hs
    simp only [hκ, gridPt_zero, sub_self, h1, h2]
    exact tendsto_const_nhds

/-- **Optional stopping for tested increments.** -/
theorem isTestedMart_stoppedProcess_of_tested [IsFiniteMeasure Q]
    (hobs : ∀ i u, Measurable (obs i u)) (hX : IsTestedMart Q obs X)
    (hc : ∀ ω, Continuous fun t => X t ω)
    (hbd : ∀ t, ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ v ≤ t, ‖X v ω‖ ≤ C) {ρ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime (pastFiltration obs hobs) ρ) :
    IsTestedMart Q obs (stoppedProcess X ρ) := by
  have hS : ∀ (s t : ℝ≥0) (n k : ℕ),
      MeasurableSet[pastSigma obs (gridPt s t n k)]
        {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω} := fun s t n k => by
    have h := (hρ (gridPt s t n k)).compl
    have e : {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω} =
        {ω | ρ ω ≤ (gridPt s t n k : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    rw [e]
    exact h
  have hSm : ∀ (s t : ℝ≥0) (n k : ℕ), MeasurableSet {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω} :=
    fun s t n k => (pastFiltration obs hobs).le _ _ (hS s t n k)
  have hZm : ∀ (s t : ℝ≥0) (n : ℕ), AEStronglyMeasurable (gridSum X ρ s t n) Q := fun s t n => by
    unfold gridSum
    exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      (((hX.1 _).sub (hX.1 _)).aestronglyMeasurable).indicator (hSm s t n k)
  have hZb : ∀ (s t : ℝ≥0), s ≤ t → ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ n,
      ‖gridSum X ρ s t n ω‖ ≤ C + C := fun s t hst => by
    obtain ⟨C, hC⟩ := hbd t
    refine ⟨C, hC.mono fun ω hω n => ?_⟩
    rw [gridSum_eq hst]
    refine (norm_sub_le _ _).trans (add_le_add (hω _ ?_) (hω _ ?_))
    · exact (gridPt_mono hst n (gridIdx_le _ _ _ _)).trans_eq (gridPt_last hst n)
    · exact (gridPt_mono hst n (Nat.zero_le _)).trans_eq (gridPt_last hst n)
  have hlim : ∀ (s t : ℝ≥0), s ≤ t → ∀ ω, Tendsto (fun n => gridSum X ρ s t n ω) atTop
      (𝓝 (stoppedProcess X ρ t ω - stoppedProcess X ρ s ω)) := fun s t hst ω =>
    tendsto_gridSum hst (hc ω)
  have hdiff : ∀ (s t : ℝ≥0), s ≤ t →
      AEStronglyMeasurable (fun ω => stoppedProcess X ρ t ω - stoppedProcess X ρ s ω) Q :=
    fun s t hst => aestronglyMeasurable_of_tendsto_ae atTop (hZm s t)
      (ae_of_all _ (hlim s t hst))
  have h0 : stoppedProcess X ρ 0 = X 0 := by
    funext ω
    exact stoppedProcess_eq_of_le (by rw [WithTop.coe_zero]; exact bot_le)
  have hint : ∀ t, Integrable (stoppedProcess X ρ t) Q := fun t => by
    obtain ⟨C, hC⟩ := hbd t
    have hm : AEStronglyMeasurable (stoppedProcess X ρ t) Q := by
      have := (hdiff 0 t (zero_le)).add (hX.1 0).aestronglyMeasurable
      rw [h0] at this
      exact this.congr (ae_of_all _ fun ω => by simp)
    refine Integrable.of_bound hm C (hC.mono fun ω hω => ?_)
    obtain ⟨w, hwt, -, he⟩ := Ident2.exists_stoppedProcess_eq X ρ t ω
    rw [he]
    exact hω w hwt
  refine ⟨hint, fun s t hst m i u hu φ => ?_⟩
  set ψ : Ω → ℝ := fun ω => φ (fun l => obs (i l) (u l) ω) with hψ_def
  have hψm : ∀ k : ℝ≥0, s ≤ k → StronglyMeasurable[pastSigma obs k] ψ := fun k hk => by
    let _ : MeasurableSpace Ω := pastSigma obs k
    exact (φ.continuous.measurable.comp
      (measurable_cyl obs i u fun l => (hu l).trans hk)).stronglyMeasurable
  have hzero : ∀ n, ∫ ω, ψ ω • gridSum X ρ s t n ω ∂Q = 0 := fun n => by
    have e : (fun ω => ψ ω • gridSum X ρ s t n ω) = fun ω => ∑ k ∈ Finset.range (n + 1),
        (ψ ω * {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω}.indicator (fun _ => (1 : ℝ)) ω) •
          (X (gridPt s t n (k + 1)) ω - X (gridPt s t n k) ω) := by
      funext ω
      simp only [gridSum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hω : ω ∈ {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω}
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]; simp
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]; simp
    rw [e, integral_finsetSum]
    · refine Finset.sum_eq_zero fun k _ => ?_
      have hk : s ≤ gridPt s t n k :=
        (gridPt_zero s t n).symm.trans_le (gridPt_mono hst n (Nat.zero_le _))
      refine integral_smul_eq_zero_of_tested hobs hX
        (gridPt_mono hst n (Nat.le_succ k)) ((hψm _ hk).mul
          (stronglyMeasurable_const.indicator (hS s t n k))) (C := ‖φ‖) fun ω => ?_
      rw [norm_mul]
      refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (φ.norm_coe_le_norm _)
      by_cases hω : ω ∈ {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω}
      · rw [Set.indicator_of_mem hω]; simp
      · rw [Set.indicator_of_notMem hω]; simp
    · intro k _
      refine ((hX.1 (gridPt s t n (k + 1))).sub (hX.1 (gridPt s t n k))).bdd_smul
        (φ := fun ω => ψ ω * {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω}.indicator
          (fun _ => (1 : ℝ)) ω) ‖φ‖ ?_ (Eventually.of_forall fun ω => ?_)
      · exact (((hψm s le_rfl).mono ((pastFiltration obs hobs).le s)).aestronglyMeasurable).mul
          (aestronglyMeasurable_const.indicator (hSm s t n k))
      · rw [norm_mul]
        refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (φ.norm_coe_le_norm _)
        by_cases hω : ω ∈ {ω | (gridPt s t n k : WithTop ℝ≥0) < ρ ω}
        · rw [Set.indicator_of_mem hω]; simp
        · rw [Set.indicator_of_notMem hω]; simp
  obtain ⟨C, hC⟩ := hZb s t hst
  have hψa : AEStronglyMeasurable ψ Q :=
    ((hψm s le_rfl).mono ((pastFiltration obs hobs).le s)).aestronglyMeasurable
  have hlimI := tendsto_integral_of_dominated_convergence (μ := Q) (fun _ => ‖φ‖ * (C + C))
    (F := fun n ω => ψ ω • gridSum X ρ s t n ω)
    (f := fun ω => ψ ω • (stoppedProcess X ρ t ω - stoppedProcess X ρ s ω))
    (fun n => hψa.smul (hZm s t n)) (integrable_const _)
    (fun n => hC.mono fun ω hω => by
      rw [norm_smul]
      exact mul_le_mul (φ.norm_coe_le_norm _) (hω n) (norm_nonneg _) (norm_nonneg _))
    (ae_of_all _ fun ω => (hlim s t hst ω).const_smul (ψ ω))
  exact tendsto_nhds_unique hlimI (by simp only [hzero]; exact tendsto_const_nhds)

end Stop

/-!
## Continuity of primitives and bounds on finite × compact sets
-/

/-- `t ↦ ∫_{(0,t]} h` is continuous for measurable `h` bounded on every half-line. -/
theorem continuous_primitive_Ioc {h : ℝ → ℂ} (hm : AEStronglyMeasurable h volume)
    (hb : ∀ T : ℝ, ∃ C : ℝ, ∀ u, u ≤ T → ‖h u‖ ≤ C) :
    Continuous fun t : ℝ≥0 => ∫ u in Ioc (0 : ℝ) t, h u := by
  have hii : ∀ a b : ℝ, IntervalIntegrable h volume a b := fun a b => by
    obtain ⟨C, hC⟩ := hb (max a b)
    refine (intervalIntegrable_iff).2 (Measure.integrableOn_of_bounded (M := C)
      (lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top).ne
      hm ?_)
    exact (ae_restrict_mem measurableSet_uIoc).mono fun u hu => hC u hu.2
  have hc := (intervalIntegral.continuous_primitive hii 0).comp NNReal.continuous_coe
  refine hc.congr fun t => ?_
  simp only [Function.comp]
  exact intervalIntegral.integral_of_le t.2

theorem exists_bound_finite_compact {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {F : α × β → ℂ} (hF : Continuous F) {S : Set α} (hS : S.Finite) {Kz : Set β}
    (hK : IsCompact Kz) : ∃ C : ℝ, ∀ a ∈ S, ∀ z ∈ Kz, ‖F (a, z)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hS.isCompact.prod hK).exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun a ha z hz => hC (a, z) ⟨ha, hz⟩⟩

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram
