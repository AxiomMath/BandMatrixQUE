module

public import BlockBand.Transmission.LawDuality.SubLimitMetric

/-!
# Finite-dimensional convergence at every positive time

* `tendsto_fdd_qT`: fdd convergence at the dense times `qT j` (weak convergence of the path
  laws tested on `Φ ∘ (evaluation at finitely many coordinates)`; `extPath_qT` a.s.).
* `tendsto_lip`: for every bounded Lipschitz test `f` (moment metric, local instance) and
  arbitrary positive times `τ`, `E f(X_{ms n}(τ)) → E f(extPath(τ))`. Three-term comparison:
  (i) move `τ` to dense times `τ'` with the modulus (`MomentModulus`) and
  `abs_integral_sub_le`; (ii) `tendsto_fdd_qT` at `τ'`; (iii) dominated convergence on the
  limit side, from the a.s. continuity of `extPath`.
* **`tendsto_fdd`**: the same for every bounded continuous `Φ` (Mathlib's
  `tendsto_iff_forall_lipschitz_integral_tendsto`, then back to the weak topology).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality.SubLimit

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Transmission.LawDuality
open scoped NNReal ENNReal

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {Ps : ∀ n, Measure (Ωs n)}
  {X : ∀ n, ℝ → Ωs n → St}

theorem ae_mem_goodSet {Q : ProbabilityMeasure (ℕ → St)} (hG : (Q : Measure (ℕ → St)) goodSetᶜ = 0) :
    ∀ᵐ ω ∂(Q : Measure (ℕ → St)), ω ∈ goodSet :=
  ae_iff.2 hG

theorem mul_le_one_aux {x y : ℝ} (hx : x ≤ 1) (hy0 : 0 ≤ y) (hy : y ≤ 1) : x * y ≤ 1 := by
  nlinarith

/-- **fdd convergence at the dense times.** -/
theorem tendsto_fdd_qT [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas Ps X)
    {Q : ProbabilityMeasure (ℕ → St)} {ms : ℕ → ℕ}
    (hQ : Tendsto (fun n => lawY Ps X (ms n)) atTop (𝓝 Q))
    (hG : (Q : Measure (ℕ → St)) goodSetᶜ = 0) {k : ℕ} (js : Fin k → ℕ)
    (Φ : BoundedContinuousFunction (Fin k → St) ℝ) :
    Tendsto (fun n => ∫ ω, Φ (fun l => X (ms n) (qT (js l)) ω) ∂Ps (ms n)) atTop
      (𝓝 (∫ ω, Φ (fun l => extPath ω (qT (js l))) ∂(Q : Measure (ℕ → St)))) := by
  let π : C(ℕ → St, Fin k → St) :=
    ⟨fun ω l => ω (js l), continuous_pi fun l => continuous_apply _⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hQ) (Φ.compContinuous π)
  have e1 : ∀ n, ∫ ω, (Φ.compContinuous π) ω ∂((lawY Ps X (ms n) : ProbabilityMeasure _) :
      Measure (ℕ → St)) = ∫ ω, Φ (fun l => X (ms n) (qT (js l)) ω) ∂Ps (ms n) := fun n =>
    integral_map (aemeasurable_pathY hX _) (Φ.compContinuous π).continuous.aestronglyMeasurable
  have e2 : ∫ ω, (Φ.compContinuous π) ω ∂(Q : Measure (ℕ → St)) =
      ∫ ω, Φ (fun l => extPath ω (qT (js l))) ∂(Q : Measure (ℕ → St)) := by
    refine integral_congr_ae ((ae_mem_goodSet hG).mono fun ω hω => ?_)
    simp [π, extPath_qT hω]
  simpa only [e1, e2] using h

section Lip

attribute [local instance] momentMetric

theorem exists_small_delta {k I : ℕ} {δ : Fin k × Fin I → ℝ} (hδ : ∀ p, 0 < δ p) {τ : Fin k → ℝ}
    (hτ : ∀ l, 0 < τ l) : ∃ δ₀ : ℝ, 0 < δ₀ ∧ (∀ p, δ₀ ≤ δ p) ∧ ∀ l, δ₀ ≤ τ l / 2 := by
  obtain ⟨A, hA⟩ := Finite.exists_le fun p : Fin k × Fin I => 1 / δ p
  obtain ⟨B, hB⟩ := Finite.exists_le fun l : Fin k => 2 / τ l
  set M := max (max A B) 1
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1 / M, by positivity, fun p => ?_, fun l => ?_⟩
  · have h := (hA p).trans ((le_max_left _ _).trans (le_max_left _ _) : A ≤ M)
    rw [div_le_iff₀ (hδ p)] at h
    rw [div_le_iff₀ hM]; linarith [mul_comm M (δ p)]
  · have h := (hB l).trans ((le_max_right _ _).trans (le_max_left _ _) : B ≤ M)
    rw [div_le_iff₀ (hτ l)] at h
    rw [div_le_iff₀ hM]; nlinarith

/-- **Convergence of bounded Lipschitz tests at arbitrary positive times.** -/
theorem tendsto_lip [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas Ps X)
    (hM : MomentModulus Ps X) {Q : ProbabilityMeasure (ℕ → St)} {ms : ℕ → ℕ}
    (hms : StrictMono ms) (hQ : Tendsto (fun n => lawY Ps X (ms n)) atTop (𝓝 Q))
    (hG : (Q : Measure (ℕ → St)) goodSetᶜ = 0) {k : ℕ} (τ : Fin k → ℝ) (hτ : ∀ l, 0 < τ l)
    {f : (Fin k → St) → ℝ} {C : ℝ} (hC : ∀ x y, dist (f x) (f y) ≤ C) {K : ℝ≥0}
    (hK : LipschitzWith K f) :
    Tendsto (fun n => ∫ ω, f (fun l => X (ms n) (τ l) ω) ∂Ps (ms n)) atTop
      (𝓝 (∫ ω, f (fun l => extPath ω (τ l)) ∂(Q : Measure (ℕ → St)))) := by
  have hC0 : 0 ≤ C := le_trans dist_nonneg (hC (fun _ => 0) (fun _ => 0))
  let fb : BoundedContinuousFunction (Fin k → St) ℝ := ⟨⟨f, hK.continuous⟩, ⟨C, hC⟩⟩
  have hbd : ∀ x, ‖f x‖ ≤ |f (fun _ => 0)| + C := fun x => by
    have := hC x (fun _ => 0)
    rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (f x) (f (fun _ => 0))
    rw [Real.norm_eq_abs]; linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e := ε / 4 with he
  have he0 : 0 < e := by positivity
  obtain ⟨I, hI⟩ := exists_pow_lt_of_lt_one (show 0 < e / (4 * ((K : ℝ) + 1)) by positivity)
    (show (2⁻¹ : ℝ) < 1 by norm_num)
  set η : ℝ := e / (2 * ((K : ℝ) + 1) * ((I : ℝ) + 1)) with hη_def
  have hη : 0 < η := by positivity
  set r : ℝ := I * η + 2 * 2⁻¹ ^ I with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hKr : (K : ℝ) * r ≤ e := by
    have h1 : (K : ℝ) * (I * η) ≤ e / 2 := by
      rw [hη_def, show (K : ℝ) * (I * (e / (2 * ((K : ℝ) + 1) * ((I : ℝ) + 1)))) =
        e / 2 * ((K / (K + 1)) * (I / (I + 1))) by field_simp]
      refine mul_le_of_le_one_right (by positivity) ?_
      exact mul_le_one_aux ((div_le_one (by positivity)).2 (by linarith))
        (by positivity) ((div_le_one (by positivity)).2 (by linarith))
    have h2 : (K : ℝ) * (2 * 2⁻¹ ^ I) ≤ e / 2 := by
      have : (K : ℝ) * (2 * 2⁻¹ ^ I) ≤ (K + 1) * (2 * (e / (4 * ((K : ℝ) + 1)))) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      refine this.trans (le_of_eq ?_)
      field_simp; ring
    rw [hr_def, mul_add]; linarith
  set θ : ℝ := e / ((C + 1) * ((k : ℝ) * I + 1)) with hθ_def
  have hθ : 0 < θ := by positivity
  have hCθ : C * ((k : ℝ) * I * θ) ≤ e := by
    rw [hθ_def, show C * ((k : ℝ) * I * (e / ((C + 1) * ((k : ℝ) * I + 1)))) =
      e * ((C / (C + 1)) * ((k * I) / (k * I + 1))) by field_simp]
    refine mul_le_of_le_one_right he0.le ?_
    exact mul_le_one_aux ((div_le_one (by positivity)).2 (by linarith)) (by positivity)
      ((div_le_one (by positivity)).2 (by linarith))
  choose δ hδ N hN using fun p : Fin k × Fin I =>
    hM (τ p.1 / 2) (2 * τ p.1) (by linarith [hτ p.1]) p.2 η θ hη hθ
  obtain ⟨δ₀, hδ₀, hδ₀δ, hδ₀τ⟩ := exists_small_delta hδ hτ
  obtain ⟨N₁, hN₁⟩ := Finite.exists_le N
  set τ' : ℕ → Fin k → ℝ := fun m l => qT (seqT (τ l) m)
  have hτ' : ∀ l, Tendsto (fun m => τ' m l) atTop (𝓝 (τ l)) := fun l => tendsto_seqT (hτ l)
  have hev1 : ∀ᶠ m in atTop, ∀ l, |τ' m l - τ l| ≤ δ₀ :=
    eventually_all.2 fun l => (eventually_near (hτ' l) hδ₀).mono fun _ h => h.le
  have hdct : Tendsto (fun m => ∫ ω, f (fun l => extPath ω (τ' m l)) ∂(Q : Measure (ℕ → St)))
      atTop (𝓝 (∫ ω, f (fun l => extPath ω (τ l)) ∂(Q : Measure (ℕ → St)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => |f (fun _ => 0)| + C)
      (fun m => ?_) (integrable_const _) (fun m => Eventually.of_forall fun ω => hbd _)
      ((ae_mem_goodSet hG).mono fun ω hω => ?_)
    · exact (hK.continuous.measurable.comp (measurable_pi_iff.2 fun l =>
        measurable_extPath (qT_pos _))).aestronglyMeasurable
    · have : Tendsto (fun m => fun l => extPath ω (τ' m l)) atTop
          (𝓝 (fun l => extPath ω (τ l))) := tendsto_pi_nhds.2 fun l =>
        ((continuousOn_extPath hω).continuousAt (Ioi_mem_nhds (hτ l))).tendsto.comp (hτ' l)
      exact (hK.continuous.tendsto _).comp this
  have hev2 : ∀ᶠ m in atTop, dist (∫ ω, f (fun l => extPath ω (τ' m l)) ∂(Q : Measure (ℕ → St)))
      (∫ ω, f (fun l => extPath ω (τ l)) ∂(Q : Measure (ℕ → St))) < e :=
    (Metric.tendsto_nhds.1 hdct) e he0
  obtain ⟨m, hm1, hm2⟩ := (hev1.and hev2).exists
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1
    (tendsto_fdd_qT hX hQ hG (fun l => seqT (τ l) m) fb) e he0
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : ∀ p, N p ≤ ms n := fun p =>
    (hN₁ p).trans ((le_max_left _ _).trans (hn.trans (hms.id_le n)))
  have h2 := hN₂ n ((le_max_right _ _).trans hn)
  let Bs : Fin k × Fin I → Set (Ωs (ms n)) := fun p => {ω | ∃ t ∈ Icc (τ p.1 / 2) (2 * τ p.1),
    ∃ t' ∈ Icc (τ p.1 / 2) (2 * τ p.1), |t - t'| ≤ δ p ∧
      η < |moment p.2 (X (ms n) t ω) - moment p.2 (X (ms n) t' ω)|}
  have hB : (Ps (ms n) (⋃ p, Bs p)).toReal ≤ k * I * θ := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((measure_iUnion_fintype_le _ _).trans ?_)
    refine (Finset.sum_le_sum fun p _ => hN p (ms n) (hn1 p)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    push_cast; ring_nf
  have h1 := abs_integral_sub_le (P := Ps (ms n)) (AEMeasurable.of_eval fun l => hX _ _ (hτ l))
    (AEMeasurable.of_eval fun l => hX _ _ (qT_pos (seqT (τ l) m))) hK hC (B := ⋃ p, Bs p) hr0
    (fun ω hω => by
      refine dist_pi_le_moments _ _ I (by positivity) fun l => ?_
      refine (Finset.sum_le_card_nsmul _ _ η fun i hi => ?_).trans (by simp)
      by_contra hlt
      refine hω (mem_iUnion.2 ⟨(l, ⟨i, Finset.mem_range.1 hi⟩), ?_⟩)
      have hτl := hτ l
      have hd := hm1 l
      rw [abs_le] at hd
      have := hδ₀τ l
      refine ⟨τ l, ⟨by linarith, by linarith⟩, τ' m l, ⟨by linarith, by linarith⟩, ?_,
        not_le.1 hlt⟩
      rw [abs_sub_comm, abs_le]
      have := hδ₀δ (l, ⟨i, Finset.mem_range.1 hi⟩)
      exact ⟨by linarith, by linarith⟩)
  rw [Real.dist_eq] at h2 hm2 ⊢
  have h3 : C * (Ps (ms n) (⋃ p, Bs p)).toReal ≤ C * ((k : ℝ) * I * θ) :=
    mul_le_mul_of_nonneg_left hB hC0
  have := abs_sub_le (∫ ω, f (fun l => X (ms n) (τ l) ω) ∂Ps (ms n))
    (∫ ω, f (fun l => X (ms n) (τ' m l) ω) ∂Ps (ms n))
    (∫ ω, f (fun l => extPath ω (τ l)) ∂(Q : Measure (ℕ → St)))
  have := abs_sub_le (∫ ω, f (fun l => X (ms n) (τ' m l) ω) ∂Ps (ms n))
    (∫ ω, f (fun l => extPath ω (τ' m l)) ∂(Q : Measure (ℕ → St)))
    (∫ ω, f (fun l => extPath ω (τ l)) ∂(Q : Measure (ℕ → St)))
  have h2' : |∫ ω, f (fun l => X (ms n) (τ' m l) ω) ∂Ps (ms n) -
      ∫ ω, f (fun l => extPath ω (τ' m l)) ∂(Q : Measure (ℕ → St))| < e := h2
  linarith

end Lip

/-- **fdd convergence at every family of positive times.** -/
theorem tendsto_fdd [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas Ps X)
    (hM : MomentModulus Ps X) {Q : ProbabilityMeasure (ℕ → St)} {ms : ℕ → ℕ}
    (hms : StrictMono ms) (hQ : Tendsto (fun n => lawY Ps X (ms n)) atTop (𝓝 Q))
    (hG : (Q : Measure (ℕ → St)) goodSetᶜ = 0) {k : ℕ} (τ : Fin k → ℝ) (hτ : ∀ l, 0 < τ l)
    (Φ : BoundedContinuousFunction (Fin k → St) ℝ) :
    Tendsto (fun n => ∫ ω, Φ (fun l => X (ms n) (τ l) ω) ∂Ps (ms n)) atTop
      (𝓝 (∫ ω, Φ (fun l => extPath ω (τ l)) ∂(Q : Measure (ℕ → St)))) := by
  have hZ : ∀ n, AEMeasurable (fun ω l => X (ms n) (τ l) ω) (Ps (ms n)) := fun n =>
    AEMeasurable.of_eval fun l => hX _ _ (hτ l)
  have hZ' : Measurable fun (ω : ℕ → St) l => extPath ω (τ l) :=
    measurable_pi_iff.2 fun l => measurable_extPath (hτ l)
  let L : ℕ → ProbabilityMeasure (Fin k → St) := fun n =>
    ⟨(Ps (ms n)).map (fun ω l => X (ms n) (τ l) ω), inferInstance⟩
  let L' : ProbabilityMeasure (Fin k → St) :=
    ⟨(Q : Measure (ℕ → St)).map (fun ω l => extPath ω (τ l)), inferInstance⟩
  have hL : Tendsto L atTop (𝓝 L') := by
    let _ := momentMetric
    refine (tendsto_iff_forall_lipschitz_integral_tendsto (μs := L) (μ := L')).2
      fun f ⟨C, hC⟩ ⟨K, hK⟩ => ?_
    have hf := hK.continuous.aestronglyMeasurable (μ := (L' : Measure (Fin k → St)))
    rw [show ∫ x, f x ∂(L' : Measure (Fin k → St)) = ∫ ω, f (fun l => extPath ω (τ l))
        ∂(Q : Measure (ℕ → St)) from integral_map hZ'.aemeasurable hf]
    have e : ∀ n, ∫ x, f x ∂(L n : Measure (Fin k → St)) =
        ∫ ω, f (fun l => X (ms n) (τ l) ω) ∂Ps (ms n) := fun n =>
      integral_map (hZ n) hK.continuous.aestronglyMeasurable
    simp_rw [e]
    exact tendsto_lip hX hM hms hQ hG τ hτ hC hK
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hL) Φ
  have e1 : ∀ n, ∫ x, Φ x ∂(L n : Measure (Fin k → St)) =
      ∫ ω, Φ (fun l => X (ms n) (τ l) ω) ∂Ps (ms n) := fun n =>
    integral_map (hZ n) Φ.continuous.aestronglyMeasurable
  have e2 : ∫ x, Φ x ∂(L' : Measure (Fin k → St)) =
      ∫ ω, Φ (fun l => extPath ω (τ l)) ∂(Q : Measure (ℕ → St)) :=
    integral_map hZ'.aemeasurable Φ.continuous.aestronglyMeasurable
  simpa only [e1, e2] using this

end BlockBand.Transmission.LawDuality.SubLimit
