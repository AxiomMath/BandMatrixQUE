module

public import BlockBand.SourceProcess.FullSourceGenerator.LimitPath
public import BlockBand.Transmission.LawDuality.SubLimitMetric

/-!
# fdd convergence at arbitrary times, and the abstract existence of limits

* `tendsto_fdd_dT`: fdd convergence at the dense times (weak convergence of the path laws).
* `tendsto_lip`: bounded Lipschitz tests at arbitrary times `≥ t₀` (dense times nearby, the
  `Modulus` for `n` large, dominated convergence on the limit side).
* `tendsto_fdd`: every bounded continuous test (`tendsto_iff_forall_lipschitz_integral_tendsto`).
* **`exists_limit`**: under `AEMeas`, `OneTimeTight` and `Modulus`, a subsequence `ms` and a
  probability `P` on `ℕ → ℂ` such that the `extPath t₀ a` are measurable, a.s. continuous on
  `[t₀, ∞)`, and the fdd of `X (ms n)` converge to theirs.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator.WordLim

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {t₀ : ℝ} {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {Ps : ∀ n, Measure (Ωs n)}
  {X : ∀ n, ℕ → ℝ → Ωs n → ℂ}

theorem ae_mem_goodSet {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hG : (Q : Measure (ℕ → ℂ)) (goodSet t₀)ᶜ = 0) :
    ∀ᵐ ω ∂(Q : Measure (ℕ → ℂ)), ω ∈ goodSet t₀ := ae_iff.2 hG

/-- **fdd convergence at the dense times.** -/
theorem tendsto_fdd_dT [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas t₀ Ps X)
    {Q : ProbabilityMeasure (ℕ → ℂ)} {ms : ℕ → ℕ}
    (hQ : Tendsto (fun n => lawY t₀ Ps X (ms n)) atTop (𝓝 Q))
    (hG : (Q : Measure (ℕ → ℂ)) (goodSet t₀)ᶜ = 0) {k : ℕ} (as js : Fin k → ℕ)
    (Φ : BoundedContinuousFunction (Fin k → ℂ) ℝ) :
    Tendsto (fun n => ∫ ω, Φ (fun l => X (ms n) (as l) (dT t₀ (js l)) ω) ∂Ps (ms n)) atTop
      (𝓝 (∫ ω, Φ (fun l => extPath t₀ (as l) ω (dT t₀ (js l))) ∂(Q : Measure (ℕ → ℂ)))) := by
  let π : C(ℕ → ℂ, Fin k → ℂ) :=
    ⟨fun ω l => ω (Nat.pair (as l) (js l)), continuous_pi fun l => continuous_apply _⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hQ) (Φ.compContinuous π)
  have e1 : ∀ n, ∫ ω, (Φ.compContinuous π) ω ∂((lawY t₀ Ps X (ms n) :
      ProbabilityMeasure _) : Measure (ℕ → ℂ)) =
        ∫ ω, Φ (fun l => X (ms n) (as l) (dT t₀ (js l)) ω) ∂Ps (ms n) := fun n => by
    rw [show ((lawY t₀ Ps X (ms n) : ProbabilityMeasure _) : Measure (ℕ → ℂ)) =
      (Ps (ms n)).map (pathY t₀ X (ms n)) from rfl,
      integral_map (aemeasurable_pathY hX _) (Φ.compContinuous π).continuous.aestronglyMeasurable]
    simp [π, pathY, Nat.unpair_pair]
  have e2 : ∫ ω, (Φ.compContinuous π) ω ∂(Q : Measure (ℕ → ℂ)) =
      ∫ ω, Φ (fun l => extPath t₀ (as l) ω (dT t₀ (js l))) ∂(Q : Measure (ℕ → ℂ)) := by
    refine integral_congr_ae ((ae_mem_goodSet hG).mono fun ω hω => ?_)
    simp [π, extPath_dT hω]
  simpa only [e1, e2] using h

theorem exists_small_delta {k : ℕ} {δ : Fin k → ℝ} (hδ : ∀ l, 0 < δ l) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ (∀ l, δ₀ ≤ δ l) ∧ δ₀ ≤ 1 := by
  obtain ⟨A, hA⟩ := Finite.exists_le fun l : Fin k => 1 / δ l
  set M := max A 1
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1 / M, by positivity, fun l => ?_, ?_⟩
  · have h := (hA l).trans (le_max_left _ _ : A ≤ M)
    rw [div_le_iff₀ (hδ l)] at h
    rw [div_le_iff₀ hM]; linarith [mul_comm M (δ l)]
  · rw [div_le_one hM]; exact le_max_right _ _

/-- **Bounded Lipschitz tests at arbitrary times `≥ t₀`.** -/
theorem tendsto_lip [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas t₀ Ps X)
    (hM : Modulus t₀ Ps X) {Q : ProbabilityMeasure (ℕ → ℂ)} {ms : ℕ → ℕ}
    (hms : StrictMono ms) (hQ : Tendsto (fun n => lawY t₀ Ps X (ms n)) atTop (𝓝 Q))
    (hG : (Q : Measure (ℕ → ℂ)) (goodSet t₀)ᶜ = 0) {k : ℕ} (as : Fin k → ℕ) (τ : Fin k → ℝ)
    (hτ : ∀ l, t₀ ≤ τ l) {f : (Fin k → ℂ) → ℝ} {C : ℝ} (hC : ∀ x y, dist (f x) (f y) ≤ C)
    {K : ℝ≥0} (hK : LipschitzWith K f) :
    Tendsto (fun n => ∫ ω, f (fun l => X (ms n) (as l) (τ l) ω) ∂Ps (ms n)) atTop
      (𝓝 (∫ ω, f (fun l => extPath t₀ (as l) ω (τ l)) ∂(Q : Measure (ℕ → ℂ)))) := by
  have hC0 : 0 ≤ C := le_trans dist_nonneg (hC (fun _ => 0) (fun _ => 0))
  let fb : BoundedContinuousFunction (Fin k → ℂ) ℝ := ⟨⟨f, hK.continuous⟩, ⟨C, hC⟩⟩
  have hbd : ∀ x, ‖f x‖ ≤ |f (fun _ => 0)| + C := fun x => by
    have := hC x (fun _ => 0)
    rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (f x) (f (fun _ => 0))
    rw [Real.norm_eq_abs]; linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e := ε / 4 with he
  have he0 : 0 < e := by positivity
  set η : ℝ := e / ((K : ℝ) + 1) with hη_def
  have hη : 0 < η := by positivity
  have hKη : (K : ℝ) * η ≤ e := by
    rw [hη_def, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  set θ : ℝ := e / ((C + 1) * ((k : ℝ) + 1)) with hθ_def
  have hθ : 0 < θ := by positivity
  have hCθ : C * ((k : ℝ) * θ) ≤ e := by
    rw [hθ_def, show C * ((k : ℝ) * (e / ((C + 1) * ((k : ℝ) + 1)))) =
      e * ((C / (C + 1)) * (k / (k + 1))) by field_simp]
    refine mul_le_of_le_one_right he0.le ?_
    have h1 : C / (C + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have h2 : (k : ℝ) / (k + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have h3 : 0 ≤ (k : ℝ) / (k + 1) := by positivity
    nlinarith
  choose δ hδ N hN using fun l : Fin k => hM (as l) (τ l + 1) η θ hη hθ
  obtain ⟨δ₀, hδ₀, hδ₀δ, hδ₀1⟩ := exists_small_delta hδ
  obtain ⟨N₁, hN₁⟩ := Finite.exists_le N
  set τ' : ℕ → Fin k → ℝ := fun m l => dT t₀ (seqT t₀ (τ l) m)
  have hτ' : ∀ l, Tendsto (fun m => τ' m l) atTop (𝓝 (τ l)) := fun l => tendsto_seqT (hτ l)
  have hev1 : ∀ᶠ m in atTop, ∀ l, |τ' m l - τ l| ≤ δ₀ :=
    eventually_all.2 fun l => (eventually_near (hτ' l) hδ₀).mono fun _ h => h.le
  have hdct : Tendsto (fun m => ∫ ω, f (fun l => extPath t₀ (as l) ω (τ' m l))
      ∂(Q : Measure (ℕ → ℂ))) atTop
      (𝓝 (∫ ω, f (fun l => extPath t₀ (as l) ω (τ l)) ∂(Q : Measure (ℕ → ℂ)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => |f (fun _ => 0)| + C)
      (fun m => ?_) (integrable_const _) (fun m => Eventually.of_forall fun ω => hbd _)
      ((ae_mem_goodSet hG).mono fun ω hω => ?_)
    · exact (hK.continuous.measurable.comp (measurable_pi_iff.2 fun l =>
        measurable_extPath (as l) (le_dT t₀ _))).aestronglyMeasurable
    · have : Tendsto (fun m => fun l => extPath t₀ (as l) ω (τ' m l)) atTop
          (𝓝 (fun l => extPath t₀ (as l) ω (τ l))) := tendsto_pi_nhds.2 fun l =>
        ((continuousOn_extPath hω (as l)) (τ l) (hτ l)).tendsto.comp
          (tendsto_nhdsWithin_iff.2 ⟨hτ' l, Eventually.of_forall fun m => le_dT t₀ _⟩)
      exact (hK.continuous.tendsto _).comp this
  have hev2 : ∀ᶠ m in atTop, dist (∫ ω, f (fun l => extPath t₀ (as l) ω (τ' m l))
      ∂(Q : Measure (ℕ → ℂ))) (∫ ω, f (fun l => extPath t₀ (as l) ω (τ l))
        ∂(Q : Measure (ℕ → ℂ))) < e :=
    (Metric.tendsto_nhds.1 hdct) e he0
  obtain ⟨m, hm1, hm2⟩ := (hev1.and hev2).exists
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1
    (tendsto_fdd_dT hX hQ hG as (fun l => seqT t₀ (τ l) m) fb) e he0
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : ∀ l, N l ≤ ms n := fun l =>
    (hN₁ l).trans ((le_max_left _ _).trans (hn.trans (hms.id_le n)))
  have h2 := hN₂ n ((le_max_right _ _).trans hn)
  let Bs : Fin k → Set (Ωs (ms n)) := fun l => {ω | ∃ t ∈ Icc t₀ (τ l + 1),
    ∃ t' ∈ Icc t₀ (τ l + 1), |t - t'| ≤ δ l ∧
      η < ‖X (ms n) (as l) t ω - X (ms n) (as l) t' ω‖}
  have hB : (Ps (ms n) (⋃ l, Bs l)).toReal ≤ k * θ := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((measure_iUnion_fintype_le _ _).trans ?_)
    refine (Finset.sum_le_sum fun l _ => hN l (ms n) (hn1 l)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  have h1 := BlockBand.Transmission.LawDuality.SubLimit.abs_integral_sub_le (P := Ps (ms n))
    (AEMeasurable.of_eval fun l => hX _ _ _ (hτ l))
    (AEMeasurable.of_eval fun l => hX _ _ _ (le_dT t₀ (seqT t₀ (τ l) m))) hK hC
    (B := ⋃ l, Bs l) hη.le (fun ω hω => by
      refine (dist_pi_le_iff hη.le).2 fun l => ?_
      by_contra hlt
      refine hω (mem_iUnion.2 ⟨l, ?_⟩)
      have hd := hm1 l
      rw [abs_le] at hd
      have hτl := hτ l
      have h0 : t₀ ≤ τ' m l := le_dT t₀ _
      refine ⟨τ l, ⟨hτl, by linarith⟩, τ' m l, ⟨h0, by linarith⟩, ?_, ?_⟩
      · rw [abs_sub_comm, abs_le]
        have := hδ₀δ l
        exact ⟨by linarith, by linarith⟩
      · rw [← dist_eq_norm]; exact not_le.1 hlt)
  rw [Real.dist_eq] at h2 hm2 ⊢
  have h3 : C * (Ps (ms n) (⋃ l, Bs l)).toReal ≤ C * ((k : ℝ) * θ) :=
    mul_le_mul_of_nonneg_left hB hC0
  have := abs_sub_le (∫ ω, f (fun l => X (ms n) (as l) (τ l) ω) ∂Ps (ms n))
    (∫ ω, f (fun l => X (ms n) (as l) (τ' m l) ω) ∂Ps (ms n))
    (∫ ω, f (fun l => extPath t₀ (as l) ω (τ l)) ∂(Q : Measure (ℕ → ℂ)))
  have := abs_sub_le (∫ ω, f (fun l => X (ms n) (as l) (τ' m l) ω) ∂Ps (ms n))
    (∫ ω, f (fun l => extPath t₀ (as l) ω (τ' m l)) ∂(Q : Measure (ℕ → ℂ)))
    (∫ ω, f (fun l => extPath t₀ (as l) ω (τ l)) ∂(Q : Measure (ℕ → ℂ)))
  have h2' : |∫ ω, f (fun l => X (ms n) (as l) (τ' m l) ω) ∂Ps (ms n) -
      ∫ ω, f (fun l => extPath t₀ (as l) ω (τ' m l)) ∂(Q : Measure (ℕ → ℂ))| < e := h2
  linarith

/-- **fdd convergence at every finite family of times `≥ t₀`.** -/
theorem tendsto_fdd [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas t₀ Ps X)
    (hM : Modulus t₀ Ps X) {Q : ProbabilityMeasure (ℕ → ℂ)} {ms : ℕ → ℕ}
    (hms : StrictMono ms) (hQ : Tendsto (fun n => lawY t₀ Ps X (ms n)) atTop (𝓝 Q))
    (hG : (Q : Measure (ℕ → ℂ)) (goodSet t₀)ᶜ = 0) {k : ℕ} (as : Fin k → ℕ) (τ : Fin k → ℝ)
    (hτ : ∀ l, t₀ ≤ τ l) (Φ : BoundedContinuousFunction (Fin k → ℂ) ℝ) :
    Tendsto (fun n => ∫ ω, Φ (fun l => X (ms n) (as l) (τ l) ω) ∂Ps (ms n)) atTop
      (𝓝 (∫ ω, Φ (fun l => extPath t₀ (as l) ω (τ l)) ∂(Q : Measure (ℕ → ℂ)))) := by
  have hZ : ∀ n, AEMeasurable (fun ω l => X (ms n) (as l) (τ l) ω) (Ps (ms n)) := fun n =>
    AEMeasurable.of_eval fun l => hX _ _ _ (hτ l)
  have hZ' : Measurable fun (ω : ℕ → ℂ) l => extPath t₀ (as l) ω (τ l) :=
    measurable_pi_iff.2 fun l => measurable_extPath (as l) (hτ l)
  let L : ℕ → ProbabilityMeasure (Fin k → ℂ) := fun n =>
    ⟨(Ps (ms n)).map (fun ω l => X (ms n) (as l) (τ l) ω), inferInstance⟩
  let L' : ProbabilityMeasure (Fin k → ℂ) :=
    ⟨(Q : Measure (ℕ → ℂ)).map (fun ω l => extPath t₀ (as l) ω (τ l)), inferInstance⟩
  have hL : Tendsto L atTop (𝓝 L') := by
    refine (tendsto_iff_forall_lipschitz_integral_tendsto (μs := L) (μ := L')).2
      fun f ⟨C, hC⟩ ⟨K, hK⟩ => ?_
    have hf := hK.continuous.aestronglyMeasurable (μ := (L' : Measure (Fin k → ℂ)))
    rw [show ∫ x, f x ∂(L' : Measure (Fin k → ℂ)) = ∫ ω, f (fun l => extPath t₀ (as l) ω (τ l))
        ∂(Q : Measure (ℕ → ℂ)) from integral_map hZ'.aemeasurable hf]
    have e : ∀ n, ∫ x, f x ∂(L n : Measure (Fin k → ℂ)) =
        ∫ ω, f (fun l => X (ms n) (as l) (τ l) ω) ∂Ps (ms n) := fun n =>
      integral_map (hZ n) hK.continuous.aestronglyMeasurable
    simp_rw [e]
    exact tendsto_lip hX hM hms hQ hG as τ hτ hC hK
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hL) Φ
  have e1 : ∀ n, ∫ x, Φ x ∂(L n : Measure (Fin k → ℂ)) =
      ∫ ω, Φ (fun l => X (ms n) (as l) (τ l) ω) ∂Ps (ms n) := fun n =>
    integral_map (hZ n) Φ.continuous.aestronglyMeasurable
  have e2 : ∫ x, Φ x ∂(L' : Measure (Fin k → ℂ)) =
      ∫ ω, Φ (fun l => extPath t₀ (as l) ω (τ l)) ∂(Q : Measure (ℕ → ℂ)) :=
    integral_map hZ'.aemeasurable Φ.continuous.aestronglyMeasurable
  simpa only [e1, e2] using this

/-- **Subsequential limits exist** (abstract form). -/
theorem exists_limit [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas t₀ Ps X)
    (hT : OneTimeTight t₀ Ps X) (hM : Modulus t₀ Ps X) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∃ P : Measure (ℕ → ℂ), IsProbabilityMeasure P ∧
      (∀ a t, t₀ ≤ t → Measurable fun ω => extPath t₀ a ω t) ∧
      (∀ a, ∀ᵐ ω ∂P, ContinuousOn (fun t => extPath t₀ a ω t) (Ici t₀)) ∧
      ∀ (k : ℕ) (as : Fin k → ℕ) (τ : Fin k → ℝ), (∀ l, t₀ ≤ τ l) →
        ∀ Φ : BoundedContinuousFunction (Fin k → ℂ) ℝ,
          Tendsto (fun n => ∫ ω, Φ (fun l => X (ms n) (as l) (τ l) ω) ∂Ps (ms n)) atTop
            (𝓝 (∫ ω, Φ (fun l => extPath t₀ (as l) ω (τ l)) ∂P)) := by
  obtain ⟨Q, ms, hms, hQ⟩ := exists_tendsto_lawY hX hT
  have hG := ae_goodSet hX hM hms hQ
  exact ⟨ms, hms, Q, inferInstance, fun a t ht => measurable_extPath a ht,
    fun a => (ae_mem_goodSet hG).mono fun ω hω => continuousOn_extPath hω a,
    fun k as τ hτ Φ => tendsto_fdd hX hM hms hQ hG as τ hτ Φ⟩

end BlockBand.SourceProcess.FullSourceGenerator.WordLim
