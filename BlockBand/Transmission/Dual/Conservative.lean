module

public import BlockBand.Transmission.Dual.LevelStep
public import BlockBand.Transmission.Dual.Normalize

/-!
# `conservative`: `P(∃ t ≤ T, R_t ≥ K) ≤ R₀/K`

* `expect_capped_total`: for a normalized realization, `E R_{T∧τ_K} = R₀` (telescoping the
  level steps `E[R_{ρ∧σ_{q-1}} − R_{ρ∧σ_q}] = 0`, `q = p, …, 1`; `R = 0` on the empty state).
* Markov's inequality on `{R_{T∧τ_K} ≥ K} ⊇ {∃ t ≤ T, R_t ≥ K}` (path continuity of `R`).
* The general case reduces to a normalized version (`exists_normalized`), which agrees
  with the original a.s. at all times. No Gronwall or uniform-integrability step is needed: the
  capped total is bounded by `K`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 m} {D0 : ℝ} {p : ℕ} {x y : Fin p → ℝ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

omit m in
theorem dualTotal_start {ω : Ω} (hs : N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i) :
    dualTotal (N 0 ω) (X 0 ω) (Y 0 ω) = ∑ i, (x i + y i) := by
  rw [hs.1, dualTotal, ← Fin.sum_univ_eq_sum_range (fun i => X 0 ω i + Y 0 ω i) p]
  exact Finset.sum_congr rfl fun i _ => by rw [(hs.2 i).1, (hs.2 i).2]

/-- **`E R_{T∧τ_K} = R₀`** for a normalized realization with `R₀ < K`. -/
theorem expect_capped_total (h : IsDualDeletionProcess P 𝓕 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i) {K : ℝ}
    (hK : ∑ i, (x i + y i) < K) (T : ℝ≥0) :
    Integrable (stopTotal N X Y K T 0) P ∧ ∫ ω, stopTotal N X Y K T 0 ω ∂P = ∑ i, (x i + y i) := by
  have hK' : ∀ ω, dualTotal (N 0 ω) (X 0 ω) (Y 0 ω) < K := fun ω => by
    rw [dualTotal_start (hstart ω)]; exact hK
  have htop : stopTotal N X Y K T p = fun _ => ∑ i, (x i + y i) := by
    funext ω
    have h0 : entryTime (fun t => N t ω) p = ((0 : ℝ≥0) : WithTop ℝ≥0) :=
      le_antisymm (iInf₂_le 0 (hstart ω).1.le) (by rw [WithTop.coe_zero]; exact zero_le)
    have hmin : min (capTime N X Y K T ω : WithTop ℝ≥0) (entryTime (fun t => N t ω) p) =
        ((0 : ℝ≥0) : WithTop ℝ≥0) := by
      rw [h0]; exact min_eq_right (by rw [WithTop.coe_zero]; exact zero_le)
    simp only [stopTotal, hmin, untopA_coe']
    exact dualTotal_start (hstart ω)
  have step : ∀ j, j ≤ p → Integrable (stopTotal N X Y K T (p - j)) P ∧
      ∫ ω, stopTotal N X Y K T (p - j) ω ∂P = ∑ i, (x i + y i) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, htop]
      exact ⟨integrable_const _, by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨hI, hE⟩ := ih (by omega)
      obtain ⟨hI', hE'⟩ := levelStep h hpath (fun ω => (hstart ω).1) hK' T
        (q := p - j) (by omega) (by omega)
      have he : p - (j + 1) = p - j - 1 := by omega
      rw [he]
      have hsum : stopTotal N X Y K T (p - j - 1) = fun ω =>
          (stopTotal N X Y K T (p - j - 1) ω - stopTotal N X Y K T (p - j) ω) +
            stopTotal N X Y K T (p - j) ω := by funext ω; ring
      rw [hsum]
      exact ⟨hI'.add hI, by rw [integral_add hI' hI, hE', hE, zero_add]⟩
  simpa using step p le_rfl

omit m in
/-- At level `0` the capped total is `R` at `T ∧ τ_K`. -/
theorem stopTotal_zero_eq (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω)
    (fun t => Y t ω)) (K : ℝ) (T : ℝ≥0) (ω : Ω) :
    stopTotal N X Y K T 0 ω = dualTotal (N (capTime N X Y K T ω) ω)
      (X (capTime N X Y K T ω) ω) (Y (capTime N X Y K T ω) ω) := by
  unfold stopTotal
  by_cases he : entryTime (fun t => N t ω) 0 ≤ (capTime N X Y K T ω : WithTop ℝ≥0)
  · obtain ⟨e, hee⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top he)
    rw [min_eq_right he, ← hee, untopA_coe']
    have hne : N e ω ≤ 0 := (entryTime_le_iff (hpath ω) 0 e).1 hee.symm.le
    have hce : e ≤ capTime N X Y K T ω := WithTop.coe_le_coe.1 (hee ▸ he)
    have hnc : N (capTime N X Y K T ω) ω = 0 := by
      have h1 : N (capTime N X Y K T ω) ω ≤ N e ω := (hpath ω).antitone hce
      omega
    have hne' : N e ω = 0 := by omega
    simp [pathTotal, dualTotal, hne', hnc]
  · rw [min_eq_left (not_le.1 he).le, untopA_coe']
    rfl

/-- **`conservative` for a normalized realization.** -/
theorem conservative_of_normalized (h : IsDualDeletionProcess P 𝓕 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i) {K : ℝ}
    (hK0 : 0 < K) (T : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0, t ≤ T ∧ K ≤ dualTotal (N t ω) (X t ω) (Y t ω)} ≤
      ENNReal.ofReal ((∑ i, (x i + y i)) / K) := by
  by_cases hK : ∑ i, (x i + y i) < K
  · obtain ⟨hI, hE⟩ := expect_capped_total h hpath hstart hK T
    have hsub : {ω | ∃ t : ℝ≥0, t ≤ T ∧ K ≤ dualTotal (N t ω) (X t ω) (Y t ω)} ⊆
        {ω | K ≤ stopTotal N X Y K T 0 ω} := by
      rintro ω ⟨t, htT, ht⟩
      have hrc : ∀ s, Tendsto (fun u => -dualTotal (N u ω) (X u ω) (Y u ω)) (𝓝[≥] s)
          (𝓝 (-dualTotal (N s ω) (X s ω) (Y s ω))) := fun s =>
        (((continuous_total (hpath ω)).neg).tendsto s).mono_left nhdsWithin_le_nhds
      have hle : capHit N X Y K ω ≤ t := (hitLe_le_iff hrc t).2 ⟨t, le_rfl, by linarith⟩
      obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
      have hcT : (c : WithTop ℝ≥0) ≤ T := hc ▸ hle.trans (WithTop.coe_le_coe.2 htT)
      have hcap : capTime N X Y K T ω = c := by
        rw [capTime, ← hc, min_eq_right hcT, untopA_coe']
      have hatt := hitLe_attained hrc hc.symm
      simp only [mem_ofPred_eq]
      rw [stopTotal_zero_eq hpath, hcap]
      linarith
    have hnn : 0 ≤ᵐ[P] stopTotal N X Y K T 0 :=
      ae_of_all _ fun ω => by rw [stopTotal_zero_eq hpath]; exact dualTotal_nonneg (hpath ω) _
    have hmk := mul_meas_ge_le_integral_of_nonneg hnn hI K
    rw [hE] at hmk
    have hreal : P.real {ω | K ≤ stopTotal N X Y K T 0 ω} ≤ (∑ i, (x i + y i)) / K := by
      rw [le_div_iff₀ hK0]; linarith
    calc P {ω | ∃ t : ℝ≥0, t ≤ T ∧ K ≤ dualTotal (N t ω) (X t ω) (Y t ω)}
        ≤ P {ω | K ≤ stopTotal N X Y K T 0 ω} := measure_mono hsub
      _ = ENNReal.ofReal (P.real {ω | K ≤ stopTotal N X Y K T 0 ω}) :=
        (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal ((∑ i, (x i + y i)) / K) := ENNReal.ofReal_le_ofReal hreal
  · calc _ ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal ((∑ i, (x i + y i)) / K) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((one_le_div hK0).2 (not_lt.1 hK))

/-- **The `conservative` clause of `DualBoundaryLawStatement`.** -/
theorem conservative_holds : ∀ D0 : ℝ, 0 < D0 → ∀ (p : ℕ) (x y : Fin p → ℝ),
    IsRatioParameter x y →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ),
      IsDualDeletionProcess P 𝓖 D0 x y N X Y →
      ∀ K T : ℝ, 0 < K →
        P {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ K ≤ dualTotal (N t ω) (X t ω) (Y t ω)} ≤
          ENNReal.ofReal ((∑ i, (x i + y i)) / K) := by
  intro D0 _ p x y hxy Ω m 𝓖 P N X Y h K T hK0
  have := h.prob
  obtain ⟨N', X', Y', h', hpath', hstart', hae⟩ := exists_normalized hxy h
  by_cases hT : T < 0
  · have : {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ K ≤ dualTotal (N t ω) (X t ω) (Y t ω)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro t ht
      exact absurd (lt_of_le_of_lt (NNReal.coe_nonneg t) (lt_of_le_of_lt ht hT)) (lt_irrefl 0)
    rw [this, measure_empty]; exact zero_le
  have hT' : 0 ≤ T := not_lt.1 hT
  set B : Set Ω := {ω | ¬ ∀ t, N' t ω = N t ω ∧ X' t ω = X t ω ∧ Y' t ω = Y t ω}
  have hB : P B = 0 := ae_iff.1 hae
  have hsub : {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ K ≤ dualTotal (N t ω) (X t ω) (Y t ω)} ⊆
      {ω | ∃ t : ℝ≥0, t ≤ T.toNNReal ∧ K ≤ dualTotal (N' t ω) (X' t ω) (Y' t ω)} ∪ B := by
    rintro ω ⟨t, htT, ht⟩
    by_cases hω : ω ∈ B
    · exact Or.inr hω
    · left
      have he : ∀ t, N' t ω = N t ω ∧ X' t ω = X t ω ∧ Y' t ω = Y t ω := not_not.1 hω
      refine ⟨t, ?_, ?_⟩
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hT']; exact htT
      · obtain ⟨h1, h2, h3⟩ := he t; rw [h1, h2, h3]; exact ht
  calc _ ≤ P ({ω | ∃ t : ℝ≥0, t ≤ T.toNNReal ∧ K ≤ dualTotal (N' t ω) (X' t ω) (Y' t ω)} ∪ B) :=
        measure_mono hsub
    _ ≤ P {ω | ∃ t : ℝ≥0, t ≤ T.toNNReal ∧ K ≤ dualTotal (N' t ω) (X' t ω) (Y' t ω)} + P B :=
        measure_union_le _ _
    _ ≤ _ := by
        rw [hB, add_zero]
        exact conservative_of_normalized h' hpath' hstart' hK0 T.toNNReal

end BlockBand.Transmission.Dual
