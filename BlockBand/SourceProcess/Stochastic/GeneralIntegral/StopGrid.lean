module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.StopRect
public import BlockBand.SourceProcess.Stochastic.Integral.Dyadic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Stopping the general integral at grid-valued and bounded random times

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, `h : IsL2Integrator Q 𝓖 N α`,
horizon `T`, `ν_T = bracketMeasure Q α T`, `H ∈ PredL2 𝓖 ν_T`, `Z = h.contIntegral T H`.
For `ρ : Ω → ℝ≥0`, `stopSet ρ = [[0, ρ]] = {(s, ω) | s⁺ ≤ ρ ω}`.

* `stochIntegral_grid`: if `ρ` takes values in `δ ℕ` and `{ρ ≤ K δ} ∈ 𝓖_{K δ}` for all `K`,
  then for every `K`, `[[0, ρ ∧ K δ]]` is predictable and
  `∫_0^T 1_{[[0, ρ ∧ K δ]]} H dN = Z_{ρ ∧ K δ}` a.s. Induction on `K`: the new layer is the
  predictable rectangle `(K δ, (K+1) δ] × {ρ > K δ}` (`stochIntegral_predInd_rect`).
* `stochIntegral_stopSet_of_bounded`: if `σ ≤ u` and `{σ ≤ t} ∈ 𝓖_t` for all `t` (a bounded
  raw stopping time), then `∫_0^T 1_{[[0, σ]]} H dN = Z_σ` a.s. Proof: dyadic upper
  approximations `ρ_n = ⌈σ 2ⁿ⌉ 2⁻ⁿ ↓ σ`; the integrands converge in `L²(ν_T)` by dominated
  convergence, so the integrals converge in `L²(Q)` (isometry), while `Z_{ρ_n} → Z_σ` a.s. by
  a.s. path continuity; limits in measure are a.s. unique. (Mirrors native `Integral/Grid`,
  `Integral/Limit`, with raw instead of augmented events.)
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.Stochastic.Integral (dyadicUp dyadicStep dyadicStep_pos le_dyadicUp
  dyadicUp_le_iff dyadicUp_mono tendsto_dyadicUp tendsto_toLp_of_integral_sq grid_succ_le)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {N α : ℝ≥0 → Ω → ℝ}

omit mΩ in
theorem stopSet_coe_succ {δ : ℝ≥0} {ρ : Ω → ℝ≥0} (hgrid : ∀ ω, ∃ m : ℕ, ρ ω = m * δ) (K : ℕ) :
    stopSet (fun ω => ((min (ρ ω) (((K + 1 : ℕ) : ℝ≥0) * δ) : ℝ≥0) : WithTop ℝ≥0)) =
      stopSet (fun ω => ((min (ρ ω) ((K : ℝ≥0) * δ) : ℝ≥0) : WithTop ℝ≥0)) ∪
        Ioc (((K : ℝ≥0) * δ : ℝ≥0) : ℝ) ((((K + 1 : ℕ) : ℝ≥0) * δ : ℝ≥0) : ℝ) ×ˢ
          {ω | ρ ω ≤ (K : ℝ≥0) * δ}ᶜ := by
  have hab : (K : ℝ≥0) * δ ≤ ((K + 1 : ℕ) : ℝ≥0) * δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast K.le_succ) zero_le
  ext p
  simp only [stopSet, mem_ofPred_eq, mem_union, mem_prod, mem_Ioc, mem_compl_iff,
    WithTop.coe_le_coe, not_le]
  obtain ⟨m, hm⟩ := hgrid p.2
  by_cases hy : ρ p.2 ≤ K * δ
  · rw [min_eq_left hy, min_eq_left (hy.trans hab)]
    constructor
    · exact Or.inl
    · rintro (h | ⟨-, h⟩)
      · exact h
      · exact absurd hy (not_le.2 h)
  · have hb := grid_succ_le hm hy
    rw [min_eq_right (le_of_not_ge hy), min_eq_right hb]
    have hy' : (K : ℝ≥0) * δ < ρ p.2 := lt_of_not_ge hy
    constructor
    · intro hs
      by_cases hk : p.1.toNNReal ≤ K * δ
      · exact Or.inl hk
      · refine Or.inr ⟨⟨?_, ?_⟩, hy'⟩
        · have := lt_of_not_ge hk
          rwa [Real.lt_toNNReal_iff_coe_lt] at this
        · exact (Real.toNNReal_le_iff_le_coe).1 hs
    · rintro (h | ⟨⟨-, h⟩, -⟩)
      · exact h.trans hab
      · exact Real.toNNReal_le_iff_le_coe.2 h

theorem measurableSet_stopSet_grid {δ : ℝ≥0} {ρ : Ω → ℝ≥0} (hgrid : ∀ ω, ∃ m : ℕ, ρ ω = m * δ)
    (hρ : ∀ K : ℕ, MeasurableSet[𝓖 ((K : ℝ≥0) * δ)] {ω | ρ ω ≤ (K : ℝ≥0) * δ}) (K : ℕ) :
    MeasurableSet[predictableSpace (toCF 𝓖)]
      (stopSet (fun ω => ((min (ρ ω) ((K : ℝ≥0) * δ) : ℝ≥0) : WithTop ℝ≥0))) := by
  induction K with
  | zero =>
      have he : (fun ω => ((min (ρ ω) (((0 : ℕ) : ℝ≥0) * δ) : ℝ≥0) : WithTop ℝ≥0)) =
          fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0) := by
        funext ω; simp
      rw [he]
      exact measurableSet_stopSet 𝓖 (isStoppingTime_const 𝓖 0)
  | succ K ih =>
      rw [stopSet_coe_succ hgrid K]
      exact ih.union (measurableSet_rect_pred 𝓖 (hρ K).compl)

namespace IsL2Integrator

variable (h : IsL2Integrator Q 𝓖 N α) (T : ℝ≥0) (H : PredL2 𝓖 (bracketMeasure Q α T))

/-- **Grid stopping identity.** -/
theorem stochIntegral_grid {δ : ℝ≥0} {ρ : Ω → ℝ≥0} (hgrid : ∀ ω, ∃ m : ℕ, ρ ω = m * δ)
    (hρ : ∀ K : ℕ, MeasurableSet[𝓖 ((K : ℝ≥0) * δ)] {ω | ρ ω ≤ (K : ℝ≥0) * δ}) (K : ℕ) :
    (h.stochIntegral T (predInd 𝓖 _ (measurableSet_stopSet_grid hgrid hρ K) H) : Ω → ℝ) =ᵐ[Q]
      fun ω => h.contIntegral T H (min (ρ ω) ((K : ℝ≥0) * δ)) ω := by
  induction K with
  | zero =>
      have hnull : bracketMeasure Q α T
          (stopSet (fun ω => ((min (ρ ω) (((0 : ℕ) : ℝ≥0) * δ) : ℝ≥0) : WithTop ℝ≥0))) = 0 := by
        refine measure_mono_null (fun p hp => ?_) (ae_iff.1 (bracketMeasure_ae_mem Q α T))
        intro hm
        have h0 := mem_stopSet.1 hp
        simp only [WithTop.coe_le_coe, Nat.cast_zero, zero_mul, min_eq_right zero_le,
          Real.toNNReal_le_iff_le_coe, NNReal.coe_zero] at h0
        exact absurd h0 (not_le.2 hm.1)
      rw [predInd_null 𝓖 _ hnull, map_zero]
      refine (Lp.coeFn_zero _ _ _).trans (Eventually.of_forall fun ω => ?_)
      simp [h.contIntegral_zero T H]
  | succ K ih =>
      have hab : (K : ℝ≥0) * δ ≤ ((K + 1 : ℕ) : ℝ≥0) * δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast K.le_succ) zero_le
      have hS := measurableSet_stopSet_grid hgrid hρ K
      have hR := measurableSet_rect_pred 𝓖 (q₂ := ((K + 1 : ℕ) : ℝ≥0) * δ) (hρ K).compl
      have hdisj : Disjoint (stopSet (fun ω => ((min (ρ ω) ((K : ℝ≥0) * δ) : ℝ≥0) :
          WithTop ℝ≥0))) (Ioc (((K : ℝ≥0) * δ : ℝ≥0) : ℝ) ((((K + 1 : ℕ) : ℝ≥0) * δ : ℝ≥0) : ℝ)
            ×ˢ {ω | ρ ω ≤ (K : ℝ≥0) * δ}ᶜ) := by
        rw [Set.disjoint_left]
        rintro p hp ⟨⟨h1, -⟩, -⟩
        have h2 : p.1.toNNReal ≤ (K : ℝ≥0) * δ :=
          (WithTop.coe_le_coe.1 hp).trans (min_le_right _ _)
        exact absurd (Real.toNNReal_le_iff_le_coe.1 h2) (not_le.2 h1)
      have hEq : predInd 𝓖 _ (measurableSet_stopSet_grid hgrid hρ (K + 1)) H =
          predInd 𝓖 _ (hS.union hR) H :=
        predInd_congr 𝓖 _ _ (by rw [stopSet_coe_succ hgrid K]) H
      rw [hEq, predInd_union 𝓖 hS hR hdisj, map_add]
      filter_upwards [Lp.coeFn_add (h.stochIntegral T (predInd 𝓖 _ hS H))
          (h.stochIntegral T (predInd 𝓖 _ hR H)), ih,
        h.stochIntegral_predInd_rect T H hab (hρ K).compl] with ω h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3]
      obtain ⟨m, hm⟩ := hgrid ω
      by_cases hy : ρ ω ≤ K * δ
      · rw [indicator_of_notMem
            (show ω ∉ {ω | ρ ω ≤ (K : ℝ≥0) * δ}ᶜ from Set.notMem_compl_iff.2 hy),
          add_zero, min_eq_left hy,
          min_eq_left (hy.trans hab)]
      · rw [indicator_of_mem hy, min_eq_right (le_of_not_ge hy),
          min_eq_right (grid_succ_le hm hy)]
        ring

/-- **Stopping identity at a bounded raw stopping time** `σ ≤ u`. -/
theorem stochIntegral_stopSet_of_bounded {σ : Ω → ℝ≥0} {u : ℝ≥0} (hσu : ∀ ω, σ ω ≤ u)
    (hσ : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | σ ω ≤ t}) :
    ∃ hS : MeasurableSet[predictableSpace (toCF 𝓖)]
        (stopSet fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)),
      (h.stochIntegral T (predInd 𝓖 _ hS H) : Ω → ℝ) =ᵐ[Q]
        fun ω => h.contIntegral T H (σ ω) ω := by
  have := h.isFiniteMeasure_bracketMeasure T
  have hστ : IsStoppingTime 𝓖 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0) := fun t => by
    simpa only [WithTop.coe_le_coe] using hσ t
  have hS := measurableSet_stopSet 𝓖 hστ
  refine ⟨hS, ?_⟩
  let ρ : ℕ → Ω → ℝ≥0 := fun n ω => dyadicUp n (σ ω)
  have hgrid (n : ℕ) (ω : Ω) : ∃ m : ℕ, ρ n ω = m * dyadicStep n := ⟨_, rfl⟩
  have hρ (n K : ℕ) : MeasurableSet[𝓖 ((K : ℝ≥0) * dyadicStep n)]
      {ω | ρ n ω ≤ (K : ℝ≥0) * dyadicStep n} := by
    have he : {ω | ρ n ω ≤ (K : ℝ≥0) * dyadicStep n} = {ω | σ ω ≤ K * dyadicStep n} := by
      ext ω; exact dyadicUp_le_iff n K (σ ω)
    rw [he]; exact hσ _
  set Kn : ℕ → ℕ := fun n => ⌈u / dyadicStep n⌉₊
  have hmin (n : ℕ) (ω : Ω) : min (ρ n ω) ((Kn n : ℝ≥0) * dyadicStep n) = ρ n ω :=
    min_eq_left (dyadicUp_mono n (hσu ω))
  have hSn (n : ℕ) := measurableSet_stopSet_grid (hgrid n) (hρ n) (Kn n)
  have hI (n : ℕ) : (h.stochIntegral T (predInd 𝓖 _ (hSn n) H) : Ω → ℝ) =ᵐ[Q]
      fun ω => h.contIntegral T H (ρ n ω) ω := by
    simpa only [hmin] using h.stochIntegral_grid T H (hgrid n) (hρ n) (Kn n)
  -- `L²(ν_T)` convergence of the stopped integrands
  set Sn : ℕ → Set (ℝ × Ω) := fun n =>
    stopSet (fun ω => ((min (ρ n ω) ((Kn n : ℝ≥0) * dyadicStep n) : ℝ≥0) : WithTop ℝ≥0))
  set S := stopSet fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)
  set g : ℝ × Ω → ℝ := ((H : Lp ℝ 2 (bracketMeasure Q α T)) : ℝ × Ω → ℝ)
  have hSnm (n : ℕ) : MeasurableSet (Sn n) := predictableSpace_le _ _ (hSn n)
  have hSm : MeasurableSet S := predictableSpace_le _ _ hS
  have hGn (n : ℕ) : MemLp ((Sn n).indicator g) 2 (bracketMeasure Q α T) :=
    (Lp.memLp _).indicator (hSnm n).nullMeasurableSet
  have hG0 : MemLp (S.indicator g) 2 (bracketMeasure Q α T) :=
    (Lp.memLp _).indicator hSm.nullMeasurableSet
  have hpt (p : ℝ × Ω) : Tendsto (fun n => (Sn n).indicator g p) atTop (𝓝 (S.indicator g p)) := by
    have hmem (n : ℕ) : p ∈ Sn n ↔ p.1.toNNReal ≤ ρ n p.2 := by
      simp only [Sn, mem_stopSet, hmin, WithTop.coe_le_coe]
    by_cases hp : p.1.toNNReal ≤ σ p.2
    · have hpS : p ∈ S := mem_stopSet.2 (WithTop.coe_le_coe.2 hp)
      have he (n : ℕ) : (Sn n).indicator g p = S.indicator g p := by
        rw [indicator_of_mem ((hmem n).2 (hp.trans (le_dyadicUp n _))), indicator_of_mem hpS]
      simp only [he]
      exact tendsto_const_nhds
    · have hpS : p ∉ S := fun hm => hp (WithTop.coe_le_coe.1 (mem_stopSet.1 hm))
      have hev : ∀ᶠ n in atTop, dyadicUp n (σ p.2) < p.1.toNNReal :=
        (tendsto_dyadicUp (σ p.2)).eventually (gt_mem_nhds (lt_of_not_ge hp))
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with n hn
      rw [indicator_of_notMem hpS, indicator_of_notMem fun hm => not_le.2 hn ((hmem n).1 hm)]
  have hint : Tendsto (fun n => ∫ p, ((Sn n).indicator g p - S.indicator g p) ^ 2
      ∂(bracketMeasure Q α T)) atTop (𝓝 0) := by
    have hFm (n : ℕ) : AEStronglyMeasurable
        (fun p => ((Sn n).indicator g p - S.indicator g p) ^ 2) (bracketMeasure Q α T) :=
      (continuous_pow 2).comp_aestronglyMeasurable
        ((hGn n).aestronglyMeasurable.sub hG0.aestronglyMeasurable)
    have hgi : Integrable (fun p => (g p) ^ 2) (bracketMeasure Q α T) :=
      (Lp.memLp (H : Lp ℝ 2 (bracketMeasure Q α T))).integrable_sq
    have hd := tendsto_integral_of_dominated_convergence
      (F := fun n p => ((Sn n).indicator g p - S.indicator g p) ^ 2) (f := fun _ => 0)
      (fun p => (g p) ^ 2) hFm hgi
      (fun n => ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        by_cases h1 : p ∈ Sn n <;> by_cases h2 : p ∈ S <;> simp [h1, h2] <;> positivity)
      (ae_of_all _ fun p => by
        have ht := ((hpt p).sub_const (S.indicator g p)).pow 2
        rwa [sub_self, zero_pow two_ne_zero] at ht)
    simpa only [integral_zero] using hd
  have hLp := tendsto_toLp_of_integral_sq hGn hG0 hint
  have hcoe (n : ℕ) : ((predInd 𝓖 _ (hSn n) H : PredL2 𝓖 (bracketMeasure Q α T)) :
      Lp ℝ 2 (bracketMeasure Q α T)) = (hGn n).toLp _ :=
    Lp.ext ((predInd_coeFn 𝓖 _ (hSn n) H).trans (MemLp.coeFn_toLp _).symm)
  have hcoe0 : ((predInd 𝓖 _ hS H : PredL2 𝓖 (bracketMeasure Q α T)) :
      Lp ℝ 2 (bracketMeasure Q α T)) = hG0.toLp _ :=
    Lp.ext ((predInd_coeFn 𝓖 _ hS H).trans (MemLp.coeFn_toLp _).symm)
  have hpred : Tendsto (fun n => predInd 𝓖 _ (hSn n) H) atTop (𝓝 (predInd 𝓖 _ hS H)) := by
    rw [tendsto_subtype_rng]
    simp only [hcoe, hcoe0]
    exact hLp
  have hItend := ((h.stochIntegral T).continuous.tendsto _).comp hpred
  have hmeas := (tendstoInMeasure_of_tendsto_Lp hItend).congr_left hI
  have hae : ∀ᵐ ω ∂Q, Tendsto (fun n => h.contIntegral T H (ρ n ω) ω) atTop
      (𝓝 (h.contIntegral T H (σ ω) ω)) := by
    filter_upwards [h.contIntegral_continuous T H] with ω hω
    exact (hω.tendsto (σ ω)).comp (tendsto_dyadicUp (σ ω))
  have hmeas2 := tendstoInMeasure_of_tendsto_ae
    (fun n => (Lp.aestronglyMeasurable (h.stochIntegral T (predInd 𝓖 _ (hSn n) H))).congr
      (hI n)) hae
  exact tendstoInMeasure_ae_unique hmeas hmeas2

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
