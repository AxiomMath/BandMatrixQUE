module

public import BlockBand.Palm.RelativeLocalizationSpectral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Relative localization: Markov with a vanishing exceptional sequence; far labels

* `markov_limit` : if `Bad ⊆ B₁ ∪ Nul ∪ G n ∪ {thr < X n}` for every `n`, with `μ Nul = 0`,
  `μ (G n) → 0` and `∫ X n ≤ e₂` (`X n ≥ 0` measurable, integrable), then
  `μ Bad ≤ μ B₁ + e₂/thr` (outer measures; `Bad`, `B₁` arbitrary sets).
* `far_from_label` : with the upper count `#{λ_i ∈ [x,y]} ≤ CN((y-x)+h)` and increasing
  labels, `|j - k| > R ≥ 0` forces `|λ_j - λ_k| ≥ R/(CN) - h`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory Set Filter Topology BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal

theorem markov_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X : Ω → ℝ}
    (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (hXi : Integrable X μ) {thr e₂ : ℝ}
    (hthr : 0 < thr) (hXe : ∫ ω, X ω ∂μ ≤ e₂) :
    μ {ω | thr < X ω} ≤ ENNReal.ofReal (e₂ / thr) := by
  have hsub : {ω | thr < X ω} ⊆ {ω | ENNReal.ofReal thr ≤ ENNReal.ofReal (X ω)} := fun ω hω =>
    ENNReal.ofReal_le_ofReal hω.le
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp hXm).aemeasurable
    (by simp [hthr]) ENNReal.ofReal_ne_top).trans ?_
  simp only [Function.comp_def]
  rw [← ofReal_integral_eq_lintegral_ofReal hXi (Eventually.of_forall hX0),
    ← ENNReal.ofReal_div_of_pos hthr]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hXe hthr.le)

theorem markov_limit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Bad B₁ Nul : Set Ω)
    (G : ℕ → Set Ω) (X : ℕ → Ω → ℝ) {thr e₂ : ℝ} (hthr : 0 < thr) (hNul : μ Nul = 0)
    (hG : Tendsto (fun n => μ (G n)) atTop (𝓝 0)) (hXm : ∀ n, Measurable (X n))
    (hX0 : ∀ n ω, 0 ≤ X n ω) (hXi : ∀ n, Integrable (X n) μ)
    (hXe : ∀ n, ∫ ω, X n ω ∂μ ≤ e₂)
    (hsub : ∀ n, Bad ⊆ B₁ ∪ Nul ∪ G n ∪ {ω | thr < X n ω}) :
    μ Bad ≤ μ B₁ + ENNReal.ofReal (e₂ / thr) := by
  have hstep : ∀ n, μ Bad ≤ μ B₁ + μ (G n) + ENNReal.ofReal (e₂ / thr) := by
    intro n
    calc μ Bad ≤ μ (B₁ ∪ Nul ∪ G n ∪ {ω | thr < X n ω}) := measure_mono (hsub n)
      _ ≤ μ B₁ + μ Nul + μ (G n) + μ {ω | thr < X n ω} := by
          have h1 := measure_union_le (μ := μ) (B₁ ∪ Nul ∪ G n) {ω | thr < X n ω}
          have h2 := measure_union_le (μ := μ) (B₁ ∪ Nul) (G n)
          have h3 := measure_union_le (μ := μ) B₁ Nul
          calc _ ≤ _ := h1
            _ ≤ μ (B₁ ∪ Nul) + μ (G n) + μ {ω | thr < X n ω} := by gcongr
            _ ≤ _ := by gcongr
      _ ≤ μ B₁ + μ (G n) + ENNReal.ofReal (e₂ / thr) := by
          rw [hNul, add_zero]
          gcongr
          exact markov_le μ (hXm n) (hX0 n) (hXi n) hthr (hXe n)
  have hlim : Tendsto (fun n => μ B₁ + μ (G n) + ENNReal.ofReal (e₂ / thr)) atTop
      (𝓝 (μ B₁ + 0 + ENNReal.ofReal (e₂ / thr))) :=
    (tendsto_const_nhds.add hG).add tendsto_const_nhds
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hstep

/-- Far labels are far in energy (upper count). -/
theorem far_from_label {N : ℕ} (lam : Fin N → ℝ) (hmono : Monotone lam) {C h R : ℝ}
    (hC : 0 < C)
    (hcount : ∀ x y : ℝ, x ≤ y →
      ((Finset.univ.filter fun i : Fin N => lam i ∈ Set.Icc x y).card : ℝ) ≤
        C * N * ((y - x) + h))
    {j k : Fin N} (hjk : R < (labelDist k j : ℝ)) :
    R / (C * N) - h ≤ |lam j - lam k| := by
  classical
  have hN : 0 < N := Fin.pos k
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ p q : Fin N, p ≤ q → R < (q.val - p.val : ℕ) →
      R / (C * N) - h ≤ lam q - lam p := by
    intro p q hpq hR'
    have hsub : Finset.Icc p q ⊆
        Finset.univ.filter fun i : Fin N => lam i ∈ Set.Icc (lam p) (lam q) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
      exact ⟨hmono hm.1, hmono hm.2⟩
    have hc1 := Finset.card_le_card hsub
    rw [Fin.card_Icc] at hc1
    have hc2 := hcount (lam p) (lam q) (hmono hpq)
    have h3 : ((q.val + 1 - p.val : ℕ) : ℝ) ≤
        ((Finset.univ.filter fun i : Fin N => lam i ∈ Set.Icc (lam p) (lam q)).card : ℝ) := by
      exact_mod_cast hc1
    have h4 : (((q.val - p.val : ℕ) : ℝ)) ≤ ((q.val + 1 - p.val : ℕ) : ℝ) := by
      exact_mod_cast (by omega : q.val - p.val ≤ q.val + 1 - p.val)
    have h5 : R ≤ C * N * ((lam q - lam p) + h) := by linarith
    have h6 : R / (C * N) ≤ (lam q - lam p) + h := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  rcases le_total k j with hkj | hjk'
  · have hd : (labelDist k j : ℝ) = ((j.val - k.val : ℕ) : ℝ) := by
      unfold labelDist
      have : (k : ℕ) ≤ j := hkj
      congr 1; omega
    rw [hd] at hjk
    have := key k j hkj hjk
    exact this.trans (le_abs_self _)
  · have hd : (labelDist k j : ℝ) = ((k.val - j.val : ℕ) : ℝ) := by
      unfold labelDist
      have : (j : ℕ) ≤ k := hjk'
      congr 1; omega
    rw [hd] at hjk
    have := key j k hjk' hjk
    rw [abs_sub_comm]
    exact this.trans (le_abs_self _)

end BlockBand.Palm.RelativeLocalization
