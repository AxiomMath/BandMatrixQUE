module

public import BlockBand.Transmission.Generator.LimitDrift

/-!
# Abstract tools for the product martingale (`ProductMartingaleAlong`)

* `riemann_tendsto`: if `c_n(⌊W_n u⌋) → g(u)` boundedly on `[s, t]`, then
  `Σ_{⌊W_ns⌋ ≤ r < ⌊W_nt⌋} c_n(r)/W_n → ∫_s^t g` (dominated convergence + two boundary cells);
* `fubini_slices`: interval Fubini for `ψ(ω)F(u, ω)` with `L¹`-bounded slices (no boundedness of
  `ψ`); it also bounds `E|ψ ∫_s^t F|` (Tonelli);
* `limit_version`: a jointly measurable version of `(u, ω) ↦ H(P(u))` on `[s, t]`, from a.s.
  continuous paths (the construction inside `limit_fubini`);
* `abs_integral_mul_mul_le`: `|E[Φfg]| ≤ B‖f‖₂‖g‖₂` (Hölder).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Riemann sums with pointwise convergent bounded cells.** -/
theorem riemann_tendsto {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop) {c : ℕ → ℕ → ℝ} {g : ℝ → ℝ}
    {s t K : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hbd : ∀ᶠ n in atTop, ∀ u ∈ Set.Icc s t, |c n ⌊((σ n : ℕ) : ℝ) * u⌋₊| ≤ K)
    (hlim : ∀ u ∈ Set.Icc s t, Tendsto (fun n => c n ⌊((σ n : ℕ) : ℝ) * u⌋₊) atTop (𝓝 (g u))) :
    Tendsto (fun n => ∑ r ∈ Finset.Ico ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊,
      c n r / (σ n : ℝ)) atTop (𝓝 (∫ u in s..t, g u)) := by
  have hDCT : Tendsto (fun n => ∫ u in s..t, c n ⌊((σ n : ℕ) : ℝ) * u⌋₊) atTop
      (𝓝 (∫ u in s..t, g u)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => K)
      (Eventually.of_forall fun n => ((measurable_from_nat (f := c n)).comp
        (Nat.measurable_floor.comp (measurable_const.mul measurable_id))).aestronglyMeasurable)
      ?_ intervalIntegrable_const ?_
    · filter_upwards [hbd] with n hn
      refine Eventually.of_forall fun u hu => ?_
      rw [Set.uIoc_of_le hst] at hu
      rw [Real.norm_eq_abs]; exact hn u ⟨hu.1.le, hu.2⟩
    · refine Eventually.of_forall fun u hu => ?_
      rw [Set.uIoc_of_le hst] at hu
      exact hlim u ⟨hu.1.le, hu.2⟩
  have hK : Tendsto (fun n => 2 * K / ((σ n : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * K)).comp hσ
  have hcmp : ∀ᶠ n in atTop, |∑ r ∈ Finset.Ico ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊,
      c n r / (σ n : ℝ) - ∫ u in s..t, c n ⌊((σ n : ℕ) : ℝ) * u⌋₊| ≤ 2 * K / ((σ n : ℕ) : ℝ) := by
    filter_upwards [hbd, hσ.eventually_ge_atTop 1] with n hn hn1
    have hW : 0 < σ n := hn1
    have hWr : (0 : ℝ) ≤ (σ n : ℝ) := Nat.cast_nonneg _
    have hrst : ⌊((σ n : ℕ) : ℝ) * s⌋₊ ≤ ⌊((σ n : ℕ) : ℝ) * t⌋₊ :=
      Nat.floor_mono (mul_le_mul_of_nonneg_left hst hWr)
    rw [sum_div_eq_integral hW (c n) hrst, abs_sub_comm]
    refine (boundary_le hW (c n) hs hst).trans ?_
    have h1 := hn s ⟨le_rfl, hst⟩
    have h2 := hn t ⟨hst, le_rfl⟩
    gcongr; linarith
  have h0 : Tendsto (fun n => ∑ r ∈ Finset.Ico ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊,
      c n r / (σ n : ℝ) - ∫ u in s..t, c n ⌊((σ n : ℕ) : ℝ) * u⌋₊) atTop (𝓝 0) :=
    squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hcmp) hK
  simpa using h0.add hDCT

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_intervalIntegral_of_uncurry {F : ℝ → Ω → ℝ}
    (hF : Measurable (Function.uncurry F)) {s t : ℝ} (hst : s ≤ t) :
    Measurable fun ω => ∫ u in s..t, F u ω := by
  have h := (hF.stronglyMeasurable.integral_prod_left
    (μ := volume.restrict (Set.Ioc s t))).measurable
  have e : (fun ω => ∫ u in s..t, F u ω) = fun ω => ∫ u in Set.Ioc s t, F u ω :=
    funext fun ω => intervalIntegral.integral_of_le hst
  rw [e]; exact h

/-- **Interval Fubini with `L¹`-bounded slices.** -/
theorem fubini_slices {P : Measure Ω} [IsFiniteMeasure P] {F : ℝ → Ω → ℝ}
    (hF : Measurable (Function.uncurry F)) {ψ : Ω → ℝ} (hψ : Measurable ψ) {s t C : ℝ}
    (hst : s ≤ t) (hC : ∀ u ∈ Set.Ioc s t, ∫⁻ ω, ‖ψ ω * F u ω‖ₑ ∂P ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ψ ω * ∫ u in s..t, F u ω) P ∧
      ∫⁻ ω, ‖ψ ω * ∫ u in s..t, F u ω‖ₑ ∂P ≤ ENNReal.ofReal ((t - s) * C) ∧
      ∫ ω, ψ ω * (∫ u in s..t, F u ω) ∂P = ∫ u in s..t, ∫ ω, ψ ω * F u ω ∂P ∧
      IntervalIntegrable (fun u => ∫ ω, ψ ω * F u ω ∂P) volume s t := by
  set G : ℝ → Ω → ℝ := fun u ω => ψ ω * F u ω
  have hGm : Measurable (Function.uncurry G) := (hψ.comp measurable_snd).mul hF
  have hC0 : ∀ u ∈ Set.Ioc s t, ∫⁻ ω, ‖G u ω‖ₑ ∂P ≤ ENNReal.ofReal C := hC
  have hlin : ∫⁻ u in Set.uIoc s t, ∫⁻ ω, ‖G u ω‖ₑ ∂P ≤ ENNReal.ofReal ((t - s) * C) := by
    rw [Set.uIoc_of_le hst]
    calc ∫⁻ u in Set.Ioc s t, ∫⁻ ω, ‖G u ω‖ₑ ∂P ≤ ∫⁻ _ in Set.Ioc s t, ENNReal.ofReal C :=
          setLIntegral_mono' measurableSet_Ioc hC0
      _ = ENNReal.ofReal ((t - s) * C) := by
          rw [setLIntegral_const, Real.volume_Ioc, mul_comm, ← ENNReal.ofReal_mul (by linarith)]
  have hint : Integrable (Function.uncurry G) ((volume.restrict (Set.uIoc s t)).prod P) := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral]
    rw [lintegral_prod _ hGm.enorm.aemeasurable]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hfun : ∀ ω, ψ ω * ∫ u in s..t, F u ω = ∫ u, G u ω ∂volume.restrict (Set.uIoc s t) := by
    intro ω
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hst, Set.uIoc_of_le hst]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hint.integral_prod_right
    simp only [Function.uncurry_apply_pair] at this
    exact this.congr (Eventually.of_forall fun ω => (hfun ω).symm)
  · calc ∫⁻ ω, ‖ψ ω * ∫ u in s..t, F u ω‖ₑ ∂P
        ≤ ∫⁻ ω, (∫⁻ u in Set.uIoc s t, ‖G u ω‖ₑ) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [hfun ω]; exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ u in Set.uIoc s t, ∫⁻ ω, ‖G u ω‖ₑ ∂P := by
          exact lintegral_lintegral_swap (f := fun ω u => ‖G u ω‖ₑ) (μ := P)
            (ν := volume.restrict (Set.uIoc s t)) (by exact (hGm.enorm.comp measurable_swap).aemeasurable)
      _ ≤ _ := hlin
  · rw [intervalIntegral_integral_swap hint]
    exact integral_congr_ae (Eventually.of_forall fun ω => by
      simp only [G]; rw [intervalIntegral.integral_const_mul])
  · have h2 := hint.integral_prod_left
    simp only [Function.uncurry_apply_pair] at h2
    rw [intervalIntegrable_iff]; exact h2

/-- **A jointly measurable version of `H(P(u))` on `[s, t]`.** -/
theorem limit_version {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ}
    (hmeas : ∀ k, 1 ≤ k → ∀ t, 0 < t → Measurable (Pk k t))
    (hcont : ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0))
    {H : (ℕ → ℝ) → ℝ} (hH : Continuous H) {s t : ℝ} (hs : 0 < s) :
    ∃ F : ℝ → Ω → ℝ, Measurable (Function.uncurry F) ∧
      ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc s t, F u ω = H (cutVec Pk u ω) := by
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, 1 ≤ k → ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0) := by
    refine ae_all_iff.mpr fun k => ?_
    by_cases hk : 1 ≤ k
    · exact (hcont k hk).mono fun ω h _ => h
    · exact Eventually.of_forall fun ω h => absurd h hk
  set S := (toMeasurable P {ω | ¬ ∀ k : ℕ, 1 ≤ k →
    ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0)})ᶜ with hSdef
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hS : ∀ᵐ ω ∂P, ω ∈ S := by
    rw [ae_iff]; simp only [hSdef, Set.mem_compl_iff, not_not, Set.ofPred_mem_eq]
    rw [measure_toMeasurable]; exact ae_iff.mp hall
  have hSgood : ∀ ω ∈ S, ∀ k : ℕ, 1 ≤ k → ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0) := by
    intro ω hω
    by_contra hc
    exact hω (subset_toMeasurable _ _ hc)
  set cl : ℝ → ℝ := fun u => max s (min t u)
  have hcl : Continuous cl := by fun_prop
  have hcl_pos : ∀ u, 0 < cl u := fun u => lt_of_lt_of_le hs (le_max_left _ _)
  have hcl_eq : ∀ u ∈ Set.Icc s t, cl u = u := by
    intro u hu
    simp only [cl, min_eq_right hu.2, max_eq_right hu.1]
  set F : ℝ → Ω → ℝ := fun u ω => S.indicator (fun ω => H (cutVec Pk (cl u) ω)) ω
  have hFc : ∀ ω, Continuous fun u => F u ω := by
    intro ω
    by_cases hω : ω ∈ S
    · simp only [F, Set.indicator_of_mem hω]
      refine hH.comp (continuous_pi fun j => ?_)
      by_cases hj : 1 ≤ j
      · simp only [cutVec, hj, ↓reduceIte]
        exact (hSgood ω hω j hj).comp_continuous hcl fun u => hcl_pos u
      · simp only [cutVec, hj, ↓reduceIte]; exact continuous_const
    · simp only [F, Set.indicator_of_notMem hω]; exact continuous_const
  have hFm : ∀ u, Measurable (F u) := fun u =>
    (hH.measurable.comp (measurable_cutVec hmeas (hcl_pos u))).indicator hSm
  refine ⟨F, measurable_uncurry_of_continuous_of_measurable hFc hFm, ?_⟩
  filter_upwards [hS] with ω hω u hu
  simp only [F, Set.indicator_of_mem hω, hcl_eq u hu]

/-- **Hölder for a bounded test**: `|E[Φfg]| ≤ B‖f‖₂‖g‖₂`. -/
theorem abs_integral_mul_mul_le {μ : Measure Ω} {Φ f g : Ω → ℝ} {B : ℝ} (hB00 : 0 ≤ B)
    (hΦ : AEStronglyMeasurable Φ μ) (hB : ∀ᵐ ω ∂μ, |Φ ω| ≤ B) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) :
    |∫ ω, Φ ω * (f ω * g ω) ∂μ| ≤ B * (eLpNorm f 2 μ * eLpNorm g 2 μ).toReal := by
  have hfg : MemLp (f * g) 1 μ := hf.mul hg
  have hB' : ∀ᵐ ω ∂μ, ‖Φ ω‖ ≤ B := hB.mono fun ω h => by rwa [Real.norm_eq_abs]
  have hint : Integrable (fun ω => f ω * g ω) μ := memLp_one_iff_integrable.mp hfg
  have hH : eLpNorm (f * g) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ :=
    eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hf.aestronglyMeasurable hg.aestronglyMeasurable
  have hfin : eLpNorm f 2 μ * eLpNorm g 2 μ ≠ ⊤ := ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top
  have hB0 : ∀ᵐ ω ∂μ, |Φ ω * (f ω * g ω)| ≤ B * |f ω * g ω| := hB.mono fun ω h => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
  calc |∫ ω, Φ ω * (f ω * g ω) ∂μ| ≤ ∫ ω, |Φ ω * (f ω * g ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, B * |f ω * g ω| ∂μ :=
        integral_mono_ae (hint.bdd_mul hΦ hB').abs (hint.abs.const_mul B) hB0
    _ = B * (eLpNorm (f * g) 1 μ).toReal := by
        rw [integral_const_mul]; congr 1
        rw [eLpNorm_one_eq_lintegral_enorm,
          ← integral_norm_eq_lintegral_enorm hfg.aestronglyMeasurable]
        · simp [Real.norm_eq_abs]
        · exact hfg.aestronglyMeasurable
    _ ≤ B * (eLpNorm f 2 μ * eLpNorm g 2 μ).toReal := by
        exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfin hH) hB00

end BlockBand.Transmission.Generator
