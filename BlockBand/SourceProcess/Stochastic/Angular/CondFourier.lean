module

public import BlockBand.SourceProcess.Stochastic.Angular.CondOrth

/-!
# Complex angular martingale problem: Fourier and π–λ step for an abstract martingale

Under `OHyp Q 𝓕 Y Ms`, with `D = Ms_u - Ms_0` (`Dq`):
* `OHyp.orth_exp`: `E[1_A e^{i ∑_j θ_j·W_j} D] = 0` for `A ∈ 𝓕_0`;
* `OHyp.orth_cyl`: `∫_{A ∩ {W_J ∈ C}} D = 0` (uniqueness of characteristic functions of the
  two finite measures `W_J # (D^± 1_A Q)`);
* **`OHyp.orth_sigma`**: `∫_S D = 0` for every `S ∈ 𝓕_0 ⊔ σ(W)` (π–λ).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Dyson BlockBand.SourceProcess.Stochastic.Dyson.Angular

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {Y : ℝ≥0 → Ω → Fin (N + N) → ℝ} {Ms : ℝ≥0 → Ω → ℝ}

theorem OHyp.measurable_Wp (H : OHyp Q 𝓕 Y Ms) (t : ℝ≥0) :
    Measurable (Wp (Y) t) :=
  measurable_pi_iff.2 fun i =>
    ((H.adapted_phase (Pi.single i 1) t).mono ((𝓕).le t)).measurable

theorem OHyp.measurable_WJ (H : OHyp Q 𝓕 Y Ms) (J : Finset ℝ≥0) :
    Measurable (WJ (Y) J) :=
  measurable_pi_iff.2 fun j => H.measurable_Wp j

theorem OHyp.D_props (H : OHyp Q 𝓕 Y Ms) (u : ℝ≥0) :
    Measurable (Dq Ms u) ∧
      ∃ C, ∀ᵐ ω ∂Q, |Dq Ms u ω| ≤ C := by
  obtain ⟨hMsad, hMsb⟩ := H.ms_props
  refine ⟨((hMsad u).mono ((𝓕).le u)).measurable.sub
    ((hMsad 0).mono ((𝓕).le 0)).measurable, ?_⟩
  obtain ⟨C, hC⟩ := hMsb u
  exact ⟨C + C, hC.mono fun ω h => (abs_sub _ _).trans (add_le_add (h u le_rfl) (h 0 zero_le))⟩

theorem OHyp.integrable_D [IsProbabilityMeasure Q] (H : OHyp Q 𝓕 Y Ms) (u : ℝ≥0) :
    Integrable (Dq Ms u) Q := by
  obtain ⟨hm, C, hC⟩ := H.D_props u
  exact Integrable.of_bound hm.aestronglyMeasurable C (hC.mono fun ω h => by
    rwa [Real.norm_eq_abs])

/-- **Exponential test functionals.** -/
theorem OHyp.orth_exp [IsProbabilityMeasure Q] (H : OHyp Q 𝓕 Y Ms) {A : Set Ω}
    (hA : MeasurableSet[𝓕 0] A) (J : Finset ℝ≥0) (θ : ℝ≥0 → Fin N → ℝ)
    (u : ℝ≥0) :
    ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω *
      cexp ((∑ j ∈ J, Wd (θ j) (Y) j ω : ℝ) * I) *
        (Dq Ms u ω : ℂ) ∂Q = 0 := by
  set ζ : Ω → ℂ := fun ω => A.indicator (fun _ => (1 : ℂ)) ω *
    cexp ((∑ j ∈ J, Wd (θ j) (Y) 0 ω : ℝ) * I)
  have hζ : StronglyMeasurable[𝓕 0] ζ := by
    have hc : Continuous fun x : ℝ => cexp ((x : ℂ) * I) := by fun_prop
    exact (stronglyMeasurable_const.indicator hA).mul (hc.comp_stronglyMeasurable
      (Finset.stronglyMeasurable_fun_sum _ fun j _ => H.adapted_Wd (θ j) 0))
  have hζb : ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ 1 := ae_of_all _ fun ω => by
    simp only [ζ, norm_mul, norm_cexp_mul_I, mul_one]
    by_cases h : ω ∈ A <;> simp [h]
  have := H.F2 J 0 (fun j _ => zero_le) θ ζ hζ 1 hζb u
  rw [min_eq_right (zero_le : (0 : ℝ≥0) ≤ u)] at this
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [ζ, Dq, psum, Finset.sum_sub_distrib]
  have e : cexp (((∑ j ∈ J, Wd (θ j) (Y) j ω : ℝ) : ℂ) * I) =
      cexp (((∑ j ∈ J, Wd (θ j) (Y) 0 ω : ℝ) : ℂ) * I) *
        cexp (((∑ j ∈ J, Wd (θ j) (Y) j ω -
          ∑ j ∈ J, Wd (θ j) (Y) 0 ω : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]; ring

/-- **Cylinder sets.** -/
theorem OHyp.orth_cyl [IsProbabilityMeasure Q] (H : OHyp Q 𝓕 Y Ms) {A : Set Ω}
    (hA : MeasurableSet[𝓕 0] A) (J : Finset ℝ≥0)
    {C : Set (J → Fin N → ℝ)} (hC : MeasurableSet C) (u : ℝ≥0) :
    ∫ ω in A ∩ WJ (Y) J ⁻¹' C, Dq Ms u ω ∂Q = 0 := by
  set D := Dq Ms u
  obtain ⟨hDm, CD, hCD⟩ := H.D_props u
  have hAm : MeasurableSet A := (𝓕).le 0 A hA
  have hW := H.measurable_WJ J
  set g₁ : Ω → ℝ≥0 := A.indicator fun ω => (D ω).toNNReal
  set g₂ : Ω → ℝ≥0 := A.indicator fun ω => (-D ω).toNNReal
  have hg₁ : Measurable g₁ := (measurable_real_toNNReal.comp hDm).indicator hAm
  have hg₂ : Measurable g₂ := (measurable_real_toNNReal.comp hDm.neg).indicator hAm
  have hdiff : ∀ ω, (g₁ ω : ℝ) - (g₂ ω : ℝ) = A.indicator D ω := fun ω => by
    by_cases h : ω ∈ A
    · simp only [g₁, g₂, indicator_of_mem h, Real.coe_toNNReal']
      exact max_zero_sub_max_neg_zero_eq_self (D ω)
    · simp [g₁, g₂, h]
  have hfin : ∀ g : Ω → ℝ≥0, Measurable g → (∀ ω, (g ω : ℝ) ≤ |D ω|) →
      IsFiniteMeasure (Measure.map (WJ Y J) (Q.withDensity fun ω => g ω)) := by
    intro g hg hgD
    have : IsFiniteMeasure (Q.withDensity fun ω => (g ω : ENNReal)) := by
      refine isFiniteMeasure_withDensity ?_
      refine ne_top_of_le_ne_top (H.integrable_D u).hasFiniteIntegral.ne
        (lintegral_mono fun ω => ?_)
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (hgD ω)
    infer_instance
  have hb₁ : ∀ ω, (g₁ ω : ℝ) ≤ |D ω| := fun ω => by
    by_cases h : ω ∈ A
    · simp only [g₁, indicator_of_mem h, Real.coe_toNNReal']; exact max_le (le_abs_self _) (abs_nonneg _)
    · simp [g₁, h]
  have hb₂ : ∀ ω, (g₂ ω : ℝ) ≤ |D ω| := fun ω => by
    by_cases h : ω ∈ A
    · simp only [g₂, indicator_of_mem h, Real.coe_toNNReal']; exact max_le (neg_le_abs _) (abs_nonneg _)
    · simp [g₂, h]
  have := hfin g₁ hg₁ hb₁
  have := hfin g₂ hg₂ hb₂
  have hint : ∀ g : Ω → ℝ≥0, (∀ ω, (g ω : ℝ) ≤ |D ω|) → Measurable g → ∀ φ : (J → Fin N → ℝ) → ℂ,
      Measurable φ → (∀ x, ‖φ x‖ ≤ 1) → Integrable (fun ω => (g ω : ℝ) • φ (WJ Y J ω)) Q := by
    intro g hgD hg φ hφ hφb
    refine Integrable.of_bound ((measurable_coe_nnreal_real.comp hg).smul
      (hφ.comp hW)).aestronglyMeasurable CD ?_
    filter_upwards [hCD] with ω hω
    rw [norm_smul, Real.norm_eq_abs, NNReal.abs_eq]
    calc (g ω : ℝ) * ‖φ (WJ Y J ω)‖ ≤ |D ω| * 1 :=
          mul_le_mul (hgD ω) (hφb _) (norm_nonneg _) (abs_nonneg _)
      _ ≤ CD := by rw [mul_one]; exact hω
  have hchar : charFunDual (Measure.map (WJ Y J) (Q.withDensity fun ω => g₁ ω)) =
      charFunDual (Measure.map (WJ Y J) (Q.withDensity fun ω => g₂ ω)) := by
    funext L
    have hφ : Measurable fun x : J → Fin N → ℝ => cexp ((L x : ℂ) * I) := by
      have : Continuous fun x : J → Fin N → ℝ => cexp ((L x : ℂ) * I) := by fun_prop
      exact this.measurable
    rw [charFunDual_apply, charFunDual_apply, integral_map_withDensity hW hg₁ hφ,
      integral_map_withDensity hW hg₂ hφ, ← sub_eq_zero,
      ← integral_sub (hint g₁ hb₁ hg₁ _ hφ fun x => by rw [norm_cexp_mul_I])
        (hint g₂ hb₂ hg₂ _ hφ fun x => by rw [norm_cexp_mul_I])]
    set θ : ℝ≥0 → Fin N → ℝ := fun t i =>
      if h : t ∈ J then L (Pi.single ⟨t, h⟩ (Pi.single i 1)) else 0
    have hL : ∀ ω, L (WJ Y J ω) = ∑ j ∈ J, Wd (θ j) Y j ω := fun ω => by
      rw [dual_apply_eq, ← Finset.sum_coe_sort J]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Wd, WJ, θ, j.2, ↓reduceDIte]
      refine Finset.sum_congr rfl fun i _ => by ring
    have := H.orth_exp hA J θ u
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [Complex.real_smul, ← sub_mul, ← Complex.ofReal_sub, hdiff, hL]
    by_cases h : ω ∈ A
    · simp [h, D]; ring
    · simp [h]
  have hν := Measure.ext_of_charFunDual hchar
  have hφC : Measurable (C.indicator fun _ => (1 : ℂ)) := measurable_const.indicator hC
  have h1 := congrArg (fun ν => ∫ x, C.indicator (fun _ => (1 : ℂ)) x ∂ν) hν
  rw [integral_map_withDensity hW hg₁ hφC, integral_map_withDensity hW hg₂ hφC] at h1
  have h2 : ∫ ω, (((A ∩ WJ Y J ⁻¹' C).indicator D ω : ℝ) : ℂ) ∂Q = 0 := by
    rw [← sub_eq_zero.2 h1, ← integral_sub
      (hint g₁ hb₁ hg₁ _ hφC fun x => by by_cases hx : x ∈ C <;> simp [hx])
      (hint g₂ hb₂ hg₂ _ hφC fun x => by by_cases hx : x ∈ C <;> simp [hx])]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [Complex.real_smul, ← sub_mul, ← Complex.ofReal_sub, hdiff]
    by_cases hx : WJ Y J ω ∈ C <;> by_cases h : ω ∈ A <;> simp [hx, h, Set.indicator]
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero,
    integral_indicator (hAm.inter (hW hC))] at h2
  exact h2

/-- **The stopped angular increment is orthogonal to `𝓕_0 ⊔ σ(W)`.** -/
theorem OHyp.orth_sigma [IsProbabilityMeasure Q] (H : OHyp Q 𝓕 Y Ms) (u : ℝ≥0) {S : Set Ω}
    (hS : MeasurableSet[sigB (𝓕 0) (Y)] S) :
    ∫ ω in S, Dq Ms u ω ∂Q = 0 := by
  have hgen : MeasurableSpace.generateFrom (cylSets (𝓕 0) Y) ≤ (inferInstance : MeasurableSpace Ω) := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨A, hA, J, C, hC, rfl⟩
    exact ((𝓕).le 0 A hA).inter (H.measurable_WJ J hC)
  have hD := H.integrable_D u
  have htot : ∫ ω, Dq Ms u ω ∂Q = 0 := by
    have := H.orth_cyl (A := univ) MeasurableSet.univ ∅ (C := univ)
      MeasurableSet.univ u
    simpa using this
  refine @MeasurableSpace.induction_on_inter Ω (MeasurableSpace.generateFrom (cylSets (𝓕 0) Y))
    (fun S _ => ∫ ω in S, Dq Ms u ω ∂Q = 0) (cylSets (𝓕 0) Y) rfl
    (isPiSystem_cylSets (𝓕 0) Y) (by simp) ?_ ?_ ?_ S (sigB_le_generateFrom (𝓕 0) Y S hS)
  · rintro _ ⟨A, hA, J, C, hC, rfl⟩
    exact H.orth_cyl hA J hC u
  · intro T hT h
    rw [setIntegral_compl (hgen T hT) hD, htot, h, sub_zero]
  · intro g hdisj hgm hg
    have hg' : ∀ i, ∫ ω in g i, Dq Ms u ω ∂Q = 0 := hg
    rw [integral_iUnion (fun i => hgen _ (hgm i)) hdisj hD.integrableOn]
    exact (tsum_congr hg').trans tsum_zero

end BlockBand.SourceProcess.Stochastic.ComplexAngular
