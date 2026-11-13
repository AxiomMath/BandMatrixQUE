module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularInduct
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The stopped angular martingale is centred given `𝓕_0 ∨ σ(W)`

With `D_u = Ms_u - Ms_0` (`Ms = (f(X) - ∫ 𝒜 f)^{σ_n}`) and `W = λ - ∫ b(λ)`:
* `Hyp.orth_exp`: `E[1_A e^{i∑_{j∈J} θ_j·W_j} D_u] = 0` for `A ∈ 𝓕_0`, finite `J` (from `Hyp.F2`);
* `Hyp.orth_cyl`: `E[1_{A ∩ {W_J ∈ C}} D_u] = 0` for Borel `C` (uniqueness of characteristic
  functions of finite measures, `Measure.ext_of_charFunDual`, applied to the images of
  `1_A D_u^± dQ` under `W_J`);
These give, in the sibling module, `Hyp.orth_sigma`: `E[1_S D_u] = 0` for every `S` in
`𝓕_0 ⊔ ⨆_t σ(W_t)` (π–λ theorem).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ} {s : ℝ≥0}
  {f : (Fin N → ℝ) → ℝ} {n : ℕ}

/-- `D_u = Ms_u - Ms_0`. -/
def Dp (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (σ : Ω → WithTop ℝ≥0)
    (u : ℝ≥0) (ω : Ω) : ℝ :=
  stoppedProcess (Mt f Y) σ u ω - stoppedProcess (Mt f Y) σ 0 ω

/-- The vector `(W_j)_{j ∈ J}`. -/
def WJ (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (J : Finset ℝ≥0) (ω : Ω) : J → Fin N → ℝ :=
  fun j => Wp Y j ω

theorem Hyp.measurable_Wp (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (t : ℝ≥0) :
    Measurable (Wp (Yst N q G F s) t) :=
  measurable_pi_iff.2 fun i =>
    ((H.adapted_phase q (Pi.single i 1) t).mono ((shiftFiltration 𝓖 s).le t)).measurable

theorem Hyp.measurable_WJ (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (J : Finset ℝ≥0) :
    Measurable (WJ (Yst N q G F s) J) :=
  measurable_pi_iff.2 fun j => H.measurable_Wp q j

theorem Hyp.D_props (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (u : ℝ≥0) :
    Measurable (Dp f (Yst N q G F s) (sig N G F s n) u) ∧
      ∃ C, ∀ᵐ ω ∂Q, |Dp f (Yst N q G F s) (sig N G F s n) u ω| ≤ C := by
  obtain ⟨-, hMsad, hMsb⟩ := H.ms_props (f := f) q
  refine ⟨((hMsad u).mono ((shiftFiltration 𝓖 s).le u)).measurable.sub
    ((hMsad 0).mono ((shiftFiltration 𝓖 s).le 0)).measurable, ?_⟩
  obtain ⟨C, hC⟩ := hMsb u
  exact ⟨C + C, hC.mono fun ω h => (abs_sub _ _).trans (add_le_add (h u le_rfl) (h 0 zero_le))⟩

theorem Hyp.integrable_D (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (u : ℝ≥0) :
    Integrable (Dp f (Yst N q G F s) (sig N G F s n) u) Q := by
  obtain ⟨hm, C, hC⟩ := H.D_props q u
  exact Integrable.of_bound hm.aestronglyMeasurable C (hC.mono fun ω h => by
    rwa [Real.norm_eq_abs])

/-- **Exponential test functionals.** -/
theorem Hyp.orth_exp (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) {A : Set Ω}
    (hA : MeasurableSet[shiftFiltration 𝓖 s 0] A) (J : Finset ℝ≥0) (θ : ℝ≥0 → Fin N → ℝ)
    (u : ℝ≥0) :
    ∫ ω, A.indicator (fun _ => (1 : ℂ)) ω *
      cexp ((∑ j ∈ J, Wd (θ j) (Yst N q G F s) j ω : ℝ) * I) *
        (Dp f (Yst N q G F s) (sig N G F s n) u ω : ℂ) ∂Q = 0 := by
  set ζ : Ω → ℂ := fun ω => A.indicator (fun _ => (1 : ℂ)) ω *
    cexp ((∑ j ∈ J, Wd (θ j) (Yst N q G F s) 0 ω : ℝ) * I)
  have hζ : StronglyMeasurable[shiftFiltration 𝓖 s 0] ζ := by
    have hc : Continuous fun x : ℝ => cexp ((x : ℂ) * I) := by fun_prop
    exact (stronglyMeasurable_const.indicator hA).mul (hc.comp_stronglyMeasurable
      (Finset.stronglyMeasurable_fun_sum _ fun j _ => H.adapted_Wd q (θ j) 0))
  have hζb : ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ 1 := ae_of_all _ fun ω => by
    simp only [ζ, norm_mul, norm_cexp_mul_I, mul_one]
    by_cases h : ω ∈ A <;> simp [h]
  have := H.F2 q J 0 (fun j _ => zero_le) θ ζ hζ 1 hζb u
  rw [min_eq_right (zero_le : (0 : ℝ≥0) ≤ u)] at this
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [ζ, Dp, psum, Finset.sum_sub_distrib]
  have e : cexp (((∑ j ∈ J, Wd (θ j) (Yst N q G F s) j ω : ℝ) : ℂ) * I) =
      cexp (((∑ j ∈ J, Wd (θ j) (Yst N q G F s) 0 ω : ℝ) : ℂ) * I) *
        cexp (((∑ j ∈ J, Wd (θ j) (Yst N q G F s) j ω -
          ∑ j ∈ J, Wd (θ j) (Yst N q G F s) 0 ω : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]; ring

/-- A continuous linear functional on `J → ℝ^N` in coordinates. -/
theorem dual_apply_eq {J : Finset ℝ≥0} (L : StrongDual ℝ (J → Fin N → ℝ)) (x : J → Fin N → ℝ) :
    L x = ∑ j, ∑ i, x j i * L (Pi.single j (Pi.single i 1)) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [pi_eq_sum_univ' (x j)]
  have hs : ∀ v : Fin N → ℝ, (Pi.single j v : J → Fin N → ℝ) =
      LinearMap.single ℝ (fun _ : J => Fin N → ℝ) j v := fun v => rfl
  rw [hs, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← hs, map_smul, smul_eq_mul]

omit [IsProbabilityMeasure Q] in
theorem integral_map_withDensity {J : Finset ℝ≥0} {W : Ω → J → Fin N → ℝ} (hW : Measurable W)
    {g : Ω → ℝ≥0} (hg : Measurable g) {φ : (J → Fin N → ℝ) → ℂ} (hφ : Measurable φ) :
    ∫ x, φ x ∂(Measure.map W (Q.withDensity fun ω => g ω)) = ∫ ω, (g ω : ℝ) • φ (W ω) ∂Q := by
  rw [integral_map hW.aemeasurable hφ.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul hg]
  rfl

/-- **Cylinder sets.** -/
theorem Hyp.orth_cyl (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) {A : Set Ω}
    (hA : MeasurableSet[shiftFiltration 𝓖 s 0] A) (J : Finset ℝ≥0)
    {C : Set (J → Fin N → ℝ)} (hC : MeasurableSet C) (u : ℝ≥0) :
    ∫ ω in A ∩ WJ (Yst N q G F s) J ⁻¹' C, Dp f (Yst N q G F s) (sig N G F s n) u ω ∂Q = 0 := by
  set Y := Yst N q G F s
  set D := Dp f Y (sig N G F s n) u
  obtain ⟨hDm, CD, hCD⟩ := H.D_props (f := f) q u
  have hAm : MeasurableSet A := (shiftFiltration 𝓖 s).le 0 A hA
  have hW := H.measurable_WJ q J
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
      refine ne_top_of_le_ne_top (H.integrable_D (f := f) q u).hasFiniteIntegral.ne
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
    have := H.orth_exp q hA J θ u
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

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
