module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Scheme.Limits
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Taylor scheme theorem with integral bounds)

**Setting.** `(Ω, m₀, Q)` a probability space, `𝓖 : Filtration ℝ≥0 m₀` arbitrary (raw).
`Z : ℝ≥0 → Ω → ℝ^d` with characteristics `β, α` satisfying `IHyp Q 𝓖 K Z β α N B C`: values
a.s. in the compact `K`, a.s. continuous paths, `𝓖_t`-a.e. measurable; a.s. the paths of
`β, α` are integrable on every `(0, t]` with `∫_0^t (Σ|β^i| + Σ|α^{ij}|) ≤ C` for all `t`
(no pointwise bound); `N`, `B` martingales equal a.s. at each time to the compensated
coordinates and products. `φ ∈ C²(U)`, `U ⊇ K` open.

**Results.**
* `IHyp.setIntegral_schemeProc_eq'`: `∫_A X_t dQ = ∫_A X_s dQ` for `s ≤ t`, `A ∈ 𝓖_s`, where
  `X_t = φ(Z_t) - φ(Z_0) - ∫_0^t 𝓛φ` (`schemeProc`);
* `IHyp.exists_martingale_schemeProc'`: `X` has a `𝓖`-martingale modification.

Proof: the Stroock–Varadhan Taylor scheme on the uniform grids of `[s, t]`; the zero-mean grid
transforms are those of the pointwise-bounded scheme, and the error is shown to vanish in `L¹`
using the control `G` (`err_le'`, `integral_sqSum_sq_le'`, `tendsto_integral_sqG`).
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀} {K U : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {C : ℝ}
  {φ : (Fin d → ℝ) → ℝ}

theorem IHyp.aesm_schemeProc' (H : IHyp Q 𝓖 K Z β α N B C) (hU : IsOpen U)
    (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (t : ℝ≥0) :
    AEStronglyMeasurable[𝓖 t] (schemeProc φ Z β α t) Q := by
  have h0 : (0 : ℝ≥0) ≤ t := zero_le
  have hI := H.aesm_integral_gen' hU hKU hφ h0
  have hφK : ContinuousOn φ K := hφ.continuousOn.mono hKU
  have e : schemeProc φ Z β α t = fun ω => φ (Z t ω) - φ (Z 0 ω) -
      ∫ u in ((0 : ℝ≥0) : ℝ)..t, schemeGen φ Z β α u.toNNReal ω := by
    funext ω
    rw [schemeProc, NNReal.coe_zero, intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  rw [e]
  exact ((H.aesm_comp hφK t).sub ((H.aesm_comp hφK 0).mono (𝓖.mono h0))).sub hI

/-- Bounds of `φ`, `Dφ`, `D²φ` on `K` (nonnegative). -/
theorem exists_bounds_K (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ 2 φ U) : ∃ M₀ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ (∀ z ∈ K, ‖φ z‖ ≤ M₀) ∧
      (∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁) ∧ (∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) := by
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (f := φ) (hφ.continuousOn.mono hKU)
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ φ)
    ((hφ.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hKU)
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ φ))
    (((hφ.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU
      le_rfl).mono hKU)
  exact ⟨M₀, max M₁ 0, max M₂ 0, le_max_right _ _, le_max_right _ _, hM₀,
    fun z hz => (hM₁ z hz).trans (le_max_left _ _), fun z hz => (hM₂ z hz).trans (le_max_left _ _)⟩

theorem IHyp.ae_abs_schemeProc_le' (H : IHyp Q 𝓖 K Z β α N B C) {M₀ M₁ M₂ : ℝ}
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂)
    (hM₀ : ∀ z ∈ K, ‖φ z‖ ≤ M₀) (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁)
    (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, ‖schemeProc φ Z β α t ω‖ ≤ 2 * M₀ + (M₁ + M₂) * C := by
  filter_upwards [H.ae_igood 0 t] with ω hω
  rw [Real.norm_eq_abs, schemeProc]
  have h1 := hM₀ _ (hω.1.1 t); have h2 := hM₀ _ (hω.1.1 0)
  rw [Real.norm_eq_abs] at h1 h2
  have h3 := hω.abs_integral_gen_le' (zero_le : (0 : ℝ≥0) ≤ t) hM₁0 hM₂0 hM₁ hM₂
  rw [NNReal.coe_zero, intervalIntegral.integral_of_le (NNReal.coe_nonneg t)] at h3
  have := abs_sub (φ (Z t ω) - φ (Z 0 ω)) (∫ u in Ioc (0 : ℝ) t, schemeGen φ Z β α u.toNNReal ω)
  have := abs_sub (φ (Z t ω)) (φ (Z 0 ω))
  linarith

variable [IsProbabilityMeasure Q]

theorem IHyp.integrable_schemeProc' (H : IHyp Q 𝓖 K Z β α N B C) (hU : IsOpen U)
    (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (t : ℝ≥0) :
    Integrable (schemeProc φ Z β α t) Q := by
  obtain ⟨M₀, M₁, M₂, hM₁0, hM₂0, hM₀, hM₁, hM₂⟩ := exists_bounds_K H.compact hU hKU hφ
  exact Integrable.of_bound ((H.aesm_schemeProc' hU hKU hφ t).mono (𝓖.le t)) _
    (H.ae_abs_schemeProc_le' hM₁0 hM₂0 hM₀ hM₁ hM₂ t)

/-- **The Taylor-scheme identity**: `∫_A X_t = ∫_A X_s` for `s ≤ t`, `A ∈ 𝓖_s`. -/
theorem IHyp.setIntegral_schemeProc_eq' (H : IHyp Q 𝓖 K Z β α N B C)
    (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, schemeProc φ Z β α t ω ∂Q = ∫ ω in A, schemeProc φ Z β α s ω ∂Q := by
  have hC0 : 0 ≤ C := by
    obtain ⟨ω, hω⟩ := (H.ae_igood s t).exists
    exact hω.C_nonneg
  obtain ⟨R₀, hR₀⟩ := H.compact.isBounded.exists_norm_le
  have hR : ∀ z ∈ K, ‖z‖ ≤ max R₀ 0 := fun z hz => (hR₀ z hz).trans (le_max_left _ _)
  set R := max R₀ 0
  have hR0 : 0 ≤ R := le_max_right _ _
  obtain ⟨M₀, M₁, M₂, hM₁0, hM₂0, hM₀, hM₁, hM₂⟩ := exists_bounds_K H.compact hU hKU hφ
  obtain ⟨C_T, hCT0, hT1, hT2⟩ := taylorRem_uniform hU H.compact hKU hφ
  set X := schemeProc φ Z β α
  set ι : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hAm : MeasurableSet A := 𝓖.le s A hA
  have iXt := H.integrable_schemeProc' hU hKU hφ t
  have iXs := H.integrable_schemeProc' hU hKU hφ s
  set c₀ := ∫ ω in A, (X t ω - X s ω) ∂Q with hc₀
  suffices hsuf : c₀ = 0 by
    rwa [hc₀, integral_sub iXt.integrableOn iXs.integrableOn, sub_eq_zero] at hsuf
  set D : ℝ := d * (2 * (2 * R + C)) ^ 2
  set CS : ℝ := d * C
  set CS2 : ℝ := (D + 2 * CS) * CS
  have hCS : 0 ≤ CS := by positivity
  have hCS2 : 0 ≤ CS2 := by positivity
  have hι : ∀ ω, |ι ω| ≤ 1 := fun ω => by
    by_cases h : ω ∈ A <;> simp [ι, h]
  have hιm : AEStronglyMeasurable ι Q :=
    (stronglyMeasurable_const.indicator hAm).aestronglyMeasurable
  have e₁ : c₀ = ∫ ω, ι ω * (X t ω - X s ω) ∂Q := by
    rw [hc₀, ← integral_indicator hAm]
    congr 1; funext ω
    by_cases h : ω ∈ A <;> simp [ι, h]
  -- the bound for each grid
  have hbound : ∀ ε > 0, ∀ δ > 0, (∀ y ∈ K, ∀ z ∈ K, ‖z - y‖ ≤ δ →
      |taylorRem φ y z| ≤ ε * ‖z - y‖ ^ 2) → ∀ c > 0, ∀ n : ℕ,
      |c₀| ≤ (∫ ω, |riemannSum φ Z β α s t n ω -
          ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω| ∂Q) +
        (M₂ * d + 2) * ε * CS + C_T / δ * (CS2 / (2 * c) + 2 * c *
          ∫ ω, meshMax Z s t n ω ^ 2 ∂Q) +
        (∫ ω, sqG β α s t n ω ∂Q) * errConst' d M₂ R C_T δ ε := by
    intro ε hε δ hδ hT2' c hc n
    obtain ⟨i1, z1⟩ := H.integral_indicator_transform1' hU hKU hφ hM₁ hst hA n
    obtain ⟨i2, z2⟩ := H.integral_indicator_transform2' hU hKU hφ hR hM₂ hst hA n
    have iX : Integrable (fun ω => ι ω * (X t ω - X s ω)) Q :=
      (iXt.sub iXs).bdd_mul hιm (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hι ω)
    set Eι : Ω → ℝ := fun ω => ι ω * (X t ω - X s ω) - ι ω * transform1 φ Z N s t n ω -
      1 / 2 * (ι ω * transform2 φ Z α N s t n ω)
    have hEi : Integrable Eι Q := (iX.sub i1).sub (i2.const_mul _)
    have e₂ : ∫ ω, ι ω * (X t ω - X s ω) ∂Q = ∫ ω, Eι ω ∂Q := by
      have hA1 : Integrable (fun ω => ι ω * (X t ω - X s ω) - ι ω * transform1 φ Z N s t n ω)
        Q := iX.sub i1
      have hA2 : Integrable (fun ω => 1 / 2 * (ι ω * transform2 φ Z α N s t n ω)) Q :=
        i2.const_mul _
      simp only [Eι]
      rw [integral_sub hA1 hA2, integral_sub iX i1, integral_const_mul, z1, z2]
      ring
    set G : Ω → ℝ := fun ω => |riemannSum φ Z β α s t n ω -
        ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω| +
      (M₂ * d + 2) * ε * sqSum N s t n ω +
      C_T / δ * (sqSum N s t n ω ^ 2 / (2 * c) + 2 * c * meshMax Z s t n ω ^ 2) +
      sqG β α s t n ω * errConst' d M₂ R C_T δ ε
    have hEG : ∀ᵐ ω ∂Q, ‖Eι ω‖ ≤ G ω := by
      filter_upwards [H.ae_igood s t] with ω hω
      have h := err_le' hω hU hKU hφ hst hR hM₂0 hM₂ hCT0 hδ hε hc hT1 hT2' n
      have hE : Eι ω = ι ω * (X t ω - X s ω - transform1 φ Z N s t n ω -
          1 / 2 * transform2 φ Z α N s t n ω) := by simp only [Eι]; ring
      rw [Real.norm_eq_abs, hE, abs_mul]
      calc |ι ω| * |X t ω - X s ω - transform1 φ Z N s t n ω -
            1 / 2 * transform2 φ Z α N s t n ω| ≤ 1 * |X t ω - X s ω -
              transform1 φ Z N s t n ω - 1 / 2 * transform2 φ Z α N s t n ω| :=
            mul_le_mul_of_nonneg_right (hι ω) (abs_nonneg _)
        _ ≤ G ω := by rw [one_mul]; exact h
    -- integrability of the majorant pieces
    have bS : ∀ᵐ ω ∂Q, ‖sqSum N s t n ω‖ ≤ (n + 1) * D := by
      filter_upwards [ae_all_iff.2 fun k => H.ae_cellSq_le (s := s) (t := t) hR n k] with ω hω
      have : sqSum N s t n ω = ∑ k ∈ Finset.range (n + 1), cellSq N s t n k ω := rfl
      rw [this, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => (hω k).1)]
      refine (Finset.sum_le_sum fun k _ => (hω k).2).trans ?_
      simp [D]
    have mS : AEStronglyMeasurable (sqSum N s t n) Q := by
      have : sqSum N s t n = fun ω => ∑ k ∈ Finset.range (n + 1), cellSq N s t n k ω := rfl
      rw [this]
      exact (Finset.stronglyMeasurable_fun_sum _ fun k _ =>
        ((H.stronglyMeasurable_cellSq hst n k).mono (𝓖.le _))).aestronglyMeasurable
    have iS : Integrable (sqSum N s t n) Q := Integrable.of_bound mS _ bS
    have iS2 : Integrable (fun ω => sqSum N s t n ω ^ 2) Q :=
      Integrable.of_bound (mS.pow 2) (((n + 1) * D) ^ 2)
        (bS.mono fun ω h => by
          rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h 2)
    have iM : Integrable (fun ω => meshMax Z s t n ω ^ 2) Q :=
      Integrable.of_bound ((H.aesm_meshMax n).pow 2) ((2 * R) ^ 2)
        ((H.ae_igood s t).mono fun ω hω => by
          rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (meshMax_nonneg n)]
          exact pow_le_pow_left₀ (meshMax_nonneg n) (hω.meshMax_le hR n) 2)
    have iW : Integrable (sqG β α s t n) Q :=
      Integrable.of_bound (H.aesm_sqG n) (C * C) ((H.ae_igood s t).mono fun ω hω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sqG_nonneg n)]; exact hω.sqG_le hst n)
    have iRie : Integrable (fun ω => |riemannSum φ Z β α s t n ω -
        ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω|) Q := by
      refine Integrable.of_bound ((((H.aesm_riemannSum hU hKU hφ hst n).sub
        (H.aesm_integral_gen' hU hKU hφ hst)).mono (𝓖.le t)).norm)
        ((d * M₁ + d * d * M₂) * C + (M₁ + M₂) * C) ?_
      refine (H.ae_igood s t).mono fun ω hω => ?_
      rw [Real.norm_eq_abs, abs_abs]
      have h1 := hω.abs_riemannSum_le' hst hM₁0 hM₂0 hM₁ hM₂ n
      have h2 := hω.abs_integral_gen_le' hst hM₁0 hM₂0 hM₁ hM₂
      have := abs_sub (riemannSum φ Z β α s t n ω)
        (∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω)
      linarith
    have j2 : Integrable (fun ω => (M₂ * d + 2) * ε * sqSum N s t n ω) Q := iS.const_mul _
    have j3a : Integrable (fun ω => sqSum N s t n ω ^ 2 / (2 * c)) Q := iS2.div_const _
    have j3b : Integrable (fun ω => 2 * c * meshMax Z s t n ω ^ 2) Q := iM.const_mul _
    have j3ab : Integrable (fun ω => sqSum N s t n ω ^ 2 / (2 * c) +
        2 * c * meshMax Z s t n ω ^ 2) Q := j3a.add j3b
    have j3 : Integrable (fun ω => C_T / δ * (sqSum N s t n ω ^ 2 / (2 * c) +
        2 * c * meshMax Z s t n ω ^ 2)) Q := j3ab.const_mul _
    have j4 : Integrable (fun ω => sqG β α s t n ω * errConst' d M₂ R C_T δ ε) Q :=
      iW.mul_const _
    have j12 : Integrable (fun ω => |riemannSum φ Z β α s t n ω -
        ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω| +
        (M₂ * d + 2) * ε * sqSum N s t n ω) Q := iRie.add j2
    have j123 : Integrable (fun ω => |riemannSum φ Z β α s t n ω -
        ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω| +
        (M₂ * d + 2) * ε * sqSum N s t n ω + C_T / δ * (sqSum N s t n ω ^ 2 / (2 * c) +
        2 * c * meshMax Z s t n ω ^ 2)) Q := j12.add j3
    have iG : Integrable G Q := j123.add j4
    have hIG : ∫ ω, G ω ∂Q = (∫ ω, |riemannSum φ Z β α s t n ω -
          ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω| ∂Q) +
        (M₂ * d + 2) * ε * (∫ ω, sqSum N s t n ω ∂Q) +
        C_T / δ * ((∫ ω, sqSum N s t n ω ^ 2 ∂Q) / (2 * c) + 2 * c *
          ∫ ω, meshMax Z s t n ω ^ 2 ∂Q) +
        (∫ ω, sqG β α s t n ω ∂Q) * errConst' d M₂ R C_T δ ε := by
      simp only [G]
      rw [integral_add j123 j4, integral_add j12 j3, integral_add iRie j2,
        integral_const_mul, integral_const_mul, integral_add j3a j3b, integral_div,
        integral_const_mul, integral_mul_const]
    have hS1 := H.integral_sqSum_le' hR hst n
    have hS2 := H.integral_sqSum_sq_le' hR hst n
    have hpos1 : 0 ≤ (M₂ * d + 2) * ε := by positivity
    have hpos2 : 0 ≤ C_T / δ := div_nonneg hCT0 hδ.le
    calc |c₀| = |∫ ω, Eι ω ∂Q| := by rw [e₁, e₂]
      _ ≤ ∫ ω, ‖Eι ω‖ ∂Q := by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ ω, G ω ∂Q := integral_mono_ae hEi.norm iG hEG
      _ ≤ _ := by
        rw [hIG]
        have a1 : (M₂ * d + 2) * ε * (∫ ω, sqSum N s t n ω ∂Q) ≤ (M₂ * d + 2) * ε * CS :=
          mul_le_mul_of_nonneg_left hS1 hpos1
        have a2 : (∫ ω, sqSum N s t n ω ^ 2 ∂Q) / (2 * c) ≤ CS2 / (2 * c) :=
          div_le_div_of_nonneg_right hS2 (by positivity)
        have a3 := mul_le_mul_of_nonneg_left (add_le_add_right a2
          (2 * c * ∫ ω, meshMax Z s t n ω ^ 2 ∂Q)) hpos2
        linarith
  have key : ∀ ε > 0, |c₀| ≤ ((M₂ * d + 2) * CS + 1) * ε := by
    intro ε hε
    obtain ⟨δ, hδ, hT2'⟩ := hT2 ε hε
    have hq : 0 ≤ C_T / δ * CS2 / (2 * ε) := by
      have := div_nonneg hCT0 hδ.le; positivity
    set c := C_T / δ * CS2 / (2 * ε) + 1 with hcdef
    have hc : 0 < c := by linarith
    have hF := ((((H.tendsto_integral_riemann_err' hU hKU hφ hst hM₁0 hM₂0 hM₁ hM₂).add
      (tendsto_const_nhds (x := (M₂ * d + 2) * ε * CS))).add
      (((tendsto_const_nhds (x := CS2 / (2 * c))).add
        ((H.tendsto_integral_meshMax_sq' hst hR).const_mul (2 * c))).const_mul (C_T / δ))).add
      ((H.tendsto_integral_sqG hst).mul_const (errConst' d M₂ R C_T δ ε)))
    have hle := ge_of_tendsto' hF (hbound ε hε δ hδ hT2' c hc)
    simp only [zero_add, mul_zero, add_zero, zero_mul] at hle
    have h2 : C_T / δ * (CS2 / (2 * c)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      have : ε * (2 * c) = C_T / δ * CS2 + 2 * ε := by
        rw [hcdef]; field_simp
      linarith
    nlinarith
  by_contra hne
  have hpos : 0 < |c₀| := abs_pos.2 hne
  have hK' : 0 < (M₂ * d + 2) * CS + 1 := by positivity
  have := key (|c₀| / (2 * ((M₂ * d + 2) * CS + 1))) (by positivity)
  have e : ((M₂ * d + 2) * CS + 1) * (|c₀| / (2 * ((M₂ * d + 2) * CS + 1))) = |c₀| / 2 := by
    field_simp
  linarith

/-- **The Taylor-scheme theorem with integral bounds**: `φ(Z_t) - φ(Z_0) - ∫_0^t 𝓛φ` has a
`𝓖`-martingale modification. -/
theorem IHyp.exists_martingale_schemeProc' (H : IHyp Q 𝓖 K Z β α N B C)
    (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 Q ∧ ∀ t, M t =ᵐ[Q] schemeProc φ Z β α t :=
  exists_martingale_modification (H.integrable_schemeProc' hU hKU hφ)
    (H.aesm_schemeProc' hU hKU hφ) fun _ _ hst _ hA =>
      H.setIntegral_schemeProc_eq' hU hKU hφ hst hA

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
