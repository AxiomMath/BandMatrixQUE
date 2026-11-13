module

public import BlockBand.Critical.RelativeVectors.Window

/-!
# The conditional comparison summed over windows

One application of the comparison is needed for each window; the partition is by the exact
window set `S` (any `S`, `|S| ≤ k`), which needs no monotonicity of the ranks, and the right side
is additive in `B`.

*Law.* `μ = flowLaw N a`, `a = rmvStart c N`, `H = flowMatrix F a · c` (terminal matrix).
*Inputs.* `ComparisonAt N F c E C_w V₀ n η₁ η₂`: the body of the main clause
`RelativeMixedVectorsComparison` for fixed `N, F, E`, frame `V₀`, `n` labels, failure bound `η₁`
and comparison constant `η₂` (with `η₁ = N^{-D}`, `η₂ = C N^{-χ}` it is exactly that clause,
`comparisonAt_of`).

* `window_comparison`: if `ComparisonAt … V₀ n η₁ (η₂ n)` holds for every `n ≤ k`, `η₂ n ≤ η`,
  `R ≤ C_w ρ`, `‖matCLM T^*‖ ≤ B`, then
  `|E_μ[Ψ₁(H) - Ψ₂(H)]| ≤ M(k,K,B) η + (k+1)η₁ + μ(|window| > k)` with
  `Ψ₁ = markedIntegrand ρ E (V₀T) φ` and `Ψ₂ = gaussIntegrand ρ E φ T^*` (`Π_ℓ I_{T^*}(x_ℓ)`).

*Uniformity.* The bound depends on `(k, K, B, η, η₁)` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.MomentFlow

variable {N r : ℕ}

/-- The body of `RelativeMixedVectorsComparison` for fixed `N, F, E`, frame `V`, `k` labels,
window constant `C_w`, failure bound `η₁` (for `N^{-D}`) and comparison constant `η₂`
(for `C N^{-χ}`). -/
def ComparisonAt (N : ℕ) (F : Matrix (Fin N) (Fin N) ℂ) (c E Cw : ℝ)
    (V : Matrix (Fin N) (Fin r) ℂ) (k : ℕ) (η₁ η₂ : ℝ) : Prop :=
  ∃ 𝒢 : Set (FlowSample N),
    MeasurableSet[pathSigma F (rmvStart c N) (rmvStart c N) c] 𝒢 ∧
    flowLaw N (rmvStart c N) 𝒢ᶜ ≤ ENNReal.ofReal η₁ ∧
    ∀ ι : Fin k → Fin N, Function.Injective ι →
    ∀ B : Set (FlowSample N),
      MeasurableSet[pathSigma F (rmvStart c N) (rmvStart c N) c] B →
      B ⊆ 𝒢 →
      (∀ ω ∈ B, ∀ m : Fin k, |flowEigenvalue F (rmvStart c N) ω c (ι m) - E| ≤ Cw / N) →
    ∀ f : FlowSample N → MarkArray k r → ℝ,
      IsPathMarkTest (pathSigma F (rmvStart c N) (rmvStart c N) c) f →
      |∫ ω in B, ∫ θ, (f ω (fun m => relativeMark V (flowMatrix F (rmvStart c N) ω c) θ (ι m)) -
          ∫ g, f ω g ∂gaussianMarkLaw k r) ∂phaseVectorLaw N ∂flowLaw N (rmvStart c N)| ≤
        η₂ * (flowLaw N (rmvStart c N) B).toReal

/-- The main clause gives `ComparisonAt` with `η₁ = N^{-D}` and `η₂ = C N^{-χ}`. -/
theorem comparisonAt_of (hC : RelativeMixedVectorsComparison) {A c r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (r k : ℕ) (Cw : ℝ) :
    ∃ χ : ℝ, 0 < χ ∧ ∃ C : ℝ, ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      ∀ V : Matrix (Fin N) (Fin r) ℂ, Vᴴ * freshGamma F c E * V = 1 →
        ComparisonAt N F c E Cw V k ((N : ℝ) ^ (-D)) (C * (N : ℝ) ^ (-χ)) :=
  hC A c r₀ s₀ v₀ hK r k Cw

theorem expSumConst_mono {n k : ℕ} (hnk : n ≤ k) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) :
    expSumConst n K B ≤ expSumConst k K B := by
  unfold expSumConst
  have : (n : ℝ) * K ≤ k * K := mul_le_mul_of_nonneg_right (by exact_mod_cast hnk) hK
  have h0 : 0 ≤ (n : ℝ) * K := by positivity
  gcongr

theorem abs_sub_le_one_of_mem {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    |x - y| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- **The comparison summed over windows.** See the module docstring. -/
theorem window_comparison (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) {c E ρ R K B Cw η₁ η : ℝ}
    {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ) (hρ : 0 < ρ)
    (hCw : R ≤ Cw * ρ) (hac : rmvStart c N ≤ c) (V₀ : Matrix (Fin N) (Fin r) ℂ)
    (T : Matrix (Fin r) (Fin r) ℂ) (hB : ‖matCLM Tᴴ‖ ≤ B) (hη₁ : 0 ≤ η₁) (hη : 0 ≤ η) {k : ℕ}
    (η₂ : Fin (k + 1) → ℝ) (hη₂ : ∀ n, η₂ n ≤ η)
    (hcmp : ∀ n : Fin (k + 1), ComparisonAt N F c E Cw V₀ n η₁ (η₂ n)) :
    |∫ ω, (markedIntegrand ρ E (V₀ * T) φ (flowMatrix F (rmvStart c N) ω c) -
        gaussIntegrand ρ E φ Tᴴ (flowMatrix F (rmvStart c N) ω c)) ∂flowLaw N (rmvStart c N)| ≤
      expSumConst k K B * η + (k + 1) * η₁ +
        (flowLaw N (rmvStart c N)).real
          {ω | k < (windowSet ρ E R (flowMatrix F (rmvStart c N) ω c)).card} := by
  classical
  set a := rmvStart c N with ha
  set μ := flowLaw N a with hμ
  have hK : 0 ≤ K := (hφ.c2 0).nonneg
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have h𝓛 : pathSigma F a a c ≤ (inferInstance : MeasurableSpace (FlowSample N)) := pathSigma_le F a a c
  set X : FlowSample N → Fin N → ℝ := fun ω ℓ => (N : ℝ) * ρ * (flowEigenvalue F a ω c ℓ - E)
    with hXdef
  have hX : ∀ ℓ, Measurable[pathSigma F a a c] fun ω => X ω ℓ := fun ℓ =>
    measurable_const.mul ((measurable_flowEigenvalue_pathSigma F a a c ⟨hac, le_rfl⟩ ℓ).sub
      measurable_const)
  set W : Finset (Fin N) → Set (FlowSample N) :=
    fun S => {ω | windowSet ρ E R (flowMatrix F a ω c) = S} with hWdef
  have hWm : ∀ S, MeasurableSet[pathSigma F a a c] (W S) := fun S => measurableSet_filter_eq X hX R S
  choose 𝒢 h𝒢m h𝒢p h𝒢c using hcmp
  set G := ⋂ n, 𝒢 n with hGdef
  have hGm : MeasurableSet[pathSigma F a a c] G := MeasurableSet.iInter h𝒢m
  set P := (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card ≤ k) with hPdef
  set Bs : Finset (Fin N) → Set (FlowSample N) := fun S => G ∩ W S with hBsdef
  have hBs𝓛 : ∀ S, MeasurableSet[pathSigma F a a c] (Bs S) := fun S => hGm.inter (hWm S)
  have hBsm : ∀ S, MeasurableSet (Bs S) := fun S => h𝓛 _ (hBs𝓛 S)
  set Dfun : FlowSample N → ℝ := fun ω => markedIntegrand ρ E (V₀ * T) φ (flowMatrix F a ω c) -
    gaussIntegrand ρ E φ Tᴴ (flowMatrix F a ω c) with hDdef
  have hDm : Measurable Dfun :=
    ((measurable_markedIntegrand hφ ρ E _).comp (measurable_flowMatrix F a c)).sub
      ((measurable_gaussIntegrand hφ ρ E _).comp (measurable_flowMatrix F a c))
  have hDb : ∀ ω, ‖Dfun ω‖ ≤ 1 := fun ω => by
    rw [Real.norm_eq_abs]
    exact abs_sub_le_one_of_mem (markedIntegrand_mem hφ ρ E _ _) (gaussIntegrand_mem hφ ρ E _ _)
  have hDi : Integrable Dfun μ := Integrable.of_bound hDm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hDb)
  set U := ⋃ S ∈ P, Bs S with hUdef
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion _ fun S _ => hBsm S
  have hdisj : (↑P : Set (Finset (Fin N))).PairwiseDisjoint Bs := by
    intro S _ S' _ hne
    exact Set.disjoint_left.2 fun ω h1 h2 => hne (h1.2.symm.trans h2.2)
  -- the windows of size `≤ k` inside the good event
  have hterm : ∀ S ∈ P, |∫ ω in Bs S, Dfun ω ∂μ| ≤ expSumConst k K B * η * μ.real (Bs S) := by
    intro S hS
    have hSk : S.card ≤ k := (Finset.mem_filter.1 hS).2
    set n := S.card with hn
    set nF : Fin (k + 1) := ⟨n, Nat.lt_succ_of_le hSk⟩ with hnF
    set ι : Fin n → Fin N := ⇑(S.orderEmbOfFin rfl) with hι
    have hιinj : Function.Injective ι := (S.orderEmbOfFin rfl).injective
    set f : FlowSample N → MarkArray n r → ℝ :=
      fun ω z => windowTest n K B φ Tᴴ (fun m => X ω (ι m)) z with hf
    have hYm : Measurable[pathSigma F a a c] (fun ω => fun m : Fin n => X ω (ι m)) :=
      measurable_pi_of_forall _ fun m => hX (ι m)
    have hfP : IsPathMarkTest (pathSigma F a a c) f :=
      isPathMarkTest_windowTest hφ hB (pathSigma F a a c) _ hYm
    have hsub : Bs S ⊆ 𝒢 nF := fun ω hω => Set.mem_iInter.1 hω.1 nF
    have hwin : ∀ ω ∈ Bs S, ∀ m : Fin n, |flowEigenvalue F a ω c (ι m) - E| ≤ Cw / N := by
      intro ω hω m
      have hm : ι m ∈ windowSet ρ E R (flowMatrix F a ω c) := by
        rw [hω.2]; exact Finset.orderEmbOfFin_mem S rfl m
      simp only [windowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      rw [abs_mul, abs_of_pos (mul_pos hNr hρ)] at hm
      rw [le_div_iff₀ hNr]
      have : (N : ℝ) * ρ * |flowEigenvalue F a ω c (ι m) - E| ≤ Cw * ρ := hm.trans hCw
      nlinarith
    have hc := h𝒢c nF ι hιinj (Bs S) (hBs𝓛 S) hsub hwin f hfP
    -- identify the integrand on `Bs S`
    have heq : Set.EqOn Dfun (fun ω => expSumConst n K B * ∫ θ, (f ω
        (fun m => relativeMark V₀ (flowMatrix F a ω c) θ (ι m)) -
        ∫ g, f ω g ∂gaussianMarkLaw n r) ∂phaseVectorLaw N) (Bs S) := by
      intro ω hω
      have hSω : windowSet ρ E R (flowMatrix F a ω c) = S := hω.2
      have hint : Integrable (fun θ => f ω (fun m => relativeMark V₀ (flowMatrix F a ω c) θ (ι m)))
          (phaseVectorLaw N) := by
        have hz : Measurable (fun θ : Fin N → ℂ =>
            (fun m : Fin n => relativeMark V₀ (flowMatrix F a ω c) θ (ι m))) :=
          measurable_pi_iff.2 fun m =>
            (measurable_relativeMark V₀ (ι m)).comp (measurable_const.prodMk measurable_id)
        have hm0 := (continuous_windowTest hφ n B Tᴴ).measurable.comp
          ((measurable_const (a := fun m : Fin n => X ω (ι m))).prodMk hz)
        have hmeas : Measurable (fun θ : Fin N → ℂ =>
            f ω (fun m => relativeMark V₀ (flowMatrix F a ω c) θ (ι m))) := hm0
        refine Integrable.of_bound (C := 1) hmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall fun θ => ?_)
        · rw [Real.norm_eq_abs]
          exact (isC2Bounded_windowTest hφ hB _).bound _
      have h1 : markedIntegrand ρ E (V₀ * T) φ (flowMatrix F a ω c) = expSumConst n K B *
          ∫ θ, f ω (fun m => relativeMark V₀ (flowMatrix F a ω c) θ (ι m)) ∂phaseVectorLaw N := by
        rw [markedIntegrand, ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun θ =>
          exp_marked_eq_windowTest hφ B hB0 ρ E V₀ T _ S hSω θ)
      have h2 : gaussIntegrand ρ E φ Tᴴ (flowMatrix F a ω c) =
          expSumConst n K B * ∫ g, f ω g ∂gaussianMarkLaw n r :=
        gaussIntegrand_eq_windowTest hφ B hB0 ρ E Tᴴ _ S hSω
      have h3 : ∫ θ, (f ω (fun m => relativeMark V₀ (flowMatrix F a ω c) θ (ι m)) -
            ∫ g, f ω g ∂gaussianMarkLaw n r) ∂phaseVectorLaw N =
          ∫ θ, f ω (fun m => relativeMark V₀ (flowMatrix F a ω c) θ (ι m)) ∂phaseVectorLaw N -
            ∫ g, f ω g ∂gaussianMarkLaw n r := by
        rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
      change markedIntegrand ρ E (V₀ * T) φ (flowMatrix F a ω c) -
        gaussIntegrand ρ E φ Tᴴ (flowMatrix F a ω c) = expSumConst n K B *
          ∫ θ, (f ω (fun m => relativeMark V₀ (flowMatrix F a ω c) θ (ι m)) -
            ∫ g, f ω g ∂gaussianMarkLaw n r) ∂phaseVectorLaw N
      rw [h1, h2, h3, mul_sub]
    rw [setIntegral_congr_fun (hBsm S) heq, integral_const_mul, abs_mul,
      abs_of_pos (by unfold expSumConst; positivity)]
    have hP0 : 0 ≤ μ.real (Bs S) := measureReal_nonneg
    have hc' : |∫ ω in Bs S, ∫ θ, (f ω (fun m => relativeMark V₀ (flowMatrix F a ω c) θ (ι m)) -
        ∫ g, f ω g ∂gaussianMarkLaw n r) ∂phaseVectorLaw N ∂μ| ≤ η * μ.real (Bs S) :=
      hc.trans (mul_le_mul_of_nonneg_right (hη₂ nF) hP0)
    have hMn : expSumConst n K B ≤ expSumConst k K B := expSumConst_mono hSk hK hB0
    have hMn0 : 0 ≤ expSumConst n K B := by unfold expSumConst; positivity
    calc expSumConst n K B * |∫ ω in Bs S, ∫ θ, (f ω
          (fun m => relativeMark V₀ (flowMatrix F a ω c) θ (ι m)) -
          ∫ g, f ω g ∂gaussianMarkLaw n r) ∂phaseVectorLaw N ∂μ|
        ≤ expSumConst n K B * (η * μ.real (Bs S)) := mul_le_mul_of_nonneg_left hc' hMn0
      _ ≤ expSumConst k K B * (η * μ.real (Bs S)) :=
          mul_le_mul_of_nonneg_right hMn (mul_nonneg hη hP0)
      _ = expSumConst k K B * η * μ.real (Bs S) := by ring
  have hUpart : |∫ ω in U, Dfun ω ∂μ| ≤ expSumConst k K B * η := by
    rw [integral_biUnion_finset P (fun S _ => hBsm S) hdisj (fun S _ => hDi.integrableOn)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum, ← measureReal_biUnion_finset hdisj (fun S _ => hBsm S)]
    have hM0 : 0 ≤ expSumConst k K B := by unfold expSumConst; positivity
    calc expSumConst k K B * η * μ.real U ≤ expSumConst k K B * η * 1 :=
          mul_le_mul_of_nonneg_left measureReal_le_one (mul_nonneg hM0 hη)
      _ = expSumConst k K B * η := mul_one _
  -- the complement
  have hcompl : Uᶜ ⊆ (⋃ n, (𝒢 n)ᶜ) ∪
      {ω | k < (windowSet ρ E R (flowMatrix F a ω c)).card} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, not_or, not_exists,
      not_not, Set.mem_ofPred_eq, not_lt] at hcon
    apply hω
    refine Set.mem_biUnion (x := windowSet ρ E R (flowMatrix F a ω c)) ?_ ⟨?_, rfl⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon.2⟩
    · exact Set.mem_iInter.2 hcon.1
  have hCpart : |∫ ω in Uᶜ, Dfun ω ∂μ| ≤ (k + 1) * η₁ +
      μ.real {ω | k < (windowSet ρ E R (flowMatrix F a ω c)).card} := by
    have h1 := norm_setIntegral_le_of_norm_le_const (s := Uᶜ) (μ := μ) (measure_lt_top _ _)
      (fun ω _ => hDb ω)
    rw [Real.norm_eq_abs, one_mul] at h1
    refine h1.trans ((measureReal_mono hcompl).trans ((measureReal_union_le _ _).trans ?_))
    gcongr
    refine (measureReal_iUnion_fintype_le _).trans ?_
    calc ∑ n : Fin (k + 1), μ.real (𝒢 n)ᶜ ≤ ∑ _n : Fin (k + 1), η₁ :=
          Finset.sum_le_sum fun n _ => ENNReal.toReal_le_of_le_ofReal hη₁ (h𝒢p n)
      _ = (k + 1) * η₁ := by simp
  rw [← integral_add_compl hUm hDi]
  refine (abs_add_le _ _).trans ?_
  linarith

end BlockBand.Critical.RelativeVectors
