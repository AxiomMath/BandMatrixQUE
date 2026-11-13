module

public import BlockBand.Critical.RelativeVectors.WindowSum
public import BlockBand.Critical.RelativeVectors.FrameRoot
public import BlockBand.Critical.RelativeVectors.CountTail
public import BlockBand.Critical.RelativeVectors.Unmarked
public import BlockBand.Critical.WeightedDensity.Relative

/-!
# The decorated-sine clause from the main clause

`relativeMixedVectors_decorated`: the main clause `RelativeMixedVectorsComparison` implies the
decorated-sine clause `RelativeMixedVectorsDecorated`, given `PSSS.SourceContract` (count tail) and
`Inputs.ExternalSine` (unmarked sine limit at variance `c`).

*Law.* `markedLaplace`: `G ~ GUE_N(c/N)` with i.i.d. uniform phases; it equals the terminal law
of `flowLaw N a` at variance `c` (`map_flowMatrix_sub`, `integral_flow_terminal`).
*Limit.* `markedSineLaplace r φ = sineLaplaceFunctional ψ`, `ψ = -log∫e^{-φ(·,g)}γ_r(dg)`.
*Proof.* With `S = V^*ΓV`, `T = S^{1/2}` (`exists_frameRoot`), `V₀ = VT⁻¹` (`V₀^*ΓV₀ = I_r`) and
`L = T^*`:
`|E Ψ₁ - sine| ≤ |E(Ψ₁ - Π I_L)| + |E(Π I_L - Π I)| + |E Π I - sine|`, where
1. `window_comparison` (main clause at every `n ≤ k`, `C_w = πR/v₀`, `D = 1`) bounds the first
   term by `M(k,K,2r) η + (k+1)/N + P(N_R > k)`;
2. `abs_integral_gauss_frame_le` bounds the second by `k K r⁴ ε E‖g‖ + P(N_R > k)`;
3. `unfoldedSine_uniform` (from `ExternalSine`) bounds the third;
4. `unfoldedCount_tail` gives `P(N_R > k) ≤ x^{k+1}/(k+1)!`.
The choices are made in the order: `k` from the tail, then `ε`, then `N₀`.
*Uniformity.* Exactly that of `RelativeMixedVectorsDecorated`: `φ` and `δ` fixed, then `ε, N₀`
uniform over `N ≥ N₀`, `F ∈ FreshClass`, frames with `|(V^*ΓV - I)_{ij}| ≤ ε`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.MomentFlow BlockBand.External

variable {N r : ℕ}

/-!
## Flow terminal law
-/

/-- **Terminal law of the flow.** For `0 ≤ a ≤ σ` and measurable `Ψ`,
`E_{flowLaw N a} Ψ(H_σ) = E Ψ(F + G)`, `G ~ GUE_N(σ/N)` (`map_flowMatrix_sub`).
-/
theorem integral_flow_terminal (F : Matrix (Fin N) (Fin N) ℂ) {a σ : ℝ} (ha : 0 ≤ a)
    (haσ : a ≤ σ) {Ψ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hΨ : Measurable Ψ) :
    ∫ ω, Ψ (flowMatrix F a ω σ) ∂flowLaw N a =
      ∫ G, Ψ (F + G) ∂gueMeasure (Fin N) (Real.toNNReal (σ / N)) := by
  have hm : Measurable (fun G : Matrix (Fin N) (Fin N) ℂ => Ψ (F + G)) :=
    hΨ.comp (measurable_const_add F)
  rw [← map_flowMatrix_sub F ha haσ, integral_map
    ((measurable_flowMatrix F a σ).sub_const F).aemeasurable hm.aestronglyMeasurable]
  simp

theorem measureReal_flow_terminal (F : Matrix (Fin N) (Fin N) ℂ) {a σ : ℝ} (ha : 0 ≤ a)
    (haσ : a ≤ σ) {A : Set (Matrix (Fin N) (Fin N) ℂ)} (hA : MeasurableSet A) :
    (flowLaw N a).real {ω | flowMatrix F a ω σ ∈ A} =
      (gueMeasure (Fin N) (Real.toNNReal (σ / N))).real {G | F + G ∈ A} := by
  have hA' : MeasurableSet {G : Matrix (Fin N) (Fin N) ℂ | F + G ∈ A} :=
    (continuous_const.add continuous_id).measurable hA
  rw [← map_flowMatrix_sub F ha haσ, measureReal_def, measureReal_def,
    Measure.map_apply ((measurable_flowMatrix F a σ).sub_const F) hA']
  congr 2
  ext ω
  simp

theorem measurableSet_windowCard (ρ E R : ℝ) (k : ℕ) :
    MeasurableSet {K : Matrix (Fin N) (Fin N) ℂ | k < (windowSet ρ E R K).card} := by
  classical
  have h : {K : Matrix (Fin N) (Fin N) ℂ | k < (windowSet ρ E R K).card} =
      ⋃ S ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun S => k < S.card),
        {K | windowSet ρ E R K = S} := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨S, hS, hK⟩ => hK ▸ hS⟩
  rw [h]
  refine Finset.measurableSet_biUnion _ fun S _ => ?_
  exact measurableSet_filter_eq (fun K ℓ => (N : ℝ) * ρ * (freshEigenvalue K ℓ - E))
    (fun ℓ => measurable_const.mul
      ((BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue ℓ).sub measurable_const)) R S

/-!
## The frame change on the Gaussian side
-/

/-- **Frame change of the Gaussian integrand.** If `|(L - I)_{ij}| ≤ β`, then for every
probability law `ν` of `G` and every `k`:
`|E Π_ℓ I_L(x_ℓ) - E Π_ℓ I(x_ℓ)| ≤ k K rβ E‖g‖ + P(#{ℓ : |x_ℓ| ≤ R} > k)`,
`x_ℓ = Nρ(λ_ℓ(F + G) - E)`. -/
theorem abs_integral_gauss_frame_le (ν : Measure (Matrix (Fin N) (Fin N) ℂ))
    [IsProbabilityMeasure ν] (F : Matrix (Fin N) (Fin N) ℂ) {R K : ℝ}
    {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ) (ρ E : ℝ)
    (L : Matrix (Fin r) (Fin r) ℂ) {β : ℝ} (hβ : 0 ≤ β) (hL : ∀ i j, ‖(L - 1) i j‖ ≤ β)
    (k : ℕ) :
    |∫ G, gaussIntegrand ρ E φ L (F + G) ∂ν - ∫ G, gaussIntegrand ρ E φ 1 (F + G) ∂ν| ≤
      k * (K * (r * β) * gaussNormMean r) + ν.real {G | k < (windowSet ρ E R (F + G)).card} := by
  classical
  have hK : 0 ≤ K := (hφ.c2 0).nonneg
  set η' := K * (r * β) * gaussNormMean r with hη'
  have hη'0 : 0 ≤ η' := by have := gaussNormMean_nonneg r; positivity
  set A := {G : Matrix (Fin N) (Fin N) ℂ | k < (windowSet ρ E R (F + G)).card} with hAdef
  have hAm : MeasurableSet A :=
    (continuous_const.add continuous_id).measurable (measurableSet_windowCard ρ E R k)
  have hadd : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => F + G :=
    (continuous_const.add continuous_id).measurable
  have hm1 := (measurable_gaussIntegrand hφ ρ E L).comp hadd
  have hm2 := (measurable_gaussIntegrand hφ ρ E 1).comp hadd
  have hi1 : Integrable (fun G => gaussIntegrand ρ E φ L (F + G)) ν :=
    Integrable.of_bound hm1.aestronglyMeasurable 1 (Eventually.of_forall fun G => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussIntegrand_mem hφ ρ E L _).1]
      exact (gaussIntegrand_mem hφ ρ E L _).2)
  have hi2 : Integrable (fun G => gaussIntegrand ρ E φ 1 (F + G)) ν :=
    Integrable.of_bound hm2.aestronglyMeasurable 1 (Eventually.of_forall fun G => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussIntegrand_mem hφ ρ E 1 _).1]
      exact (gaussIntegrand_mem hφ ρ E 1 _).2)
  have hpt : ∀ G, |gaussIntegrand ρ E φ L (F + G) - gaussIntegrand ρ E φ 1 (F + G)| ≤
      k * η' + A.indicator 1 G := by
    intro G
    by_cases hG : G ∈ A
    · rw [Set.indicator_of_mem hG, Pi.one_apply]
      have := abs_sub_le_one_of_mem (gaussIntegrand_mem hφ ρ E L (F + G))
        (gaussIntegrand_mem hφ ρ E 1 (F + G))
      have : 0 ≤ (k : ℝ) * η' := by positivity
      linarith
    · rw [Set.indicator_of_notMem hG, add_zero]
      have hcard : (windowSet ρ E R (F + G)).card ≤ k := by
        simpa [hAdef] using hG
      unfold gaussIntegrand
      refine (abs_prod_sub_prod_le _ _ _ (fun ℓ => markAverageL_mem hφ L _)
        (fun ℓ => markAverageL_mem hφ 1 _)).trans ?_
      rw [← Finset.sum_subset (Finset.subset_univ (windowSet ρ E R (F + G))) ?_]
      · calc ∑ ℓ ∈ windowSet ρ E R (F + G), |markAverageL r φ L
              ((N : ℝ) * ρ * (freshEigenvalue (F + G) ℓ - E)) -
              markAverageL r φ 1 ((N : ℝ) * ρ * (freshEigenvalue (F + G) ℓ - E))|
            ≤ ∑ _ℓ ∈ windowSet ρ E R (F + G), η' := Finset.sum_le_sum fun ℓ _ => by
              rw [markAverageL_one]; exact abs_markAverageL_sub_le hφ L hβ hL _
          _ = (windowSet ρ E R (F + G)).card * η' := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ k * η' := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hη'0
      · intro ℓ _ hℓ
        have hx : R < |(N : ℝ) * ρ * (freshEigenvalue (F + G) ℓ - E)| := by
          simpa [windowSet] using hℓ
        rw [markAverageL_eq_one hφ L hx, markAverageL_eq_one hφ 1 hx, sub_self, abs_zero]
  rw [← integral_sub hi1 hi2]
  refine (abs_integral_le_integral_abs).trans ?_
  have hind : Integrable (A.indicator (1 : Matrix (Fin N) (Fin N) ℂ → ℝ)) ν :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hbi : Integrable (fun G => (k : ℝ) * η' + A.indicator 1 G) ν :=
    (integrable_const _).add hind
  refine (integral_mono (hi1.sub hi2).abs hbi hpt).trans (le_of_eq ?_)
  rw [integral_add (integrable_const _) hind,
    integral_const, probReal_univ, one_smul, integral_indicator_one hAm]

/-- `E Π_ℓ I(x_ℓ) = E exp(-Σ_ℓ ψ(x_ℓ))` (pointwise, `I = e^{-ψ}`). -/
theorem gaussIntegrand_one_eq {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (ρ E : ℝ) (K' : Matrix (Fin N) (Fin N) ℂ) :
    gaussIntegrand ρ E φ 1 K' = Real.exp (-unfoldedSum K' E ρ (markPsiC hφ)) := by
  unfold gaussIntegrand unfoldedSum
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  change markAverageL r φ 1 _ = Real.exp (-markPsi r φ _)
  rw [markAverageL_one, markPsi, neg_neg, Real.exp_log (markAverage_pos hφ _)]

/-!
## Elementary limits
-/

theorem exists_mul_rpow_neg_le {χ : ℝ} (hχ : 0 < χ) (C : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * (N : ℝ) ^ (-χ) ≤ η := by
  have h : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-χ)) atTop (𝓝 (C * 0)) :=
    ((tendsto_rpow_neg_atTop hχ).comp tendsto_natCast_atTop_atTop).const_mul C
  rw [mul_zero] at h
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((tendsto_order.1 h).2 η hη)
  exact ⟨N₀, fun N hN => (hN₀ N hN).le⟩

theorem exists_pow_div_factorial_le (x : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, x ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ) ≤ η := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    ((tendsto_order.1 (FloorSemiring.tendsto_pow_div_factorial_atTop x)).2 η hη)
  exact ⟨n₀, (hn₀ (n₀ + 1) (Nat.le_succ _)).le⟩

theorem norm_one_apply_le (i j : Fin r) : ‖(1 : Matrix (Fin r) (Fin r) ℂ) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

/-!
## The decorated-sine clause
-/

/-- **The relative mixed-vector theorem, decorated-sine clause from the main clause.**
Hypotheses: the main clause `RelativeMixedVectorsComparison` (derived from further hypotheses in
`relativeMixedVectors_comparison`), `PSSS.SourceContract` (count tail `unfoldedCount_tail`) and
`Inputs.ExternalSine` (`unfoldedSine_uniform`).
Conclusion: `RelativeMixedVectorsDecorated` with its exact quantifiers (`φ`, `δ` fixed; `ε`,
`N₀` uniform over `N ≥ N₀`, `FreshClass`, frames with `|(V^*ΓV - I_r)_{ij}| ≤ ε`; law
`GUE_N(c/N)` with uniform phases; limit the sine process with i.i.d.
`CN(0, I_r)` marks).
-/
theorem relativeMixedVectors_decorated (hC : RelativeMixedVectorsComparison)
    (source : PSSS.SourceContract.{0}) (hES : BlockBand.Internal.Contracts.Inputs.ExternalSine) :
    RelativeMixedVectorsDecorated := by
  intro A c r₀ s₀ v₀ hKc r R K φ hφ0 δ hδ
  -- normalize `R ≥ 0`
  set R' := max R 0 with hR'def
  have hφ : IsDecoratedTest r R' K φ :=
    ⟨hφ0.continuous, hφ0.nonneg,
      fun x z hx => hφ0.support x z (lt_of_le_of_lt (le_max_left _ _) hx), hφ0.c2⟩
  have hR' : 0 ≤ R' := le_max_right _ _
  have hK0 : 0 ≤ K := (hφ.c2 0).nonneg
  have hc : 0 < c := hKc.1
  have hv₀ : 0 < v₀ := hKc.2.2.2.2.2
  -- `k` from the count tail
  obtain ⟨CP, hCP, htail⟩ := unfoldedCount_tail source
  set x := 2 * Real.pi * CP * R' / (Real.sqrt c * v₀) with hxdef
  obtain ⟨k, hk⟩ := exists_pow_div_factorial_le x (by positivity : (0 : ℝ) < δ / 10)
  -- `ε` from the frame change
  set B : ℝ := r * 2 with hBdef
  have hB0 : 0 ≤ B := by positivity
  set Mk := expSumConst k K B with hMkdef
  have hMk : 0 < Mk := by rw [hMkdef]; unfold expSumConst; positivity
  set Gm := gaussNormMean r with hGm
  have hGm0 : 0 ≤ Gm := gaussNormMean_nonneg r
  set ε : ℝ := min (min (1 / (2 * ((r : ℝ) ^ 2 + 1))) (1 / ((r : ℝ) ^ 3 + 1)))
    (δ / (10 * ((k : ℝ) * K * (r : ℝ) ^ 4 * Gm + 1))) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε1 : (r : ℝ) ^ 2 * ε ≤ 1 / 2 := by
    have h1 : ε ≤ 1 / (2 * ((r : ℝ) ^ 2 + 1)) := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : (r : ℝ) ^ 2 * (1 / (2 * ((r : ℝ) ^ 2 + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2
  have hε2 : (r : ℝ) ^ 3 * ε ≤ 1 := by
    have h1 : ε ≤ 1 / ((r : ℝ) ^ 3 + 1) := (min_le_left _ _).trans (min_le_right _ _)
    have h2 : (r : ℝ) ^ 3 * (1 / ((r : ℝ) ^ 3 + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2
  have hε3 : (k : ℝ) * (K * (r * ((r : ℝ) ^ 3 * ε)) * Gm) ≤ δ / 10 := by
    have h1 : ε ≤ δ / (10 * ((k : ℝ) * K * (r : ℝ) ^ 4 * Gm + 1)) := min_le_right _ _
    set q := (k : ℝ) * K * (r : ℝ) ^ 4 * Gm with hq
    have hq0 : 0 ≤ q := by positivity
    have heq : (k : ℝ) * (K * (r * ((r : ℝ) ^ 3 * ε)) * Gm) = q * ε := by rw [hq]; ring
    rw [heq]
    calc q * ε ≤ q * (δ / (10 * (q + 1))) := mul_le_mul_of_nonneg_left h1 hq0
      _ ≤ δ / 10 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  -- the comparison constants for `n ≤ k`
  set Cw := Real.pi * R' / v₀ with hCwdef
  have hcmp := fun n : Fin (k + 1) => comparisonAt_of hC (A := A) hKc r n Cw
  choose χ hχ C hcmpD using hcmp
  choose N₀c hN₀c using fun n => hcmpD n 1
  set ηc := δ / (5 * Mk) with hηc
  have hηc0 : 0 < ηc := by positivity
  choose N₁ hN₁ using fun n => exists_mul_rpow_neg_le (hχ n) (C n) hηc0
  obtain ⟨N₂, hN₂⟩ := exists_mul_rpow_neg_le one_pos ((k : ℝ) + 1) (by positivity : (0 : ℝ) < δ / 5)
  obtain ⟨N₃, hN₃⟩ := exists_mul_rpow_neg_le (by norm_num : (0 : ℝ) < 1 / 500) 1 hc
  obtain ⟨N₄, hN₄⟩ := unfoldedSine_uniform hES (A := A) hKc (markPsiC hφ) (markPsi_nonneg hφ)
    (by positivity : (0 : ℝ) < δ / 5)
  refine ⟨ε, hε, max (max (Finset.univ.sup fun n => max (N₀c n) (N₁ n)) N₂) (max (max N₃ N₄) 1),
    fun N hN F E hF V hV => ?_⟩
  have hNsup : (Finset.univ.sup fun n => max (N₀c n) (N₁ n)) ≤ N :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNn : ∀ n, N₀c n ≤ N ∧ N₁ n ≤ N := fun n => by
    have := le_trans (Finset.le_sup (f := fun n => max (N₀c n) (N₁ n)) (Finset.mem_univ n)) hNsup
    exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hN3 : N₃ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hN))
  have hN4 : N₄ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hN))
  have hNpos : 0 < N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  -- variance window
  have ha0 : 0 ≤ rmvStart c N := by
    have := hN₃ N hN3; unfold rmvStart; linarith
  have hac : rmvStart c N ≤ c := by
    unfold rmvStart; have := Real.rpow_nonneg (Nat.cast_nonneg N) (-(1 / 500 : ℝ)); linarith
  -- frame root
  have hSH : (Vᴴ * freshGamma F c E * V).IsHermitian :=
    isHermitian_conjTranspose_mul_mul V
      (BlockBand.Critical.WeightedDensity.freshGamma_isHermitian F hc.le E)
  obtain ⟨T, Tinv, hTh, hTT, hT1, hT2, hTe⟩ := exists_frameRoot hSH hV hε1
  obtain ⟨hV₀, hVT⟩ := frame_renormalize (freshGamma F c E) V hTT hT1 hT2
  have hLe : ∀ i j, ‖(Tᴴ - 1) i j‖ ≤ (r : ℝ) ^ 3 * ε := by rw [hTh]; exact hTe
  have hB : ‖matCLM Tᴴ‖ ≤ B := by
    refine norm_matCLM_le Tᴴ (by norm_num : (0 : ℝ) ≤ 2) fun i j => ?_
    have h : Tᴴ i j = (Tᴴ - 1) i j + (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
      rw [Matrix.sub_apply]; ring
    rw [h]
    refine (norm_add_le _ _).trans ?_
    have := hLe i j
    have := norm_one_apply_le i j
    linarith
  -- the comparison at this `N`
  have hcN : ∀ n : Fin (k + 1), ComparisonAt N F c E Cw (V * Tinv) n ((N : ℝ) ^ (-(1 : ℝ)))
      (C n * (N : ℝ) ^ (-χ n)) := fun n => hN₀c n N (hNn n).1 F E hF (V * Tinv) hV₀
  -- density
  set ρ := unfoldingDensity F c E with hρdef
  obtain ⟨hvd, -⟩ := BlockBand.Critical.PointDensity.freshDyson_im_bounds hKc hF
  have hρ : v₀ / Real.pi ≤ ρ := div_le_div_of_nonneg_right hvd Real.pi_pos.le
  have hρpos : 0 < ρ := lt_of_lt_of_le (div_pos hv₀ Real.pi_pos) hρ
  have hCw : R' ≤ Cw * ρ := by
    have h1 : Cw * (v₀ / Real.pi) = R' := by
      rw [hCwdef]; field_simp
    calc R' = Cw * (v₀ / Real.pi) := h1.symm
      _ ≤ Cw * ρ := mul_le_mul_of_nonneg_left hρ (by positivity)
  have hNr1 : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hW := window_comparison hNpos F hφ hρpos hCw hac (V * Tinv) T hB hNr1 hηc0.le
    (fun n => C n * (N : ℝ) ^ (-χ n)) (fun n => hN₁ n N (hNn n).2) hcN
  rw [hVT] at hW
  -- transfer to `GUE_N(c/N)`
  have hm1 := measurable_markedIntegrand hφ ρ E V
  have hm2 := measurable_gaussIntegrand (N := N) hφ ρ E Tᴴ
  have hmf1 : Integrable (fun ω => markedIntegrand ρ E V φ (flowMatrix F (rmvStart c N) ω c))
      (flowLaw N (rmvStart c N)) :=
    Integrable.of_bound (hm1.comp (measurable_flowMatrix F _ c)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (markedIntegrand_mem hφ ρ E V _).1]
        exact (markedIntegrand_mem hφ ρ E V _).2)
  have hmf2 : Integrable (fun ω => gaussIntegrand ρ E φ Tᴴ (flowMatrix F (rmvStart c N) ω c))
      (flowLaw N (rmvStart c N)) :=
    Integrable.of_bound (hm2.comp (measurable_flowMatrix F _ c)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gaussIntegrand_mem hφ ρ E Tᴴ _).1]
        exact (gaussIntegrand_mem hφ ρ E Tᴴ _).2)
  rw [integral_sub hmf1 hmf2, integral_flow_terminal F ha0 hac hm1,
    integral_flow_terminal F ha0 hac hm2, ← markedLaplace_eq] at hW
  have e3 : (flowLaw N (rmvStart c N)).real
      {ω | k < (windowSet ρ E R' (flowMatrix F (rmvStart c N) ω c)).card} =
      (gueMeasure (Fin N) (Real.toNNReal (c / N))).real
        {G | k < (windowSet ρ E R' (F + G)).card} :=
    measureReal_flow_terminal F ha0 hac (measurableSet_windowCard ρ E R' k)
  rw [e3] at hW
  -- the frame change on the Gaussian side
  have hT2' := abs_integral_gauss_frame_le (gueMeasure (Fin N) (Real.toNNReal (c / N))) F hφ ρ E
    Tᴴ (by positivity) hLe k
  -- unmarked sine limit
  have hT3 := hN₄ N hN4 F E hF
  have he4 : ∫ G, gaussIntegrand ρ E φ 1 (F + G) ∂gueMeasure (Fin N) (Real.toNNReal (c / N)) =
      ∫ G, Real.exp (-unfoldedSum (F + G) E ρ (markPsiC hφ))
        ∂gueMeasure (Fin N) (Real.toNNReal (c / N)) := by
    congr 1; funext G; exact gaussIntegrand_one_eq hφ ρ E (F + G)
  rw [← he4] at hT3
  -- count tail
  have htl : (gueMeasure (Fin N) (Real.toNNReal (c / N))).real
      {G | k < (windowSet ρ E R' (F + G)).card} ≤ δ / 10 := by
    have h := htail A c r₀ s₀ v₀ hKc N hNpos F E hF R' hR' k
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) h).trans hk
  -- combine
  have hNk := hN₂ N hN2
  have hMη : Mk * ηc = δ / 5 := by rw [hηc]; field_simp
  rw [markedSineLaplace_eq_sineLaplace hφ]
  set IL := ∫ G, gaussIntegrand ρ E φ Tᴴ (F + G) ∂gueMeasure (Fin N) (Real.toNNReal (c / N))
    with hIL
  set I1 := ∫ G, gaussIntegrand ρ E φ 1 (F + G) ∂gueMeasure (Fin N) (Real.toNNReal (c / N))
    with hI1
  have t1 := abs_sub_le (markedLaplace c F E V φ) IL (BlockBand.sineLaplaceFunctional (markPsiC hφ))
  have t2 := abs_sub_le IL I1 (BlockBand.sineLaplaceFunctional (markPsiC hφ))
  have hW' : |markedLaplace c F E V φ - IL| ≤ δ / 5 + δ / 5 + δ / 10 := by
    refine hW.trans ?_
    rw [← hMkdef, hMη]
    linarith
  have hT2'' : |IL - I1| ≤ δ / 10 + δ / 10 := by
    refine hT2'.trans ?_
    linarith
  linarith

/-- **The relative mixed-vector theorem from its main clause.** The full statement
(`RelativeMixedVectorsComparison ∧ RelativeMixedVectorsDecorated`) follows from the main clause,
`PSSS.SourceContract` and `Inputs.ExternalSine`. -/
theorem relativeMixedVectorsStatement_of_comparison (hC : RelativeMixedVectorsComparison)
    (source : PSSS.SourceContract.{0}) (hES : BlockBand.Internal.Contracts.Inputs.ExternalSine) :
    RelativeMixedVectorsStatement :=
  ⟨hC, relativeMixedVectors_decorated hC source hES⟩

end BlockBand.Critical.RelativeVectors
