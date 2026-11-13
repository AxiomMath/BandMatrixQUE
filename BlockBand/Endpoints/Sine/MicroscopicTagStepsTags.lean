module

public import BlockBand.Endpoints.Sine.MicroscopicTagStepsCovariance

/-!
# Step 3 of the microscopic tag comparison: the multi-tag covariance change (the `K` trick)

In Step 3 of the proof, the relative change of covariance is legitimate for these sources, by the
last paragraph of the two-positive-clocks lemma; in Step 2, the exceptional tag bound `1/K₀`
holds for each exterior, including its covariance `Γ`.

`ClockCovarianceStabilityContract` compares the Gaussian clocks of `q = Mg` and `q₀ = M₀g`
(`MM* = Γ`, `M₀M₀* = Γ₀`, `(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`) for **one** ratio `v*Cv/v*Dv` with
`Tr(Γ₀C) ≤ K Tr(Γ₀D)`. For the uniform tag test `q⁻¹ Σ_j Φ(q v*D_jv / v*Dv)`, `D = Σ_j D_j`, the
tags with `q Tr(Γ₀D_j) ≤ K Tr(Γ₀D)` are compared by that clause; since
`q⁻¹ Σ_j q Tr(Γ₀D_j)/Tr(Γ₀D) = 1`, at most `q/K` tags are exceptional, each costing `2‖Φ‖`.

* `mts_traceAgainst_nonneg`, `mts_traceAgainst_sum`, `mts_traceAgainst_smul`: `Tr(Γ₀ ·)` is a
  nonnegative linear functional on PSD matrices when `Γ₀ = M₀M₀*`.
* `mts_multiTag_covariance`: `|q⁻¹ Σ_j E Φ(ratio_j(Mg)) - q⁻¹ Σ_j E Φ(ratio_j(M₀g))| ≤ ε + 2‖Φ‖/K`,
  uniformly in `N`, `q ≥ 1` and the tag family. No measurability of the tests is needed
  (the bound `|E f| ≤ ‖Φ‖` holds for every function bounded by `‖Φ‖`).
Law: `g ~ CN(0, I_N)` (`circularVectorLaw (Fin N)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexOrder BoundedContinuousFunction

variable {N : ℕ}

theorem mts_traceAgainst_nonneg (M₀ D : Matrix (Fin N) (Fin N) ℂ) (hD : D.PosSemidef) :
    0 ≤ traceAgainst (M₀ * M₀ᴴ) D := by
  unfold traceAgainst
  have h : (M₀ * M₀ᴴ * D).trace = (M₀ᴴ * D * M₀).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [h]
  have := (hD.conjTranspose_mul_mul_same M₀).trace_nonneg
  exact (Complex.nonneg_iff.1 this).1

theorem mts_traceAgainst_sum (Γ : Matrix (Fin N) (Fin N) ℂ) {q : ℕ}
    (D : Fin q → Matrix (Fin N) (Fin N) ℂ) :
    traceAgainst Γ (∑ j, D j) = ∑ j, traceAgainst Γ (D j) := by
  unfold traceAgainst
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

theorem mts_traceAgainst_smul (Γ D : Matrix (Fin N) (Fin N) ℂ) (q : ℕ) :
    traceAgainst Γ ((q : ℂ) • D) = q * traceAgainst Γ D := by
  unfold traceAgainst
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  simp

/-- At most `q/K` tags are exceptional: `#{j : q a_j > K Σ a} ≤ q/K` for `a_j ≥ 0`, `Σ a > 0`. -/
theorem mts_card_exceptional {q : ℕ} (a : Fin q → ℝ) (ha : ∀ j, 0 ≤ a j) {K : ℝ} (hK : 0 < K)
    (hT : 0 < ∑ j, a j) :
    ((Finset.univ.filter fun j => K * ∑ i, a i < q * a j).card : ℝ) ≤ q / K := by
  set S := Finset.univ.filter fun j => K * ∑ i, a i < q * a j
  rw [le_div_iff₀ hK]
  have h1 : (S.card : ℝ) * (K * ∑ i, a i) ≤ ∑ j ∈ S, q * a j := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j hj => (Finset.mem_filter.1 hj).2.le
  have h2 : ∑ j ∈ S, q * a j ≤ ∑ j, q * a j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (ha j)
  have h3 : ∑ j, (q : ℝ) * a j = q * ∑ j, a j := (Finset.mul_sum _ _ _).symm
  have h4 : (S.card * K) * ∑ i, a i ≤ q * ∑ i, a i := by
    have := h1.trans (h2.trans h3.le); linarith [this]
  exact le_of_mul_le_mul_right h4 hT

/-- **The multi-tag covariance change.** Hypothesis: `ClockCovarianceStabilityContract`. Fixed
first `K > 0`, `Φ ∈ C_b([0,∞))` and `ε > 0`; then there is `ω₀ > 0`; for every `N`,
`Γ₀ = M₀M₀*`, `Γ = MM*` with `(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`, `0 ≤ ω ≤ ω₀`, every `q ≥ 1`, PSD tags `D_j`
with `Tr(Γ₀ Σ D_j) > 0` and measurable default `d`:
`|q⁻¹ Σ_j E Φ(ratio(qD_j, D)(Mg)) - q⁻¹ Σ_j E Φ(ratio(qD_j, D)(M₀g))| ≤ ε + 2‖Φ‖/K`. -/
theorem mts_multiTag_covariance (hCS : ClockCovarianceStabilityContract) {K : ℝ} (hK : 0 < K)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ω₀ : ℝ, 0 < ω₀ ∧
    ∀ (N : ℕ) (Γ₀ Γ : Matrix (Fin N) (Fin N) ℂ) (ω : ℝ), 0 ≤ ω → ω ≤ ω₀ → Γ₀.PosSemidef →
      (((1 + ω : ℝ) : ℂ) • Γ₀ - Γ).PosSemidef → (Γ - ((1 - ω : ℝ) : ℂ) • Γ₀).PosSemidef →
    ∀ (q : ℕ), 0 < q → ∀ Dt : Fin q → Matrix (Fin N) (Fin N) ℂ, (∀ j, (Dt j).PosSemidef) →
      0 < traceAgainst Γ₀ (∑ j, Dt j) →
    ∀ M M₀ : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = Γ → M₀ * M₀ᴴ = Γ₀ →
    ∀ d : (Fin N → ℂ) → ℝ, Measurable d →
      |(q : ℝ)⁻¹ * ∑ j, (∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) d (M *ᵥ g))
            ∂circularVectorLaw (Fin N)) -
          (q : ℝ)⁻¹ * ∑ j, ∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) d (M₀ *ᵥ g))
            ∂circularVectorLaw (Fin N)| ≤ ε + 2 * ‖Φ‖ / K := by
  obtain ⟨ω₀, hω₀, hst⟩ := hCS K 0 Φ ε hε
  refine ⟨ω₀, hω₀, ?_⟩
  intro N Γ₀ Γ ω hω0 hω hΓ₀ h1 h2 q hq Dt hDt hT M M₀ hM hM₀ d hd
  have hPcv : IsProbabilityMeasure (circularVectorLaw (Fin N)) := by
    unfold circularVectorLaw; infer_instance
  set T := traceAgainst Γ₀ (∑ j, Dt j)
  set a : Fin q → ℝ := fun j => traceAgainst Γ₀ (Dt j)
  have ha : ∀ j, 0 ≤ a j := fun j => by
    simp only [a]; rw [← hM₀]; exact mts_traceAgainst_nonneg M₀ _ (hDt j)
  have hTa : T = ∑ j, a j := mts_traceAgainst_sum Γ₀ Dt
  set Δ : Fin q → ℝ := fun j =>
    (∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) d (M *ᵥ g)) ∂circularVectorLaw (Fin N)) -
      ∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) d (M₀ *ᵥ g)) ∂circularVectorLaw (Fin N)
  have hbd : ∀ (v : Fin N → ℂ) (C : Matrix (Fin N) (Fin N) ℂ),
      ‖Φ (ratioHalfLine C (∑ j, Dt j) d v)‖ ≤ ‖Φ‖ := fun v C => Φ.norm_coe_le_norm _
  have hΔ2 : ∀ j, |Δ j| ≤ 2 * ‖Φ‖ := by
    intro j
    have e1 := norm_integral_le_of_norm_le_const (μ := circularVectorLaw (Fin N)) (C := ‖Φ‖)
      (ae_of_all _ fun g => hbd (M *ᵥ g) ((q : ℂ) • Dt j))
    have e2 := norm_integral_le_of_norm_le_const (μ := circularVectorLaw (Fin N)) (C := ‖Φ‖)
      (ae_of_all _ fun g => hbd (M₀ *ᵥ g) ((q : ℂ) • Dt j))
    simp only [probReal_univ, mul_one, Real.norm_eq_abs] at e1 e2
    simp only [Δ]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ ‖Φ‖ + ‖Φ‖ := add_le_add e1 e2
      _ = 2 * ‖Φ‖ := by ring
  have hΔε : ∀ j, q * a j ≤ K * T → |Δ j| ≤ ε := by
    intro j hj
    have hC : traceAgainst Γ₀ ((q : ℂ) • Dt j) ≤ K * traceAgainst Γ₀ (∑ j, Dt j) := by
      rw [mts_traceAgainst_smul]; exact hj
    have hpsd : ((q : ℂ) • Dt j).PosSemidef := by
      have : ((q : ℂ) • Dt j) = ((q : ℝ) : ℂ) • Dt j := by norm_cast
      rw [this]
      exact (hDt j).smul (by exact_mod_cast (Nat.cast_nonneg q : (0 : ℝ) ≤ q))
    have hDsum : (∑ j, Dt j).PosSemidef := posSemidef_sum _ fun j _ => hDt j
    exact (hst N Γ₀ Γ ω hω0 hω hΓ₀ h1 h2 (∑ j, Dt j) ((q : ℂ) • Dt j) hDsum hpsd hT hC M M₀
      hM hM₀ d hd).2
  -- sum over the tags
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [abs_mul, abs_of_pos (inv_pos.2 hq')]
  set S := Finset.univ.filter fun j => K * ∑ i, a i < q * a j
  have hsplit : ∀ j, |Δ j| ≤ ε + (if j ∈ S then 2 * ‖Φ‖ else 0) := by
    intro j
    by_cases hj : j ∈ S
    · rw [ite_eq_left hj]; linarith [hΔ2 j]
    · rw [ite_eq_right hj, add_zero]
      refine hΔε j ?_
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
      rw [hTa]; exact hj
  have hcard := mts_card_exceptional a ha hK (by rw [← hTa]; exact hT)
  calc (q : ℝ)⁻¹ * |∑ j, Δ j| ≤ (q : ℝ)⁻¹ * ∑ j, (ε + if j ∈ S then 2 * ‖Φ‖ else 0) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => hsplit j)) (by positivity)
    _ = ε + (q : ℝ)⁻¹ * (2 * ‖Φ‖ * S.card) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        field_simp
    _ ≤ ε + (q : ℝ)⁻¹ * (2 * ‖Φ‖ * (q / K)) := by
        gcongr
    _ = ε + 2 * ‖Φ‖ / K := by
        field_simp

end BlockBand.Endpoints
