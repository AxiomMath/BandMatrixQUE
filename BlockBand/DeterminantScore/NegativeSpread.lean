module

public import BlockBand.DeterminantScore.NegativeSpreadLaw
public import BlockBand.DeterminantScore.NegativeSpreadPZ

/-!
# The negative spread, product clause: `E U · E U⁻¹ ≤ 64e⁸`

`negativeSpread_product_of_convexity`: from `IndexedSpectralConvexityStatement` (a hypothesis
here), the `product` field of `NegativeSpreadStatement`, for every `m`, `t > 0`, Hermitian `K`
and attainable sector, with absolute constant `64e⁸`.

Proof: `U = Tr M⁻² = Σλ_j⁻²` a.s. (`invSqSum_orderedEigs`, `det M ≠ 0` a.s.);
`E U, E U⁻¹ < ∞` (`integrable_invSqSum`, `integrable_inv_invSqSum`); the `variance` clause
applied to `√U`, `√U⁻¹`, `log U`, `log U⁻¹` with the energies of `weightedEnergy_comp_le`
(evaluated on the chamber, which carries the law by the `density` clause, `ae_mem_chamber`) gives
`Var √U ≤ E U/2`, `Var √U⁻¹ ≤ E U⁻¹/2`, `Var log U^{±1} ≤ 2`; Paley–Zygmund + Chebyshev
(`integral_le_of_sqrt_log_spread`) gives `E U ≤ 8e⁴e^{E log U}`,
`E U⁻¹ ≤ 8e⁴e^{-E log U}`. For `m = 0`, `U = 0`.

The `inverse_moment` field (`E U^{-q} ≤ C_q (E U)^{-q}`, all `q > 0`) uses Prékopa's theorem
(log-concavity of `P(f ≥ r)`, `f = U^{-1/2}`), which does not follow from the two clauses of
`IndexedSpectralConvexityStatement` alone; it is proved with Prékopa's theorem as a hypothesis in
`negativeSpread_inverse_moment_of_prekopa`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.NegativeSpread

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open scoped ENNReal NNReal ContDiff

variable {m : ℕ} {t : ℝ≥0} {K : Matrix (Fin m) (Fin m) ℂ} {ℓ : ℕ}

/-- The `variance` clause for a spread test `φ ∘ U` with an integrable energy majorant `B`
on the chamber. -/
theorem evariance_comp_le (hconv : IndexedSpectralConvexityStatement) (ht : 0 < t)
    (hK : K.IsHermitian) (hZ : 0 < (sectorMass m t K ℓ).re) (hm : 0 < m) {φ : ℝ → ℝ}
    (hφm : Measurable φ) (hφs : ∀ y : ℝ, 0 < y → ContDiffAt ℝ ∞ φ y)
    {B : (Fin m → ℝ) → ℝ} (hB : Integrable (fun x => B (orderedEigs K x)) (sectorLaw m t K ℓ))
    (hle : ∀ lam ∈ chamber m ℓ, weightedEnergy (t : ℝ) (fun y => φ (invSqSum y)) lam ≤ B lam) :
    evariance (fun x => φ (invSqSum (orderedEigs K x))) (sectorLaw m t K ℓ) ≤
      ∫⁻ x, ENNReal.ofReal (B (orderedEigs K x)) ∂sectorLaw m t K ℓ := by
  have hae := ae_mem_chamber hconv ht hK hZ
  have hmono : ∫⁻ x, ENNReal.ofReal (weightedEnergy (t : ℝ) (fun y => φ (invSqSum y))
        (orderedEigs K x)) ∂sectorLaw m t K ℓ ≤
      ∫⁻ x, ENNReal.ofReal (B (orderedEigs K x)) ∂sectorLaw m t K ℓ :=
    lintegral_mono_ae (hae.mono fun x hx => ENNReal.ofReal_le_ofReal (hle _ hx))
  exact (hconv.variance m t K ℓ ht hK hZ (fun y => φ (invSqSum y))
    (hφm.comp measurable_invSqSum) (contDiffOn_comp_invSqSum hm hφs)
    (ne_top_of_le_ne_top hB.lintegral_lt_top.ne hmono)).trans hmono

/-- **The negative spread, product clause**: from `IndexedSpectralConvexityStatement`, under the
normalized sector law, `E U < ∞` and `E U · E U⁻¹ ≤ 64e⁸`, `U = Tr M⁻²`, for every `m`, `t > 0`,
Hermitian `K` and attainable sector `ℓ`. -/
theorem negativeSpread_product_of_convexity (hconv : IndexedSpectralConvexityStatement)
    (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (ht : 0 < t)
    (hK : K.IsHermitian) (hZ : 0 < (sectorMass m t K ℓ).re) :
    (∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) ≠ ⊤ ∧
      (∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) *
          (∫⁻ x, ENNReal.ofReal (sectorInvSq K x)⁻¹ ∂sectorLaw m t K ℓ) ≤
        ENNReal.ofReal (64 * Real.exp 8) := by
  have := isProbabilityMeasure_sectorLaw hK hZ
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : ∀ x, sectorInvSq K x = 0 := fun x => by simp [sectorInvSq]
    simp [h0]
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 ht
  set μ := sectorLaw m t K ℓ with hμ
  set V : (HermCoord m → ℝ) → ℝ := fun x => invSqSum (orderedEigs K x) with hVdef
  set W : (HermCoord m → ℝ) → ℝ := fun x => (invSqSum (orderedEigs K x))⁻¹ with hWdef
  have hVm : Measurable V := measurable_invSqSum.comp (measurable_orderedEigs K)
  have hWm : Measurable W := hVm.inv
  have hVint : Integrable V μ := integrable_invSqSum hK hZ
  have hWint : Integrable W μ := integrable_inv_invSqSum hm hK hZ
  have hch := ae_mem_chamber hconv ht hK hZ
  have hVpos : ∀ᵐ x ∂μ, 0 < V x :=
    hch.mono fun x hx => invSqSum_pos (ne_zero_of_mem_chamber hx) ⟨0, hm⟩
  have hWpos : ∀ᵐ x ∂μ, 0 < W x := hVpos.mono fun x hx => inv_pos.2 hx
  have hUV : ∀ᵐ x ∂μ, sectorInvSq K x = V x :=
    (ae_det_ne_zero_sectorLaw ht).mono fun x h => (invSqSum_orderedEigs hK h).symm
  -- the four variance bounds
  have hconst : Integrable (fun _ : HermCoord m → ℝ => (2 : ℝ)) μ := integrable_const _
  have hlint2 : ∫⁻ _x, ENNReal.ofReal 2 ∂μ = 2 := by simp
  have hsqV : evariance (fun x => Real.sqrt (V x)) μ ≤ ENNReal.ofReal ((∫ x, V x ∂μ) / 2) := by
    have h := evariance_comp_le hconv ht hK hZ hm Real.continuous_sqrt.measurable
      (fun y hy => Real.contDiffAt_sqrt hy.ne') (B := fun lam => invSqSum lam / 2)
      (hVint.div_const 2) fun lam hlam =>
        weightedEnergy_sqrt_le ht' (ne_zero_of_mem_chamber hlam) ⟨0, hm⟩
    refine h.trans_eq ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hVint.div_const 2)
      (ae_of_all _ fun x => div_nonneg (invSqSum_nonneg _) zero_le_two), integral_div]
  have hsqW : evariance (fun x => Real.sqrt (W x)) μ ≤ ENNReal.ofReal ((∫ x, W x ∂μ) / 2) := by
    have h := evariance_comp_le hconv ht hK hZ hm (φ := fun y => Real.sqrt y⁻¹)
      (Real.continuous_sqrt.measurable.comp measurable_inv)
      (fun y hy => (Real.contDiffAt_sqrt (inv_pos.2 hy).ne').comp y (contDiffAt_inv ℝ hy.ne'))
      (B := fun lam => (invSqSum lam)⁻¹ / 2)
      (hWint.div_const 2) fun lam hlam =>
        weightedEnergy_sqrt_inv_le ht' (ne_zero_of_mem_chamber hlam) ⟨0, hm⟩
    refine h.trans_eq ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hWint.div_const 2)
      (ae_of_all _ fun x => div_nonneg (inv_nonneg.2 (invSqSum_nonneg _)) zero_le_two),
      integral_div]
  have hlogV : evariance (fun x => Real.log (V x)) μ ≤ 2 := by
    have h := evariance_comp_le hconv ht hK hZ hm Real.measurable_log
      (fun y hy => Real.contDiffAt_log.2 hy.ne') (B := fun _ => 2) hconst fun lam hlam =>
        weightedEnergy_log_le ht' (ne_zero_of_mem_chamber hlam) ⟨0, hm⟩
    exact h.trans_eq hlint2
  have hlogW : evariance (fun x => Real.log (W x)) μ ≤ 2 := by
    have h := evariance_comp_le hconv ht hK hZ hm (φ := fun y => Real.log y⁻¹)
      (Real.measurable_log.comp measurable_inv)
      (fun y hy => (Real.contDiffAt_log.2 (inv_pos.2 hy).ne').comp y (contDiffAt_inv ℝ hy.ne'))
      (B := fun _ => 2) hconst fun lam hlam =>
        weightedEnergy_log_inv_le ht' (ne_zero_of_mem_chamber hlam) ⟨0, hm⟩
    exact h.trans_eq hlint2
  -- Paley–Zygmund + Chebyshev
  have hA := integral_le_of_sqrt_log_spread hVm hVpos hVint hsqV hlogV
  have hB := integral_le_of_sqrt_log_spread hWm hWpos hWint hsqW hlogW
  have hlogneg : ∫ x, Real.log (W x) ∂μ = -∫ x, Real.log (V x) ∂μ := by
    simp only [hWdef, hVdef, Real.log_inv]
    exact integral_neg _
  rw [hlogneg] at hB
  have h1 : ∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂μ = ENNReal.ofReal (∫ x, V x ∂μ) := by
    rw [lintegral_congr_ae (hUV.mono fun x h => by rw [h]),
      ofReal_integral_eq_lintegral_ofReal hVint (ae_of_all _ fun x => invSqSum_nonneg _)]
  have h2 : ∫⁻ x, ENNReal.ofReal (sectorInvSq K x)⁻¹ ∂μ = ENNReal.ofReal (∫ x, W x ∂μ) := by
    rw [lintegral_congr_ae (hUV.mono fun x h => by rw [h]),
      ofReal_integral_eq_lintegral_ofReal hWint
        (ae_of_all _ fun x => inv_nonneg.2 (invSqSum_nonneg _))]
  refine ⟨by rw [h1]; exact ENNReal.ofReal_ne_top, ?_⟩
  have hV0 : 0 ≤ ∫ x, V x ∂μ := integral_nonneg fun x => invSqSum_nonneg _
  rw [h1, h2, ← ENNReal.ofReal_mul hV0]
  apply ENNReal.ofReal_le_ofReal
  set M := ∫ x, Real.log (V x) ∂μ
  have e1 : Real.exp 8 = Real.exp 4 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  have e2 : Real.exp M * Real.exp (-M) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc (∫ x, V x ∂μ) * ∫ x, W x ∂μ
      ≤ (8 * Real.exp 4 * Real.exp M) * (8 * Real.exp 4 * Real.exp (-M)) :=
        mul_le_mul hA hB (integral_nonneg fun x => inv_nonneg.2 (invSqSum_nonneg _))
          (by positivity)
    _ = 64 * (Real.exp 4 * Real.exp 4) * (Real.exp M * Real.exp (-M)) := by ring
    _ = 64 * Real.exp 8 := by rw [← e1, e2, mul_one]

end BlockBand.DeterminantScore.NegativeSpread
