module

public import BlockBand.Endpoints.Clock.DetClockCovariance
public import BlockBand.Endpoints.Clock.ClockMixingEnergyUniform
public import BlockBand.Endpoints.Clock.MovingEnergyRuledHyps

/-!
# The deterministic-clock lemma on `bulkInterval κ`: the covariance identities, energy-uniform

`DetClockCov.covIdentities_of` and `DetClockCov.covTraceSquare_of` take their constants from
`PassiveCovarianceContract` at a fixed `E` and a fixed stationary jet `s`, and from
`PassiveSourceMixingContract.oneStepFluctuation` (`p = 2`, integrability only) at that `E`. Here
they come instead from:
* `MovingEnergy.PassiveCovarianceEnergyUniformHyp`: `κ` before `C, W₀`, then
  `∀ E ∈ bulkInterval κ, ∀ s, IsStationaryJet b E s`;
* `TransmissionUniform3.PassiveSourceMixingEnergyUniformContract.oneStepFluctuation` (`p = 2`),
  for the integrability of the products of centered entries.

The algebra (diagonalizing `A`) is the same. The only other `E`-dependent constant is `|σ₋|`; it is
bounded by `sigmaMax b κ = r_κ/(b + g_κ)` (`norm_sigmaMinus_le`, as in
`norm_thetaStar_le_thetaMax`: `|k₋| ≤ r_κ`, `|1 + k₋s| ≥ b + g_κ`).

* `covIdentities_unif`: the two identities with explicit same-sign terms, `C, W₀` depending only
  on `(b, κ)`, uniformly in `E ∈ bulkInterval κ` and in the stationary jet `s`.
* `covTraceSquare_unif`: the trace-square and square-trace bounds, with the same uniformity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexConjugate Matrix Matrix.Norms.L2Operator ComplexOrder

namespace MovingEnergy

namespace DetClockBulk

open DetClockCov ClockMixingAlg
open BlockBand.Internal.Contracts.TransmissionUniform3

variable {b κ : ℝ}

/-- `σ_max = r_κ/(b + g_κ)`, the uniform bound of `|σ₋|` on `bulkInterval κ`. -/
def sigmaMax (b κ : ℝ) : ℝ := kHigh b κ / (b + gapLow b κ)

theorem sigmaMax_nonneg (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) : 0 ≤ sigmaMax b κ := by
  have := gapLow_pos hb0 hb1 hκ
  have : 0 ≤ kHigh b κ := Real.sqrt_nonneg _
  unfold sigmaMax; positivity

/-- **`|σ₋| ≤ σ_max`, uniformly** in `E ∈ bulkInterval κ` and in the stationary jet `s`:
`|k₋| ≤ r_κ` and `|1 + k₋s| ≥ 1 - r_κ d_* = b + g_κ`. -/
theorem norm_sigmaMinus_le (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) {E : ℝ}
    (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s) :
    ‖sigmaMinus b E s‖ ≤ sigmaMax b κ := by
  have hk := norm_kMinus_le_kHigh hb1 hκ hE
  have hg := gapLow_pos hb0 hb1 hκ
  have hks : ‖kMinus b E * s‖ ≤ kHigh b κ * dStar b := by
    rw [norm_mul]
    exact mul_le_mul hk hs.2 (norm_nonneg _) (Real.sqrt_nonneg _)
  have hden : b + gapLow b κ ≤ ‖1 + kMinus b E * s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(kMinus b E * s))
    rw [norm_neg, norm_one, sub_neg_eq_add] at this
    unfold gapLow
    linarith
  unfold sigmaMinus sigmaMax
  rw [norm_div]
  exact div_le_div₀ (Real.sqrt_nonneg _) hk (by positivity) hden

/-- **The covariance trace-square and square-trace identities with explicit same-sign terms,
uniformly in `E ∈ bulkInterval κ` and in the stationary jet** (the uniform version of
`DetClockCov.covIdentities_of`), from `PassiveCovarianceEnergyUniformHyp` by diagonalizing `A`. -/
theorem covIdentities_unif (hcov : PassiveCovarianceEnergyUniformHyp)
    (hmix : PassiveSourceMixingEnergyUniformContract) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ A : Matrix (Fin W) (Fin W) ℂ, A.PosSemidef →
        ‖(∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * A.trace ^ 2 -
            sigmaMinus b E s / W * (A * passiveF b E X).trace ^ 2 -
            conj (sigmaMinus b E s) / W * (A * (passiveF b E X)ᴴ).trace ^ 2‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)) *
            A.trace.re ^ 2 ∧
        ‖(∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * (A * A).trace -
            sigmaMinus b E s / W * (A * passiveF b E X * A * passiveF b E X).trace -
            conj (sigmaMinus b E s) / W *
              (A * (passiveF b E X)ᴴ * A * (passiveF b E X)ᴴ).trace‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)) *
            A.trace.re ^ 2 := by
  obtain ⟨C, W₀, hC⟩ := hcov b hb0 hb1 κ hκ
  obtain ⟨Cf, Wf, hfl⟩ := hmix.oneStepFluctuation b hb0 hb1 κ hκ 2 (by norm_num)
  refine ⟨C, max (max W₀ Wf) 1, fun W hWW E hE s hs X hX A hA => ?_⟩
  have hW0 : W₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWW
  have hWf : Wf ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWW
  have hWpos : 0 < W := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hWW)
  have hWne : (W : ℂ) ≠ 0 := by exact_mod_cast hWpos.ne'
  set μ := freshLaw W b with hμ
  set f := passiveF b E X with hf
  set D₀ := transportD0 b E with hD₀
  set σ := sigmaMinus b E s with hσ
  set ε := C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X))
    with hε
  set v : Fin W → Fin W → ℂ := fun i a => eU hA.1 a i with hv
  have hα0 : ∀ i, 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg
  have hvn : ∀ i, vecNorm (v i) = 1 := fun i => vecNorm_eU_col hA.1 i
  have h4 : ∀ i k l m, fourNorm (v i) (v k) (v l) (v m) = 1 := fun i k l m => by
    unfold fourNorm; rw [hvn, hvn, hvn, hvn]; ring
  have hfl2 := fun u w => (hfl W hWf E hE X (passiveY_posSemidef hX) u w).1
  have hmem := memLp_bilinear_freshU0 b E X hfl2
  have hT := passiveTransmission_eq_zero b E hX
  have hq := passiveMass_eq_zero b E hX
  have hcon : ∀ i k l m, ‖bilinearCovariance μ (freshU b E X) (v i) (v k) (v l) (v m) -
      ((((D₀ / (2 * W) : ℝ)) : ℂ) * (crossedTensor (v i) (v k) (v l) (v m) 1 1 +
          crossedTensor (v i) (v k) (v l) (v m) 1 1) +
        σ / W * crossedTensor (v i) (v k) (v l) (v m) f f +
        conj σ / W * crossedTensor (v i) (v k) (v l) (v m) fᴴ fᴴ)‖ ≤ ε := by
    intro i k l m
    have h := hC W hW0 E hE s hs X (passiveY_posSemidef hX) (v i) (v k) (v l) (v m)
    simp only [hT, sub_zero, hq, zero_div, add_zero, h4, mul_one] at h
    exact h
  have hbil : ∀ (M : Matrix (Fin W) (Fin W) ℂ) i k, bilinear (v i) M (v k) = rot hA.1 M i k :=
    fun M i k => (rot_apply hA.1 M i k).symm
  have hcovint : ∀ i k l m, bilinearCovariance μ (freshU b E X) (v i) (v k) (v l) (v m) =
      ∫ ω, rot hA.1 (freshU0 b E X ω) i k * rot hA.1 (freshU0 b E X ω) l m ∂μ := by
    intro i k l m
    unfold bilinearCovariance
    simp only [← hbil]
    rfl
  have hint : ∀ i k l m, Integrable (fun ω =>
      rot hA.1 (freshU0 b E X ω) i k * rot hA.1 (freshU0 b E X ω) l m) μ := by
    intro i k l m
    have h1 := hmem (v i) (v k)
    have h2 := hmem (v l) (v m)
    simp only [hbil] at h1 h2
    exact h1.integrable_mul h2
  have hTrA : A.trace = ∑ i, (hA.1.eigenvalues i : ℂ) := trace_eq_sum hA.1
  have hTrAre : A.trace.re = ∑ i, hA.1.eigenvalues i := by rw [hTrA, Complex.re_sum]; simp
  have herr : ∀ (c : Fin W → Fin W → ℂ), (∀ i k, ‖c i k‖ ≤ ε) →
      ‖∑ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) * c i k‖ ≤
        ε * A.trace.re ^ 2 := by
    intro c hc
    rw [hTrAre, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hα0 i),
      Real.norm_of_nonneg (hα0 k)]
    have := mul_le_mul_of_nonneg_left (hc i k) (mul_nonneg (hα0 i) (hα0 k))
    linarith
  have hrot1 : ∀ i k, rot hA.1 (1 : Matrix (Fin W) (Fin W) ℂ) i k = if i = k then 1 else 0 :=
    fun i k => by rw [rot_one, Matrix.one_apply]
  constructor
  · have hexp : (∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂μ) =
        ∑ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          bilinearCovariance μ (freshU b E X) (v i) (v k) (v k) (v i) := by
      simp only [trace_sandwich_two hA.1, hcovint]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        (hint i k k i).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun k _ => (hint i k k i).const_mul _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul]
    have hmain : (((D₀ / W : ℝ)) : ℂ) * A.trace ^ 2 + σ / W * (A * f).trace ^ 2 +
        conj σ / W * (A * fᴴ).trace ^ 2 =
        ∑ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          ((((D₀ / (2 * W) : ℝ)) : ℂ) * (crossedTensor (v i) (v k) (v k) (v i) 1 1 +
            crossedTensor (v i) (v k) (v k) (v i) 1 1) +
          σ / W * crossedTensor (v i) (v k) (v k) (v i) f f +
          conj σ / W * crossedTensor (v i) (v k) (v k) (v i) fᴴ fᴴ) := by
      simp only [crossedTensor, hbil, hrot1, ite_true]
      rw [hTrA, trace_mul_eq_sum hA.1 f, trace_mul_eq_sum hA.1 fᴴ]
      have hterm : ∀ i k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          ((((D₀ / (2 * W) : ℝ)) : ℂ) * (1 * 1 + 1 * 1) +
            σ / W * (rot hA.1 f i i * rot hA.1 f k k) +
            conj σ / W * (rot hA.1 fᴴ i i * rot hA.1 fᴴ k k)) =
          (((D₀ / W : ℝ)) : ℂ) * ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ)) +
            σ / W * (((hA.1.eigenvalues i : ℂ) * rot hA.1 f i i) *
              ((hA.1.eigenvalues k : ℂ) * rot hA.1 f k k)) +
            conj σ / W * (((hA.1.eigenvalues i : ℂ) * rot hA.1 fᴴ i i) *
              ((hA.1.eigenvalues k : ℂ) * rot hA.1 fᴴ k k)) := by
        intro i k
        push_cast
        field_simp
        ring
      simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sq]
    rw [show (∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂μ) -
        (((D₀ / W : ℝ)) : ℂ) * A.trace ^ 2 - σ / W * (A * f).trace ^ 2 -
        conj σ / W * (A * fᴴ).trace ^ 2 =
        (∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂μ) -
          ((((D₀ / W : ℝ)) : ℂ) * A.trace ^ 2 + σ / W * (A * f).trace ^ 2 +
            conj σ / W * (A * fᴴ).trace ^ 2) by ring, hexp, hmain, ← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    exact herr _ fun i k => hcon i k k i
  · have hexp : (∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂μ) =
        ∑ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          bilinearCovariance μ (freshU b E X) (v i) (v i) (v k) (v k) := by
      simp only [trace_mul_eq_sum hA.1, hcovint, sq, Finset.sum_mul_sum]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => by
        have := (hint i i k k).const_mul ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ))
        refine this.congr (ae_of_all _ fun ω => ?_)
        simp only; ring]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun k _ => by
        have := (hint i i k k).const_mul ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ))
        refine this.congr (ae_of_all _ fun ω => ?_)
        simp only; ring]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← integral_const_mul]
      congr 1; funext ω; ring
    have hmain : (((D₀ / W : ℝ)) : ℂ) * (A * A).trace + σ / W * (A * f * A * f).trace +
        conj σ / W * (A * fᴴ * A * fᴴ).trace =
        ∑ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          ((((D₀ / (2 * W) : ℝ)) : ℂ) * (crossedTensor (v i) (v i) (v k) (v k) 1 1 +
            crossedTensor (v i) (v i) (v k) (v k) 1 1) +
          σ / W * crossedTensor (v i) (v i) (v k) (v k) f f +
          conj σ / W * crossedTensor (v i) (v i) (v k) (v k) fᴴ fᴴ) := by
      simp only [crossedTensor, hbil]
      rw [trace_sandwich_two hA.1 f f, trace_sandwich_two hA.1 fᴴ fᴴ, trace_mul_self_eq_sum hA.1]
      have hterm : ∀ i k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          ((((D₀ / (2 * W) : ℝ)) : ℂ) * (rot hA.1 1 i k * rot hA.1 1 k i +
            rot hA.1 1 i k * rot hA.1 1 k i) +
            σ / W * (rot hA.1 f i k * rot hA.1 f k i) +
            conj σ / W * (rot hA.1 fᴴ i k * rot hA.1 fᴴ k i)) =
          (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
            ((((D₀ / (2 * W) : ℝ)) : ℂ) * (rot hA.1 1 i k * rot hA.1 1 k i +
              rot hA.1 1 i k * rot hA.1 1 k i)) +
            σ / W * ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
              (rot hA.1 f i k * rot hA.1 f k i)) +
            conj σ / W * ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
              (rot hA.1 fᴴ i k * rot hA.1 fᴴ k i)) := by
        intro i k; ring
      have hdiag : ∀ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          ((((D₀ / (2 * W) : ℝ)) : ℂ) * (rot hA.1 1 i k * rot hA.1 1 k i +
            rot hA.1 1 i k * rot hA.1 1 k i)) =
          (((D₀ / W : ℝ)) : ℂ) * ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues i : ℂ)) := by
        intro i
        rw [Finset.sum_eq_single i]
        · simp only [hrot1, ite_true]; push_cast; ring
        · intro k _ hk; simp [hrot1, Ne.symm hk]
        · simp
      simp only [hterm, Finset.sum_add_distrib, hdiag, ← Finset.mul_sum]
    rw [show (∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂μ) -
        (((D₀ / W : ℝ)) : ℂ) * (A * A).trace - σ / W * (A * f * A * f).trace -
        conj σ / W * (A * fᴴ * A * fᴴ).trace =
        (∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂μ) -
          ((((D₀ / W : ℝ)) : ℂ) * (A * A).trace + σ / W * (A * f * A * f).trace +
            conj σ / W * (A * fᴴ * A * fᴴ).trace) by ring, hexp, hmain]
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    exact herr _ fun i k => hcon i i k k

/-- **The covariance trace-square and square-trace bounds, uniformly in `E ∈ bulkInterval κ` and in
the stationary jet** (the uniform version of `DetClockCov.covTraceSquare_of`; `|σ₋| ≤ σ_max`):
`|E Tr(AU⁰AU⁰) - (D₀/W)(Tr A)²| ≤ C(|Tr(Af)|²/W + [W⁻² + W⁻¹(δ₀ + δ₁)](Tr A)²)` and
`|E (Tr AU⁰)² - (D₀/W) Tr A²| ≤ C(Tr(AfAf*)/W + [W⁻² + W⁻¹(δ₀ + δ₁)](Tr A)²)`. -/
theorem covTraceSquare_unif (hcov : PassiveCovarianceEnergyUniformHyp)
    (hmix : PassiveSourceMixingEnergyUniformContract) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ A : Matrix (Fin W) (Fin W) ℂ, A.PosSemidef →
        ‖(∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * A.trace ^ 2‖ ≤
          C * (‖(A * passiveF b E X).trace‖ ^ 2 / W +
            ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)) *
              A.trace.re ^ 2) ∧
        ‖(∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * (A * A).trace‖ ≤
          C * ((A * passiveF b E X * A * (passiveF b E X)ᴴ).trace.re / W +
            ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)) *
              A.trace.re ^ 2) := by
  obtain ⟨C₀, W₀, h⟩ := covIdentities_unif hcov hmix hb0 hb1 hκ
  have hσm := sigmaMax_nonneg hb0 hb1 hκ
  refine ⟨max C₀ 0 + 2 * sigmaMax b κ, W₀, fun W hW E hE s hs X hX A hA => ?_⟩
  obtain ⟨h1, h2⟩ := h W hW E hE s hs X hX A hA
  set σ := sigmaMinus b E s
  have hσle : ‖σ‖ ≤ sigmaMax b κ := norm_sigmaMinus_le hb0 hb1 hκ hE hs
  set f := passiveF b E X
  set e := (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)
  have he : 0 ≤ e := by
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    positivity
  have hTA : 0 ≤ A.trace.re ^ 2 := sq_nonneg _
  have hW0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hσW : ‖σ / (W : ℂ)‖ = ‖σ‖ / W := by rw [norm_div, Complex.norm_natCast]
  have hσW' : ‖(starRingEnd ℂ) σ / (W : ℂ)‖ = ‖σ‖ / W := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_conj]
  have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg _
  have hmax : 0 ≤ max C₀ 0 := le_max_right _ _
  have hC0 : C₀ * e * A.trace.re ^ 2 ≤ max C₀ 0 * (e * A.trace.re ^ 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg he hTA)
  have hmono : ∀ x : ℝ, 0 ≤ x → (max C₀ 0 + 2 * ‖σ‖) * x ≤ (max C₀ 0 + 2 * sigmaMax b κ) * x :=
    fun x hx => mul_le_mul_of_nonneg_right (by linarith) hx
  constructor
  · have hn := norm_trace_mul_conjTranspose hA.1 f
    set g := ‖(A * f).trace‖
    have hsame : ‖σ / W * (A * f).trace ^ 2 + (starRingEnd ℂ) σ / W * (A * fᴴ).trace ^ 2‖ ≤
        2 * ‖σ‖ * (g ^ 2 / W) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, norm_pow, hσW, hσW', hn]
      have : ‖σ‖ / W * g ^ 2 = ‖σ‖ * (g ^ 2 / W) := by ring
      linarith
    have hx0 : 0 ≤ g ^ 2 / W + e * A.trace.re ^ 2 := by positivity
    refine le_trans ?_ (hmono _ hx0)
    calc ‖(∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂freshLaw W b) -
          (((transportD0 b E / W : ℝ)) : ℂ) * A.trace ^ 2‖
        ≤ ‖(∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * A.trace ^ 2 - σ / W * (A * f).trace ^ 2 -
            (starRingEnd ℂ) σ / W * (A * fᴴ).trace ^ 2‖ +
          ‖σ / W * (A * f).trace ^ 2 + (starRingEnd ℂ) σ / W * (A * fᴴ).trace ^ 2‖ := by
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; ring
      _ ≤ C₀ * e * A.trace.re ^ 2 + 2 * ‖σ‖ * (g ^ 2 / W) := add_le_add h1 hsame
      _ ≤ (max C₀ 0 + 2 * ‖σ‖) * (g ^ 2 / W + e * A.trace.re ^ 2) := by
          have : 0 ≤ g ^ 2 / W := by positivity
          nlinarith [mul_nonneg hmax this, mul_nonneg hσ0 (mul_nonneg he hTA)]
  · set g := (A * f * A * fᴴ).trace.re
    have hg1 := norm_trace_sandwich_le hA f
    have hg2 := norm_trace_sandwich_conj_le hA f
    have hg0 : 0 ≤ g := (norm_nonneg _).trans hg1
    have hsame : ‖σ / W * (A * f * A * f).trace +
        (starRingEnd ℂ) σ / W * (A * fᴴ * A * fᴴ).trace‖ ≤ 2 * ‖σ‖ * (g / W) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hσW, hσW']
      have e1 : ‖σ‖ / W * ‖(A * f * A * f).trace‖ ≤ ‖σ‖ / W * g :=
        mul_le_mul_of_nonneg_left hg1 (by positivity)
      have e2 : ‖σ‖ / W * ‖(A * fᴴ * A * fᴴ).trace‖ ≤ ‖σ‖ / W * g :=
        mul_le_mul_of_nonneg_left hg2 (by positivity)
      have : ‖σ‖ / W * g = ‖σ‖ * (g / W) := by ring
      linarith
    have hx0 : 0 ≤ g / W + e * A.trace.re ^ 2 := by positivity
    refine le_trans ?_ (hmono _ hx0)
    calc ‖(∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
          (((transportD0 b E / W : ℝ)) : ℂ) * (A * A).trace‖
        ≤ ‖(∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * (A * A).trace - σ / W * (A * f * A * f).trace -
            (starRingEnd ℂ) σ / W * (A * fᴴ * A * fᴴ).trace‖ +
          ‖σ / W * (A * f * A * f).trace +
            (starRingEnd ℂ) σ / W * (A * fᴴ * A * fᴴ).trace‖ := by
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; ring
      _ ≤ C₀ * e * A.trace.re ^ 2 + 2 * ‖σ‖ * (g / W) := add_le_add h2 hsame
      _ ≤ (max C₀ 0 + 2 * ‖σ‖) * (g / W + e * A.trace.re ^ 2) := by
          have : 0 ≤ g / W := by positivity
          nlinarith [mul_nonneg hmax this, mul_nonneg hσ0 (mul_nonneg he hTA)]

end DetClockBulk

end MovingEnergy

end BlockBand.Endpoints.Clock
