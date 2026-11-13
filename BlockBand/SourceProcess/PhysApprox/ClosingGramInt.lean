module

public import BlockBand.SourceProcess.PhysApprox.ClosingGramPath
public import BlockBand.SourceProcess.Closing.GaussClosing
public import BlockBand.SourceProcess.ClosingLeak.Phase
public import BlockBand.SourceProcess.Sampling.Mix

/-!
# Phase and probe integrals of the column norms

The integrals of the column norms used for the closing error of the Gram coordinates:

* `lintegral_probe_col`: for a fixed matrix `M`, the probe Gaussian of tag `k` gives
  `E_g ‖M 𝒥_k‖² = (m_k/W) Re Tr(M P_k Mᴴ)`, `P_k = tagProjection` (one normalized tag column
  `√(m_k/W) ι_k g_k`, `g_k ~ CN(0, I_W)`).
* `lintegral_phase_defect`: on a path with `N^n → 0` and the closing covariance identity,
  `E_z ‖(C - 1)ᴴ v‖² = 2 ‖A v‖²` (`lintegral_phase_leak` with `X = vvᴴ`).
* `lintegral_phase_cavity`: `E_z ‖P𝕊Z(z)v‖² ≤ ‖Π𝕊v‖²` for the physical closing data.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingLeak BlockBand.SourceProcess.ClosingAux
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Sampling
open scoped ComplexOrder

section Generic

variable {ρ : Type*} [Fintype ρ]

theorem l2_sq_eq_sum (w : ρ → ℂ) : l2 w ^ 2 = ∑ x, ‖w x‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem l2_smul_sq (c : ℂ) (w : ρ → ℂ) : l2 (c • w) ^ 2 = ‖c‖ ^ 2 * l2 w ^ 2 := by
  rw [l2_sq_eq_sum, l2_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

theorem continuous_l2 : Continuous (l2 : (ρ → ℂ) → ℝ) := by
  unfold l2
  exact (continuous_finsetSum _ fun x _ => ((continuous_apply x).norm.pow 2)).sqrt

theorem measurable_l2_col {α c : Type*} [MeasurableSpace α] {F : α → Matrix ρ c ℂ}
    (hF : Measurable F) (j : c) : Measurable fun a => l2 ((F a)ᵀ j) := by
  refine continuous_l2.measurable.comp ?_
  exact measurable_pi_iff.2 fun x => (hF.eval_matrix (i := x) (j := j))

theorem trace_mul_vecMulVec [DecidableEq ρ] (K : Matrix ρ ρ ℂ) (v : ρ → ℂ) :
    (K * vecMulVec v (star v)).trace = star v ⬝ᵥ (K *ᵥ v) := by
  simp only [Matrix.trace, diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
    Finset.mul_sum, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `‖Mv‖² = Re(v* MᴴM v)`. -/
theorem l2_mulVec_sq {κ : Type*} [Fintype κ] (M : Matrix κ ρ ℂ) (v : ρ → ℂ) :
    l2 (M *ᵥ v) ^ 2 = (star v ⬝ᵥ ((Mᴴ * M) *ᵥ v)).re := by
  rw [l2_sq, star_mulVec_dotProduct]

end Generic

variable {W : ℕ}

/-- The embedding of the probe `g_k` at the block of tag `k`. -/
def tagEmbed (W n c : ℕ) : Matrix (Fin n × Fin W) (Fin W) ℂ :=
  Matrix.of fun x a => if (c < n ∧ x.1.val = n - 1 - c) ∧ x.2 = a then 1 else 0

theorem probeColumns_col {np : ℕ} (n : ℕ) (τ m : Fin np → ℝ) (g : Fin np → Fin W → ℂ)
    (k : Fin np) :
    (probeColumns W n τ m g)ᵀ k =
      ((Real.sqrt (m k / W) : ℝ) : ℂ) • (tagEmbed W n ⌊(W : ℝ) * τ k⌋₊ *ᵥ g k) := by
  ext x
  simp only [transpose_apply, probeColumns, Pi.smul_apply, smul_eq_mul, tagEmbed, mulVec,
    dotProduct, Matrix.of_apply]
  by_cases hP : ⌊(W : ℝ) * τ k⌋₊ < n ∧ x.1.val = n - 1 - ⌊(W : ℝ) * τ k⌋₊
  · simp [hP]
  · simp [hP]

theorem tagEmbed_mul_conjTranspose (n c : ℕ) :
    tagEmbed W n c * (tagEmbed W n c)ᴴ = tagProjection W n c := by
  ext x y
  simp only [tagEmbed, tagProjection, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
    diagonal_apply]
  by_cases hx : c < n ∧ x.1.val = n - 1 - c
  · by_cases hy : c < n ∧ y.1.val = n - 1 - c
    · have h1 : x.1 = y.1 := Fin.ext (hx.2.trans hy.2.symm)
      by_cases h2 : x.2 = y.2
      · have hxy : x = y := Prod.ext h1 h2
        subst hxy
        simp [hx]
      · have hxy : x ≠ y := fun h => h2 (congrArg Prod.snd h)
        simp only [hx, hy, true_and, hxy, ite_false]
        refine Finset.sum_eq_zero fun a _ => ?_
        by_cases ha : x.2 = a
        · subst ha
          simp [Ne.symm h2]
        · simp [ha]
    · have hxy : x ≠ y := fun h => hy (h ▸ hx)
      simp [hy, hxy]
  · by_cases hxy : x = y
    · subst hxy
      simp [hx]
    · simp [hx, hxy]

/-- **One probe Gaussian**: `E_g ‖M 𝒥_k‖² = (m_k/W) Re Tr(M P_k Mᴴ)`. -/
theorem lintegral_probe_col {np : ℕ} (n : ℕ) (τ m : Fin np → ℝ) (k : Fin np) (hm : 0 ≤ m k)
    {ρ : Type*} [Fintype ρ] (M : Matrix ρ (Fin n × Fin W) ℂ) :
    ∫⁻ g, ENNReal.ofReal (l2 (M *ᵥ (probeColumns W n τ m g)ᵀ k) ^ 2)
        ∂(Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)) =
      ENNReal.ofReal (m k / W * (M * tagProjection W n ⌊(W : ℝ) * τ k⌋₊ * Mᴴ).trace.re) := by
  set B := M * tagEmbed W n ⌊(W : ℝ) * τ k⌋₊ with hB
  have hmW : 0 ≤ m k / W := div_nonneg hm (Nat.cast_nonneg W)
  have hpt : ∀ g : Fin np → Fin W → ℂ, l2 (M *ᵥ (probeColumns W n τ m g)ᵀ k) ^ 2 =
      m k / W * ∑ r, ‖(B *ᵥ g k) r‖ ^ 2 := by
    intro g
    rw [probeColumns_col, mulVec_smul, mulVec_mulVec, ← hB, l2_smul_sq, l2_sq_eq_sum,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hmW]
  simp_rw [hpt]
  have hF : Measurable fun u : Fin W → ℂ => ENNReal.ofReal (m k / W * ∑ r, ‖(B *ᵥ u) r‖ ^ 2) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_finsetSum _ fun r _ =>
      ((continuous_apply r).comp (continuous_const.matrix_mulVec continuous_id)).norm.pow
        2))).measurable
  rw [(measurePreserving_eval (fun _ : Fin np => circularVectorLaw (Fin W)) k).lintegral_comp
    (f := fun u => ENNReal.ofReal (m k / W * ∑ r, ‖(B *ᵥ u) r‖ ^ 2)) hF]
  have hint : Integrable (fun u : Fin W → ℂ => ∑ r, ‖(B *ᵥ u) r‖ ^ 2)
      (circularVectorLaw (Fin W)) := by
    simp_rw [mulVec, dotProduct]
    exact integrable_finsetSum _ fun r _ => ComplexSourceLaw.integrable_normSq_lin (B r)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (ae_of_all _ fun u => by positivity), integral_const_mul, integral_normSq_mulVec, hB,
    conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc M, tagEmbed_mul_conjTranspose]

/-- **The phase average of the closing defect on one vector**: `E_z ‖(C - 1)ᴴ v‖² = 2‖Av‖²`. -/
theorem lintegral_phase_defect {b E s T h : ℝ} {ω : GrowthPath W}
    (hN : Tendsto (fun n => closingN (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)
        (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
        (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)) ^ n) atTop (𝓝 0))
    (hD : phaseAvg (fun θ => (physClosingMap b E s T h W ω (phase θ) - 1) *
          (physClosingMap b E s T h W ω (phase θ) - 1)ᴴ) =
        (2 : ℂ) • farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
    (v : Fin 2 × Fin W → ℂ) :
    ∫⁻ θ, ENNReal.ofReal (l2 ((physClosingMap b E s T h W ω (phase θ) - 1)ᴴ *ᵥ v) ^ 2)
        ∂phaseLaw =
      ENNReal.ofReal (2 * l2 (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *ᵥ v) ^ 2) := by
  have hA2 : farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
      farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) =
      farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) := by
    rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))ᴴ =
      farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) := by
    rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have e : ∀ θ, l2 ((physClosingMap b E s T h W ω (phase θ) - 1)ᴴ *ᵥ v) ^ 2 =
      (((physClosingMap b E s T h W ω (phase θ) - 1) *
        (physClosingMap b E s T h W ω (phase θ) - 1)ᴴ) * vecMulVec v (star v)).trace.re := by
    intro θ
    rw [l2_mulVec_sq, conjTranspose_conjTranspose, trace_mul_vecMulVec]
  simp_rw [e]
  rw [lintegral_phase_leak hN hD (posSemidef_vecMulVec_self_star v), Matrix.smul_mul,
    trace_smul, trace_mul_vecMulVec, l2_mulVec_sq, hAH, hA2, smul_eq_mul]
  simp

/-- **The physical cavity bound**: `E_z ‖P𝕊Z(z)v‖² ≤ ‖Π𝕊v‖²`. -/
theorem lintegral_phase_cavity {b E s T h : ℝ} (hh : h ^ 2 < 1) {ω : GrowthPath W}
    (hS : (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)ᴴ * scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω = 1)
    (hN : Tendsto (fun n => closingN (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)
        (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
        (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)) ^ n) atTop (𝓝 0))
    (v : Fin 2 × Fin W → ℂ) :
    ∫⁻ θ, ENNReal.ofReal (l2 (nearProjection W *ᵥ (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω *ᵥ
        (closingZ (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)
          (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
          (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)) (phase θ) *ᵥ v))) ^ 2)
        ∂phaseLaw ≤
      ENNReal.ofReal (l2 (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω) *ᵥ
        (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω *ᵥ v)) ^ 2) := by
  refine lintegral_cavity_le ?_ ?_ ?_ hS hN nearProjection_mul_self nearProjection_conjTranspose
    ?_ v
  · rw [farEmbed_mul, omittedProj_mul_self]
  · rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  · rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  · rw [farEmbed_conjTranspose, nearProjection_mul_farEmbed]

end BlockBand.SourceProcess.PhysApprox
