module

public import BlockBand.Transmission.PassiveLayer.GaussNorm
public import BlockBand.Transmission.Bridge.GueNull

/-!
# Operator-norm moments of the fresh GUE and Ginibre blocks

* `ginibre_moment`: for `b > 0`, `p ≥ 1` there is `C` with
  `∫ ‖B‖^p dGin_W(b/W) ≤ C` for every `W ≥ 1`.
* `gue_moment`: for `c > 0`, `p ≥ 1` there is `C` with `∫ ‖A‖^p dGUE_W(c/W) ≤ C` for every
  `W ≥ 1` (`A = H + H*`, `H = √(t/2) X`, `X` circular).

Both are `lintegral_norm_rpow_le` with variance proxy `τ/W` (`τ = b`, resp. `c`).
Norm: Euclidean operator norm. Expectations are `lintegral`s of `‖·‖ₑ^p`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexConjugate

variable {n : ℕ}

theorem vecNorm_sq (x : Fin n → ℂ) : vecNorm x ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Ginibre sample in its real coordinates. -/
def ginibreRaw (r : Fin n × Fin n × Fin 2 → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I

theorem isGaussMatrix_ginibreRaw (t : ℝ≥0) :
    IsGaussMatrix (t / 2) (t : ℝ) (ginibreRaw (n := n)) := by
  intro x y
  refine ⟨fun k => (if k.2.2 = 0 then 1 else Complex.I) * (star (y k.1) * x k.2.1), ?_, ?_⟩
  · intro ρ
    simp only [dotProduct, mulVec, ginibreRaw, Matrix.of_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp; ring
  · simp only [Fintype.sum_prod_type, Fin.sum_univ_two, norm_mul, mul_pow]
    simp only [Fin.isValue, ↓reduceIte, norm_one, one_pow, one_mul, one_ne_zero,
      Complex.norm_I, norm_star]
    rw [vecNorm_sq, vecNorm_sq]
    have h : ∑ a, ∑ b, (‖y a‖ ^ 2 * ‖x b‖ ^ 2 + ‖y a‖ ^ 2 * ‖x b‖ ^ 2) =
        2 * ((∑ i, ‖x i‖ ^ 2) * ∑ i, ‖y i‖ ^ 2) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [h, NNReal.coe_div]
    apply le_of_eq
    push_cast
    ring

theorem ginibreMeasure_eq_map (t : ℝ≥0) :
    ginibreMeasure (Fin n) (Fin n) t = (gaussPi (Fin n × Fin n × Fin 2) (t / 2)).map ginibreRaw :=
  rfl

theorem measurable_ginibreRaw : Measurable (ginibreRaw (n := n)) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_ 
  simp only [ginibreRaw, Matrix.of_apply]
  fun_prop

/-- Half of the GUE sample: `√(t/2) X`, `X` the circular coordinates (`gueRaw = H + H*`). -/
def gueHalf (t : ℝ≥0) (ρ : (Fin n × Fin n) × Fin 2 → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => (Real.sqrt ((t : ℝ) / 2) : ℂ) *
    BlockBand.SourceProcess.circularBrownianCoordinates ρ (a, b)

theorem gueRaw_eq (t : ℝ≥0) (ρ : (Fin n × Fin n) × Fin 2 → ℝ) :
    BlockBand.Transmission.Bridge.gueRaw t ρ = gueHalf t ρ + (gueHalf t ρ)ᴴ := by
  ext a b
  simp [BlockBand.Transmission.Bridge.gueRaw, gueSample, gueHalf, Matrix.conjTranspose_apply]
  ring

theorem measurable_gueHalf (t : ℝ≥0) : Measurable (gueHalf (n := n) t) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [gueHalf, Matrix.of_apply, BlockBand.SourceProcess.circularBrownianCoordinates]
  fun_prop

theorem isGaussMatrix_gueHalf (t : ℝ≥0) : IsGaussMatrix 1 (t : ℝ) (gueHalf (n := n) t) := by
  intro x y
  set α : ℂ := (Real.sqrt ((t : ℝ) / 2) : ℂ) / (Real.sqrt 2 : ℂ)
  refine ⟨fun k => α * (if k.2 = 0 then 1 else Complex.I) * (star (y k.1.1) * x k.1.2), ?_, ?_⟩
  · intro ρ
    simp only [dotProduct, mulVec, gueHalf, Matrix.of_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Finset.mul_sum, BlockBand.SourceProcess.circularBrownianCoordinates]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [α]; simp; ring
  · have hα : ‖α‖ ^ 2 = (t : ℝ) / 4 := by
      simp only [α, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
        Real.sq_sqrt (show (0 : ℝ) ≤ (t : ℝ) / 2 by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      ring
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, norm_mul, mul_pow, hα]
    simp only [Fin.isValue, ↓reduceIte, norm_one, one_pow, mul_one, one_ne_zero,
      Complex.norm_I, norm_star, NNReal.coe_one, one_mul]
    rw [vecNorm_sq, vecNorm_sq]
    have h : ∑ a, ∑ b, ((t : ℝ) / 4 * (‖y a‖ ^ 2 * ‖x b‖ ^ 2) +
        (t : ℝ) / 4 * (‖y a‖ ^ 2 * ‖x b‖ ^ 2)) =
        (t : ℝ) / 2 * ((∑ i, ‖x i‖ ^ 2) * ∑ i, ‖y i‖ ^ 2) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [h]
    have h0 : 0 ≤ (∑ i, ‖x i‖ ^ 2) * ∑ i, ‖y i‖ ^ 2 := by positivity
    have ht : (0 : ℝ) ≤ t := t.2
    nlinarith

/-- **Ginibre operator-norm moments**: `E‖B‖^p ≤ C` for `B ~ Gin(b/W)`, uniformly in `W ≥ 1`. -/
theorem ginibre_moment {b : ℝ} (hb : 0 < b) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, ∀ W : ℕ, 1 ≤ W →
      ∫⁻ B, ‖B‖ₑ ^ p ∂ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := lintegral_norm_rpow_le hb hp
  refine ⟨C, fun W hW => ?_⟩
  rw [ginibreMeasure_eq_map, lintegral_map (measurable_enorm.pow_const p) measurable_ginibreRaw]
  have hg := isGaussMatrix_ginibreRaw (n := W) (Real.toNNReal (b / W))
  rw [Real.coe_toNNReal _ (by positivity)] at hg
  exact hC W hW _ _ _ measurable_ginibreRaw hg

/-- **GUE operator-norm moments**: `E‖A‖^p ≤ C` for `A ~ GUE_W(c/W)`, uniformly in `W ≥ 1`. -/
theorem gue_moment {c : ℝ} (hc : 0 < c) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, ∀ W : ℕ, 1 ≤ W →
      ∫⁻ A, ‖A‖ₑ ^ p ∂gueMeasure (Fin W) (Real.toNNReal (c / W)) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := lintegral_norm_rpow_le hc hp
  have hp0 : 0 ≤ p := by linarith
  refine ⟨2 ^ p * C, fun W hW => ?_⟩
  rw [BlockBand.Transmission.Bridge.gueMeasure_eq_map, lintegral_map
    (measurable_enorm.pow_const p) (BlockBand.Transmission.Bridge.measurable_gueRaw _ _)]
  have hg := isGaussMatrix_gueHalf (n := W) (Real.toNNReal (c / W))
  rw [Real.coe_toNNReal _ (by positivity)] at hg
  have hbd := hC W hW _ 1 _ (measurable_gueHalf _) hg
  have hpt : ∀ ρ : (Fin W × Fin W) × Fin 2 → ℝ, ‖BlockBand.Transmission.Bridge.gueRaw (Real.toNNReal (c / W)) ρ‖ₑ ^ p ≤
      ENNReal.ofReal (2 ^ p) * ‖gueHalf (Real.toNNReal (c / W)) ρ‖ₑ ^ p := by
    intro ρ
    rw [gueRaw_eq, ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hp0, ENNReal.ofReal_ofNat,
      ← ENNReal.mul_rpow_of_nonneg _ _ hp0]
    gcongr
    calc ‖gueHalf _ ρ + (gueHalf _ ρ)ᴴ‖ₑ ≤ ‖gueHalf _ ρ‖ₑ + ‖(gueHalf _ ρ)ᴴ‖ₑ := enorm_add_le _ _
      _ = 2 * ‖gueHalf _ ρ‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, Matrix.l2_opNorm_conjTranspose, two_mul]
  calc _ ≤ ∫⁻ ρ, ENNReal.ofReal (2 ^ p) * ‖gueHalf (Real.toNNReal (c / W)) ρ‖ₑ ^ p
          ∂gaussPi ((Fin W × Fin W) × Fin 2) 1 := lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ p) * ∫⁻ ρ, ‖gueHalf (Real.toNNReal (c / W)) ρ‖ₑ ^ p
          ∂gaussPi ((Fin W × Fin W) × Fin 2) 1 :=
        lintegral_const_mul _ ((measurable_enorm.pow_const p).comp (measurable_gueHalf _))
    _ ≤ ENNReal.ofReal (2 ^ p) * ENNReal.ofReal C := by gcongr
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]

end BlockBand.Transmission.PassiveLayer
