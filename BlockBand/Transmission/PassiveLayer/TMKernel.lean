module

public import BlockBand.Transmission.PassiveLayer.TMVar
public import BlockBand.Transmission.PassiveLayer.TMReg
public import BlockBand.Transmission.PassiveLayer.OUCov

/-!
# Kernel algebra, the `W⁻²` kernel bound, AM–GM, moments and the law of `x_t`

* `tm_kernel_eq` (deterministic): with `∂ᵢf = w Tr(Σⱼ aⱼ Nᵢ cⱼ)` (`aⱼ : W × 2W`,
  `cⱼ : 2W × W`) and `∂ᵢU = Σₖ a'ₖ Nᵢ c'ₖ`,
  `Σᵢ vᵢ ∂ᵢf ∂ᵢU = w Σⱼ Σₖ a'ₖ 𝒱(cⱼaⱼ) c'ₖ`, `𝒱 = tmV`.
* `tm_kernel_le`: `‖W⁻¹ Σⱼ Σₖ a'ₖ 𝒱(cⱼaⱼ) c'ₖ‖ ≤ 3 ℓ_f ℓ_U B_f B_U / W²` (operator norm;
  `tm_contract_le`, the exact contraction, no Hilbert–Schmidt loss).
* `tm_pow_mul_le` (AM–GM), `tm_moment` (integer moments from `L^m` bounds), and
  `tm_integral_interp`: `x_t = e^{-t}x + √(1-e^{-2t})x'` has law `μ` under `μ ⊗ μ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal Matrix.Norms.L2Operator

variable {W : ℕ}

theorem tm_sum_rot {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (u : Finset γ) (F : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, F a b c = ∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, F a b c := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]

/-- **Kernel algebra** (rectangular factors). -/
theorem tm_kernel_eq {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι] (s : ι → ℂ)
    (Λ : ι → Matrix n n ℂ) (w : ℂ) {ℓf ℓU : ℕ} (a : Fin ℓf → Matrix m n ℂ)
    (c : Fin ℓf → Matrix n m ℂ) (a' : Fin ℓU → Matrix m n ℂ) (c' : Fin ℓU → Matrix n m ℂ) :
    ∑ i, (s i * (w * (∑ j, a j * Λ i * c j).trace)) • (∑ k, a' k * Λ i * c' k) =
      w • ∑ j, ∑ k, a' k * (∑ i, (s i * (c j * a j * Λ i).trace) • Λ i) * c' k := by
  simp only [Finset.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum, smul_smul, trace_sum, Finset.sum_smul]
  rw [tm_sum_rot]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => ?_
  rw [trace_mul_cycle (a j)]
  congr 1
  ring

/-- **Pointwise kernel bound**: `‖W⁻¹ Σⱼ Σₖ a'ₖ 𝒱(cⱼaⱼ) c'ₖ‖ ≤ 3 ℓ_f ℓ_U B_f B_U / W²`. -/
theorem tm_kernel_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) {ℓf ℓU : ℕ}
    (a : Fin ℓf → Matrix (Fin W) (LS W) ℂ) (c : Fin ℓf → Matrix (LS W) (Fin W) ℂ)
    (a' : Fin ℓU → Matrix (Fin W) (LS W) ℂ) (c' : Fin ℓU → Matrix (LS W) (Fin W) ℂ)
    {Bf BU : ℝ} (hBf0 : 0 ≤ Bf)
    (hBf : ∀ j, ‖a j‖ * ‖c j‖ ≤ Bf) (hBU : ∀ k, ‖a' k‖ * ‖c' k‖ ≤ BU) :
    ‖((W : ℂ)⁻¹) • ∑ j, ∑ k, a' k * tmV b (c j * a j) * c' k‖ ≤
      3 * ℓf * ℓU * Bf * BU / (W : ℝ) ^ 2 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h3 : (0 : ℝ) ≤ 3 / W := by positivity
  have hterm : ∀ j k, ‖a' k * tmV b (c j * a j) * c' k‖ ≤ 3 / W * Bf * BU := by
    intro j k
    have h1 : ‖a' k * tmV b (c j * a j) * c' k‖ ≤
        ‖a' k‖ * ‖tmV b (c j * a j)‖ * ‖c' k‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    have h2 := tm_contract_le hb0 hb hW (c j * a j)
    have hca : ‖c j * a j‖ ≤ ‖c j‖ * ‖a j‖ := Matrix.l2_opNorm_mul _ _
    have ha := norm_nonneg (a j)
    have hc := norm_nonneg (c j)
    have ha' := norm_nonneg (a' k)
    have hc' := norm_nonneg (c' k)
    have h4 : ‖tmV b (c j * a j)‖ ≤ 3 / W * (‖a j‖ * ‖c j‖) := by
      refine h2.trans ?_
      rw [mul_comm (‖a j‖)]
      exact mul_le_mul_of_nonneg_left hca h3
    calc ‖a' k * tmV b (c j * a j) * c' k‖
        ≤ ‖a' k‖ * ‖tmV b (c j * a j)‖ * ‖c' k‖ := h1
      _ ≤ ‖a' k‖ * (3 / W * (‖a j‖ * ‖c j‖)) * ‖c' k‖ := by gcongr
      _ = 3 / W * ((‖a j‖ * ‖c j‖) * (‖a' k‖ * ‖c' k‖)) := by ring
      _ ≤ 3 / W * (Bf * BU) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hBf j) (hBU k) (by positivity) hBf0) h3
      _ = 3 / W * Bf * BU := by ring
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ j, ∑ k, a' k * tmV b (c j * a j) * c' k‖ ≤ ℓf * (ℓU * (3 / W * Bf * BU)) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _j : Fin ℓf, ℓU * (3 / W * Bf * BU) := by
          refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans ?_
          calc _ ≤ ∑ _k : Fin ℓU, 3 / W * Bf * BU := Finset.sum_le_sum fun k _ => hterm j k
            _ = _ := by simp
      _ = _ := by simp
  calc (W : ℝ)⁻¹ * ‖∑ j, ∑ k, a' k * tmV b (c j * a j) * c' k‖
      ≤ (W : ℝ)⁻¹ * (ℓf * (ℓU * (3 / W * Bf * BU))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 3 * ℓf * ℓU * Bf * BU / (W : ℝ) ^ 2 := by field_simp

/-- `u^a w^b ≤ u^{a+b} + w^{a+b}` for `u, w ≥ 0`. -/
theorem tm_pow_mul_le {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) (a c : ℕ) :
    u ^ a * w ^ c ≤ u ^ (a + c) + w ^ (a + c) := by
  rcases le_total u w with h | h
  · have h1 : u ^ a ≤ w ^ a := pow_le_pow_left₀ hu h a
    have h2 : u ^ a * w ^ c ≤ w ^ a * w ^ c := mul_le_mul_of_nonneg_right h1 (by positivity)
    rw [← pow_add] at h2
    have : 0 ≤ u ^ (a + c) := by positivity
    linarith
  · have h1 : w ^ c ≤ u ^ c := pow_le_pow_left₀ hw h c
    have h2 : u ^ a * w ^ c ≤ u ^ a * u ^ c := mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [← pow_add] at h2
    have : 0 ≤ w ^ (a + c) := by positivity
    linarith

/-- Integer moments from an `L^m` bound: `E g^m ≤ C^m` (`g ≥ 0`). -/
theorem tm_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → ℝ}
    (hg0 : ∀ ω, 0 ≤ g ω) {m : ℕ} (hm : 1 ≤ m) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm g (ENNReal.ofReal m) μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => g ω ^ m) μ ∧ ∫ ω, g ω ^ m ∂μ ≤ C ^ m := by
  have hm0 : m ≠ 0 := by omega
  rw [ENNReal.ofReal_natCast] at h
  have hmem : MemLp g (m : ℝ≥0∞) μ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have he : (fun ω => g ω ^ m) = fun ω => ‖g ω‖ ^ m := by
    funext ω; rw [Real.norm_of_nonneg (hg0 ω)]
  have hint : Integrable (fun ω => g ω ^ m) μ := by
    rw [he]; exact hmem.integrable_norm_pow hm0
  refine ⟨hint, ?_⟩
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hm0) (ENNReal.natCast_ne_top m)] at h
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast] at h
  rw [← he] at h
  have hI0 : 0 ≤ ∫ ω, g ω ^ m ∂μ := integral_nonneg fun ω => by have := hg0 ω; positivity
  have h1 := (ENNReal.ofReal_le_ofReal_iff hC).mp h
  have h2 : ((∫ ω, g ω ^ m ∂μ) ^ (m : ℝ)⁻¹) ^ m ≤ C ^ m :=
    pow_le_pow_left₀ (by positivity) h1 m
  rwa [Real.rpow_inv_natCast_pow hI0 hm0] at h2

/-- **The law of `x_t`.** Under `μ ⊗ μ`, `e^{-t} x + √(1-e^{-2t}) x'` has law `μ` (`t ≥ 0`). -/
theorem tm_integral_interp {ι : Type} [Fintype ι] (v : ι → ℝ≥0) {h : (ι → ℝ) → ℝ}
    (hh : Continuous h) {t : ℝ} (ht : 0 ≤ t) :
    ∫ p, h (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
        ∂(gaussianProduct v).prod (gaussianProduct v) = ∫ x, h x ∂gaussianProduct v := by
  have hc01 : Real.exp (-t) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hθc : Real.cos (Real.arccos (Real.exp (-t))) = Real.exp (-t) :=
    Real.cos_arccos (by linarith [(Real.exp_pos (-t)).le]) hc01
  have hθs : Real.sin (Real.arccos (Real.exp (-t))) = Real.sqrt (1 - Real.exp (-2 * t)) := by
    rw [Real.sin_arccos, ou_exp_sq]
  have hG : AEStronglyMeasurable (fun p : (ι → ℝ) × (ι → ℝ) => h p.1)
      ((gaussianProduct v).prod (gaussianProduct v)) :=
    (hh.comp continuous_fst).aestronglyMeasurable
  have h1 := ou_integral_rotation v (Real.arccos (Real.exp (-t))) hG
  simp only [ContinuousLinearMap.rotation_apply, hθc, hθs] at h1
  rw [h1, integral_fun_fst, probReal_univ, one_smul]

end BlockBand.Transmission.PassiveLayer
