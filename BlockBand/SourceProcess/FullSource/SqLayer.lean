module

public import BlockBand.SourceProcess.FullSource.SqAlgebra
public import BlockBand.SourceProcess.FullSource.MomentStep

/-!
# The one-layer step of the tag square

Fresh law `freshLaw W b`, deterministic Hermitian `𝕏`, `N = freshTransport b E 𝕏`,
`𝓔 = NN* - I`, a deterministic factor `S` of the old tag `Y = S*S`; `h = W⁻¹Re Tr Y²` (`sqOf`),
`h₊ = W⁻¹Re Tr((SN)*(SN))²` (`sqPlus`).
* `sqStep_moment`: `E h₊ ≤ (1 + 2c + 2c²)h + 2σ²W⁻¹(Re Tr Y)²` when `‖E𝓔‖ ≤ c` and the centered
  bilinear entries of `𝓔` have `L²` norm `≤ σ‖u‖‖v‖`;
* `sqStep_crude`, `sqStep_crude_moment`: `h₊ ≤ ‖N‖⁴h`, `E h₊² ≤ C_N⁸h²` (`‖‖N‖‖₈ ≤ C_N`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ} {m : Type*} [Fintype m]

/-- The tag square `h = W⁻¹ Re Tr Y²` of a factored source `Y = S*S`. -/
def sqOf (W : ℕ) {n : Type*} [Fintype n] (S : Matrix m n ℂ) : ℝ :=
  (W : ℝ)⁻¹ * (Sᴴ * S * (Sᴴ * S)).trace.re

theorem sqOf_nonneg (W : ℕ) {n : Type*} [Fintype n] (S : Matrix m n ℂ) : 0 ≤ sqOf W S := by
  have h := trace_factor_re_nonneg (Sᴴ * S)
  rw [(Matrix.isHermitian_conjTranspose_mul_self S).eq] at h
  exact mul_nonneg (by positivity) h

theorem measurable_sqOf_comp {α n : Type*} [Fintype n] [MeasurableSpace α]
    {S : α → Matrix m n ℂ} (hS : Measurable S) : Measurable fun a => sqOf W (S a) := by
  have hY := measurable_matrix_mul' (measurable_matrix_conjTranspose' hS) hS
  have hYY := measurable_matrix_mul' hY hY
  unfold sqOf
  simp only [Matrix.trace, Matrix.diag]
  exact measurable_const.mul (Complex.measurable_re.comp
    (Finset.measurable_sum _ fun i _ => hYY.eval_matrix))

/-- The transported tag square `h₊ = W⁻¹ Re Tr((SN)*(SN))²`. -/
def sqPlus (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℝ :=
  sqOf W (S * freshTransport b E XX ω)

theorem measurable_sqPlus (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) : Measurable (sqPlus b E XX S) :=
  measurable_sqOf_comp (measurable_matrix_mul' measurable_const
    (measurable_freshTransport_comp b E measurable_const measurable_id))

/-- **Crude square transport**: `h₊ ≤ ‖N‖⁴ h`. -/
theorem sqStep_crude (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    sqPlus b E XX S ω ≤ ‖freshTransport b E XX ω‖ ^ 4 * sqOf W S := by
  have h := re_trace_sq_transport_le S (freshTransport b E XX ω)
  have hw : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  simp only [sqPlus, sqOf]
  nlinarith [mul_le_mul_of_nonneg_left h hw]

/-- **Crude moments of the transported square**: `E h₊² ≤ C_N⁸ h²` from `‖‖N‖‖₈ ≤ C_N`. -/
theorem sqStep_crude_moment {b E : ℝ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) {CN : ℝ} (hCN : 0 ≤ CN)
    (hN : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * (2 * 2) : ℕ) : ℝ))
      (freshLaw W b) ≤ ENNReal.ofReal CN) :
    Integrable (fun ω => sqPlus b E XX S ω ^ 2) (freshLaw W b) ∧
      ∫ ω, sqPlus b E XX S ω ^ 2 ∂freshLaw W b ≤ CN ^ (2 * (2 * 2)) * sqOf W S ^ 2 := by
  have hmN : Measurable fun ω => freshTransport b E XX ω :=
    measurable_freshTransport_comp b E measurable_const measurable_id
  obtain ⟨hi, hb⟩ := integral_abs_pow_le (ν := freshLaw W b)
    (f := fun ω => ‖freshTransport b E XX ω‖) (n := 2 * (2 * 2)) (by omega) hCN
    ⟨hmN.norm.aestronglyMeasurable, hN⟩
  have h0 := sqOf_nonneg W S
  have hle : ∀ ω, sqPlus b E XX S ω ^ 2 ≤
      |‖freshTransport b E XX ω‖| ^ (2 * (2 * 2)) * sqOf W S ^ 2 := by
    intro ω
    rw [abs_of_nonneg (norm_nonneg _), show 2 * (2 * 2) = 4 * 2 by rfl, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (sqOf_nonneg _ _) (sqStep_crude b E XX S ω) 2
  have hint : Integrable (fun ω => sqPlus b E XX S ω ^ 2) (freshLaw W b) :=
    (hi.mul_const _).mono' ((measurable_sqPlus b E XX S).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle ω)
  refine ⟨hint, (integral_mono hint (hi.mul_const _) hle).trans ?_⟩
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

theorem sum_sum_vecNorm_mul {n : Type*} [Fintype n] (S : Matrix m n ℂ) (σ : ℝ) :
    ∑ x, ∑ y, σ ^ 2 * vecNorm (rowv S x) ^ 2 * vecNorm (rowv S y) ^ 2 =
      σ ^ 2 * (Sᴴ * S).trace.re ^ 2 := by
  rw [← sum_vecNorm_rowv]
  have : (∑ x, vecNorm (rowv S x) ^ 2) ^ 2 =
      ∑ x, ∑ y, vecNorm (rowv S x) ^ 2 * vecNorm (rowv S y) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **The one-layer step of the tag square**:
`E h₊ ≤ (1 + 2c + 2c²) h + 2σ²W⁻¹(Tr Y)²`, when `‖E𝓔‖ ≤ c` and the centered bilinear entries
of `𝓔` have `L²` norm `≤ σ‖u‖‖v‖`. -/
theorem sqStep_moment {b E : ℝ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) {c σ CN₂ : ℝ} (hσ : 0 ≤ σ)
    (hc : ‖matrixExpect (freshLaw W b) (wardNoise b E XX)‖ ≤ c)
    (hfl₂ : ∀ u v : Fin 2 × Fin W → ℂ, eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
      matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
        ENNReal.ofReal (σ * vecNorm u * vecNorm v))
    (hN : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) 2 (freshLaw W b) ≤ ENNReal.ofReal CN₂) :
    Integrable (sqPlus b E XX S) (freshLaw W b) ∧
      ∫ ω, sqPlus b E XX S ω ∂freshLaw W b ≤
        (1 + 2 * c + 2 * c ^ 2) * sqOf W S + 2 * σ ^ 2 * (W : ℝ)⁻¹ * (Sᴴ * S).trace.re ^ 2 := by
  set μ := freshLaw W b
  set 𝓔 := wardNoise b E XX
  set A := matrixExpect μ 𝓔
  set Y := Sᴴ * S
  have hYh : Y.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self S
  set TY := (Y * Y).trace.re
  have hTY : 0 ≤ TY := by
    have := trace_factor_re_nonneg Y; rwa [hYh.eq] at this
  have hw : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hmw : Measurable 𝓔 := measurable_wardNoise_comp b E measurable_const measurable_id
  have hint := integrable_wardNoise_entry (b := b) (E := E) XX hN
  -- the linear term
  obtain ⟨hym, -, hyabs, hycen⟩ := trace_noise (ν := μ) 𝓔 hmw hint Y hc (by norm_num) hσ hfl₂
  rw [hYh.eq] at hym hyabs hycen
  set yf : LayerSample W .oneBlockOnePort → ℝ := fun ω => (Y * Y * 𝓔 ω).trace.re
  have hyB := momBd_of_centered hym (by norm_num) (by positivity) hyabs hycen
  have hyi : Integrable yf μ := by
    have hmem : MemLp yf (ENNReal.ofReal 2) μ := lt_of_le_of_lt hyB.2 ENNReal.ofReal_lt_top
    exact hmem.integrable (by simp)
  -- the quadratic terms
  set g : m → m → LayerSample W .oneBlockOnePort → ℝ :=
    fun x y ω => ‖bilinear (rowv S x) (𝓔 ω - A) (rowv S y)‖
  have hg : ∀ x y, Integrable (fun ω => g x y ω ^ 2) μ ∧
      ∫ ω, g x y ω ^ 2 ∂μ ≤ σ ^ 2 * vecNorm (rowv S x) ^ 2 * vecNorm (rowv S y) ^ 2 := by
    intro x y
    have hm : Measurable (g x y) :=
      (measurable_bilinear_comp (hmw.sub measurable_const) _ _).norm
    have hC : 0 ≤ σ * vecNorm (rowv S x) * vecNorm (rowv S y) := by
      have := vecNorm_nonneg (rowv S x); have := vecNorm_nonneg (rowv S y); positivity
    obtain ⟨hi, hb⟩ := integral_abs_pow_le (ν := μ) (f := g x y) (n := 2) (by norm_num) hC
      ⟨hm.aestronglyMeasurable, by
        simp only [g]
        have hmeas : AEStronglyMeasurable (fun ω => bilinear (rowv S x) (𝓔 ω - A) (rowv S y)) μ :=
          (measurable_bilinear_comp (hmw.sub measurable_const) _ _).aestronglyMeasurable
        rw [eLpNorm_norm (fun ω => bilinear (rowv S x) (𝓔 ω - A) (rowv S y)) hmeas]
        exact_mod_cast hfl₂ (rowv S x) (rowv S y)⟩
    have e : (fun ω => |g x y ω| ^ 2) = fun ω => g x y ω ^ 2 := by
      funext ω; rw [abs_of_nonneg (norm_nonneg _)]
    rw [e] at hi hb
    exact ⟨hi, hb.trans (le_of_eq (by ring))⟩
  -- the pointwise bound
  set β : ℝ := 2 * (W : ℝ)⁻¹
  set a : ℝ := (W : ℝ)⁻¹ * (1 + 2 * c ^ 2) * TY
  set G : LayerSample W .oneBlockOnePort → ℝ := fun ω =>
    a + β * yf ω + β * ∑ x, ∑ y, g x y ω ^ 2
  have hpt : ∀ ω, sqPlus b E XX S ω ≤ G ω := by
    intro ω
    have e1 := trace_sq_transport S (freshTransport b E XX ω)
    have h𝓔 : freshTransport b E XX ω * (freshTransport b E XX ω)ᴴ - 1 = A + (𝓔 ω - A) := by
      simp only [𝓔, wardNoise]; abel
    rw [h𝓔] at e1
    have h2 := re_trace_noise_sq_le S A (𝓔 ω - A)
    have hA2 : ‖A‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
    have hyω : (Y * Y * (A + (𝓔 ω - A))).trace.re = yf ω := by
      simp only [yf, add_sub_cancel]
    have e2 := congrArg Complex.re e1
    simp only [Complex.add_re, Complex.mul_re, show (2 : ℂ).re = 2 from rfl,
      show (2 : ℂ).im = 0 from rfl, zero_mul, sub_zero] at e2
    simp only [sqPlus, sqOf, G, a, β]
    rw [e2]
    change (W : ℝ)⁻¹ * (TY + 2 * (Y * Y * (A + (𝓔 ω - A))).trace.re +
      (Y * (A + (𝓔 ω - A)) * Y * (A + (𝓔 ω - A))).trace.re) ≤ _
    rw [hyω]
    have h3 : 2 * ‖A‖ ^ 2 * TY ≤ 2 * c ^ 2 * TY := by nlinarith
    have h4 : (Y * (A + (𝓔 ω - A)) * Y * (A + (𝓔 ω - A))).trace.re ≤
        2 * c ^ 2 * TY + 2 * ∑ x, ∑ y, g x y ω ^ 2 := h2.trans (by simp only [g]; linarith)
    nlinarith [mul_le_mul_of_nonneg_left h4 hw]
  have hGi : Integrable G μ :=
    ((integrable_const a).add (hyi.const_mul β)).add ((integrable_finsetSum _ fun x _ =>
      integrable_finsetSum _ fun y _ => (hg x y).1).const_mul β)
  have hint' : Integrable (sqPlus b E XX S) μ :=
    hGi.mono' (measurable_sqPlus b E XX S).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ sqPlus b E XX S ω from sqOf_nonneg _ _)]
        exact hpt ω)
  refine ⟨hint', (integral_mono hint' hGi hpt).trans ?_⟩
  have hGint : ∫ ω, G ω ∂μ = a + β * ∫ ω, yf ω ∂μ + β * ∑ x, ∑ y, ∫ ω, g x y ω ^ 2 ∂μ := by
    simp only [G]
    rw [integral_add (f := fun ω => a + β * yf ω) (g := fun ω => β * ∑ x, ∑ y, g x y ω ^ 2)
      ((integrable_const a).add (hyi.const_mul β)) ((integrable_finsetSum _
      fun x _ => integrable_finsetSum _ fun y _ => (hg x y).1).const_mul β),
      integral_add (f := fun _ => a) (g := fun ω => β * yf ω) (integrable_const a)
        (hyi.const_mul β), integral_const, integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
        (hg x y).1]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    congr 2
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_finsetSum _ fun y _ => (hg x y).1]
  rw [hGint]
  have hβ : 0 ≤ β := by positivity
  have hy1 : ∫ ω, yf ω ∂μ ≤ c * TY := (le_abs_self _).trans hyabs
  have hg1 : ∑ x, ∑ y, ∫ ω, g x y ω ^ 2 ∂μ ≤ σ ^ 2 * Y.trace.re ^ 2 := by
    rw [← sum_sum_vecNorm_mul]
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => (hg x y).2
  have e : (1 + 2 * c + 2 * c ^ 2) * sqOf W S + 2 * σ ^ 2 * (W : ℝ)⁻¹ * Y.trace.re ^ 2 =
      a + β * (c * TY) + β * (σ ^ 2 * Y.trace.re ^ 2) := by
    simp only [sqOf, a, β, TY, Y]; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hy1 hβ, mul_le_mul_of_nonneg_left hg1 hβ]

end BlockBand.SourceProcess.FullSource
