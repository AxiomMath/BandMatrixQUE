module

public import BlockBand.Transmission.Generator.BrCov

/-!
# The one-layer bracket for an abstract random layer

`T ⪰ 0`, `t_i ≤ 1`; `U` a random Hermitian matrix with mean `Ū`, `Z = U - Ū`, `S = sand T U`
with `‖S‖ ≤ 1` a.s.; `Δ_k = Re Tr S^k - Re Tr D^k` (`brInc`), `x_k = k Re λ_k(Z)`,
`b_k = k Re λ_k(Ū - 1)`, `h = ‖sand T Z‖²_HS`, `g = Tr T`, `‖Ū - 1‖ ≤ ν`, `n = ν²g`,
`c_k = k6^{2k}`, `Er = (‖σ‖+‖σ'‖)hs(T,f)² + εg²`, `M = 2|r|g + Er`.
* `br_point_ae`: a.s. `|Δ_kΔ_l - x_kx_l - x_kb_l - b_kx_l| ≤ A₁x_k² + A₂x_l² + A₃h² + A₄`;
* `br_xx`: `|E x_kx_l - kl·2rΣt^{k+l}(1-t)| ≤ kl·Er` (covariance contraction, `br_cov_main`).

These give, in the sibling module, **`br_law`**:
`|E Δ_kΔ_l - kl·2rΣ_i t_i^{k+l}(1-t_i)| ≤ kl·Er + A₁k²M + A₂l²M + A₃H₄ + A₄`, with
`A₁ = 2c_l/s`, `A₂ = 2c_k/s`, `A₃ = s(c_k+c_l) + 8(c_k²+c_l²)`,
`A₄ = A₃n² + (kνg)² + (lνg)²`, for any `s > 0` and `E h² ≤ H₄`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Internal.Contracts.Layers
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `Δ_k(U) = Re Tr (sand T U)^k - Re Tr (sand T 1)^k`. -/
def brInc (hT : T.PosSemidef) (k : ℕ) (U : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ((sand hT U) ^ k).trace.re - ((sand hT 1) ^ k).trace.re

theorem brLin_add (hT : T.PosSemidef) (k : ℕ) (A B : Matrix (Fin W) (Fin W) ℂ) :
    brLin hT k (A + B) = brLin hT k A + brLin hT k B := by
  simp only [brLin, ts_ent_add, mul_add, Finset.sum_add_distrib]

theorem continuous_brLin (hT : T.PosSemidef) (k : ℕ) :
    Continuous (brLin hT k : Matrix (Fin W) (Fin W) ℂ → ℂ) := by
  unfold brLin ts_ent bilinear; fun_prop

theorem continuous_brInc (hT : T.PosSemidef) (k : ℕ) :
    Continuous (brInc hT k : Matrix (Fin W) (Fin W) ℂ → ℝ) :=
  (Complex.continuous_re.comp (((continuous_sand hT).pow _).matrix_trace)).sub continuous_const

theorem abs_brInc_le (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) (k : ℕ)
    {U : Matrix (Fin W) (Fin W) ℂ} (hS : ‖sand hT U‖ ≤ 1) : |brInc hT k U| ≤ 2 * W := by
  have hD1 : ‖sand hT 1‖ ≤ 1 := by
    rw [sand_one]
    exact norm_diagonal_le (c := (1 : ℝ)) _ zero_le_one fun i => by
      rw [Complex.norm_real, Real.norm_of_nonneg (ts_lam_nonneg hT i)]; exact ht1 i
  have b : ∀ A : Matrix (Fin W) (Fin W) ℂ, ‖A‖ ≤ 1 → |(A ^ k).trace.re| ≤ W := fun A hA => by
    refine (Complex.abs_re_le_norm _).trans ((norm_trace_le_card _).trans ?_)
    have := pe_pow_le hA le_rfl k
    rw [one_pow] at this
    nlinarith [Nat.cast_nonneg (α := ℝ) W]
  have := abs_sub (((sand hT U) ^ k).trace.re) (((sand hT 1) ^ k).trace.re)
  unfold brInc; linarith [b _ hS, b _ hD1]

/-- **The pointwise remainder, a.s.** -/
theorem br_point_ae (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hS : ∀ᵐ ω ∂μ, ‖sand hT (U ω)‖ ≤ 1)
    {ν : ℝ} (hν : ‖matrixExpect μ U - 1‖ ≤ ν) {s : ℝ} (hs : 0 < s) (k l : ℕ) :
    let Ub := matrixExpect μ U
    let g := T.trace.re
    let ck := ((k + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (k + 1))
    let cl := ((l + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (l + 1))
    ∀ᵐ ω ∂μ, |brInc hT (k + 1) (U ω) * brInc hT (l + 1) (U ω) -
        ((k + 1 : ℕ) : ℝ) * (brLin hT (k + 1) (U ω - Ub)).re *
          (((l + 1 : ℕ) : ℝ) * (brLin hT (l + 1) (U ω - Ub)).re) -
        ((k + 1 : ℕ) : ℝ) * (brLin hT (k + 1) (U ω - Ub)).re *
          (((l + 1 : ℕ) : ℝ) * (brLin hT (l + 1) (Ub - 1)).re) -
        ((k + 1 : ℕ) : ℝ) * (brLin hT (k + 1) (Ub - 1)).re *
          (((l + 1 : ℕ) : ℝ) * (brLin hT (l + 1) (U ω - Ub)).re)| ≤
      2 * cl / s * (((k + 1 : ℕ) : ℝ) * (brLin hT (k + 1) (U ω - Ub)).re) ^ 2 +
      2 * ck / s * (((l + 1 : ℕ) : ℝ) * (brLin hT (l + 1) (U ω - Ub)).re) ^ 2 +
      (s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2)) * frobSq (sand hT (U ω - Ub)) ^ 2 +
      ((s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2)) * (ν ^ 2 * g) ^ 2 +
        ((((k + 1 : ℕ) : ℝ) * (ν * g)) ^ 2 + (((l + 1 : ℕ) : ℝ) * (ν * g)) ^ 2)) := by
  intro Ub g ck cl
  have hg : 0 ≤ g := by rw [show g = T.trace.re from rfl, ← ts_sum_lam hT]
                        exact Finset.sum_nonneg fun i _ => ts_lam_nonneg hT i
  have hν0 : 0 ≤ ν := (norm_nonneg _).trans hν
  have hfb : frobSq (sand hT (Ub - 1)) ≤ ν ^ 2 * g :=
    (frobSq_sand_le hT ht1 _).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hν 2) hg)
  have hb : ∀ m : ℕ, |((m + 1 : ℕ) : ℝ) * (brLin hT (m + 1) (Ub - 1)).re| ≤
      ((m + 1 : ℕ) : ℝ) * (ν * g) := fun m => by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (Nat.cast_nonneg _)
    exact (norm_brLin_le hT ht1 (by omega) _).trans (mul_le_mul_of_nonneg_right hν hg)
  filter_upwards [hS] with ω hω
  have hR : ∀ m : ℕ, |brInc hT (m + 1) (U ω) -
      ((m + 1 : ℕ) : ℝ) * (brLin hT (m + 1) (U ω - Ub)).re -
      ((m + 1 : ℕ) : ℝ) * (brLin hT (m + 1) (Ub - 1)).re| ≤
      ((m + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (m + 1)) *
        (2 * frobSq (sand hT (U ω - Ub)) + 2 * (ν ^ 2 * g)) := fun m => by
    have h := br_expand hT ht1 (U ω) hω m
    have e : U ω - 1 = (U ω - Ub) + (Ub - 1) := by abel
    rw [e, brLin_add, Complex.add_re, sand_add] at h
    have hf := frobSq_add_le (sand hT (U ω - Ub)) (sand hT (Ub - 1))
    have hc : 0 ≤ ((m + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (m + 1)) := by positivity
    refine le_trans (le_of_eq ?_) (h.trans (mul_le_mul_of_nonneg_left (hf.trans (by linarith)) hc))
    congr 1; unfold brInc; ring
  have hsc := br_scalar (Δk := brInc hT (k + 1) (U ω)) (Δl := brInc hT (l + 1) (U ω))
    (xk := ((k + 1 : ℕ) : ℝ) * (brLin hT (k + 1) (U ω - Ub)).re)
    (xl := ((l + 1 : ℕ) : ℝ) * (brLin hT (l + 1) (U ω - Ub)).re)
    (bk := ((k + 1 : ℕ) : ℝ) * (brLin hT (k + 1) (Ub - 1)).re)
    (bl := ((l + 1 : ℕ) : ℝ) * (brLin hT (l + 1) (Ub - 1)).re)
    (Rk := brInc hT (k + 1) (U ω) - ((k + 1 : ℕ) : ℝ) * (brLin hT (k + 1) (U ω - Ub)).re -
      ((k + 1 : ℕ) : ℝ) * (brLin hT (k + 1) (Ub - 1)).re)
    (Rl := brInc hT (l + 1) (U ω) - ((l + 1 : ℕ) : ℝ) * (brLin hT (l + 1) (U ω - Ub)).re -
      ((l + 1 : ℕ) : ℝ) * (brLin hT (l + 1) (Ub - 1)).re)
    (h := frobSq (sand hT (U ω - Ub))) (n := ν ^ 2 * g) (s := s) (ck := ck) (cl := cl)
    (Bk := ((k + 1 : ℕ) : ℝ) * (ν * g)) (Bl := ((l + 1 : ℕ) : ℝ) * (ν * g))
    (by ring) (by ring) (hb k) (hb l) (hR k) (hR l) hs (by positivity) (by positivity)
  refine hsc.trans (le_of_eq ?_)
  ring

/-- **The covariance part**: `E x_kx_l` against `kl·2rΣt^{k+l}(1-t)`. -/
theorem br_xx [IsProbabilityMeasure μ] (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUH : ∀ ω, (U ω).IsHermitian)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i i *
      ts_ent hT (U ω - matrixExpect μ U) m m) μ)
    (f : Matrix (Fin W) (Fin W) ℂ) (r : ℝ) (σ σ' : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      ((r : ℂ) * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    Integrable (fun ω => (k : ℝ) * (brLin hT k (U ω - matrixExpect μ U)).re *
      ((l : ℝ) * (brLin hT l (U ω - matrixExpect μ U)).re)) μ ∧
    |∫ ω, (k : ℝ) * (brLin hT k (U ω - matrixExpect μ U)).re *
        ((l : ℝ) * (brLin hT l (U ω - matrixExpect μ U)).re) ∂μ -
      (k : ℝ) * l * (2 * r * ∑ i, ts_lam hT i ^ (k + l) * (1 - ts_lam hT i))| ≤
      (k : ℝ) * l * ((‖σ‖ + ‖σ'‖) * hsSandwich T f ^ 2 + ε * T.trace.re ^ 2) := by
  set Z := fun ω => U ω - matrixExpect μ U
  have hpt : ∀ ω, (k : ℝ) * (brLin hT k (Z ω)).re * ((l : ℝ) * (brLin hT l (Z ω)).re) =
      (k : ℝ) * l * (brLin hT k (Z ω) * brLin hT l (Z ω)).re := fun ω => by
    rw [Complex.mul_re, im_brLin_centered hT U hUH k ω, zero_mul, sub_zero]; ring
  have hI := integrable_brLin_mul hT U hp k l
  have hI' : Integrable (fun ω => (k : ℝ) * (brLin hT k (Z ω)).re *
      ((l : ℝ) * (brLin hT l (Z ω)).re)) μ :=
    ((integrable_cre hI).const_mul ((k : ℝ) * l)).congr
      (Filter.Eventually.of_forall fun ω => (hpt ω).symm)
  refine ⟨hI', ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, integral_cre hI,
    integral_brLin_mul hT U hp k l, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * l)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hm := br_cov_main hT ht1 U f r σ σ' hcov hk hl
  refine le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans hm)
  rw [Complex.sub_re, Complex.ofReal_re]

/-- `0 ≤ Σ t^m(1-t) ≤ Tr T` (`m ≥ 1`). -/
theorem br_weight_le (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ ∑ i, ts_lam hT i ^ m * (1 - ts_lam hT i) ∧
      ∑ i, ts_lam hT i ^ m * (1 - ts_lam hT i) ≤ T.trace.re := by
  rw [← ts_sum_lam hT]
  have h0 : ∀ i, 0 ≤ ts_lam hT i ^ m * (1 - ts_lam hT i) := fun i =>
    mul_nonneg (pow_nonneg (ts_lam_nonneg hT i) m) (by linarith [ht1 i])
  refine ⟨Finset.sum_nonneg fun i _ => h0 i, Finset.sum_le_sum fun i _ => ?_⟩
  have := pow_le_of_le_one (ts_lam_nonneg hT i) (ht1 i) (by omega : m ≠ 0)
  have := ts_lam_nonneg hT i
  nlinarith [ht1 i, pow_nonneg (ts_lam_nonneg hT i) m]

end BlockBand.Transmission.Generator
