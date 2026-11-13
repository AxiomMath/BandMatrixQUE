module

public import BlockBand.Transmission.Generator.BrAlg

/-!
# The one-layer bracket: the covariance contraction

For a random Hermitian `U` with mean `Ū`, `Z = U - Ū`, `λ_k = brLin hT k Z`:
* `matrixExpect_isHermitian`, `im_ts_ent_herm`, **`im_brLin_centered`** (`λ_k` is real);
* `integrable_brLin_mul`, **`integral_brLin_mul`**
  (`E[λ_kλ_l] = Σ_{im} t_i^k t_m^l Cov(v_i, v_i, v_m, v_m)`);
* **`br_cov_main`**: a covariance bound of the passive-covariance shape (`a = r` real) gives
  `‖Σ_{im} t_i^k t_m^l Cov(v_i,v_i,v_m,v_m) - 2rΣ_i t_i^{k+l}(1-t_i)‖ ≤
  (‖σ‖ + ‖σ'‖)hs(T,f)² + ε(Tr T)²`.
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

theorem matrixExpect_isHermitian (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hUH : ∀ ω, (U ω).IsHermitian) : (matrixExpect μ U).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, matrixExpect, Matrix.of_apply]
  rw [show star (∫ ω, U ω j i ∂μ) = conj (∫ ω, U ω j i ∂μ) from rfl, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have := congrFun (congrFun (hUH ω) i) j
  simpa [conjTranspose_apply] using this

theorem im_ts_ent_herm (hT : T.PosSemidef) {H : Matrix (Fin W) (Fin W) ℂ} (hH : H.IsHermitian)
    (i : Fin W) : (ts_ent hT H i i).im = 0 := by
  have h := br_bilinear_conjTranspose (ts_vec hT i) (ts_vec hT i) H
  rw [hH.eq] at h
  exact Complex.conj_eq_iff_im.mp h.symm

theorem im_brLin_herm (hT : T.PosSemidef) {H : Matrix (Fin W) (Fin W) ℂ} (hH : H.IsHermitian)
    (k : ℕ) : (brLin hT k H).im = 0 := by
  rw [brLin, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, im_ts_ent_herm hT hH i, zero_mul,
    mul_zero, add_zero]

theorem im_brLin_centered (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hUH : ∀ ω, (U ω).IsHermitian) (k : ℕ) (ω : Ω) :
    (brLin hT k (U ω - matrixExpect μ U)).im = 0 :=
  im_brLin_herm hT ((hUH ω).sub (matrixExpect_isHermitian U hUH)) k

theorem integrable_brLin_mul (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i i *
      ts_ent hT (U ω - matrixExpect μ U) m m) μ) (k l : ℕ) :
    Integrable (fun ω => brLin hT k (U ω - matrixExpect μ U) *
      brLin hT l (U ω - matrixExpect μ U)) μ := by
  simp only [brLin, Finset.sum_mul_sum]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ => ?_
  have := ((hp i m).const_mul (((ts_lam hT i ^ k : ℝ) : ℂ) * ((ts_lam hT m ^ l : ℝ) : ℂ)))
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only; ring

/-- **`E[λ_kλ_l]` as a contraction of the bilinear covariance.** -/
theorem integral_brLin_mul (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i i *
      ts_ent hT (U ω - matrixExpect μ U) m m) μ) (k l : ℕ) :
    ∫ ω, brLin hT k (U ω - matrixExpect μ U) * brLin hT l (U ω - matrixExpect μ U) ∂μ =
      ∑ i, ∑ m, ((ts_lam hT i ^ k * ts_lam hT m ^ l : ℝ) : ℂ) *
        bilinearCovariance μ U (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) := by
  simp only [brLin, Finset.sum_mul_sum]
  have hI : ∀ i m, Integrable (fun ω => ((ts_lam hT i ^ k : ℝ) : ℂ) *
      ts_ent hT (U ω - matrixExpect μ U) i i * (((ts_lam hT m ^ l : ℝ) : ℂ) *
      ts_ent hT (U ω - matrixExpect μ U) m m)) μ := fun i m => by
    have := ((hp i m).const_mul (((ts_lam hT i ^ k : ℝ) : ℂ) * ((ts_lam hT m ^ l : ℝ) : ℂ)))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only; ring
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ => hI i m]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun m _ => hI i m]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [bilinearCovariance, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [ts_ent]; push_cast; ring

theorem fourNorm_eigen_diag (hT : T.PosSemidef) (i m : Fin W) :
    fourNorm (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) = 1 := by
  simp [fourNorm, ts_vecNorm]

/-- **The covariance contracted with the bracket weights.** -/
theorem br_cov_main (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (f : Matrix (Fin W) (Fin W) ℂ) (r : ℝ) (σ σ' : ℂ)
    {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      ((r : ℂ) * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ‖∑ i, ∑ m, ((ts_lam hT i ^ k * ts_lam hT m ^ l : ℝ) : ℂ) *
        bilinearCovariance μ U (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) -
      ((2 * r * ∑ i, ts_lam hT i ^ (k + l) * (1 - ts_lam hT i) : ℝ) : ℂ)‖ ≤
      (‖σ‖ + ‖σ'‖) * hsSandwich T f ^ 2 + ε * T.trace.re ^ 2 := by
  set t := ts_lam hT
  set fe := ts_ent hT f
  set w : Fin W → Fin W → ℝ := fun i m => t i ^ k * t m ^ l
  have hw0 : ∀ i m, 0 ≤ w i m := fun i m =>
    mul_nonneg (pow_nonneg (ts_lam_nonneg hT i) k) (pow_nonneg (ts_lam_nonneg hT m) l)
  set M : Fin W → Fin W → ℂ := fun i m => (if i = m then (r : ℂ) * (2 * (1 - (t i : ℂ))) else 0) +
      σ * (fe i m * fe m i) + σ' * (conj (fe m i) * conj (fe i m))
  -- covariance error
  have h1 : ‖∑ i, ∑ m, ((w i m : ℝ) : ℂ) *
      bilinearCovariance μ U (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) -
      ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * M i m‖ ≤ ε * T.trace.re ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hsq : T.trace.re ^ 2 = ∑ i, ∑ m, t i * t m := by
      rw [← ts_sum_lam hT, sq, Finset.sum_mul_sum]
    rw [hsq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 i m)]
    have hc := hcov (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m)
    rw [fourNorm_eigen_diag, mul_one, br_crossed hT f (r : ℂ) σ σ' i m] at hc
    have hwt : w i m ≤ t i * t m :=
      mul_le_mul (pow_le_of_le_one (ts_lam_nonneg hT i) (ht1 i) (by omega))
        (pow_le_of_le_one (ts_lam_nonneg hT m) (ht1 m) (by omega))
        (pow_nonneg (ts_lam_nonneg hT m) l) (ts_lam_nonneg hT i)
    calc w i m * ‖_‖ ≤ (t i * t m) * ε :=
          mul_le_mul hwt hc (norm_nonneg _) (mul_nonneg (ts_lam_nonneg hT i) (ts_lam_nonneg hT m))
      _ = _ := by ring
  -- the main term
  have hdiag : ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * (if i = m then (r : ℂ) * (2 * (1 - (t i : ℂ))) else 0)
      = ((2 * r * ∑ i, t i ^ (k + l) * (1 - t i) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun m _ hm => by simp [Ne.symm hm]) (by simp)]
    simp only [w]; push_cast; ring
  -- the `f`-terms
  have hF : ‖∑ i, ∑ m, ((w i m : ℝ) : ℂ) * (σ * (fe i m * fe m i) +
      σ' * (conj (fe m i) * conj (fe i m)))‖ ≤ (‖σ‖ + ‖σ'‖) * hsSandwich T f ^ 2 := by
    have hb := br_fterm_le hT ht1 hk hl f
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _) ?_
    have hpt : ∀ i m, ‖((w i m : ℝ) : ℂ) * (σ * (fe i m * fe m i) +
        σ' * (conj (fe m i) * conj (fe i m)))‖ ≤
        (‖σ‖ + ‖σ'‖) * (t i ^ k * t m ^ l * (‖fe i m‖ * ‖fe m i‖)) := by
      intro i m
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 i m)]
      have := norm_add_le (σ * (fe i m * fe m i)) (σ' * (conj (fe m i) * conj (fe i m)))
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj] at this
      calc w i m * ‖_‖ ≤ w i m * (‖σ‖ * (‖fe i m‖ * ‖fe m i‖) +
          ‖σ'‖ * (‖fe m i‖ * ‖fe i m‖)) := mul_le_mul_of_nonneg_left this (hw0 i m)
        _ = _ := by simp only [w]; ring
    refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => hpt i m) ?_
    simp only [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hsplit : ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * M i m =
      ((2 * r * ∑ i, t i ^ (k + l) * (1 - t i) : ℝ) : ℂ) +
      ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * (σ * (fe i m * fe m i) +
        σ' * (conj (fe m i) * conj (fe i m))) := by
    rw [← hdiag, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [M]; ring
  have e : ∑ i, ∑ m, ((t i ^ k * t m ^ l : ℝ) : ℂ) *
      bilinearCovariance μ U (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) -
      ((2 * r * ∑ i, t i ^ (k + l) * (1 - t i) : ℝ) : ℂ) =
      (∑ i, ∑ m, ((w i m : ℝ) : ℂ) *
        bilinearCovariance μ U (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) -
      ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * M i m) +
      ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * (σ * (fe i m * fe m i) +
        σ' * (conj (fe m i) * conj (fe i m))) := by
    rw [hsplit]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

end BlockBand.Transmission.Generator
