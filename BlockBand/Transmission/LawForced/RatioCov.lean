module

public import BlockBand.Transmission.Generator.BrCov
public import BlockBand.Transmission.Generator.PowerCov

/-!
# Covariance contractions with general eigenvalue weights

The `F_z` one-layer expansion contracts the PCB covariance with the weights `t_k φ_k` of
`Λ_z` or of `r_w = (1 + wt)⁻¹`, instead of the powers `t^k`. Here `t = ts_lam hT`,
`v_k = ts_vec hT k` and `f'_{km} = ts_ent hT f k m`. Every statement is deterministic in the
covariance: the hypothesis `hcov` is exactly the shape of
`CovarianceBulk.PassiveCovarianceBulk` (`a = D₀/(2W)`, `σ = σ₋/W`, `σ' = conj σ₋/W`).
* `gW hT φ = V diag(tφ) V*`: `gW_posSemidef` (`φ ≥ 0`), `trace_gW_mul`
  (`Tr(gW·Z) = Σ t_k φ_k Z'_{kk}`), `trace_gW`;
* **`cov_diag_contract`** (`br_cov_main` with weights `t_k φ_k t_m φ_m`, `|φ| ≤ Φ`):
  `‖Σ_{km} t_k φ_k t_m φ_m Cov(v_k,v_k,v_m,v_m) − 2aΣ_k t_k²φ_k²(1−t_k)‖ ≤
  (‖σ‖+‖σ'‖)Φ²hs(T,f)² + εΦ²(Tr T)²`;
* **`cov_cross_contract`** (`quad_contract` with weights `t_k φ_k t_m φ_m`):
  `‖Σ_{km} t_k φ_k t_m φ_m (Cov(v_k,v_m,v_m,v_k) − a(2−t_k−t_m) − σf'_{kk}f'_{mm}
  − σ' conj f'_{kk} conj f'_{mm})‖ ≤ εΦ²(Tr T)²`;
* `norm_sum_weight_fd_le`: if `|φ_k − φ₀| ≤ Lt_k` then
  `‖Σ_k t_k φ_k f'_{kk}‖ ≤ |φ₀|‖Tr(Tf)‖ + L√(Tr T)·hs(T,f)` (as in `norm_sum_pow_fd_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.Generator
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `gW hT φ = V diag(t_k φ_k) V*`. -/
def gW (hT : T.PosSemidef) (φ : Fin W → ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  ts_U hT * diagonal (fun i => ((ts_lam hT i * φ i : ℝ) : ℂ)) * star (ts_U hT)

theorem gW_posSemidef (hT : T.PosSemidef) {φ : Fin W → ℝ} (hφ : ∀ i, 0 ≤ φ i) :
    (gW hT φ).PosSemidef := by
  have hd : (diagonal (fun i => ((ts_lam hT i * φ i : ℝ) : ℂ))).PosSemidef := by
    refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
    exact_mod_cast mul_nonneg (ts_lam_nonneg hT i) (hφ i)
  have := hd.mul_mul_conjTranspose_same (ts_U hT)
  rwa [← Matrix.star_eq_conjTranspose] at this

theorem trace_gW_mul (hT : T.PosSemidef) (φ : Fin W → ℝ) (Z : Matrix (Fin W) (Fin W) ℂ) :
    (gW hT φ * Z).trace = ∑ i, ((ts_lam hT i * φ i : ℝ) : ℂ) * ts_ent hT Z i i := by
  rw [gW, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, ts_ent_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.mul_assoc, Matrix.mul_diagonal]
  ring

theorem trace_gW (hT : T.PosSemidef) (φ : Fin W → ℝ) :
    (gW hT φ).trace = ((∑ i, ts_lam hT i * φ i : ℝ) : ℂ) := by
  have h := trace_gW_mul hT φ 1
  rw [Matrix.mul_one] at h
  rw [h]; push_cast
  exact Finset.sum_congr rfl fun i _ => by rw [ts_ent_one, mul_one]

/-- The weighted `f`-terms are bounded by `Φ²hs(T,f)²`. -/
theorem fterm_weight_le (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) {φ : Fin W → ℝ}
    {Φ : ℝ} (hφ : ∀ i, |φ i| ≤ Φ) (f : Matrix (Fin W) (Fin W) ℂ) (σ σ' : ℂ) :
    ‖∑ i, ∑ m, ((ts_lam hT i * φ i * (ts_lam hT m * φ m) : ℝ) : ℂ) *
        (σ * (ts_ent hT f i m * ts_ent hT f m i) +
          σ' * (conj (ts_ent hT f m i) * conj (ts_ent hT f i m)))‖ ≤
      (‖σ‖ + ‖σ'‖) * Φ ^ 2 * hsSandwich T f ^ 2 := by
  set t := ts_lam hT
  set fe := ts_ent hT f
  have ht := ts_lam_nonneg hT
  have hb := br_fterm_le hT ht1 (k := 1) (l := 1) le_rfl le_rfl f
  simp only [pow_one] at hb
  have hpt : ∀ i m, ‖((t i * φ i * (t m * φ m) : ℝ) : ℂ) * (σ * (fe i m * fe m i) +
      σ' * (conj (fe m i) * conj (fe i m)))‖ ≤
      (‖σ‖ + ‖σ'‖) * Φ ^ 2 * (t i * t m * (‖fe i m‖ * ‖fe m i‖)) := by
    intro i m
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := norm_add_le (σ * (fe i m * fe m i)) (σ' * (conj (fe m i) * conj (fe i m)))
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj] at h1
    have hw : |t i * φ i * (t m * φ m)| ≤ Φ ^ 2 * (t i * t m) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (ht i), abs_of_nonneg (ht m)]
      have := mul_le_mul (hφ i) (hφ m) (abs_nonneg _) ((abs_nonneg _).trans (hφ i))
      nlinarith [mul_nonneg (ht i) (ht m), abs_nonneg (φ i), abs_nonneg (φ m)]
    calc |t i * φ i * (t m * φ m)| * ‖_‖ ≤ (Φ ^ 2 * (t i * t m)) * (‖σ‖ * (‖fe i m‖ * ‖fe m i‖) +
        ‖σ'‖ * (‖fe m i‖ * ‖fe i m‖)) := mul_le_mul hw h1 (norm_nonneg _) (by
          have := (abs_nonneg _).trans hw; exact this)
      _ = _ := by ring
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => hpt i m) ?_
  simp only [← Finset.mul_sum]
  have hc : 0 ≤ (‖σ‖ + ‖σ'‖) * Φ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hb hc

/-- **The covariance contracted with the variance weights `t_k φ_k t_m φ_m`.** -/
theorem cov_diag_contract (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (f : Matrix (Fin W) (Fin W) ℂ) (r : ℝ) (σ σ' : ℂ)
    {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      ((r : ℂ) * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) {φ : Fin W → ℝ} {Φ : ℝ} (hφ : ∀ i, |φ i| ≤ Φ) :
    ‖∑ i, ∑ m, ((ts_lam hT i * φ i * (ts_lam hT m * φ m) : ℝ) : ℂ) *
        bilinearCovariance μ U (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) -
      ((2 * r * ∑ i, ts_lam hT i ^ 2 * φ i ^ 2 * (1 - ts_lam hT i) : ℝ) : ℂ)‖ ≤
      (‖σ‖ + ‖σ'‖) * Φ ^ 2 * hsSandwich T f ^ 2 + ε * Φ ^ 2 * T.trace.re ^ 2 := by
  set t := ts_lam hT
  set fe := ts_ent hT f
  have ht := ts_lam_nonneg hT
  set w : Fin W → Fin W → ℝ := fun i m => t i * φ i * (t m * φ m)
  have hw : ∀ i m, |w i m| ≤ Φ ^ 2 * (t i * t m) := fun i m => by
    simp only [w]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (ht i), abs_of_nonneg (ht m)]
    have := mul_le_mul (hφ i) (hφ m) (abs_nonneg _) ((abs_nonneg _).trans (hφ i))
    nlinarith [mul_nonneg (ht i) (ht m), abs_nonneg (φ i), abs_nonneg (φ m)]
  set M : Fin W → Fin W → ℂ := fun i m => (if i = m then (r : ℂ) * (2 * (1 - (t i : ℂ))) else 0) +
      σ * (fe i m * fe m i) + σ' * (conj (fe m i) * conj (fe i m))
  have h1 : ‖∑ i, ∑ m, ((w i m : ℝ) : ℂ) *
      bilinearCovariance μ U (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) -
      ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * M i m‖ ≤ ε * Φ ^ 2 * T.trace.re ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hsq : ε * Φ ^ 2 * T.trace.re ^ 2 = ∑ i, ∑ m, ε * (Φ ^ 2 * (t i * t m)) := by
      rw [← ts_sum_lam hT, pow_two (∑ i, ts_lam hT i), Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hsq]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hc := hcov (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m)
    rw [fourNorm_eigen_diag, mul_one, br_crossed hT f (r : ℂ) σ σ' i m] at hc
    calc |w i m| * ‖_‖ ≤ (Φ ^ 2 * (t i * t m)) * ε :=
          mul_le_mul (hw i m) hc (norm_nonneg _) ((abs_nonneg _).trans (hw i m))
      _ = _ := by ring
  have hdiag : ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * (if i = m then (r : ℂ) * (2 * (1 - (t i : ℂ))) else 0)
      = ((2 * r * ∑ i, t i ^ 2 * φ i ^ 2 * (1 - t i) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun m _ hm => by simp [Ne.symm hm]) (by simp)]
    simp only [w]; push_cast; ring
  have hF := fterm_weight_le hT ht1 hφ f σ σ'
  have hsplit : ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * M i m =
      ((2 * r * ∑ i, t i ^ 2 * φ i ^ 2 * (1 - t i) : ℝ) : ℂ) +
      ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * (σ * (fe i m * fe m i) +
        σ' * (conj (fe m i) * conj (fe i m))) := by
    rw [← hdiag, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [M]; ring
  have e : ∑ i, ∑ m, ((t i * φ i * (t m * φ m) : ℝ) : ℂ) *
      bilinearCovariance μ U (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) -
      ((2 * r * ∑ i, t i ^ 2 * φ i ^ 2 * (1 - t i) : ℝ) : ℂ) =
      (∑ i, ∑ m, ((w i m : ℝ) : ℂ) *
        bilinearCovariance μ U (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) -
      ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * M i m) +
      ∑ i, ∑ m, ((w i m : ℝ) : ℂ) * (σ * (fe i m * fe m i) +
        σ' * (conj (fe m i) * conj (fe i m))) := by
    rw [hsplit]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- The crossed pattern `(v_i, v_m, v_m, v_i)` of the PCB shape. -/
theorem cross_crossed (hT : T.PosSemidef) (f : Matrix (Fin W) (Fin W) ℂ) (a σ σ' : ℂ)
    (i m : Fin W) :
    a * (crossedTensor (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) (ts_vec hT i) 1 (1 - T) +
        crossedTensor (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) (ts_vec hT i) (1 - T) 1) +
      σ * crossedTensor (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) (ts_vec hT i) f f +
      σ' * crossedTensor (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) (ts_vec hT i) fᴴ fᴴ =
    a * ((2 - ts_lam hT i - ts_lam hT m : ℝ) : ℂ) + σ * (ts_ent hT f i i * ts_ent hT f m m) +
      σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m)) := by
  simp only [crossedTensor, bilinear_one_eigen, bilinear_one_sub_eigen,
    bilinear_conjTranspose_self, ts_ent]
  push_cast; ring

/-- **The covariance contracted with the quadratic weights `t_k φ_k t_m φ_m`.** -/
theorem cov_cross_contract (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (f : Matrix (Fin W) (Fin W) ℂ) (a σ σ' : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      (a * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) {φ : Fin W → ℝ} {Φ : ℝ} (hφ : ∀ i, |φ i| ≤ Φ) :
    ‖∑ i, ∑ m, ((ts_lam hT i * φ i * (ts_lam hT m * φ m) : ℝ) : ℂ) *
        (bilinearCovariance μ U (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) (ts_vec hT i) -
          (a * ((2 - ts_lam hT i - ts_lam hT m : ℝ) : ℂ) +
            σ * (ts_ent hT f i i * ts_ent hT f m m) +
            σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m))))‖ ≤
      ε * Φ ^ 2 * T.trace.re ^ 2 := by
  set t := ts_lam hT
  have ht := ts_lam_nonneg hT
  have hsq : ε * Φ ^ 2 * T.trace.re ^ 2 = ∑ i, ∑ m, ε * (Φ ^ 2 * (t i * t m)) := by
    rw [← ts_sum_lam hT, pow_two (∑ i, ts_lam hT i), Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hsq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc := hcov (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) (ts_vec hT i)
  rw [fourNorm_eigen, mul_one, cross_crossed hT f a σ σ' i m] at hc
  have hw : |t i * φ i * (t m * φ m)| ≤ Φ ^ 2 * (t i * t m) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (ht i), abs_of_nonneg (ht m)]
    have := mul_le_mul (hφ i) (hφ m) (abs_nonneg _) ((abs_nonneg _).trans (hφ i))
    nlinarith [mul_nonneg (ht i) (ht m), abs_nonneg (φ i), abs_nonneg (φ m)]
  calc |t i * φ i * (t m * φ m)| * ‖_‖ ≤ (Φ ^ 2 * (t i * t m)) * ε :=
        mul_le_mul hw hc (norm_nonneg _) ((abs_nonneg _).trans hw)
    _ = _ := by ring

/-- **Weighted source term**: `‖Σ t_k φ_k f'_{kk}‖ ≤ |φ₀|‖Tr(Tf)‖ + L√(Tr T)hs(T,f)` when
`|φ_k − φ₀| ≤ Lt_k`. -/
theorem norm_sum_weight_fd_le (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (f : Matrix (Fin W) (Fin W) ℂ) {φ : Fin W → ℝ} {φ₀ L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ i, |φ i - φ₀| ≤ L * ts_lam hT i) :
    ‖∑ i, ((ts_lam hT i * φ i : ℝ) : ℂ) * ts_ent hT f i i‖ ≤
      |φ₀| * ‖(T * f).trace‖ + L * (Real.sqrt T.trace.re * hsSandwich T f) := by
  set t := ts_lam hT
  have ht := ts_lam_nonneg hT
  have e : ∑ i, ((t i * φ i : ℝ) : ℂ) * ts_ent hT f i i =
      (φ₀ : ℂ) * (T * f).trace + ∑ i, ((t i * (φ i - φ₀) : ℝ) : ℂ) * ts_ent hT f i i := by
    rw [ts_trace_mul hT f, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (by rw [norm_mul, Complex.norm_real,
    Real.norm_eq_abs]) ?_)
  have hcs : ∑ i, t i * (t i * ‖ts_ent hT f i i‖) ≤
      Real.sqrt (∑ i, t i ^ 2) * Real.sqrt (∑ i, (t i * ‖ts_ent hT f i i‖) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have ha : ∑ i, t i ^ 2 ≤ T.trace.re := by
    rw [← ts_sum_lam hT]
    exact Finset.sum_le_sum fun i _ => by nlinarith [ht i, ht1 i]
  have hb : ∑ i, (t i * ‖ts_ent hT f i i‖) ^ 2 ≤ hsSandwich T f ^ 2 := by
    rw [ts_hs_eq hT, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (ht i) (ht j)) (sq_nonneg _))]
    refine Finset.sum_le_sum fun i _ => ?_
    have := Finset.single_le_sum (f := fun j => t i * t j * ‖ts_ent hT f i j‖ ^ 2)
      (fun j _ => mul_nonneg (mul_nonneg (ht i) (ht j)) (sq_nonneg _)) (Finset.mem_univ i)
    nlinarith
  calc ‖∑ i, ((t i * (φ i - φ₀) : ℝ) : ℂ) * ts_ent hT f i i‖
      ≤ ∑ i, L * (t i * (t i * ‖ts_ent hT f i i‖)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (ht i)]
        have := mul_le_mul_of_nonneg_left (hφ i) (ht i)
        nlinarith [norm_nonneg (ts_ent hT f i i)]
    _ = L * ∑ i, t i * (t i * ‖ts_ent hT f i i‖) := by rw [Finset.mul_sum]
    _ ≤ L * (Real.sqrt T.trace.re * hsSandwich T f) := by
        refine mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul (Real.sqrt_le_sqrt ha) ?_
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hL
        calc Real.sqrt (∑ i, (t i * ‖ts_ent hT f i i‖) ^ 2)
            ≤ Real.sqrt (hsSandwich T f ^ 2) := Real.sqrt_le_sqrt hb
          _ = hsSandwich T f := Real.sqrt_sq (Real.sqrt_nonneg _)

end BlockBand.Transmission.LawForced
