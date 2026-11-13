module

public import BlockBand.Transmission.LawForced.RatioMean

/-!
# The one-layer mean of `linR + quadR + linR²/2`

Notation of `RatioMean`. With `t = ts_lam hT`, `Λ_k = Λ_z(t_k)`, `r^w_k = (1+wt_k)⁻¹`:
* `covQ hT U w = Σ_{km} t_kr^w_kt_mr^w_m Cov(v_k,v_m,v_m,v_k)`;
* `covV hT U z = Σ_{km} t_kΛ_kt_mΛ_m Cov(v_k,v_k,v_m,v_m)`;
* `quadB_centered`: `E quadB(S⁰) = Σ_i[(x_i²/2)Re covQ(x_i) − (y_i²/2)Re covQ(−y_i)]`;
* `linB_sq_centered` (`U` Hermitian): `E linB(S⁰)² = Re covV`;
* **`integral_ratio_terms`**: for `S = sand T U`, `B̄ = sand T Ū − diag t`,
  `E[linR + quadR + linR²/2](S) = linB B̄ + quadB B̄ + (linB B̄)²/2 + E quadB(S⁰) + Re covV/2`,
  with the integrand integrable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder ComplexConjugate

variable {p W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}

/-- The quadratic covariance contraction at weight point `w`. -/
def covQ (μ : Measure Ω) (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ) (w : ℝ) : ℂ :=
  ∑ k, ∑ m, ((ts_lam hT k * (1 + w * ts_lam hT k)⁻¹ * (ts_lam hT m * (1 + w * ts_lam hT m)⁻¹) :
    ℝ) : ℂ) * bilinearCovariance μ U (ts_vec hT k) (ts_vec hT m) (ts_vec hT m) (ts_vec hT k)

/-- The variance covariance contraction. -/
def covV (μ : Measure Ω) (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (z : DualCoord p) : ℂ :=
  ∑ k, ∑ m, ((ts_lam hT k * dualLam z (ts_lam hT k) * (ts_lam hT m * dualLam z (ts_lam hT m)) :
    ℝ) : ℂ) * bilinearCovariance μ U (ts_vec hT k) (ts_vec hT k) (ts_vec hT m) (ts_vec hT m)

/-- The mean of the centred quadratic term. -/
def quadMean (μ : Measure Ω) (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (z : DualCoord p) : ℝ :=
  ∑ i, (z.1 i ^ 2 / 2 * (covQ μ hT U (z.1 i)).re - z.2 i ^ 2 / 2 * (covQ μ hT U (-z.2 i)).re)

theorem quadB_centered (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i m *
      ts_ent hT (U ω - matrixExpect μ U) m i) μ) (z : DualCoord p) :
    Integrable (fun ω => quadB z (ts_lam hT) (sand hT (U ω - matrixExpect μ U))) μ ∧
      ∫ ω, quadB z (ts_lam hT) (sand hT (U ω - matrixExpect μ U)) ∂μ = quadMean μ hT U z := by
  have h := fun w : ℝ => integral_rBrB hT U hp w
  have hI : ∀ i, Integrable (fun ω => z.1 i ^ 2 / 2 * (rres (z.1 i) (ts_lam hT) *
      sand hT (U ω - matrixExpect μ U) * rres (z.1 i) (ts_lam hT) *
      sand hT (U ω - matrixExpect μ U)).trace.re - z.2 i ^ 2 / 2 * (rres (-z.2 i) (ts_lam hT) *
      sand hT (U ω - matrixExpect μ U) * rres (-z.2 i) (ts_lam hT) *
      sand hT (U ω - matrixExpect μ U)).trace.re) μ := fun i =>
    ((h _).1.const_mul _).sub ((h _).1.const_mul _)
  refine ⟨integrable_finsetSum _ fun i _ => hI i, ?_⟩
  unfold quadB quadMean
  rw [integral_finsetSum _ fun i _ => hI i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_sub ((h _).1.const_mul _) ((h _).1.const_mul _), integral_const_mul,
    integral_const_mul, (h _).2, (h _).2]
  rfl

/-- `E linB(S⁰)² = Re covV` for Hermitian `U`. -/
theorem linB_sq_centered (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hUH : ∀ ω, (U ω).IsHermitian)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i i *
      ts_ent hT (U ω - matrixExpect μ U) m m) μ) (z : DualCoord p) :
    Integrable (fun ω => linB z (ts_lam hT) (sand hT (U ω - matrixExpect μ U)) ^ 2) μ ∧
      ∫ ω, linB z (ts_lam hT) (sand hT (U ω - matrixExpect μ U)) ^ 2 ∂μ =
        (covV μ hT U z).re := by
  set t := ts_lam hT
  set Z := fun ω => U ω - matrixExpect μ U
  set X : Ω → ℂ := fun ω => ∑ k, ((t k * dualLam z (t k) : ℝ) : ℂ) * ts_ent hT (Z ω) k k
  have hZH : ∀ ω, (Z ω).IsHermitian := fun ω => (hUH ω).sub (matrixExpect_isHermitian U hUH)
  have him : ∀ ω, (X ω).im = 0 := fun ω => by
    simp only [X, Complex.im_sum, Complex.im_ofReal_mul, im_ts_ent_herm hT (hZH ω), mul_zero,
      Finset.sum_const_zero]
  have hlin : ∀ ω, linB z t (sand hT (Z ω)) = -(X ω).re := fun ω => by
    rw [linB_eq_dualLam]
    simp only [X, Complex.re_sum, Complex.re_ofReal_mul, sand_apply,
      Real.mul_self_sqrt (ts_lam_nonneg hT _)]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsq : ∀ ω, linB z t (sand hT (Z ω)) ^ 2 = (X ω * X ω).re := fun ω => by
    rw [hlin, Complex.mul_re, him]; ring
  have hXX : ∀ ω, X ω * X ω = ∑ k, ∑ m, ((t k * dualLam z (t k) * (t m * dualLam z (t m)) : ℝ) :
      ℂ) * (ts_ent hT (Z ω) k k * ts_ent hT (Z ω) m m) := fun ω => by
    simp only [X, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
    push_cast; ring
  have hI : ∀ k m, Integrable (fun ω => ((t k * dualLam z (t k) * (t m * dualLam z (t m)) : ℝ) :
      ℂ) * (ts_ent hT (Z ω) k k * ts_ent hT (Z ω) m m)) μ := fun k m => (hp k m).const_mul _
  have hC : Integrable (fun ω => X ω * X ω) μ := by
    simp only [hXX]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun m _ => hI k m
  have e : ∀ ω, linB z t (sand hT (U ω - matrixExpect μ U)) ^ 2 = (X ω * X ω).re := hsq
  simp only [e]
  refine ⟨integrable_cre hC, ?_⟩
  rw [integral_cre hC]
  congr 1
  simp only [hXX]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun m _ => hI k m]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun m _ => hI k m]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, bilinearCovariance]
  rfl

/-- **The one-layer mean of the expansion terms.** -/
theorem integral_ratio_terms [IsProbabilityMeasure μ] (hT : T.PosSemidef)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ)
    (hUH : ∀ ω, (U ω).IsHermitian)
    (hp1 : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i m *
      ts_ent hT (U ω - matrixExpect μ U) m i) μ)
    (hp2 : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i i *
      ts_ent hT (U ω - matrixExpect μ U) m m) μ) (z : DualCoord p) :
    Integrable (fun ω => linR z (ts_lam hT) (sand hT (U ω)) + quadR z (ts_lam hT) (sand hT (U ω)) +
      linR z (ts_lam hT) (sand hT (U ω)) ^ 2 / 2) μ ∧
    ∫ ω, (linR z (ts_lam hT) (sand hT (U ω)) + quadR z (ts_lam hT) (sand hT (U ω)) +
        linR z (ts_lam hT) (sand hT (U ω)) ^ 2 / 2) ∂μ =
      linB z (ts_lam hT) (sand hT (matrixExpect μ U) - dmat (ts_lam hT)) +
        quadB z (ts_lam hT) (sand hT (matrixExpect μ U) - dmat (ts_lam hT)) +
        linB z (ts_lam hT) (sand hT (matrixExpect μ U) - dmat (ts_lam hT)) ^ 2 / 2 +
        quadMean μ hT U z + (covV μ hT U z).re / 2 := by
  set t := ts_lam hT
  set Bb := sand hT (matrixExpect μ U) - dmat t
  set A : Ω → Matrix (Fin W) (Fin W) ℂ := fun ω => sand hT (U ω - matrixExpect μ U)
  have hdec : ∀ ω, sand hT (U ω) - dmat t = A ω + Bb := fun ω => by
    simp only [A, Bb, sand_sub]; abel
  have hl := linB_centered hT U hUi z t
  have hc := crossB_centered hT U hUi z t Bb
  have hq := quadB_centered hT U hp1 z
  have hs := linB_sq_centered hT U hUH hp2 z
  set lb := linB z t Bb
  have hpt : ∀ ω, linR z t (sand hT (U ω)) + quadR z t (sand hT (U ω)) +
      linR z t (sand hT (U ω)) ^ 2 / 2 =
      ((1 + lb) * linB z t (A ω) + crossB z t Bb (A ω)) +
        quadB z t (A ω) + linB z t (A ω) ^ 2 / 2 + (lb + quadB z t Bb + lb ^ 2 / 2) := fun ω => by
    rw [linR_eq_linB, quadR_eq_quadB, hdec, linB_add, quadB_add]; ring
  have i1 : Integrable (fun ω => (1 + lb) * linB z t (A ω) + crossB z t Bb (A ω)) μ :=
    (hl.1.const_mul _).add hc.1
  have i2 : Integrable (fun ω => (1 + lb) * linB z t (A ω) + crossB z t Bb (A ω) +
      quadB z t (A ω)) μ := i1.add hq.1
  have i3 : Integrable (fun ω => (1 + lb) * linB z t (A ω) + crossB z t Bb (A ω) +
      quadB z t (A ω) + linB z t (A ω) ^ 2 / 2) μ := i2.add (hs.1.div_const 2)
  have j1 : Integrable (fun ω => (1 + lb) * linB z t (A ω)) μ := hl.1.const_mul _
  have k1 : ∫ ω, (1 + lb) * linB z t (A ω) ∂μ = 0 := by rw [integral_const_mul, hl.2, mul_zero]
  have k2 : ∫ ω, linB z t (A ω) ^ 2 / 2 ∂μ = (covV μ hT U z).re / 2 := by
    rw [integral_div]; exact congrArg (· / 2) hs.2
  simp only [hpt]
  refine ⟨i3.add (integrable_const _), ?_⟩
  rw [integral_add i3 (integrable_const _), integral_add i2 (hs.1.div_const 2),
    integral_add i1 hq.1, integral_add j1 hc.1, k1, k2, hc.2, hq.2, integral_const,
    probReal_univ, one_smul]
  ring

end BlockBand.Transmission.LawForced
