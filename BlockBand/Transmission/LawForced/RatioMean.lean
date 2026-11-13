module

public import BlockBand.Transmission.LawForced.RatioStep
public import BlockBand.Transmission.LawForced.RatioCov
public import BlockBand.Transmission.Generator.StepQuad

/-!
# The exact one-layer mean of the `F_z` expansion terms

Under any probability law `μ` with a random Hermitian `U` (entries integrable, `U⁰ = U − Ū`
with the two products `U⁰'_{im}U⁰'_{mi}`, `U⁰'_{ii}U⁰'_{mm}` integrable), with
`t = ts_lam hT`, `S = sand T U`, `B̄ = sand T Ū − diag t`:
* `linB`, `quadB`, `crossB`: the terms of `RatioStep` as functions of `B = S − diag t`;
  `linB_add`, `quadB_add` (`quadB(A + B̄) = quadB A + quadB B̄ + crossB B̄ A`);
* `linB_eq_dualLam`: `linB z t B = −Σ_k Λ_z(t_k) Re B_kk`;
* `trace_rBrB`: `Tr(RBRB) = Σ_{km} r_kr_mB_kmB_mk`;
* `linB_centered`, `crossB_centered`, `integral_rBrB`: the centred linear terms vanish
  (`integral_trace_mul_sand_centered`) and `E Re Tr(R S⁰ R S⁰)` is a covariance contraction.

They give, in the sibling module, `integral_ratio_terms`: `∫ (linR + quadR + linR²/2)(S) =
linB B̄ + quadB B̄ + (linB B̄)²/2 + Σ_i[(x_i²/2)Re C(x_i) − (y_i²/2)Re C(−y_i)] + (1/2)Re V`,
where `C(w) = Σ_{km} t_kr_kt_mr_m Cov(v_k,v_m,v_m,v_k)` (`r = (1+wt)⁻¹`) and
`V = Σ_{km} t_kΛ_kt_mΛ_m Cov(v_k,v_k,v_m,v_m)`; the integrand is integrable.
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

variable {p : ℕ}

section Alg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The first-order term as a function of `B`. -/
def linB (z : DualCoord p) (t : n → ℝ) (B : Matrix n n ℂ) : ℝ :=
  ∑ i, (-z.2 i * (rres (-z.2 i) t * B).trace.re - z.1 i * (rres (z.1 i) t * B).trace.re)

/-- The second-order term as a function of `B`. -/
def quadB (z : DualCoord p) (t : n → ℝ) (B : Matrix n n ℂ) : ℝ :=
  ∑ i, (z.1 i ^ 2 / 2 * (rres (z.1 i) t * B * rres (z.1 i) t * B).trace.re -
    z.2 i ^ 2 / 2 * (rres (-z.2 i) t * B * rres (-z.2 i) t * B).trace.re)

/-- The cross term of `quadB`, linear in `A`. -/
def crossB (z : DualCoord p) (t : n → ℝ) (Bb A : Matrix n n ℂ) : ℝ :=
  ∑ i, (z.1 i ^ 2 * (rres (z.1 i) t * Bb * rres (z.1 i) t * A).trace.re -
    z.2 i ^ 2 * (rres (-z.2 i) t * Bb * rres (-z.2 i) t * A).trace.re)

theorem linR_eq_linB (z : DualCoord p) (t : n → ℝ) (S : Matrix n n ℂ) :
    linR z t S = linB z t (S - dmat t) := rfl

theorem quadR_eq_quadB (z : DualCoord p) (t : n → ℝ) (S : Matrix n n ℂ) :
    quadR z t S = quadB z t (S - dmat t) := rfl

theorem linB_add (z : DualCoord p) (t : n → ℝ) (A B : Matrix n n ℂ) :
    linB z t (A + B) = linB z t A + linB z t B := by
  unfold linB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_add, trace_add, Complex.add_re]; ring

omit [DecidableEq n] in
theorem trace_rBrB_add (R A B : Matrix n n ℂ) :
    (R * (A + B) * R * (A + B)).trace =
      (R * A * R * A).trace + (R * B * R * B).trace + 2 * (R * B * R * A).trace := by
  have h1 : (R * A * R * B).trace = (R * B * R * A).trace := by
    calc (R * A * R * B).trace = (R * (A * R * B)).trace := by simp only [Matrix.mul_assoc]
      _ = (A * R * B * R).trace := Matrix.trace_mul_comm _ _
      _ = (A * (R * B * R)).trace := by simp only [Matrix.mul_assoc]
      _ = (R * B * R * A).trace := Matrix.trace_mul_comm _ _
  simp only [Matrix.mul_add, Matrix.add_mul, trace_add]
  rw [h1]; ring

theorem quadB_add (z : DualCoord p) (t : n → ℝ) (A Bb : Matrix n n ℂ) :
    quadB z t (A + Bb) = quadB z t A + quadB z t Bb + crossB z t Bb A := by
  unfold quadB crossB
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ∀ c : ℂ, (2 * c).re = 2 * c.re := fun c => by simp
  simp only [trace_rBrB_add, Complex.add_re, h2]; ring

theorem trace_rres_mul (w : ℝ) (t : n → ℝ) (B : Matrix n n ℂ) :
    (rres w t * B).trace = ∑ k, (((1 + w * t k)⁻¹ : ℝ) : ℂ) * B k k := by
  simp only [rres, Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

theorem linB_eq_dualLam (z : DualCoord p) (t : n → ℝ) (B : Matrix n n ℂ) :
    linB z t B = -∑ k, dualLam z (t k) * (B k k).re := by
  unfold linB dualLam
  simp only [trace_rres_mul, Complex.re_sum, Complex.re_ofReal_mul]
  have e : ∀ i, -z.2 i * ∑ k, (1 + -z.2 i * t k)⁻¹ * (B k k).re -
      z.1 i * ∑ k, (1 + z.1 i * t k)⁻¹ * (B k k).re =
      -∑ k, (z.1 i / (1 + z.1 i * t k) + z.2 i / (1 - z.2 i * t k)) * (B k k).re := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_mul (z.2 i) (t k), ← sub_eq_add_neg]; ring
  simp only [e, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_mul]

/-- `Tr(RBRB) = Σ_{km} r_kr_mB_kmB_mk`. -/
theorem trace_rBrB (w : ℝ) (t : n → ℝ) (B : Matrix n n ℂ) :
    (rres w t * B * rres w t * B).trace =
      ∑ k, ∑ m, (((1 + w * t k)⁻¹ * (1 + w * t m)⁻¹ : ℝ) : ℂ) * (B k m * B m k) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [rres, Matrix.mul_diagonal, Matrix.diagonal_mul]
  push_cast; ring

end Alg

section Law

variable {W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

theorem re_trace_centered (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Integrable (fun ω => (X * sand hT (U ω - matrixExpect μ U)).trace.re) μ ∧
      ∫ ω, (X * sand hT (U ω - matrixExpect μ U)).trace.re ∂μ = 0 := by
  obtain ⟨h1, h2⟩ := integral_trace_mul_sand_centered hT U hUi X
  exact ⟨integrable_cre h1, by rw [integral_cre h1, h2, Complex.zero_re]⟩

theorem linB_centered (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ) (z : DualCoord p) (t : Fin W → ℝ) :
    Integrable (fun ω => linB z t (sand hT (U ω - matrixExpect μ U))) μ ∧
      ∫ ω, linB z t (sand hT (U ω - matrixExpect μ U)) ∂μ = 0 := by
  have h := fun w : ℝ => re_trace_centered hT U hUi (rres w t)
  have hI : ∀ i, Integrable (fun ω => -z.2 i * (rres (-z.2 i) t *
      sand hT (U ω - matrixExpect μ U)).trace.re - z.1 i * (rres (z.1 i) t *
      sand hT (U ω - matrixExpect μ U)).trace.re) μ := fun i =>
    ((h _).1.const_mul _).sub ((h _).1.const_mul _)
  refine ⟨integrable_finsetSum _ fun i _ => hI i, ?_⟩
  unfold linB
  rw [integral_finsetSum _ fun i _ => hI i]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_sub ((h _).1.const_mul _) ((h _).1.const_mul _), integral_const_mul,
    integral_const_mul, (h _).2, (h _).2]; ring

theorem crossB_centered (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ) (z : DualCoord p) (t : Fin W → ℝ)
    (Bb : Matrix (Fin W) (Fin W) ℂ) :
    Integrable (fun ω => crossB z t Bb (sand hT (U ω - matrixExpect μ U))) μ ∧
      ∫ ω, crossB z t Bb (sand hT (U ω - matrixExpect μ U)) ∂μ = 0 := by
  have h := fun w : ℝ => re_trace_centered hT U hUi (rres w t * Bb * rres w t)
  have hI : ∀ i, Integrable (fun ω => z.1 i ^ 2 * (rres (z.1 i) t * Bb * rres (z.1 i) t *
      sand hT (U ω - matrixExpect μ U)).trace.re - z.2 i ^ 2 * (rres (-z.2 i) t * Bb *
      rres (-z.2 i) t * sand hT (U ω - matrixExpect μ U)).trace.re) μ := fun i =>
    ((h _).1.const_mul _).sub ((h _).1.const_mul _)
  refine ⟨integrable_finsetSum _ fun i _ => hI i, ?_⟩
  unfold crossB
  rw [integral_finsetSum _ fun i _ => hI i]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_sub ((h _).1.const_mul _) ((h _).1.const_mul _), integral_const_mul,
    integral_const_mul, (h _).2, (h _).2]; ring

omit [IsProbabilityMeasure μ] in
/-- `E Re Tr(R S⁰ R S⁰)` as a covariance contraction. -/
theorem integral_rBrB (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i m *
      ts_ent hT (U ω - matrixExpect μ U) m i) μ) (w : ℝ) :
    Integrable (fun ω => (rres w (ts_lam hT) * sand hT (U ω - matrixExpect μ U) *
      rres w (ts_lam hT) * sand hT (U ω - matrixExpect μ U)).trace.re) μ ∧
    ∫ ω, (rres w (ts_lam hT) * sand hT (U ω - matrixExpect μ U) * rres w (ts_lam hT) *
        sand hT (U ω - matrixExpect μ U)).trace.re ∂μ =
      (∑ k, ∑ m, ((ts_lam hT k * (1 + w * ts_lam hT k)⁻¹ *
        (ts_lam hT m * (1 + w * ts_lam hT m)⁻¹) : ℝ) : ℂ) *
        bilinearCovariance μ U (ts_vec hT k) (ts_vec hT m) (ts_vec hT m) (ts_vec hT k)).re := by
  set t := ts_lam hT
  set Z := fun ω => U ω - matrixExpect μ U
  have e : ∀ ω, (rres w t * sand hT (Z ω) * rres w t * sand hT (Z ω)).trace =
      ∑ k, ∑ m, ((t k * (1 + w * t k)⁻¹ * (t m * (1 + w * t m)⁻¹) : ℝ) : ℂ) *
        (ts_ent hT (Z ω) k m * ts_ent hT (Z ω) m k) := fun ω => by
    rw [trace_rBrB]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
    rw [sand_mul_sand]; push_cast; ring
  have hI : ∀ k m, Integrable (fun ω => ((t k * (1 + w * t k)⁻¹ * (t m * (1 + w * t m)⁻¹) : ℝ) :
      ℂ) * (ts_ent hT (Z ω) k m * ts_ent hT (Z ω) m k)) μ := fun k m => (hp k m).const_mul _
  have hC : Integrable (fun ω => (rres w t * sand hT (Z ω) * rres w t *
      sand hT (Z ω)).trace) μ := by
    simp only [e]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun m _ => hI k m
  refine ⟨integrable_cre hC, ?_⟩
  rw [integral_cre hC]
  congr 1
  simp only [e]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun m _ => hI k m]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun m _ => hI k m]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, bilinearCovariance]
  rfl

end Law

end BlockBand.Transmission.LawForced
