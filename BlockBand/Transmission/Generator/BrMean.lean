module

public import BlockBand.Transmission.Generator.BrLaw

/-!
# The one-layer bracket for an abstract random layer: the expectation

**`br_law`**: `|E Δ_{k+1}Δ_{l+1} - (k+1)(l+1)·2rΣ_i t_i^{k+l+2}(1-t_i)| ≤
(k+1)(l+1)Er + (2c_l/s)(k+1)²M + (2c_k/s)(l+1)²M + A₃H₄ + A₄`
(`br_point_ae` integrated; the cross terms `x_k b_l` have mean zero; `br_xx` for `E x_k x_l` and for
`E x_k² ≤ k²M`).
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

theorem integrable_brLin_centered [IsFiniteMeasure μ] (hT : T.PosSemidef)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ) (k : ℕ) :
    Integrable (fun ω => brLin hT k (U ω - matrixExpect μ U)) μ :=
  integrable_finsetSum _ fun i _ => (integrable_ts_ent_centered hT U hUi i i).const_mul _

theorem integral_brLin_centered [IsProbabilityMeasure μ] (hT : T.PosSemidef)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ) (k : ℕ) :
    ∫ ω, brLin hT k (U ω - matrixExpect μ U) ∂μ = 0 := by
  simp only [brLin]
  rw [integral_finsetSum _ fun i _ => (integrable_ts_ent_centered hT U hUi i i).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, integral_ts_ent_centered hT U hUi, mul_zero]

/-- `E x_k² ≤ k²(2|r|g + Er)`. -/
theorem br_sq_le [IsProbabilityMeasure μ] (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUH : ∀ ω, (U ω).IsHermitian)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i i *
      ts_ent hT (U ω - matrixExpect μ U) m m) μ)
    (f : Matrix (Fin W) (Fin W) ℂ) (r : ℝ) (σ σ' : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      ((r : ℂ) * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun ω => ((k : ℝ) * (brLin hT k (U ω - matrixExpect μ U)).re) ^ 2) μ ∧
    ∫ ω, ((k : ℝ) * (brLin hT k (U ω - matrixExpect μ U)).re) ^ 2 ∂μ ≤
      (k : ℝ) ^ 2 * (2 * |r| * T.trace.re +
        ((‖σ‖ + ‖σ'‖) * hsSandwich T f ^ 2 + ε * T.trace.re ^ 2)) := by
  obtain ⟨hI, hb⟩ := br_xx hT ht1 U hUH hp f r σ σ' hcov hk hk
  have e : (fun ω => ((k : ℝ) * (brLin hT k (U ω - matrixExpect μ U)).re) ^ 2) =
      fun ω => (k : ℝ) * (brLin hT k (U ω - matrixExpect μ U)).re *
        ((k : ℝ) * (brLin hT k (U ω - matrixExpect μ U)).re) := funext fun ω => sq _
  rw [e]
  refine ⟨hI, ?_⟩
  obtain ⟨w0, w1⟩ := br_weight_le hT ht1 (m := k + k) (by omega)
  have hw : 2 * r * ∑ i, ts_lam hT i ^ (k + k) * (1 - ts_lam hT i) ≤ 2 * |r| * T.trace.re := by
    have := le_abs_self r
    calc 2 * r * ∑ i, ts_lam hT i ^ (k + k) * (1 - ts_lam hT i) ≤
        2 * |r| * ∑ i, ts_lam hT i ^ (k + k) * (1 - ts_lam hT i) := by gcongr
      _ ≤ 2 * |r| * T.trace.re := by gcongr
  have := (abs_le.mp hb).2
  have hk2 : (k : ℝ) * k = (k : ℝ) ^ 2 := (sq _).symm
  rw [hk2] at this
  nlinarith [sq_nonneg (k : ℝ)]

/-- **The one-layer bracket for an abstract random layer.** -/
theorem br_law [IsProbabilityMeasure μ] (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUm : Measurable U) (hUH : ∀ ω, (U ω).IsHermitian)
    (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i i *
      ts_ent hT (U ω - matrixExpect μ U) m m) μ)
    (hS : ∀ᵐ ω ∂μ, ‖sand hT (U ω)‖ ≤ 1) {ν : ℝ} (hν : ‖matrixExpect μ U - 1‖ ≤ ν) {H4 : ℝ}
    (hh : Integrable (fun ω => frobSq (sand hT (U ω - matrixExpect μ U)) ^ 2) μ)
    (hH4 : ∫ ω, frobSq (sand hT (U ω - matrixExpect μ U)) ^ 2 ∂μ ≤ H4)
    (f : Matrix (Fin W) (Fin W) ℂ) (r : ℝ) (σ σ' : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      ((r : ℂ) * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) {s : ℝ} (hs : 0 < s) (k l : ℕ) :
    |∫ ω, brInc hT (k + 1) (U ω) * brInc hT (l + 1) (U ω) ∂μ -
        ((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ) *
          (2 * r * ∑ i, ts_lam hT i ^ (k + 1 + (l + 1)) * (1 - ts_lam hT i))| ≤
      ((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ) *
          ((‖σ‖ + ‖σ'‖) * hsSandwich T f ^ 2 + ε * T.trace.re ^ 2) +
        2 * (((l + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (l + 1))) / s * (((k + 1 : ℕ) : ℝ) ^ 2 *
          (2 * |r| * T.trace.re + ((‖σ‖ + ‖σ'‖) * hsSandwich T f ^ 2 + ε * T.trace.re ^ 2))) +
        2 * (((k + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (k + 1))) / s * (((l + 1 : ℕ) : ℝ) ^ 2 *
          (2 * |r| * T.trace.re + ((‖σ‖ + ‖σ'‖) * hsSandwich T f ^ 2 + ε * T.trace.re ^ 2))) +
        (s * (((k + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (k + 1)) +
            ((l + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (l + 1))) +
          8 * ((((k + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (k + 1))) ^ 2 +
            (((l + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (l + 1))) ^ 2)) * H4 +
        ((s * (((k + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (k + 1)) +
            ((l + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (l + 1))) +
          8 * ((((k + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (k + 1))) ^ 2 +
            (((l + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (l + 1))) ^ 2)) * (ν ^ 2 * T.trace.re) ^ 2 +
          ((((k + 1 : ℕ) : ℝ) * (ν * T.trace.re)) ^ 2 +
            (((l + 1 : ℕ) : ℝ) * (ν * T.trace.re)) ^ 2)) := by
  set Ub := matrixExpect μ U
  set ck := ((k + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (k + 1))
  set cl := ((l + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (l + 1))
  set A3 := s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2)
  set A4 := A3 * (ν ^ 2 * T.trace.re) ^ 2 +
    ((((k + 1 : ℕ) : ℝ) * (ν * T.trace.re)) ^ 2 + (((l + 1 : ℕ) : ℝ) * (ν * T.trace.re)) ^ 2)
  set xk : Ω → ℝ := fun ω => ((k + 1 : ℕ) : ℝ) * (brLin hT (k + 1) (U ω - Ub)).re
  set xl : Ω → ℝ := fun ω => ((l + 1 : ℕ) : ℝ) * (brLin hT (l + 1) (U ω - Ub)).re
  set bk : ℝ := ((k + 1 : ℕ) : ℝ) * (brLin hT (k + 1) (Ub - 1)).re
  set bl : ℝ := ((l + 1 : ℕ) : ℝ) * (brLin hT (l + 1) (Ub - 1)).re
  set h : Ω → ℝ := fun ω => frobSq (sand hT (U ω - Ub))
  set D : Ω → ℝ := fun ω => brInc hT (k + 1) (U ω) * brInc hT (l + 1) (U ω)
  have hck : 0 ≤ ck := by positivity
  have hcl : 0 ≤ cl := by positivity
  have hpt := br_point_ae hT ht1 U hS hν hs k l
  -- integrability
  have ixk : Integrable xk μ := (integrable_cre (integrable_brLin_centered hT U hUi _)).const_mul _
  have ixl : Integrable xl μ := (integrable_cre (integrable_brLin_centered hT U hUi _)).const_mul _
  have exk : ∫ ω, xk ω ∂μ = 0 := by
    simp only [xk]
    rw [integral_const_mul, integral_cre (integrable_brLin_centered hT U hUi _),
      integral_brLin_centered hT U hUi, Complex.zero_re, mul_zero]
  have exl : ∫ ω, xl ω ∂μ = 0 := by
    simp only [xl]
    rw [integral_const_mul, integral_cre (integrable_brLin_centered hT U hUi _),
      integral_brLin_centered hT U hUi, Complex.zero_re, mul_zero]
  obtain ⟨ixx, hxx⟩ := br_xx hT ht1 U hUH hp f r σ σ' hcov (k := k + 1) (l := l + 1)
    (by omega) (by omega)
  obtain ⟨ikk, hkk⟩ := br_sq_le hT ht1 U hUH hp f r σ σ' hcov (k := k + 1) (by omega)
  obtain ⟨ill, hll⟩ := br_sq_le hT ht1 U hUH hp f r σ σ' hcov (k := l + 1) (by omega)
  have iD : Integrable D μ := by
    have hm : Measurable D :=
      ((continuous_brInc hT (k + 1)).measurable.comp hUm).mul
        ((continuous_brInc hT (l + 1)).measurable.comp hUm)
    refine Integrable.of_bound hm.aestronglyMeasurable ((2 * W) * (2 * W)) ?_
    filter_upwards [hS] with ω hω
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_brInc_le hT ht1 _ hω) (abs_brInc_le hT ht1 _ hω) (abs_nonneg _)
      (by positivity)
  set rem : Ω → ℝ := fun ω => D ω - xk ω * xl ω - xk ω * bl - bk * xl ω
  have irem : Integrable rem μ := ((iD.sub ixx).sub (ixk.mul_const _)).sub (ixl.const_mul _)
  set rhs : Ω → ℝ := fun ω => 2 * cl / s * xk ω ^ 2 + 2 * ck / s * xl ω ^ 2 + A3 * h ω ^ 2 + A4
  have ikk' : Integrable (fun ω => xk ω ^ 2) μ := ikk
  have ill' : Integrable (fun ω => xl ω ^ 2) μ := ill
  have hh' : Integrable (fun ω => h ω ^ 2) μ := hh
  have i1 : Integrable (fun ω => 2 * cl / s * xk ω ^ 2) μ := ikk'.const_mul _
  have i2 : Integrable (fun ω => 2 * ck / s * xl ω ^ 2) μ := ill'.const_mul _
  have i3 : Integrable (fun ω => A3 * h ω ^ 2) μ := hh'.const_mul _
  have i12 : Integrable (fun ω => 2 * cl / s * xk ω ^ 2 + 2 * ck / s * xl ω ^ 2) μ := i1.add i2
  have i123 : Integrable (fun ω => 2 * cl / s * xk ω ^ 2 + 2 * ck / s * xl ω ^ 2 +
      A3 * h ω ^ 2) μ := i12.add i3
  have irhs : Integrable rhs μ := i123.add (integrable_const _)
  have hrem : |∫ ω, rem ω ∂μ| ≤ ∫ ω, rhs ω ∂μ :=
    (abs_integral_le_integral_abs).trans (integral_mono_ae irem.abs irhs hpt)
  have erhs : ∫ ω, rhs ω ∂μ = 2 * cl / s * ∫ ω, xk ω ^ 2 ∂μ + 2 * ck / s * ∫ ω, xl ω ^ 2 ∂μ +
      A3 * ∫ ω, h ω ^ 2 ∂μ + A4 := by
    simp only [rhs]
    rw [integral_add i123 (integrable_const _), integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
    simp
  have eD : ∫ ω, D ω ∂μ = ∫ ω, rem ω ∂μ + ∫ ω, xk ω * xl ω ∂μ := by
    have e : ∀ ω, D ω = rem ω + xk ω * xl ω + xk ω * bl + bk * xl ω := fun ω => by
      simp only [rem]; ring
    have ixx' : Integrable (fun ω => xk ω * xl ω) μ := ixx
    have j1 : Integrable (fun ω => rem ω + xk ω * xl ω) μ := irem.add ixx'
    have j2 : Integrable (fun ω => xk ω * bl) μ := ixk.mul_const _
    have j3 : Integrable (fun ω => rem ω + xk ω * xl ω + xk ω * bl) μ := j1.add j2
    have j4 : Integrable (fun ω => bk * xl ω) μ := ixl.const_mul _
    have ek : ∫ ω, xk ω * bl ∂μ = 0 := by rw [integral_mul_const, exk, zero_mul]
    have el : ∫ ω, bk * xl ω ∂μ = 0 := by rw [integral_const_mul, exl, mul_zero]
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_add j3 j4,
      integral_add j1 j2, integral_add irem ixx', ek, el]
    ring
  have hA3 : 0 ≤ A3 := by positivity
  have hb1 : 2 * cl / s * ∫ ω, xk ω ^ 2 ∂μ ≤ 2 * cl / s * (((k + 1 : ℕ) : ℝ) ^ 2 *
      (2 * |r| * T.trace.re + ((‖σ‖ + ‖σ'‖) * hsSandwich T f ^ 2 + ε * T.trace.re ^ 2))) :=
    mul_le_mul_of_nonneg_left hkk (by positivity)
  have hb2 : 2 * ck / s * ∫ ω, xl ω ^ 2 ∂μ ≤ 2 * ck / s * (((l + 1 : ℕ) : ℝ) ^ 2 *
      (2 * |r| * T.trace.re + ((‖σ‖ + ‖σ'‖) * hsSandwich T f ^ 2 + ε * T.trace.re ^ 2))) :=
    mul_le_mul_of_nonneg_left hll (by positivity)
  have hb3 : A3 * ∫ ω, h ω ^ 2 ∂μ ≤ A3 * H4 := mul_le_mul_of_nonneg_left hH4 hA3
  have e2 : ∫ ω, brInc hT (k + 1) (U ω) * brInc hT (l + 1) (U ω) ∂μ -
      ((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ) *
        (2 * r * ∑ i, ts_lam hT i ^ (k + 1 + (l + 1)) * (1 - ts_lam hT i)) =
      ∫ ω, rem ω ∂μ + (∫ ω, xk ω * xl ω ∂μ - ((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ) *
        (2 * r * ∑ i, ts_lam hT i ^ (k + 1 + (l + 1)) * (1 - ts_lam hT i))) := by
    rw [show (∫ ω, brInc hT (k + 1) (U ω) * brInc hT (l + 1) (U ω) ∂μ) = ∫ ω, D ω ∂μ from rfl, eD]
    ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  have hxx' : |∫ ω, xk ω * xl ω ∂μ - ((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ) *
      (2 * r * ∑ i, ts_lam hT i ^ (k + 1 + (l + 1)) * (1 - ts_lam hT i))| ≤
      ((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ) *
        ((‖σ‖ + ‖σ'‖) * hsSandwich T f ^ 2 + ε * T.trace.re ^ 2) := hxx
  linarith

end BlockBand.Transmission.Generator
