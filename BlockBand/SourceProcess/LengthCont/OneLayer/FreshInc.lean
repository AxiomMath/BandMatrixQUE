module

public import BlockBand.SourceProcess.LengthCont.OneLayer.FreshSize
public import BlockBand.SourceProcess.LengthCont.OneLayer.Increment
public import BlockBand.SourceProcess.FullSource.MomentStep
public import BlockBand.Transmission.PassiveCovariance.ResolventBound
public import BlockBand.SourceProcess.RawTag.StepBound

/-!
# Fresh size of the one-layer increment at a deterministic state

Abstract fresh matrix `Δ` on a probability space `(F, ρ)` with integrable entries,
`‖EΔ‖ ≤ m₀` and `‖u*(Δ - EΔ)v‖_{L⁴} ≤ s₀‖u‖‖v‖` (`DeltaHyp`). Every bilinear form
`u*Δv` has fresh size `(m₀‖u‖‖v‖, s₀‖u‖‖v‖)` (`lin_size`) and `L⁴` norm `≤ (m₀+s₀)‖u‖‖v‖`.
For deterministic frames of norm `≤ N` and `H = 1 + hsA ℝ + hsB ℝ`, the increment
`incTerm r` has fresh size `(K(m₀ + t²)N²H, K(s₀ + t²)N²H)`, `t = m₀ + s₀`,
`K = 4 + 2/|z̄ - z|` (`incTerm_size`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- `Σ_{x,y}|ℝ_{(0,x),(1,y)}|²`. -/
def hsA (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  ∑ x : Fin W, ∑ y : Fin W, ‖R (0, x) (1, y)‖ ^ 2

/-- `Σ_{x,y}|ℝ_{(1,y),(0,x)}|²`. -/
def hsB (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  ∑ x : Fin W, ∑ y : Fin W, ‖R (1, y) (0, x)‖ ^ 2

/-- `Σ_y d_y ℝ_{(0,·),(1,y)}`. -/
def vL (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (d : Fin W → ℂ) : Fin W → ℂ :=
  fun x => ∑ y, d y * R (0, x) (1, y)

/-- `Σ_y e_y conj ℝ_{(1,y),(0,·)}`. -/
def uR (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (e : Fin W → ℂ) : Fin W → ℂ :=
  fun x => ∑ y, e y * star (R (1, y) (0, x))

theorem hsA_nonneg (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : 0 ≤ hsA R := by
  unfold hsA; positivity

theorem hsB_nonneg (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : 0 ≤ hsB R := by
  unfold hsB; positivity

theorem vecNorm_sq (v : Fin W → ℂ) : vecNorm v ^ 2 = ∑ x, ‖v x‖ ^ 2 := by
  rw [vecNorm, Real.sq_sqrt (by positivity)]

theorem vecNorm_star (v : Fin W → ℂ) : vecNorm (star v) = vecNorm v := by
  simp [vecNorm]

/-- Cauchy–Schwarz over rows. -/
theorem vecNorm_rows_le (d : Fin W → ℂ) (M : Fin W → Fin W → ℂ) :
    vecNorm (fun x => ∑ y, d y * M x y) ≤ vecNorm d * Real.sqrt (∑ x, ∑ y, ‖M x y‖ ^ 2) := by
  have h : ∀ x, ‖∑ y, d y * M x y‖ ^ 2 ≤ vecNorm d ^ 2 * ∑ y, ‖M x y‖ ^ 2 := by
    intro x
    have e : ∑ y, d y * M x y = star (star d) ⬝ᵥ (M x) := by
      simp [dotProduct]
    have := norm_star_dotProduct_le (star d) (M x)
    rw [← e, vecNorm_star] at this
    calc ‖∑ y, d y * M x y‖ ^ 2 ≤ (vecNorm d * vecNorm (M x)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = vecNorm d ^ 2 * ∑ y, ‖M x y‖ ^ 2 := by simp only [mul_pow, vecNorm_sq]
  rw [vecNorm, ← Real.sqrt_sq (vecNorm_nonneg d), ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => h x

theorem vecNorm_vL_le (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (d : Fin W → ℂ) :
    vecNorm (vL R d) ≤ vecNorm d * Real.sqrt (hsA R) :=
  vecNorm_rows_le d fun x y => R (0, x) (1, y)

theorem vecNorm_uR_le (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (e : Fin W → ℂ) :
    vecNorm (uR R e) ≤ vecNorm e * Real.sqrt (hsB R) := by
  have h := vecNorm_rows_le e fun x y => star (R (1, y) (0, x))
  simp only [norm_star] at h
  rw [hsB]; exact h

theorem sum_col_sq (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ y, vecNorm (fun x => R (0, x) (1, y)) ^ 2 = hsA R := by
  simp only [vecNorm_sq, hsA]; rw [Finset.sum_comm]

theorem sum_row_sq (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ y, vecNorm (fun x => star (R (1, y) (0, x))) ^ 2 = hsB R := by
  simp only [vecNorm_sq, norm_star, hsB]; rw [Finset.sum_comm]

/-!
## Linear rewriting of the Gram increments
-/

theorem bilinear_sum_right (a : Fin W → ℂ) (D : Matrix (Fin W) (Fin W) ℂ) (c : Fin W → ℂ)
    (r : Fin W → Fin W → ℂ) :
    ∑ y, c y * bilinear a D (r y) = bilinear a D (fun x => ∑ y, c y * r y x) := by
  simp only [bilinear, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem bilinear_sum_left (s : Fin W → Fin W → ℂ) (D : Matrix (Fin W) (Fin W) ℂ)
    (c e : Fin W → ℂ) :
    ∑ y, star (e y) * bilinear (s y) D c = bilinear (fun x => ∑ y, e y * s y x) D c := by
  simp only [bilinear, dotProduct, Pi.star_apply, star_sum, star_mul', Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem gram_shiftL_left (D : Matrix (Fin W) (Fin W) ℂ)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (a d : Fin W → ℂ) :
    gramOf d (shiftL D R a) = star (bilinear a D (vL R d)) := by
  have h := bilinear_sum_right a D d (fun y x => R (0, x) (1, y))
  unfold vL
  rw [← h, star_sum]
  simp only [gramOf, shiftL, star_mul']

theorem gram_shiftL_right (D : Matrix (Fin W) (Fin W) ℂ)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (a d : Fin W → ℂ) :
    gramOf (shiftL D R a) d = bilinear a D (vL R d) := by
  have h := bilinear_sum_right a D d (fun y x => R (0, x) (1, y))
  unfold vL
  rw [← h]
  simp only [gramOf, shiftL, star_star]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem gram_shiftR_left (D : Matrix (Fin W) (Fin W) ℂ)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (c e : Fin W → ℂ) :
    gramOf e (shiftR D R c) = bilinear (uR R e) D c := by
  have h := bilinear_sum_left (fun y x => star (R (1, y) (0, x))) D c e
  unfold uR
  rw [← h]
  rfl

theorem gram_shiftR_right (D : Matrix (Fin W) (Fin W) ℂ)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (c e : Fin W → ℂ) :
    gramOf (shiftR D R c) e = star (bilinear (uR R e) D c) := by
  rw [← gram_shiftR_left, gramOf, gramOf, star_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [star_mul', star_star, mul_comm]

/-!
## The abstract fresh matrix
-/

variable {F : Type*} [MeasurableSpace F] {ρ : Measure F} [IsProbabilityMeasure ρ]

/-- The one-layer hypotheses on a fresh matrix. -/
structure DeltaHyp (ρ : Measure F) (Δ : F → Matrix (Fin W) (Fin W) ℂ) (m₀ s₀ : ℝ) : Prop where
  meas : Measurable Δ
  int : ∀ x y, Integrable (fun f => Δ f x y) ρ
  m_nonneg : 0 ≤ m₀
  s_nonneg : 0 ≤ s₀
  mean : ‖matrixExpect ρ Δ‖ ≤ m₀
  dev : ∀ u v : Fin W → ℂ, eLpNorm (fun f => bilinear u (Δ f - matrixExpect ρ Δ) v) 4 ρ ≤
    ENNReal.ofReal (s₀ * vecNorm u * vecNorm v)

variable {Δ : F → Matrix (Fin W) (Fin W) ℂ} {m₀ s₀ : ℝ}

omit [IsProbabilityMeasure ρ] in
theorem DeltaHyp.integrable_bilinear (h : DeltaHyp ρ Δ m₀ s₀) (u v : Fin W → ℂ) :
    Integrable (fun f => bilinear u (Δ f) v) ρ := by
  simp only [bilinear, dotProduct, mulVec, Pi.star_apply]
  exact integrable_finsetSum _ fun x _ => (integrable_finsetSum _ fun y _ =>
    (h.int x y).mul_const _).const_mul _

omit [IsProbabilityMeasure ρ] in
theorem DeltaHyp.meas_bilinear (h : DeltaHyp ρ Δ m₀ s₀) (u v : Fin W → ℂ) :
    AEStronglyMeasurable (fun f => bilinear u (Δ f) v) ρ :=
  (BlockBand.SourceProcess.RawTag.measurable_bilinear_jt measurable_const h.meas
    measurable_const).aestronglyMeasurable

theorem DeltaHyp.lin_size (h : DeltaHyp ρ Δ m₀ s₀) (u v : Fin W → ℂ) :
    FreshSize ρ (fun f => bilinear u (Δ f) v) (m₀ * vecNorm u * vecNorm v)
      (s₀ * vecNorm u * vecNorm v) := by
  have hu := vecNorm_nonneg u
  have hv := vecNorm_nonneg v
  have hI : ∫ f, bilinear u (Δ f) v ∂ρ = bilinear u (matrixExpect ρ Δ) v :=
    BlockBand.SourceProcess.FullSource.integral_bilinear Δ h.int u v
  refine ⟨h.meas_bilinear u v, h.integrable_bilinear u v, by have := h.m_nonneg; positivity,
    by have := h.s_nonneg; positivity, ?_, ?_⟩
  · rw [hI]
    refine (norm_bilinear_le u _ v).trans ?_
    have := h.mean
    calc vecNorm u * ‖matrixExpect ρ Δ‖ * vecNorm v ≤ vecNorm u * m₀ * vecNorm v := by gcongr
      _ = m₀ * vecNorm u * vecNorm v := by ring
  · rw [hI]
    have e : (fun f => bilinear u (Δ f) v - bilinear u (matrixExpect ρ Δ) v) =
        fun f => bilinear u (Δ f - matrixExpect ρ Δ) v := by
      funext f; rw [bilinear_sub]
    rw [e]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans (h.dev u v)

theorem DeltaHyp.lin_L4 (h : DeltaHyp ρ Δ m₀ s₀) (u v : Fin W → ℂ) :
    eLpNorm (fun f => bilinear u (Δ f) v) 4 ρ ≤
      ENNReal.ofReal ((m₀ + s₀) * vecNorm u * vecNorm v) := by
  have hu := vecNorm_nonneg u
  have hv := vecNorm_nonneg v
  have e : (fun f => bilinear u (Δ f) v) = (fun f => bilinear u (Δ f - matrixExpect ρ Δ) v) +
      fun _ => bilinear u (matrixExpect ρ Δ) v := by
    funext f; simp only [Pi.add_apply, bilinear_sub]; ring
  rw [e]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero ρ), measure_univ,
    ENNReal.one_rpow, mul_one, ← ofReal_norm]
  have hb : ‖bilinear u (matrixExpect ρ Δ) v‖ ≤ m₀ * vecNorm u * vecNorm v := by
    refine (norm_bilinear_le u _ v).trans ?_
    have := h.mean
    calc vecNorm u * ‖matrixExpect ρ Δ‖ * vecNorm v ≤ vecNorm u * m₀ * vecNorm v := by gcongr
      _ = m₀ * vecNorm u * vecNorm v := by ring
  calc eLpNorm (fun f => bilinear u (Δ f - matrixExpect ρ Δ) v) 4 ρ +
        ENNReal.ofReal ‖bilinear u (matrixExpect ρ Δ) v‖
      ≤ ENNReal.ofReal (s₀ * vecNorm u * vecNorm v) +
          ENNReal.ofReal (m₀ * vecNorm u * vecNorm v) :=
        add_le_add (h.dev u v) (ENNReal.ofReal_le_ofReal hb)
    _ = ENNReal.ofReal ((m₀ + s₀) * vecNorm u * vecNorm v) := by
        have := h.m_nonneg; have := h.s_nonneg
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

omit [IsProbabilityMeasure ρ] in
/-- `star` of a bilinear form has the same `L⁴` bound. -/
theorem eLpNorm_star_fun (X : F → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun f => star (X f)) p ρ = eLpNorm X p ρ := eLpNorm_star (f := X)

/-- The quadratic Gram term `Σ_y conj(A_y) B_y`. -/
theorem quad_size (A B : Fin W → F → ℂ) (hAm : ∀ y, AEStronglyMeasurable (A y) ρ)
    (hBm : ∀ y, AEStronglyMeasurable (B y) ρ) (a b : Fin W → ℝ) (ha : ∀ y, 0 ≤ a y)
    (hb : ∀ y, 0 ≤ b y) (hA4 : ∀ y, eLpNorm (A y) 4 ρ ≤ ENNReal.ofReal (a y))
    (hB4 : ∀ y, eLpNorm (B y) 4 ρ ≤ ENNReal.ofReal (b y)) {c : ℝ} (hc : 0 ≤ c)
    (hsum : ∑ y, a y * b y ≤ c) :
    FreshSize ρ (fun f => ∑ y, star (A y f) * B y f) c (2 * c) := by
  refine FreshSize.of_L2 hc ?_ ((eLpNorm_sum_star_mul_le A B hAm hBm a b ha hb hA4 hB4).trans
    (ENNReal.ofReal_le_ofReal hsum))
  exact Finset.aestronglyMeasurable_fun_sum _ fun y _ => (hAm y).star.mul (hBm y)

end BlockBand.SourceProcess.LengthCont.OneLayer
