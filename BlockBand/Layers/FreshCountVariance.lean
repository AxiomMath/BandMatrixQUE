module

public import BlockBand.Layers.FreshCountDerivative
public import BlockBand.Layers.ResolventRowSum

/-!
# The fresh count variance bound: the variance of the fresh resolvent traces

For `t ≥ 1/2` the Gaussian counting bound gives `E Tr|H_t⁻¹|² ≤ CW/y_t`, and the Gaussian
Poincaré inequality, with `‖H_t⁻¹KH_t⁻¹‖_HS ≤ ‖K‖ y_t⁻¹ ‖H_t⁻¹‖_HS`, yields
`E|g_t - E g_t|² ≤ C/(W²y_t³)`, also with a bounded deterministic matrix insertion. For `t ≤ 1/2`
the deterministic height is bounded below.

Law: `A = gueOfCoords W τ r`, `r` standard Gaussian, `τ = c/W`, `c = 1 - 2b`; `H_t` is
`fcHeatMatrix`. Norms: `ℓ²` operator norm, Hilbert–Schmidt `fcmHS`.

* `fcm_hs_gue`: `Σᵢ |Tr(XΛᵢ)|² = τ ‖X‖²_HS` for the GUE coordinate matrices; `fcm_hs_mul_le`;
  `fcm_ward`: `‖(X + iy)⁻¹‖²_HS = -Im Tr(X + iy)⁻¹/y`.
* `fcm_poisson_count_heat` (from `ConditionalBlockGUECount`, through `fc_ballCount_le`):
  `E Σ_j y/(μ_j(t)² + y²) ≤ (16C/√(tc) + 1)W`, by dyadic domination of the Poisson kernel
  (`fcm_poisson_le_dyadic`) and `-Im Tr(M + iy)⁻¹ = Σ_j y/(λ_j² + y²)`.
* `fcm_poincare`: `GaussianLpGradient` at `p = 2`, in integral form.
* `fcm_heat_variance`: for `t ∈ [0,1]` and deterministic `K`,
  `E|⟨K H_t⁻¹⟩ - E⟨K H_t⁻¹⟩|² ≤ Cp(16C√2/√c + 1 + 2/γ) ‖K‖²/(W² y_t³)`, `γ = c(-Im a)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Complex Filter
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (spectralSum gaussianProduct weightedGradientNorm
  GaussianLpGradient ConditionalBlockGUECount)
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator

/-!
## 1. Hilbert–Schmidt norms
-/

section HS

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The squared Hilbert–Schmidt norm `Σ_{ab} |X_ab|²`. -/
def fcmHS (X : Matrix n n ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖ ^ 2

omit [DecidableEq n] in
theorem fcmHS_nonneg (X : Matrix n n ℂ) : 0 ≤ fcmHS X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `‖XY‖²_HS ≤ ‖X‖² ‖Y‖²_HS`. -/
theorem fcm_hs_mul_le (X Y : Matrix n n ℂ) : fcmHS (X * Y) ≤ ‖X‖ ^ 2 * fcmHS Y := by
  unfold fcmHS
  rw [Finset.sum_comm, Finset.sum_comm (f := fun a b => ‖Y a b‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  set v : n → ℂ := fun a => Y a b
  have hcol : ∀ a, (X * Y) a b = (X *ᵥ v) a := fun a => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, v]
  have h := norm_toLp_mulVec_le X v
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simp only [hcol]
  exact h2

omit [DecidableEq n] in
theorem fcm_hs_eq_trace (R : Matrix n n ℂ) : fcmHS R = (R * Rᴴ).trace.re := by
  unfold fcmHS
  rw [trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [diag_apply, mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_re]

/-- **Ward identity**: `‖(X + iy)⁻¹‖²_HS = -Im Tr (X + iy)⁻¹ / y` for Hermitian `X`, `y > 0`. -/
theorem fcm_ward {X : Matrix n n ℂ} (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y) :
    fcmHS (X + ((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹ =
      -((X + ((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹).trace.im / y := by
  have hz : (0 : ℝ) < ((y : ℂ) * I).im := by simpa using hy
  have h := resolvent_sub_conjTranspose (-X) hX.neg ((y : ℂ) * I) hz
  have he : ((y : ℂ) * I) • (1 : Matrix n n ℂ) - -X = X + ((y : ℂ) * I) • (1 : Matrix n n ℂ) := by
    abel
  rw [he] at h
  set R := (X + ((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹
  have h2 := congrArg (fun M => M.trace.im) h
  simp only [trace_sub, trace_smul, smul_eq_mul, Complex.sub_im, trace_conjTranspose,
    Complex.star_def, Complex.conj_im] at h2
  rw [fcm_hs_eq_trace]
  have him : ((y : ℂ) * I).im = y := by simp
  rw [him] at h2
  have e : (-(2 * y : ℝ) * I * (R * Rᴴ).trace).im = -(2 * y) * (R * Rᴴ).trace.re := by
    simp [Complex.mul_im]
  push_cast at e
  rw [e] at h2
  field_simp
  linarith

end HS

/-!
## 2. The Gaussian gradient of a GUE resolvent trace
-/

section GueHS

theorem fcm_trace_mul_single {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (α β : n) (c : ℂ) : (X * single α β c).trace = X β α * c := by
  simp only [trace, diag_apply, mul_apply, single_apply]
  rw [Finset.sum_comm]
  simp only [ite_and]
  rw [Finset.sum_eq_single α (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

theorem fcm_parallelogram (u v : ℂ) : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im]
  ring

theorem fcm_norm_kappa_sq (t : ℝ≥0) : ‖fcdKappa t‖ ^ 2 = (t : ℝ) / 4 := by
  have h1 : Real.sqrt ((t : ℝ) / 2) ^ 2 = (t : ℝ) / 2 := Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [fcdKappa, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, h1, h2]
  ring

/-- **The GUE coordinate traces**: `Σᵢ |Tr(X Λᵢ)|² = t ‖X‖²_HS`. -/
theorem fcm_hs_gue (W : ℕ) (t : ℝ≥0) (X : Matrix (Fin W) (Fin W) ℂ) :
    ∑ i : GaussCoord W, ‖(X * gueOfCoords W t (Pi.single i 1)).trace‖ ^ 2 =
      (t : ℝ) * fcmHS X := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, fcd_lin0, fcd_lin1, Matrix.mul_smul, trace_smul, Matrix.mul_add,
    trace_add, fcm_trace_mul_single, smul_eq_mul, norm_mul]
  have hk := fcm_norm_kappa_sq t
  have e : ∀ α β : Fin W, (‖fcdKappa t‖ * ‖X β α * 1 + X α β * 1‖) ^ 2 +
      (‖fcdKappa t‖ * ‖X β α * I + X α β * -I‖) ^ 2 =
      (t : ℝ) / 2 * (‖X β α‖ ^ 2 + ‖X α β‖ ^ 2) := by
    intro α β
    have h1 : X β α * I + X α β * -I = I * (X β α - X α β) := by ring
    rw [mul_pow, mul_pow, h1, norm_mul, norm_I, one_mul, mul_one, mul_one, ← mul_add,
      fcm_parallelogram, hk]
    ring
  simp only [e]
  unfold fcmHS
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  have : ∑ x : Fin W, ∑ y : Fin W, ‖X y x‖ ^ 2 = ∑ x : Fin W, ∑ y : Fin W, ‖X x y‖ ^ 2 :=
    Finset.sum_comm
  rw [this]
  ring

end GueHS

/-!
## 3. The Gaussian counting bound `E Tr|H⁻¹|² ≤ CW/y`

`-Im Tr(M + iy)⁻¹ = Σ_j y/(λ_j² + y²)` (`fcm_neg_im_trace`); the Poisson kernel is dominated
by dyadic interval indicators (`fcm_poisson_le_dyadic`), whose expectations are bounded by the
PSSS density bound (`fc_ballCount_le`).
-/

section Count

variable {n : Type} [Fintype n] [DecidableEq n]

theorem fcm_trace_inv {M : Matrix n n ℂ} (hM : M.IsHermitian) {y : ℝ} (hy : 0 < y) :
    ((M + ((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹).trace =
      ∑ k, ((hM.eigenvalues k : ℂ) + (y : ℂ) * I)⁻¹ := by
  have h1 := fcd_trace_mul_inv hM 1 hy
  simp only [Complex.ofReal_one, one_smul, one_mul] at h1
  set R := (M + ((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹
  have hu := (fcd_herm_inv hM hy).1
  have hMR : M * R = 1 - ((y : ℂ) * I) • R := by
    have : (M + ((y : ℂ) * I) • (1 : Matrix n n ℂ)) * R = 1 := mul_nonsing_inv _ hu
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at this
    rw [← this]; abel
  rw [hMR, trace_sub, trace_one, trace_smul, smul_eq_mul] at h1
  have hc : (y : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne') I_ne_zero
  have hk : ∀ k, (hM.eigenvalues k : ℂ) + (y : ℂ) * I ≠ 0 := fun k => by
    have := fcd_eig_ne_zero (hM.eigenvalues k) 1 hy
    simpa using this
  apply mul_left_cancel₀ hc
  have e : ∑ k, (hM.eigenvalues k : ℂ) / ((hM.eigenvalues k : ℂ) + (y : ℂ) * I) =
      (Fintype.card n : ℂ) - (y : ℂ) * I * ∑ k, ((hM.eigenvalues k : ℂ) + (y : ℂ) * I)⁻¹ := by
    have e1 : ∀ k, (hM.eigenvalues k : ℂ) / ((hM.eigenvalues k : ℂ) + (y : ℂ) * I) =
        1 - (y : ℂ) * I * ((hM.eigenvalues k : ℂ) + (y : ℂ) * I)⁻¹ := fun k => by
      field_simp [hk k]
      ring
    rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, ← Finset.mul_sum, nsmul_eq_mul, mul_one]
  rw [e] at h1
  linear_combination -h1

/-- The Poisson kernel `y / (x² + y²)`. -/
def fcmPoisson (y x : ℝ) : ℝ := y / (x ^ 2 + y ^ 2)

omit [Fintype n] [DecidableEq n] in
theorem fcm_neg_im_inv (x : ℝ) {y : ℝ} : -(((x : ℂ) + (y : ℂ) * I)⁻¹).im = fcmPoisson y x := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp [fcmPoisson]
  ring

theorem fcm_neg_im_trace {M : Matrix n n ℂ} (hM : M.IsHermitian) {y : ℝ} (hy : 0 < y) :
    -((M + ((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹).trace.im = spectralSum M (fcmPoisson y) := by
  rw [fcm_trace_inv hM hy, fc_spectralSum_eq hM, Complex.im_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => fcm_neg_im_inv _

omit [Fintype n] [DecidableEq n] in
theorem fcm_poisson_nonneg {y : ℝ} (hy : 0 < y) (x : ℝ) : 0 ≤ fcmPoisson y x := by
  unfold fcmPoisson; positivity

omit [Fintype n] [DecidableEq n] in
theorem fcm_poisson_le {y : ℝ} (hy : 0 < y) (x : ℝ) : fcmPoisson y x ≤ y⁻¹ := by
  unfold fcmPoisson
  rw [div_le_iff₀ (by positivity)]
  have : y⁻¹ * y ^ 2 = y := by field_simp
  nlinarith [sq_nonneg x, inv_pos.mpr hy]

omit [Fintype n] [DecidableEq n] in
theorem fcm_poisson_le_far {y : ℝ} (hy : 0 < y) {x r : ℝ} (hr : 0 < r) (hx : r ≤ |x|) :
    fcmPoisson y x ≤ y / r ^ 2 := by
  unfold fcmPoisson
  have : r ^ 2 ≤ x ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ hr.le hx 2
  exact div_le_div_of_nonneg_left hy.le (by positivity) (by nlinarith [sq_nonneg y])

omit [Fintype n] [DecidableEq n] in
/-- **Dyadic domination of the Poisson kernel**: for `y > 0` and every `L`,
`y/(x²+y²) ≤ Σ_{m ≤ L} 4^{1-m} y⁻¹ 1_{|x| ≤ 2^m y} + 4^{-L} y⁻¹`. -/
theorem fcm_poisson_le_dyadic {y : ℝ} (hy : 0 < y) (L : ℕ) (x : ℝ) :
    fcmPoisson y x ≤ (∑ m ∈ Finset.range (L + 1), 4 / (4 ^ m * y) * fcBall (2 ^ m * y) x) +
      1 / (4 ^ L * y) := by
  have hterm : ∀ m ∈ Finset.range (L + 1), 0 ≤ 4 / (4 ^ m * y) * fcBall (2 ^ m * y) x := by
    intro m _
    unfold fcBall
    split_ifs <;> positivity
  have hS := Finset.sum_nonneg hterm
  have h4 : ∀ m : ℕ, (2 : ℝ) ^ m * (2 : ℝ) ^ m = 4 ^ m := fun m => by
    rw [← mul_pow]; norm_num
  by_cases hfar : 2 ^ L * y < |x|
  · have h1 := fcm_poisson_le_far hy (by positivity) hfar.le
    have h2 : y / (2 ^ L * y) ^ 2 = 1 / (4 ^ L * y) := by
      rw [← h4 L]; field_simp
    have : 0 ≤ 1 / (4 ^ L * y) := by positivity
    linarith
  · replace hfar := not_lt.mp hfar
    have hex : ∃ m, |x| ≤ 2 ^ m * y := ⟨L, hfar⟩
    classical
    set m₀ := Nat.find hex with hm₀
    have hm₀x : |x| ≤ 2 ^ m₀ * y := Nat.find_spec hex
    have hm₀L : m₀ ≤ L := Nat.find_min' hex hfar
    have hmem : m₀ ∈ Finset.range (L + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm₀L)
    have hsingle := Finset.single_le_sum hterm hmem
    have hball : fcBall (2 ^ m₀ * y) x = 1 := by unfold fcBall; simp only [hm₀x, ↓reduceIte]
    rw [hball, mul_one] at hsingle
    have htail : 0 ≤ 1 / (4 ^ L * y) := by positivity
    rcases Nat.eq_zero_or_pos m₀ with h0 | hpos
    · have h1 := fcm_poisson_le hy x
      rw [h0, pow_zero, one_mul] at hsingle
      have : y⁻¹ ≤ 4 / y := by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right (by norm_num) hy.le
      linarith
    · have hlt : ¬ |x| ≤ 2 ^ (m₀ - 1) * y := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      replace hlt := (not_le.mp hlt).le
      have h1 := fcm_poisson_le_far hy (by positivity) hlt
      have hpow : (4 : ℝ) ^ m₀ = 4 * 4 ^ (m₀ - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h2 : y / (2 ^ (m₀ - 1) * y) ^ 2 = 4 / (4 ^ m₀ * y) := by
        rw [hpow, ← h4 (m₀ - 1)]; field_simp
      linarith

/-- **The Gaussian counting bound** (PSSS density, one block): for `W ≥ 1`, `c' > 0`, Hermitian
`F'`, `y > 0`, under `GUE_W(c'/W)`: `E Σ_j y/(λ_j(A - F')² + y²) ≤ (16 C/√c' + 1) W`. -/
theorem fcm_poisson_count (hcount : ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ), 0 < W → ∀ c' : ℝ, 0 < c' →
      ∀ F' : Matrix (Fin W) (Fin W) ℂ, F'.IsHermitian → ∀ y : ℝ, 0 < y →
      (∫ A, spectralSum (fcShift 0 F' A) (fcmPoisson y)
          ∂gueMeasure (Fin W) (Real.toNNReal (c' / W))) ≤ (16 * C / Real.sqrt c' + 1) * W := by
  obtain ⟨C, hC, hball⟩ := fc_ballCount_le hcount
  refine ⟨C, hC, fun W hW c' hc' F' hF' y hy => ?_⟩
  set μ := gueMeasure (Fin W) (Real.toNNReal (c' / W))
  have : IsProbabilityMeasure μ := isProbabilityMeasure_gueMeasure W _
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (1 / y) (by norm_num : (1 : ℝ) < 4)
  have hLy : 1 / (4 ^ L * y) ≤ 1 := by
    rw [div_le_one (by positivity)]
    rw [div_lt_iff₀ hy] at hL
    linarith
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hmeas : ∀ f : ℝ → ℝ, Measurable f → Measurable fun A => spectralSum (fcShift 0 F' A) f :=
    fun f hf => fc_measurable_spectralSum (measurable_fcShift 0 F')
      (fun A => fcShift_isHermitian 0 hF' A) hf
  have hint : ∀ f : ℝ → ℝ, Measurable f → ∀ B, (∀ x, |f x| ≤ B) →
      Integrable (fun A => spectralSum (fcShift 0 F' A) f) μ := fun f hf B hB =>
    Integrable.of_bound (hmeas f hf).aestronglyMeasurable (W * B)
      (Filter.Eventually.of_forall fun A => by
        have := fc_abs_spectralSum_le (fcShift_isHermitian 0 hF' A) hB
        rw [Fintype.card_fin] at this
        rwa [Real.norm_eq_abs])
  have hcP : Continuous (fcmPoisson y) := by
    unfold fcmPoisson
    exact continuous_const.div (by fun_prop) fun x => by positivity
  have hPabs : ∀ x, |fcmPoisson y x| ≤ y⁻¹ := fun x => by
    rw [abs_of_nonneg (fcm_poisson_nonneg hy x)]; exact fcm_poisson_le hy x
  -- pointwise domination
  set g : Matrix (Fin W) (Fin W) ℂ → ℝ := fun A =>
    (∑ m ∈ Finset.range (L + 1), 4 / (4 ^ m * y) * spectralSum (fcShift 0 F' A) (fcBall (2 ^ m * y)))
      + W with hg
  have hpt : ∀ A, spectralSum (fcShift 0 F' A) (fcmPoisson y) ≤ g A := by
    intro A
    have hH := fcShift_isHermitian 0 hF' A
    simp only [hg, fc_spectralSum_eq hH, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hk : ∀ k, fcmPoisson y (hH.eigenvalues k) ≤
        (∑ m ∈ Finset.range (L + 1), 4 / (4 ^ m * y) * fcBall (2 ^ m * y) (hH.eigenvalues k)) + 1 :=
      fun k => (fcm_poisson_le_dyadic hy L _).trans (by linarith)
    calc ∑ k, fcmPoisson y (hH.eigenvalues k)
        ≤ ∑ k, ((∑ m ∈ Finset.range (L + 1), 4 / (4 ^ m * y) * fcBall (2 ^ m * y)
            (hH.eigenvalues k)) + 1) := Finset.sum_le_sum fun k _ => hk k
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one]
  have hgi : Integrable g μ := by
    refine (integrable_finsetSum _ fun m _ => ?_).add (integrable_const _)
    exact (hint _ (fc_measurable_ball _) 1 (fc_abs_ball_le _)).const_mul _
  calc (∫ A, spectralSum (fcShift 0 F' A) (fcmPoisson y) ∂μ) ≤ ∫ A, g A ∂μ :=
        integral_mono (hint _ hcP.measurable _ hPabs) hgi hpt
    _ = (∑ m ∈ Finset.range (L + 1), 4 / (4 ^ m * y) *
          ∫ A, spectralSum (fcShift 0 F' A) (fcBall (2 ^ m * y)) ∂μ) + W := by
        rw [integral_add (integrable_finsetSum _ fun m _ =>
          (hint _ (fc_measurable_ball _) 1 (fc_abs_ball_le _)).const_mul _) (integrable_const _),
          integral_finsetSum _ fun m _ =>
            (hint _ (fc_measurable_ball _) 1 (fc_abs_ball_le _)).const_mul _,
          integral_const, probReal_univ, one_smul]
        simp only [integral_const_mul]
    _ ≤ (∑ m ∈ Finset.range (L + 1), 4 / (4 ^ m * y) *
          (C / Real.sqrt c' * W * (2 * (2 ^ m * y)))) + W := by
        gcongr with m _
        exact hball W hW c' hc' 0 F' hF' _ (by positivity)
    _ = 8 * C / Real.sqrt c' * W * (∑ m ∈ Finset.range (L + 1), (1 / (2 : ℝ)) ^ m) + W := by
        rw [Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        have h4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
        rw [h4, _root_.one_div_pow]
        field_simp
        ring
    _ ≤ 8 * C / Real.sqrt c' * W * 2 + W := by
        gcongr
        exact sum_geometric_two_le _
    _ = (16 * C / Real.sqrt c' + 1) * W := by ring

/-- GUE scaling: `gueOfCoords W (t x) = √t · gueOfCoords W x`. -/
theorem fcm_gue_scale (W : ℕ) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) (r : GaussCoord W → ℝ) :
    gueOfCoords W (Real.toNNReal (t * x)) r = (Real.sqrt t : ℂ) • gueOfCoords W (Real.toNNReal x) r := by
  ext a b
  simp only [gueOfCoords, gueSample, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Real.coe_toNNReal _ (mul_nonneg ht hx), Real.coe_toNNReal _ hx]
  rw [show t * x / 2 = t * (x / 2) by ring, Real.sqrt_mul ht]
  push_cast
  ring

/-- **The counting bound in Gaussian coordinates** along the heat path, `t > 0`:
`E Σ_j y/(μ_j(t)² + y²) ≤ (16C/√(tc) + 1) W`. -/
theorem fcm_poisson_count_heat (hcount : ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℝ), b < 1 / 2 → ∀ (E : ℝ) (W : ℕ), 0 < W →
      ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian → ∀ t : ℝ, 0 < t → ∀ y : ℝ, 0 < y →
      (∫ r, spectralSum (fcHeatHerm b E F t (gueOfCoords W (fcdTau b W) r)) (fcmPoisson y)
          ∂stdGaussCoordLaw (GaussCoord W)) ≤
        (16 * C / Real.sqrt (t * (1 - 2 * b)) + 1) * W := by
  obtain ⟨C, hC, h⟩ := fcm_poisson_count hcount
  refine ⟨C, hC, fun b hb E W hW F hF t ht y hy => ?_⟩
  have hc : 0 < 1 - 2 * b := by linarith
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set S : ℝ := E + (1 - t) * (1 - 2 * b) * (matchedA E).re
  set F' : Matrix (Fin W) (Fin W) ℂ := ((S : ℝ) : ℂ) • 1 + F with hF'
  have hF'h : F'.IsHermitian := (fcd_isHermitian_real_smul isHermitian_one _).add hF
  have hpt : ∀ r, fcHeatHerm b E F t (gueOfCoords W (fcdTau b W) r) =
      fcShift 0 F' (gueOfCoords W (Real.toNNReal (t * (1 - 2 * b) / W)) r) := by
    intro r
    rw [mul_div_assoc, fcm_gue_scale W ht.le (div_nonneg hc.le hW'.le)]
    unfold fcShift fcHeatHerm
    rw [hermPart_of_isHermitian (fcd_isHermitian_real_smul (gueOfCoords_isHermitian W _ r) _)]
    simp only [hF', Complex.ofReal_zero, zero_smul, sub_zero, fcdTau]
    abel
  simp only [hpt]
  rw [← fcd_integral_gue W _ (fun A => spectralSum (fcShift 0 F' A) (fcmPoisson y))]
  · exact h W hW (t * (1 - 2 * b)) (by positivity) F' hF'h y hy
  · refine (fc_measurable_spectralSum ((measurable_fcShift 0 F').comp (measurable_hermPart W))
      (fun A => fcShift_isHermitian 0 hF'h _) ?_).aestronglyMeasurable
    unfold fcmPoisson
    exact (continuous_const.div (by fun_prop) fun x => by positivity).measurable

end Count

/-!
## 4. Gaussian Poincaré in integral form and the variance bound
-/

section Variance

/-- `‖f‖_{L²} = √(∫ ‖f‖²)`. -/
theorem fcm_eLpNorm_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {E : Type*}
    [NormedAddCommGroup E] {f : Ω → E} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    exact Real.rpow_two _
  · norm_num

/-- **Gaussian Poincaré** (`GaussianLpGradient` at `p = 2`), integral form, for bounded `C¹`
functions with bounded weighted gradient. -/
theorem fcm_poincare (hgrad : GaussianLpGradient) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → ∀ B B' : ℝ, (∀ x, ‖f x‖ ≤ B) →
        (∀ x, weightedGradientNorm v f x ≤ B') →
        ∫ x, ‖f x - ∫ y, f y ∂gaussianProduct v‖ ^ 2 ∂gaussianProduct v ≤
          Cp * ∫ x, weightedGradientNorm v f x ^ 2 ∂gaussianProduct v := by
  obtain ⟨C, hC, h⟩ := hgrad
  refine ⟨2 * C ^ 2, by positivity, fun ι _ _ v f hf B B' hB hB' => ?_⟩
  set μ := gaussianProduct v
  have hfc := hf.continuous
  have hmf : MemLp f (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact MemLp.of_bound hfc.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have h1 := h 2 (by norm_num) ι v f hf hmf
  rw [ENNReal.ofReal_ofNat] at h1
  have hwc : Continuous (weightedGradientNorm v f) := by
    have hd := hf.continuous_fderiv one_ne_zero
    unfold weightedGradientNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
    exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
  have hm1 : MemLp (fun x => f x - ∫ y, f y ∂μ) 2 μ :=
    (MemLp.of_bound hfc.aestronglyMeasurable B (Filter.Eventually.of_forall hB)).sub
      (memLp_const _)
  have hm2 : MemLp (weightedGradientNorm v f) 2 μ :=
    MemLp.of_bound hwc.aestronglyMeasurable B' (Filter.Eventually.of_forall fun x => by
      have h0 : (0 : ℝ) ≤ weightedGradientNorm v f x := Real.sqrt_nonneg _
      rw [Real.norm_of_nonneg h0]
      exact hB' x)
  rw [fcm_eLpNorm_two hm1, fcm_eLpNorm_two hm2, ← ENNReal.ofReal_mul (by positivity)] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  set V1 := ∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ
  set V2 := ∫ x, ‖weightedGradientNorm v f x‖ ^ 2 ∂μ
  have hV1 : 0 ≤ V1 := integral_nonneg fun x => sq_nonneg _
  have hV2 : 0 ≤ V2 := integral_nonneg fun x => sq_nonneg _
  have e2 : V2 = ∫ x, weightedGradientNorm v f x ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
  rw [← e2]
  have h3 := mul_self_le_mul_self (Real.sqrt_nonneg _) h2
  rw [Real.mul_self_sqrt hV1] at h3
  have h4 : C * Real.sqrt 2 * Real.sqrt V2 * (C * Real.sqrt 2 * Real.sqrt V2) =
      2 * C ^ 2 * V2 := by
    calc C * Real.sqrt 2 * Real.sqrt V2 * (C * Real.sqrt 2 * Real.sqrt V2) =
        C ^ 2 * (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt V2 * Real.sqrt V2) := by ring
      _ = 2 * C ^ 2 * V2 := by
        rw [Real.mul_self_sqrt (by norm_num), Real.mul_self_sqrt hV2]; ring
  linarith

/-- **Variance of a GUE resolvent trace** (Poincaré, the HS gradient identity and the Ward
identity): for Hermitian `C₀`, real `s`, `y > 0`, deterministic `K` and real `w`, with
`R = (C₀ + sA + iy)⁻¹`, `A = gueOfCoords W τ r`:
`E|w Tr(KR) - E w Tr(KR)|² ≤ Cp w² s² τ ‖K‖² y⁻³ E(-Im Tr R)`. -/
theorem fcm_var_core (hgrad : GaussianLpGradient) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (W : ℕ) (τ : ℝ≥0) (C0 : Matrix (Fin W) (Fin W) ℂ), C0.IsHermitian →
      ∀ (s y : ℝ), 0 < y → ∀ (K : Matrix (Fin W) (Fin W) ℂ) (w : ℝ),
      ∫ r, ‖(w : ℂ) * (K * (C0 + (s : ℂ) • gueOfCoords W τ r +
          ((y : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹).trace -
        ∫ r', (w : ℂ) * (K * (C0 + (s : ℂ) • gueOfCoords W τ r' +
          ((y : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹).trace
            ∂stdGaussCoordLaw (GaussCoord W)‖ ^ 2 ∂stdGaussCoordLaw (GaussCoord W) ≤
        Cp * (w ^ 2 * s ^ 2 * (τ : ℝ) * ‖K‖ ^ 2 * y⁻¹ ^ 3) *
          ∫ r, -((C0 + (s : ℂ) • gueOfCoords W τ r +
            ((y : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹).trace.im
              ∂stdGaussCoordLaw (GaussCoord W) := by
  obtain ⟨Cp, hCp, hP⟩ := fcm_poincare hgrad
  refine ⟨Cp, hCp, fun W τ C0 hC0 s y hy K w => ?_⟩
  set v : GaussCoord W → ℝ≥0 := fun _ => 1 with hv
  have hstd : stdGaussCoordLaw (GaussCoord W) = gaussianProduct v := rfl
  set L := s • fcdGue W τ with hL
  have hreg := fcd_coreReg W τ hC0 s
  set R : (GaussCoord W → ℝ) → Matrix (Fin W) (Fin W) ℂ := fun r =>
    (C0 + (s : ℂ) • gueOfCoords W τ r + ((y : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ with hR
  have hG : ∀ x, coreG C0 L y x = R x := fun x => fcd_coreG_eq W τ C0 s y x
  set f := coreF C0 L w K y with hfdef
  have hfx : ∀ x, f x = (w : ℂ) * (K * R x).trace := fun x => by
    rw [hfdef, coreF, LinearMap.coe_toContinuousLinearMap', coreTrLin_apply, hG]
  have hf := coreF_contDiff hreg w K hy
  have hHx : ∀ x, (C0 + (s : ℂ) • gueOfCoords W τ x).IsHermitian := fun x =>
    hC0.add (fcd_isHermitian_real_smul (gueOfCoords_isHermitian W τ x) s)
  have hRb : ∀ x, ‖R x‖ ≤ y⁻¹ := fun x => (fcd_herm_inv (hHx x) hy).2
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hImle : ∀ x, -(R x).trace.im ≤ W * y⁻¹ := fun x => by
    have := (fcd_abs_imTr_le (R x)).trans (mul_le_mul_of_nonneg_left (hRb x) (Nat.cast_nonneg _))
    rw [Fintype.card_fin] at this
    exact (neg_le_abs _).trans this
  set Q := w ^ 2 * s ^ 2 * (τ : ℝ) * ‖K‖ ^ 2 * y⁻¹ ^ 3 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hgrad2 : ∀ x, weightedGradientNorm v f x ^ 2 ≤ Q * -(R x).trace.im := by
    intro x
    have hsum : weightedGradientNorm v f x ^ 2 =
        ∑ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2 := by
      unfold weightedGradientNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
      simp [hv]
    set X := R x * K * R x with hX
    have hder : ∀ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2 =
        w ^ 2 * s ^ 2 * ‖(X * gueOfCoords W τ (Pi.single i 1)).trace‖ ^ 2 := by
      intro i
      rw [hfdef, coreF_fderiv hreg w K hy, hG, fcd_smul_gue_apply, norm_neg, norm_mul,
        Matrix.mul_smul, trace_smul, smul_eq_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    rw [hsum, Finset.sum_congr rfl fun i _ => hder i, ← Finset.mul_sum, fcm_hs_gue]
    have hhs : fcmHS X ≤ (y⁻¹ * ‖K‖) ^ 2 * fcmHS (R x) := by
      refine (fcm_hs_mul_le (R x * K) (R x)).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (fcmHS_nonneg _)
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hRb x) (norm_nonneg _))
    have hward : fcmHS (R x) = -(R x).trace.im / y := fcm_ward (hHx x) hy
    rw [hward] at hhs
    calc w ^ 2 * s ^ 2 * ((τ : ℝ) * fcmHS X)
        ≤ w ^ 2 * s ^ 2 * ((τ : ℝ) * ((y⁻¹ * ‖K‖) ^ 2 * (-(R x).trace.im / y))) := by
          gcongr
      _ = Q * -(R x).trace.im := by rw [hQ]; field_simp
  have hgb : ∀ x, weightedGradientNorm v f x ≤ Real.sqrt (Q * (W * y⁻¹)) := by
    intro x
    have h0 : (0 : ℝ) ≤ weightedGradientNorm v f x := Real.sqrt_nonneg _
    rw [← Real.sqrt_sq h0]
    exact Real.sqrt_le_sqrt ((hgrad2 x).trans (mul_le_mul_of_nonneg_left (hImle x) hQ0))
  have hfb : ∀ x, ‖f x‖ ≤ |w| * (W * (‖K‖ * y⁻¹)) := fun x => by
    refine (coreF_norm_le w K y x).trans ?_
    rw [Fintype.card_fin, hG]
    gcongr
    exact hRb x
  have hpoin := hP (GaussCoord W) v f hf _ _ hfb hgb
  rw [← hstd] at hpoin
  simp only [hfx] at hpoin
  refine hpoin.trans ?_
  have hre : Cp * Q * ∫ r, -(R r).trace.im ∂stdGaussCoordLaw (GaussCoord W) =
      Cp * ∫ x, Q * -(R x).trace.im ∂stdGaussCoordLaw (GaussCoord W) := by
    rw [integral_const_mul]; ring
  show _ ≤ Cp * Q * ∫ r, -(R r).trace.im ∂stdGaussCoordLaw (GaussCoord W)
  rw [hre, hstd]
  have hRc : Continuous R :=
    fcd_continuous_inv (((continuous_const.add ((continuous_const (y := (s : ℂ))).smul
      (continuous_gueOfCoords W τ))).add continuous_const)) fun x => (fcd_herm_inv (hHx x) hy).1
  have hwc : Continuous (weightedGradientNorm v f) := by
    have hd := hf.continuous_fderiv one_ne_zero
    unfold weightedGradientNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
    exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
  refine mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ hgrad2) hCp.le
  · exact Integrable.of_bound (hwc.pow 2).aestronglyMeasurable (Q * (W * y⁻¹))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact (hgrad2 x).trans (mul_le_mul_of_nonneg_left (hImle x) hQ0))
  · refine Integrable.of_bound (continuous_const.mul
      (Complex.continuous_im.comp hRc.matrix_trace).neg).aestronglyMeasurable
      (Q * (W * y⁻¹)) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hQ0]
    refine mul_le_mul_of_nonneg_left ?_ hQ0
    rw [abs_neg]
    have := (fcd_abs_imTr_le (R x)).trans (mul_le_mul_of_nonneg_left (hRb x) (Nat.cast_nonneg _))
    rwa [Fintype.card_fin] at this

/-- **The fresh count variance bound** with a deterministic insertion `K`: for `t ∈ [0,1]`,
`E|⟨K H_t⁻¹⟩ - E⟨K H_t⁻¹⟩|² ≤ Cp (16C√2/√c + 1 + 2/γ) ‖K‖² / (W² y_t³)`, `⟨·⟩ = W⁻¹ Tr`.
For `t ≥ 1/2` from the counting bound; for `t < 1/2` from `y_t ≥ γ/2`. -/
theorem fcm_heat_variance (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    ∃ Cp C : ℝ, 0 < Cp ∧ 0 < C ∧ ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, 0 < fcGamma b E →
      ∀ (W : ℕ), 0 < W → ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian → ∀ ε : ℝ, 0 < ε →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ K : Matrix (Fin W) (Fin W) ℂ,
      ∫ r, ‖(W : ℂ)⁻¹ * (K * (fcHeatMatrix b E F ε t (gueOfCoords W (fcdTau b W) r))⁻¹).trace -
        ∫ r', (W : ℂ)⁻¹ * (K * (fcHeatMatrix b E F ε t
          (gueOfCoords W (fcdTau b W) r'))⁻¹).trace ∂stdGaussCoordLaw (GaussCoord W)‖ ^ 2
          ∂stdGaussCoordLaw (GaussCoord W) ≤
        Cp * (16 * C * Real.sqrt 2 / Real.sqrt (1 - 2 * b) + 1 + 2 / fcGamma b E) * ‖K‖ ^ 2 /
          ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3) := by
  obtain ⟨Cp, hCp, hV⟩ := fcm_var_core hgrad
  obtain ⟨C, hC, hN⟩ := fcm_poisson_count_heat hcount
  refine ⟨Cp, C, hCp, hC, fun b hb0 hb E hγ W hW F hF ε hε t ht K => ?_⟩
  have hc : 0 < 1 - 2 * b := by linarith
  have hc1 : 1 - 2 * b ≤ 1 := by linarith [hb]
  set γ := fcGamma b E
  set y := fcHeight' b E ε t with hy
  have hyε : ε ≤ y := by simp only [hy, fcHeight']; nlinarith [ht.2]
  have hy0 : 0 < y := lt_of_lt_of_le hε hyε
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set τ := fcdTau b W
  have hτ : (τ : ℝ) = (1 - 2 * b) / W := fcd_tau_coe hb W
  set S : ℝ := E + (1 - t) * (1 - 2 * b) * (matchedA E).re
  set C0 : Matrix (Fin W) (Fin W) ℂ := -((S : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - F
  have hC0 : C0.IsHermitian := by
    simp only [C0, neg_smul]
    exact (fcd_isHermitian_real_smul isHermitian_one _).neg.sub hF
  have hmat : ∀ r, fcHeatMatrix b E F ε t (gueOfCoords W τ r) =
      C0 + ((Real.sqrt t : ℝ) : ℂ) • gueOfCoords W τ r + ((y : ℂ) * I) • 1 := by
    intro r
    simp only [fcHeatMatrix, fcHeatHerm, C0, neg_smul, hy]
    abel
  have hw : (W : ℂ)⁻¹ = (((W : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  simp only [hmat, hw]
  refine (hV W τ C0 hC0 (Real.sqrt t) y hy0 K (W : ℝ)⁻¹).trans ?_
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.1
  -- the integrated Poisson kernel
  have hIm : ∀ r, -(C0 + ((Real.sqrt t : ℝ) : ℂ) • gueOfCoords W τ r +
      ((y : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹.trace.im =
      spectralSum (fcHeatHerm b E F t (gueOfCoords W τ r)) (fcmPoisson y) := by
    intro r
    rw [← hmat]
    exact fcm_neg_im_trace (fcd_isHermitian_heatHerm b E hF t (gueOfCoords_isHermitian W τ r)) hy0
  simp only [hIm]
  set N := ∫ r, spectralSum (fcHeatHerm b E F t (gueOfCoords W τ r)) (fcmPoisson y)
    ∂stdGaussCoordLaw (GaussCoord W)
  set B := 16 * C * Real.sqrt 2 / Real.sqrt (1 - 2 * b) + 1 + 2 / γ
  have hB0 : 0 ≤ 16 * C * Real.sqrt 2 / Real.sqrt (1 - 2 * b) := by positivity
  have hPabs : ∀ x, |fcmPoisson y x| ≤ y⁻¹ := fun x => by
    rw [abs_of_nonneg (fcm_poisson_nonneg hy0 x)]; exact fcm_poisson_le hy0 x
  have hHc : Continuous fun r => fcHeatHerm b E F t (gueOfCoords W τ r) :=
    (fcd_continuous_heatHerm b E F t).comp (continuous_gueOfCoords W τ)
  have hPm : Measurable (fcmPoisson y) := by
    unfold fcmPoisson
    exact (continuous_const.div (by fun_prop) fun x => by positivity).measurable
  have hint : Integrable (fun r => spectralSum (fcHeatHerm b E F t (gueOfCoords W τ r))
      (fcmPoisson y)) (stdGaussCoordLaw (GaussCoord W)) :=
    Integrable.of_bound (fc_measurable_spectralSum hHc.measurable
      (fun r => fcd_isHermitian_heatHerm b E hF t (gueOfCoords_isHermitian W τ r)) hPm
      ).aestronglyMeasurable (W * y⁻¹) (Filter.Eventually.of_forall fun r => by
        have := fc_abs_spectralSum_le
          (fcd_isHermitian_heatHerm b E hF t (gueOfCoords_isHermitian W τ r)) hPabs
        rw [Fintype.card_fin] at this
        rwa [Real.norm_eq_abs])
  have hN0 : 0 ≤ N := integral_nonneg fun r => by
    rw [fc_spectralSum_eq (fcd_isHermitian_heatHerm b E hF t (gueOfCoords_isHermitian W τ r))]
    exact Finset.sum_nonneg fun k _ => fcm_poisson_nonneg hy0 _
  have hNW : N ≤ W * y⁻¹ := by
    refine (integral_mono hint (integrable_const ((W : ℝ) * y⁻¹)) fun r => ?_).trans
      (by rw [integral_const, probReal_univ, one_smul])
    have := fc_abs_spectralSum_le
      (fcd_isHermitian_heatHerm b E hF t (gueOfCoords_isHermitian W τ r)) hPabs
    rw [Fintype.card_fin] at this
    exact (le_abs_self _).trans this
  have hNB : t * N ≤ B * W := by
    have htN : t * N ≤ N := mul_le_of_le_one_left hN0 ht.2
    refine htN.trans ?_
    rcases lt_or_ge t (1 / 2) with hlt | hge
    · have hyγ : γ / 2 ≤ y := by simp only [hy, fcHeight']; nlinarith
      have h1 : y⁻¹ ≤ 2 / γ := by
        rw [inv_le_iff_one_le_mul₀ hy0]
        rw [div_mul_eq_mul_div, le_div_iff₀ hγ]
        linarith
      calc N ≤ W * y⁻¹ := hNW
        _ ≤ W * (2 / γ) := mul_le_mul_of_nonneg_left h1 hW'.le
        _ ≤ B * W := by
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_right ?_ hW'.le
            linarith
    · have ht0 : 0 < t := by linarith
      have h1 := hN b hb E W hW F hF t ht0 y hy0
      have hsq : Real.sqrt (1 - 2 * b) / Real.sqrt 2 ≤ Real.sqrt (t * (1 - 2 * b)) := by
        rw [Real.sqrt_mul ht.1, div_le_iff₀ (by positivity), mul_comm (Real.sqrt t), mul_assoc]
        have h2 : 1 ≤ Real.sqrt t * Real.sqrt 2 := by
          rw [← Real.sqrt_mul ht.1]
          rw [Real.one_le_sqrt]
          linarith
        nlinarith [Real.sqrt_nonneg (1 - 2 * b)]
      have h3 : 16 * C / Real.sqrt (t * (1 - 2 * b)) ≤ 16 * C * Real.sqrt 2 / Real.sqrt (1 - 2 * b) := by
        have hs0 : 0 < Real.sqrt (1 - 2 * b) := Real.sqrt_pos.mpr hc
        rw [div_le_div_iff₀ (by positivity) hs0]
        have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 16 * C * Real.sqrt 2)
        have e : 16 * C * Real.sqrt 2 * (Real.sqrt (1 - 2 * b) / Real.sqrt 2) =
            16 * C * Real.sqrt (1 - 2 * b) := by field_simp
        linarith
      calc N ≤ (16 * C / Real.sqrt (t * (1 - 2 * b)) + 1) * W := h1
        _ ≤ B * W := by
            refine mul_le_mul_of_nonneg_right ?_ hW'.le
            have : 0 ≤ 2 / γ := by positivity
            linarith
  have hc1 : 1 - 2 * b ≤ 1 := by linarith
  rw [hst, hτ]
  have hK0 := sq_nonneg ‖K‖
  have htN0 : 0 ≤ t * N := mul_nonneg ht.1 hN0
  have key : (1 - 2 * b) * (t * N) ≤ B * W := (mul_le_of_le_one_left htN0 hc1).trans hNB
  have hy3 : 0 < (y⁻¹) ^ 3 := by positivity
  calc Cp * ((W : ℝ)⁻¹ ^ 2 * t * ((1 - 2 * b) / W) * ‖K‖ ^ 2 * y⁻¹ ^ 3) * N
      = Cp * ‖K‖ ^ 2 * y⁻¹ ^ 3 * ((W : ℝ)⁻¹ ^ 3 * ((1 - 2 * b) * (t * N))) := by
        field_simp
    _ ≤ Cp * ‖K‖ ^ 2 * y⁻¹ ^ 3 * ((W : ℝ)⁻¹ ^ 3 * (B * W)) := by gcongr
    _ = Cp * B * ‖K‖ ^ 2 / ((W : ℝ) ^ 2 * y ^ 3) := by
        field_simp

end Variance

end BlockBand.Layers
