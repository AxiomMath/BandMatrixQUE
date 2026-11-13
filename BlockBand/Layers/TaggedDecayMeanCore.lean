module

public import BlockBand.Layers.TaggedDecayClock

/-!
# The differentiated mean equation of one untagged layer: the deterministic closure

From the proof of the tagged decay bound: "`v = d + (c + b²a²) Q v`, `w = b a² v` ... With the
scalar error `δ`, the coefficient changes by `O(δ)` ... Changing `M` to `R` costs `Cδu` ...
Consequently `|E(d₊ | X, S)| ≤ q_* |d| + Cδu + Cu/W`".

This module is deterministic. It closes the linear system obtained by differentiating the exact
matrix mean identity `(𝒟 - 𝒮(ḡ)) E𝒢 = I + Resid` of one separate-port layer along `X - hS`
(`BlockBand.Layers.TaggedDecayMean`). Notation: `K = z_∂ - X` (`tdcK`), `R = K⁻¹`, `a = matchedA E`,
`c = 1 - 2b`, `S = K*YK`, `u = W⁻¹ Tr Y` (`clkTrace`), `D_i = W⁻¹ Tr P_i R S R` (`tdcD`), the
layer means `gA, gP` of the physical and port traces, the mean top block
`T = -E - X - diag(c gA + b gP) = K - Δ`, `Δ = diag(c(gA - a) + b(gP - a))`, and `θ` a bound of
`|gA_i - a| + |gP_i - a|`.

## Main results

* `tdm_close` — the scalar closure: `v = -D̃ + Q̃(cv + bw) + f`, `w = βv + r` with weighted row sums
  `Σ_k |Q̃_ik||c + bβ_k| ≤ t' < 1` give `|w| ≤ β_*(max|D̃| + max|f| + |b| Q_s max|r|)/(1 - t') + max|r|`.
* `tdm_core` — the closure of the differentiated mean system: after `b ∈ (0, 1/2)`, a strict
  margin `t < 1 - b` (`StrictContractionContract.margin`) and `η > 0` there are `θ₀ > 0`,
  `0 ≤ q < 1` and `C ≥ 0` such that, uniformly in `W`, `E` with `|E| ≤ 2`, `Im z_∂ ≥ η`, Hermitian
  `X`, `Y ⪰ 0` satisfying the margin, means within `θ ≤ θ₀` of `a`, a mean residual `‖Res‖ ≤ ρ ≤ θ₀`
  and a differentiated residual of size `ϑ`:
  `|w_j| ≤ q max_i |D_i(X, Y)| + C (θ + ρ) u + C ϑ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

/-!
## 1. The scalar closure
-/

/-- **Scalar closure of the differentiated two-port system.** -/
theorem tdm_close {v w Dt f r β : Fin 2 → ℂ} {Qt : Fin 2 → Fin 2 → ℂ} {c bc : ℂ}
    {t' Qs βs Dm fm rm : ℝ} (ht' : t' < 1)
    (hv : ∀ i, v i = -Dt i + (Qt i 0 * (c * v 0 + bc * w 0) + Qt i 1 * (c * v 1 + bc * w 1)) + f i)
    (hw : ∀ j, w j = β j * v j + r j)
    (hrow : ∀ i, ‖Qt i 0‖ * ‖c + bc * β 0‖ + ‖Qt i 1‖ * ‖c + bc * β 1‖ ≤ t')
    (hQs : ∀ i, ‖Qt i 0‖ + ‖Qt i 1‖ ≤ Qs) (hβ : ∀ j, ‖β j‖ ≤ βs)
    (hD : ∀ i, ‖Dt i‖ ≤ Dm) (hf : ∀ i, ‖f i‖ ≤ fm) (hr : ∀ i, ‖r i‖ ≤ rm) (j : Fin 2) :
    ‖w j‖ ≤ βs * ((Dm + fm + ‖bc‖ * Qs * rm) / (1 - t')) + rm := by
  set V := max ‖v 0‖ ‖v 1‖ with hVdef
  have hV : ∀ k, ‖v k‖ ≤ V := fun k => by
    fin_cases k
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV 0)
  have hrm : 0 ≤ rm := (norm_nonneg _).trans (hr 0)
  have hQs0 : 0 ≤ Qs := le_trans (by positivity) (hQs 0)
  have key : ∀ i, ‖v i‖ ≤ Dm + t' * V + ‖bc‖ * Qs * rm + fm := by
    intro i
    have e : v i = -Dt i + (Qt i 0 * (c + bc * β 0) * v 0 + Qt i 1 * (c + bc * β 1) * v 1) +
        bc * (Qt i 0 * r 0 + Qt i 1 * r 1) + f i := by
      rw [hv i, hw 0, hw 1]; ring
    have h1 : ‖Qt i 0 * (c + bc * β 0) * v 0‖ ≤ ‖Qt i 0‖ * ‖c + bc * β 0‖ * V := by
      rw [norm_mul, norm_mul]; exact mul_le_mul_of_nonneg_left (hV 0) (by positivity)
    have h2 : ‖Qt i 1 * (c + bc * β 1) * v 1‖ ≤ ‖Qt i 1‖ * ‖c + bc * β 1‖ * V := by
      rw [norm_mul, norm_mul]; exact mul_le_mul_of_nonneg_left (hV 1) (by positivity)
    have h3 : ‖bc * (Qt i 0 * r 0 + Qt i 1 * r 1)‖ ≤ ‖bc‖ * Qs * rm := by
      rw [norm_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖Qt i 0 * r 0 + Qt i 1 * r 1‖ ≤ ‖Qt i 0‖ * ‖r 0‖ + ‖Qt i 1‖ * ‖r 1‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
        _ ≤ ‖Qt i 0‖ * rm + ‖Qt i 1‖ * rm := by gcongr <;> exact hr _
        _ = (‖Qt i 0‖ + ‖Qt i 1‖) * rm := by ring
        _ ≤ Qs * rm := mul_le_mul_of_nonneg_right (hQs i) hrm
    rw [e]
    calc ‖-Dt i + (Qt i 0 * (c + bc * β 0) * v 0 + Qt i 1 * (c + bc * β 1) * v 1) +
          bc * (Qt i 0 * r 0 + Qt i 1 * r 1) + f i‖
        ≤ ‖Dt i‖ + (‖Qt i 0 * (c + bc * β 0) * v 0‖ + ‖Qt i 1 * (c + bc * β 1) * v 1‖) +
            ‖bc * (Qt i 0 * r 0 + Qt i 1 * r 1)‖ + ‖f i‖ := by
          refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
          refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
          refine (norm_add_le _ _).trans ?_
          rw [norm_neg]
          exact add_le_add_right (norm_add_le _ _) _
      _ ≤ Dm + (‖Qt i 0‖ * ‖c + bc * β 0‖ * V + ‖Qt i 1‖ * ‖c + bc * β 1‖ * V) +
            ‖bc‖ * Qs * rm + fm := by gcongr <;> first | exact hD i | exact hf i
      _ ≤ Dm + t' * V + ‖bc‖ * Qs * rm + fm := by
          have := mul_le_mul_of_nonneg_right (hrow i) hV0
          nlinarith
  have hVb : V ≤ Dm + t' * V + ‖bc‖ * Qs * rm + fm := max_le (key 0) (key 1)
  have h1t : 0 < 1 - t' := by linarith
  have hVq : V ≤ (Dm + fm + ‖bc‖ * Qs * rm) / (1 - t') := by
    rw [le_div_iff₀ h1t]; nlinarith
  have hβs : 0 ≤ βs := (norm_nonneg _).trans (hβ 0)
  calc ‖w j‖ = ‖β j * v j + r j‖ := by rw [hw j]
    _ ≤ ‖β j‖ * ‖v j‖ + ‖r j‖ := (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ βs * V + rm := by
        gcongr
        · exact hβ j
        · exact hV j
        · exact hr j
    _ ≤ βs * ((Dm + fm + ‖bc‖ * Qs * rm) / (1 - t')) + rm := by gcongr

/-!
## 2. Matrix helpers
-/

section Helpers

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem tdm_norm_mul3_le (A B C : Matrix n n ℂ) : ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

/-- `‖diag(d)‖ ≤ θ` from `|d_x| ≤ θ`. -/
theorem tdm_norm_diagonal_le {d : n → ℂ} {θ : ℝ} (hθ : 0 ≤ θ) (hd : ∀ x, ‖d x‖ ≤ θ) :
    ‖(diagonal d : Matrix n n ℂ)‖ ≤ θ := by
  rw [l2_opNorm_diagonal]
  exact pi_norm_le_iff_of_nonneg hθ |>.mpr hd

end Helpers

section TwoPort

variable {W : ℕ}

/-- `|W⁻¹ Tr P_i (A Y B)| ≤ ‖A‖ ‖B‖ W⁻¹ Tr Y` for `Y ⪰ 0` (trace pairing with `Y`). -/
theorem tdm_norm_blockTrace_AYB_le {Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : Y.PosSemidef) (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    ‖blockTrace (A * Y * B) i‖ ≤ ‖A‖ * ‖B‖ * clkTrace Y := by
  rw [tdc_blockTrace_eq]
  have e : (A * Y * B * tdcProj i).trace = (Y * (B * tdcProj i * A)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc]
  rw [e, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 := wl_norm_trace_weight_le hY (B * tdcProj i * A)
  have h2 : ‖B * tdcProj (W := W) i * A‖ ≤ ‖A‖ * ‖B‖ := by
    refine (tdm_norm_mul3_le _ _ _).trans ?_
    have := tdc_norm_proj_le (W := W) i
    calc ‖B‖ * ‖tdcProj (W := W) i‖ * ‖A‖ ≤ ‖B‖ * 1 * ‖A‖ := by gcongr
      _ = ‖A‖ * ‖B‖ := by ring
  have h3 := wl_trace_re_nonneg hY
  unfold clkTrace
  calc (W : ℝ)⁻¹ * ‖(Y * (B * tdcProj i * A)).trace‖ ≤ (W : ℝ)⁻¹ * (‖A‖ * ‖B‖ * Y.trace.re) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_right h2 h3)
    _ = ‖A‖ * ‖B‖ * ((W : ℝ)⁻¹ * Y.trace.re) := by ring

/-- `Q_ik = W⁻¹ Tr P_i R P_k R`. -/
theorem tdm_blockPairTrace_eq (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i k : Fin 2) :
    blockPairTrace R i k = blockTrace (R * tdcProj k * R) i := by
  unfold blockPairTrace blockTrace tdcProj
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [mul_diagonal, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- `diag(g_{x.1}) = g₀ P₀ + g₁ P₁`. -/
theorem tdm_diagonal_eq (g : Fin 2 → ℂ) :
    (diagonal fun x : Fin 2 × Fin W => g x.1) = g 0 • tdcProj 0 + g 1 • tdcProj 1 := by
  ext x y
  simp only [tdcProj, Matrix.add_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨i, α⟩ := x
    fin_cases i <;> simp
  · simp [hxy]

theorem tdm_blockTrace_add (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    blockTrace (A + B) i = blockTrace A i + blockTrace B i := by
  unfold blockTrace
  simp only [Matrix.add_apply, Finset.sum_add_distrib, mul_add]

theorem tdm_blockTrace_sub (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    blockTrace (A - B) i = blockTrace A i - blockTrace B i := by
  unfold blockTrace
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]

theorem tdm_blockTrace_smul (c : ℂ) (A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    blockTrace (c • A) i = c * blockTrace A i := by
  unfold blockTrace
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => by ring

end TwoPort

/-!
## 3. The mean top block and the port coefficients
-/

section Pieces

variable {W : ℕ}

/-- The scalar error `Δ = diag(c(gA - a) + b(gP - a))` of the mean top block. -/
def tdmDelta (b E : ℝ) (gA gP : Fin 2 → ℂ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  diagonal (fun x : Fin 2 × Fin W => (1 - 2 * (b : ℂ)) * (gA x.1 - matchedA E) +
    (b : ℂ) * (gP x.1 - matchedA E))

/-- The mean top block `T = K - Δ`. -/
def tdmTop (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (gA gP : Fin 2 → ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  tdcK b E X - tdmDelta b E gA gP

theorem tdm_norm_c {b : ℝ} (hb1 : b < 1 / 2) : ‖(1 - 2 * (b : ℂ))‖ = 1 - 2 * b := by
  rw [show (1 - 2 * (b : ℂ)) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]

theorem tdm_norm_b {b : ℝ} (hb0 : 0 < b) : ‖(b : ℂ)‖ = b := by
  rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]

theorem tdm_delta_entry_le {b θ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {a gA gP : ℂ}
    (hθ : ‖gA - a‖ + ‖gP - a‖ ≤ θ) :
    ‖(1 - 2 * (b : ℂ)) * (gA - a) + (b : ℂ) * (gP - a)‖ ≤ θ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, tdm_norm_c hb1, tdm_norm_b hb0]
  have h1 := norm_nonneg (gA - a)
  have h2 := norm_nonneg (gP - a)
  nlinarith only [h1, h2, hθ, hb0, hb1]

/-- **The mean top block is invertible with `‖T⁻¹‖ ≤ 2/η`** once `θ ≤ η/2`. -/
theorem tdm_top_facts {b E η θ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hη : 0 < η)
    (hzη : η ≤ (boundaryZ b E).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {gA gP : Fin 2 → ℂ}
    (hθ : ∀ i, ‖gA i - matchedA E‖ + ‖gP i - matchedA E‖ ≤ θ) (hθη : θ ≤ η / 2) :
    IsUnit (tdmTop b E X gA gP).det ∧ ‖(tdmTop b E X gA gP)⁻¹‖ ≤ 2 / η ∧
      ‖(tdmDelta b E gA gP : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ θ := by
  have hθ0 : 0 ≤ θ := le_trans (by positivity) (hθ 0)
  have hΔe := fun i => tdm_delta_entry_le hb0 hb1 (hθ i)
  have hΔn : ‖(tdmDelta b E gA gP : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ θ :=
    tdm_norm_diagonal_le hθ0 fun x => hΔe x.1
  set z := boundaryZ b E
  set d : Fin 2 × Fin W → ℂ := fun x => (1 - 2 * (b : ℂ)) * (gA x.1 - matchedA E) +
    (b : ℂ) * (gP x.1 - matchedA E) with hd
  have hTalt : tdmTop b E X gA gP = -X - diagonal (fun x => d x - z) := by
    unfold tdmTop tdmDelta tdcK
    rw [smul_one_eq_diagonal]
    ext p q
    simp only [Matrix.sub_apply, Matrix.neg_apply, diagonal_apply, hd]
    split_ifs <;> ring
  have him : ∀ x : Fin 2 × Fin W, η / 2 ≤ -(d x - z).im := by
    intro x
    have h1 := Complex.abs_im_le_norm (d x)
    have h2 := hΔe x.1
    rw [Complex.sub_im]
    have := abs_le.mp (h1.trans h2)
    linarith
  refine ⟨?_, ?_, hΔn⟩
  · rw [hTalt]
    exact isUnit_iff_ne_zero.mpr (cmp_det_ne_zero _ hX.neg _ fun x => by
      have := him x; linarith)
  · have := lct_norm_shifted_inv_le (-X) hX.neg _ (by positivity : 0 < η / 2) him
    rw [← hTalt] at this
    refine this.trans (le_of_eq ?_)
    field_simp

/-- **The port coefficients**: `|z - b gA| ≥ 1/2` and `|b gP/(z - b gA) - b a²| ≤ θ`, with
`z = a⁻¹ + ba`, `|a| = 1`, for `|gA - a| + |gP - a| ≤ θ ≤ 1`. -/
theorem tdm_port_scalars {a gA gP : ℂ} {b θ : ℝ} (ha1 : ‖a‖ = 1) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hθ1 : θ ≤ 1) (hθ : ‖gA - a‖ + ‖gP - a‖ ≤ θ) :
    1 / 2 ≤ ‖a⁻¹ + (b : ℂ) * a - (b : ℂ) * gA‖ ∧
      ‖(b : ℂ) * gP / (a⁻¹ + (b : ℂ) * a - (b : ℂ) * gA) - (b : ℂ) * a ^ 2‖ ≤ θ := by
  have ha0 : a ≠ 0 := fun h => by rw [h, norm_zero] at ha1; exact zero_ne_one ha1
  have hbn := tdm_norm_b hb0
  have hA := norm_nonneg (gA - a)
  have hP := norm_nonneg (gP - a)
  have hpc : 1 / 2 ≤ ‖a⁻¹ + (b : ℂ) * a - (b : ℂ) * gA‖ := by
    have e : a⁻¹ + (b : ℂ) * a - (b : ℂ) * gA = a⁻¹ - (b : ℂ) * (gA - a) := by ring
    have h1 : ‖(b : ℂ) * (gA - a)‖ ≤ 1 / 2 := by
      rw [norm_mul, hbn]
      nlinarith only [hA, hP, hθ, hθ1, hb0, hb1]
    have h2 : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha1, inv_one]
    have h3 := norm_sub_norm_le (a⁻¹) ((b : ℂ) * (gA - a))
    rw [h2] at h3
    rw [e]; linarith
  refine ⟨hpc, ?_⟩
  set pc := a⁻¹ + (b : ℂ) * a - (b : ℂ) * gA with hpcd
  have hpc0 : pc ≠ 0 := fun h => by rw [h, norm_zero] at hpc; linarith
  have e : (b : ℂ) * gP / pc - (b : ℂ) * a ^ 2 =
      (b : ℂ) * ((gP - a) + (b : ℂ) * a ^ 2 * (gA - a)) / pc := by
    rw [eq_div_iff hpc0, sub_mul, div_mul_cancel₀ _ hpc0, hpcd]
    field_simp
    ring
  rw [e, norm_div, div_le_iff₀ (by linarith), norm_mul, hbn]
  have h1 : ‖(gP - a) + (b : ℂ) * a ^ 2 * (gA - a)‖ ≤ θ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, ha1, hbn, one_pow, mul_one]
    nlinarith only [hA, hP, hθ, hb0, hb1]
  have h0 := norm_nonneg ((gP - a) + (b : ℂ) * a ^ 2 * (gA - a))
  nlinarith only [h1, h0, hpc, hb0, hb1]

/-- **`M̄ → R` costs `C(θ + ρ) u` in the source term** (in the paper: "Changing `M` to `R`
costs `Cδu` in normalized traces, because `KM - I = O(δ)` and positivity permits trace pairing
with `Y`"). Deterministic. -/
theorem tdm_Dt_le {K R Mb Δ Res Gb Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : Y.PosSemidef) {m θ ρ : ℝ} (hm : 0 ≤ m) (hθ0 : 0 ≤ θ) (hρ0 : 0 ≤ ρ) (hθm : θ * m ≤ 1)
    (hρ1 : ρ ≤ 1) (hKR : K * R = 1) (hMR : Mb - R = Mb * Δ * R) (hKM : K * Mb = 1 + Δ * Mb)
    (hGb : Gb = Mb * (1 + Res)) (hMn : ‖Mb‖ ≤ m) (hΔn : ‖Δ‖ ≤ θ) (hRKs : ‖R * Kᴴ‖ ≤ 3)
    (hRes : ‖Res‖ ≤ ρ) (i : Fin 2) :
    ‖blockTrace (Mb * (Kᴴ * Y * K) * Gb) i - blockTrace (R * (Kᴴ * Y * K) * R) i‖ ≤
      (15 * m * θ + 6 * ρ) * clkTrace Y := by
  have hu0 := clkTrace_nonneg hY
  have hRSR : R * (Kᴴ * Y * K) * R = R * Kᴴ * Y * 1 := by
    simp only [Matrix.mul_assoc, hKR]
  have e : Mb * (Kᴴ * Y * K) * Gb = (Mb * Kᴴ) * Y * (K * Mb * (1 + Res)) := by
    rw [hGb]; simp only [Matrix.mul_assoc]
  have e2 : blockTrace (Mb * (Kᴴ * Y * K) * Gb) i - blockTrace (R * (Kᴴ * Y * K) * R) i =
      blockTrace ((Mb * Kᴴ - R * Kᴴ) * Y * (K * Mb * (1 + Res))) i +
        blockTrace (R * Kᴴ * Y * (K * Mb * (1 + Res) - 1)) i := by
    rw [← tdm_blockTrace_add, ← tdm_blockTrace_sub, e, hRSR]
    congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hDM : ‖Δ * Mb‖ ≤ θ * m := (norm_mul_le _ _).trans (mul_le_mul hΔn hMn (norm_nonneg _) hθ0)
  have hA1 : ‖Mb * Kᴴ - R * Kᴴ‖ ≤ 3 * (m * θ) := by
    rw [← Matrix.sub_mul, hMR, Matrix.mul_assoc, Matrix.mul_assoc]
    refine (norm_mul_le _ _).trans ?_
    have h1 : ‖Δ * (R * Kᴴ)‖ ≤ θ * 3 := (norm_mul_le _ _).trans
      (mul_le_mul hΔn hRKs (norm_nonneg _) hθ0)
    calc ‖Mb‖ * ‖Δ * (R * Kᴴ)‖ ≤ m * (θ * 3) := mul_le_mul hMn h1 (norm_nonneg _) hm
      _ = 3 * (m * θ) := by ring
  have hKMn : ‖K * Mb‖ ≤ 2 := by
    rw [hKM]
    refine (norm_add_le _ _).trans ?_
    have := lct_norm_one_le (n := Fin 2 × Fin W)
    linarith
  have h1R : ‖1 + Res‖ ≤ 1 + ρ := (norm_add_le _ _).trans (add_le_add lct_norm_one_le hRes)
  have hB1 : ‖K * Mb * (1 + Res)‖ ≤ 4 := by
    refine (norm_mul_le _ _).trans ?_
    calc ‖K * Mb‖ * ‖1 + Res‖ ≤ 2 * (1 + ρ) := mul_le_mul hKMn h1R (norm_nonneg _) (by norm_num)
      _ ≤ 4 := by linarith
  have hB1' : ‖K * Mb * (1 + Res) - 1‖ ≤ θ * m + 2 * ρ := by
    have e3 : K * Mb * (1 + Res) - 1 = Δ * Mb + Res + Δ * Mb * Res := by
      rw [hKM]; simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]; abel
    rw [e3]
    have hDMR : ‖Δ * Mb * Res‖ ≤ θ * m * ρ := (norm_mul_le _ _).trans
      (mul_le_mul hDM hRes (norm_nonneg _) (by positivity))
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) hDMR).trans ?_)
    nlinarith only [hDM, hRes, hθm, hρ0, hDMR, mul_le_mul_of_nonneg_right hθm hρ0]
  have hb1 := tdm_norm_blockTrace_AYB_le hY (Mb * Kᴴ - R * Kᴴ) (K * Mb * (1 + Res)) i
  have hb2 := tdm_norm_blockTrace_AYB_le hY (R * Kᴴ) (K * Mb * (1 + Res) - 1) i
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ ‖Mb * Kᴴ - R * Kᴴ‖ * ‖K * Mb * (1 + Res)‖ * clkTrace Y +
        ‖R * Kᴴ‖ * ‖K * Mb * (1 + Res) - 1‖ * clkTrace Y := add_le_add hb1 hb2
    _ ≤ (3 * (m * θ)) * 4 * clkTrace Y + 3 * (θ * m + 2 * ρ) * clkTrace Y := by
        gcongr
    _ = (15 * m * θ + 6 * ρ) * clkTrace Y := by ring

/-- **The coefficient comparison** `|Q̃_ik - Q_ik| ≤ e_Q`, `Q̃_ik = W⁻¹ Tr P_i M̄ P_k Gb`. -/
theorem tdm_Qt_le {R Mb Gb : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {r0 e1 e2 g : ℝ}
    (hr0 : 0 ≤ r0) (hMR : ‖Mb - R‖ ≤ e1) (hGb : ‖Gb‖ ≤ g) (hGbR : ‖Gb - R‖ ≤ e2)
    (hRn : ‖R‖ ≤ r0) (i k : Fin 2) :
    ‖blockTrace (Mb * tdcProj k * Gb) i - blockPairTrace R i k‖ ≤ e1 * g + r0 * e2 := by
  rw [tdm_blockPairTrace_eq, ← tdm_blockTrace_sub]
  refine (lct_norm_blockTrace_le _ _).trans ?_
  have e : Mb * tdcProj k * Gb - R * tdcProj k * R = (Mb - R) * tdcProj k * Gb +
      R * tdcProj k * (Gb - R) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [e]
  have hP := tdc_norm_proj_le (W := W) k
  have he1 : 0 ≤ e1 := (norm_nonneg _).trans hMR
  refine (norm_add_le _ _).trans (add_le_add ((tdm_norm_mul3_le _ _ _).trans ?_)
    ((tdm_norm_mul3_le _ _ _).trans ?_))
  · calc ‖Mb - R‖ * ‖tdcProj (W := W) k‖ * ‖Gb‖ ≤ e1 * 1 * g := by gcongr
    _ = e1 * g := by ring
  · calc ‖R‖ * ‖tdcProj (W := W) k‖ * ‖Gb - R‖ ≤ r0 * 1 * e2 := by gcongr
    _ = r0 * e2 := by ring

end Pieces

/-!
## 4. The closure of the differentiated mean system
-/

/-- The constant `A_Q = 2m²r + mr² + mr` of the coefficient comparison (`m = 2/η`, `r = 1/η`). -/
def tdmAQ (η : ℝ) : ℝ := 2 * (2 / η) ^ 2 * η⁻¹ + (2 / η) * η⁻¹ ^ 2 + (2 / η) * η⁻¹

/-- The smallness threshold `θ₀` of `tdm_core`. -/
def tdmTheta0 (b t η : ℝ) : ℝ :=
  min (min 1 (η / 2)) (min ((1 - b - t) / 4) ((1 - b - t) / (4 * (2 * η⁻¹ ^ 2 + 4 * tdmAQ η))))

theorem tdmAQ_pos {η : ℝ} (hη : 0 < η) : 0 < tdmAQ η := by unfold tdmAQ; positivity

theorem tdmTheta0_pos {b t η : ℝ} (ht : t < 1 - b) (hη : 0 < η) : 0 < tdmTheta0 b t η := by
  have := tdmAQ_pos hη
  have hg : 0 < 1 - b - t := by linarith
  unfold tdmTheta0
  exact lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity) (by positivity))

/-- The `e_Q` bound: `m θ r (2m) + r (m θ r + m ρ) ≤ A_Q (θ + ρ)`. -/
theorem tdm_eQ_le {η θ ρ : ℝ} (hη : 0 < η) (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) :
    2 / η * θ * η⁻¹ * (2 * (2 / η)) + η⁻¹ * (2 / η * θ * η⁻¹ + 2 / η * ρ) ≤
      tdmAQ η * (θ + ρ) := by
  unfold tdmAQ
  have e1 : 2 / η * θ * η⁻¹ * (2 * (2 / η)) + η⁻¹ * (2 / η * θ * η⁻¹ + 2 / η * ρ) =
      (2 * (2 / η) ^ 2 * η⁻¹ + 2 / η * η⁻¹ ^ 2) * θ + 2 / η * η⁻¹ * ρ := by ring
  rw [e1]
  have h1 : 0 ≤ 2 * (2 / η) ^ 2 * η⁻¹ + 2 / η * η⁻¹ ^ 2 := by positivity
  have h2 : 0 ≤ 2 / η * η⁻¹ := by positivity
  nlinarith only [mul_nonneg h2 hθ, mul_nonneg h1 hρ, h1, h2, hθ, hρ]

/-- The final arithmetic of `tdm_core`. -/
theorem tdm_final_arith {b gap θ ρ m ϑ u Dm eD w : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hgap : 0 < gap) (hθ0 : 0 ≤ θ) (hθg : θ ≤ gap / 4) (hρ0 : 0 ≤ ρ) (hm : 0 ≤ m) (hϑ : 0 ≤ ϑ)
    (hu : 0 ≤ u) (hDm : 0 ≤ Dm) (heD : eD = 15 * m * θ + 6 * ρ)
    (hw : w ≤ (b + θ) * ((Dm + eD * u + m * ϑ + b * (4 * m ^ 2) * (2 * ϑ)) / (b + gap / 2)) +
      2 * ϑ) :
    w ≤ (b + gap / 4) / (b + gap / 2) * Dm +
      max (15 * m + 6) (m + 8 * m ^ 2 + 2) * (θ + ρ) * u +
        max (15 * m + 6) (m + 8 * m ^ 2 + 2) * ϑ := by
  set q := (b + gap / 4) / (b + gap / 2) with hq
  set C := max (15 * m + 6) (m + 8 * m ^ 2 + 2) with hC
  have hden : 0 < b + gap / 2 := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hden]; linarith
  have heD0 : 0 ≤ eD := by rw [heD]; positivity
  set A := Dm + eD * u + m * ϑ + b * (4 * m ^ 2) * (2 * ϑ) with hA
  have hA0 : 0 ≤ A := by positivity
  have hbq : (b + θ) * (A / (b + gap / 2)) ≤ q * A := by
    rw [hq, ← mul_div_assoc, div_mul_eq_mul_div]
    gcongr
  have hC1 : 15 * m + 6 ≤ C := le_max_left _ _
  have hC2 : m + 8 * m ^ 2 + 2 ≤ C := le_max_right _ _
  have hθρ : 0 ≤ θ + ρ := by positivity
  have heDC : eD ≤ C * (θ + ρ) := by
    rw [heD]
    nlinarith only [mul_le_mul_of_nonneg_right hC1 hθρ, hθ0, hρ0, hm]
  have h1 : q * (eD * u) ≤ C * (θ + ρ) * u := by
    have : q * eD ≤ C * (θ + ρ) := by nlinarith only [heDC, hq1, heD0, hq0]
    nlinarith only [this, hu]
  have h2 : q * (m * ϑ + b * (4 * m ^ 2) * (2 * ϑ)) + 2 * ϑ ≤ C * ϑ := by
    have hb' : b * (4 * m ^ 2) * (2 * ϑ) ≤ 8 * m ^ 2 * ϑ := by
      have : b ≤ 1 := by linarith
      nlinarith only [this, sq_nonneg m, hϑ, hb0, mul_nonneg (sq_nonneg m) hϑ]
    have hsum0 : 0 ≤ m * ϑ + b * (4 * m ^ 2) * (2 * ϑ) := by positivity
    have : q * (m * ϑ + b * (4 * m ^ 2) * (2 * ϑ)) ≤ m * ϑ + b * (4 * m ^ 2) * (2 * ϑ) := by
      nlinarith only [hq1, hsum0, hq0]
    nlinarith only [mul_le_mul_of_nonneg_right hC2 hϑ, this, hb']
  have hqA : q * A = q * Dm + q * (eD * u) + q * (m * ϑ + b * (4 * m ^ 2) * (2 * ϑ)) := by
    rw [hA]; ring
  linarith

/-- **Closure of the differentiated mean system of one separate-port layer**.
Deterministic. `T Gb = 1 + Res` is the physical block of the exact mean equation at `h = 0`
(`Gb = (E𝒢)₁₁`, `T = tdmTop`); `T Gd = Rd - S Gb + diag(cv + bw) Gb` and
`(z - b gA_j) w_j = rp_j + b v_j gP_j` are the physical and port blocks of its `h`-derivative
(`Gd = (∂_h E𝒢)₁₁`, `v, w` the derivatives of the physical and port means, `Rd, rp` the
differentiated covariance residual). With the margin `t < 1 - b` of the strict contraction bound:
`|w_j| ≤ q max_i |D_i(X, Y)| + C(θ + ρ) u + C ϑ`, `q = (b + g/4)/(b + g/2) < 1`, `g = 1 - b - t`,
`C` after `η` only. -/
theorem tdm_core {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {t η : ℝ} (ht : t < 1 - b)
    (hη : 0 < η) :
    ∃ q C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
    ∀ {W : ℕ} (E : ℝ), |E| ≤ 2 → η ≤ (boundaryZ b E).im →
    ∀ (X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), X.IsHermitian → Y.PosSemidef →
    (∀ i, ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ *
      ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ ≤ t) →
    ∀ (gA gP v w rp : Fin 2 → ℂ) (Gb Gd Res Rd : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      (θ ρ ϑ : ℝ),
    (∀ i, ‖gA i - matchedA E‖ + ‖gP i - matchedA E‖ ≤ θ) → θ ≤ tdmTheta0 b t η →
    ‖Res‖ ≤ ρ → ρ ≤ tdmTheta0 b t η → ‖Rd‖ ≤ ϑ → (∀ j, ‖rp j‖ ≤ ϑ) →
    tdmTop b E X gA gP * Gb = 1 + Res →
    tdmTop b E X gA gP * Gd = Rd - (tdcK b E X)ᴴ * Y * tdcK b E X * Gb +
      diagonal (fun x : Fin 2 × Fin W => (1 - 2 * (b : ℂ)) * v x.1 + (b : ℂ) * w x.1) * Gb →
    (∀ i, v i = blockTrace Gd i) →
    (∀ j, (boundaryZ b E - (b : ℂ) * gA j) * w j = rp j + (b : ℂ) * v j * gP j) →
    ∀ j, ‖w j‖ ≤ q * tdcMaxD b E X Y + C * (θ + ρ) * clkTrace Y + C * ϑ := by
  set gap := 1 - b - t with hgap
  have hgap0 : 0 < gap := by rw [hgap]; linarith
  set m := 2 / η with hm
  set r0 := η⁻¹ with hr0
  have hm0 : 0 < m := by positivity
  have hr00 : 0 < r0 := by positivity
  refine ⟨(b + gap / 4) / (b + gap / 2), max (15 * m + 6) (m + 8 * m ^ 2 + 2), by positivity,
    by rw [div_lt_one (by positivity)]; linarith,
    (by positivity : (0 : ℝ) ≤ 15 * m + 6).trans (le_max_left _ _), ?_⟩
  intro W E hE2 hzη X Y hX hY hmargin gA gP v w rp Gb Gd Res Rd θ ρ ϑ hθ hθ0 hRes hρ0 hRd hrp
    hGb hGd hv hport j
  -- thresholds
  have hθ1 : θ ≤ 1 := hθ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθη : θ ≤ η / 2 := hθ0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hθg : θ ≤ gap / 4 := hθ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ1 : ρ ≤ 1 := hρ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθ0' : 0 ≤ θ := le_trans (by positivity) (hθ 0)
  have hρ0' : 0 ≤ ρ := (norm_nonneg _).trans hRes
  have hϑ0 : 0 ≤ ϑ := (norm_nonneg _).trans hRd
  have hAQ := tdmAQ_pos hη
  have hsmall : (2 * r0 ^ 2 + 4 * tdmAQ η) * (θ + ρ) ≤ gap / 2 := by
    have h1 : θ ≤ gap / (4 * (2 * η⁻¹ ^ 2 + 4 * tdmAQ η)) :=
      hθ0.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : ρ ≤ gap / (4 * (2 * η⁻¹ ^ 2 + 4 * tdmAQ η)) :=
      hρ0.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hpos : 0 < 2 * η⁻¹ ^ 2 + 4 * tdmAQ η := by positivity
    have h3 : θ + ρ ≤ 2 * (gap / (4 * (2 * η⁻¹ ^ 2 + 4 * tdmAQ η))) := by linarith
    calc (2 * r0 ^ 2 + 4 * tdmAQ η) * (θ + ρ) ≤
        (2 * η⁻¹ ^ 2 + 4 * tdmAQ η) * (2 * (gap / (4 * (2 * η⁻¹ ^ 2 + 4 * tdmAQ η)))) :=
          mul_le_mul_of_nonneg_left h3 hpos.le
      _ = gap / 2 := by field_simp; ring
  -- scalars
  set a := matchedA E with ha
  set z := boundaryZ b E with hz
  have ha1 : ‖a‖ = 1 := norm_matchedA hE2
  have hzpos : 0 < z.im := lt_of_lt_of_le hη hzη
  have hza : z = a⁻¹ + (b : ℂ) * a := rfl
  set c : ℂ := 1 - 2 * (b : ℂ) with hc
  have hcR : c = ((1 - 2 * b : ℝ) : ℂ) := by rw [hc]; push_cast; ring
  have hbn := tdm_norm_b hb0
  -- `K`, `R`, `T`, `M̄`
  set K := tdcK b E X with hK
  set R := K⁻¹ with hR
  have hKR : K * R = 1 := tdc_K_mul_inv hzpos hX
  have hRn : ‖R‖ ≤ r0 := (tdc_norm_Kinv_le hzpos hX).trans (inv_anti₀ hη hzη)
  have hRKs : ‖R * Kᴴ‖ ≤ 3 := tdc_norm_RKstar_le hzpos hX
  obtain ⟨hTu, hMn, hΔn⟩ := tdm_top_facts (W := W) hb0 hb1 hη hzη hX hθ hθη
  set Δ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := tdmDelta b E gA gP with hΔ
  set T := tdmTop b E X gA gP with hT
  have hTK : T = K - Δ := rfl
  set Mb := T⁻¹ with hMb
  have hMT : Mb * T = 1 := nonsing_inv_mul _ hTu
  have hTM : T * Mb = 1 := mul_nonsing_inv _ hTu
  have hθm : θ * m ≤ 1 := by
    rw [hm, show θ * (2 / η) = 2 * θ / η by ring, div_le_one hη]; linarith
  have hMR : Mb - R = Mb * Δ * R := by
    have : Mb * Δ * R = Mb * (K - T) * R := by rw [hTK]; abel_nf
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hKR, Matrix.mul_one, hMT,
      Matrix.one_mul]
  have hKM : K * Mb = 1 + Δ * Mb := by
    have : K = T + Δ := by rw [hTK]; abel
    rw [this, Matrix.add_mul, hTM]
  have hGbe : Gb = Mb * (1 + Res) := by
    rw [← hGb, ← Matrix.mul_assoc, hMT, Matrix.one_mul]
  have hGde : Gd = Mb * (Rd - Kᴴ * Y * K * Gb +
      diagonal (fun x : Fin 2 × Fin W => c * v x.1 + (b : ℂ) * w x.1) * Gb) := by
    rw [← hGd, ← Matrix.mul_assoc, hMT, Matrix.one_mul]
  have hMRn : ‖Mb - R‖ ≤ m * θ * r0 := by
    rw [hMR]; refine (tdm_norm_mul3_le _ _ _).trans ?_; gcongr
  have h1Res : ‖1 + Res‖ ≤ 1 + ρ := (norm_add_le _ _).trans (add_le_add lct_norm_one_le hRes)
  have hGbn : ‖Gb‖ ≤ 2 * m := by
    rw [hGbe]
    refine (norm_mul_le _ _).trans ?_
    calc ‖Mb‖ * ‖1 + Res‖ ≤ m * (1 + ρ) := mul_le_mul hMn h1Res (norm_nonneg _) hm0.le
      _ ≤ 2 * m := by nlinarith only [hρ1, hm0]
  have hGbR : ‖Gb - R‖ ≤ m * θ * r0 + m * ρ := by
    have e : Gb - R = (Mb - R) + Mb * Res := by
      rw [hGbe, Matrix.mul_add, Matrix.mul_one]; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add hMRn ((norm_mul_le _ _).trans
      (mul_le_mul hMn hRes (norm_nonneg _) hm0.le)))
  -- the linear system
  set Dt : Fin 2 → ℂ := fun i => blockTrace (Mb * (Kᴴ * Y * K) * Gb) i with hDt
  set Qt : Fin 2 → Fin 2 → ℂ := fun i k => blockTrace (Mb * tdcProj k * Gb) i with hQt
  set f : Fin 2 → ℂ := fun i => blockTrace (Mb * Rd) i with hf
  have hps := fun j => tdm_port_scalars (gA := gA j) (gP := gP j) ha1 hb0 hb1 hθ1 (hθ j)
  set pc : Fin 2 → ℂ := fun j => z - (b : ℂ) * gA j with hpc
  have hpcb : ∀ j, 1 / 2 ≤ ‖pc j‖ := fun j => (hps j).1
  have hpc0 : ∀ j, pc j ≠ 0 := fun j h => by
    have := hpcb j; rw [h, norm_zero] at this; linarith
  set β : Fin 2 → ℂ := fun j => (b : ℂ) * gP j / pc j with hβ
  set r : Fin 2 → ℂ := fun j => rp j / pc j with hr
  have hwsys : ∀ j, w j = β j * v j + r j := by
    intro j
    have h := hport j
    change pc j * w j = _ at h
    simp only [hβ, hr]
    field_simp [hpc0 j]
    linear_combination h
  have hvsys : ∀ i, v i = -Dt i + (Qt i 0 * (c * v 0 + (b : ℂ) * w 0) +
      Qt i 1 * (c * v 1 + (b : ℂ) * w 1)) + f i := by
    intro i
    rw [hv i, hGde, tdm_diagonal_eq (W := W) (fun k => c * v k + (b : ℂ) * w k)]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
      tdm_blockTrace_add, tdm_blockTrace_sub, tdm_blockTrace_smul, hDt, hQt, hf]
    simp only [Matrix.mul_assoc]
    ring
  -- bounds for `tdm_close`
  have hrb : ∀ j, ‖r j‖ ≤ 2 * ϑ := by
    intro j
    simp only [hr]
    rw [norm_div, div_le_iff₀ (by linarith [hpcb j])]
    nlinarith only [hrp j, hpcb j, hϑ0]
  have hβa : ∀ j, ‖β j - (b : ℂ) * a ^ 2‖ ≤ θ := fun j => (hps j).2
  have hβb : ∀ j, ‖β j‖ ≤ b + θ := by
    intro j
    have h1 : ‖(b : ℂ) * a ^ 2‖ = b := by rw [norm_mul, norm_pow, ha1, hbn]; ring
    calc ‖β j‖ = ‖(β j - (b : ℂ) * a ^ 2) + (b : ℂ) * a ^ 2‖ := by rw [sub_add_cancel]
      _ ≤ θ + b := (norm_add_le _ _).trans (by rw [h1]; linarith [hβa j])
      _ = b + θ := by ring
  set c0 : ℂ := ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * a ^ 2 with hc0
  have hc01 : ‖c0‖ ≤ 1 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_mul, norm_pow, norm_pow, hbn,
      ha1]
    nlinarith only [hb0, hb1]
  have hcβ : ∀ k, ‖c + (b : ℂ) * β k‖ ≤ ‖c0‖ + θ := by
    intro k
    have e : c + (b : ℂ) * β k = c0 + (b : ℂ) * (β k - (b : ℂ) * a ^ 2) := by
      rw [hc0, hcR]; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul, hbn]
    have h1 := hβa k
    have h2 := norm_nonneg (β k - (b : ℂ) * a ^ 2)
    nlinarith only [h1, h2, hb0, hb1, hθ0']
  set eQ := m * θ * r0 * (2 * m) + r0 * (m * θ * r0 + m * ρ) with heQ
  have hQQ : ∀ i k, ‖Qt i k - blockPairTrace R i k‖ ≤ eQ := fun i k =>
    tdm_Qt_le hr00.le hMRn hGbn hGbR hRn i k
  have heQb : eQ ≤ tdmAQ η * (θ + ρ) := tdm_eQ_le hη hθ0' hρ0'
  have hQn : ∀ i k, ‖blockPairTrace R i k‖ ≤ r0 ^ 2 := by
    intro i k
    rw [tdm_blockPairTrace_eq]
    refine (lct_norm_blockTrace_le _ _).trans ((tdm_norm_mul3_le _ _ _).trans ?_)
    have := tdc_norm_proj_le (W := W) k
    calc ‖R‖ * ‖tdcProj (W := W) k‖ * ‖R‖ ≤ r0 * 1 * r0 := by gcongr
      _ = r0 ^ 2 := by ring
  have hmar : ∀ i, ‖c0‖ * (‖blockPairTrace R i 0‖ + ‖blockPairTrace R i 1‖) ≤ t := by
    intro i
    have := hmargin i
    rw [Fin.sum_univ_two] at this
    exact this
  have heQ0 : 0 ≤ eQ := by simp only [heQ]; positivity
  have hrow : ∀ i, ‖Qt i 0‖ * ‖c + (b : ℂ) * β 0‖ + ‖Qt i 1‖ * ‖c + (b : ℂ) * β 1‖ ≤
      t + gap / 2 := by
    intro i
    have hq0' : ‖Qt i 0‖ ≤ ‖blockPairTrace R i 0‖ + eQ := by
      have := norm_le_norm_add_norm_sub' (Qt i 0) (blockPairTrace R i 0)
      linarith [hQQ i 0]
    have hq1' : ‖Qt i 1‖ ≤ ‖blockPairTrace R i 1‖ + eQ := by
      have := norm_le_norm_add_norm_sub' (Qt i 1) (blockPairTrace R i 1)
      linarith [hQQ i 1]
    have hc0n := norm_nonneg c0
    have hb00 := norm_nonneg (blockPairTrace R i 0)
    have hb01 := norm_nonneg (blockPairTrace R i 1)
    calc ‖Qt i 0‖ * ‖c + (b : ℂ) * β 0‖ + ‖Qt i 1‖ * ‖c + (b : ℂ) * β 1‖
        ≤ (‖blockPairTrace R i 0‖ + eQ) * (‖c0‖ + θ) +
            (‖blockPairTrace R i 1‖ + eQ) * (‖c0‖ + θ) := by
          gcongr
          · exact hcβ 0
          · exact hcβ 1
      _ = ‖c0‖ * (‖blockPairTrace R i 0‖ + ‖blockPairTrace R i 1‖) +
            θ * (‖blockPairTrace R i 0‖ + ‖blockPairTrace R i 1‖) + 2 * eQ * (‖c0‖ + θ) := by ring
      _ ≤ t + θ * (2 * r0 ^ 2) + 2 * eQ * 2 := by
          gcongr
          · exact hmar i
          · linarith [hQn i 0, hQn i 1]
          · linarith
      _ ≤ t + gap / 2 := by
          nlinarith only [hsmall, heQb, hθ0', hρ0', hr00]
  have hQsb : ∀ i, ‖Qt i 0‖ + ‖Qt i 1‖ ≤ 4 * m ^ 2 := by
    intro i
    have hk : ∀ k, ‖Qt i k‖ ≤ 2 * m ^ 2 := by
      intro k
      simp only [hQt]
      refine (lct_norm_blockTrace_le _ _).trans ((tdm_norm_mul3_le _ _ _).trans ?_)
      have := tdc_norm_proj_le (W := W) k
      calc ‖Mb‖ * ‖tdcProj (W := W) k‖ * ‖Gb‖ ≤ m * 1 * (2 * m) := by gcongr
        _ = 2 * m ^ 2 := by ring
    linarith [hk 0, hk 1]
  set eD := 15 * m * θ + 6 * ρ with heD
  have hDt' : ∀ i, ‖Dt i‖ ≤ tdcMaxD b E X Y + eD * clkTrace Y := by
    intro i
    have hdiff := tdm_Dt_le hY hm0.le hθ0' hρ0' hθm hρ1 hKR hMR hKM hGbe hMn hΔn hRKs hRes i
    have hD : blockTrace (R * (Kᴴ * Y * K) * R) i = tdcD b E X Y i := rfl
    have hDmax : ‖tdcD b E X Y i‖ ≤ tdcMaxD b E X Y := by
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
    rw [hD] at hdiff
    calc ‖Dt i‖ = ‖(Dt i - tdcD b E X Y i) + tdcD b E X Y i‖ := by rw [sub_add_cancel]
      _ ≤ eD * clkTrace Y + tdcMaxD b E X Y := (norm_add_le _ _).trans (add_le_add hdiff hDmax)
      _ = _ := by ring
  have hfb : ∀ i, ‖f i‖ ≤ m * ϑ := by
    intro i
    simp only [hf]
    exact (lct_norm_blockTrace_le _ _).trans ((norm_mul_le _ _).trans
      (mul_le_mul hMn hRd (norm_nonneg _) hm0.le))
  -- close
  have ht'1 : t + gap / 2 < 1 := by rw [hgap]; linarith
  have hfin := tdm_close (c := c) (bc := (b : ℂ)) ht'1 hvsys hwsys hrow hQsb hβb hDt' hfb hrb j
  rw [hbn, show 1 - (t + gap / 2) = b + gap / 2 by rw [hgap]; ring] at hfin
  have hfin' : ‖w j‖ ≤ (b + θ) * ((tdcMaxD b E X Y + eD * clkTrace Y + m * ϑ +
      b * (4 * m ^ 2) * (2 * ϑ)) / (b + gap / 2)) + 2 * ϑ := by
    refine hfin.trans (le_of_eq ?_); ring
  exact tdm_final_arith hb0 hb1 hgap0 hθ0' hθg hρ0' hm0.le hϑ0 (clkTrace_nonneg hY)
    (tdcMaxD_nonneg b E X Y) heD hfin'
