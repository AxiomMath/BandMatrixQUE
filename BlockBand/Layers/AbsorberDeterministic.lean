module

public import Mathlib

/-!
# The deterministic absorber inverse bound

Setting: complex inner-product spaces `E` (physical coordinates) and `F` (ports), a
self-adjoint `D` on `E` (`D = A - E - X`), a coupling `Bs = B* : E → F` with `‖B*‖ ≤ K`, a
linear map `P` on `E` (in the application, the spectral projection onto the eigenvectors of `D`
nearest zero), and `w = -z⁻¹` with `γ = Im w > 0`. The two hypotheses are exactly the defining
properties of `δ` and `d`:
* `δ ‖v - Pv‖ ≤ ‖D v‖` (on the complement of `Ran P`, `|D| ≥ δ`);
* `d ‖P v‖ ≤ ‖B* P v‖` (`d ≤ s_min(B*|_{Ran P})`).
Then for every `v`, `(dδ)² / (C₀² (1+K)⁴) ‖v‖ ≤ ‖(D + w B B*) v‖` with
`C₀ = γ^{-1/2} + 1 + |w| γ^{-1/2}`, whenever `0 < d ≤ 1`, `0 < δ ≤ 1`, `0 ≤ K`.
Since `D - z⁻¹ B B* = D + w B B*`, this is the deterministic absorber bound with an explicit constant.
No dimension, no probability and no norm bound on `D` enter.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The constant `C₀ = γ^{-1/2} + 1 + |w| γ^{-1/2}`, `γ = Im w`. -/
def absorberConstant (w : ℂ) : ℝ :=
  (Real.sqrt w.im)⁻¹ + 1 + ‖w‖ * (Real.sqrt w.im)⁻¹

theorem one_le_absorberConstant (w : ℂ) : 1 ≤ absorberConstant w := by
  unfold absorberConstant
  have h1 : 0 ≤ (Real.sqrt w.im)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h2 : 0 ≤ ‖w‖ * (Real.sqrt w.im)⁻¹ := mul_nonneg (norm_nonneg _) h1
  linarith

/-- Imaginary quadratic form: `Im ⟨v, (D + w B B*) v⟩ = Im w · ‖B* v‖²` for self-adjoint `D`. -/
theorem im_inner_absorber (D : E →L[ℂ] E) (hD : IsSelfAdjoint D) (Bs : E →L[ℂ] F) (w : ℂ)
    (v : E) :
    (⟪v, (D + w • ((ContinuousLinearMap.adjoint Bs).comp Bs)) v⟫_ℂ).im = w.im * ‖Bs v‖ ^ 2 := by
  have hDv : (⟪v, D v⟫_ℂ).im = 0 := by
    have hsym : ⟪D v, v⟫_ℂ = ⟪v, D v⟫_ℂ := hD.isSymmetric v v
    have hc : (starRingEnd ℂ) ⟪v, D v⟫_ℂ = ⟪v, D v⟫_ℂ := by
      rw [inner_conj_symm]; exact hsym
    have := congrArg Complex.im hc
    simp only [Complex.conj_im] at this
    linarith
  have hB : ⟪v, (ContinuousLinearMap.adjoint Bs) (Bs v)⟫_ℂ = ((‖Bs v‖ ^ 2 : ℝ) : ℂ) := by
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hTv : (D + w • ((ContinuousLinearMap.adjoint Bs).comp Bs)) v =
      D v + w • (ContinuousLinearMap.adjoint Bs) (Bs v) := rfl
  rw [hTv, inner_add_right, inner_smul_right, hB, Complex.add_im, hDv, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The scalar combination step of the deterministic absorber bound: from
`√γ x ≤ s`, `δ y ≤ ε + |w| K x`, `d p ≤ x + K y`, `1 ≤ p + y`, `ε ≤ s`, conclude
`dδ ≤ C₀ (1+K)² s`. -/
theorem absorber_scalar (w : ℂ) (hw : 0 < w.im) (d δ K x y q ε s : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y) (_hq : 0 ≤ q)
    (_hε : 0 ≤ ε) (hs : 0 ≤ s)
    (h1 : Real.sqrt w.im * x ≤ s) (h2 : δ * y ≤ ε + ‖w‖ * K * x) (h3 : d * q ≤ x + K * y)
    (h4 : 1 ≤ q + y) (h5 : ε ≤ s) :
    d * δ ≤ absorberConstant w * (1 + K) ^ 2 * s := by
  set r := Real.sqrt w.im with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hw
  set u := r⁻¹ * s with hu
  have hxu : x ≤ u := by
    rw [hu, le_inv_mul_iff₀ hr0]; linarith
  have hu0 : 0 ≤ u := by positivity
  have hW : 0 ≤ ‖w‖ := norm_nonneg _
  -- `dδ ≤ δ (d q) + d (δ y)`
  have step1 : d * δ ≤ δ * (d * q) + d * (δ * y) := by
    have h := mul_le_mul_of_nonneg_left h4 (mul_pos hd hδ).le
    calc d * δ = d * δ * 1 := by ring
      _ ≤ d * δ * (q + y) := h
      _ = δ * (d * q) + d * (δ * y) := by ring
  have step2 : δ * (d * q) ≤ x + K * (δ * y) := by
    have : δ * (d * q) ≤ δ * (x + K * y) := mul_le_mul_of_nonneg_left h3 hδ.le
    nlinarith
  have step3 : d * (δ * y) ≤ δ * y := by
    have : 0 ≤ δ * y := by positivity
    nlinarith
  have hδy : δ * y ≤ s + ‖w‖ * K * u := by
    have : ‖w‖ * K * x ≤ ‖w‖ * K * u := by
      apply mul_le_mul_of_nonneg_left hxu; positivity
    linarith
  have total : d * δ ≤ u + (1 + K) * (s + ‖w‖ * K * u) := by
    have hKδy : K * (δ * y) ≤ K * (s + ‖w‖ * K * u) := mul_le_mul_of_nonneg_left hδy hK
    nlinarith
  have hC : absorberConstant w * (1 + K) ^ 2 * s =
      (1 + K) ^ 2 * u + (1 + K) ^ 2 * s + ‖w‖ * (1 + K) ^ 2 * u := by
    unfold absorberConstant; rw [hu]; ring
  rw [hC]
  have hK2 : 1 + K ≤ (1 + K) ^ 2 := by nlinarith
  have e1 : u ≤ (1 + K) ^ 2 * u := by nlinarith
  have e2 : (1 + K) * s ≤ (1 + K) ^ 2 * s := by nlinarith
  have e3 : (1 + K) * (‖w‖ * K * u) ≤ ‖w‖ * (1 + K) ^ 2 * u := by
    have : (1 + K) * K ≤ (1 + K) ^ 2 := by nlinarith
    have h0 : 0 ≤ ‖w‖ * u := by positivity
    nlinarith
  nlinarith

/-- The deterministic absorber bound for a unit vector. -/
theorem absorber_lower_unit (D : E →L[ℂ] E) (hD : IsSelfAdjoint D) (Bs : E →L[ℂ] F)
    (P : E →L[ℂ] E) (w : ℂ) (hw : 0 < w.im) (d δ K : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : ‖Bs‖ ≤ K)
    (hPD : ∀ v, δ * ‖v - P v‖ ≤ ‖D v‖) (hPB : ∀ v, d * ‖P v‖ ≤ ‖Bs (P v)‖)
    (v : E) (hv : ‖v‖ = 1) :
    (d * δ) ^ 2 / (absorberConstant w ^ 2 * (1 + K) ^ 4) ≤
      ‖(D + w • ((ContinuousLinearMap.adjoint Bs).comp Bs)) v‖ := by
  set T := D + w • ((ContinuousLinearMap.adjoint Bs).comp Bs) with hT
  set ε := ‖T v‖ with hε
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hK
  have hC1 := one_le_absorberConstant w
  have hden : 0 < absorberConstant w ^ 2 * (1 + K) ^ 4 := by positivity
  rw [div_le_iff₀ hden]
  by_cases hε1 : 1 ≤ ε
  · have hnum : (d * δ) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ d * δ := by positivity
      have : d * δ ≤ 1 := by nlinarith
      nlinarith
    have hden1 : 1 ≤ absorberConstant w ^ 2 * (1 + K) ^ 4 := by
      have h1 : 1 ≤ absorberConstant w ^ 2 := by nlinarith
      have h2 : 1 ≤ (1 + K) ^ 4 := one_le_pow₀ (by linarith)
      nlinarith
    nlinarith
  rw [not_le] at hε1
  have hε0 : 0 ≤ ε := norm_nonneg _
  set s := Real.sqrt ε with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = ε := Real.sq_sqrt hε0
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sqrt_le_one.mpr hε1.le
  have hεs : ε ≤ s := by nlinarith
  -- (1) `√γ ‖B* v‖ ≤ s`
  have h1 : Real.sqrt w.im * ‖Bs v‖ ≤ s := by
    have him := im_inner_absorber D hD Bs w v
    have hle : w.im * ‖Bs v‖ ^ 2 ≤ ε := by
      rw [← him]
      calc (⟪v, T v⟫_ℂ).im ≤ ‖⟪v, T v⟫_ℂ‖ := Complex.im_le_norm _
        _ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm _ _
        _ = ε := by rw [hv, one_mul]
    have hsq : (Real.sqrt w.im * ‖Bs v‖) ^ 2 ≤ s ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hw.le, hss]; exact hle
    have h0 : 0 ≤ Real.sqrt w.im * ‖Bs v‖ := by positivity
    nlinarith
  -- (2) `‖D v‖ ≤ ε + |w| K ‖B* v‖`
  have h2 : ‖D v‖ ≤ ε + ‖w‖ * K * ‖Bs v‖ := by
    have hDv : D v = T v - w • (ContinuousLinearMap.adjoint Bs) (Bs v) := by
      simp [hT]
    have hadj : ‖(ContinuousLinearMap.adjoint Bs) (Bs v)‖ ≤ K * ‖Bs v‖ := by
      calc ‖(ContinuousLinearMap.adjoint Bs) (Bs v)‖
          ≤ ‖ContinuousLinearMap.adjoint Bs‖ * ‖Bs v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * ‖Bs v‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [LinearIsometryEquiv.norm_map]; exact hK
    calc ‖D v‖ = ‖T v - w • (ContinuousLinearMap.adjoint Bs) (Bs v)‖ := by rw [hDv]
      _ ≤ ‖T v‖ + ‖w • (ContinuousLinearMap.adjoint Bs) (Bs v)‖ := norm_sub_le _ _
      _ = ε + ‖w‖ * ‖(ContinuousLinearMap.adjoint Bs) (Bs v)‖ := by rw [norm_smul]
      _ ≤ ε + ‖w‖ * (K * ‖Bs v‖) := by gcongr
      _ = ε + ‖w‖ * K * ‖Bs v‖ := by ring
  -- (3) `d ‖P v‖ ≤ ‖B* v‖ + K ‖v - P v‖`
  have h3 : d * ‖P v‖ ≤ ‖Bs v‖ + K * ‖v - P v‖ := by
    have : Bs (P v) = Bs v - Bs (v - P v) := by simp
    calc d * ‖P v‖ ≤ ‖Bs (P v)‖ := hPB v
      _ = ‖Bs v - Bs (v - P v)‖ := by rw [this]
      _ ≤ ‖Bs v‖ + ‖Bs (v - P v)‖ := norm_sub_le _ _
      _ ≤ ‖Bs v‖ + K * ‖v - P v‖ := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  -- (4) `1 ≤ ‖P v‖ + ‖v - P v‖`
  have h4 : 1 ≤ ‖P v‖ + ‖v - P v‖ := by
    rw [← hv]
    calc ‖v‖ = ‖P v + (v - P v)‖ := by rw [add_sub_cancel]
      _ ≤ ‖P v‖ + ‖v - P v‖ := norm_add_le _ _
  have hmain := absorber_scalar w hw d δ K ‖Bs v‖ ‖v - P v‖ ‖P v‖ ε s hd hd1 hδ hδ1 hK0
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hε0 hs0 h1 ((hPD v).trans h2) h3 h4 hεs
  have h0 : 0 ≤ d * δ := by positivity
  have hsq : (d * δ) ^ 2 ≤ (absorberConstant w * (1 + K) ^ 2 * s) ^ 2 := by
    exact pow_le_pow_left₀ h0 hmain 2
  calc (d * δ) ^ 2 ≤ (absorberConstant w * (1 + K) ^ 2 * s) ^ 2 := hsq
    _ = ε * (absorberConstant w ^ 2 * (1 + K) ^ 4) := by rw [← hss]; ring

/-- **The deterministic absorber bound**. For every `v`,
`(dδ)² / (C₀² (1+K)⁴) ‖v‖ ≤ ‖(D + w B B*) v‖`, with `w = -z⁻¹`, `Im w > 0`, `D` self-adjoint,
`‖B*‖ ≤ K`, and `δ, d ∈ (0,1]` as in the module docstring. Equivalently
`‖(D - z⁻¹ B B*)⁻¹‖ ≤ C₀² (1+K)⁴ d⁻² δ⁻²`. Deterministic; uniform in the dimension and in `D`. -/
theorem absorber_lower (D : E →L[ℂ] E) (hD : IsSelfAdjoint D) (Bs : E →L[ℂ] F)
    (P : E →L[ℂ] E) (w : ℂ) (hw : 0 < w.im) (d δ K : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : ‖Bs‖ ≤ K)
    (hPD : ∀ v, δ * ‖v - P v‖ ≤ ‖D v‖) (hPB : ∀ v, d * ‖P v‖ ≤ ‖Bs (P v)‖) (v : E) :
    (d * δ) ^ 2 / (absorberConstant w ^ 2 * (1 + K) ^ 4) * ‖v‖ ≤
      ‖(D + w • ((ContinuousLinearMap.adjoint Bs).comp Bs)) v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hun : ‖(‖v‖⁻¹ : ℂ) • v‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hnv.le,
      inv_mul_cancel₀ hnv.ne']
  have hmain := absorber_lower_unit D hD Bs P w hw d δ K hd hd1 hδ hδ1 hK hPD hPB _ hun
  have hTu : ‖(D + w • ((ContinuousLinearMap.adjoint Bs).comp Bs)) ((‖v‖⁻¹ : ℂ) • v)‖ =
      ‖v‖⁻¹ * ‖(D + w • ((ContinuousLinearMap.adjoint Bs).comp Bs)) v‖ := by
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hnv.le]
  rw [hTu] at hmain
  calc (d * δ) ^ 2 / (absorberConstant w ^ 2 * (1 + K) ^ 4) * ‖v‖
      ≤ ‖v‖⁻¹ * ‖(D + w • ((ContinuousLinearMap.adjoint Bs).comp Bs)) v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right hmain hnv.le
    _ = ‖(D + w • ((ContinuousLinearMap.adjoint Bs).comp Bs)) v‖ := by
        field_simp

end BlockBand.Layers
