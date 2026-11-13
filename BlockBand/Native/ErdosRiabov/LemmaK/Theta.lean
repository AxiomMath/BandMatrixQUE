module

public import BlockBand.Native.ErdosRiabov.LemmaK.CF1
public import BlockBand.Native.ErdosRiabov.Kernel.VSKernelExtra

/-!
# Scaling of the VS kernels to the kernels of the admissibility theorem

Deterministic: no measure occurs.

For `t ∈ (0,1]` and nonreal `z`, `lemmaKPoint z t = w_t = (z + (1-t)m(z))/√t` (local name for the
point of the VS trajectory). With `semicircleM_vsScale`,
`m(w_t) = √t m(z)`, so for nonreal `z, z'` and any real `N × N` matrix `S`:

* `theta_vsScale`: `theta S w_t w'_t = t • A_t(z, z̄') = t • vsKernel S m(z) conj(m(z')) t`;
* `xi_vsScale`: `xi S w_t w'_t = t • A_t(z, z') = t • vsKernel S m(z) m(z') t`;
* `lemmaKPoint_domain`: for `z, z' ∈ 𝒟` (`BulkDomain N δ₀ κ C₀`, `N ≥ 1`, `κ > 0`),
  `t ∈ [1/4, 1]` and a record `q` with `q.δ₀ = δ₀`, `q.κ ≤ min κ 1`, `2(C₀+1) ≤ q.C₀`:
  `w_t, w'_t ∈ SpectralDomain q N`, both in the upper half-plane, and
  `min |Im w_t| |Im w'_t| = η_t/√t ∈ [η_t, 2η_t]` with `η_t = min (vsHeight z t) (vsHeight z' t)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.LemmaK

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open scoped BigOperators ComplexConjugate

/-- The rescaled VS point `w_t = z_t/√t`, `z_t = z + (1-t) m(z)`. -/
def lemmaKPoint (z : ℂ) (t : ℝ) : ℂ :=
  (z + (1 - (t : ℂ)) * semicircleM z) / (Real.sqrt t : ℂ)

/-- `m(w_t) = √t m(z)` (`semicircleM_vsScale` restated for `lemmaKPoint`). -/
theorem semicircleM_lemmaKPoint {z : ℂ} (hz : z.im ≠ 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    semicircleM (lemmaKPoint z t) = (Real.sqrt t : ℂ) * semicircleM z :=
  semicircleM_vsScale hz ht0 ht1

/-- `Im w_t = η_t(z)/√t` (every `z`, `t`). -/
theorem lemmaKPoint_im (z : ℂ) (t : ℝ) : (lemmaKPoint z t).im = vsHeight z t / Real.sqrt t :=
  vsScale_im z t

private theorem lemmaK_sqrt_mul_self {t : ℝ} (ht0 : 0 ≤ t) :
    (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht0]

/-- **Scaling of `theta`.** For every real `S`, nonreal `z, z'` and
`t ∈ (0,1]`: `theta S w_t w'_t = t • A_t(z, z̄')`, where `A_t(z, z̄') = vsKernel S m(z)
conj(m(z')) t = Y(1-tY)⁻¹`, `Y = m(z) conj(m(z')) S`. -/
theorem theta_vsScale {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) {z z' : ℂ} (hz : z.im ≠ 0)
    (hz' : z'.im ≠ 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ErdosRiabov.theta S (lemmaKPoint z t) (lemmaKPoint z' t) =
      (t : ℂ) • vsKernel S (semicircleM z) (conj (semicircleM z')) t := by
  have hA : (semicircleM (lemmaKPoint z t) * conj (semicircleM (lemmaKPoint z' t))) •
      S.map (algebraMap ℝ ℂ) = (t : ℂ) • vsY S (semicircleM z) (conj (semicircleM z')) := by
    rw [semicircleM_lemmaKPoint hz ht0 ht1, semicircleM_lemmaKPoint hz' ht0 ht1, smul_vsY]
    congr 1
    rw [map_mul, Complex.conj_ofReal]
    linear_combination (semicircleM z * conj (semicircleM z')) * lemmaK_sqrt_mul_self ht0.le
  dsimp only [ErdosRiabov.theta]
  rw [hA, vsKernel, Matrix.smul_mul]

/-- **Scaling of `xi`.** For every real `S`, nonreal `z, z'` and
`t ∈ (0,1]`: `xi S w_t w'_t = t • A_t(z, z')`, `A_t(z, z') = vsKernel S m(z) m(z') t`. -/
theorem xi_vsScale {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) {z z' : ℂ} (hz : z.im ≠ 0)
    (hz' : z'.im ≠ 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ErdosRiabov.xi S (lemmaKPoint z t) (lemmaKPoint z' t) =
      (t : ℂ) • vsKernel S (semicircleM z) (semicircleM z') t := by
  have hA : (semicircleM (lemmaKPoint z t) * semicircleM (lemmaKPoint z' t)) •
      S.map (algebraMap ℝ ℂ) = (t : ℂ) • vsY S (semicircleM z) (semicircleM z') := by
    rw [semicircleM_lemmaKPoint hz ht0 ht1, semicircleM_lemmaKPoint hz' ht0 ht1, smul_vsY]
    congr 1
    linear_combination (semicircleM z * semicircleM z') * lemmaK_sqrt_mul_self ht0.le
  dsimp only [ErdosRiabov.xi]
  rw [hA, vsKernel, Matrix.smul_mul]

/-- `vsHeight z t > 0` for `Im z > 0`, `t ≤ 1`. -/
theorem lemmaK_vsHeight_pos {z : ℂ} (hη : 0 < z.im) {t : ℝ} (ht1 : t ≤ 1) :
    0 < vsHeight z t := by
  have hy := semicircleM_im_pos hη
  unfold vsHeight
  nlinarith

/-- `Im z ≤ vsHeight z t` for `Im z > 0`, `t ≤ 1`. -/
theorem lemmaK_im_le_vsHeight {z : ℂ} (hη : 0 < z.im) {t : ℝ} (ht1 : t ≤ 1) :
    z.im ≤ vsHeight z t := by
  have hy := semicircleM_im_pos hη
  unfold vsHeight
  nlinarith

private theorem lemmaK_half_le_sqrt {t : ℝ} (ht : 1 / 4 ≤ t) : 1 / 2 ≤ Real.sqrt t := by
  have h := Real.sqrt_le_sqrt ht
  rwa [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h

/-- Single-point domain membership: for `z ∈ 𝒟`, `κ > 0`, `N ≥ 1`,
`t ∈ [1/4, 1]` and `q` with `q.δ₀ = δ₀`, `q.κ ≤ min κ 1`, `2(C₀+1) ≤ q.C₀`:
`w_t ∈ SpectralDomain q N`. -/
theorem lemmaKPoint_spectralDomain {N : ℕ} (hN : 0 < N) {δ₀ κ C₀ : ℝ} (hκ : 0 < κ) {z : ℂ}
    (hz : BulkDomain N δ₀ κ C₀ z) (q : ErdosRiabov.ModelParameters) (hqδ : q.delta0 = δ₀)
    (hqκ : q.kappa ≤ phaseConst κ) (hqC : 2 * (C₀ + 1) ≤ q.C0) {t : ℝ} (ht : 1 / 4 ≤ t)
    (ht1 : t ≤ 1) : ErdosRiabov.SpectralDomain q N (lemmaKPoint z t) := by
  have hη := hz.im_pos hN
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
  have hsth := lemmaK_half_le_sqrt ht
  have hhpos := lemmaK_vsHeight_pos hη ht1
  have hm1 := norm_semicircleM_lt_one hη.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [lemmaKPoint_im, abs_of_pos (div_pos hhpos hst), hqδ]
    calc (N : ℝ) ^ (-1 + δ₀) ≤ z.im := hz.2.1
      _ ≤ vsHeight z t := lemmaK_im_le_vsHeight hη ht1
      _ ≤ vsHeight z t / Real.sqrt t := le_div_self hhpos.le hst hst1
  · have hC0 : 0 ≤ C₀ := (norm_nonneg z).trans hz.2.2
    have h1t : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    have hnum : ‖z + (1 - (t : ℂ)) * semicircleM z‖ ≤ C₀ + 1 := by
      calc ‖z + (1 - (t : ℂ)) * semicircleM z‖
          ≤ ‖z‖ + ‖(1 : ℂ) - (t : ℂ)‖ * ‖semicircleM z‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
        _ = ‖z‖ + (1 - t) * ‖semicircleM z‖ := by
            rw [h1t, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        _ ≤ C₀ + 1 := by nlinarith [norm_nonneg (semicircleM z), hz.2.2]
    rw [lemmaKPoint, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hst]
    rw [div_le_iff₀ hst]
    nlinarith
  · rw [semicircleM_lemmaKPoint hη.ne' ht0 ht1]
    have hm0 : semicircleM z ≠ 0 := Kernel.ne_zero_of_root (semicircleM_dyson z)
    have hnorm : ((‖(Real.sqrt t : ℂ) * semicircleM z‖ : ℝ) : ℂ) =
        (Real.sqrt t : ℂ) * ((‖semicircleM z‖ : ℝ) : ℂ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hst, Complex.ofReal_mul]
    have hsc : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hst.ne'
    rw [hnorm, mul_div_mul_left _ _ hsc]
    exact hqκ.trans (semicircleM_phase_ge hκ hz.1 hη)

/-- **The rescaled points lie in the spectral domain.** For `N ≥ 1`, `κ > 0`,
`z, z' ∈ 𝒟` (`BulkDomain N δ₀ κ C₀`), a record `q` with `q.δ₀ = δ₀`, `q.κ ≤ min κ 1`,
`2(C₀+1) ≤ q.C₀`, and `t ∈ [1/4, 1]`: `w_t, w'_t ∈ SpectralDomain q N`, they lie in the same
(upper) half-plane, and `min |Im w_t| |Im w'_t| = η_t/√t ∈ [η_t, 2η_t]` with
`η_t = min (vsHeight z t) (vsHeight z' t)`. -/
theorem lemmaKPoint_domain {N : ℕ} (hN : 0 < N) {δ₀ κ C₀ : ℝ} (hκ : 0 < κ) {z z' : ℂ}
    (hz : BulkDomain N δ₀ κ C₀ z) (hz' : BulkDomain N δ₀ κ C₀ z')
    (q : ErdosRiabov.ModelParameters) (hqδ : q.delta0 = δ₀) (hqκ : q.kappa ≤ phaseConst κ)
    (hqC : 2 * (C₀ + 1) ≤ q.C0) {t : ℝ} (ht : 1 / 4 ≤ t) (ht1 : t ≤ 1) :
    ErdosRiabov.SpectralDomain q N (lemmaKPoint z t) ∧
    ErdosRiabov.SpectralDomain q N (lemmaKPoint z' t) ∧
    ErdosRiabov.SameHalfPlane (lemmaKPoint z t) (lemmaKPoint z' t) ∧
    min |(lemmaKPoint z t).im| |(lemmaKPoint z' t).im| =
      min (vsHeight z t) (vsHeight z' t) / Real.sqrt t ∧
    min (vsHeight z t) (vsHeight z' t) ≤ min |(lemmaKPoint z t).im| |(lemmaKPoint z' t).im| ∧
    min |(lemmaKPoint z t).im| |(lemmaKPoint z' t).im| ≤
      2 * min (vsHeight z t) (vsHeight z' t) := by
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
  have hsth := lemmaK_half_le_sqrt ht
  have h1 := lemmaK_vsHeight_pos (hz.im_pos hN) ht1
  have h2 := lemmaK_vsHeight_pos (hz'.im_pos hN) ht1
  have hmin : 0 < min (vsHeight z t) (vsHeight z' t) := lt_min h1 h2
  have heq : min |(lemmaKPoint z t).im| |(lemmaKPoint z' t).im| =
      min (vsHeight z t) (vsHeight z' t) / Real.sqrt t := by
    rw [lemmaKPoint_im, lemmaKPoint_im, abs_of_pos (div_pos h1 hst),
      abs_of_pos (div_pos h2 hst), min_div_div_right hst.le]
  refine ⟨lemmaKPoint_spectralDomain hN hκ hz q hqδ hqκ hqC ht ht1,
    lemmaKPoint_spectralDomain hN hκ hz' q hqδ hqκ hqC ht ht1, ?_, heq, ?_, ?_⟩
  · unfold ErdosRiabov.SameHalfPlane
    rw [lemmaKPoint_im, lemmaKPoint_im]
    exact mul_pos (div_pos h1 hst) (div_pos h2 hst)
  · rw [heq]
    exact le_div_self hmin.le hst hst1
  · rw [heq, div_le_iff₀ hst]
    nlinarith

end BlockBand.Native.ErdosRiabov.LemmaK
