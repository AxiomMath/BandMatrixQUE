module

public import BlockBand.Transmission.Dual.GHTilt
public import BlockBand.Transmission.Dual.MPConverseCalc

/-!
# The Leibniz rule for diagonal generators and the h-transformed drift)

* `mpGenerator_mul_diag`: `𝓛(hφ) = h𝓛φ + φ𝓛h + Σ_k d_k ∂_kh ∂_kφ` (line derivatives);
* `htDrift b d h = b + d ∂ log h` and `mpGenerator_htDrift`: `𝓛^{htDrift} φ = 𝓛φ + Σ_k d_k (∂_kh/h) ∂_kφ`;
* `transform_of_htDrift`: if `𝓛h = 0` and `h ≠ 0` at `w`, then `𝓛(hφ) = h 𝓛^{htDrift}φ` at `w`:
  the `transform` field of `IsHTransform` with `b̃ = htDrift` (no target identity to check);
* `htDrift_cauchyH`: on the chamber, the h-transformed drift of `H_q` is the flat dual drift.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Filter Topology Set Finset
open BlockBand.SourceProcess.Stochastic BlockBand.Transmission.Dual

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ}

/-- `D(hφ)(v)` along a line. -/
theorem fderiv_mul_apply' {h φ : (Fin d → ℝ) → ℝ} {w : Fin d → ℝ} (hh : DifferentiableAt ℝ h w)
    (hφ : DifferentiableAt ℝ φ w) (v : Fin d → ℝ) :
    fderiv ℝ (fun y => h y * φ y) w v = h w * fderiv ℝ φ w v + φ w * fderiv ℝ h w v := by
  rw [fderiv_fun_mul hh hφ]; simp [smul_eq_mul]

/-- `D²(hφ)(v, v) = h D²φ(v,v) + 2 Dh(v) Dφ(v) + φ D²h(v,v)`. -/
theorem fderiv_fderiv_hmul_apply {h φ : (Fin d → ℝ) → ℝ} {w : Fin d → ℝ}
    (hh : ContDiffAt ℝ 2 h w) (hφ : ContDiffAt ℝ 2 φ w) (v : Fin d → ℝ) :
    fderiv ℝ (fderiv ℝ fun y => h y * φ y) w v v =
      h w * fderiv ℝ (fderiv ℝ φ) w v v + 2 * fderiv ℝ h w v * fderiv ℝ φ w v +
        φ w * fderiv ℝ (fderiv ℝ h) w v v := by
  have hp : ContDiffAt ℝ 2 (fun y => h y * φ y) w := hh.mul hφ
  rw [Exists.fderiv_fderiv_eq_deriv_line v hp]
  have hc : Continuous fun r : ℝ => w + r • v := continuous_const.add (continuous_id.smul
    continuous_const)
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 h (w + r • v) ∧ ContDiffAt ℝ 2 φ (w + r • v) := by
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.eventually ((hh.eventually (by simp)).and (hφ.eventually (by simp)))
  have e : deriv (fun r : ℝ => h (w + r • v) * φ (w + r • v)) =ᶠ[𝓝 0] fun r =>
      fderiv ℝ h (w + r • v) v * φ (w + r • v) + h (w + r • v) * fderiv ℝ φ (w + r • v) v := by
    filter_upwards [hev] with r hr
    exact ((Exists.hasDerivAt_line r (hr.1.differentiableAt (by norm_num))).mul
      (Exists.hasDerivAt_line r (hr.2.differentiableAt (by norm_num)))).deriv
  rw [e.deriv_eq]
  have h0 : DifferentiableAt ℝ h (w + (0 : ℝ) • v) := by
    simpa using hh.differentiableAt (by norm_num)
  have f0 : DifferentiableAt ℝ φ (w + (0 : ℝ) • v) := by
    simpa using hφ.differentiableAt (by norm_num)
  have := (((Exists.hasDerivAt_fderiv_line v hh).mul (Exists.hasDerivAt_line 0 f0)).add
    ((Exists.hasDerivAt_line 0 h0).mul (Exists.hasDerivAt_fderiv_line v hφ))).deriv
  simp only [zero_smul, add_zero] at this
  refine this.trans ?_
  ring

/-- The generator for a diagonal covariance. -/
theorem mpGenerator_diag (b : (Fin d → ℝ) → Fin d → ℝ) (δ : (Fin d → ℝ) → Fin d → ℝ)
    (φ : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) :
    mpGenerator b (fun y => Matrix.diagonal (δ y)) φ w = ∑ i, b w i * fderiv ℝ φ w (Pi.single i 1) +
      (1 / 2 : ℝ) * ∑ i, δ w i * fderiv ℝ (fderiv ℝ φ) w (Pi.single i 1) (Pi.single i 1) := by
  unfold mpGenerator
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

/-- **Leibniz rule** for a diagonal generator. -/
theorem mpGenerator_mul_diag (b : (Fin d → ℝ) → Fin d → ℝ) (δ : (Fin d → ℝ) → Fin d → ℝ)
    {h φ : (Fin d → ℝ) → ℝ} {w : Fin d → ℝ} (hh : ContDiffAt ℝ 2 h w) (hφ : ContDiffAt ℝ 2 φ w) :
    mpGenerator b (fun y => Matrix.diagonal (δ y)) (fun y => h y * φ y) w =
      h w * mpGenerator b (fun y => Matrix.diagonal (δ y)) φ w +
        φ w * mpGenerator b (fun y => Matrix.diagonal (δ y)) h w +
        ∑ i, δ w i * fderiv ℝ h w (Pi.single i 1) * fderiv ℝ φ w (Pi.single i 1) := by
  simp only [mpGenerator_diag, fderiv_mul_apply' (hh.differentiableAt (by norm_num))
    (hφ.differentiableAt (by norm_num)), fderiv_fderiv_hmul_apply hh hφ _]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The h-transformed drift `b + d ∂ log h`. -/
def htDrift (b : (Fin d → ℝ) → Fin d → ℝ) (δ : (Fin d → ℝ) → Fin d → ℝ)
    (h : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) : Fin d → ℝ :=
  fun i => b w i + δ w i * fderiv ℝ h w (Pi.single i 1) / h w

theorem mpGenerator_htDrift (b : (Fin d → ℝ) → Fin d → ℝ) (δ : (Fin d → ℝ) → Fin d → ℝ)
    (h φ : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) :
    mpGenerator (htDrift b δ h) (fun y => Matrix.diagonal (δ y)) φ w =
      mpGenerator b (fun y => Matrix.diagonal (δ y)) φ w +
        ∑ i, δ w i * fderiv ℝ h w (Pi.single i 1) / h w * fderiv ℝ φ w (Pi.single i 1) := by
  simp only [mpGenerator_diag, htDrift, add_mul, Finset.sum_add_distrib]
  ring

/-- **The transform identity for the h-transformed drift.** -/
theorem transform_of_htDrift (b : (Fin d → ℝ) → Fin d → ℝ) (δ : (Fin d → ℝ) → Fin d → ℝ)
    {h φ : (Fin d → ℝ) → ℝ} {w : Fin d → ℝ} (hh : ContDiffAt ℝ 2 h w) (hφ : ContDiffAt ℝ 2 φ w)
    (h0 : h w ≠ 0) (hL : mpGenerator b (fun y => Matrix.diagonal (δ y)) h w = 0) :
    mpGenerator b (fun y => Matrix.diagonal (δ y)) (fun y => h y * φ y) w =
      h w * mpGenerator (htDrift b δ h) (fun y => Matrix.diagonal (δ y)) φ w := by
  rw [mpGenerator_mul_diag b δ hh hφ, hL, mpGenerator_htDrift, mul_add, Finset.mul_sum]
  simp only [mul_zero, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

variable {q : ℕ}

/-- **The h-transformed drift of `H_q` is the flat dual drift** on the chamber. -/
theorem htDrift_cauchyH (D0 : ℝ) {w : Fin (q + q) → ℝ} (hw : w ∈ flatChamber q) :
    htDrift (flatBaseDrift D0 q) (flatDiffDiag D0 q) (flatH q) w = flatDrift D0 q w := by
  have hH : ContDiffAt ℝ 2 (flatH q) w :=
    ((isHTransform_cauchyH (q := q) D0).smooth.contDiffAt ((isOpen_flatChamber q).mem_nhds hw))
  have h0 : flatH q w ≠ 0 := (cauchyH_pos hw).ne'
  funext k
  have hk : ContDiff ℝ 2 fun y : Fin (q + q) → ℝ => y k := (contDiff_apply ℝ ℝ k)
  have e1 := (isHTransform_cauchyH (q := q) D0).transform _ hk w hw
  have e2 := transform_of_htDrift (flatBaseDrift D0 q) (flatDiffDiag D0 q) hH hk.contDiffAt h0
    (mpGenerator_flatBase_cauchyH D0 hw)
  have e3 : flatDiff D0 q = fun y => Matrix.diagonal (flatDiffDiag D0 q y) := rfl
  rw [e3] at e1
  rw [e1, mpGenerator_coord, mpGenerator_coord] at e2
  exact (mul_left_cancel₀ h0 e2).symm

end BlockBand.Transmission.Dual.G
