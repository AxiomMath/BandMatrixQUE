module

public import BlockBand.Transmission.FractionalBulk.LayerTools

/-!
# One entry of the fresh layer: the weighted variance lower bound

Deterministic passive `X`, `U = LL*` under `freshLaw W b`, unit vectors `u, v`, `N = max(1, ‖L‖²)`.

**`entryGap_lower`**: from `E|u*(U-EU)v|² ≥ c/W` (`entryVariance`), `E|u*(U-EU)v|⁴ ≤ C_B⁴/W²`
and `E‖L‖⁴ ≤ C_L⁴`: for every constant `m₀`,
`E[|u*Uv - m₀|²/N] ≥ (c/W)/(4K + M/2)`, `K = max(1, C_B⁴/c²)`, `M = 1 + C_L⁴`
(`weighted_lower` with `Y = u*(U-EU)v`, `m = u*(EU)v - m₀`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `N = max(1, ‖L‖²)`. -/
def weightN (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y : LayerSample W .oneBlockOnePort) : ℝ :=
  max 1 (‖freshL b E X y‖ ^ 2)

theorem measurable_weightN (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (weightN b E X) :=
  measurable_const.max ((measurable_norm_freshL b E X).pow_const 2)

theorem weightN_sq_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y) :
    weightN b E X y ^ 2 ≤ 1 + ‖freshL b E X y‖ ^ 4 := by
  unfold weightN
  rcases le_total 1 (‖freshL b E X y‖ ^ 2) with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith [norm_nonneg (freshL b E X y)]

theorem bilinear_sub' {n : Type*} [Fintype n] (u : n → ℂ) (A B : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u (A - B) v = bilinear u A v - bilinear u B v := by
  simp only [bilinear, sub_mulVec, dotProduct_sub]

/-- **The weighted entry lower bound.** -/
theorem entryGap_lower {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {u v : Fin W → ℂ} (m₀ : ℂ)
    {c CB CL : ℝ} (hc : 0 < c) (hW : 0 < W)
    (hU : ∀ x y, Integrable (fun ω => freshU b E X ω x y) (freshLaw W b))
    (hY2 : c / W ≤ ∫ y, ‖bilinear u (freshU b E X y -
      matrixExpect (freshLaw W b) (freshU b E X)) v‖ ^ 2 ∂freshLaw W b)
    (hY4i : Integrable (fun y => ‖bilinear u (freshU b E X y -
      matrixExpect (freshLaw W b) (freshU b E X)) v‖ ^ 4) (freshLaw W b))
    (hY4 : ∫ y, ‖bilinear u (freshU b E X y - matrixExpect (freshLaw W b) (freshU b E X)) v‖ ^ 4
      ∂freshLaw W b ≤ CB ^ 4 / (W : ℝ) ^ 2)
    (hL4i : Integrable (fun y => ‖freshL b E X y‖ ^ 4) (freshLaw W b))
    (hL4 : ∫ y, ‖freshL b E X y‖ ^ 4 ∂freshLaw W b ≤ CL ^ 4) :
    (c / W) / (4 * max 1 (CB ^ 4 / c ^ 2) + (1 + CL ^ 4) / 2) ≤
      ∫ y, ‖bilinear u (freshU b E X y) v - m₀‖ ^ 2 / weightN b E X y ∂freshLaw W b := by
  set ν := freshLaw W b
  set Ub := matrixExpect ν (freshU b E X)
  set Y : LayerSample W .oneBlockOnePort → ℂ := fun y => bilinear u (freshU b E X y - Ub) v
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hYm : Measurable Y := measurable_bilinear_centered b E X Ub u v
  have hYi : Integrable Y ν := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hY4i) hYm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    nlinarith [norm_nonneg (Y y), sq_nonneg (‖Y y‖ - 1), sq_nonneg (‖Y y‖ ^ 2 - 1),
      sq_nonneg (‖Y y‖)]
  have hY0 : ∫ y, Y y ∂ν = 0 := by
    have hc' : ∀ x y, Integrable (fun ω => (freshU b E X ω - Ub) x y) ν := fun x y =>
      (hU x y).sub (integrable_const _)
    have := SourceProcess.FullSource.integral_bilinear (fun ω => freshU b E X ω - Ub) hc' u v
    refine this.trans ?_
    have h0 : matrixExpect ν (fun ω => freshU b E X ω - Ub) = 0 := by
      ext x y
      simp only [matrixExpect, Matrix.of_apply, Matrix.sub_apply, Matrix.zero_apply]
      rw [integral_sub (hU x y) (integrable_const _), integral_const]
      simp [Ub, matrixExpect]
    rw [h0]
    simp [bilinear]
  have hY2i : Integrable (fun y => ‖Y y‖ ^ 2) ν := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hY4i) (hYm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (‖Y y‖ ^ 2 - 1)]
  set K := max 1 (CB ^ 4 / c ^ 2)
  have hK : 1 ≤ K := le_max_left _ _
  have hY4' : ∫ y, ‖Y y‖ ^ 4 ∂ν ≤ K * (c / W) ^ 2 := by
    refine hY4.trans ?_
    have : CB ^ 4 / c ^ 2 ≤ K := le_max_right _ _
    calc CB ^ 4 / (W : ℝ) ^ 2 = CB ^ 4 / c ^ 2 * (c / W) ^ 2 := by field_simp
      _ ≤ K * (c / W) ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
  have hN2i : Integrable (fun y => weightN b E X y ^ 2) ν := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hL4i)
      ((measurable_weightN b E X).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (by positivity)]
    exact weightN_sq_le b E X y
  have hN2 : ∫ y, weightN b E X y ^ 2 ∂ν ≤ 1 + CL ^ 4 := by
    calc ∫ y, weightN b E X y ^ 2 ∂ν ≤ ∫ y, (1 + ‖freshL b E X y‖ ^ 4) ∂ν :=
          integral_mono hN2i ((integrable_const _).add hL4i) (weightN_sq_le b E X)
      _ = 1 + ∫ y, ‖freshL b E X y‖ ^ 4 ∂ν := by
          rw [integral_add (integrable_const _) hL4i, integral_const]; simp
      _ ≤ 1 + CL ^ 4 := by linarith
  have h := weighted_lower (bilinear u Ub v - m₀) (by positivity : 0 < c / W) hK
    hYm.aestronglyMeasurable (measurable_weightN b E X).aestronglyMeasurable
    (fun y => le_max_left _ _) hYi hY0 hY2i hY2 hY4i hY4' hN2i hN2
  refine h.trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)))
  simp only [Y]
  rw [bilinear_sub']
  ring_nf

end BlockBand.Transmission.FractionalBulk
