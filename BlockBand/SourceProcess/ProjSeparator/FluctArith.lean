module

public import BlockBand.SourceProcess.ProjSeparator.Bounds

/-!
# Arithmetic of `ProjGammaFluct`

* `le_split_of_two`: `n ≤ Am`, `n ≤ Bm`, `m ≤ d + e` give `n ≤ Ad + Be`;
* `sqrt_S_div`: `η⁻¹√S/√W = r/(2η²)`;
* `wvec_term_le`: `C₂W^{-1/2}‖x‖‖w‖ ≤ C₂C_M H(δ₀r + gw)‖x‖‖y‖` from `‖w‖ ≤ η⁻¹√S‖M‖‖y‖`,
  `‖w‖ ≤ S‖M‖‖y‖`, `‖M‖ ≤ C_M(δ₀ + w²)`;
* `fluct_arith`: the sum of the three terms of `eLpNorm_gamma_centered` is
  `≤ 2(C₂C_M + C₄²)H(g/W + δ₀√(g/W))‖x‖‖y‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

theorem le_split_of_two {n m A B d e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d) (he : 0 ≤ e)
    (h1 : n ≤ A * m) (h2 : n ≤ B * m) (hm : m ≤ d + e) : n ≤ A * d + B * e := by
  rcases le_total A B with h | h
  · have := mul_le_mul_of_nonneg_left hm hA
    nlinarith [mul_le_mul_of_nonneg_right h he]
  · have := mul_le_mul_of_nonneg_left hm hB
    nlinarith [mul_le_mul_of_nonneg_right h hd]

theorem sqrt_S_div {g η W : ℝ} (hg : 0 ≤ g) (hη : 0 < η) (hW : 0 < W) :
    η⁻¹ * Real.sqrt (g / (4 * η ^ 2)) / Real.sqrt W = Real.sqrt (g / W) / (2 * η ^ 2) := by
  have h4 : Real.sqrt (4 * η ^ 2) = 2 * η := by
    rw [show 4 * η ^ 2 = (2 * η) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [Real.sqrt_div hg, Real.sqrt_div hg, h4]
  have := Real.sqrt_pos.mpr hW
  field_simp

/-- One linear term of the fluctuation. -/
theorem wvec_term_le {C₂ CM δ₀ g η W nM nx ny nw H : ℝ} (hW : 1 ≤ W) (hη : 0 < η)
    (hH : η⁻¹ ^ 2 ≤ H) (hg : 0 ≤ g) (hδ₀ : 0 ≤ δ₀) (hC₂ : 0 ≤ C₂) (hCM : 0 ≤ CM) (hnx : 0 ≤ nx)
    (hny : 0 ≤ ny) (hnM : nM ≤ CM * (δ₀ + W⁻¹ ^ 2))
    (hw1 : nw ≤ η⁻¹ * Real.sqrt (g / (4 * η ^ 2)) * (nM * ny))
    (hw2 : nw ≤ g / (4 * η ^ 2) * (nM * ny)) :
    C₂ / Real.sqrt W * nx * nw ≤ C₂ * CM * H * (δ₀ * Real.sqrt (g / W) + g / W) * (nx * ny) := by
  have hW0 : 0 < W := by linarith
  have hsW := Real.sqrt_pos.mpr hW0
  have hsW1 : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW
  set S := g / (4 * η ^ 2)
  have hS0 : 0 ≤ S := by positivity
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have hw : nw ≤ η⁻¹ * Real.sqrt S * (CM * δ₀ * ny) + S * (CM * W⁻¹ ^ 2 * ny) :=
    le_split_of_two (by positivity) hS0 (by positivity) (by positivity) hw1 hw2
      (by have := mul_le_mul_of_nonneg_right hnM hny; nlinarith)
  have e1 : η⁻¹ * Real.sqrt S / Real.sqrt W = Real.sqrt (g / W) / (2 * η ^ 2) :=
    sqrt_S_div hg hη hW0
  have e2 : S * W⁻¹ ^ 2 / Real.sqrt W ≤ H * (g / W) := by
    have hw' : W⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW
    have : S * W⁻¹ ^ 2 / Real.sqrt W ≤ S * W⁻¹ := by
      rw [div_le_iff₀ hsW]
      have : W⁻¹ ^ 2 ≤ W⁻¹ * Real.sqrt W := by
        rw [sq]; exact mul_le_mul_of_nonneg_left (hw'.trans hsW1) (by positivity)
      nlinarith
    refine this.trans ?_
    have hSH : S ≤ H * g := by
      have : S = η⁻¹ ^ 2 * g / 4 := by simp only [S]; field_simp
      rw [this]; nlinarith [mul_le_mul_of_nonneg_right hH hg, sq_nonneg η⁻¹]
    rw [div_eq_mul_inv g W, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hSH (by positivity)
  have e3 : Real.sqrt (g / W) / (2 * η ^ 2) ≤ H * Real.sqrt (g / W) := by
    have : Real.sqrt (g / W) / (2 * η ^ 2) = η⁻¹ ^ 2 / 2 * Real.sqrt (g / W) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg η⁻¹]) (Real.sqrt_nonneg _)
  have hrw : C₂ / Real.sqrt W * nx * nw ≤ C₂ / Real.sqrt W * nx *
      (η⁻¹ * Real.sqrt S * (CM * δ₀ * ny) + S * (CM * W⁻¹ ^ 2 * ny)) :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  have e4 : C₂ / Real.sqrt W * nx * (η⁻¹ * Real.sqrt S * (CM * δ₀ * ny) + S * (CM * W⁻¹ ^ 2 * ny)) =
      C₂ * CM * (nx * ny) * (δ₀ * (η⁻¹ * Real.sqrt S / Real.sqrt W) +
        S * W⁻¹ ^ 2 / Real.sqrt W) := by
    field_simp
  rw [e4, e1] at hrw
  refine hrw.trans ?_
  have hk : 0 ≤ C₂ * CM * (nx * ny) := by positivity
  have := add_le_add (mul_le_mul_of_nonneg_left e3 hδ₀) e2
  calc C₂ * CM * (nx * ny) * (δ₀ * (Real.sqrt (g / W) / (2 * η ^ 2)) + S * W⁻¹ ^ 2 / Real.sqrt W)
      ≤ C₂ * CM * (nx * ny) * (δ₀ * (H * Real.sqrt (g / W)) + H * (g / W)) :=
        mul_le_mul_of_nonneg_left this hk
    _ = _ := by ring

/-- **The real arithmetic of `ProjGammaFluct`.** -/
theorem fluct_arith {C₂ C₄ CM δ₀ g η W nM nx ny nwx nwy H : ℝ} (hW : 1 ≤ W) (hη : 0 < η)
    (hH : η⁻¹ ^ 2 ≤ H) (hg : 0 ≤ g) (hδ₀ : 0 ≤ δ₀) (hC₂ : 0 ≤ C₂) (hCM : 0 ≤ CM)
    (hnx : 0 ≤ nx) (hny : 0 ≤ ny) (hnM : nM ≤ CM * (δ₀ + W⁻¹ ^ 2))
    (hx1 : nwx ≤ η⁻¹ * Real.sqrt (g / (4 * η ^ 2)) * (nM * nx))
    (hx2 : nwx ≤ g / (4 * η ^ 2) * (nM * nx))
    (hy1 : nwy ≤ η⁻¹ * Real.sqrt (g / (4 * η ^ 2)) * (nM * ny))
    (hy2 : nwy ≤ g / (4 * η ^ 2) * (nM * ny)) :
    C₂ / Real.sqrt W * nx * nwy + C₂ / Real.sqrt W * ny * nwx +
        2 * ((C₄ / Real.sqrt W) ^ 2 * nx * ny * (g / (4 * η ^ 2))) ≤
      2 * (C₂ * CM + C₄ ^ 2) * H * (g / W + δ₀ * Real.sqrt (g / W)) * nx * ny := by
  have t1 := wvec_term_le hW hη hH hg hδ₀ hC₂ hCM hnx hny hnM hy1 hy2
  have t2 := wvec_term_le hW hη hH hg hδ₀ hC₂ hCM hny hnx hnM hx1 hx2
  have hW0 : 0 < W := by linarith
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have t3 : 2 * ((C₄ / Real.sqrt W) ^ 2 * nx * ny * (g / (4 * η ^ 2))) ≤
      2 * C₄ ^ 2 * H * (g / W) * (nx * ny) := by
    have hs : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0.le
    have e : (C₄ / Real.sqrt W) ^ 2 = C₄ ^ 2 / W := by rw [div_pow, hs]
    have hSH : g / (4 * η ^ 2) ≤ H * g := by
      have : g / (4 * η ^ 2) = η⁻¹ ^ 2 * g / 4 := by field_simp
      rw [this]; nlinarith [mul_le_mul_of_nonneg_right hH hg, sq_nonneg η⁻¹]
    rw [e]
    have hk : 0 ≤ 2 * (C₄ ^ 2 / W * nx * ny) := by positivity
    have := mul_le_mul_of_nonneg_left hSH hk
    calc 2 * (C₄ ^ 2 / W * nx * ny * (g / (4 * η ^ 2))) = 2 * (C₄ ^ 2 / W * nx * ny) *
          (g / (4 * η ^ 2)) := by ring
      _ ≤ 2 * (C₄ ^ 2 / W * nx * ny) * (H * g) := this
      _ = _ := by field_simp
  have hr : 0 ≤ δ₀ * Real.sqrt (g / W) := mul_nonneg hδ₀ (Real.sqrt_nonneg _)
  have hgW : 0 ≤ g / W := by positivity
  have hxy : 0 ≤ nx * ny := mul_nonneg hnx hny
  have k1 : 0 ≤ C₄ ^ 2 * H * (δ₀ * Real.sqrt (g / W)) * (nx * ny) := by positivity
  calc C₂ / Real.sqrt W * nx * nwy + C₂ / Real.sqrt W * ny * nwx +
        2 * ((C₄ / Real.sqrt W) ^ 2 * nx * ny * (g / (4 * η ^ 2)))
      ≤ C₂ * CM * H * (δ₀ * Real.sqrt (g / W) + g / W) * (nx * ny) +
          C₂ * CM * H * (δ₀ * Real.sqrt (g / W) + g / W) * (ny * nx) +
          2 * C₄ ^ 2 * H * (g / W) * (nx * ny) := add_le_add (add_le_add t1 t2) t3
    _ ≤ _ := by nlinarith

end BlockBand.SourceProcess.ProjSeparator
