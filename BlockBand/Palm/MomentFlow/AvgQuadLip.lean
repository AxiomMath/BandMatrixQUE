module

public import BlockBand.Palm.MomentFlow.SlowGamma
public import BlockBand.Palm.MomentFlow.AvgLineDet

/-!
# Lipschitz continuity of `q*M_s(z)q` in `(s, z)`, uniformly in the height

* `freshW_window_lipschitz`: `|w_s(z) - w_{s'}(z')| ≤ slowWConst (|z - z'| + |s - s'|)` on the
  regularity window (any heights in `[0,1]`).
* `resolvent_quad_sub_le`: `|q*((F-w)⁻¹ - (F-w')⁻¹)q| ≤ |w - w'| ‖q‖²/(Im w Im w')`.
* **`freshM_quad_lipschitz`**:
  `|q*M_s(z)q - q*M_{s'}(z')q| ≤ quadLipConst (|z - z'| + |s - s'|) ‖q‖²`,
  `quadLipConst = slowWConst/((c₀-s₀)v₀)²`, uniform in `N`, `F`, `E`, the heights and `q`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm BlockBand.Palm.CoarseRelative
open scoped ComplexConjugate

variable {N : ℕ}

theorem freshDyson_window_norm_le (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    {s : ℝ} (hs : s ∈ Icc (c₀ - s₀) c₀) {z : ℂ} (hx : |z.re - E| ≤ r₀) (hz : 0 ≤ z.im)
    (hz1 : z.im ≤ 1) :
    ‖freshDyson F s z‖ ≤ 1 / ((c₀ - s₀) * v₀) ∧ (c₀ - s₀) * v₀ ≤ (freshW F s z).im := by
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hκ : 0 < c₀ - s₀ := by linarith
  have hm := (fresh_regular_bounds hC.2.2 hs hx hz hz1).1
  have hσ0 : 0 < s := lt_of_lt_of_le hκ hs.1
  have hw : (c₀ - s₀) * v₀ ≤ (freshW F s z).im := by
    rw [freshW_im]; nlinarith [hs.1]
  refine ⟨(freshDyson_norm_le hC.1 hN hσ0 hz (lt_of_lt_of_le hv0 hm)).trans ?_, hw⟩
  rw [one_div]; exact inv_anti₀ (by positivity) hw

theorem freshW_window_lipschitz (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    {s s' : ℝ} (hs : s ∈ Icc (c₀ - s₀) c₀) (hs' : s' ∈ Icc (c₀ - s₀) c₀) {z z' : ℂ}
    (hx : |z.re - E| ≤ r₀) (hx' : |z'.re - E| ≤ r₀) (hz : 0 ≤ z.im) (hz1 : z.im ≤ 1)
    (hz' : 0 ≤ z'.im) (hz1' : z'.im ≤ 1) :
    ‖freshW F s z - freshW F s' z'‖ ≤ slowWConst c₀ s₀ v₀ * (‖z - z'‖ + |s - s'|) := by
  have hK' := hK
  have hlip := freshDyson_window_lipschitz hN hK' hC hs hs' hx hx' hz hz1 hz' hz1'
  have hmn := (freshDyson_window_norm_le hN hK' hC hs hx hz hz1).1
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hκ : 0 < c₀ - s₀ := by linarith
  have hsq : 0 < Real.sqrt (c₀ - s₀) := Real.sqrt_pos.2 hκ
  have hL := dysonLipConst_nonneg c₀ s₀ v₀
  set m := freshDyson F s z
  set m' := freshDyson F s' z'
  set d := ‖z - z'‖ + |s - s'|
  have hd1 : ‖z - z'‖ ≤ d := by simp only [d]; linarith [abs_nonneg (s - s')]
  have hd2 : |s - s'| ≤ d := by simp only [d]; linarith [norm_nonneg (z - z')]
  have e : freshW F s z - freshW F s' z' = (z - z') + ((s : ℂ) - s') * m + (s' : ℂ) * (m - m') := by
    simp only [freshW, m, m']; ring
  rw [e]
  have t1 : ‖((s : ℂ) - s') * m‖ ≤ d * (1 / ((c₀ - s₀) * v₀)) := by
    rw [norm_mul, show ((s : ℂ) - s') = ((s - s' : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul hd2 hmn (norm_nonneg _) ((abs_nonneg _).trans hd2)
  have hs'0 : 0 ≤ s' := by linarith [hs'.1]
  have t2 : ‖(s' : ℂ) * (m - m')‖ ≤ c₀ * dysonLipConst c₀ s₀ v₀ *
      (1 + 1 / Real.sqrt (c₀ - s₀)) * d := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs'0]
    have h3 : ‖z - z'‖ + |s - s'| / Real.sqrt (c₀ - s₀) ≤ (1 + 1 / Real.sqrt (c₀ - s₀)) * d := by
      have : |s - s'| / Real.sqrt (c₀ - s₀) ≤ d / Real.sqrt (c₀ - s₀) :=
        div_le_div_of_nonneg_right hd2 hsq.le
      have : (1 + 1 / Real.sqrt (c₀ - s₀)) * d = d + d / Real.sqrt (c₀ - s₀) := by ring
      linarith
    calc s' * ‖m - m'‖ ≤ c₀ * (dysonLipConst c₀ s₀ v₀ *
          (‖z - z'‖ + |s - s'| / Real.sqrt (c₀ - s₀))) :=
          mul_le_mul hs'.2 hlip (norm_nonneg _) hc0.le
      _ ≤ c₀ * (dysonLipConst c₀ s₀ v₀ * ((1 + 1 / Real.sqrt (c₀ - s₀)) * d)) := by gcongr
      _ = _ := by ring
  calc ‖(z - z') + ((s : ℂ) - s') * m + (s' : ℂ) * (m - m')‖
      ≤ ‖z - z'‖ + ‖((s : ℂ) - s') * m‖ + ‖(s' : ℂ) * (m - m')‖ := norm_add₃_le
    _ ≤ d + d * (1 / ((c₀ - s₀) * v₀)) +
          c₀ * dysonLipConst c₀ s₀ v₀ * (1 + 1 / Real.sqrt (c₀ - s₀)) * d := by linarith
    _ = slowWConst c₀ s₀ v₀ * d := by unfold slowWConst; ring

theorem resolvent_quad_sub_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {w w' : ℂ}
    (hw : 0 < w.im) (hw' : 0 < w'.im) (q : Fin N → ℂ) :
    ‖star q ⬝ᵥ (((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        (F - w' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) *ᵥ q)‖ ≤
      ‖w - w'‖ * nsq q / (w.im * w'.im) := by
  set R := (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  set R' := (F - w' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  have hid := hermitian_resolvent_sub hF hw.ne' hw'.ne'
  have e2 : star q ⬝ᵥ ((R * R') *ᵥ q) = star (Rᴴ *ᵥ q) ⬝ᵥ (R' *ᵥ q) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec]
  have hRc : Rᴴ = (F - (conj w) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ :=
    hermitian_resolvent_conjTranspose hF w
  have hwc : (conj w).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.2 hw.ne'
  have hb1 : l2Norm (Rᴴ *ᵥ q) ≤ l2Norm q / w.im := by
    rw [hRc]
    have := l2Norm_resolvent_le hF hwc q
    rwa [Complex.conj_im, abs_neg, abs_of_pos hw] at this
  have hb2 : l2Norm (R' *ᵥ q) ≤ l2Norm q / w'.im := by
    have := l2Norm_resolvent_le hF hw'.ne' q
    rwa [abs_of_pos hw'] at this
  have hnn : 0 ≤ nsq q := Finset.sum_nonneg fun _ _ => by positivity
  have hl2 : l2Norm q * l2Norm q = nsq q := by
    rw [l2Norm_eq_sqrt_nsq]; exact Real.mul_self_sqrt hnn
  rw [hid, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, norm_mul, e2]
  have hCS : ‖star (Rᴴ *ᵥ q) ⬝ᵥ (R' *ᵥ q)‖ ≤ nsq q / (w.im * w'.im) := by
    refine (norm_dotProduct_le_l2 _ _).trans ?_
    calc l2Norm (Rᴴ *ᵥ q) * l2Norm (R' *ᵥ q) ≤ (l2Norm q / w.im) * (l2Norm q / w'.im) :=
          mul_le_mul hb1 hb2 (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hw.le)
      _ = nsq q / (w.im * w'.im) := by rw [← hl2]; field_simp
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hCS (norm_nonneg _)

/-- `quadLipConst = slowWConst/((c₀-s₀)v₀)²`. -/
def quadLipConst (c₀ s₀ v₀ : ℝ) : ℝ := slowWConst c₀ s₀ v₀ / ((c₀ - s₀) * v₀) ^ 2

/-- **Lipschitz bound for `q*M_s(z)q` on the regularity window**, uniform in the height. -/
theorem freshM_quad_lipschitz (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    {s s' : ℝ} (hs : s ∈ Icc (c₀ - s₀) c₀) (hs' : s' ∈ Icc (c₀ - s₀) c₀) {z z' : ℂ}
    (hx : |z.re - E| ≤ r₀) (hx' : |z'.re - E| ≤ r₀) (hz : 0 ≤ z.im) (hz1 : z.im ≤ 1)
    (hz' : 0 ≤ z'.im) (hz1' : z'.im ≤ 1) (q : Fin N → ℂ) :
    ‖star q ⬝ᵥ (freshM F s z *ᵥ q) - star q ⬝ᵥ (freshM F s' z' *ᵥ q)‖ ≤
      quadLipConst c₀ s₀ v₀ * (‖z - z'‖ + |s - s'|) * nsq q := by
  have hK' := hK
  have hW := freshW_window_lipschitz hN hK' hC hs hs' hx hx' hz hz1 hz' hz1'
  have hw1 := (freshDyson_window_norm_le hN hK' hC hs hx hz hz1).2
  have hw2 := (freshDyson_window_norm_le hN hK' hC hs' hx' hz' hz1').2
  have hW0 := slowWConst_nonneg hK'
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hκ : 0 < (c₀ - s₀) * v₀ := mul_pos (by linarith) hv0
  have hsub : star q ⬝ᵥ (freshM F s z *ᵥ q) - star q ⬝ᵥ (freshM F s' z' *ᵥ q) =
      star q ⬝ᵥ ((freshM F s z - freshM F s' z') *ᵥ q) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [hsub, freshM_eq, freshM_eq]
  refine (resolvent_quad_sub_le hC.1 (lt_of_lt_of_le hκ hw1) (lt_of_lt_of_le hκ hw2) q).trans ?_
  have hnn : 0 ≤ nsq q := Finset.sum_nonneg fun _ _ => by positivity
  have hden : ((c₀ - s₀) * v₀) ^ 2 ≤ (freshW F s z).im * (freshW F s' z').im := by
    rw [sq]; exact mul_le_mul hw1 hw2 hκ.le (le_trans hκ.le hw1)
  calc ‖freshW F s z - freshW F s' z'‖ * nsq q / ((freshW F s z).im * (freshW F s' z').im)
      ≤ slowWConst c₀ s₀ v₀ * (‖z - z'‖ + |s - s'|) * nsq q / ((c₀ - s₀) * v₀) ^ 2 :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hW hnn) (by positivity) hden
    _ = _ := by unfold quadLipConst; ring

end BlockBand.Palm.MomentFlow
