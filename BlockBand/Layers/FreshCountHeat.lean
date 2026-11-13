module

public import BlockBand.Layers.FreshCountFluct
public import BlockBand.Layers.MatchedScalar

/-!
# Deterministic kernels of the fresh count: smoothing and height removal

* "The initial phase changes by `O(Wε)` when removing its extra height": for `Im w > 0` and
  `s ≥ 0`, `|arg(w + is) - arg w| ≤ s / Im w` (`fc_arg_vertical_le`), hence
  `|Θ_{z+iε}(F) - Θ_z(F)| ≤ W ε / Im z` (`fc_phaseCount_height_le`).
* "the scalar kernel error is `C min(1, ε/|x|)`": for `ε > 0` and real `x`,
  `|π⁻¹ arg(x + iε) - 1_{x<0}| ≤ 1` and `≤ ε/|x|` for `x ≠ 0` (`fc_kernel_le_one`,
  `fc_kernel_le_div`), and its dyadic domination by interval indicators (`fc_kernel_le_dyadic`).

Everything here is deterministic.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory Matrix Complex
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers
open scoped NNReal ENNReal Topology

/-!
## 1. Vertical Lipschitz bound for the logarithm and the argument
-/

/-- Along a vertical segment inside the slit plane at distance `≥ ρ` from `0`,
`‖log(w + is) - log w‖ ≤ s / ρ`. -/
theorem fc_log_vertical_le {w : ℂ} {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 < ρ)
    (hslit : ∀ u ∈ Set.Icc (0 : ℝ) s, w + (u : ℂ) * I ∈ slitPlane)
    (hnorm : ∀ u ∈ Set.Icc (0 : ℝ) s, ρ ≤ ‖w + (u : ℂ) * I‖) :
    ‖log (w + (s : ℂ) * I) - log w‖ ≤ s / ρ := by
  have hderiv : ∀ u ∈ Set.Icc (0 : ℝ) s, HasDerivWithinAt (fun u : ℝ => log (w + (u : ℂ) * I))
      ((w + (u : ℂ) * I)⁻¹ * I) (Set.Icc 0 s) u := by
    intro u hu
    have hg : HasDerivAt (fun u : ℝ => w + (u : ℂ) * I) I u := by
      have h1 := ((hasDerivAt_id u).ofReal_comp).mul_const I
      simpa using h1.const_add w
    exact ((hasDerivAt_log (hslit u hu)).comp u hg).hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Ico (0 : ℝ) s, ‖(w + (u : ℂ) * I)⁻¹ * I‖ ≤ ρ⁻¹ := by
    intro u hu
    have hn := hnorm u (Set.Ico_subset_Icc_self hu)
    rw [norm_mul, norm_I, mul_one, norm_inv]
    exact inv_anti₀ hρ hn
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound s ⟨hs, le_rfl⟩
  simpa [div_eq_inv_mul] using this

/-- `|arg(w + is) - arg w| ≤ s / Im w` for `Im w > 0`, `s ≥ 0`. -/
theorem fc_arg_vertical_le {w : ℂ} (hw : 0 < w.im) {s : ℝ} (hs : 0 ≤ s) :
    |arg (w + (s : ℂ) * I) - arg w| ≤ s / w.im := by
  have h := fc_log_vertical_le (w := w) hs hw
    (fun u hu => by
      refine mem_slitPlane_iff.mpr (Or.inr ?_)
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith [hu.1])
    (fun u hu => by
      refine le_trans ?_ (abs_im_le_norm _)
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      rw [abs_of_pos (by linarith [hu.1])]
      linarith [hu.1])
  calc |arg (w + (s : ℂ) * I) - arg w|
      = |(log (w + (s : ℂ) * I) - log w).im| := by rw [sub_im, log_im, log_im]
    _ ≤ ‖log (w + (s : ℂ) * I) - log w‖ := abs_im_le_norm _
    _ ≤ s / w.im := h

/-- `0 ≤ arg(x + iε) ≤ ε / x` for `x > 0`, `ε ≥ 0`. -/
theorem fc_arg_pos_le {x ε : ℝ} (hx : 0 < x) (hε : 0 ≤ ε) :
    arg ((x : ℂ) + (ε : ℂ) * I) ≤ ε / x := by
  have h := fc_log_vertical_le (w := (x : ℂ)) hε hx
    (fun u _ => by
      refine mem_slitPlane_iff.mpr (Or.inl ?_)
      simpa using hx)
    (fun u _ => by
      refine le_trans ?_ (abs_re_le_norm _)
      simp [abs_of_pos hx])
  have h2 : arg ((x : ℂ) + (ε : ℂ) * I) = (log ((x : ℂ) + (ε : ℂ) * I) - log (x : ℂ)).im := by
    rw [sub_im, log_im, log_im, arg_ofReal_of_nonneg hx.le, sub_zero]
  rw [h2]
  exact (le_abs_self _).trans ((abs_im_le_norm _).trans h)

/-- `arg(x + iε) ∈ [0, π]` and it is `> 0` for `ε > 0`. -/
theorem fc_arg_nonneg {x ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ arg ((x : ℂ) + (ε : ℂ) * I) := by
  refine arg_nonneg_iff.mpr ?_
  simpa using hε

/-- Reflection: `arg(x + iε) = π - arg(-x + iε)` for `ε > 0`. -/
theorem fc_arg_reflect {x ε : ℝ} (hε : 0 < ε) :
    arg ((x : ℂ) + (ε : ℂ) * I) = Real.pi - arg ((-x : ℝ) + (ε : ℂ) * I) := by
  set z : ℂ := (x : ℂ) + (ε : ℂ) * I with hz
  have hzim : 0 < z.im := by simpa [hz] using hε
  have hrefl : ((-x : ℝ) : ℂ) + (ε : ℂ) * I = -(starRingEnd ℂ z) := by
    apply Complex.ext <;> simp [hz]
  rw [hrefl]
  have hc : (starRingEnd ℂ z).im < 0 := by simpa using hzim
  rw [arg_neg_eq_arg_add_pi_of_im_neg hc, arg_conj]
  have : arg z ≠ Real.pi := by
    intro h
    have := (arg_eq_pi_iff.mp h).2
    linarith
  simp [this]

/-!
## 2. The scalar kernel `π⁻¹ arg(x + iε) - 1_{x<0}`
-/

/-- The smoothed negative indicator `π⁻¹ arg(x + iε) ∈ [0,1]` (`π⁻¹ Im log(x + iε)`). -/
def fcSmoothInd (ε x : ℝ) : ℝ := arg ((x : ℂ) + (ε : ℂ) * I) / Real.pi

/-- The sharp negative indicator. -/
def fcNegInd (x : ℝ) : ℝ := if x < 0 then 1 else 0

theorem fcSmoothInd_mem {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) : fcSmoothInd ε x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold fcSmoothInd
  refine ⟨div_nonneg (fc_arg_nonneg hε) Real.pi_pos.le, ?_⟩
  rw [div_le_one Real.pi_pos]
  exact arg_le_pi _

theorem fc_kernel_le_one {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) : |fcNegInd x - fcSmoothInd ε x| ≤ 1 := by
  have h := fcSmoothInd_mem hε x
  unfold fcNegInd
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [h.1, h.2]

theorem fc_kernel_le_div {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : x ≠ 0) :
    |fcNegInd x - fcSmoothInd ε x| ≤ ε / |x| := by
  have hpi := Real.pi_pos
  have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · -- `x < 0`: `1 - π⁻¹ arg(x + iε) = π⁻¹ arg(-x + iε)`
    have hx' : 0 < -x := neg_pos.mpr hneg
    have h1 := fc_arg_pos_le hx' hε.le
    have h0 : 0 ≤ arg (((-x : ℝ) : ℂ) + (ε : ℂ) * I) := fc_arg_nonneg hε.le
    have heq : fcNegInd x - fcSmoothInd ε x = arg (((-x : ℝ) : ℂ) + (ε : ℂ) * I) / Real.pi := by
      unfold fcNegInd fcSmoothInd
      simp only [hneg, ↓reduceIte]
      rw [fc_arg_reflect hε]
      field_simp
      ring
    rw [heq, abs_of_nonneg (div_nonneg h0 hpi.le), abs_of_neg hneg]
    calc arg (((-x : ℝ) : ℂ) + (ε : ℂ) * I) / Real.pi ≤ arg (((-x : ℝ) : ℂ) + (ε : ℂ) * I) :=
          div_le_self h0 hpi1
      _ ≤ ε / -x := h1
  · have h1 := fc_arg_pos_le hpos hε.le
    have h0 := fc_arg_nonneg (x := x) hε.le
    have heq : fcNegInd x - fcSmoothInd ε x = -(arg ((x : ℂ) + (ε : ℂ) * I) / Real.pi) := by
      unfold fcNegInd fcSmoothInd
      simp only [not_lt.mpr hpos.le, ↓reduceIte]
      ring
    rw [heq, abs_neg, abs_of_nonneg (div_nonneg h0 hpi.le), abs_of_pos hpos]
    exact (div_le_self h0 hpi1).trans h1

/-- The dyadic interval indicator `1_{|x| ≤ r}`. -/
def fcBall (r x : ℝ) : ℝ := if |x| ≤ r then 1 else 0

/-- **Dyadic domination of the kernel**: if `2^L ε ≥ 1` then
`|1_{x<0} - π⁻¹ arg(x + iε)| ≤ Σ_{m ≤ L} 2^{1-m} 1_{|x| ≤ 2^m ε} + ε`. -/
theorem fc_kernel_le_dyadic {ε : ℝ} (hε : 0 < ε) {L : ℕ} (hL : 1 ≤ 2 ^ L * ε) (x : ℝ) :
    |fcNegInd x - fcSmoothInd ε x| ≤
      (∑ m ∈ Finset.range (L + 1), 2 / 2 ^ m * fcBall (2 ^ m * ε) x) + ε := by
  have hterm : ∀ m ∈ Finset.range (L + 1), 0 ≤ 2 / 2 ^ m * fcBall (2 ^ m * ε) x := by
    intro m _
    unfold fcBall
    split_ifs <;> positivity
  have hS : 0 ≤ ∑ m ∈ Finset.range (L + 1), 2 / 2 ^ m * fcBall (2 ^ m * ε) x :=
    Finset.sum_nonneg hterm
  by_cases hfar : 2 ^ L * ε < |x|
  · have hx0 : x ≠ 0 := by
      intro h; rw [h, abs_zero] at hfar; linarith
    have h1 := fc_kernel_le_div hε hx0
    have h2 : ε / |x| ≤ ε := div_le_self hε.le (by linarith)
    linarith
  · replace hfar := not_lt.mp hfar
    have hex : ∃ m, |x| ≤ 2 ^ m * ε := ⟨L, hfar⟩
    classical
    set m₀ := Nat.find hex with hm₀
    have hm₀x : |x| ≤ 2 ^ m₀ * ε := Nat.find_spec hex
    have hm₀L : m₀ ≤ L := Nat.find_min' hex hfar
    have hmem : m₀ ∈ Finset.range (L + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm₀L)
    have hsingle : 2 / 2 ^ m₀ * fcBall (2 ^ m₀ * ε) x ≤
        ∑ m ∈ Finset.range (L + 1), 2 / 2 ^ m * fcBall (2 ^ m * ε) x :=
      Finset.single_le_sum hterm hmem
    have hball : fcBall (2 ^ m₀ * ε) x = 1 := by unfold fcBall; simp only [hm₀x, ↓reduceIte]
    rw [hball, mul_one] at hsingle
    rcases Nat.eq_zero_or_pos m₀ with h0 | hpos
    · have := fc_kernel_le_one hε.le x
      rw [h0, pow_zero, div_one] at hsingle
      linarith
    · have hlt : ¬ |x| ≤ 2 ^ (m₀ - 1) * ε := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      replace hlt := not_le.mp hlt
      have hx0 : x ≠ 0 := by
        intro h; rw [h, abs_zero] at hlt
        have : 0 < 2 ^ (m₀ - 1) * ε := by positivity
        linarith
      have h1 := fc_kernel_le_div hε hx0
      have hpow : (2 : ℝ) ^ m₀ = 2 * 2 ^ (m₀ - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hq : 0 < (2 : ℝ) ^ (m₀ - 1) * ε := by positivity
      have hxpos : 0 < |x| := by linarith
      have h2 : ε / |x| ≤ 2 / 2 ^ m₀ := by
        rw [hpow, div_le_div_iff₀ hxpos (by positivity)]
        nlinarith
      linarith

/-!
## 3. Spectral sums and the height removal
-/

/-- A spectral sum of a Hermitian matrix is the sum over its eigenvalues. -/
theorem fc_spectralSum_eq {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (f : ℝ → ℝ) :
    Internal.Contracts.Inputs.spectralSum M f = ∑ k, f (hM.eigenvalues k) := by
  unfold Internal.Contracts.Inputs.spectralSum
  rw [hM.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1

/-- `Θ_z(F) = π⁻¹ Σ_k arg(z - λ_k(F))`. -/
theorem fc_phaseCount_eq {ι : Type} [Fintype ι] [DecidableEq ι] {F : Matrix ι ι ℂ}
    (hF : F.IsHermitian) (z : ℂ) :
    phaseCount z F = ∑ k, arg (z - (hF.eigenvalues k : ℂ)) / Real.pi := by
  unfold phaseCount
  rw [fc_spectralSum_eq hF, Finset.sum_div]

/-- **Height removal**: for `Im z > 0` and `ε ≥ 0`,
`|Θ_{z+iε}(F) - Θ_z(F)| ≤ W ε / Im z`, uniformly in Hermitian `F`. -/
theorem fc_phaseCount_height_le {ι : Type} [Fintype ι] [DecidableEq ι] {F : Matrix ι ι ℂ}
    (hF : F.IsHermitian) {z : ℂ} (hz : 0 < z.im) {ε : ℝ} (hε : 0 ≤ ε) :
    |phaseCount (z + (ε : ℂ) * I) F - phaseCount z F| ≤ Fintype.card ι * (ε / z.im) := by
  rw [fc_phaseCount_eq hF, fc_phaseCount_eq hF, ← Finset.sum_sub_distrib]
  have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  calc |∑ k, (arg (z + (ε : ℂ) * I - (hF.eigenvalues k : ℂ)) / Real.pi -
        arg (z - (hF.eigenvalues k : ℂ)) / Real.pi)|
      ≤ ∑ k, |arg (z + (ε : ℂ) * I - (hF.eigenvalues k : ℂ)) / Real.pi -
        arg (z - (hF.eigenvalues k : ℂ)) / Real.pi| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, ε / z.im := by
        refine Finset.sum_le_sum fun k _ => ?_
        set w : ℂ := z - (hF.eigenvalues k : ℂ) with hw
        have hwim : w.im = z.im := by simp [hw]
        have hshift : z + (ε : ℂ) * I - (hF.eigenvalues k : ℂ) = w + (ε : ℂ) * I := by
          rw [hw]; ring
        rw [hshift, ← sub_div, abs_div, abs_of_pos Real.pi_pos]
        have h := fc_arg_vertical_le (w := w) (by rw [hwim]; exact hz) hε
        rw [hwim] at h
        exact (div_le_self (abs_nonneg _) hpi1).trans h
    _ = Fintype.card ι * (ε / z.im) := by rw [Finset.sum_const, nsmul_eq_mul]; rfl

end BlockBand.Layers
