module

public import BlockBand.Endpoints.Clock.ZeroEntranceChain

/-!
# The zero-entrance lemma: the finite chain with a general port parameter, existence

`IsPortChain b e J z' m` is the finite Dyson equation with the matched port `z` replaced by an
arbitrary port parameter `z'` in the upper half-plane: `m₀ = 0`, `Im m_ℓ < 0` for
`1 ≤ ℓ ≤ J+1`,
`m_ℓ⁻¹ = -e - c m_ℓ - b m_{ℓ-1} - b m_{ℓ+1}` (`1 ≤ ℓ ≤ J`, `c = 1 - 2b`) and
`m_{J+1}⁻¹ = z' - b m_J`. At `z' = boundaryZ b e` it is `IsZeroEntranceChain`
(`isPortChain_boundaryZ_iff`). Nesting the cavity maps of the cavity-mean lemma over `J` layers
evaluated at the port `z'` produces exactly this system; we prove that it is solvable.

## Results

* `portChain_exists`: for `0 < b`, `0 < 1 - 2b`, every real `e`, every `J` and every `z'` with
  `Im z' > 0`, a solution exists. Proof: (1) for the regularized diagonal
  `d_k = -e + iε` (`k < J`), `d_J = z'`, `ε > 0`, the map `Φ(m)_k = (d_k - (Sm)_k)⁻¹` maps the
  closed lower half-plane product into a bounded set with imaginary parts bounded away from `0`,
  and it contracts the hyperbolic ratio `|m_k - m'_k|²/(Im m_k Im m'_k)` by the factor
  `Y/(ε' + Y) < 1` (`w ↦ w⁻¹` preserves the ratio; Cauchy–Schwarz for `S ≥ 0`); the iterates are
  Cauchy and converge to a fixed point; (2) the self-interaction and the port give bounds
  `|m_k| ≤ R`, `|m_k| ≥ r` and `-Im m_k ≥ (r² b)^{J-k} r² Im z'` uniform in `ε ∈ (0, 1]`;
  (3) along `ε = 1/(n+1)` a subsequence converges (compactness), and the limit solves the
  `ε = 0` system with strictly negative imaginary parts.
* `portChain_phys_bound` (`(1-2b)|m_ℓ|² ≤ 1`, `1 ≤ ℓ ≤ J`) and `portChain_port_ward`
  (`Im z' |m_{J+1}|² ≤ -Im m_{J+1}`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Complex Filter Topology BlockBand.Internal.Contracts.Layers

/-- the finite Dyson equation with zero boundary `m₀ = 0`, `c = 1 - 2b`, a
general port parameter `z'`, and negative imaginary parts. -/
structure IsPortChain (b e : ℝ) (J : ℕ) (z' : ℂ) (m : ℕ → ℂ) : Prop where
  zero : m 0 = 0
  im_neg : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ J + 1 → (m ℓ).im < 0
  bulk : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ J →
    (m ℓ)⁻¹ = -(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * m ℓ - b * m (ℓ - 1) - b * m (ℓ + 1)
  port : (m (J + 1))⁻¹ = z' - b * m J

/-- At the matched port `z = boundaryZ b e` the general chain is `IsZeroEntranceChain`. -/
theorem isPortChain_boundaryZ_iff {b e : ℝ} {J : ℕ} {m : ℕ → ℂ} :
    IsPortChain b e J (boundaryZ b e) m ↔ IsZeroEntranceChain b e J m :=
  ⟨fun h => ⟨h.zero, h.im_neg, h.bulk, h.port⟩, fun h => ⟨h.zero, h.im_neg, h.bulk, h.port⟩⟩

/-- The a priori bound for a general port: `(1-2b)|m_ℓ|² ≤ 1` on the physical sites. -/
theorem portChain_phys_bound {b e : ℝ} {J : ℕ} {z' : ℂ} {m : ℕ → ℂ} (h : IsPortChain b e J z' m)
    (hb : 0 ≤ b) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ J) :
    (1 - 2 * b) * ‖m ℓ‖ ^ 2 ≤ 1 := by
  have hy := h.im_neg ℓ h1 (by omega)
  have hm : m ℓ ≠ 0 := fun h0 => by rw [h0] at hy; simp at hy
  have hprev : (m (ℓ - 1)).im ≤ 0 := by
    rcases Nat.eq_zero_or_pos (ℓ - 1) with h0 | h0
    · rw [h0, h.zero]; simp
    · exact (h.im_neg (ℓ - 1) (by omega) (by omega)).le
  have hnext : (m (ℓ + 1)).im ≤ 0 := (h.im_neg (ℓ + 1) (by omega) (by omega)).le
  have hE := congrArg Complex.im (h.bulk ℓ h1 h2)
  rw [CavityMean.inv_im_eq, norm_inv] at hE
  simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re] at hE
  have hn : 0 < ‖m ℓ‖ := norm_pos_iff.mpr hm
  have key : (1 - 2 * b) * (-(m ℓ).im) ≤ (-(m ℓ).im) * (‖m ℓ‖⁻¹ ^ 2) := by
    nlinarith [mul_nonneg hb (neg_nonneg.mpr hprev), mul_nonneg hb (neg_nonneg.mpr hnext)]
  have hyp : 0 < -(m ℓ).im := by linarith
  have : (1 - 2 * b) ≤ ‖m ℓ‖⁻¹ ^ 2 := by
    have := (mul_le_mul_iff_left₀ hyp).mp (by linarith [key] :
      (1 - 2 * b) * (-(m ℓ).im) ≤ ‖m ℓ‖⁻¹ ^ 2 * (-(m ℓ).im))
    exact this
  rw [inv_pow] at this
  have hn2 : 0 < ‖m ℓ‖ ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_right this hn2.le
  rwa [inv_mul_cancel₀ hn2.ne'] at h3

/-- The port Ward inequality `Im z' |m_{J+1}|² ≤ -Im m_{J+1}`. -/
theorem portChain_port_ward {b e : ℝ} {J : ℕ} {z' : ℂ} {m : ℕ → ℂ} (h : IsPortChain b e J z' m)
    (hb : 0 ≤ b) : z'.im * ‖m (J + 1)‖ ^ 2 ≤ -(m (J + 1)).im := by
  have hJ : (m J).im ≤ 0 := by
    rcases Nat.eq_zero_or_pos J with h0 | h0
    · rw [h0, h.zero]; simp
    · exact (h.im_neg J (by omega) (by omega)).le
  have hy := h.im_neg (J + 1) (by omega) le_rfl
  have hm : m (J + 1) ≠ 0 := fun h0 => by rw [h0] at hy; simp at hy
  have hE := congrArg Complex.im h.port
  rw [CavityMean.inv_im_eq] at hE
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero] at hE
  have hn : 0 < ‖m (J + 1)‖ := norm_pos_iff.mpr hm
  have hinv : ‖(m (J + 1))⁻¹‖ ^ 2 * ‖m (J + 1)‖ ^ 2 = 1 := by
    rw [norm_inv, ← mul_pow, inv_mul_cancel₀ hn.ne', one_pow]
  -- `-Im m = Im(m⁻¹) |m|²` and `Im(m⁻¹) = Im z' - b Im m_J ≥ Im z'`
  have h1 : -(m (J + 1)).im = (z'.im - b * (m J).im) * ‖m (J + 1)‖ ^ 2 := by
    rw [← hE]
    calc -(m (J + 1)).im = -(m (J + 1)).im * (‖(m (J + 1))⁻¹‖ ^ 2 * ‖m (J + 1)‖ ^ 2) := by
          rw [hinv, mul_one]
      _ = _ := by ring
  rw [h1]
  have : z'.im ≤ z'.im - b * (m J).im := by nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

namespace PortChain

open ZeroEntrance

/-!
## The regularized system on positions `0, …, J`
-/

/-- The diagonal vector `d^ε = (-e + iε, …, -e + iε, z')`. -/
def dReg (e ε : ℝ) (J : ℕ) (z' : ℂ) (k : Fin (J + 1)) : ℂ :=
  if (k : ℕ) < J then -(e : ℂ) + (ε : ℂ) * Complex.I else z'

/-- `w_k = d^ε_k - (S m)_k`. -/
def wArg (b e ε : ℝ) (J : ℕ) (z' : ℂ) (m : Fin (J + 1) → ℂ) (k : Fin (J + 1)) : ℂ :=
  dReg e ε J z' k - cmv (chainSf b J) m k

/-- `y_k = -Im m_k`. -/
def yv {J : ℕ} (m : Fin (J + 1) → ℂ) (k : Fin (J + 1)) : ℝ := -(m k).im

variable {b e : ℝ} {J : ℕ} {z' : ℂ}

theorem dReg_im (ε : ℝ) (k : Fin (J + 1)) :
    (dReg e ε J z' k).im = if (k : ℕ) < J then ε else z'.im := by
  unfold dReg; split_ifs <;> simp

theorem dReg_im_ge {ε ε' : ℝ} (hε : ε' ≤ ε) (hz : ε' ≤ z'.im) (k : Fin (J + 1)) :
    ε' ≤ (dReg e ε J z' k).im := by
  rw [dReg_im]; split_ifs <;> assumption

theorem dReg_norm_le {ε : ℝ} (hε : 0 ≤ ε) (k : Fin (J + 1)) :
    ‖dReg e ε J z' k‖ ≤ |e| + ε + ‖z'‖ := by
  unfold dReg
  split_ifs
  · refine (norm_add_le _ _).trans ?_
    rw [norm_neg, Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_of_nonneg hε]
    linarith [norm_nonneg z']
  · linarith [abs_nonneg e]

theorem wArg_im (ε : ℝ) (m : Fin (J + 1) → ℂ) (k : Fin (J + 1)) :
    (wArg b e ε J z' m k).im = (dReg e ε J z' k).im + mv (chainSf b J) (yv m) k := by
  unfold wArg
  rw [Complex.sub_im, cmv_im]
  unfold mv yv
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem mv_nonneg' (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b) {y : Fin (J + 1) → ℝ} (hy : ∀ l, 0 ≤ y l)
    (k : Fin (J + 1)) : 0 ≤ mv (chainSf b J) y k :=
  Finset.sum_nonneg fun l _ => mul_nonneg (chainSf_nonneg hb hc k l) (hy l)

theorem mv_le' (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b) {y : Fin (J + 1) → ℝ} {Y : ℝ} (hY : 0 ≤ Y)
    (hy : ∀ l, y l ≤ Y) (k : Fin (J + 1)) : mv (chainSf b J) y k ≤ Y := by
  unfold mv
  calc ∑ l, chainSf b J k l * y l ≤ ∑ l, chainSf b J k l * Y :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hy l) (chainSf_nonneg hb hc k l)
    _ = (∑ l, chainSf b J k l) * Y := by rw [Finset.sum_mul]
    _ ≤ 1 * Y := mul_le_mul_of_nonneg_right (chainSf_rowsum_le hb hc k) hY
    _ = Y := one_mul Y

theorem norm_cmv_le (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b) {m : Fin (J + 1) → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hm : ∀ l, ‖m l‖ ≤ B) (k : Fin (J + 1)) : ‖cmv (chainSf b J) m k‖ ≤ B := by
  unfold cmv
  refine (norm_sum_le _ _).trans ?_
  have := mv_le' hb hc hB hm k
  unfold mv at this
  refine le_trans (le_of_eq ?_) this
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (chainSf_nonneg hb hc k l)]

/-!
## The map `Φ`
-/

section Phi

theorem wArg_im_ge {ε ε' : ℝ} (hε : ε' ≤ ε) (hz : ε' ≤ z'.im) {m : Fin (J + 1) → ℂ}
    (k : Fin (J + 1)) :
    ε' + mv (chainSf b J) (yv m) k ≤ (wArg b e ε J z' m k).im := by
  rw [wArg_im]; linarith [dReg_im_ge (e := e) hε hz k]

theorem yv_inv_eq (w : ℂ) : -(w⁻¹).im = w.im * ‖w⁻¹‖ ^ 2 := by
  rw [CavityMean.inv_im_eq]; ring

/-- `Φ` maps the closed lower half-plane into a bounded set with `Im < 0`. -/
theorem phi_facts (hb : 0 < b) (hc : 0 < 1 - 2 * b) {ε ε' : ℝ} (hε' : 0 < ε') (hε : ε' ≤ ε) (hz : ε' ≤ z'.im)
    {m : Fin (J + 1) → ℂ} (hm : ∀ l, (m l).im ≤ 0) (k : Fin (J + 1)) :
    ‖(wArg b e ε J z' m k)⁻¹‖ ≤ 1 / ε' ∧ ((wArg b e ε J z' m k)⁻¹).im < 0 := by
  have hy : ∀ l, 0 ≤ yv m l := fun l => by unfold yv; linarith [hm l]
  have hw := wArg_im_ge (e := e) (b := b) (m := m) hε hz k
  have hS := mv_nonneg' hb.le hc.le hy k
  have hwi : 0 < (wArg b e ε J z' m k).im := by linarith
  refine ⟨CavityMean.norm_inv_le_of_im hε' (by linarith), ?_⟩
  have hne : wArg b e ε J z' m k ≠ 0 := CavityMean.ne_zero_of_im_pos hwi
  have := yv_inv_eq (wArg b e ε J z' m k)
  have hn : 0 < ‖(wArg b e ε J z' m k)⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hne)
  have : 0 < -((wArg b e ε J z' m k)⁻¹).im := by rw [this]; positivity
  linarith

/-- The imaginary lower bound of `Φ` on a bounded set. -/
theorem phi_im_lower (hb : 0 < b) (hc : 0 < 1 - 2 * b) {ε ε' B : ℝ} (hε0 : 0 ≤ ε) (hε' : 0 < ε') (hε : ε' ≤ ε) (hz : ε' ≤ z'.im)
    (hB : 0 ≤ B) {m : Fin (J + 1) → ℂ} (hm : ∀ l, (m l).im ≤ 0) (hmB : ∀ l, ‖m l‖ ≤ B)
    (k : Fin (J + 1)) :
    ε' * (1 / (|e| + ε + ‖z'‖ + B)) ^ 2 ≤ -((wArg b e ε J z' m k)⁻¹).im := by
  have hy : ∀ l, 0 ≤ yv m l := fun l => by unfold yv; linarith [hm l]
  have hw := wArg_im_ge (e := e) (b := b) (m := m) hε hz k
  have hS := mv_nonneg' hb.le hc.le hy k
  rw [yv_inv_eq]
  have hwn : ‖wArg b e ε J z' m k‖ ≤ |e| + ε + ‖z'‖ + B := by
    unfold wArg
    exact (norm_sub_le _ _).trans (add_le_add (dReg_norm_le hε0 k) (norm_cmv_le hb.le hc.le hB hmB k))
  have hwi : 0 < (wArg b e ε J z' m k).im := by linarith
  have hne : wArg b e ε J z' m k ≠ 0 := CavityMean.ne_zero_of_im_pos hwi
  have hpos : 0 < ‖wArg b e ε J z' m k‖ := norm_pos_iff.mpr hne
  have h1 : 1 / (|e| + ε + ‖z'‖ + B) ≤ ‖(wArg b e ε J z' m k)⁻¹‖ := by
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hpos hwn
  have h2 : (1 / (|e| + ε + ‖z'‖ + B)) ^ 2 ≤ ‖(wArg b e ε J z' m k)⁻¹‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  exact mul_le_mul (by linarith) h2 (by positivity) hwi.le

/-- **Contraction of the hyperbolic ratio** under `Φ`. -/
theorem phi_contract (hb : 0 < b) (hc : 0 < 1 - 2 * b) {ε ε' R Y : ℝ} (hε' : 0 < ε') (hε : ε' ≤ ε) (hz : ε' ≤ z'.im) (hR : 0 ≤ R)
    (hY : 0 ≤ Y) {m m' : Fin (J + 1) → ℂ} (hm : ∀ l, (m l).im ≤ 0) (hm' : ∀ l, (m' l).im ≤ 0)
    (hmY : ∀ l, yv m l ≤ Y)
    (hd : ∀ l, ‖m l - m' l‖ ^ 2 ≤ R * (yv m l * yv m' l)) (k : Fin (J + 1)) :
    ‖(wArg b e ε J z' m k)⁻¹ - (wArg b e ε J z' m' k)⁻¹‖ ^ 2 ≤
      (Y / (ε' + Y)) * R * ((-((wArg b e ε J z' m k)⁻¹).im) *
        (-((wArg b e ε J z' m' k)⁻¹).im)) := by
  set w := wArg b e ε J z' m k
  set w' := wArg b e ε J z' m' k
  have hy : ∀ l, 0 ≤ yv m l := fun l => by unfold yv; linarith [hm l]
  have hy' : ∀ l, 0 ≤ yv m' l := fun l => by unfold yv; linarith [hm' l]
  set sy := mv (chainSf b J) (yv m) k
  set sy' := mv (chainSf b J) (yv m') k
  have hsy := mv_nonneg' hb.le hc.le hy k
  have hsy' := mv_nonneg' hb.le hc.le hy' k
  have hsyY : sy ≤ Y := mv_le' hb.le hc.le hY hmY k
  have hw : ε' + sy ≤ w.im := wArg_im_ge (e := e) (b := b) (m := m) hε hz k
  have hw' : ε' + sy' ≤ w'.im := wArg_im_ge (e := e) (b := b) (m := m') hε hz k
  have hwi : 0 < w.im := by linarith
  have hwi' : 0 < w'.im := by linarith
  have hne : w ≠ 0 := CavityMean.ne_zero_of_im_pos hwi
  have hne' : w' ≠ 0 := CavityMean.ne_zero_of_im_pos hwi'
  -- `|w - w'|² ≤ R sy sy'`
  have hdiff : ‖w - w'‖ ^ 2 ≤ R * (sy * sy') := by
    have hww : w - w' = cmv (chainSf b J) m' k - cmv (chainSf b J) m k := by
      simp only [w, w', wArg]; ring
    have hsum : ‖w - w'‖ ≤ ∑ l, chainSf b J k l * (Real.sqrt R * (Real.sqrt (yv m l) *
        Real.sqrt (yv m' l))) := by
      rw [hww]
      unfold cmv
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [← mul_sub, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (chainSf_nonneg hb.le hc.le k l)]
      refine mul_le_mul_of_nonneg_left ?_ (chainSf_nonneg hb.le hc.le k l)
      rw [norm_sub_rev, ← Real.sqrt_mul (hy l), ← Real.sqrt_mul hR, ← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (hd l)
    have hcs := CavityMean.weighted_cs (chainSf b J k) (fun l => Real.sqrt (yv m l))
      (fun l => Real.sqrt (yv m' l)) (fun l => chainSf_nonneg hb.le hc.le k l)
    simp only [Real.sq_sqrt (hy _), Real.sq_sqrt (hy' _)] at hcs
    have hre : ∑ l, chainSf b J k l * (Real.sqrt R * (Real.sqrt (yv m l) *
        Real.sqrt (yv m' l))) = Real.sqrt R * ∑ l, chainSf b J k l * Real.sqrt (yv m l) *
          Real.sqrt (yv m' l) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [hre] at hsum
    have h0 : 0 ≤ ‖w - w'‖ := norm_nonneg _
    calc ‖w - w'‖ ^ 2 ≤ (Real.sqrt R * ∑ l, chainSf b J k l * Real.sqrt (yv m l) *
          Real.sqrt (yv m' l)) ^ 2 := pow_le_pow_left₀ h0 hsum 2
      _ = R * (∑ l, chainSf b J k l * Real.sqrt (yv m l) * Real.sqrt (yv m' l)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hR]
      _ ≤ R * (sy * sy') := mul_le_mul_of_nonneg_left hcs hR
  -- `sy sy' ≤ κ Im w Im w'`
  have hκ : sy ≤ Y / (ε' + Y) * w.im := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  have hprod : sy * sy' ≤ Y / (ε' + Y) * (w.im * w'.im) := by
    have := mul_le_mul hκ (by linarith : sy' ≤ w'.im) hsy' (by positivity)
    linarith
  -- the inversion identity
  have hinv : w⁻¹ - w'⁻¹ = (w' - w) * (w⁻¹ * w'⁻¹) := by field_simp
  rw [yv_inv_eq w, yv_inv_eq w', hinv, norm_mul, norm_mul, mul_pow, mul_pow,
    norm_sub_rev]
  have hn : 0 ≤ ‖w⁻¹‖ ^ 2 * ‖w'⁻¹‖ ^ 2 := by positivity
  calc ‖w - w'‖ ^ 2 * (‖w⁻¹‖ ^ 2 * ‖w'⁻¹‖ ^ 2)
      ≤ (R * (Y / (ε' + Y) * (w.im * w'.im))) * (‖w⁻¹‖ ^ 2 * ‖w'⁻¹‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (hdiff.trans (mul_le_mul_of_nonneg_left hprod hR)) hn
    _ = Y / (ε' + Y) * R * (w.im * ‖w⁻¹‖ ^ 2 * (w'.im * ‖w'⁻¹‖ ^ 2)) := by ring

end Phi

/-!
## Step (1): the regularized system has a solution
-/

section Exist

/-- The iterates `u n = Φ^{n+1}(0)` of the regularized map. -/
def iter (b e ε : ℝ) (J : ℕ) (z' : ℂ) : ℕ → Fin (J + 1) → ℂ
  | 0 => fun k => (wArg b e ε J z' (fun _ => 0) k)⁻¹
  | n + 1 => fun k => (wArg b e ε J z' (iter b e ε J z' n) k)⁻¹

theorem sqrt_pow_sq (κ : ℝ) (hκ : 0 ≤ κ) (n : ℕ) : (Real.sqrt κ ^ n) ^ 2 = κ ^ n := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hκ]

/-- **Step (1)**: for `ε > 0` the regularized system `m_k = (d^ε_k - (S m)_k)⁻¹` has a solution
with negative imaginary parts. -/
theorem reg_exists (hb : 0 < b) (hc : 0 < 1 - 2 * b) {ε : ℝ} (hε : 0 < ε) (hz : 0 < z'.im) :
    ∃ m : Fin (J + 1) → ℂ, (∀ k, (m k).im < 0) ∧ ∀ k, m k = (wArg b e ε J z' m k)⁻¹ := by
  set ε' := min ε z'.im with hε'def
  have hε' : 0 < ε' := lt_min hε hz
  have h1 : ε' ≤ ε := min_le_left _ _
  have h2 : ε' ≤ z'.im := min_le_right _ _
  set B := 1 / ε' with hBdef
  have hB : 0 < B := by positivity
  have hA : 0 < |e| + ε + ‖z'‖ + B := by positivity
  set y₀ := ε' * (1 / (|e| + ε + ‖z'‖ + B)) ^ 2 with hy₀def
  have hy₀ : 0 < y₀ := by positivity
  set u := iter b e ε J z' with hudef
  -- one application of `Φ`
  have hstep : ∀ m : Fin (J + 1) → ℂ, (∀ l, (m l).im ≤ 0) → (∀ l, ‖m l‖ ≤ B) → ∀ k,
      ‖(wArg b e ε J z' m k)⁻¹‖ ≤ B ∧ ((wArg b e ε J z' m k)⁻¹).im < 0 ∧
        y₀ ≤ -((wArg b e ε J z' m k)⁻¹).im := by
    intro m hm hmB k
    obtain ⟨hn, hi⟩ := phi_facts (e := e) hb hc hε' h1 h2 hm k
    exact ⟨hn, hi, phi_im_lower hb hc hε.le hε' h1 h2 hB.le hm hmB k⟩
  have hfact : ∀ n l, ‖u n l‖ ≤ B ∧ (u n l).im < 0 ∧ y₀ ≤ yv (u n) l := by
    intro n
    induction n with
    | zero =>
      intro l
      exact hstep (fun _ => 0) (fun _ => by simp) (fun _ => by simp [hB.le]) l
    | succ n ih =>
      intro l
      exact hstep (u n) (fun l => (ih l).2.1.le) (fun l => (ih l).1) l
  have hsucc : ∀ n l, u (n + 1) l = (wArg b e ε J z' (u n) l)⁻¹ := fun n l => rfl
  -- contraction of the ratio
  set κ := B / (ε' + B) with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ < 1 := by rw [hκdef, div_lt_one (by linarith)]; linarith
  set R₀ := (2 * B) ^ 2 / y₀ ^ 2 with hR₀def
  have hR₀ : 0 ≤ R₀ := by positivity
  have hyB : ∀ n l, yv (u n) l ≤ B := fun n l => by
    unfold yv
    have := Complex.abs_im_le_norm (u n l)
    rw [abs_le] at this
    linarith [(hfact n l).1]
  have hratio : ∀ n l, ‖u n l - u (n + 1) l‖ ^ 2 ≤
      R₀ * κ ^ n * (yv (u n) l * yv (u (n + 1)) l) := by
    intro n
    induction n with
    | zero =>
      intro l
      have hd : ‖u 0 l - u (0 + 1) l‖ ≤ 2 * B := by
        refine (norm_sub_le _ _).trans ?_
        linarith [(hfact 0 l).1, (hfact (0 + 1) l).1]
      have hsq : ‖u 0 l - u (0 + 1) l‖ ^ 2 ≤ (2 * B) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hd 2
      have hyy : y₀ * y₀ ≤ yv (u 0) l * yv (u (0 + 1)) l :=
        mul_le_mul (hfact 0 l).2.2 (hfact (0 + 1) l).2.2 hy₀.le (by linarith [(hfact 0 l).2.2])
      have : (2 * B) ^ 2 = R₀ * (y₀ * y₀) := by
        rw [hR₀def]; field_simp
      rw [pow_zero, mul_one]
      calc ‖u 0 l - u (0 + 1) l‖ ^ 2 ≤ (2 * B) ^ 2 := hsq
        _ = R₀ * (y₀ * y₀) := this
        _ ≤ R₀ * (yv (u 0) l * yv (u (0 + 1)) l) := mul_le_mul_of_nonneg_left hyy hR₀
    | succ n ih =>
      intro l
      have hc' := phi_contract (e := e) hb hc hε' h1 h2 (by positivity : 0 ≤ R₀ * κ ^ n) hB.le
        (fun l => (hfact n l).2.1.le) (fun l => (hfact (n + 1) l).2.1.le) (hyB n) ih l
      rw [← hsucc, ← hsucc] at hc'
      have e1 : yv (u (n + 1)) l = -((u (n + 1)) l).im := rfl
      rw [e1]
      calc ‖u (n + 1) l - u (n + 1 + 1) l‖ ^ 2 ≤ κ * (R₀ * κ ^ n) *
            (-(u (n + 1) l).im * -(u (n + 1 + 1) l).im) := hc'
        _ = R₀ * κ ^ (n + 1) * (-(u (n + 1) l).im * yv (u (n + 1 + 1)) l) := by
            unfold yv; ring
  -- geometric bound on distances
  have hdist : ∀ n, dist (u n) (u (n + 1)) ≤ (Real.sqrt R₀ * B) * Real.sqrt κ ^ n := by
    intro n
    rw [dist_pi_le_iff (by positivity)]
    intro l
    rw [dist_eq_norm]
    have hyy : yv (u n) l * yv (u (n + 1)) l ≤ B * B :=
      mul_le_mul (hyB n l) (hyB (n + 1) l) (by linarith [(hfact (n + 1) l).2.2]) hB.le
    have hsq : ‖u n l - u (n + 1) l‖ ^ 2 ≤ (Real.sqrt R₀ * B * Real.sqrt κ ^ n) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hR₀, sqrt_pow_sq κ hκ0]
      calc ‖u n l - u (n + 1) l‖ ^ 2 ≤ R₀ * κ ^ n * (yv (u n) l * yv (u (n + 1)) l) :=
            hratio n l
        _ ≤ R₀ * κ ^ n * (B * B) := mul_le_mul_of_nonneg_left hyy (by positivity)
        _ = R₀ * B ^ 2 * κ ^ n := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hsk : Real.sqrt κ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt hκ0 hκ1
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric _ _ hsk hdist
  obtain ⟨m, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hcoord : ∀ l, Tendsto (fun n => u n l) atTop (𝓝 (m l)) := fun l => tendsto_pi_nhds.1 hlim l
  have him : ∀ l, y₀ ≤ -(m l).im := fun l =>
    ge_of_tendsto' ((Complex.continuous_im.tendsto _).comp (hcoord l)).neg
      (fun n => (hfact n l).2.2)
  have hmim : ∀ l, (m l).im < 0 := fun l => by linarith [him l]
  refine ⟨m, hmim, fun k => ?_⟩
  have hw : Tendsto (fun n => wArg b e ε J z' (u n) k) atTop (𝓝 (wArg b e ε J z' m k)) := by
    unfold wArg cmv
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun l _ =>
      tendsto_const_nhds.mul (hcoord l))
  have hne : wArg b e ε J z' m k ≠ 0 := by
    have := wArg_im_ge (e := e) (b := b) (m := m) h1 h2 k
    have hS := mv_nonneg' hb.le hc.le (y := yv m) (fun l => by unfold yv; linarith [hmim l]) k
    exact CavityMean.ne_zero_of_im_pos (by linarith)
  have h3 : Tendsto (fun n => u (n + 1) k) atTop (𝓝 ((wArg b e ε J z' m k)⁻¹)) := by
    simp only [hsucc]
    exact hw.inv₀ hne
  have h4 : Tendsto (fun n => u (n + 1) k) atTop (𝓝 (m k)) :=
    (hcoord k).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h4 h3

end Exist

/-!
## Step (2): bounds uniform in `ε ∈ [0, 1]`
-/

section Bounds

/-- The upper bound `R = 1/(1-2b) + 1 + 1/Im z'`. -/
def bigR (b : ℝ) (z' : ℂ) : ℝ := 1 / (1 - 2 * b) + 1 + 1 / z'.im

/-- The lower bound `r = 1/(|e| + 1 + |z'| + R)`. -/
def smallR (b e : ℝ) (z' : ℂ) : ℝ := 1 / (|e| + 1 + ‖z'‖ + bigR b z')

theorem chainSf_diag' (k : Fin (J + 1)) (hk : (k : ℕ) < J) : chainSf b J k k = 1 - 2 * b := by
  unfold chainSf; rw [chainS_diag]; simp [hk]

theorem chainSf_next (k l : Fin (J + 1)) (hkl : (l : ℕ) = (k : ℕ) + 1) : chainSf b J k l = b := by
  unfold chainSf chainS
  simp only [hkl]
  simp only [one_ne_zero, ↓reduceIte, zero_add, add_eq_left]
  have h3 : ¬ ((k : ℕ) = (k : ℕ) + 1 + 1) := by omega
  simp [h3]

theorem mv_ge_single (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b) {y : Fin (J + 1) → ℝ} (hy : ∀ l, 0 ≤ y l)
    (k l : Fin (J + 1)) : chainSf b J k l * y l ≤ mv (chainSf b J) y k :=
  Finset.single_le_sum (f := fun l => chainSf b J k l * y l)
    (fun l _ => mul_nonneg (chainSf_nonneg hb hc k l) (hy l)) (Finset.mem_univ l)

/-- **Step (2)**: a solution of the system with `0 ≤ ε ≤ 1` obeys `r ≤ |m_k| ≤ R` and
`-Im m_{J-i} ≥ (r² b)^i r² Im z'`. -/
theorem reg_bounds (hb : 0 < b) (hc : 0 < 1 - 2 * b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hz : 0 < z'.im) {m : Fin (J + 1) → ℂ} (hmim : ∀ k, (m k).im < 0)
    (hm : ∀ k, m k = (wArg b e ε J z' m k)⁻¹) :
    (∀ k, ‖m k‖ ≤ bigR b z') ∧ (∀ k, smallR b e z' ≤ ‖m k‖) ∧
      ∀ i (hi : i ≤ J), (smallR b e z' ^ 2 * b) ^ i * (smallR b e z' ^ 2 * z'.im) ≤
        yv m ⟨J - i, by omega⟩ := by
  have hy : ∀ l, 0 < yv m l := fun l => by unfold yv; linarith [hmim l]
  have hyv : ∀ k, yv m k = (wArg b e ε J z' m k).im * ‖m k‖ ^ 2 := fun k => by
    unfold yv; rw [hm k, yv_inv_eq, ← hm k]
  have hwim : ∀ k, (wArg b e ε J z' m k).im = (dReg e ε J z' k).im + mv (chainSf b J) (yv m) k :=
    fun k => wArg_im ε m k
  have hS : ∀ k, 0 ≤ mv (chainSf b J) (yv m) k :=
    fun k => mv_nonneg' hb.le hc.le (fun l => (hy l).le) k
  have hRpos : 0 < bigR b z' := by unfold bigR; positivity
  have hup : ∀ k, ‖m k‖ ≤ bigR b z' := by
    intro k
    have hyk := hyv k
    rw [hwim k, dReg_im] at hyk
    by_cases hk : (k : ℕ) < J
    · simp only [hk, ↓reduceIte] at hyk
      have hsingle := mv_ge_single hb.le hc.le (fun l => (hy l).le) k k
      rw [chainSf_diag' k hk] at hsingle
      have hcm : (1 - 2 * b) * ‖m k‖ ^ 2 ≤ 1 := by
        have ha : (1 - 2 * b) * yv m k * ‖m k‖ ^ 2 ≤
            mv (chainSf b J) (yv m) k * ‖m k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsingle (sq_nonneg _)
        have hb2 : mv (chainSf b J) (yv m) k * ‖m k‖ ^ 2 ≤ yv m k := by
          rw [hyk]; nlinarith [sq_nonneg ‖m k‖]
        have h0 : (1 - 2 * b) * ‖m k‖ ^ 2 * yv m k ≤ 1 * yv m k := by nlinarith
        exact le_of_mul_le_mul_right h0 (hy k)
      have hx : ‖m k‖ ^ 2 ≤ 1 / (1 - 2 * b) := by
        rw [le_div_iff₀ hc]; linarith
      have : ‖m k‖ ≤ 1 + ‖m k‖ ^ 2 := by nlinarith [sq_nonneg (‖m k‖ - 1)]
      unfold bigR
      have : 0 ≤ 1 / z'.im := by positivity
      linarith
    · simp only [hk, ↓reduceIte] at hyk
      have hyle : yv m k ≤ ‖m k‖ := by
        unfold yv
        have := Complex.abs_im_le_norm (m k); rw [abs_le] at this; linarith
      have hn : 0 < ‖m k‖ := lt_of_lt_of_le (hy k) hyle
      have h0 : z'.im * ‖m k‖ ^ 2 ≤ ‖m k‖ := by
        nlinarith [hS k, sq_nonneg ‖m k‖]
      have h1 : z'.im * ‖m k‖ ≤ 1 := by
        have : z'.im * ‖m k‖ * ‖m k‖ ≤ 1 * ‖m k‖ := by nlinarith
        exact le_of_mul_le_mul_right this hn
      have h2 : ‖m k‖ ≤ 1 / z'.im := by rw [le_div_iff₀ hz]; linarith
      unfold bigR
      have : 0 ≤ 1 / (1 - 2 * b) := by positivity
      linarith
  have hlow : ∀ k, smallR b e z' ≤ ‖m k‖ := by
    intro k
    have hwn : ‖wArg b e ε J z' m k‖ ≤ |e| + 1 + ‖z'‖ + bigR b z' := by
      unfold wArg
      refine (norm_sub_le _ _).trans ?_
      have := dReg_norm_le (e := e) (J := J) (z' := z') hε0 k
      have := norm_cmv_le hb.le hc.le hRpos.le hup k
      linarith
    have hne : wArg b e ε J z' m k ≠ 0 := by
      intro h0; have := hmim k; rw [hm k, h0, inv_zero] at this; simp at this
    have hpos : 0 < ‖wArg b e ε J z' m k‖ := norm_pos_iff.mpr hne
    rw [hm k, norm_inv]
    unfold smallR
    rw [← one_div]
    exact one_div_le_one_div_of_le hpos hwn
  have hr : 0 < smallR b e z' := by unfold smallR; positivity
  refine ⟨hup, hlow, ?_⟩
  intro i
  induction i with
  | zero =>
    intro hi
    set k : Fin (J + 1) := ⟨J - 0, by omega⟩
    have hk : ¬ (k : ℕ) < J := by simp [k]
    have hyk := hyv k
    rw [hwim k, dReg_im] at hyk
    simp only [hk, ↓reduceIte] at hyk
    have hr2 : smallR b e z' ^ 2 ≤ ‖m k‖ ^ 2 := pow_le_pow_left₀ hr.le (hlow k) 2
    rw [pow_zero, one_mul, hyk]
    nlinarith [hS k]
  | succ i ih =>
    intro hi
    set k : Fin (J + 1) := ⟨J - (i + 1), by omega⟩
    set kp : Fin (J + 1) := ⟨J - i, by omega⟩
    have hk : (k : ℕ) < J := by simp [k]; omega
    have hkp : (kp : ℕ) = (k : ℕ) + 1 := by simp [k, kp]; omega
    have hyk := hyv k
    rw [hwim k, dReg_im] at hyk
    simp only [hk, ↓reduceIte] at hyk
    have hsingle := mv_ge_single hb.le hc.le (fun l => (hy l).le) k kp
    rw [chainSf_next k kp hkp] at hsingle
    have hr2 : smallR b e z' ^ 2 ≤ ‖m k‖ ^ 2 := pow_le_pow_left₀ hr.le (hlow k) 2
    have hih := ih (by omega)
    have hL : 0 ≤ (smallR b e z' ^ 2 * b) ^ i * (smallR b e z' ^ 2 * z'.im) := by positivity
    have hwk : b * yv m kp ≤ ε + mv (chainSf b J) (yv m) k := by linarith
    have e1 : (smallR b e z' ^ 2 * b) ^ (i + 1) * (smallR b e z' ^ 2 * z'.im) =
        (b * ((smallR b e z' ^ 2 * b) ^ i * (smallR b e z' ^ 2 * z'.im))) * smallR b e z' ^ 2 := by
      ring
    rw [e1, hyk]
    have hb' : 0 ≤ b * ((smallR b e z' ^ 2 * b) ^ i * (smallR b e z' ^ 2 * z'.im)) := by positivity
    have : b * ((smallR b e z' ^ 2 * b) ^ i * (smallR b e z' ^ 2 * z'.im)) ≤
        ε + mv (chainSf b J) (yv m) k := by
      have := mul_le_mul_of_nonneg_left hih hb.le
      linarith
    exact mul_le_mul this hr2 (by positivity) (by linarith)

end Bounds

/-!
## Step (3): the limit `ε → 0`
-/

section Limit

/-- The vector solution of the `ε = 0` system as a sequence (`m₀ = 0`, `m_ℓ = a_{ℓ-1}`). -/
def toSeq (a : Fin (J + 1) → ℂ) (ℓ : ℕ) : ℂ :=
  if h : 1 ≤ ℓ ∧ ℓ ≤ J + 1 then a ⟨ℓ - 1, by omega⟩ else 0

theorem toSeq_succ (a : Fin (J + 1) → ℂ) (l : Fin (J + 1)) : toSeq a ((l : ℕ) + 1) = a l := by
  unfold toSeq
  split_ifs with h
  · exact congrArg a (Fin.ext (by simp))
  · exact absurd ⟨by omega, by omega⟩ h

theorem toSeq_zero (a : Fin (J + 1) → ℂ) : toSeq a 0 = 0 := by
  unfold toSeq; simp

/-- The solution of the `ε = 0` system: existence. -/
theorem lim_exists (hb : 0 < b) (hc : 0 < 1 - 2 * b) (hz : 0 < z'.im) :
    ∃ a : Fin (J + 1) → ℂ, (∀ k, (a k).im < 0) ∧ ∀ k, a k = (wArg b e 0 J z' a k)⁻¹ := by
  set εs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεs
  have hεpos : ∀ n, 0 < εs n := fun n => by simp only [hεs]; positivity
  have hε1 : ∀ n, εs n ≤ 1 := fun n => by
    simp only [hεs]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hreg : ∀ n : ℕ, ∃ m : Fin (J + 1) → ℂ, (∀ k, (m k).im < 0) ∧
      ∀ k, m k = (wArg b e (εs n) J z' m k)⁻¹ := fun n => reg_exists hb hc (hεpos n) hz
  choose sol hsim hseq using hreg
  have hbd := fun n => reg_bounds (e := e) hb hc (hεpos n).le (hε1 n) hz (hsim n) (hseq n)
  have hRpos : 0 < bigR b z' := by unfold bigR; positivity
  have hmem : ∀ n, sol n ∈ Metric.closedBall (0 : Fin (J + 1) → ℂ) (bigR b z') := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hRpos.le]
    exact (hbd n).1
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : Fin (J + 1) → ℂ) (bigR b z')).tendsto_subseq hmem
  have hcoord : ∀ l, Tendsto (fun n => sol (φ n) l) atTop (𝓝 (a l)) := fun l =>
    tendsto_pi_nhds.1 hlim l
  have hεlim : Tendsto (fun n => εs (φ n)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hr : 0 < smallR b e z' := by unfold smallR; positivity
  -- imaginary parts
  have him : ∀ k, (a k).im < 0 := by
    intro k
    set i := J - (k : ℕ)
    have hi : i ≤ J := Nat.sub_le _ _
    have hk : (⟨J - i, by omega⟩ : Fin (J + 1)) = k := Fin.ext (by simp [i]; omega)
    have hL : 0 < (smallR b e z' ^ 2 * b) ^ i * (smallR b e z' ^ 2 * z'.im) := by positivity
    have hle : ∀ n, (smallR b e z' ^ 2 * b) ^ i * (smallR b e z' ^ 2 * z'.im) ≤
        -(sol (φ n) k).im := by
      intro n
      have := (hbd (φ n)).2.2 i hi
      rw [hk] at this
      exact this
    have := ge_of_tendsto' ((Complex.continuous_im.tendsto _).comp (hcoord k)).neg hle
    linarith
  refine ⟨a, him, fun k => ?_⟩
  have hd : Tendsto (fun n => dReg e (εs (φ n)) J z' k) atTop (𝓝 (dReg e 0 J z' k)) := by
    unfold dReg
    split_ifs
    · exact tendsto_const_nhds.add
        (((Complex.continuous_ofReal.tendsto 0).comp hεlim).mul_const Complex.I)
    · exact tendsto_const_nhds
  have hw : Tendsto (fun n => wArg b e (εs (φ n)) J z' (sol (φ n)) k) atTop
      (𝓝 (wArg b e 0 J z' a k)) := by
    unfold wArg cmv
    exact hd.sub (tendsto_finsetSum _ fun l _ => tendsto_const_nhds.mul (hcoord l))
  have hone : ∀ n, sol (φ n) k * wArg b e (εs (φ n)) J z' (sol (φ n)) k = 1 := by
    intro n
    have hne : wArg b e (εs (φ n)) J z' (sol (φ n)) k ≠ 0 := by
      intro h0
      have := hsim (φ n) k
      rw [hseq (φ n) k, h0, inv_zero] at this
      simp at this
    rw [hseq (φ n) k]
    exact inv_mul_cancel₀ hne
  have hprod := (hcoord k).mul hw
  have hfun : (fun n => sol (φ n) k * wArg b e (εs (φ n)) J z' (sol (φ n)) k) = fun _ => 1 :=
    funext hone
  rw [hfun] at hprod
  have h1 : a k * wArg b e 0 J z' a k = 1 := tendsto_nhds_unique hprod tendsto_const_nhds
  exact eq_inv_of_mul_eq_one_left h1

end Limit

end PortChain

open PortChain ZeroEntrance in
/-- **Existence of a solution of the finite Dyson equation with a general port parameter**: for `0 < b`, `0 < 1 - 2b`, every real `e`, every `J` and every `z'` with
`Im z' > 0` there is a solution with negative imaginary parts. -/
theorem portChain_exists {b : ℝ} (hb : 0 < b) (hc : 0 < 1 - 2 * b) (e : ℝ) (J : ℕ) {z' : ℂ}
    (hz : 0 < z'.im) : ∃ m : ℕ → ℂ, IsPortChain b e J z' m := by
  obtain ⟨a, him, heq⟩ := lim_exists (e := e) (J := J) hb hc hz
  have hm0 : toSeq a 0 = 0 := toSeq_zero a
  -- the row equation at position `k`
  have hrow : ∀ k : Fin (J + 1), (toSeq a ((k : ℕ) + 1))⁻¹ = dReg e 0 J z' k -
      ((if (k : ℕ) < J then ((1 - 2 * b : ℝ) : ℂ) * toSeq a (k + 1) + b * toSeq a (k + 2)
        else 0) + b * toSeq a k) := by
    intro k
    rw [← sum_chainS b (toSeq a) hm0 k]
    simp only [toSeq_succ]
    conv_lhs => rw [heq k, inv_inv]
    rfl
  refine ⟨toSeq a, hm0, fun ℓ h1 h2 => ?_, fun ℓ h1 h2 => ?_, ?_⟩
  · have := him ⟨ℓ - 1, by omega⟩
    rw [← toSeq_succ a ⟨ℓ - 1, by omega⟩] at this
    simp only [show ℓ - 1 + 1 = ℓ by omega] at this
    exact this
  · have h := hrow ⟨ℓ - 1, by omega⟩
    simp only [show ℓ - 1 + 1 = ℓ by omega, show ℓ - 1 < J by omega, ↓reduceIte,
      show ℓ - 1 + 2 = ℓ + 1 by omega, dReg] at h
    rw [h]
    simp
    ring
  · have h := hrow ⟨J, by omega⟩
    simp only [lt_irrefl, ↓reduceIte, dReg] at h
    rw [h]
    ring

end BlockBand.Endpoints.Clock
