module

public import BlockBand.Layers.MatchedScalar

/-!
# Stability of the vector Dyson equations of the one- and two-block cores

In the proof of the matched-traces theorem, the vector Dyson equation
`(h_i - Σ_j S_ij m̄_j) m̄_i = 1 + e_i` for the variance matrices `S₃` (one block, two ports) and
`S₄` (two blocks, one port each) is solved by `m̄ = a`, stably, and the branch is selected by the
imaginary parts: the port rows lose a fixed fraction of `Im` to the boundary parameter
`Im z > 0`, and this selects `a`.

All statements are deterministic (no measure). Norms: complex modulus.

## Method

Eliminating the port rows, `ū = (1 + e_port) (z - b m̄)⁻¹`, leaves the physical rows
`m_i (-E - Σ_j S_ij m_j - b n_i ũ_i) = 1 + e_i`, `ũ_i = (z - b m_i)⁻¹`, where `S` is the
physical part of `S₃`/`S₄` and `n_i` the number of ports of block `i`, with row sums
`Σ_j S_ij + b n_i = 1`. With `y_i = -Im m_i ≥ 0`:

* imaginary identity (`coreDyson_im_identity`):
  `|m_i|² (Σ_j S_ij y_j + b² n_i |ũ_i|² y_i) + |m_i|² b n_i |ũ_i|² Im z = y_i + Im(m̄_i e_i)`;
  the port loss `ℓ_i = |m_i|² b n_i |ũ_i|² Im z ≥ ℓ₀ > 0` gives the lower bound
  `y_i ≥ ℓ₀/2` (this is the branch selection: no closeness to `a` is assumed);
* exact difference identity (`coreDyson_diff_identity`), `d = m - a`:
  `d_i = a e_i + m_i a Σ_j S_ij d_j + m_i a² b² n_i ũ_i d_i`;
* weighted contraction with weights `√y_i` (AM–GM in place of Cauchy–Schwarz):
  `Σ_j S_ij |m_i| √y_j + b² n_i |m_i| |ũ_i| √y_i ≤ q √y_i`, `q² = 1 - b(1-b)` (this is
  `‖S²‖_∞ < 1` of the square-norm identity in weighted form: the ports are substituted into the
  physical rows in one step).

## Main results

* `coreDyson_stable`: the abstract `k`-block form, ports eliminated.
* `coreDyson_ports`: the form with the port rows, via `core_port_close`.
* `coreDyson_one`, `coreDyson_two`: the cores `S₃` (`r = 1`) and `S₄` (`r = 2`).

Constants depend only on `b, κ` and the a priori bound `K` on `|m̄|`, uniformly in
`E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open BlockBand.Internal.Contracts.Layers
open scoped ComplexConjugate

/-!
## 1. Scalar facts
-/

/-- `-Im w⁻¹ = |w⁻¹|² Im w`. -/
theorem core_neg_im_inv (w : ℂ) : -(w⁻¹).im = ‖w⁻¹‖ ^ 2 * w.im := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have h0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [Complex.inv_im, norm_inv, Complex.normSq_eq_norm_sq]
  field_simp

/-- `Im (z - b m) ≥ Im z` for `Im m ≤ 0`, `b ≥ 0`. -/
theorem core_im_shift_ge {z m : ℂ} {b : ℝ} (hb : 0 ≤ b) (hm : m.im ≤ 0) :
    z.im ≤ (z - (b : ℂ) * m).im := by
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero]
  nlinarith

/-- `|w⁻¹| ≤ ζ⁻¹` for `Im w ≥ ζ > 0`. -/
theorem core_norm_inv_le_of_im {w : ℂ} {ζ : ℝ} (hζ : 0 < ζ) (hw : ζ ≤ w.im) :
    ‖w⁻¹‖ ≤ ζ⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hζ (hw.trans (Complex.im_le_norm w))

/-- AM–GM: `x ≤ x²/(2λ) + λ/2` for `λ > 0`. -/
theorem core_amgm (x : ℝ) {l : ℝ} (hl : 0 < l) : x ≤ x ^ 2 / (2 * l) + l / 2 := by
  rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (x - l)]

/-- `Σ_j S_j + b² n ≤ 1 - b(1-b)` when `Σ_j S_j = 1 - b n` and `n ≥ 1`. -/
theorem core_rowsum_le {b n s : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hn : 1 ≤ n)
    (hs : s = 1 - b * n) : s + b ^ 2 * n ≤ 1 - b * (1 - b) := by
  subst hs
  nlinarith [mul_nonneg (mul_nonneg hb0 (sub_nonneg.2 hb1)) (sub_nonneg.2 hn)]

/-- **Weighted AM–GM** (in place of Cauchy–Schwarz): for nonnegative weights `w_j, w'` with
`Σ_j w_j + w' ≤ Q²` and `Σ_j w_j x_j² + w' x'² ≤ Y`, `Y, Q > 0`:
`Σ_j w_j x_j + w' x' ≤ Q √Y`. -/
theorem core_amgm_sum {k : ℕ} (w x : Fin k → ℝ) (w' x' : ℝ) (hw : ∀ j, 0 ≤ w j) (hw' : 0 ≤ w')
    {Y Q : ℝ} (hY : 0 < Y) (hQ : 0 < Q)
    (hP : ∑ j, w j * x j ^ 2 + w' * x' ^ 2 ≤ Y) (hQle : ∑ j, w j + w' ≤ Q ^ 2) :
    ∑ j, w j * x j + w' * x' ≤ Q * Real.sqrt Y := by
  obtain ⟨sy, hsy⟩ : ∃ sy, sy = Real.sqrt Y := ⟨_, rfl⟩
  have hs0 : 0 < sy := hsy ▸ Real.sqrt_pos.mpr hY
  have hs2 : sy ^ 2 = Y := by rw [hsy]; exact Real.sq_sqrt hY.le
  rw [← hsy]
  obtain ⟨l, hl⟩ : ∃ l, l = sy / Q := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hl]; positivity
  have h1 : ∑ j, w j * x j ≤ ∑ j, w j * (x j ^ 2 / (2 * l) + l / 2) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (core_amgm (x j) hl0) (hw j)
  have h2 : w' * x' ≤ w' * (x' ^ 2 / (2 * l) + l / 2) :=
    mul_le_mul_of_nonneg_left (core_amgm x' hl0) hw'
  have e1 : ∑ j, w j * (x j ^ 2 / (2 * l) + l / 2) =
      (∑ j, w j * x j ^ 2) / (2 * l) + (∑ j, w j) * (l / 2) := by
    rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : (∑ j, w j * x j ^ 2 + w' * x' ^ 2) / (2 * l) + (∑ j, w j + w') * (l / 2) ≤
      Y / (2 * l) + Q ^ 2 * (l / 2) := by
    gcongr
  have h4 : Y / (2 * l) + Q ^ 2 * (l / 2) = Q * sy := by
    rw [hl, ← hs2]
    field_simp
    ring
  calc ∑ j, w j * x j + w' * x' ≤ ∑ j, w j * (x j ^ 2 / (2 * l) + l / 2) +
        w' * (x' ^ 2 / (2 * l) + l / 2) := add_le_add h1 h2
    _ = (∑ j, w j * x j ^ 2 + w' * x' ^ 2) / (2 * l) + (∑ j, w j + w') * (l / 2) := by
        rw [e1]; ring
    _ ≤ Q * sy := h3.trans h4.le

/-!
## 2. The abstract `k`-block system
-/

section Abstract

variable {k : ℕ} (S : Fin k → Fin k → ℝ) (n : Fin k → ℝ) (b E : ℝ) (a z : ℂ)

/-- The physical row map `X_i(m) = -E - Σ_j S_ij m_j - b n_i (z - b m_i)⁻¹`. -/
def coreRow (m : Fin k → ℂ) (i : Fin k) : ℂ :=
  -(E : ℂ) - ∑ j, (S i j : ℂ) * m j - (b : ℂ) * (n i : ℂ) * (z - (b : ℂ) * m i)⁻¹

/-- The port loss constant `ℓ₀ = b ζ / (4 L² (3 + K)²)`, `L = 2 + K + 2/ζ`. -/
def coreLoss (b ζ K : ℝ) : ℝ :=
  b * ζ / (4 * (2 + K + 2 / ζ) ^ 2 * (3 + K) ^ 2)

/-- The weighted contraction factor `q = √(1 - b(1-b))`. -/
def coreQ (b : ℝ) : ℝ := Real.sqrt (1 - b * (1 - b))

/-- The admissible residual size `ε₀ = min(1/2, ℓ₀/(2K))`. -/
def coreEps (b ζ K : ℝ) : ℝ := min (1 / 2) (coreLoss b ζ K / (2 * K))

/-- The stability constant `C = √K / (√(ℓ₀/2) (1 - q))`. -/
def coreConst (b ζ K : ℝ) : ℝ :=
  Real.sqrt K / (Real.sqrt (coreLoss b ζ K / 2) * (1 - coreQ b))

theorem coreLoss_pos {b ζ K : ℝ} (hb : 0 < b) (hζ : 0 < ζ) (hK : 0 ≤ K) :
    0 < coreLoss b ζ K := by
  unfold coreLoss
  have : 0 < 2 + K + 2 / ζ := by positivity
  positivity

theorem coreQ_lt_one {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) : coreQ b < 1 := by
  unfold coreQ
  rw [Real.sqrt_lt' one_pos]
  nlinarith

theorem coreQ_nonneg (b : ℝ) : 0 ≤ coreQ b := Real.sqrt_nonneg _

theorem coreQ_sq {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : coreQ b ^ 2 = 1 - b * (1 - b) := by
  unfold coreQ
  rw [Real.sq_sqrt]
  nlinarith

theorem coreConst_nonneg {b ζ K : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    0 ≤ coreConst b ζ K := by
  unfold coreConst
  have := coreQ_lt_one hb0 hb1
  have : 0 ≤ 1 - coreQ b := by linarith
  positivity

theorem coreEps_pos {b ζ K : ℝ} (hb : 0 < b) (hζ : 0 < ζ) (hK : 0 < K) :
    0 < coreEps b ζ K := by
  unfold coreEps
  have := coreLoss_pos hb hζ hK.le
  exact lt_min (by norm_num) (by positivity)

variable {S n b E a z}

/-- **Imaginary identity** of a physical row: with `ũ = (z - b m_i)⁻¹`, `y = -Im m`,
`|m_i|² (Σ_j S_ij y_j + b² n_i |ũ|² y_i) + |m_i|² b n_i |ũ|² Im z = y_i + Im(m̄_i e_i)`. -/
theorem coreDyson_im_identity (m e : Fin k → ℂ) (i : Fin k)
    (hrow : m i * coreRow S n b E z m i = 1 + e i) :
    ‖m i‖ ^ 2 * (∑ j, S i j * (-(m j).im) +
        b ^ 2 * n i * ‖(z - (b : ℂ) * m i)⁻¹‖ ^ 2 * (-(m i).im)) +
      ‖m i‖ ^ 2 * (b * n i * ‖(z - (b : ℂ) * m i)⁻¹‖ ^ 2 * z.im) =
      -(m i).im + (conj (m i) * e i).im := by
  set u := (z - (b : ℂ) * m i)⁻¹ with hu
  have h1 : (((‖m i‖ ^ 2 : ℝ)) : ℂ) * coreRow S n b E z m i = conj (m i) * (1 + e i) := by
    rw [← hrow, ← mul_assoc, Complex.ofReal_pow, ← Complex.conj_mul' (m i)]
  have h2 := congrArg Complex.im h1
  rw [Complex.im_ofReal_mul] at h2
  have hU : -(u.im) = ‖u‖ ^ 2 * (z - (b : ℂ) * m i).im := core_neg_im_inv _
  have hshift : (z - (b : ℂ) * m i).im = z.im - b * (m i).im := by
    simp [Complex.sub_im, Complex.mul_im]
  have hrowim : (coreRow S n b E z m i).im =
      ∑ j, S i j * (-(m j).im) + b * n i * (-(u.im)) := by
    unfold coreRow
    simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.im_sum,
      Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, ← hu]
    simp only [mul_zero, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, mul_neg, Finset.sum_neg_distrib]
    ring
  have hrhs : (conj (m i) * (1 + e i)).im = -(m i).im + (conj (m i) * e i).im := by
    rw [mul_add, mul_one, Complex.add_im, Complex.conj_im]
  rw [hrhs, hrowim, hU, hshift] at h2
  rw [← h2]
  ring

/-- **Exact difference identity**: with `d = m - a`, `ũ = (z - b m_i)⁻¹`,
`d_i = a e_i + m_i a Σ_j S_ij d_j + m_i a² b² n_i ũ d_i`, given the matched relations
`a(-E - a) = 1`, `a(z - b a) = 1` and the row sum `Σ_j S_ij + b n_i = 1`. -/
theorem coreDyson_diff_identity (m e : Fin k → ℂ) (i : Fin k)
    (hrow : m i * coreRow S n b E z m i = 1 + e i)
    (ha : a * (-(E : ℂ) - a) = 1) (haz : a * (z - (b : ℂ) * a) = 1)
    (hsum : ∑ j, S i j + b * n i = 1) (hne : z - (b : ℂ) * m i ≠ 0) :
    m i - a = a * e i + m i * a * ∑ j, (S i j : ℂ) * (m j - a) +
      m i * a ^ 2 * (b : ℂ) ^ 2 * (n i : ℂ) * (z - (b : ℂ) * m i)⁻¹ * (m i - a) := by
  set u := (z - (b : ℂ) * m i)⁻¹ with hu
  have hU : u * (z - (b : ℂ) * m i) = 1 := inv_mul_cancel₀ hne
  set T := ∑ j, (S i j : ℂ) * m j with hT
  set s : ℂ := ∑ j, (S i j : ℂ) with hs
  have hsum' : s + (b : ℂ) * (n i : ℂ) = 1 := by
    rw [hs]; exact_mod_cast hsum
  have hSd : ∑ j, (S i j : ℂ) * (m j - a) = T - s * a := by
    rw [hT, hs, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hrow' : m i * (-(E : ℂ) - T - (b : ℂ) * (n i : ℂ) * u) = 1 + e i := hrow
  rw [hSd]
  linear_combination a * hrow' + (-(m i)) * ha + (m i * a ^ 2) * hsum' +
    (-(a * (b : ℂ) * (n i : ℂ) * m i * u)) * haz + (a * (b : ℂ) * (n i : ℂ) * m i * a) * hU

/-- **Stability of the abstract `k`-block vector Dyson equation** (the vector Dyson equation after
elimination of the ports; branch selection by imaginary parts). Hypotheses: `0 < b < 1`,
`S ≥ 0`, `1 ≤ n_i ≤ 2`, row sums `Σ_j S_ij + b n_i = 1`; `|E| ≤ 2`, `|z| ≤ 3`,
`Im z ≥ ζ > 0`, `|a| = 1`, `a(-E-a) = 1`, `a(z - ba) = 1`; an approximate solution `m` with
`Im m_i ≤ 0`, `|m_i| ≤ K` (`K > 0`) and residuals `|e_i| ≤ ε ≤ ε₀(b, ζ, K)`. Conclusion:
`|m_i - a| ≤ C(b, ζ, K) ε`. -/
theorem coreDyson_stable {K ζ ε : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hS : ∀ i j, 0 ≤ S i j) (hn1 : ∀ i, 1 ≤ n i) (hn2 : ∀ i, n i ≤ 2)
    (hsum : ∀ i, ∑ j, S i j + b * n i = 1)
    (hE : |E| ≤ 2) (hz : ‖z‖ ≤ 3) (hζ : 0 < ζ) (hzim : ζ ≤ z.im)
    (hna : ‖a‖ = 1) (ha : a * (-(E : ℂ) - a) = 1) (haz : a * (z - (b : ℂ) * a) = 1)
    (hK : 0 < K) (m e : Fin k → ℂ) (hmim : ∀ i, (m i).im ≤ 0) (hmK : ∀ i, ‖m i‖ ≤ K)
    (heps : ∀ i, ‖e i‖ ≤ ε) (hε : ε ≤ coreEps b ζ K)
    (hrow : ∀ i, m i * coreRow S n b E z m i = 1 + e i) :
    ∀ i, ‖m i - a‖ ≤ coreConst b ζ K * ε := by
  intro i0
  have : Nonempty (Fin k) := ⟨i0⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin k → ℂ, u = fun i => (z - (b : ℂ) * m i)⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin k → ℝ, y = fun i => -(m i).im := ⟨_, rfl⟩
  have hui : ∀ i, u i = (z - (b : ℂ) * m i)⁻¹ := fun i => by rw [hu]
  have hyi' : ∀ i, y i = -(m i).im := fun i => by rw [hy]
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 + K + 2 / ζ := ⟨_, rfl⟩
  obtain ⟨l0, hl0⟩ : ∃ l0 : ℝ, l0 = coreLoss b ζ K := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = coreQ b := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; positivity
  have hl0pos : 0 < l0 := hl0 ▸ coreLoss_pos hb0 hζ hK.le
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (heps i0)
  have hεh : ε ≤ 1 / 2 := hε.trans (min_le_left _ _)
  have hεl : K * ε ≤ l0 / 2 := by
    have := hε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity), ← hl0] at this
    linarith
  have hq0 : 0 < q := hq ▸ Real.sqrt_pos.mpr (by nlinarith)
  have hq1 : q < 1 := hq ▸ coreQ_lt_one hb0 hb1
  have hq2 : q ^ 2 = 1 - b * (1 - b) := hq ▸ coreQ_sq hb0.le hb1.le
  have hy0 : ∀ i, 0 ≤ y i := fun i => by rw [hyi']; linarith [hmim i]
  have hyK : ∀ i, y i ≤ K := fun i => by
    rw [hyi']; exact (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (hmK i))
  -- per-row facts
  have hrowfacts : ∀ i, l0 / 2 ≤ y i ∧
      ‖m i - a‖ ≤ ε + (∑ j, S i j * (‖m i‖ * ‖m j - a‖) +
        b ^ 2 * n i * (‖m i‖ * ‖u i‖ * ‖m i - a‖)) ∧
      ∀ t : ℝ, 0 ≤ t → (∀ j, ‖m j - a‖ ≤ t * Real.sqrt (y j)) →
        ∑ j, S i j * (‖m i‖ * (t * Real.sqrt (y j))) +
          b ^ 2 * n i * (‖m i‖ * ‖u i‖ * (t * Real.sqrt (y i))) ≤ t * (q * Real.sqrt (y i)) := by
    intro i
    have hSi : ∑ j, S i j = 1 - b * n i := by linarith [hsum i]
    have hSi1 : ∑ j, S i j ≤ 1 := by nlinarith [hn1 i]
    have hshift : ζ ≤ (z - (b : ℂ) * m i).im := hzim.trans (core_im_shift_ge hb0.le (hmim i))
    have hne : z - (b : ℂ) * m i ≠ 0 := by
      intro h; rw [h, Complex.zero_im] at hshift; linarith
    have hule : ‖u i‖ ≤ ζ⁻¹ := hui i ▸ core_norm_inv_le_of_im hζ hshift
    have hwle : ‖z - (b : ℂ) * m i‖ ≤ 3 + K := by
      calc ‖z - (b : ℂ) * m i‖ ≤ ‖z‖ + ‖(b : ℂ) * m i‖ := norm_sub_le _ _
        _ ≤ 3 + 1 * K := by
            gcongr
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
            exact mul_le_mul hb1.le (hmK i) (norm_nonneg _) zero_le_one
        _ = 3 + K := by ring
    have huge : (3 + K)⁻¹ ≤ ‖u i‖ := by
      rw [hui i, norm_inv]
      exact inv_anti₀ (norm_pos_iff.mpr hne) hwle
    -- the row is bounded
    have hrowle : ‖coreRow S n b E z m i‖ ≤ L := by
      rw [hL]
      unfold coreRow
      have h1 : ‖∑ j, (S i j : ℂ) * m j‖ ≤ K := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ j, ‖(S i j : ℂ) * m j‖ ≤ ∑ j, S i j * K := Finset.sum_le_sum fun j _ => by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hS i j)]
              exact mul_le_mul_of_nonneg_left (hmK j) (hS i j)
          _ = (∑ j, S i j) * K := by rw [Finset.sum_mul]
          _ ≤ 1 * K := by gcongr
          _ = K := one_mul K
      have h2 : ‖(b : ℂ) * (n i : ℂ) * (z - (b : ℂ) * m i)⁻¹‖ ≤ 2 / ζ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hb0.le, Real.norm_of_nonneg (by linarith [hn1 i])]
        have : b * n i ≤ 2 := by nlinarith [hn2 i, hn1 i]
        calc b * n i * ‖(z - (b : ℂ) * m i)⁻¹‖ ≤ 2 * ζ⁻¹ :=
              mul_le_mul this (hui i ▸ hule) (norm_nonneg _) (by norm_num)
          _ = 2 / ζ := by ring
      have h3 : ‖-(E : ℂ)‖ ≤ 2 := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hE
      calc ‖-(E : ℂ) - ∑ j, (S i j : ℂ) * m j - (b : ℂ) * (n i : ℂ) * (z - (b : ℂ) * m i)⁻¹‖
          ≤ ‖-(E : ℂ)‖ + ‖∑ j, (S i j : ℂ) * m j‖ +
            ‖(b : ℂ) * (n i : ℂ) * (z - (b : ℂ) * m i)⁻¹‖ :=
            (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
        _ ≤ 2 + K + 2 / ζ := by gcongr
    -- `|m_i| ≥ 1/(2L)`
    have hmge : (2 * L)⁻¹ ≤ ‖m i‖ := by
      have h1 : 1 / 2 ≤ ‖m i‖ * L := by
        have h := congrArg norm (hrow i)
        rw [norm_mul] at h
        have h2 : 1 - ε ≤ ‖1 + e i‖ := by
          have := norm_sub_norm_le (1 : ℂ) (-(e i))
          rw [norm_one, norm_neg, sub_neg_eq_add] at this
          linarith [heps i]
        calc 1 / 2 ≤ 1 - ε := by linarith
          _ ≤ ‖m i‖ * ‖coreRow S n b E z m i‖ := h ▸ h2
          _ ≤ ‖m i‖ * L := mul_le_mul_of_nonneg_left hrowle (norm_nonneg _)
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      linarith
    -- the loss
    have hloss : l0 ≤ ‖m i‖ ^ 2 * (b * n i * ‖u i‖ ^ 2 * z.im) := by
      have hm2 : ((2 * L)⁻¹) ^ 2 ≤ ‖m i‖ ^ 2 := pow_le_pow_left₀ (by positivity) hmge 2
      have hu2 : ((3 + K)⁻¹) ^ 2 ≤ ‖u i‖ ^ 2 := pow_le_pow_left₀ (by positivity) huge 2
      have hbn : b ≤ b * n i := by nlinarith [hn1 i]
      calc l0 = ((2 * L)⁻¹) ^ 2 * (b * ((3 + K)⁻¹) ^ 2 * ζ) := by
            rw [hl0, coreLoss, ← hL]; field_simp; ring
        _ ≤ ‖m i‖ ^ 2 * (b * n i * ‖u i‖ ^ 2 * z.im) := by
            gcongr
            all_goals first
              | exact mul_nonneg (mul_nonneg hb0.le (by linarith [hn1 i])) (sq_nonneg _)
              | exact mul_nonneg hb0.le (by linarith [hn1 i])
    have hid := coreDyson_im_identity (S := S) (n := n) (b := b) (E := E) (z := z) m e i (hrow i)
    have himE : |(conj (m i) * e i).im| ≤ K * ε := by
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hmK i) (heps i) (norm_nonneg _) hK.le
    obtain ⟨P, hP⟩ : ∃ P, P = ‖m i‖ ^ 2 * (∑ j, S i j * (-(m j).im) +
        b ^ 2 * n i * ‖(z - (b : ℂ) * m i)⁻¹‖ ^ 2 * (-(m i).im)) := ⟨_, rfl⟩
    have hP0 : 0 ≤ P := by
      rw [hP]
      have : 0 ≤ ∑ j, S i j * (-(m j).im) := Finset.sum_nonneg fun j _ =>
        mul_nonneg (hS i j) (by linarith [hmim j])
      have : 0 ≤ b ^ 2 * n i * ‖(z - (b : ℂ) * m i)⁻¹‖ ^ 2 * (-(m i).im) :=
        mul_nonneg (by have := hn1 i; positivity) (by linarith [hmim i])
      positivity
    have habsle := (abs_le.mp himE)
    rw [← hP, ← hui i] at hid
    have hyi : l0 / 2 ≤ y i := by
      rw [hyi']
      linarith
    have hPle : P ≤ y i := by
      rw [hyi']
      linarith
    refine ⟨hyi, ?_, ?_⟩
    · -- norm form of the difference identity
      have hdi := coreDyson_diff_identity (S := S) (n := n) (b := b) (E := E) (a := a) (z := z)
        m e i (hrow i) ha haz (hsum i) hne
      have hn0 : 0 ≤ n i := by linarith [hn1 i]
      calc ‖m i - a‖ = ‖a * e i + m i * a * ∑ j, (S i j : ℂ) * (m j - a) +
            m i * a ^ 2 * (b : ℂ) ^ 2 * (n i : ℂ) * (z - (b : ℂ) * m i)⁻¹ * (m i - a)‖ :=
            congrArg norm hdi
        _ ≤ ‖a * e i‖ + ‖m i * a * ∑ j, (S i j : ℂ) * (m j - a)‖ +
            ‖m i * a ^ 2 * (b : ℂ) ^ 2 * (n i : ℂ) * (z - (b : ℂ) * m i)⁻¹ * (m i - a)‖ :=
            (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
        _ ≤ ε + ∑ j, S i j * (‖m i‖ * ‖m j - a‖) +
            b ^ 2 * n i * (‖m i‖ * ‖u i‖ * ‖m i - a‖) := by
            gcongr
            · rw [norm_mul, hna, one_mul]; exact heps i
            · rw [norm_mul, norm_mul, hna, mul_one]
              refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans
                (le_of_eq ?_)
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hS i j)]
              ring
            · simp only [norm_mul, norm_pow, hna, Complex.norm_real, Real.norm_of_nonneg hb0.le,
                Real.norm_of_nonneg hn0, one_pow, mul_one, hui i]
              exact le_of_eq (by ring)
        _ = _ := add_assoc _ _ _
    · -- the weighted contraction (AM–GM)
      intro t ht _
      have hyi0 : 0 < y i := lt_of_lt_of_le (by positivity) hyi
      have hsy : 0 < Real.sqrt (y i) := Real.sqrt_pos.mpr hyi0
      have hn0 : 0 ≤ n i := by linarith [hn1 i]
      have hsumq : ∑ j, S i j + b ^ 2 * n i ≤ q ^ 2 := by
        rw [hq2]; exact core_rowsum_le hb0.le hb1.le (hn1 i) hSi
      have hPform : ∑ j, S i j * (‖m i‖ * Real.sqrt (y j)) ^ 2 +
          b ^ 2 * n i * (‖m i‖ * ‖u i‖ * Real.sqrt (y i)) ^ 2 = P := by
        rw [hP, mul_add, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_pow, Real.sq_sqrt (hy0 j), hyi']; ring
        · rw [mul_pow, mul_pow, Real.sq_sqrt (hy0 i), hyi', hui i]; ring
      have hmain := core_amgm_sum (fun j => S i j) (fun j => ‖m i‖ * Real.sqrt (y j))
        (b ^ 2 * n i) (‖m i‖ * ‖u i‖ * Real.sqrt (y i)) (hS i) (by positivity) hyi0 hq0
        (hPform.le.trans hPle) hsumq
      calc ∑ j, S i j * (‖m i‖ * (t * Real.sqrt (y j))) +
            b ^ 2 * n i * (‖m i‖ * ‖u i‖ * (t * Real.sqrt (y i)))
          = t * (∑ j, S i j * (‖m i‖ * Real.sqrt (y j)) +
            b ^ 2 * n i * (‖m i‖ * ‖u i‖ * Real.sqrt (y i))) := by
            rw [mul_add, Finset.mul_sum]
            congr 1
            · exact Finset.sum_congr rfl fun j _ => by ring
            · ring
        _ ≤ t * (q * Real.sqrt (y i)) := mul_le_mul_of_nonneg_left hmain ht
  -- the weighted sup
  have hypos : ∀ i, 0 < Real.sqrt (y i) := fun i =>
    Real.sqrt_pos.mpr (lt_of_lt_of_le (by positivity) (hrowfacts i).1)
  obtain ⟨t, ht⟩ : ∃ t : ℝ,
      t = Finset.univ.sup' Finset.univ_nonempty (fun i => ‖m i - a‖ / Real.sqrt (y i)) :=
    ⟨_, rfl⟩
  have htle : ∀ j, ‖m j - a‖ ≤ t * Real.sqrt (y j) := by
    intro j
    have : ‖m j - a‖ / Real.sqrt (y j) ≤ t := ht ▸
      Finset.le_sup' (fun i => ‖m i - a‖ / Real.sqrt (y i)) (Finset.mem_univ j)
    rwa [div_le_iff₀ (hypos j)] at this
  have ht0 : 0 ≤ t := (div_nonneg (norm_nonneg _) (hypos i0).le).trans (ht ▸
    (Finset.le_sup' (fun i => ‖m i - a‖ / Real.sqrt (y i)) (Finset.mem_univ i0)))
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = Real.sqrt (l0 / 2) := ⟨_, rfl⟩
  have hc0pos : 0 < c0 := hc0 ▸ Real.sqrt_pos.mpr (by positivity)
  have hstep : ∀ i, ‖m i - a‖ / Real.sqrt (y i) ≤ ε / c0 + q * t := by
    intro i
    obtain ⟨hyi, hdi, hwi⟩ := hrowfacts i
    have hbound : ‖m i - a‖ ≤ ε + t * (q * Real.sqrt (y i)) := by
      refine hdi.trans ?_
      have hS' : ∑ j, S i j * (‖m i‖ * ‖m j - a‖) +
          b ^ 2 * n i * (‖m i‖ * ‖u i‖ * ‖m i - a‖) ≤
          ∑ j, S i j * (‖m i‖ * (t * Real.sqrt (y j))) +
          b ^ 2 * n i * (‖m i‖ * ‖u i‖ * (t * Real.sqrt (y i))) := by
        have hn0 : 0 ≤ n i := by linarith [hn1 i]
        gcongr with j
        · exact hS i j
        · exact htle j
        · exact htle i
      linarith [hwi t ht0 htle]
    have hc0le : c0 ≤ Real.sqrt (y i) := hc0 ▸ Real.sqrt_le_sqrt hyi
    rw [div_le_iff₀ (hypos i)]
    calc ‖m i - a‖ ≤ ε + t * (q * Real.sqrt (y i)) := hbound
      _ = ε / Real.sqrt (y i) * Real.sqrt (y i) + q * t * Real.sqrt (y i) := by
          field_simp [(hypos i).ne']
      _ ≤ ε / c0 * Real.sqrt (y i) + q * t * Real.sqrt (y i) := by
          gcongr
      _ = (ε / c0 + q * t) * Real.sqrt (y i) := by ring
  have htle2 : t ≤ ε / c0 + q * t := ht ▸ Finset.sup'_le _ _ fun i _ => ht ▸ hstep i
  have htfin : t ≤ ε / (c0 * (1 - q)) := by
    rw [le_div_iff₀ (mul_pos hc0pos (by linarith))]
    have : t * (1 - q) ≤ ε / c0 := by linarith
    calc t * (c0 * (1 - q)) = (t * (1 - q)) * c0 := by ring
      _ ≤ ε / c0 * c0 := mul_le_mul_of_nonneg_right this hc0pos.le
      _ = ε := by field_simp
  calc ‖m i0 - a‖ ≤ t * Real.sqrt (y i0) := htle i0
    _ ≤ ε / (c0 * (1 - q)) * Real.sqrt K := by
        gcongr
        exact hyK i0
    _ = coreConst b ζ K * ε := by
        rw [coreConst, ← hl0, ← hc0, ← hq]
        ring

/-- **A port row is slaved to its physical row**: `(z - b m) u = 1 + f`, `Im m ≤ 0`,
`Im z ≥ ζ > 0`, `a (z - b a) = 1`, `|a| = 1` give `|u - a| ≤ (b |m - a| + |f|)/ζ`. -/
theorem core_port_close {m u f : ℂ} {ζ : ℝ} (hb0 : 0 ≤ b) (hζ : 0 < ζ) (hzim : ζ ≤ z.im)
    (hna : ‖a‖ = 1) (haz : a * (z - (b : ℂ) * a) = 1) (hmim : m.im ≤ 0)
    (hq : (z - (b : ℂ) * m) * u = 1 + f) :
    ‖u - a‖ ≤ (b * ‖m - a‖ + ‖f‖) / ζ := by
  have hshift : ζ ≤ (z - (b : ℂ) * m).im := hzim.trans (core_im_shift_ge hb0 hmim)
  have hne : z - (b : ℂ) * m ≠ 0 := by
    intro h; rw [h, Complex.zero_im] at hshift; linarith
  set v := (z - (b : ℂ) * m)⁻¹ with hv
  have hvle : ‖v‖ ≤ ζ⁻¹ := core_norm_inv_le_of_im hζ hshift
  have hV : v * (z - (b : ℂ) * m) = 1 := inv_mul_cancel₀ hne
  have heq : u - a = v * a * (b : ℂ) * (m - a) + v * f := by
    linear_combination v * hq - u * hV - v * haz + a * hV
  rw [heq]
  calc ‖v * a * (b : ℂ) * (m - a) + v * f‖ ≤ ‖v * a * (b : ℂ) * (m - a)‖ + ‖v * f‖ :=
        norm_add_le _ _
    _ ≤ ζ⁻¹ * (b * ‖m - a‖) + ζ⁻¹ * ‖f‖ := by
        rw [norm_mul, norm_mul, norm_mul, hna, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hb0, norm_mul, mul_assoc]
        gcongr
    _ = (b * ‖m - a‖ + ‖f‖) / ζ := by field_simp

/-- **Stability with the port rows** (the vector Dyson equation before elimination): physical rows
`m_i (-E - Σ_j S_ij m_j - b n_i U_i) = 1 + e_i` and port rows `(z - b m_i) U_i = 1 + f_i`
(`U_i` the mean of the ports of block `i`), residuals `≤ ε` with `(1 + 2K/ζ) ε ≤ ε₀`:
`|m_i - a| ≤ C (1 + 2K/ζ) ε`. -/
theorem coreDyson_ports {K ζ ε : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hS : ∀ i j, 0 ≤ S i j) (hn1 : ∀ i, 1 ≤ n i) (hn2 : ∀ i, n i ≤ 2)
    (hsum : ∀ i, ∑ j, S i j + b * n i = 1)
    (hE : |E| ≤ 2) (hz : ‖z‖ ≤ 3) (hζ : 0 < ζ) (hzim : ζ ≤ z.im)
    (hna : ‖a‖ = 1) (ha : a * (-(E : ℂ) - a) = 1) (haz : a * (z - (b : ℂ) * a) = 1)
    (hK : 0 < K) (m e U f : Fin k → ℂ) (hmim : ∀ i, (m i).im ≤ 0) (hmK : ∀ i, ‖m i‖ ≤ K)
    (heps : ∀ i, ‖e i‖ ≤ ε) (hfeps : ∀ i, ‖f i‖ ≤ ε)
    (hε : (1 + 2 * K / ζ) * ε ≤ coreEps b ζ K)
    (hphys : ∀ i, m i * (-(E : ℂ) - ∑ j, (S i j : ℂ) * m j - (b : ℂ) * (n i : ℂ) * U i) = 1 + e i)
    (hport : ∀ i, (z - (b : ℂ) * m i) * U i = 1 + f i) :
    ∀ i, ‖m i - a‖ ≤ coreConst b ζ K * ((1 + 2 * K / ζ) * ε) := by
  set e' : Fin k → ℂ := fun i =>
    e i + m i * (b : ℂ) * (n i : ℂ) * (z - (b : ℂ) * m i)⁻¹ * f i with he'
  have hne : ∀ i, z - (b : ℂ) * m i ≠ 0 := fun i => by
    have hshift : ζ ≤ (z - (b : ℂ) * m i).im := hzim.trans (core_im_shift_ge hb0.le (hmim i))
    intro h; rw [h, Complex.zero_im] at hshift; linarith
  have hrow : ∀ i, m i * coreRow S n b E z m i = 1 + e' i := by
    intro i
    have hV : (z - (b : ℂ) * m i)⁻¹ * (z - (b : ℂ) * m i) = 1 := inv_mul_cancel₀ (hne i)
    have hU : U i = (z - (b : ℂ) * m i)⁻¹ * (1 + f i) := by
      rw [← hport i, ← mul_assoc, hV, one_mul]
    simp only [coreRow, he']
    have h := hphys i
    rw [hU] at h
    linear_combination h
  have he'le : ∀ i, ‖e' i‖ ≤ (1 + 2 * K / ζ) * ε := by
    intro i
    have hshift : ζ ≤ (z - (b : ℂ) * m i).im := hzim.trans (core_im_shift_ge hb0.le (hmim i))
    have hvle := core_norm_inv_le_of_im hζ hshift
    have hn0 : 0 ≤ n i := by linarith [hn1 i]
    have hbn : b * n i ≤ 2 := by nlinarith [hn2 i, hn1 i]
    simp only [he']
    calc ‖e i + m i * (b : ℂ) * (n i : ℂ) * (z - (b : ℂ) * m i)⁻¹ * f i‖
        ≤ ‖e i‖ + ‖m i‖ * (b * n i) * ‖(z - (b : ℂ) * m i)⁻¹‖ * ‖f i‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg hb0.le, Real.norm_of_nonneg hn0]
          ring
      _ ≤ ε + K * 2 * ζ⁻¹ * ε := by
          gcongr
          · exact heps i
          · exact hmK i
          · exact hfeps i
      _ = (1 + 2 * K / ζ) * ε := by ring
  exact coreDyson_stable hb0 hb1 hS hn1 hn2 hsum hE hz hζ hzim hna ha haz hK m e' hmim hmK he'le hε
    hrow

end Abstract

/-!
## 3. The matched point on the bulk interval
-/

/-- The uniform lower bound `ζ_κ = (1-b)√(4-(2-κ)²)/2` on `Im z_∂` over `bulkInterval κ`. -/
def coreZeta (b κ : ℝ) : ℝ := (1 - b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2

/-- The matched facts used by the stability lemmas, for `E ∈ bulkInterval κ`. -/
theorem core_matched_facts {b κ E : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) :
    |E| ≤ 2 ∧ ‖boundaryZ b E‖ ≤ 3 ∧ 0 < coreZeta b κ ∧ coreZeta b κ ≤ (boundaryZ b E).im ∧
      ‖matchedA E‖ = 1 ∧ matchedA E * (-(E : ℂ) - matchedA E) = 1 ∧
      matchedA E * (boundaryZ b E - (b : ℂ) * matchedA E) = 1 := by
  have hE2 : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  obtain ⟨hz0, hz1⟩ := boundaryZ_im_pos_of_mem_bulkInterval hb1 hκ hE
  have hna := norm_matchedA hE2.le
  have ha0 : matchedA E ≠ 0 := by
    intro h; rw [h, norm_zero] at hna; exact zero_ne_one hna
  refine ⟨hE2.le, norm_boundaryZ_le hb0 hb1.le hE2.le, hz0, hz1, hna, ?_, ?_⟩
  · have := matchedA_quadratic hE2.le
    linear_combination -this
  · unfold boundaryZ
    rw [add_sub_cancel_right, mul_inv_cancel₀ ha0]

/-!
## 4. The one- and two-block cores
-/

/-- **`S₃` (one block, two ports; `r = 1`)**: constants `ε₁ > 0`, `C ≥ 0` depending only on
`b, κ, K`; for every `E ∈ bulkInterval κ` and approximate solution
`(-E - (c m + b u₀ + b u₁)) m = 1 + e`, `(z_∂ - b m) u_j = 1 + e_j` with `Im m ≤ 0`, `|m| ≤ K`
and residuals `≤ ε ≤ ε₁`: `|m - a|, |u₀ - a|, |u₁ - a| ≤ C ε`. -/
theorem coreDyson_one {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {K : ℝ}
    (hK : 0 < K) :
    ∃ ε₁ C : ℝ, 0 < ε₁ ∧ 0 ≤ C ∧ ∀ E ∈ bulkInterval κ, ∀ (m u0 u1 e e0 e1 : ℂ) (ε : ℝ),
      m.im ≤ 0 → ‖m‖ ≤ K → ‖e‖ ≤ ε → ‖e0‖ ≤ ε → ‖e1‖ ≤ ε → ε ≤ ε₁ →
      (-(E : ℂ) - (((1 - 2 * b : ℝ) : ℂ) * m + (b : ℂ) * u0 + (b : ℂ) * u1)) * m = 1 + e →
      (boundaryZ b E - (b : ℂ) * m) * u0 = 1 + e0 →
      (boundaryZ b E - (b : ℂ) * m) * u1 = 1 + e1 →
      ‖m - matchedA E‖ ≤ C * ε ∧ ‖u0 - matchedA E‖ ≤ C * ε ∧ ‖u1 - matchedA E‖ ≤ C * ε := by
  by_cases hex : ∃ E₀, E₀ ∈ bulkInterval κ
  swap
  · exact ⟨1, 0, one_pos, le_rfl, fun E hE => absurd ⟨E, hE⟩ hex⟩
  obtain ⟨E₀, hE₀⟩ := hex
  have hb1' : b < 1 := by linarith
  have hζ : 0 < coreZeta b κ := (core_matched_facts hb0.le hb1' hκ hE₀).2.2.1
  set ζ := coreZeta b κ with hζdef
  set R := 1 + 2 * K / ζ with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ 2 * K / ζ := by positivity
    rw [hR]; linarith
  set C₀ := coreConst b ζ K * R with hC₀def
  have hC₀ : 0 ≤ C₀ := mul_nonneg (coreConst_nonneg hb0 hb1') (by linarith)
  refine ⟨coreEps b ζ K / R, (C₀ + 1) * (1 + ζ⁻¹),
    div_pos (coreEps_pos hb0 hζ hK) (by linarith), by positivity, ?_⟩
  intro E hE m u0 u1 e e0 e1 ε hm hmK he he0 he1 hε hP hQ0 hQ1
  obtain ⟨hE2, hz3, -, hzim, hna, ha, haz⟩ := core_matched_facts hb0.le hb1' hκ hE
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans he
  have hRε : R * ε ≤ coreEps b ζ K := by
    rw [le_div_iff₀ (by linarith)] at hε; linarith
  have hmain := coreDyson_ports (k := 1) (S := fun _ _ => 1 - 2 * b) (n := fun _ => 2)
    (b := b) (E := E) (a := matchedA E) (z := boundaryZ b E) (ε := ε) hb0 hb1'
    (fun _ _ => by linarith) (fun _ => by norm_num) (fun _ => le_rfl)
    (fun _ => by simp; ring) hE2 hz3 hζ hzim hna ha haz hK (fun _ => m) (fun _ => e)
    (fun _ => (u0 + u1) / 2) (fun _ => (e0 + e1) / 2) (fun _ => hm) (fun _ => hmK)
    (fun _ => he) (fun _ => by
      calc ‖(e0 + e1) / 2‖ ≤ (‖e0‖ + ‖e1‖) / 2 := by
            rw [norm_div, Complex.norm_ofNat]; gcongr; exact norm_add_le _ _
        _ ≤ ε := by linarith) hRε
    (fun _ => by
      have h := hP
      simp only [Fin.sum_univ_one]
      push_cast at h ⊢
      linear_combination h)
    (fun _ => by linear_combination (hQ0 + hQ1) / 2) 0
  have hm' : ‖m - matchedA E‖ ≤ C₀ * ε := by rw [hC₀def, mul_assoc]; exact hmain
  have hport : ∀ (u f : ℂ), ‖f‖ ≤ ε → (boundaryZ b E - (b : ℂ) * m) * u = 1 + f →
      ‖u - matchedA E‖ ≤ (C₀ + 1) * (1 + ζ⁻¹) * ε := by
    intro u f hf hq
    have h := core_port_close hb0.le hζ hzim hna haz hm hq
    calc ‖u - matchedA E‖ ≤ (b * ‖m - matchedA E‖ + ‖f‖) / ζ := h
      _ ≤ (1 * (C₀ * ε) + ε) / ζ := by gcongr
      _ = (C₀ + 1) * ζ⁻¹ * ε := by field_simp
      _ ≤ (C₀ + 1) * (1 + ζ⁻¹) * ε := by gcongr; exact le_add_of_nonneg_left zero_le_one
  refine ⟨hm'.trans ?_, hport u0 e0 he0 hQ0, hport u1 e1 he1 hQ1⟩
  have : C₀ ≤ (C₀ + 1) * (1 + ζ⁻¹) := by
    have : 0 ≤ ζ⁻¹ := by positivity
    nlinarith
  exact mul_le_mul_of_nonneg_right this hε0

/-- **`S₄` (two blocks, one port each; `r = 2`)**: constants `ε₁ > 0`, `C ≥ 0` depending only
on `b, κ, K`; for every `E ∈ bulkInterval κ` and approximate solution
`(-E - (c m_i + b m_{1-i} + b u_i)) m_i = 1 + e_i`, `(z_∂ - b m_i) u_i = 1 + f_i` with
`Im m_i ≤ 0`, `|m_i| ≤ K` and residuals `≤ ε ≤ ε₁`: `|m_i - a|, |u_i - a| ≤ C ε`. -/
theorem coreDyson_two {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {K : ℝ}
    (hK : 0 < K) :
    ∃ ε₁ C : ℝ, 0 < ε₁ ∧ 0 ≤ C ∧ ∀ E ∈ bulkInterval κ,
      ∀ (m0 m1 u0 u1 e0 e1 f0 f1 : ℂ) (ε : ℝ),
      m0.im ≤ 0 → m1.im ≤ 0 → ‖m0‖ ≤ K → ‖m1‖ ≤ K → ‖e0‖ ≤ ε → ‖e1‖ ≤ ε → ‖f0‖ ≤ ε →
      ‖f1‖ ≤ ε → ε ≤ ε₁ →
      (-(E : ℂ) - (((1 - 2 * b : ℝ) : ℂ) * m0 + (b : ℂ) * m1 + (b : ℂ) * u0)) * m0 = 1 + e0 →
      (-(E : ℂ) - (((1 - 2 * b : ℝ) : ℂ) * m1 + (b : ℂ) * m0 + (b : ℂ) * u1)) * m1 = 1 + e1 →
      (boundaryZ b E - (b : ℂ) * m0) * u0 = 1 + f0 →
      (boundaryZ b E - (b : ℂ) * m1) * u1 = 1 + f1 →
      ‖m0 - matchedA E‖ ≤ C * ε ∧ ‖m1 - matchedA E‖ ≤ C * ε ∧
        ‖u0 - matchedA E‖ ≤ C * ε ∧ ‖u1 - matchedA E‖ ≤ C * ε := by
  by_cases hex : ∃ E₀, E₀ ∈ bulkInterval κ
  swap
  · exact ⟨1, 0, one_pos, le_rfl, fun E hE => absurd ⟨E, hE⟩ hex⟩
  obtain ⟨E₀, hE₀⟩ := hex
  have hb1' : b < 1 := by linarith
  have hζ : 0 < coreZeta b κ := (core_matched_facts hb0.le hb1' hκ hE₀).2.2.1
  set ζ := coreZeta b κ with hζdef
  set R := 1 + 2 * K / ζ with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ 2 * K / ζ := by positivity
    rw [hR]; linarith
  set C₀ := coreConst b ζ K * R with hC₀def
  have hC₀ : 0 ≤ C₀ := mul_nonneg (coreConst_nonneg hb0 hb1') (by linarith)
  refine ⟨coreEps b ζ K / R, (C₀ + 1) * (1 + ζ⁻¹),
    div_pos (coreEps_pos hb0 hζ hK) (by linarith), by positivity, ?_⟩
  intro E hE m0 m1 u0 u1 e0 e1 f0 f1 ε hm0 hm1 hmK0 hmK1 he0 he1 hf0 hf1 hε hP0 hP1 hQ0 hQ1
  obtain ⟨hE2, hz3, -, hzim, hna, ha, haz⟩ := core_matched_facts hb0.le hb1' hκ hE
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans he0
  have hRε : R * ε ≤ coreEps b ζ K := by
    rw [le_div_iff₀ (by linarith)] at hε; linarith
  have hmain := coreDyson_ports (k := 2) (S := fun i j => if i = j then 1 - 2 * b else b)
    (n := fun _ => 1) (b := b) (E := E) (a := matchedA E) (z := boundaryZ b E) (ε := ε)
    hb0 hb1' (fun i j => by split_ifs <;> linarith) (fun _ => le_rfl)
    (fun _ => by norm_num)
    (fun i => by fin_cases i <;> simp [Fin.sum_univ_two] <;> ring) hE2 hz3 hζ hzim hna ha haz hK
    ![m0, m1] ![e0, e1] ![u0, u1] ![f0, f1]
    (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> assumption)
    (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> assumption) hRε
    (fun i => by
      have h0 := hP0
      have h1 := hP1
      push_cast at h0 h1
      fin_cases i <;> simp [Fin.sum_univ_two]
      · linear_combination h0
      · linear_combination h1)
    (fun i => by fin_cases i <;> simpa)
  have hm' : ∀ i, ‖![m0, m1] i - matchedA E‖ ≤ C₀ * ε := fun i => by
    rw [hC₀def, mul_assoc]; exact hmain i
  have hC : C₀ ≤ (C₀ + 1) * (1 + ζ⁻¹) := by
    have : 0 ≤ ζ⁻¹ := by positivity
    nlinarith
  have hport : ∀ (m u f : ℂ), m.im ≤ 0 → ‖m - matchedA E‖ ≤ C₀ * ε → ‖f‖ ≤ ε →
      (boundaryZ b E - (b : ℂ) * m) * u = 1 + f →
      ‖u - matchedA E‖ ≤ (C₀ + 1) * (1 + ζ⁻¹) * ε := by
    intro m u f hm hmd hf hq
    have h := core_port_close hb0.le hζ hzim hna haz hm hq
    calc ‖u - matchedA E‖ ≤ (b * ‖m - matchedA E‖ + ‖f‖) / ζ := h
      _ ≤ (1 * (C₀ * ε) + ε) / ζ := by gcongr
      _ = (C₀ + 1) * ζ⁻¹ * ε := by field_simp
      _ ≤ (C₀ + 1) * (1 + ζ⁻¹) * ε := by gcongr; exact le_add_of_nonneg_left zero_le_one
  have h0 : ‖m0 - matchedA E‖ ≤ C₀ * ε := hm' 0
  have h1 : ‖m1 - matchedA E‖ ≤ C₀ * ε := hm' 1
  exact ⟨h0.trans (mul_le_mul_of_nonneg_right hC hε0), h1.trans (mul_le_mul_of_nonneg_right hC hε0),
    hport m0 u0 f0 hm0 h0 hf0 hQ0, hport m1 u1 f1 hm1 h1 hf1 hQ1⟩

end BlockBand.Layers
