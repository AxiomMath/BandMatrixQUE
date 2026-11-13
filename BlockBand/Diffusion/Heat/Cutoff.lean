module

public import BlockBand.Diffusion.Heat.Process

/-!
# Smooth compactly supported truncations of `e^{-l(x+y)}`

`σ = Real.smoothTransition`. For `n ≥ 1`, `l > 0`:
`chF n l (x, y) = σ(x+2)σ(2 - x/n)e^{-lx} · σ(y+2)σ(4-y)e^{-ly}` is `C^∞` with compact support
(`[-2, 2n] × [-2, 4]`), equals `e^{-l(x+y)}` on the strip where `x < n`, and there its base
generator is `chGen D0 l` (`ch_gen_chF_of_lt`). On the whole strip `|chF n l| ≤ 1` and
`|𝒟₀ chF n l| ≤ chCb D0 l B` uniformly in `n ≥ 1` (`ch_abs_gen_chF_le`), where `B ≥ 1` bounds
`σ, σ', σ''`. The generator of a product `G(x)K(y)` is computed in `ch_exBaseGenerator_prod`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped ENNReal NNReal

/-!
### `σ = smoothTransition`
-/

theorem ch_st_contDiff : ContDiff ℝ (⊤ : ℕ∞) smoothTransition := smoothTransition.contDiff

theorem ch_st_hasDerivAt (u : ℝ) : HasDerivAt smoothTransition (deriv smoothTransition u) u :=
  ((ch_st_contDiff.differentiable (by simp)) u).hasDerivAt

theorem ch_st_differentiable_deriv : Differentiable ℝ (deriv smoothTransition) := by
  have h := (ch_st_contDiff.of_le (by simp) : ContDiff ℝ 2 smoothTransition).iterate_deriv' 1 1
  simpa using h.differentiable (by simp)

theorem ch_st_hasDerivAt' (u : ℝ) :
    HasDerivAt (deriv smoothTransition) (deriv (deriv smoothTransition) u) u :=
  (ch_st_differentiable_deriv u).hasDerivAt

theorem ch_st_eventuallyEq_const {u : ℝ} (hu : u ∉ Icc (0 : ℝ) 1) :
    ∃ c : ℝ, smoothTransition =ᶠ[𝓝 u] fun _ => c := by
  rcases lt_or_ge u 0 with h0 | h0
  · refine ⟨0, ?_⟩
    filter_upwards [Iio_mem_nhds h0] with v hv
    exact smoothTransition.zero_of_nonpos (le_of_lt hv)
  · have h1 : 1 < u := by
      by_contra h
      exact hu ⟨h0, not_lt.1 h⟩
    refine ⟨1, ?_⟩
    filter_upwards [Ioi_mem_nhds h1] with v hv
    exact smoothTransition.one_of_one_le (le_of_lt hv)

theorem ch_st_deriv_eq_zero {u : ℝ} (hu : u ∉ Icc (0 : ℝ) 1) : deriv smoothTransition u = 0 := by
  obtain ⟨c, hc⟩ := ch_st_eventuallyEq_const hu
  rw [hc.deriv_eq]
  simp

theorem ch_st_deriv2_eq_zero {u : ℝ} (hu : u ∉ Icc (0 : ℝ) 1) :
    deriv (deriv smoothTransition) u = 0 := by
  obtain ⟨c, hc⟩ := ch_st_eventuallyEq_const hu
  have h2 : deriv smoothTransition =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
    hc.deriv.trans (Eventually.of_forall fun v => by simp)
  rw [h2.deriv_eq]
  simp

theorem ch_st_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ u, |smoothTransition u| ≤ B ∧
    |deriv smoothTransition u| ≤ B ∧ |deriv (deriv smoothTransition) u| ≤ B := by
  have hc1 : Continuous (deriv smoothTransition) := ch_st_differentiable_deriv.continuous
  have hc2 : Continuous (deriv (deriv smoothTransition)) := by
    have h := (ch_st_contDiff.of_le (by simp) : ContDiff ℝ 2 smoothTransition).iterate_deriv' 0 2
    simpa using h.continuous
  obtain ⟨C1, hC1⟩ := hc1.bounded_above_of_compact_support
    (HasCompactSupport.intro isCompact_Icc fun u hu => ch_st_deriv_eq_zero hu)
  obtain ⟨C2, hC2⟩ := hc2.bounded_above_of_compact_support
    (HasCompactSupport.intro isCompact_Icc fun u hu => ch_st_deriv2_eq_zero hu)
  refine ⟨max 1 (max C1 C2), le_max_left _ _, fun u => ⟨?_, ?_, ?_⟩⟩
  · rw [abs_of_nonneg (smoothTransition.nonneg u)]
    exact (smoothTransition.le_one u).trans (le_max_left _ _)
  · exact (hC1 u).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hC2 u).trans ((le_max_right _ _).trans (le_max_right _ _))

/-!
### The generator of a product `G(x) K(y)`
-/

theorem ch_fderiv_prod {G K : ℝ → ℝ} (hG : Differentiable ℝ G) (hK : Differentiable ℝ K)
    (v a : ℝ × ℝ) :
    fderiv ℝ (fun w : ℝ × ℝ => G w.1 * K w.2) v a =
      deriv G v.1 * K v.2 * a.1 + G v.1 * deriv K v.2 * a.2 := by
  have h1 : HasFDerivAt (fun w : ℝ × ℝ => G w.1) (deriv G v.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) v :=
    (hG v.1).hasDerivAt.comp_hasFDerivAt v hasFDerivAt_fst
  have h2 : HasFDerivAt (fun w : ℝ × ℝ => K w.2) (deriv K v.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) v :=
    (hK v.2).hasDerivAt.comp_hasFDerivAt v hasFDerivAt_snd
  have h3 : HasFDerivAt (fun w : ℝ × ℝ => G w.1 * K w.2) _ v := h1.mul h2
  rw [h3.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- **The base generator of a product** `G(x)K(y)` for `G, K ∈ C²(ℝ)`. -/
theorem ch_exBaseGenerator_prod {G K : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (hK : ContDiff ℝ 2 K)
    (D0 : ℝ) (w : ℝ × ℝ) :
    exBaseGenerator D0 (fun v => G v.1 * K v.2) w =
      D0 / 2 * ((w.1 * (1 + w.1) * deriv (deriv G) w.1 + (1 + 2 * w.1) * deriv G w.1) * K w.2 +
        G w.1 * (w.2 * (1 - w.2) * deriv (deriv K) w.2 + (1 - 2 * w.2) * deriv K w.2)) := by
  have hG1 : Differentiable ℝ G := hG.differentiable (by simp)
  have hK1 : Differentiable ℝ K := hK.differentiable (by simp)
  have hG2 : Differentiable ℝ (deriv G) := by
    simpa using (hG.iterate_deriv' 1 1).differentiable (by simp)
  have hK2 : Differentiable ℝ (deriv K) := by
    simpa using (hK.iterate_deriv' 1 1).differentiable (by simp)
  have e1 : (fun v => fderiv ℝ (fun w : ℝ × ℝ => G w.1 * K w.2) v (1, 0)) =
      fun v => deriv G v.1 * K v.2 := funext fun v => by rw [ch_fderiv_prod hG1 hK1]; simp
  have e2 : (fun v => fderiv ℝ (fun w : ℝ × ℝ => G w.1 * K w.2) v (0, 1)) =
      fun v => G v.1 * deriv K v.2 := funext fun v => by rw [ch_fderiv_prod hG1 hK1]; simp
  simp only [exBaseGenerator]
  rw [e1, e2, ch_fderiv_prod hG2 hK1, ch_fderiv_prod hG1 hK2, ch_fderiv_prod hG1 hK1,
    ch_fderiv_prod hG1 hK1]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  ring

/-!
### The truncated exponentials
-/

/-- The `x`-cutoff `σ(x+2)σ(2 - x/n)` (`= 1` on `[-1, n]`, `= 0` off `[-2, 2n]`). -/
def chCutX (n x : ℝ) : ℝ := smoothTransition (x + 2) * smoothTransition (2 - x / n)

/-- The `y`-cutoff `σ(y+2)σ(4-y)` (`= 1` on `[-1, 3]`, `= 0` off `[-2, 4]`). -/
def chCutY (y : ℝ) : ℝ := smoothTransition (y + 2) * smoothTransition (4 - y)

/-- `x`-factor `chCutX n x e^{-lx}`. -/
def chG (n l x : ℝ) : ℝ := chCutX n x * Real.exp (-(l * x))

/-- `y`-factor `chCutY y e^{-ly}`. -/
def chK (l y : ℝ) : ℝ := chCutY y * Real.exp (-(l * y))

/-- The truncated test `chG n l x · chK l y`. -/
def chF (n l : ℝ) (w : ℝ × ℝ) : ℝ := chG n l w.1 * chK l w.2

/-- The `x`-factor near `x ≥ -1`: `σ(2 - x/n)e^{-lx}`. -/
def chGt (n l x : ℝ) : ℝ := smoothTransition (2 - x / n) * Real.exp (-(l * x))

/-- Its first derivative. -/
def chGt1 (n l x : ℝ) : ℝ :=
  -(n⁻¹ * deriv smoothTransition (2 - x / n)) * Real.exp (-(l * x)) +
    smoothTransition (2 - x / n) * (-l * Real.exp (-(l * x)))

/-- Its second derivative. -/
def chGt2 (n l x : ℝ) : ℝ :=
  n⁻¹ ^ 2 * deriv (deriv smoothTransition) (2 - x / n) * Real.exp (-(l * x)) +
    2 * l * n⁻¹ * deriv smoothTransition (2 - x / n) * Real.exp (-(l * x)) +
    l ^ 2 * smoothTransition (2 - x / n) * Real.exp (-(l * x))

theorem ch_hasDerivAt_lin (n x : ℝ) : HasDerivAt (fun x => 2 - x / n) (-n⁻¹) x := by
  have := ((hasDerivAt_id x).div_const n).const_sub 2
  simpa [div_eq_mul_inv] using this

theorem ch_hasDerivAt_exp (l x : ℝ) :
    HasDerivAt (fun x => Real.exp (-(l * x))) (-l * Real.exp (-(l * x))) x := by
  have h : HasDerivAt (fun x => -(l * x)) (-l) x :=
    (hasDerivAt_mul_const (-l)).congr_of_eventuallyEq (Eventually.of_forall fun y => by ring)
  refine h.exp.congr_deriv ?_
  ring

theorem ch_hasDerivAt_gt (n l x : ℝ) : HasDerivAt (chGt n l) (chGt1 n l x) x := by
  have h1 := (ch_st_hasDerivAt (2 - x / n)).comp x (ch_hasDerivAt_lin n x)
  have h := h1.mul (ch_hasDerivAt_exp l x)
  unfold chGt chGt1
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  ring

theorem ch_hasDerivAt_gt1 (n l x : ℝ) : HasDerivAt (chGt1 n l) (chGt2 n l x) x := by
  have hs := (ch_st_hasDerivAt (2 - x / n)).comp x (ch_hasDerivAt_lin n x)
  have hs' := (ch_st_hasDerivAt' (2 - x / n)).comp x (ch_hasDerivAt_lin n x)
  have he := ch_hasDerivAt_exp l x
  have h := ((hs'.const_mul n⁻¹).neg.mul he).add (hs.mul (he.const_mul (-l)))
  have hf : chGt1 n l = fun x => -(n⁻¹ * deriv smoothTransition (2 - x / n)) *
      Real.exp (-(l * x)) + smoothTransition (2 - x / n) * (-l * Real.exp (-(l * x))) := rfl
  rw [hf]
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, Pi.neg_apply, chGt2]
  ring

theorem ch_contDiff_chG (n l : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (chG n l) := by
  unfold chG chCutX
  exact ((ch_st_contDiff.comp (contDiff_id.add contDiff_const)).mul
    (ch_st_contDiff.comp (contDiff_const.sub (contDiff_id.div_const n)))).mul
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg)

theorem ch_contDiff_chK (l : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (chK l) := by
  unfold chK chCutY
  exact ((ch_st_contDiff.comp (contDiff_id.add contDiff_const)).mul
    (ch_st_contDiff.comp (contDiff_const.sub contDiff_id))).mul
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg)

theorem ch_contDiff_chF (n l : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (chF n l) :=
  ((ch_contDiff_chG n l).comp contDiff_fst).mul ((ch_contDiff_chK l).comp contDiff_snd)

theorem ch_hasCompactSupport_chF {n : ℝ} (hn : 0 < n) (l : ℝ) : HasCompactSupport (chF n l) := by
  refine HasCompactSupport.intro (K := Icc (-2) (2 * n) ×ˢ Icc (-2) 4)
    (isCompact_Icc.prod isCompact_Icc) fun w hw => ?_
  simp only [mem_prod, mem_Icc, not_and_or, not_le] at hw
  unfold chF chG chK chCutX chCutY
  rcases hw with (h | h) | (h | h)
  · rw [smoothTransition.zero_of_nonpos (by linarith : w.1 + 2 ≤ 0)]; ring
  · have : 2 - w.1 / n ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hn]; linarith
    rw [smoothTransition.zero_of_nonpos this]; ring
  · rw [smoothTransition.zero_of_nonpos (by linarith : w.2 + 2 ≤ 0)]; ring
  · rw [smoothTransition.zero_of_nonpos (by linarith : 4 - w.2 ≤ 0)]; ring

theorem ch_chG_eventuallyEq {n l x : ℝ} (hx : -1 < x) : chG n l =ᶠ[𝓝 x] chGt n l := by
  filter_upwards [Ioi_mem_nhds hx] with v hv
  have hv' : -1 < v := hv
  simp only [chG, chGt, chCutX, smoothTransition.one_of_one_le (by linarith : 1 ≤ v + 2), one_mul]

theorem ch_chK_eventuallyEq {l y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 3) :
    chK l =ᶠ[𝓝 y] fun y => Real.exp (-(l * y)) := by
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with v hv
  simp only [chK, chCutY, smoothTransition.one_of_one_le (by linarith [hv.1] : 1 ≤ v + 2),
    smoothTransition.one_of_one_le (by linarith [hv.2] : 1 ≤ 4 - v), one_mul]

theorem ch_deriv_chG {n l x : ℝ} (hx : -1 < x) : deriv (chG n l) x = chGt1 n l x := by
  rw [(ch_chG_eventuallyEq hx).deriv_eq, (ch_hasDerivAt_gt n l x).deriv]

theorem ch_deriv2_chG {n l x : ℝ} (hx : -1 < x) : deriv (deriv (chG n l)) x = chGt2 n l x := by
  have h : deriv (chG n l) =ᶠ[𝓝 x] chGt1 n l := by
    filter_upwards [Ioi_mem_nhds hx] with v hv
    exact ch_deriv_chG hv
  rw [h.deriv_eq, (ch_hasDerivAt_gt1 n l x).deriv]

theorem ch_deriv_chK {l y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 3) :
    deriv (chK l) y = -l * Real.exp (-(l * y)) := by
  rw [(ch_chK_eventuallyEq hy).deriv_eq, (ch_hasDerivAt_exp l y).deriv]

theorem ch_deriv2_chK {l y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 3) :
    deriv (deriv (chK l)) y = l ^ 2 * Real.exp (-(l * y)) := by
  have h : deriv (chK l) =ᶠ[𝓝 y] fun y => -l * Real.exp (-(l * y)) := by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with v hv
    exact ch_deriv_chK hv
  rw [h.deriv_eq, ((ch_hasDerivAt_exp l y).const_mul (-l)).deriv]
  ring

theorem ch_strip_Ioo {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) : w.2 ∈ Ioo (-1 : ℝ) 3 :=
  ⟨by linarith [hw.2.1], by linarith [hw.2.2]⟩

theorem ch_strip_fst {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) : -1 < w.1 := by
  have : 0 ≤ w.1 := hw.1
  linarith

/-- The generator of `chF n l` at strip points (any `n`). -/
theorem ch_gen_chF (D0 n l : ℝ) {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) :
    exBaseGenerator D0 (chF n l) w =
      D0 / 2 * ((w.1 * (1 + w.1) * chGt2 n l w.1 + (1 + 2 * w.1) * chGt1 n l w.1) *
          Real.exp (-(l * w.2)) +
        chGt n l w.1 * (w.2 * (1 - w.2) * (l ^ 2 * Real.exp (-(l * w.2))) +
          (1 - 2 * w.2) * (-l * Real.exp (-(l * w.2))))) := by
  have h := ch_exBaseGenerator_prod ((ch_contDiff_chG n l).of_le (by simp))
    ((ch_contDiff_chK l).of_le (by simp)) D0 w
  have hF : chF n l = fun v => chG n l v.1 * chK l v.2 := rfl
  rw [hF, h, ch_deriv2_chG (ch_strip_fst hw), ch_deriv_chG (ch_strip_fst hw),
    ch_deriv2_chK (ch_strip_Ioo hw), ch_deriv_chK (ch_strip_Ioo hw),
    (ch_chG_eventuallyEq (n := n) (l := l) (ch_strip_fst hw)).eq_of_nhds,
    (ch_chK_eventuallyEq (l := l) (ch_strip_Ioo hw)).eq_of_nhds]

theorem ch_st_one_of_lt {n x : ℝ} (hn : 0 < n) (hx : x < n) :
    smoothTransition (2 - x / n) = 1 ∧ deriv smoothTransition (2 - x / n) = 0 ∧
      deriv (deriv smoothTransition) (2 - x / n) = 0 := by
  have h1 : 1 < 2 - x / n := by
    have : x / n < 1 := (div_lt_one hn).2 hx
    linarith
  have hu : 2 - x / n ∉ Icc (0 : ℝ) 1 := fun h => by linarith [h.2]
  exact ⟨smoothTransition.one_of_one_le h1.le, ch_st_deriv_eq_zero hu, ch_st_deriv2_eq_zero hu⟩

/-- **On the strip where `x < n`, `𝒟₀ chF n l = chGen D0 l`.** -/
theorem ch_gen_chF_of_lt (D0 : ℝ) {n : ℝ} (hn : 0 < n) (l : ℝ) {w : ℝ × ℝ}
    (hw : w ∈ exBaseStrip) (hwn : w.1 < n) : exBaseGenerator D0 (chF n l) w = chGen D0 l w := by
  obtain ⟨h0, h1, h2⟩ := ch_st_one_of_lt hn hwn
  rw [ch_gen_chF D0 n l hw]
  simp only [chGt, chGt1, chGt2, h0, h1, h2, chGen]
  rw [show -(l * (w.1 + w.2)) = -(l * w.1) + -(l * w.2) by ring, Real.exp_add]
  ring

theorem ch_chF_of_lt {n : ℝ} (hn : 0 < n) (l : ℝ) {w : ℝ × ℝ} (hw : w ∈ exBaseStrip)
    (hwn : w.1 < n) : chF n l w = chExp l w := by
  obtain ⟨h0, -, -⟩ := ch_st_one_of_lt hn hwn
  have e1 := (ch_chG_eventuallyEq (n := n) (l := l) (ch_strip_fst hw)).eq_of_nhds
  have e2 := (ch_chK_eventuallyEq (l := l) (ch_strip_Ioo hw)).eq_of_nhds
  simp only [chF, e1, e2, chGt, h0, one_mul, chExp]
  rw [← Real.exp_add]
  ring_nf

theorem ch_abs_chF_le {n l : ℝ} (hl : 0 ≤ l) {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) :
    |chF n l w| ≤ 1 := by
  have e1 := (ch_chG_eventuallyEq (n := n) (l := l) (ch_strip_fst hw)).eq_of_nhds
  have e2 := (ch_chK_eventuallyEq (l := l) (ch_strip_Ioo hw)).eq_of_nhds
  have hx : 0 ≤ w.1 := hw.1
  have hy : 0 ≤ w.2 := hw.2.1
  have a1 : Real.exp (-(l * w.1)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have a2 : Real.exp (-(l * w.2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  simp only [chF, e1, e2, chGt]
  rw [abs_of_nonneg (by have := smoothTransition.nonneg (2 - w.1 / n); positivity)]
  have := smoothTransition.le_one (2 - w.1 / n)
  have := smoothTransition.nonneg (2 - w.1 / n)
  have := Real.exp_pos (-(l * w.1))
  have := Real.exp_pos (-(l * w.2))
  calc smoothTransition (2 - w.1 / n) * Real.exp (-(l * w.1)) * Real.exp (-(l * w.2))
      ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by ring

/-!
### The uniform bound of the generator
-/

/-- `(1+x)² e^{-lx} ≤ 2 + 4/l²` for `x ≥ 0`, `l > 0`. -/
theorem ch_sq_mul_exp_le {l x : ℝ} (hl : 0 < l) (hx : 0 ≤ x) :
    (1 + x) ^ 2 * Real.exp (-(l * x)) ≤ 2 + 4 / l ^ 2 := by
  have q := Real.quadratic_le_exp_of_nonneg (mul_nonneg hl.le hx)
  have h1 : 1 ≤ Real.exp (l * x) := Real.one_le_exp (by positivity)
  have hq : (l * x) ^ 2 ≤ 2 * Real.exp (l * x) := by nlinarith
  have hE : (1 + x) ^ 2 ≤ (2 + 4 / l ^ 2) * Real.exp (l * x) := by
    have hl2 : 0 < l ^ 2 := by positivity
    calc (1 + x) ^ 2 ≤ 2 + 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
      _ = 2 + 2 * (l * x) ^ 2 / l ^ 2 := by field_simp
      _ ≤ 2 * Real.exp (l * x) + 2 * (2 * Real.exp (l * x)) / l ^ 2 := by gcongr; linarith
      _ = (2 + 4 / l ^ 2) * Real.exp (l * x) := by ring
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact hE

/-- The uniform generator bound. -/
def chCb (D0 l B : ℝ) : ℝ :=
  D0 / 2 * ((B + 2 * l * B + l ^ 2 * B) * (2 + 4 / l ^ 2) + (B + l * B) * (2 + 4 / l ^ 2) +
    (l ^ 2 + l))

theorem ch_abs_gen_chF_le {D0 : ℝ} (hD0 : 0 < D0) {n l B : ℝ} (hn : 1 ≤ n) (hl : 0 < l)
    (hB : ∀ u, |smoothTransition u| ≤ B ∧ |deriv smoothTransition u| ≤ B ∧
      |deriv (deriv smoothTransition) u| ≤ B) {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) :
    |exBaseGenerator D0 (chF n l) w| ≤ chCb D0 l B := by
  rw [ch_gen_chF D0 n l hw]
  set x := w.1
  set y := w.2
  have hx : 0 ≤ x := hw.1
  have hy0 : 0 ≤ y := hw.2.1
  have hy1 : y ≤ 1 := hw.2.2
  set u := 2 - x / n
  set e := Real.exp (-(l * x))
  set ey := Real.exp (-(l * y))
  have he : 0 < e := Real.exp_pos _
  have hey : 0 < ey := Real.exp_pos _
  have hey1 : ey ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hM := ch_sq_mul_exp_le hl hx
  set M := 2 + 4 / l ^ 2
  obtain ⟨hB0, hB1, hB2⟩ := hB u
  have hBnn : 0 ≤ B := (abs_nonneg _).trans hB0
  have hni : 0 < n⁻¹ := inv_pos.2 (by linarith)
  have hni1 : n⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hni2 : n⁻¹ ^ 2 ≤ 1 := pow_le_one₀ hni.le hni1
  have hG2 : |chGt2 n l x| ≤ (B + 2 * l * B + l ^ 2 * B) * e := by
    unfold chGt2
    calc _ ≤ |n⁻¹ ^ 2 * deriv (deriv smoothTransition) u * e| +
          |2 * l * n⁻¹ * deriv smoothTransition u * e| + |l ^ 2 * smoothTransition u * e| :=
          abs_add_three _ _ _
      _ = n⁻¹ ^ 2 * |deriv (deriv smoothTransition) u| * e +
          2 * l * n⁻¹ * |deriv smoothTransition u| * e + l ^ 2 * |smoothTransition u| * e := by
          simp only [abs_mul, abs_of_pos he, abs_of_pos hni, abs_of_pos hl,
            abs_two, abs_pow]
      _ ≤ 1 * B * e + 2 * l * 1 * B * e + l ^ 2 * B * e := by gcongr
      _ = _ := by ring
  have hG1 : |chGt1 n l x| ≤ (B + l * B) * e := by
    unfold chGt1
    calc _ ≤ |-(n⁻¹ * deriv smoothTransition u) * e| + |smoothTransition u * (-l * e)| :=
          abs_add_le _ _
      _ = n⁻¹ * |deriv smoothTransition u| * e + |smoothTransition u| * (l * e) := by
          simp only [abs_mul, abs_neg, abs_of_pos he, abs_of_pos hni, abs_of_pos hl]
      _ ≤ 1 * B * e + B * (l * e) := by gcongr
      _ = _ := by ring
  have hG0 : |chGt n l x| ≤ 1 := by
    unfold chGt
    rw [abs_mul, abs_of_pos he, abs_of_nonneg (smoothTransition.nonneg _)]
    have := smoothTransition.le_one u
    have : e ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith [smoothTransition.nonneg u]
  have hxx : x * (1 + x) ≤ (1 + x) ^ 2 := by nlinarith
  have hx2 : 1 + 2 * x ≤ (1 + x) ^ 2 := by nlinarith
  have hA : |x * (1 + x) * chGt2 n l x| ≤ (B + 2 * l * B + l ^ 2 * B) * M := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ x * (1 + x))]
    calc x * (1 + x) * |chGt2 n l x| ≤ (1 + x) ^ 2 * ((B + 2 * l * B + l ^ 2 * B) * e) := by
          gcongr
      _ = (B + 2 * l * B + l ^ 2 * B) * ((1 + x) ^ 2 * e) := by ring
      _ ≤ _ := by gcongr
  have hA' : |(1 + 2 * x) * chGt1 n l x| ≤ (B + l * B) * M := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + 2 * x)]
    calc (1 + 2 * x) * |chGt1 n l x| ≤ (1 + x) ^ 2 * ((B + l * B) * e) := by gcongr
      _ = (B + l * B) * ((1 + x) ^ 2 * e) := by ring
      _ ≤ _ := by gcongr
  have hC : |y * (1 - y) * (l ^ 2 * ey) + (1 - 2 * y) * (-l * ey)| ≤ l ^ 2 + l := by
    have h1 : 0 ≤ y * (1 - y) := by nlinarith
    have h2 : y * (1 - y) ≤ 1 := by nlinarith
    have h3 : |1 - 2 * y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc _ ≤ |y * (1 - y) * (l ^ 2 * ey)| + |(1 - 2 * y) * (-l * ey)| := abs_add_le _ _
      _ = y * (1 - y) * (l ^ 2 * ey) + |1 - 2 * y| * (l * ey) := by
          rw [abs_of_nonneg (by positivity), abs_mul, abs_mul, abs_neg, abs_of_pos hl,
            abs_of_pos hey]
      _ ≤ 1 * (l ^ 2 * 1) + 1 * (l * 1) := by gcongr
      _ = _ := by ring
  have hD : 0 ≤ D0 / 2 := by positivity
  unfold chCb
  rw [abs_mul, abs_of_nonneg hD]
  refine mul_le_mul_of_nonneg_left ?_ hD
  calc _ ≤ |(x * (1 + x) * chGt2 n l x + (1 + 2 * x) * chGt1 n l x) * ey| +
        |chGt n l x * (y * (1 - y) * (l ^ 2 * ey) + (1 - 2 * y) * (-l * ey))| := abs_add_le _ _
    _ ≤ ((B + 2 * l * B + l ^ 2 * B) * M + (B + l * B) * M) * 1 + 1 * (l ^ 2 + l) := by
        rw [abs_mul, abs_mul, abs_of_pos hey]
        gcongr
        exact (abs_add_le _ _).trans (add_le_add hA hA')
    _ = _ := by ring

end BlockBand.Diffusion
