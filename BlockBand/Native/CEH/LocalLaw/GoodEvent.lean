module

public import BlockBand.Native.CEH.LocalLaw.Setup

/-!
# CEH local law, assembly: the pathwise argument on the good event

On one sample path where the martingale controls hold, a bootstrap along the flow gives the
monitored bounds of the local law on all of `[0, s]` and the final isotropic and averaged bounds.

Setting (`FlowPath`): a matrix path `R : ℝ → Mat` with `R_t = (H_t - w_t)⁻¹`, `H_t` Hermitian,
`|Im w_t| = η_t = η + c (s - t)` on `[0, s]`, `R_0 = M`, `⟨M⟩ = m`, `|Im m| = c`, `R` continuous
on `[0, s]`. For a representing matrix `K`, `X_K = tr(K (R - M))`, `D_K = (⟨R⟩ - m) tr(K R²)` and
`M_K = X_K - ∫_0 D_K` (`obsX`, `obsD`, `obsM`). `MartGood K … a b` says: at every `t ∈ [0, s]`
where the bracket integral `∫_{(0,t]} brk K` (resp. of `-i K`) is `≤ b`, `|Re M_K t| < a`
(resp. `|Im M_K t| < a`). It is what the complement of the exponential-tail events gives
(`martGood_of_not_mem`).

* `FlowPath.monitored`: from `MartGood` for the averaged quantity (`K = N⁻¹ · 1`) and the
  diagonal quadratic forms (`K = u_i u_i*`) on a dyadic height grid, via `zig_bootstrap`:
  on all of `[0, s]`, `‖⟨R⟩ - m‖ ≤ 2 K (1 + log(η_0/η_t)) / (N η_t)`, `‖⟨R⟩ - m‖ ≤ c / 2` and
  `|Im u_i* R u_i| ≤ 2 |Im u_i* M u_i|`.
* `FlowPath.target_iso`, `FlowPath.target_avg`: the final bounds at `t = s` for `x* (R - M) y`
  and `⟨(R - M) B⟩`, via `norm_target_le_const`.

Both half-planes: only `|Im w_t|` enters. Measure: Lebesgue measure on `ℝ` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.LocalLaw

open Matrix MeasureTheory Set
open BlockBand.External.CEH BlockBand.Native.CEH.Phase1 BlockBand.Native.CEH.Flow
open BlockBand.Native.CEH.Zig

variable {N : ℕ}

/-- The deterministic path hypotheses for one sample path, in variance time `t ∈ [0, s]`:
* `H t` is Hermitian, and `R t` is its resolvent at the characteristic point `w t`;
* `|Im w t| = zigHeight η c s t = η + c(s − t)`;
* `R 0 = Mz`, with `⟨Mz⟩ = m` and `c = |Im m|`;
* `R` is continuous on `[0, s]`.

`flowPath_pathR` supplies all of these for every sample of the flow. -/
structure FlowPath (R H : ℝ → Matrix (Fin N) (Fin N) ℂ) (w : ℝ → ℂ) (Mz : Matrix (Fin N) (Fin N) ℂ)
    (m : ℂ) (η c s : ℝ) : Prop where
  herm : ∀ t, (H t).IsHermitian
  res : ∀ t, R t = Phase1.resolvent (H t) (w t)
  height : ∀ t ∈ Icc 0 s, |(w t).im| = zigHeight η c s t
  init : R 0 = Mz
  cont : ContinuousOn R (Icc 0 s)
  trace_init : normalizedTrace Mz = m
  c_eq : |m.im| = c
  η_pos : 0 < η
  c_pos : 0 < c
  s_nonneg : 0 ≤ s

/-- Martingale control from the complement of the tail events.

For every `t ∈ [0, s]`: if the bracket integral `∫_{(0,t]} brk` (a Bochner integral; the density
`brk` is continuous on `[0, s]`) is `≤ b` up to that same `t`, then the real or imaginary part of
the compensated observable `obsM` is `< a` at `t`. This localizes without a stopping time.
`martGood_of_not_mem` proves it off `tailEvent`. -/
def MartGood (K Mz : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (s a b : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) s,
    (∫ r in Ioc 0 t, brk K R r ≤ b → |(obsM K Mz m R t).re| < a) ∧
    (∫ r in Ioc 0 t, brk ((-Complex.I) • K) R r ≤ b → |(obsM K Mz m R t).im| < a)

theorem MartGood.norm_lt {K Mz : Matrix (Fin N) (Fin N) ℂ} {m : ℂ}
    {R : ℝ → Matrix (Fin N) (Fin N) ℂ} {s a b t : ℝ} (h : MartGood K Mz m R s a b)
    (ht : t ∈ Icc 0 s) (h1 : ∫ r in Ioc 0 t, brk K R r ≤ b)
    (h2 : ∫ r in Ioc 0 t, brk ((-Complex.I) • K) R r ≤ b) :
    ‖obsM K Mz m R t‖ < 2 * a := by
  have e1 := (h t ht).1 h1
  have e2 := (h t ht).2 h2
  calc ‖obsM K Mz m R t‖ ≤ |(obsM K Mz m R t).re| + |(obsM K Mz m R t).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < a + a := add_lt_add e1 e2
    _ = 2 * a := by ring

theorem abs_im_le_add_norm_sub (A B : ℂ) : |A.im| ≤ |B.im| + ‖A - B‖ := by
  have h : A.im = B.im + (A - B).im := by simp
  rw [h]
  exact (abs_add_le _ _).trans (add_le_add_right (Complex.abs_im_le_norm _) _)

theorem obsX_isoK (x y : Fin N → ℂ) (Mz : Matrix (Fin N) (Fin N) ℂ)
    (R : ℝ → Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    obsX (isoK x y) Mz R t = sourceMatrixElement (R t) x y - sourceMatrixElement Mz x y := by
  rw [obsX, trace_isoK_mul, sourceMatrixElement_sub]

theorem obsX_obsB (B Mz : Matrix (Fin N) (Fin N) ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    obsX (obsB B) Mz R t = normalizedTrace ((R t - Mz) * B) := by
  rw [obsX, trace_obsB_mul]

namespace FlowPath

variable {R H : ℝ → Matrix (Fin N) (Fin N) ℂ} {w : ℝ → ℂ} {Mz : Matrix (Fin N) (Fin N) ℂ}
  {m : ℂ} {η c s : ℝ}

theorem height_pos (hP : FlowPath R H w Mz m η c s) {t : ℝ} (ht : t ∈ Icc 0 s) :
    0 < zigHeight η c s t :=
  zigHeight_pos hP.η_pos hP.c_pos.le ht.2

theorem im_ne (hP : FlowPath R H w Mz m η c s) {t : ℝ} (ht : t ∈ Icc 0 s) : (w t).im ≠ 0 := by
  intro h
  have h1 := hP.height t ht
  rw [h, abs_zero] at h1
  linarith [hP.height_pos ht]

theorem continuous_trace_mul (K : Matrix (Fin N) (Fin N) ℂ) :
    Continuous fun X : Matrix (Fin N) (Fin N) ℂ => trace (K * X) :=
  (continuous_const.matrix_mul continuous_id).matrix_trace

theorem continuous_normalizedTrace :
    Continuous fun X : Matrix (Fin N) (Fin N) ℂ => normalizedTrace X :=
  continuous_const.mul continuous_id.matrix_trace

theorem continuousOn_obsX (hP : FlowPath R H w Mz m η c s) (K : Matrix (Fin N) (Fin N) ℂ) :
    ContinuousOn (obsX K Mz R) (Icc 0 s) :=
  (continuous_trace_mul K).comp_continuousOn (hP.cont.sub continuousOn_const)

theorem continuousOn_obsD (hP : FlowPath R H w Mz m η c s) (K : Matrix (Fin N) (Fin N) ℂ) :
    ContinuousOn (obsD K m R) (Icc 0 s) :=
  ((continuous_normalizedTrace.comp_continuousOn hP.cont).sub continuousOn_const).mul
    ((continuous_trace_mul K).comp_continuousOn (hP.cont.mul hP.cont))

theorem intervalIntegrable_obsD (hP : FlowPath R H w Mz m η c s) (K : Matrix (Fin N) (Fin N) ℂ) :
    IntervalIntegrable (obsD K m R) volume 0 s :=
  (hP.continuousOn_obsD K).intervalIntegrable_of_Icc hP.s_nonneg

theorem obsX_zero (hP : FlowPath R H w Mz m η c s) (K : Matrix (Fin N) (Fin N) ℂ) :
    obsX K Mz R 0 = 0 := by
  simp [obsX, hP.init]

theorem obsX_avgK (hP : FlowPath R H w Mz m η c s) (t : ℝ) :
    obsX (avgK N) Mz R t = normalizedTrace (R t) - m := by
  rw [obsX, trace_avgK_mul, normalizedTrace_sub, hP.trace_init]

theorem abs_im_trace_le (hP : FlowPath R H w Mz m η c s) (t : ℝ) :
    |(normalizedTrace (R t)).im| ≤ c + ‖obsX (avgK N) Mz R t‖ := by
  rw [hP.obsX_avgK, ← hP.c_eq]
  exact abs_im_le_add_norm_sub _ _

/-!
### Drift bounds (unconditional)
-/

theorem norm_obsD_avgK_le (hP : FlowPath R H w Mz m η c s) {r : ℝ} (hr : r ∈ Icc 0 s) :
    ‖obsD (avgK N) m R r‖ ≤
      ‖obsX (avgK N) Mz R r‖ * (c + ‖obsX (avgK N) Mz R r‖) / zigHeight η c s r := by
  have hb := hP.abs_im_trace_le r
  rw [obsD, trace_avgK_mul, ← hP.obsX_avgK, norm_mul, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := norm_normalizedTrace_resolvent_sq_le' (hP.herm r) (hP.im_ne hr)
  rw [← hP.res r, hP.height r hr] at h
  exact h.trans (div_le_div_of_nonneg_right hb (hP.height_pos hr).le)

theorem norm_obsD_isoK_self_le (hP : FlowPath R H w Mz m η c s) (v : Fin N → ℂ) {r : ℝ}
    (hr : r ∈ Icc 0 s) :
    ‖obsD (isoK v v) m R r‖ ≤ ‖obsX (avgK N) Mz R r‖ *
      (|(sourceMatrixElement Mz v v).im| + ‖obsX (isoK v v) Mz R r‖) / zigHeight η c s r := by
  rw [obsD, trace_isoK_mul, ← hP.obsX_avgK, norm_mul, mul_div_assoc, obsX_isoK]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := norm_sourceMatrixElement_resolvent_sq_self_le (hP.herm r) (hP.im_ne hr) v
  rw [← hP.res r, hP.height r hr] at h
  exact h.trans (div_le_div_of_nonneg_right (abs_im_le_add_norm_sub _ _) (hP.height_pos hr).le)

theorem norm_obsD_isoK_le (hP : FlowPath R H w Mz m η c s) (x y : Fin N → ℂ) {r : ℝ}
    (hr : r ∈ Icc 0 s) :
    ‖obsD (isoK x y) m R r‖ ≤ ‖obsX (avgK N) Mz R r‖ *
      (Real.sqrt |(sourceMatrixElement (R r) x x).im| *
        Real.sqrt |(sourceMatrixElement (R r) y y).im|) / zigHeight η c s r := by
  rw [obsD, trace_isoK_mul, ← hP.obsX_avgK, norm_mul, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := norm_sourceMatrixElement_resolvent_sq_le (hP.herm r) (hP.im_ne hr) x y
  rw [← hP.res r, hP.height r hr] at h
  exact h

theorem norm_obsD_obsB_le (hP : FlowPath R H w Mz m η c s) (B : Matrix (Fin N) (Fin N) ℂ)
    {r : ℝ} (hr : r ∈ Icc 0 s) :
    ‖obsD (obsB B) m R r‖ ≤ ‖obsX (avgK N) Mz R r‖ *
      Real.sqrt (|(normalizedTrace (R r)).im| *
        |(normalizedTrace (External.CEH.imaginaryPart (R r) * B * Bᴴ)).re|) /
        zigHeight η c s r := by
  rw [obsD, trace_obsB_mul, ← hP.obsX_avgK, norm_mul, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := norm_normalizedTrace_resolvent_sq_mul_le (hP.herm r) (hP.im_ne hr) B
  rw [← hP.res r, hP.height r hr] at h
  refine h.trans ?_
  rw [div_eq_inv_mul, ← abs_re_normalizedTrace_imaginaryPart, ← abs_mul]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_abs_self _))
    (inv_nonneg.2 (hP.height_pos hr).le)

/-!
### Bracket bounds
-/

theorem brk_avgK_le (hP : FlowPath R H w Mz m η c s) {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : K = avgK N ∨ K = (-Complex.I) • avgK N) {r : ℝ} (hr : r ∈ Icc 0 s) :
    brk K R r ≤ 1 / (N : ℝ) ^ 2 * (|(normalizedTrace (R r)).im| / zigHeight η c s r ^ 3) := by
  have hf := avg_bracket_factor_le (hP.herm r) (hP.im_ne hr)
  rw [← hP.res r, hP.height r hr] at hf
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2 := by positivity
  rcases hK with rfl | rfl
  · exact (brk_obsB_le 1 R r).trans (mul_le_mul_of_nonneg_left hf hN)
  · exact (brk_negI_obsB_le 1 R r).trans (mul_le_mul_of_nonneg_left hf hN)

theorem brk_isoK_le' (hP : FlowPath R H w Mz m η c s) (x y : Fin N → ℂ)
    {K : Matrix (Fin N) (Fin N) ℂ} (hK : K = isoK x y ∨ K = (-Complex.I) • isoK x y) {r : ℝ}
    (hr : r ∈ Icc 0 s) :
    brk K R r ≤ 1 / (N : ℝ) * (|(sourceMatrixElement (R r) x x).im| *
      |(sourceMatrixElement (R r) y y).im| / zigHeight η c s r ^ 2) := by
  have hf := iso_bracket_factor_eq (hP.herm r) (hP.im_ne hr) x y
  rw [← hP.res r, hP.height r hr] at hf
  rcases hK with rfl | rfl
  · exact (brk_isoK_le x y R r).trans_eq (by rw [hf])
  · exact (brk_negI_isoK_le x y R r).trans_eq (by rw [hf])

theorem brk_obsB_le' (hP : FlowPath R H w Mz m η c s) (B : Matrix (Fin N) (Fin N) ℂ)
    {K : Matrix (Fin N) (Fin N) ℂ} (hK : K = obsB B ∨ K = (-Complex.I) • obsB B) {r : ℝ}
    (hr : r ∈ Icc 0 s) :
    brk K R r ≤ 1 / (N : ℝ) ^ 2 *
      (|(normalizedTrace (External.CEH.imaginaryPart (R r) * B * Bᴴ)).re| /
        zigHeight η c s r ^ 3) := by
  have hf := obsB_bracket_factor_le (hP.herm r) (hP.im_ne hr) B
  rw [← hP.res r, hP.height r hr] at hf
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2 := by positivity
  rcases hK with rfl | rfl
  · exact (brk_obsB_le B R r).trans (mul_le_mul_of_nonneg_left hf hN)
  · exact (brk_negI_obsB_le B R r).trans (mul_le_mul_of_nonneg_left hf hN)

/-- Bracket integral along the height. -/
theorem bracket_integral_le (hP : FlowPath R H w Mz m η c s) {K : Matrix (Fin N) (Fin N) ℂ}
    {β t : ℝ} (ht : t ∈ Icc 0 s) (hb : ∀ r ∈ Ioo 0 t, brk K R r ≤ β / zigHeight η c s r ^ 2) :
    ∫ r in Ioc 0 t, brk K R r ≤ β / c * (1 / zigHeight η c s t - 1 / zigHeight η c s 0) :=
  setIntegral_Ioc_le_of_le hP.η_pos hP.c_pos ht.1 ht.2 (fun r _ => brk_nonneg K R r) hb

end FlowPath

/-!
### Scalar inequalities
-/

theorem aux_avg_bracket {N c ηt η0 h : ℝ} (hN : 0 < N) (hc : 0 < c) (hh : 0 < h)
    (h1 : h ≤ ηt) (h2 : ηt ≤ η0) :
    2 * c / (N ^ 2 * ηt) / c * (1 / ηt - 1 / η0) ≤ 2 / (N ^ 2 * h ^ 2) := by
  have hηt : 0 < ηt := hh.trans_le h1
  have hη0 : 0 < η0 := hηt.trans_le h2
  have e : 2 * c / (N ^ 2 * ηt) / c = 2 / (N ^ 2 * ηt) := by field_simp
  rw [e]
  calc 2 / (N ^ 2 * ηt) * (1 / ηt - 1 / η0) ≤ 2 / (N ^ 2 * ηt) * (1 / ηt) := by
        have : 0 < 1 / η0 := by positivity
        gcongr
        linarith
    _ = 2 / (N ^ 2 * ηt ^ 2) := by field_simp
    _ ≤ 2 / (N ^ 2 * h ^ 2) := by gcongr

theorem aux_avg_scale {N K ηt h : ℝ} (hN : 0 < N) (hK : 0 ≤ K) (hh : 0 < h) (hηt : 0 < ηt)
    (h2 : ηt ≤ 2 * h) : 2 * (K / (4 * N * h)) ≤ K / (N * ηt) := by
  rw [show 2 * (K / (4 * N * h)) = K / (N * (2 * h)) by field_simp; ring]
  gcongr

theorem aux_vec_bracket {N c ρ ηt η0 h W : ℝ} (hN : 0 < N) (hc : 0 < c) (hρ : 0 < ρ)
    (hρc : ρ ≤ c) (hh : 0 < h) (h1 : h ≤ ηt) (h2 : ηt ≤ η0) :
    4 * W ^ 2 / N / c * (1 / ηt - 1 / η0) ≤ 4 * W ^ 2 / (N * ρ * h) := by
  have hηt : 0 < ηt := hh.trans_le h1
  have hη0 : 0 < η0 := hηt.trans_le h2
  calc 4 * W ^ 2 / N / c * (1 / ηt - 1 / η0) ≤ 4 * W ^ 2 / N / c * (1 / ηt) := by
        have : 0 < 1 / η0 := by positivity
        gcongr
        linarith
    _ = 4 * W ^ 2 / (N * c * ηt) := by field_simp
    _ ≤ 4 * W ^ 2 / (N * ρ * h) := by gcongr

theorem aux_vec_scale {N K W ρ ηt h : ℝ} (hN : 0 < N) (hK : 0 ≤ K) (hW : 0 ≤ W) (hρ : 0 < ρ)
    (hh : 0 < h) (hηt : 0 < ηt) (h2 : ηt ≤ 2 * h) :
    2 * (K * W / (2 * Real.sqrt (2 * N * h * ρ))) ≤ K * W / Real.sqrt (N * ηt * ρ) := by
  have hs1 : 0 < Real.sqrt (2 * N * h * ρ) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 0 < Real.sqrt (N * ηt * ρ) := Real.sqrt_pos.2 (by positivity)
  rw [show 2 * (K * W / (2 * Real.sqrt (2 * N * h * ρ))) = K * W / Real.sqrt (2 * N * h * ρ) by
    field_simp]
  have hKW : 0 ≤ K * W := mul_nonneg hK hW
  refine div_le_div_of_nonneg_left hKW hs2 (Real.sqrt_le_sqrt ?_)
  have : N * ηt * ρ ≤ N * (2 * h) * ρ := by gcongr
  linarith

/-- `θ / (N η_r) ≤ c / 2` from `2 θ ≤ N c η`. -/
theorem aux_thr_avg {N θ c η ηr : ℝ} (hN : 0 < N) (hc : 0 ≤ c) (hη : 0 < η)
    (hr : η ≤ ηr)
    (hsmall : 2 * θ ≤ N * c * η) : θ / (N * ηr) ≤ c / 2 := by
  have hηr : 0 < ηr := hη.trans_le hr
  rw [div_le_div_iff₀ (by positivity) two_pos]
  nlinarith [mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ N * c)]

/-- `θ W / √(N η_r ρ) ≤ W` from `θ² ≤ N η ρ`. -/
theorem aux_thr_vec {N θ ρ η ηr W : ℝ} (hN : 0 < N) (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hη : 0 < η)
    (hr : η ≤ ηr) (hW : 0 ≤ W) (hsmall : θ ^ 2 ≤ N * η * ρ) :
    θ * W / Real.sqrt (N * ηr * ρ) ≤ W := by
  have hηr : 0 < ηr := hη.trans_le hr
  have hs : 0 < Real.sqrt (N * ηr * ρ) := Real.sqrt_pos.2 (by positivity)
  rw [div_le_iff₀ hs, mul_comm θ W]
  refine mul_le_mul_of_nonneg_left ?_ hW
  rw [← Real.sqrt_sq hθ]
  exact Real.sqrt_le_sqrt (hsmall.trans (by gcongr))

namespace FlowPath

variable {R H : ℝ → Matrix (Fin N) (Fin N) ℂ} {w : ℝ → ℂ} {Mz : Matrix (Fin N) (Fin N) ℂ}
  {m : ℂ} {η c s : ℝ}

/-- **Monitored bounds (CEH (6.2)–(6.3)) on the good event.**

`zig_bootstrap` is applied with:
* `V` = the nonzero vectors among `u`, with weights `|Im u*Mz u| > 0`;
* the dyadic levels `h_k = η_0/2^k`, `k ≤ L`, with `2^L η ≥ η_0`, and at each level the
  martingale controls `MartGood` with `a_k = K/(4Nh_k)`, `b_k = 2/(N²h_k²)` (averaged) and
  `a_k = K w/(2√(2Nh_kρ))`, `b_k = 4w²/(Nρh_k)` (vector), so that `a_k²/(2b_k) = K²/64`.

At a time `t` with `h_k ≤ η_t ≤ 2h_k`, the strict threshold on `[0, t)` gives two bounds:
* `‖⟨R⟩ − m‖ ≤ c/2`, using `hsmall₂ : 2θ ≤ Ncη` (`aux_thr_avg`);
* `|Im v*Rv| ≤ 2w_v`, using `hsmall₄ : θ² ≤ Nηρ` (`aux_thr_vec`).

Ward's identity then bounds the bracket integral up to `t` by `b_k`; the vector bracket bound also
uses `ρ ≤ c` (`aux_vec_bracket`). This yields the bootstrap's martingale hypothesis. No stopping
time is used. -/
theorem monitored (hP : FlowPath R H w Mz m η c s) {ι : Type*} [Fintype ι]
    (u : ι → Fin N → ℂ) {ρ θ K : ℝ} {L : ℕ} (hN : 0 < N) (hρ : 0 < ρ) (hρc : ρ ≤ c)
    (hK : 0 ≤ K) (hw : ∀ i, u i ≠ 0 → 0 < |(sourceMatrixElement Mz (u i) (u i)).im|)
    (hL : zigHeight η c s 0 ≤ 2 ^ L * η)
    (hsmall₁ : 4 * K * (1 + Real.log (zigHeight η c s 0 / η)) < θ)
    (hsmall₂ : 2 * θ ≤ N * c * η) (hsmall₃ : θ ^ 2 * ρ ≤ K ^ 2 * c ^ 2 * (N * η))
    (hsmall₄ : θ ^ 2 ≤ N * η * ρ)
    (hav : ∀ k ≤ L, MartGood (avgK N) Mz m R s (K / (4 * N * (zigHeight η c s 0 / 2 ^ k)))
      (2 / ((N : ℝ) ^ 2 * (zigHeight η c s 0 / 2 ^ k) ^ 2)))
    (hv : ∀ i, u i ≠ 0 → ∀ k ≤ L, MartGood (isoK (u i) (u i)) Mz m R s
      (K * |(sourceMatrixElement Mz (u i) (u i)).im| /
        (2 * Real.sqrt (2 * N * (zigHeight η c s 0 / 2 ^ k) * ρ)))
      (4 * |(sourceMatrixElement Mz (u i) (u i)).im| ^ 2 /
        (N * ρ * (zigHeight η c s 0 / 2 ^ k)))) :
    ∀ t ∈ Icc 0 s,
      ‖normalizedTrace (R t) - m‖ ≤
        2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t)) /
          (N * zigHeight η c s t) ∧
      ‖normalizedTrace (R t) - m‖ ≤ c / 2 ∧
      ∀ i, |(sourceMatrixElement (R t) (u i) (u i)).im| ≤
        2 * |(sourceMatrixElement Mz (u i) (u i)).im| := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hη := hP.η_pos
  have hc := hP.c_pos
  have hs := hP.s_nonneg
  have hθ : 0 ≤ θ := le_of_lt (lt_of_le_of_lt (by
    have : 0 ≤ Real.log (zigHeight η c s 0 / η) :=
      Real.log_nonneg ((one_le_div hη).2 (le_zigHeight hc.le hs))
    positivity) hsmall₁)
  set V := {i : ι // u i ≠ 0}
  set wv : V → ℝ := fun v => |(sourceMatrixElement Mz (u v.1) (u v.1)).im| with hwv
  set Xav := obsX (avgK N) Mz R
  set Xv : V → ℝ → ℂ := fun v => obsX (isoK (u v.1) (u v.1)) Mz R with hXv
  have hη0 : 0 < zigHeight η c s 0 := zigHeight_pos hη hc.le hs
  -- the grid point of a time
  have grid : ∀ t ∈ Icc 0 s, ∃ k ≤ L, zigHeight η c s 0 / 2 ^ k ≤ zigHeight η c s t ∧
      zigHeight η c s t ≤ 2 * (zigHeight η c s 0 / 2 ^ k) := by
    intro t ht
    refine exists_grid hη0 (zigHeight_antitone hc.le ht.1) (hL.trans ?_)
    exact mul_le_mul_of_nonneg_left (le_zigHeight hc.le ht.2) (by positivity)
  -- strict threshold consequences
  have thr_av : ∀ r ∈ Icc 0 s, ‖Xav r‖ < θ / (N * zigHeight η c s r) → ‖Xav r‖ ≤ c / 2 :=
    fun r hr h => h.le.trans (aux_thr_avg hNr hc.le hη (le_zigHeight hc.le hr.2) hsmall₂)
  have thr_v : ∀ v : V, ∀ r ∈ Icc 0 s,
      ‖Xv v r‖ < θ * wv v / Real.sqrt (N * zigHeight η c s r * ρ) → ‖Xv v r‖ ≤ wv v :=
    fun v r hr h => h.le.trans
      (aux_thr_vec hNr hθ hρ hη (le_zigHeight hc.le hr.2) (abs_nonneg _) hsmall₄)
  have im_v : ∀ v : V, ∀ r, ‖Xv v r‖ ≤ wv v →
      |(sourceMatrixElement (R r) (u v.1) (u v.1)).im| ≤ 2 * wv v := by
    intro v r h
    have := abs_im_le_add_norm_sub (sourceMatrixElement (R r) (u v.1) (u v.1))
      (sourceMatrixElement Mz (u v.1) (u v.1))
    rw [← obsX_isoK] at this
    simp only [hXv] at h
    simp only [hwv]
    linarith
  have hboot := zig_bootstrap (V := V) (N := (N : ℝ)) (η := η) (c := c) (s := s) (ρ := ρ)
    (θ := θ) (K := K) (w := wv) (Xav := Xav) (Mav := obsM (avgK N) Mz m R)
    (Dav := obsD (avgK N) m R) (Xv := Xv) (Mv := fun v => obsM (isoK (u v.1) (u v.1)) Mz m R)
    (Dv := fun v => obsD (isoK (u v.1) (u v.1)) m R) hNr hη hc hρ hK (fun v => hw v.1 v.2)
    hsmall₁ hsmall₂ hsmall₃ (hP.continuousOn_obsX _) (fun v => hP.continuousOn_obsX _)
    (hP.obsX_zero _) (fun v => hP.obsX_zero _) (hP.intervalIntegrable_obsD _)
    (fun v => hP.intervalIntegrable_obsD _) (fun t _ => obsX_eq _ _ _ _ t)
    (fun v t _ => obsX_eq _ _ _ _ t) (fun r hr _ => hP.norm_obsD_avgK_le hr)
    (fun v r hr _ => hP.norm_obsD_isoK_self_le (u v.1) hr) ?_ ?_
  · intro t ht
    obtain ⟨hstr, hb1, _⟩ := hboot t ht
    refine ⟨by rw [← hP.obsX_avgK]; exact hb1, by rw [← hP.obsX_avgK]; exact thr_av t ht hstr.1,
      fun i => ?_⟩
    by_cases hi : u i = 0
    · rw [hi]; simp [sourceMatrixElement]
    · exact im_v ⟨i, hi⟩ t (thr_v ⟨i, hi⟩ t ht (hstr.2 ⟨i, hi⟩))
  · -- averaged martingale part
    intro t ht hstr
    obtain ⟨k, hk, hk1, hk2⟩ := grid t ht
    set h := zigHeight η c s 0 / 2 ^ k with hh
    have hhpos : 0 < h := by positivity
    have hηt := hP.height_pos ht
    have hb : ∀ K' : Matrix (Fin N) (Fin N) ℂ, (K' = avgK N ∨ K' = (-Complex.I) • avgK N) →
        ∫ r in Ioc 0 t, brk K' R r ≤ 2 / ((N : ℝ) ^ 2 * h ^ 2) := by
      intro K' hK'
      refine le_trans (hP.bracket_integral_le (β := 2 * c / (N ^ 2 * zigHeight η c s t)) ht
        fun r hr => ?_) (aux_avg_bracket hNr hc hhpos hk1 (zigHeight_antitone hc.le ht.1))
      have hrI : r ∈ Icc 0 s := ⟨hr.1.le, hr.2.le.trans ht.2⟩
      have hηr := hP.height_pos hrI
      have hX := thr_av r hrI (hstr r ⟨hr.1.le, hr.2⟩).1
      have him : |(normalizedTrace (R r)).im| ≤ 2 * c := by
        have := hP.abs_im_trace_le r; linarith
      have hmono : zigHeight η c s t ≤ zigHeight η c s r := zigHeight_antitone hc.le hr.2.le
      calc brk K' R r ≤ 1 / (N : ℝ) ^ 2 * (|(normalizedTrace (R r)).im| /
            zigHeight η c s r ^ 3) := hP.brk_avgK_le hK' hrI
        _ ≤ 1 / (N : ℝ) ^ 2 * (2 * c / zigHeight η c s r ^ 3) := by gcongr
        _ = 2 * c / (N ^ 2 * zigHeight η c s r) / zigHeight η c s r ^ 2 := by
            field_simp
        _ ≤ 2 * c / (N ^ 2 * zigHeight η c s t) / zigHeight η c s r ^ 2 := by
            gcongr
    have hlt := (hav k hk).norm_lt ht (hb _ (Or.inl rfl)) (hb _ (Or.inr rfl))
    exact hlt.le.trans (aux_avg_scale hNr hK hhpos hηt hk2)
  · -- vector martingale parts
    intro v t ht hstr
    obtain ⟨k, hk, hk1, hk2⟩ := grid t ht
    set h := zigHeight η c s 0 / 2 ^ k with hh
    have hhpos : 0 < h := by positivity
    have hηt := hP.height_pos ht
    have hW : 0 ≤ wv v := abs_nonneg _
    have hb : ∀ K' : Matrix (Fin N) (Fin N) ℂ,
        (K' = isoK (u v.1) (u v.1) ∨ K' = (-Complex.I) • isoK (u v.1) (u v.1)) →
        ∫ r in Ioc 0 t, brk K' R r ≤ 4 * wv v ^ 2 / (N * ρ * h) := by
      intro K' hK'
      refine le_trans (hP.bracket_integral_le (β := 4 * wv v ^ 2 / N) ht fun r hr => ?_)
        (aux_vec_bracket hNr hc hρ hρc hhpos hk1 (zigHeight_antitone hc.le ht.1))
      have hrI : r ∈ Icc 0 s := ⟨hr.1.le, hr.2.le.trans ht.2⟩
      have hηr := hP.height_pos hrI
      have hX := im_v v r (thr_v v r hrI ((hstr r ⟨hr.1.le, hr.2⟩).2 v))
      have h0 : 0 ≤ |(sourceMatrixElement (R r) (u v.1) (u v.1)).im| := abs_nonneg _
      calc brk K' R r ≤ 1 / (N : ℝ) * (|(sourceMatrixElement (R r) (u v.1) (u v.1)).im| *
            |(sourceMatrixElement (R r) (u v.1) (u v.1)).im| / zigHeight η c s r ^ 2) :=
            hP.brk_isoK_le' _ _ hK' hrI
        _ ≤ 1 / (N : ℝ) * (2 * wv v * (2 * wv v) / zigHeight η c s r ^ 2) := by gcongr
        _ = 4 * wv v ^ 2 / N / zigHeight η c s r ^ 2 := by field_simp; ring
    have hlt := (hv v.1 v.2 k hk).norm_lt ht (hb _ (Or.inl rfl)) (hb _ (Or.inr rfl))
    exact hlt.le.trans (aux_vec_scale hNr hK hW hρ hhpos hηt hk2)

/-- The final bracket bound: `(β / c)(1/η_s - 1/η_0) ≤ β / (c η)`. -/
theorem aux_final_bracket {β : ℝ} (hP : FlowPath R H w Mz m η c s) (hβ : 0 ≤ β) :
    β / c * (1 / zigHeight η c s s - 1 / zigHeight η c s 0) ≤ β / (c * η) := by
  have hη := hP.η_pos
  have hc := hP.c_pos
  have hη0 : 0 < zigHeight η c s 0 := zigHeight_pos hη hc.le hP.s_nonneg
  rw [zigHeight_self]
  calc β / c * (1 / η - 1 / zigHeight η c s 0) ≤ β / c * (1 / η) := by
        have : 0 < 1 / zigHeight η c s 0 := by positivity
        have : 0 ≤ β / c := div_nonneg hβ hc.le
        gcongr
        linarith
    _ = β / (c * η) := by field_simp

theorem sqrt_two_mul_sqrt_two_mul {a b : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (2 * a) * Real.sqrt (2 * b) = 2 * Real.sqrt (a * b) := by
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * a),
    show 2 * a * (2 * b) = 2 ^ 2 * (a * b) by ring,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Isotropic target at `t = s`.** The drift is `(⟨R⟩ − m)(R²)_xy` with
`|(R²)_xy| ≤ 2√(w_x w_y)/η_t`, so `Λ = 2√(w_x w_y)`, and the bracket integral is
`≤ 4 w_x w_y/(Ncη)`. -/
theorem target_iso (hP : FlowPath R H w Mz m η c s) (x y : Fin N → ℂ) {K a : ℝ} (hN : 0 < N)
    (hK : 0 ≤ K)
    (hmon : ∀ t ∈ Icc 0 s,
      ‖normalizedTrace (R t) - m‖ ≤
        2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t)) /
          (N * zigHeight η c s t) ∧
      |(sourceMatrixElement (R t) x x).im| ≤ 2 * |(sourceMatrixElement Mz x x).im| ∧
      |(sourceMatrixElement (R t) y y).im| ≤ 2 * |(sourceMatrixElement Mz y y).im|)
    (hmart : MartGood (isoK x y) Mz m R s a
      (4 * |(sourceMatrixElement Mz x x).im| * |(sourceMatrixElement Mz y y).im| /
        (N * c * η))) :
    ‖sourceMatrixElement (R s) x y - sourceMatrixElement Mz x y‖ ≤
      2 * a + 2 * K * (2 * Real.sqrt (|(sourceMatrixElement Mz x x).im| *
        |(sourceMatrixElement Mz y y).im|)) * (1 + Real.log (zigHeight η c s 0 / η)) /
        (N * c * η) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hη := hP.η_pos
  have hc := hP.c_pos
  have hs := hP.s_nonneg
  set wx := |(sourceMatrixElement Mz x x).im| with hwx
  set wy := |(sourceMatrixElement Mz y y).im| with hwy
  have hwx0 : 0 ≤ wx := abs_nonneg _
  have hwy0 : 0 ≤ wy := abs_nonneg _
  have hsI : s ∈ Icc 0 s := ⟨hs, le_rfl⟩
  have hb : ∀ K' : Matrix (Fin N) (Fin N) ℂ, (K' = isoK x y ∨ K' = (-Complex.I) • isoK x y) →
      ∫ r in Ioc 0 s, brk K' R r ≤ 4 * wx * wy / (N * c * η) := by
    intro K' hK'
    refine le_trans (hP.bracket_integral_le (β := 4 * wx * wy / N) hsI fun r hr => ?_)
      ((aux_final_bracket hP (by positivity)).trans_eq (by field_simp))
    have hrI : r ∈ Icc 0 s := ⟨hr.1.le, hr.2.le⟩
    have hηr := hP.height_pos hrI
    obtain ⟨_, h1, h2⟩ := hmon r hrI
    calc brk K' R r ≤ 1 / (N : ℝ) * (|(sourceMatrixElement (R r) x x).im| *
          |(sourceMatrixElement (R r) y y).im| / zigHeight η c s r ^ 2) :=
          hP.brk_isoK_le' x y hK' hrI
      _ ≤ 1 / (N : ℝ) * (2 * wx * (2 * wy) / zigHeight η c s r ^ 2) := by
          gcongr
      _ = 4 * wx * wy / N / zigHeight η c s r ^ 2 := by field_simp; ring
  have hmartlt := hmart.norm_lt hsI (hb _ (Or.inl rfl)) (hb _ (Or.inr rfl))
  have h := norm_target_le_const (N := (N : ℝ)) (η := η) (c := c) (s := s) (K := K)
    (Λ := 2 * Real.sqrt (wx * wy)) (KY := 2 * a) (Y := obsX (isoK x y) Mz R)
    (MY := obsM (isoK x y) Mz m R) (DY := obsD (isoK x y) m R) (Xav := obsX (avgK N) Mz R)
    hNr hη hc hK (by positivity) hsI (hP.intervalIntegrable_obsD _) (obsX_eq _ _ _ _ s)
    (fun r hr => by rw [hP.obsX_avgK]; exact (hmon r hr).1)
    (fun r hr => by
      have hηr := hP.height_pos hr
      obtain ⟨_, h1, h2⟩ := hmon r hr
      refine (hP.norm_obsD_isoK_le x y hr).trans ?_
      rw [← sqrt_two_mul_sqrt_two_mul hwx0]
      gcongr) hmartlt.le
  rw [obsX_isoK] at h
  exact h

/-- **Averaged target at `t = s`.** The drift is `(⟨R⟩ − m)⟨R² B⟩` with
`|⟨R²B⟩| ≤ η_t⁻¹√(⟨Im R⟩⟨Im R BB*⟩)`, so `Λ = 2√(cW)` with
`W = N⁻¹ Σ_j |Im (Be_j)* Mz (Be_j)|`, and the bracket integral is `≤ 2W/(N²cη²)`. -/
theorem target_avg (hP : FlowPath R H w Mz m η c s) (B : Matrix (Fin N) (Fin N) ℂ) {K a : ℝ}
    (hN : 0 < N) (hK : 0 ≤ K)
    (hmon : ∀ t ∈ Icc 0 s,
      ‖normalizedTrace (R t) - m‖ ≤
        2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t)) /
          (N * zigHeight η c s t) ∧
      ‖normalizedTrace (R t) - m‖ ≤ c / 2 ∧
      ∀ j, |(sourceMatrixElement (R t) (col B j) (col B j)).im| ≤
        2 * |(sourceMatrixElement Mz (col B j) (col B j)).im|)
    (hmart : MartGood (obsB B) Mz m R s a
      (2 * ((N : ℝ)⁻¹ * ∑ j, |(sourceMatrixElement Mz (col B j) (col B j)).im|) /
        ((N : ℝ) ^ 2 * c * η ^ 2))) :
    ‖normalizedTrace ((R s - Mz) * B)‖ ≤
      2 * a + 2 * K * (2 * Real.sqrt (c * ((N : ℝ)⁻¹ *
        ∑ j, |(sourceMatrixElement Mz (col B j) (col B j)).im|))) *
        (1 + Real.log (zigHeight η c s 0 / η)) / (N * c * η) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hη := hP.η_pos
  have hc := hP.c_pos
  have hs := hP.s_nonneg
  set W := (N : ℝ)⁻¹ * ∑ j, |(sourceMatrixElement Mz (col B j) (col B j)).im| with hWdef
  have hW0 : 0 ≤ W := mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hsI : s ∈ Icc 0 s := ⟨hs, le_rfl⟩
  -- the two traces on `[0, s]`
  have hBB : ∀ r ∈ Icc 0 s,
      |(normalizedTrace (External.CEH.imaginaryPart (R r) * B * Bᴴ)).re| ≤ 2 * W := by
    intro r hr
    have h := abs_re_normalizedTrace_imaginaryPart_resolvent_mul (hP.herm r) (hP.im_ne hr) B
    rw [← hP.res r] at h
    rw [h, hWdef, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := (hmon r hr).2.2 j
    have hN0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    nlinarith
  have htr : ∀ r ∈ Icc 0 s, |(normalizedTrace (R r)).im| ≤ 2 * c := by
    intro r hr
    have h1 := hP.abs_im_trace_le r
    have h2 := (hmon r hr).2.1
    rw [hP.obsX_avgK] at h1
    linarith
  have hb : ∀ K' : Matrix (Fin N) (Fin N) ℂ, (K' = obsB B ∨ K' = (-Complex.I) • obsB B) →
      ∫ r in Ioc 0 s, brk K' R r ≤ 2 * W / ((N : ℝ) ^ 2 * c * η ^ 2) := by
    intro K' hK'
    refine le_trans (hP.bracket_integral_le (β := 2 * W / (N ^ 2 * η)) hsI fun r hr => ?_)
      ((aux_final_bracket hP (by positivity)).trans_eq (by field_simp))
    have hrI : r ∈ Icc 0 s := ⟨hr.1.le, hr.2.le⟩
    have hηr := hP.height_pos hrI
    have hle : η ≤ zigHeight η c s r := le_zigHeight hc.le hrI.2
    calc brk K' R r ≤ 1 / (N : ℝ) ^ 2 *
          (|(normalizedTrace (External.CEH.imaginaryPart (R r) * B * Bᴴ)).re| /
            zigHeight η c s r ^ 3) := hP.brk_obsB_le' B hK' hrI
      _ ≤ 1 / (N : ℝ) ^ 2 * (2 * W / zigHeight η c s r ^ 3) := by gcongr; exact hBB r hrI
      _ = 2 * W / (N ^ 2 * zigHeight η c s r) / zigHeight η c s r ^ 2 := by field_simp
      _ ≤ 2 * W / (N ^ 2 * η) / zigHeight η c s r ^ 2 := by gcongr
  have hmartlt := hmart.norm_lt hsI (hb _ (Or.inl rfl)) (hb _ (Or.inr rfl))
  have h := norm_target_le_const (N := (N : ℝ)) (η := η) (c := c) (s := s) (K := K)
    (Λ := 2 * Real.sqrt (c * W)) (KY := 2 * a) (Y := obsX (obsB B) Mz R)
    (MY := obsM (obsB B) Mz m R) (DY := obsD (obsB B) m R) (Xav := obsX (avgK N) Mz R)
    hNr hη hc hK (by positivity) hsI (hP.intervalIntegrable_obsD _) (obsX_eq _ _ _ _ s)
    (fun r hr => by rw [hP.obsX_avgK]; exact (hmon r hr).1)
    (fun r hr => by
      have hηr := hP.height_pos hr
      refine (hP.norm_obsD_obsB_le B hr).trans ?_
      rw [← sqrt_two_mul_sqrt_two_mul hc.le, ← Real.sqrt_mul (by positivity)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
        (mul_le_mul (htr r hr) (hBB r hr) (abs_nonneg _) (by positivity))) (norm_nonneg _))
        hηr.le) hmartlt.le
  rw [obsX_obsB] at h
  exact h

end FlowPath

end BlockBand.Native.CEH.LocalLaw
