module

public import BlockBand.Diffusion.Kernel.McKeanPDERadial

/-!
# Joint continuity of the derivatives of McKean's kernel; strict positivity of `pX`

We prove joint continuity of the first derivatives of McKean's kernel off the diagonal and strict
positivity of the radial factor `pX`.

* `mk_k1_continuousAt`, `mk_k2_continuousAt`, `mk_kT_continuousAt`: the maps
  `(T, c) ↦ ∂_c K_T(c) = mkK1 T c`, `(T, c) ↦ ∂_c² K_T(c) = mkK2 T c` and
  `(T, c) ↦ ∂_T K_T(c) = mkKT T c = (c² - 1) mkK2 T c + 2 c mkK1 T c` are jointly continuous at
  every point of `(0, ∞) × (1, ∞)` (dominated convergence with the majorant of `mk_gw_le_inv`).
* `mk_kernelX_pos`: `0 < mkKernelX D0 t x x'` for `D₀ > 0`, `t > 0`, `x' ≥ 0` and every
  real `x` (from `mk_hypKernel_pos` and continuity of the angular integrand).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real

/-- `∂_T K_T(c) = (c² - 1) ∂_c² K_T(c) + 2 c ∂_c K_T(c)` (`c > 1`). -/
def mkKT (T c : ℝ) : ℝ := (c ^ 2 - 1) * mkK2 T c + 2 * c * mkK1 T c

theorem mk_arcosh_snd_continuousAt {T w : ℝ} (hw : 1 < w) :
    ContinuousAt (fun p : ℝ × ℝ => Real.arcosh p.2) (T, w) :=
  ((Real.differentiableAt_arcosh (show w ∈ Ioi 1 from hw)).continuousAt).comp
    (f := Prod.snd) (x := (T, w)) continuousAt_snd

theorem mk_gw1_continuousAt {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    ContinuousAt (fun p : ℝ × ℝ => mkGw1 p.1 p.2) (T, w) := by
  have hS := mk_arcosh_snd_continuousAt (T := T) hw
  have hR := (mk_sqrt_pos hw).ne'
  unfold mkGw1 mkN1
  fun_prop (disch := simp [hT, hR])

theorem mk_gw2_continuousAt {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    ContinuousAt (fun p : ℝ × ℝ => mkGw2 p.1 p.2) (T, w) := by
  have hS := mk_arcosh_snd_continuousAt (T := T) hw
  have hR := (mk_sqrt_pos hw).ne'
  unfold mkGw2 mkN2 mkN1 mkN1d
  fun_prop (disch := simp [hT, hR])

theorem mk_shift_continuousAt {f : ℝ × ℝ → ℝ} {T c v : ℝ}
    (hf : ContinuousAt f (T, c + v ^ 2)) :
    ContinuousAt (fun p : ℝ × ℝ => f (p.1, p.2 + v ^ 2)) (T, c) :=
  hf.comp (f := fun p : ℝ × ℝ => (p.1, p.2 + v ^ 2)) (x := (T, c)) (by fun_prop)

theorem mk_nhds_box {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    Ioo (T / 2) (2 * T) ×ˢ Ioi ((1 + c) / 2) ∈ 𝓝 (T, c) :=
  prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) (Ioi_mem_nhds (by linarith))

/-- Joint continuity of a `v`-integral `∫_0^∞ g(T, c + v²) dv` from the majorant. -/
theorem mk_integral_shift_continuousAt {g : ℝ → ℝ → ℝ} {T₀ c₀ : ℝ} (hT₀ : 0 < T₀)
    (hc₀ : 1 < c₀) (hm : ∀ T, Measurable (g T))
    (hb : ∀ T c v, T₀ / 2 ≤ T → T ≤ 2 * T₀ → (1 + c₀) / 2 ≤ c →
      |g T (c + v ^ 2)| ≤ mkBd (T₀ / 2) (2 * T₀) ((1 + c₀) / 2) * (1 + v ^ 2)⁻¹)
    (hcont : ∀ v, ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (T₀, c₀ + v ^ 2)) :
    ContinuousAt (fun p : ℝ × ℝ => ∫ v in Ioi (0 : ℝ), g p.1 (p.2 + v ^ 2)) (T₀, c₀) := by
  refine continuousAt_of_dominated
    (bound := fun v => mkBd (T₀ / 2) (2 * T₀) ((1 + c₀) / 2) * (1 + v ^ 2)⁻¹)
    (Eventually.of_forall fun p => (mk_measurable_shift (hm p.1) p.2).aestronglyMeasurable)
    ?_ (integrable_inv_one_add_sq.const_mul _).integrableOn
    (ae_of_all _ fun v => mk_shift_continuousAt (f := fun p : ℝ × ℝ => g p.1 p.2) (hcont v))
  filter_upwards [mk_nhds_box hT₀ hc₀] with p hp
  refine ae_of_all _ fun v => ?_
  rw [Real.norm_eq_abs]
  exact hb p.1 p.2 v hp.1.1.le hp.1.2.le (le_of_lt hp.2)

theorem mk_f1_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkF1 p.1 p.2) (T, c) := by
  have hc' : 1 < (1 + c) / 2 := by linarith
  exact mk_integral_shift_continuousAt (g := mkGw1) hT hc mk_gw1_measurable
    (fun T' c' v h1 h2 h3 => (mk_gw_le_inv (by linarith) h1 h2 hc' h3 v).2.1)
    (fun v => mk_gw1_continuousAt hT.ne' (by nlinarith [sq_nonneg v]))

theorem mk_f2_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkF2 p.1 p.2) (T, c) := by
  have hc' : 1 < (1 + c) / 2 := by linarith
  exact mk_integral_shift_continuousAt (g := mkGw2) hT hc mk_gw2_measurable
    (fun T' c' v h1 h2 h3 => (mk_gw_le_inv (by linarith) h1 h2 hc' h3 v).2.2.1)
    (fun v => mk_gw2_continuousAt hT.ne' (by nlinarith [sq_nonneg v]))

theorem mk_mkA_continuousAt {T : ℝ} (hT : 0 < T) : ContinuousAt mkA T :=
  mk_mkA_continuousOn.continuousAt (Ioi_mem_nhds hT)

/-- Joint continuity of `∂_c K_T(c)` on `(0,∞) × (1,∞)`. -/
theorem mk_k1_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkK1 p.1 p.2) (T, c) :=
  ((mk_mkA_continuousAt hT).comp (f := Prod.fst) (x := (T, c)) continuousAt_fst).mul
    (mk_f1_continuousAt hT hc)

/-- Joint continuity of `∂_c² K_T(c)` on `(0,∞) × (1,∞)`. -/
theorem mk_k2_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkK2 p.1 p.2) (T, c) :=
  ((mk_mkA_continuousAt hT).comp (f := Prod.fst) (x := (T, c)) continuousAt_fst).mul
    (mk_f2_continuousAt hT hc)

/-- Joint continuity of `∂_T K_T(c)` on `(0,∞) × (1,∞)`. -/
theorem mk_kT_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkKT p.1 p.2) (T, c) := by
  unfold mkKT
  have h1 := mk_k1_continuousAt hT hc
  have h2 := mk_k2_continuousAt hT hc
  fun_prop

theorem mk_hasDerivAt_hypKernel_T' {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (fun T' => mkHypKernel T' c) (mkKT T c) T :=
  mk_hasDerivAt_hypKernel_T hT hc

/-!
### Strict positivity
-/

/-- `0 < mkHypRadial T x x'` for `T > 0` and all real `x, x'`. -/
theorem mk_hypRadial_pos {T : ℝ} (hT : 0 < T) (x x' : ℝ) : 0 < mkHypRadial T x x' := by
  unfold mkHypRadial
  have hc := mk_hypKernel_comp_continuous hT x x'
  have := intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable 0 (2 * π))
    (fun θ _ => mk_hypKernel_pos hT _) (by positivity)
  positivity

/-- **Strict positivity of `pX`.** For `D₀ > 0`, `t > 0`, `x' ≥ 0` and any `x ∈ ℝ`:
`0 < mkKernelX D0 t x x'`. -/
theorem mk_kernelX_pos {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (x : ℝ) {x' : ℝ} (hx' : 0 ≤ x') :
    0 < mkKernelX D0 t x x' := by
  rw [mk_kernelX_eq ht hx']
  exact mk_hypRadial_pos (by positivity) x x'

end BlockBand.Diffusion
