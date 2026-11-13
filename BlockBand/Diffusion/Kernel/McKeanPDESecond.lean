module

public import BlockBand.Diffusion.Kernel.McKeanPDEJoint

/-!
# Second time derivatives of McKean's kernel

For `T > 0`, `c > 1` (Lebesgue measure on `(0,∞)` in `v`, `w = c + v²`):
* `mkFTT T c = ∫ ∂_T² G_T(w) dv`, `mkFTw T c = ∫ ∂_T∂_w G_T(w) dv`, with
  `∂_T mkFT = mkFTT` (`mk_hasDerivAt_fT_T`), `∂_c mkFT = mkFTw` (`mk_hasDerivAt_fT_c`),
  `∂_T mkF1 = mkFTw` (`mk_hasDerivAt_f1_T`);
* `mkA1 = A'`, `mkA2 = A''` (`mk_hasDerivAt_mkA1`);
* `mk_kT_eq`: `∂_T K = mkKT T c = A' F₀ + A F_T`;
  `mkKTT = A'' F₀ + 2 A' F_T + A F_TT`, `mkKTc = A' F₁ + A F_Tw`, and
  `∂_T mkKT = mkKTT` (`mk_hasDerivAt_kT_T`), `∂_c mkKT = mkKTc` (`mk_hasDerivAt_kT_c`),
  `∂_T mkK1 = mkKTc` (`mk_hasDerivAt_k1_T`);
* joint continuity on `(0,∞) × (1,∞)` of `F₀, F_T, F_TT, F_Tw` and of `mkKTT`, `mkKTc`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real

/-- `F_TT(T, c) = ∫_0^∞ ∂_T² G_T(c + v²) dv`. -/
def mkFTT (T c : ℝ) : ℝ := ∫ v in Ioi (0 : ℝ), mkGTT T (c + v ^ 2)

/-- `F_Tw(T, c) = ∫_0^∞ ∂_T ∂_w G_T(c + v²) dv`. -/
def mkFTw (T c : ℝ) : ℝ := ∫ v in Ioi (0 : ℝ), mkGTw T (c + v ^ 2)

theorem mk_gTT_measurable (T : ℝ) : Measurable (mkGTT T) := by
  have := mk_arcosh_measurable
  have := mk_mcKeanG_measurable T
  unfold mkGTT mkGT
  fun_prop

theorem mk_gTw_measurable (T : ℝ) : Measurable (mkGTw T) := by
  have := mk_arcosh_measurable
  have := mk_mcKeanG_measurable T
  have := mk_gw1_measurable T
  unfold mkGTw
  fun_prop

theorem mk_integrableOn_gw' {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    IntegrableOn (fun v => mkGTT T (c + v ^ 2)) (Ioi 0) ∧
      IntegrableOn (fun v => mkGTw T (c + v ^ 2)) (Ioi 0) := by
  have hb := fun v => mk_gw_le_inv hT le_rfl le_rfl hc le_rfl (c := c) v
  exact ⟨mk_integrableOn_of_le (mk_measurable_shift (mk_gTT_measurable T) c)
      fun v => (hb v).2.2.2.2.1,
    mk_integrableOn_of_le (mk_measurable_shift (mk_gTw_measurable T) c)
      fun v => (hb v).2.2.2.2.2⟩

theorem mk_hasDerivAt_fT_T {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (fun T' => mkFT T' c) (mkFTT T c) T := by
  have hs : Ioo (T / 2) (2 * T) ∈ 𝓝 T := Ioo_mem_nhds (by linarith) (by linarith)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall fun T' =>
      (mk_measurable_shift (mk_gT_measurable T') c).aestronglyMeasurable)
    (mk_integrableOn_gw hT hc).2.2.2
    (mk_measurable_shift (mk_gTT_measurable T) c).aestronglyMeasurable
    (bound := fun v => mkBd (T / 2) (2 * T) c * (1 + v ^ 2)⁻¹)
    (ae_of_all _ fun v T' hT' => by
      rw [Real.norm_eq_abs]
      exact (mk_gw_le_inv (by linarith) hT'.1.le hT'.2.le hc le_rfl v).2.2.2.2.1)
    (integrable_inv_one_add_sq.const_mul _).integrableOn
    (ae_of_all _ fun v T' hT' => ?_)).2
  exact mk_hasDerivAt_gT_T (by linarith [hT'.1] : (0 : ℝ) < T').ne'

theorem mk_hasDerivAt_fT_c {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (mkFT T) (mkFTw T c) c := by
  have hc₀ : 1 < (1 + c) / 2 := by linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (mk_ioo_mem_nhds hc)
    (Eventually.of_forall fun c' =>
      (mk_measurable_shift (mk_gT_measurable T) c').aestronglyMeasurable)
    (mk_integrableOn_gw hT hc).2.2.2
    (mk_measurable_shift (mk_gTw_measurable T) c).aestronglyMeasurable
    (bound := fun v => mkBd T T ((1 + c) / 2) * (1 + v ^ 2)⁻¹)
    (ae_of_all _ fun v c' hc' => by
      rw [Real.norm_eq_abs]
      exact (mk_gw_le_inv hT le_rfl le_rfl hc₀ hc'.1.le v).2.2.2.2.2)
    (integrable_inv_one_add_sq.const_mul _).integrableOn
    (ae_of_all _ fun v c' hc' => ?_)).2
  have hw : 1 < c' + v ^ 2 := by nlinarith [hc'.1, sq_nonneg v]
  exact HasDerivAt.comp_add_const c' (v ^ 2) (mk_hasDerivAt_gT_w hT.ne' hw)

theorem mk_hasDerivAt_f1_T {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (fun T' => mkF1 T' c) (mkFTw T c) T := by
  have hs : Ioo (T / 2) (2 * T) ∈ 𝓝 T := Ioo_mem_nhds (by linarith) (by linarith)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall fun T' =>
      (mk_measurable_shift (mk_gw1_measurable T') c).aestronglyMeasurable)
    (mk_integrableOn_gw hT hc).2.1
    (mk_measurable_shift (mk_gTw_measurable T) c).aestronglyMeasurable
    (bound := fun v => mkBd (T / 2) (2 * T) c * (1 + v ^ 2)⁻¹)
    (ae_of_all _ fun v T' hT' => by
      rw [Real.norm_eq_abs]
      exact (mk_gw_le_inv (by linarith) hT'.1.le hT'.2.le hc le_rfl v).2.2.2.2.2)
    (integrable_inv_one_add_sq.const_mul _).integrableOn
    (ae_of_all _ fun v T' hT' => ?_)).2
  have hw : 1 < c + v ^ 2 := by nlinarith [sq_nonneg v]
  exact mk_hasDerivAt_gw1_T (by linarith [hT'.1] : (0 : ℝ) < T').ne' hw

/-!
### Joint continuity of the integrands and the integrals
-/

theorem mk_mcKeanG_continuousAt {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    ContinuousAt (fun p : ℝ × ℝ => mkMcKeanG p.1 p.2) (T, w) := by
  have hS := mk_arcosh_snd_continuousAt (T := T) hw
  have hσ := mk_sdivSinh_continuous
  unfold mkMcKeanG
  fun_prop (disch := simp [hT])

theorem mk_gT_continuousAt {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    ContinuousAt (fun p : ℝ × ℝ => mkGT p.1 p.2) (T, w) := by
  have hS := mk_arcosh_snd_continuousAt (T := T) hw
  have hg := mk_mcKeanG_continuousAt hT hw
  unfold mkGT
  fun_prop (disch := simp [hT])

theorem mk_gTT_continuousAt {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    ContinuousAt (fun p : ℝ × ℝ => mkGTT p.1 p.2) (T, w) := by
  have hS := mk_arcosh_snd_continuousAt (T := T) hw
  have hg := mk_mcKeanG_continuousAt hT hw
  have hgT := mk_gT_continuousAt hT hw
  unfold mkGTT
  fun_prop (disch := simp [hT])

theorem mk_gTw_continuousAt {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    ContinuousAt (fun p : ℝ × ℝ => mkGTw p.1 p.2) (T, w) := by
  have hS := mk_arcosh_snd_continuousAt (T := T) hw
  have hg := mk_mcKeanG_continuousAt hT hw
  have hg1 := mk_gw1_continuousAt hT hw
  have hR := (mk_sqrt_pos hw).ne'
  unfold mkGTw
  fun_prop (disch := simp [hT, hR])

theorem mk_f0_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkF0 p.1 p.2) (T, c) := by
  have hc' : 1 < (1 + c) / 2 := by linarith
  exact mk_integral_shift_continuousAt (g := mkMcKeanG) hT hc mk_mcKeanG_measurable
    (fun T' c' v h1 h2 h3 => (mk_gw_le_inv (by linarith) h1 h2 hc' h3 v).1)
    (fun v => mk_mcKeanG_continuousAt hT.ne' (by nlinarith [sq_nonneg v]))

theorem mk_fT_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkFT p.1 p.2) (T, c) := by
  have hc' : 1 < (1 + c) / 2 := by linarith
  exact mk_integral_shift_continuousAt (g := mkGT) hT hc mk_gT_measurable
    (fun T' c' v h1 h2 h3 => (mk_gw_le_inv (by linarith) h1 h2 hc' h3 v).2.2.2.1)
    (fun v => mk_gT_continuousAt hT.ne' (by nlinarith [sq_nonneg v]))

theorem mk_fTT_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkFTT p.1 p.2) (T, c) := by
  have hc' : 1 < (1 + c) / 2 := by linarith
  exact mk_integral_shift_continuousAt (g := mkGTT) hT hc mk_gTT_measurable
    (fun T' c' v h1 h2 h3 => (mk_gw_le_inv (by linarith) h1 h2 hc' h3 v).2.2.2.2.1)
    (fun v => mk_gTT_continuousAt hT.ne' (by nlinarith [sq_nonneg v]))

theorem mk_fTw_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkFTw p.1 p.2) (T, c) := by
  have hc' : 1 < (1 + c) / 2 := by linarith
  exact mk_integral_shift_continuousAt (g := mkGTw) hT hc mk_gTw_measurable
    (fun T' c' v h1 h2 h3 => (mk_gw_le_inv (by linarith) h1 h2 hc' h3 v).2.2.2.2.2)
    (fun v => mk_gTw_continuousAt hT.ne' (by nlinarith [sq_nonneg v]))

/-!
### Derivatives of `A_T`
-/

/-- The derivative `A_T'` of `A_T` in `T`. -/
def mkA1 (T : ℝ) : ℝ := mkA T * (-1 / 4 - 3 / (2 * T))

/-- The second derivative `A_T''` of `A_T` in `T`. -/
def mkA2 (T : ℝ) : ℝ := mkA1 T * (-1 / 4 - 3 / (2 * T)) + mkA T * (3 / (2 * T ^ 2))

theorem mk_hasDerivAt_mkA1 {T : ℝ} (hT : 0 < T) : HasDerivAt mkA1 (mkA2 T) T := by
  have h2 : HasDerivAt (fun T' : ℝ => -1 / 4 - 3 / (2 * T')) (3 / (2 * T ^ 2)) T := by
    have := (((hasDerivAt_id T).const_mul 2).inv (by simp [hT.ne'])).const_mul 3
    convert this.const_sub (-1 / 4) using 1
    · funext T'; simp [div_eq_mul_inv]
    · simp only [id]; field_simp
  have h := (mk_hasDerivAt_mkA hT).mul h2
  unfold mkA1
  convert h using 1
  unfold mkA2 mkA1; ring

theorem mk_mkA1_continuousAt {T : ℝ} (hT : 0 < T) : ContinuousAt mkA1 T :=
  (mk_hasDerivAt_mkA1 hT).continuousAt

theorem mk_mkA2_continuousAt {T : ℝ} (hT : 0 < T) : ContinuousAt mkA2 T := by
  have h0 := mk_mkA_continuousAt hT
  have h1 := mk_mkA1_continuousAt hT
  unfold mkA2
  fun_prop (disch := simp [hT.ne'])

/-!
### `∂_T² K` and `∂_c ∂_T K = ∂_T ∂_c K`
-/

/-- `∂_T² K_T(c) = A'' F₀ + 2A' F_T + A F_TT` (`c > 1`). -/
def mkKTT (T c : ℝ) : ℝ := mkA2 T * mkF0 T c + 2 * mkA1 T * mkFT T c + mkA T * mkFTT T c

/-- `∂_c ∂_T K_T(c) = ∂_T ∂_c K_T(c) = A' F₁ + A F_Tw` (`c > 1`). -/
def mkKTc (T c : ℝ) : ℝ := mkA1 T * mkF1 T c + mkA T * mkFTw T c

theorem mk_kT_eq {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    mkKT T c = mkA1 T * mkF0 T c + mkA T * mkFT T c := by
  unfold mkKT mkK1 mkK2 mkA1
  rw [mk_fT_eq hT hc]
  ring

theorem mk_hasDerivAt_kT_T {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (fun T' => mkKT T' c) (mkKTT T c) T := by
  have heq : (fun T' => mkKT T' c) =ᶠ[𝓝 T]
      fun T' => mkA1 T' * mkF0 T' c + mkA T' * mkFT T' c := by
    filter_upwards [lt_mem_nhds hT] with T' hT'
    exact mk_kT_eq hT' hc
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have h := ((mk_hasDerivAt_mkA1 hT).mul (mk_hasDerivAt_f0_T hT hc)).add
    ((mk_hasDerivAt_mkA hT).mul (mk_hasDerivAt_fT_T hT hc))
  convert h using 1
  unfold mkKTT mkA1; ring

theorem mk_hasDerivAt_kT_c {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (mkKT T) (mkKTc T c) c := by
  have heq : mkKT T =ᶠ[𝓝 c] fun c' => mkA1 T * mkF0 T c' + mkA T * mkFT T c' := by
    filter_upwards [lt_mem_nhds hc] with c' hc'
    exact mk_kT_eq hT hc'
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  exact (((mk_hasDerivAt_f0 hT hc).const_mul (mkA1 T)).add
    ((mk_hasDerivAt_fT_c hT hc).const_mul (mkA T)))

theorem mk_hasDerivAt_k1_T {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (fun T' => mkK1 T' c) (mkKTc T c) T := by
  have h := (mk_hasDerivAt_mkA hT).mul (mk_hasDerivAt_f1_T hT hc)
  unfold mkK1
  convert h using 1
  unfold mkKTc mkA1; ring

theorem mk_kTT_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkKTT p.1 p.2) (T, c) := by
  have hA := (mk_mkA_continuousAt hT).comp (f := Prod.fst) (x := (T, c)) continuousAt_fst
  have hA1 := (mk_mkA1_continuousAt hT).comp (f := Prod.fst) (x := (T, c)) continuousAt_fst
  have hA2 := (mk_mkA2_continuousAt hT).comp (f := Prod.fst) (x := (T, c)) continuousAt_fst
  have h0 := mk_f0_continuousAt hT hc
  have h1 := mk_fT_continuousAt hT hc
  have h2 := mk_fTT_continuousAt hT hc
  unfold mkKTT
  exact ((hA2.mul h0).add ((continuousAt_const.mul hA1).mul h1)).add (hA.mul h2)

theorem mk_kTc_continuousAt {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    ContinuousAt (fun p : ℝ × ℝ => mkKTc p.1 p.2) (T, c) := by
  have hA := (mk_mkA_continuousAt hT).comp (f := Prod.fst) (x := (T, c)) continuousAt_fst
  have hA1 := (mk_mkA1_continuousAt hT).comp (f := Prod.fst) (x := (T, c)) continuousAt_fst
  have h1 := mk_f1_continuousAt hT hc
  have h2 := mk_fTw_continuousAt hT hc
  unfold mkKTc
  exact (hA1.mul h1).add (hA.mul h2)

end BlockBand.Diffusion
