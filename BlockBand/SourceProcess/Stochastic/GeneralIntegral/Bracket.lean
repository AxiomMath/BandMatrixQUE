module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.BracketElem
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.BracketBounds
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Continuous
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The bracket of the continuous stochastic integral

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, `h : IsL2Integrator Q 𝓖 N α`,
horizon `T`, `H ∈ PredL2 𝓖 ν_T` with its canonical representative `(H : ℝ × Ω → ℝ)`.

`bracketProc h T H t ω = ∫_{(0, t ∧ T]} H(r,ω)² α_r(ω) dr`.

**Main result** `bracket_martingale`: `(∫_0^t H dN)² - ∫_0^{t∧T} H² α ds` has a
`𝓖`-martingale modification (`Z = contIntegral h T H`).

Proof: the elementary identity `setIntegral_elemProc_sq` along the fast approximations,
passed to the limit in `L¹(Q)`: `I_t(x_n)² → Z_t²` (`L²` rate of `contIntegral`, Hölder) and
`∫_0^t (elemFun x_n)² α → ∫_0^t H² α` (`lintegral_enorm_bracketTerm_sub_le`, Hölder in
`L²(ν_T)`); a.e. adaptedness of the limit bracket from an a.e. convergent subsequence of the
a.e.-adapted elementary brackets (`aesm_brk2`).
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {N α : ℝ≥0 → Ω → ℝ}

namespace IsL2Integrator

variable (h : IsL2Integrator Q 𝓖 N α) (T : ℝ≥0) (H : PredL2 𝓖 (bracketMeasure Q α T))

/-- The bracket process `∫_{(0, t ∧ T]} H² α ds`. -/
def bracketProc (t : ℝ≥0) (ω : Ω) : ℝ :=
  bracketTerm α ((H : Lp ℝ 2 (bracketMeasure Q α T)) : ℝ × Ω → ℝ) (min t T) ω

/-- Elementary brackets of the fast approximations. -/
def approxBracket (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  bracketTerm α (elemFun (h.approx T H n)) (min t T) ω

theorem eLpNorm_elemFun_sub_le (n : ℕ) :
    eLpNorm (fun p => elemFun (h.approx T H n) p - (H : Lp ℝ 2 (bracketMeasure Q α T)) p) 2
      (bracketMeasure Q α T) ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
  have hae : (fun p => elemFun (h.approx T H n) p - (H : Lp ℝ 2 (bracketMeasure Q α T)) p)
      =ᵐ[bracketMeasure Q α T] ⇑(((h.integrandLin T (h.approx T H n) - H :
        PredL2 𝓖 (bracketMeasure Q α T))) : Lp ℝ 2 (bracketMeasure Q α T)) := by
    filter_upwards [integrandLin_ae h (h.approx T H n),
      Lp.coeFn_sub ((h.integrandLin T (h.approx T H n) : PredL2 𝓖 (bracketMeasure Q α T)) :
        Lp ℝ 2 (bracketMeasure Q α T)) (H : Lp ℝ 2 (bracketMeasure Q α T))] with p h1 h2
    change _ = (((h.integrandLin T (h.approx T H n) : PredL2 𝓖 (bracketMeasure Q α T)) :
      Lp ℝ 2 (bracketMeasure Q α T)) - (H : Lp ℝ 2 (bracketMeasure Q α T))) p
    rw [h2, Pi.sub_apply, h1]
  rw [eLpNorm_congr_ae hae, eLpNorm_Lp_eq]
  exact ENNReal.ofReal_le_ofReal (h.approx_spec T H n).le

/-- The constant `K = 1 + 2 ‖H‖` bounding `‖elemFun x_n + H‖_{L²(ν_T)}`. -/
def bracketConst : ℝ≥0∞ := ENNReal.ofReal 1 + (ENNReal.ofReal ‖H‖ + ENNReal.ofReal ‖H‖)

theorem eLpNorm_elemFun_add_le (n : ℕ) :
    eLpNorm (fun p => elemFun (h.approx T H n) p + (H : Lp ℝ 2 (bracketMeasure Q α T)) p) 2
      (bracketMeasure Q α T) ≤ bracketConst T H := by
  set g := ((H : Lp ℝ 2 (bracketMeasure Q α T)) : ℝ × Ω → ℝ)
  have hsplit : (fun p => elemFun (h.approx T H n) p + g p) =
      (fun p => elemFun (h.approx T H n) p - g p) + (g + g) := by
    funext p; simp only [Pi.add_apply]; ring
  rw [hsplit]
  refine (eLpNorm_add_le one_le_two).trans (add_le_add ?_ ?_)
  · refine (h.eLpNorm_elemFun_sub_le T H n).trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_one₀ (by norm_num) (by norm_num)
  · refine (eLpNorm_add_le one_le_two).trans (le_of_eq ?_)
    rw [eLpNorm_Lp_eq]; rfl

omit [IsFiniteMeasure Q] in
theorem bracketConst_ne_top : bracketConst T H ≠ ∞ := by
  simp [bracketConst]

omit [IsFiniteMeasure Q] in
theorem lintegral_sq_ne_top (f : Lp ℝ 2 (bracketMeasure Q α T)) :
    ∫⁻ p, ‖f p‖ₑ ^ 2 ∂bracketMeasure Q α T ≠ ∞ := by
  rw [SDE.lintegral_enorm_sq_eq_eLpNorm_sq (Lp.aestronglyMeasurable f)]
  exact ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)

include h in
theorem lintegral_sq_elemFun_ne_top (x : Rect 𝓖 T →₀ ℝ) :
    ∫⁻ p, ‖elemFun x p‖ₑ ^ 2 ∂bracketMeasure Q α T ≠ ∞ := by
  have := h.isFiniteMeasure_bracketMeasure T
  have hae : (fun p => ‖elemFun x p‖ₑ ^ 2) =ᵐ[bracketMeasure Q α T]
      fun p => ‖((h.integrandLin T x : PredL2 𝓖 (bracketMeasure Q α T)) :
        Lp ℝ 2 (bracketMeasure Q α T)) p‖ₑ ^ 2 :=
    (integrandLin_ae h x).mono fun p hp => by simp only [hp]
  rw [lintegral_congr_ae hae]
  exact lintegral_sq_ne_top T _

/-- **`L¹` convergence of the brackets.** -/
theorem eLpNorm_approxBracket_sub_le (n : ℕ) (t : ℝ≥0) :
    eLpNorm (h.approxBracket T H n t - bracketProc T H t) 1 Q ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ n) * bracketConst T H := by
  change eLpNorm (bracketTerm α (elemFun (h.approx T H n)) (min t T) -
    bracketTerm α ((H : Lp ℝ 2 (bracketMeasure Q α T)) : ℝ × Ω → ℝ) (min t T)) 1 Q ≤ _
  rw [eLpNorm_one_eq_lintegral_enorm ((stronglyMeasurable_bracketTerm h.alpha_measurable
    (measurable_elemFun _).stronglyMeasurable _).sub (stronglyMeasurable_bracketTerm
      h.alpha_measurable (Lp.stronglyMeasurable _) _)).aestronglyMeasurable]
  refine (lintegral_enorm_bracketTerm_sub_le h.alpha_measurable h.alpha_nonneg
    (measurable_elemFun _).stronglyMeasurable (Lp.stronglyMeasurable _)
    (h.lintegral_sq_elemFun_ne_top T _) (lintegral_sq_ne_top T _) (min_le_right t T)).trans ?_
  have hm2 : AEStronglyMeasurable (fun p => elemFun (h.approx T H n) p ^ 2 -
      ((H : Lp ℝ 2 (bracketMeasure Q α T)) : ℝ × Ω → ℝ) p ^ 2) (bracketMeasure Q α T) :=
    (((measurable_elemFun _).pow_const 2).sub
      ((Lp.stronglyMeasurable _).measurable.pow_const 2)).aestronglyMeasurable
  rw [← eLpNorm_one_eq_lintegral_enorm hm2]
  refine (eLpNorm_sq_sub_sq_le (measurable_elemFun _).aestronglyMeasurable
    (Lp.aestronglyMeasurable _)).trans ?_
  exact mul_le_mul' (h.eLpNorm_elemFun_sub_le T H n) (h.eLpNorm_elemFun_add_le T H n)

theorem tendsto_eLpNorm_approxBracket (t : ℝ≥0) :
    Tendsto (fun n => eLpNorm (h.approxBracket T H n t - bracketProc T H t) 1 Q) atTop
      (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
    (h.eLpNorm_approxBracket_sub_le T H · t)
  have ht := ENNReal.Tendsto.mul_const (IsL2Integrator.tendsto_ofReal_geom 1)
    (Or.inr (bracketConst_ne_top T H))
  simp only [one_mul, zero_mul] at ht
  exact ht

/-- **`L¹` convergence of the squares.** -/
theorem tendsto_eLpNorm_sq (t : ℝ≥0) :
    Tendsto (fun n => eLpNorm (fun ω => h.approxProc T H n t ω ^ 2 -
      h.contIntegral T H t ω ^ 2) 1 Q) atTop (𝓝 0) := by
  set K := ENNReal.ofReal 2 + (eLpNorm (h.contIntegral T H t) 2 Q +
    eLpNorm (h.contIntegral T H t) 2 Q)
  have hK : K ≠ ∞ := by
    have := (h.memLp_contIntegral T H t)
    simp only [K, ne_eq, ENNReal.add_eq_top, ENNReal.ofReal_ne_top, false_or, or_self]
    exact this.ne
  have hb : ∀ n, eLpNorm (fun ω => h.approxProc T H n t ω ^ 2 - h.contIntegral T H t ω ^ 2) 1 Q
      ≤ ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ n) * K := by
    intro n
    refine (eLpNorm_sq_sub_sq_le (h.memLp_approxProc T H n t).aestronglyMeasurable
      (h.memLp_contIntegral T H t).aestronglyMeasurable).trans (mul_le_mul'
        (h.eLpNorm_approxProc_sub_contIntegral_le T H n t) ?_)
    have hsplit : (fun ω => h.approxProc T H n t ω + h.contIntegral T H t ω) =
        (fun ω => h.approxProc T H n t ω - h.contIntegral T H t ω) +
          (h.contIntegral T H t + h.contIntegral T H t) := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [hsplit]
    refine (eLpNorm_add_le one_le_two).trans (add_le_add ?_ (eLpNorm_add_le one_le_two))
    refine (h.eLpNorm_approxProc_sub_contIntegral_le T H n t).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [pow_le_one₀ (n := n) (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hb
  simpa using ENNReal.Tendsto.mul_const (IsL2Integrator.tendsto_ofReal_geom 2) (Or.inr hK)

include h in
omit [IsFiniteMeasure Q] in
theorem memLp_bracketTerm [SFinite Q] {f : ℝ × Ω → ℝ} (hf : StronglyMeasurable f)
    (hfin : ∫⁻ p, ‖f p‖ₑ ^ 2 ∂bracketMeasure Q α T ≠ ∞) {t : ℝ≥0} (htT : t ≤ T) :
    MemLp (bracketTerm α f t) 1 Q := by
  change eLpNorm _ 1 Q < ∞
  rw [eLpNorm_one_eq_lintegral_enorm
    (stronglyMeasurable_bracketTerm h.alpha_measurable hf t).aestronglyMeasurable]
  exact (lintegral_enorm_bracketTerm_le h.alpha_measurable h.alpha_nonneg hf htT).trans_lt
    (lt_top_iff_ne_top.2 hfin)

include h in
theorem memLp_bracketProc (t : ℝ≥0) : MemLp (bracketProc T H t) 1 Q :=
  h.memLp_bracketTerm T (Lp.stronglyMeasurable _) (lintegral_sq_ne_top T _) (min_le_right t T)

include h in
theorem memLp_approxBracket (n : ℕ) (t : ℝ≥0) : MemLp (h.approxBracket T H n t) 1 Q :=
  h.memLp_bracketTerm T (measurable_elemFun _).stronglyMeasurable
    (h.lintegral_sq_elemFun_ne_top T _) (min_le_right t T)

include h in
theorem aestronglyMeasurable_bracketProc (t : ℝ≥0) :
    AEStronglyMeasurable[𝓖 t] (bracketProc T H t) Q := by
  have hm : ∀ n, AEStronglyMeasurable (h.approxBracket T H n t) Q := fun n =>
    (stronglyMeasurable_bracketTerm h.alpha_measurable
      (measurable_elemFun _).stronglyMeasurable _).aestronglyMeasurable
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (h.tendsto_eLpNorm_approxBracket T H t)).exists_seq_tendsto_ae
  refine Semimartingale.aestronglyMeasurable_of_tendsto_ae_sub
    (f := fun i => h.approxBracket T H (ns i) t) (fun i => ?_) hns
  have he : h.approxBracket T H (ns i) t = brk2 α (h.approx T H (ns i)) (h.approx T H (ns i))
      (min t T) := bracketTerm_elemFun _ _
  rw [he]
  exact (h.aesm_brk2 _ _ _).mono (𝓖.mono (min_le_left t T))

omit [IsFiniteMeasure Q] in
theorem setIntegral_tendsto_of_eLpNorm {F : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hF : ∀ n, Integrable (F n) Q) (hlim : Tendsto (fun n => eLpNorm (F n - f) 1 Q) atTop (𝓝 0))
    (B : Set Ω) :
    Tendsto (fun n => ∫ ω in B, F n ω ∂Q) atTop (𝓝 (∫ ω in B, f ω ∂Q)) :=
  tendsto_setIntegral_of_L1' f (Eventually.of_forall hF) hlim B

/-- The set-integral martingale identity for `Z² - ∫ H² α`. -/
theorem setIntegral_bracket_eq {u v : ℝ≥0} (huv : u ≤ v) {B : Set Ω}
    (hB : MeasurableSet[𝓖 u] B) :
    ∫ ω in B, (h.contIntegral T H v ω ^ 2 - bracketProc T H v ω) ∂Q =
      ∫ ω in B, (h.contIntegral T H u ω ^ 2 - bracketProc T H u ω) ∂Q := by
  have hBm : MeasurableSet B := 𝓖.le u B hB
  by_cases huT : T ≤ u
  · have hZ : h.contIntegral T H v = h.contIntegral T H u := by
      rw [h.contIntegral_of_le T H (huT.trans huv), h.contIntegral_of_le T H huT]
    have hV : bracketProc T H v = bracketProc T H u := by
      funext ω; simp only [bracketProc, min_eq_right (huT.trans huv), min_eq_right huT]
    rw [hZ, hV]
  have huT' : u ≤ T := (not_le.1 huT).le
  set v' := min v T
  have hv' : u ≤ v' := le_min huv huT'
  have hZv : h.contIntegral T H v = h.contIntegral T H v' := by
    rcases le_total v T with hv | hv
    · simp [v', min_eq_left hv]
    · rw [h.contIntegral_of_le T H hv, show v' = T from min_eq_right hv]
  have hu' : min u T = u := min_eq_left huT'
  have hv'' : min v' T = v' := min_eq_left (min_le_right _ _)
  have hVv : bracketProc T H v = bracketProc T H v' := by
    funext ω; simp only [bracketProc, hv'', v']
  -- elementary identities
  have helem : ∀ n, (∫ ω in B, h.approxProc T H n v' ω ^ 2 ∂Q) -
      ∫ ω in B, h.approxProc T H n u ω ^ 2 ∂Q =
      (∫ ω in B, h.approxBracket T H n v' ω ∂Q) - ∫ ω in B, h.approxBracket T H n u ω ∂Q := by
    intro n
    have e := h.setIntegral_elemProc_sq (h.approx T H n) hv' (min_le_right v T) hB
    have i1 : ∀ t, Integrable (fun ω => h.approxProc T H n t ω ^ 2) Q := fun t =>
      (h.memLp_approxProc T H n t).integrable_sq
    have i2 : ∀ t, Integrable (h.approxBracket T H n t) Q := fun t =>
      memLp_one_iff_integrable.1 (h.memLp_approxBracket T H n t)
    have ev' : h.approxBracket T H n v' = bracketTerm α (elemFun (h.approx T H n)) v' := by
      funext ω; simp only [approxBracket, hv'']
    have eu : h.approxBracket T H n u = bracketTerm α (elemFun (h.approx T H n)) u := by
      funext ω; simp only [approxBracket, hu']
    rw [← integral_sub (i1 v').integrableOn (i1 u).integrableOn,
      ← integral_sub (i2 v').integrableOn (i2 u).integrableOn, ev', eu]
    exact e
  have hZ2 : ∀ t, Tendsto (fun n => ∫ ω in B, h.approxProc T H n t ω ^ 2 ∂Q) atTop
      (𝓝 (∫ ω in B, h.contIntegral T H t ω ^ 2 ∂Q)) := fun t =>
    setIntegral_tendsto_of_eLpNorm (fun n => (h.memLp_approxProc T H n t).integrable_sq)
      (h.tendsto_eLpNorm_sq T H t) B
  have hV : ∀ t, Tendsto (fun n => ∫ ω in B, h.approxBracket T H n t ω ∂Q) atTop
      (𝓝 (∫ ω in B, bracketProc T H t ω ∂Q)) := fun t =>
    setIntegral_tendsto_of_eLpNorm
      (fun n => memLp_one_iff_integrable.1 (h.memLp_approxBracket T H n t))
      (h.tendsto_eLpNorm_approxBracket T H t) B
  have hlim := tendsto_nhds_unique (((hZ2 v').sub (hZ2 u)).congr helem) ((hV v').sub (hV u))
  have iZ : ∀ t, Integrable (fun ω => h.contIntegral T H t ω ^ 2) Q := fun t =>
    (h.memLp_contIntegral T H t).integrable_sq
  have iV : ∀ t, Integrable (bracketProc T H t) Q := fun t =>
    memLp_one_iff_integrable.1 (h.memLp_bracketProc T H t)
  rw [integral_sub (iZ v).integrableOn (iV v).integrableOn,
    integral_sub (iZ u).integrableOn (iV u).integrableOn, hZv, hVv]
  linarith

/-- **Bracket identity**: `(∫_0^t H dN)² - ∫_0^{t∧T} H² α ds` has a `𝓖`-martingale
modification. -/
theorem bracket_martingale :
    ∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧
      ∀ t, Y t =ᵐ[Q] fun ω => h.contIntegral T H t ω ^ 2 - bracketProc T H t ω :=
  exists_martingale_modification'
    (fun t => (h.memLp_contIntegral T H t).integrable_sq.sub
      (memLp_one_iff_integrable.1 (h.memLp_bracketProc T H t)))
    (fun t => ((h.aestronglyMeasurable_contIntegral T H t).pow 2).sub
      (h.aestronglyMeasurable_bracketProc T H t))
    (fun _ _ huv _ hB => h.setIntegral_bracket_eq T H huv hB)

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
