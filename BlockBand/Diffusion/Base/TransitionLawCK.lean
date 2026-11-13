module

public import BlockBand.Diffusion.Base.TransitionLaw

/-!
# Two-time laws and Chapman–Kolmogorov for the base kernel

`D₀ > 0`; Lebesgue measure on `ℝ`, `ℝ × ℝ`. All main results take the two named intermediate
statements `McKeanBackwardFacts D0` and `TimeMollifyDuality D0` as hypotheses.
* `exKer_univ`: `p_h(w, ·)` has mass one for `h > 0`, `w ∈ exBaseStrip`.
* `IsExBaseDiffusion.map_eq_exKer`: the law of `Z_t` is `exKer D0 t z` (`t > 0`).
* The conditional law in measure, integral and conditional-expectation form, for `s < t`, `A ∈ 𝓖_s`:
  `map_restrict_eq_bind` (`law(Z_t; A) = law(Z_s; A) ∘ p_{t-s}`), `setLIntegral_comp`
  (`E[f(Z_t); A] = E[∫ p_{t-s}(Z_s, z') f(z') dz'; A]` for measurable `f ≥ 0`),
  `condExp_indicator` (`P(Z_t ∈ B | 𝓖_s) = p_{t-s}(Z_s, B)` a.s.).
* `IsExBaseDiffusion.measure_preimage_two` (two-time fdd, product density): for `0 < s < t`,
  `P(Z_s ∈ A, Z_t ∈ B) = ∫_A p_s(z, z₁) p_{t-s}(z₁, B) dz₁`.
* `exKer_chapmanKolmogorov` (CK in measure form at every strip point `z`, `0 < s < t`):
  `p_t(z, B) = ∫ p_s(z, z₁) p_{t-s}(z₁, B) dz₁` — from the existence of a base diffusion from `z`
  (`hasExBaseDiffusion`) and the two-time law computed two ways.
* `mk_kernelX_chapmanKolmogorov` (X-factor CK at all points of the half-line): for `0 < s < T`,
  `x, x'' ≥ 0`, `∫ pX_s(x, x') pX_{T-s}(x', x'') dx' = pX_T(x, x'')` (lower integral). Proof: CK
  on rectangles `B₁ × ℝ` from `z = (x, 0)` and the sphere normalisation give equality of the
  two sides integrated over every Borel `B₁`; hence a.e. equality in `x''`; both sides are
  continuous on `[0, ∞)` (dominated convergence with the on-diagonal bound), so they agree on
  `[0, ∞)`, endpoint included.
* `exLbkCornerCKX_of : ExLbkCornerCKX D0` (the local copy of `LbkCornerCKX`): the case
  `x'' = 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-- Integrals of the product kernel over rectangles factorise (the kernel form of
`lbk_lintegral_prod`). -/
theorem exKer_prod {D0 : ℝ} (hD0 : 0 < D0) (h : ℝ) (w : ℝ × ℝ) {B₁ B₂ : Set ℝ}
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) :
    exKer D0 h w (B₁ ×ˢ B₂) =
      (∫⁻ x' in B₁, ENNReal.ofReal (mkKernelX D0 h w.1 x')) *
        ∫⁻ y' in B₂, ENNReal.ofReal (skKernelY D0 h w.2 y') := by
  have hX : Measurable fun x' => ENNReal.ofReal (mkKernelX D0 h w.1 x') :=
    ((mk_kernelX_measurable D0).comp (f := fun x' : ℝ => (h, w.1, x')) (by fun_prop)).ennreal_ofReal
  have hY : Measurable fun y' => ENNReal.ofReal (skKernelY D0 h w.2 y') :=
    ((sk_kernelY_measurable hD0).comp (f := fun y' : ℝ => (h, w.2, y'))
      (by fun_prop)).ennreal_ofReal
  rw [exKer_apply_set hD0 _ _ (hB₁.prod hB₂)]
  simp_rw [exKernel, ENNReal.ofReal_mul (mk_kernelX_nonneg hD0 _ _ _)]
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
  exact lintegral_prod_mul hX.aemeasurable hY.aemeasurable

/-- Mass one from strip points: `p_h(w, ·)` is a probability density for `h > 0`,
`w ∈ exBaseStrip`. -/
theorem exKer_univ {D0 h : ℝ} (hD0 : 0 < D0) (hh : 0 < h) {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) :
    exKer D0 h w univ = 1 := by
  rw [← univ_prod_univ, exKer_prod hD0 _ _ MeasurableSet.univ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [sk_lintegral_kernelY_one hD0 hh hw.2, mul_one,
    ← setLIntegral_eq_of_support_subset (s := Ici 0) fun x' hx' => by
      by_contra hn
      have : ¬ 0 ≤ x' := hn
      exact hx' (by simp [mkKernelX, this]),
    mk_lintegral_kernelX hD0 hh hw.1]

section Process

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {z : ℝ × ℝ}
  {Z : ℝ≥0 → Ω → ℝ × ℝ}

/-- The law of `Z_t` is `p_t(z, z') dz'`. -/
theorem IsExBaseDiffusion.map_eq_exKer (h : IsExBaseDiffusion P 𝓖 D0 z Z) (hD0 : 0 < D0)
    (hz : z ∈ exBaseStrip) (hX : McKeanBackwardFacts D0) (hT : TimeMollifyDuality D0)
    {t : ℝ≥0} (ht : 0 < t) : P.map (Z t) = exKer D0 t z :=
  Measure.ext fun B hB => by
    rw [Measure.map_apply ((h.adapted t).mono (𝓖.le t) le_rfl) hB,
      h.measure_preimage_exKer hD0 hz hX hT ht hB]

/-- **Two-time law**: for `0 < s < t`,
`P(Z_s ∈ A, Z_t ∈ B) = ∫_A p_s(z, z₁) p_{t-s}(z₁, B) dz₁`. -/
theorem IsExBaseDiffusion.measure_preimage_two (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hD0 : 0 < D0) (hz : z ∈ exBaseStrip) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) {A B : Set (ℝ × ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P (Z s ⁻¹' A ∩ Z t ⁻¹' B) =
      ∫⁻ z₁ in A, ENNReal.ofReal (exKernel D0 s z z₁) * exKer D0 ((t : ℝ) - s) z₁ B := by
  have hZs : Measurable (Z s) := (h.adapted s).mono (𝓖.le s) le_rfl
  have hpm : Measurable fun z₁ => ENNReal.ofReal (exKernel D0 s z z₁) :=
    ((exKernel_measurable hD0).comp (f := fun z₁ : ℝ × ℝ => ((s : ℝ), z, z₁))
      (by fun_prop)).ennreal_ofReal
  rw [h.measure_inter_preimage_exKer hD0 hz hX hT hst ((h.adapted s) hA) hB,
    ← setLIntegral_map hA ((exKer D0 _).measurable_coe hB) hZs,
    h.map_eq_exKer hD0 hz hX hT hs, exKer_apply hD0,
    setLIntegral_withDensity_eq_setLIntegral_mul _ hpm ((exKer D0 _).measurable_coe hB) hA]
  rfl

/-- **The conditional law, measure form**: the law of `Z_t` on `A ∈ 𝓖_s` is the law of `Z_s` on `A` transported
by `p_{t-s}`. -/
theorem IsExBaseDiffusion.map_restrict_eq_bind (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hD0 : 0 < D0) (hz : z ∈ exBaseStrip) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) {s t : ℝ≥0} (hst : s < t) {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) :
    (P.restrict A).map (Z t) = ((P.restrict A).map (Z s)).bind (exKer D0 ((t : ℝ) - s)) := by
  have hZt : Measurable (Z t) := (h.adapted t).mono (𝓖.le t) le_rfl
  have hZs : Measurable (Z s) := (h.adapted s).mono (𝓖.le s) le_rfl
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply hZt hB, Measure.restrict_apply (hZt hB), inter_comm,
    h.measure_inter_preimage_exKer hD0 hz hX hT hst hA hB,
    Measure.bind_apply hB (exKer D0 _).measurable.aemeasurable,
    lintegral_map ((exKer D0 _).measurable_coe hB) hZs]

/-- **The conditional law, integral form**: for `s < t`, `A ∈ 𝓖_s` and measurable `f ≥ 0`,
`E[f(Z_t); A] = E[∫ p_{t-s}(Z_s, z') f(z') dz'; A]`. -/
theorem IsExBaseDiffusion.setLIntegral_comp (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hD0 : 0 < D0) (hz : z ∈ exBaseStrip) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) {s t : ℝ≥0} (hst : s < t) {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in A, f (Z t ω) ∂P =
      ∫⁻ ω in A, (∫⁻ z', ENNReal.ofReal (exKernel D0 ((t : ℝ) - s) (Z s ω) z') * f z') ∂P := by
  have hZt : Measurable (Z t) := (h.adapted t).mono (𝓖.le t) le_rfl
  have hZs : Measurable (Z s) := (h.adapted s).mono (𝓖.le s) le_rfl
  have hE := h.map_restrict_eq_bind hD0 hz hX hT hst hA
  rw [← lintegral_map hf hZt, hE, Measure.lintegral_bind (exKer D0 _).measurable.aemeasurable
    hf.aemeasurable, lintegral_map hf.lintegral_kernel hZs]
  refine lintegral_congr fun ω => ?_
  have hpm : Measurable fun z' : ℝ × ℝ => ENNReal.ofReal (exKernel D0 ((t : ℝ) - s) (Z s ω) z') :=
    ((exKernel_measurable hD0).comp (f := fun z' : ℝ × ℝ => (((t : ℝ) - s), Z s ω, z'))
      (by fun_prop)).ennreal_ofReal
  rw [exKer_apply hD0, lintegral_withDensity_eq_lintegral_mul _ hpm hf]
  rfl

/-- **The conditional law, conditional expectation form**: for `s < t` and Borel `B`,
`P(Z_t ∈ B | 𝓖_s) = p_{t-s}(Z_s, B)` a.s. -/
theorem IsExBaseDiffusion.condExp_indicator (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hD0 : 0 < D0) (hz : z ∈ exBaseStrip) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) {s t : ℝ≥0} (hst : s < t) {B : Set (ℝ × ℝ)}
    (hB : MeasurableSet B) :
    P[(Z t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | 𝓖 s] =ᵐ[P]
      fun ω => (exKer D0 ((t : ℝ) - s) (Z s ω) B).toReal := by
  have := h.prob
  have hZt : Measurable (Z t) := (h.adapted t).mono (𝓖.le t) le_rfl
  have hstR : (s : ℝ) < t := by exact_mod_cast hst
  have hh0 : 0 < (t : ℝ) - s := by linarith
  set κ := exKer D0 ((t : ℝ) - s)
  have hle : ∀ᵐ ω ∂P, κ (Z s ω) B ≤ 1 := h.paths.mono fun ω hω =>
    (measure_mono (subset_univ B)).trans (exKer_univ hD0 hh0 (hω.2 s)).le
  have hgm : Measurable[𝓖 s] fun ω => κ (Z s ω) B := (κ.measurable_coe hB).comp (h.adapted s)
  have hgm' : Measurable fun ω => κ (Z s ω) B := hgm.mono (𝓖.le s) le_rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le s)
    ((integrable_const (1 : ℝ)).indicator (hZt hB)) (fun A _ _ => ?_) (fun A hA _ => ?_)
    hgm.ennreal_toReal.aestronglyMeasurable).symm
  · refine Integrable.integrableOn (Integrable.of_bound hgm'.ennreal_toReal.aestronglyMeasurable 1
      (hle.mono fun ω hω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hω)
  · rw [integral_toReal hgm'.aemeasurable.restrict
      (ae_restrict_of_ae (hle.mono fun ω hω => lt_of_le_of_lt hω ENNReal.one_lt_top)),
      ← h.measure_inter_preimage_exKer hD0 hz hX hT hst hA hB,
      integral_indicator (hZt hB), setIntegral_const, smul_eq_mul, mul_one,
      Measure.real, Measure.restrict_apply (hZt hB), inter_comm]

end Process

/-- **Chapman–Kolmogorov for the base kernel, measure form**, at every point of the closed
strip. -/
theorem exKer_chapmanKolmogorov {D0 : ℝ} (hD0 : 0 < D0) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) :
    exKer D0 t z B = ∫⁻ z₁, ENNReal.ofReal (exKernel D0 s z z₁) * exKer D0 (t - s) z₁ B := by
  obtain ⟨Ω, m, 𝓖, P, Z, h⟩ := hasExBaseDiffusion D0 hD0 z hz
  have ht : 0 < t := hs.trans hst
  have hs' : (0 : ℝ≥0) < s.toNNReal := Real.toNNReal_pos.2 hs
  have hst' : s.toNNReal < t.toNNReal := (Real.toNNReal_lt_toNNReal_iff ht).2 hst
  have h2 := h.measure_preimage_two hD0 hz hX hT hs' hst' MeasurableSet.univ hB
  rw [preimage_univ, univ_inter, h.measure_preimage_exKer hD0 hz hX hT (hs'.trans hst') hB,
    Measure.restrict_univ, Real.coe_toNNReal _ ht.le, Real.coe_toNNReal _ hs.le] at h2
  exact h2

/-!
### The X factor
-/

theorem mk_kernelX_ofReal_measurable (D0 t x : ℝ) :
    Measurable fun x' => ENNReal.ofReal (mkKernelX D0 t x x') :=
  (mk_kernelX_measurable_snd D0 t x).ennreal_ofReal

/-- The X-factor CK integrated over Borel sets: for `0 < s < T`, `x ≥ 0`, Borel `B₁`,
`∫_{B₁} pX_T(x, ·) = ∫_{B₁} ∫ pX_s(x, x₁) pX_{T-s}(x₁, ·) dx₁`. -/
theorem mk_setLIntegral_kernelX_ck {D0 : ℝ} (hD0 : 0 < D0) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) {s T : ℝ} (hs : 0 < s) (hsT : s < T) {x : ℝ} (hx : 0 ≤ x)
    {B₁ : Set ℝ} (hB₁ : MeasurableSet B₁) :
    ∫⁻ x' in B₁, ENNReal.ofReal (mkKernelX D0 T x x') =
      ∫⁻ x' in B₁, ∫⁻ x₁, ENNReal.ofReal (mkKernelX D0 s x x₁) *
        ENNReal.ofReal (mkKernelX D0 (T - s) x₁ x') := by
  have hz : ((x, 0) : ℝ × ℝ) ∈ exBaseStrip := ⟨hx, le_rfl, zero_le_one⟩
  have hT0 : 0 < T := hs.trans hsT
  have hTs : 0 < T - s := by linarith
  have hck := exKer_chapmanKolmogorov hD0 hX hT hz hs hsT (hB₁.prod MeasurableSet.univ)
  rw [exKer_prod hD0 _ _ hB₁ MeasurableSet.univ, Measure.restrict_univ,
    sk_lintegral_kernelY_one hD0 hT0 (show ((x, 0) : ℝ × ℝ).2 ∈ Icc (0 : ℝ) 1 from hz.2),
    mul_one] at hck
  rw [hck]
  -- the integrand factorises
  set a : ℝ → ℝ≥0∞ := fun x₁ => ENNReal.ofReal (mkKernelX D0 s x x₁) *
    ∫⁻ x' in B₁, ENNReal.ofReal (mkKernelX D0 (T - s) x₁ x') with ha
  set b : ℝ → ℝ≥0∞ := fun y₁ => ENNReal.ofReal (skKernelY D0 s 0 y₁) with hb
  have hfac : ∀ z₁ : ℝ × ℝ, ENNReal.ofReal (exKernel D0 s (x, 0) z₁) *
      exKer D0 (T - s) z₁ (B₁ ×ˢ univ) = a z₁.1 * b z₁.2 := by
    intro z₁
    rw [exKer_prod hD0 _ _ hB₁ MeasurableSet.univ, Measure.restrict_univ, exKernel,
      ENNReal.ofReal_mul (mk_kernelX_nonneg hD0 _ _ _)]
    simp only [ha, hb]
    by_cases hy : z₁.2 ∈ Icc (0 : ℝ) 1
    · rw [sk_lintegral_kernelY_one hD0 hTs hy]
      ring
    · rw [sk_kernelY_of_notMem_right _ hy]
      simp
  have hInner : Measurable fun x₁ => ∫⁻ x' in B₁, ENNReal.ofReal (mkKernelX D0 (T - s) x₁ x') :=
    ((mk_kernelX_measurable D0).comp (f := fun q : ℝ × ℝ => (T - s, q.1, q.2))
      (by fun_prop)).ennreal_ofReal.lintegral_prod_right'
  have ham : Measurable a := (mk_kernelX_ofReal_measurable D0 s x).mul hInner
  have hbm : Measurable b :=
    ((sk_kernelY_measurable hD0).comp (f := fun y : ℝ => (s, (0 : ℝ), y))
      (by fun_prop)).ennreal_ofReal
  simp_rw [hfac]
  rw [Measure.volume_eq_prod ℝ ℝ, lintegral_prod_mul ham.aemeasurable hbm.aemeasurable,
    hb, sk_lintegral_kernelY_one hD0 hs ⟨le_rfl, zero_le_one⟩, mul_one, ha]
  have hjm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (mkKernelX D0 s x q.1) *
      ENNReal.ofReal (mkKernelX D0 (T - s) q.1 q.2) :=
    ((mk_kernelX_ofReal_measurable D0 s x).comp measurable_fst).mul
      ((mk_kernelX_measurable D0).comp (f := fun q : ℝ × ℝ => (T - s, q.1, q.2))
        (by fun_prop)).ennreal_ofReal
  have e : ∀ x₁, ENNReal.ofReal (mkKernelX D0 s x x₁) *
      ∫⁻ x' in B₁, ENNReal.ofReal (mkKernelX D0 (T - s) x₁ x') =
      ∫⁻ x' in B₁, ENNReal.ofReal (mkKernelX D0 s x x₁) *
        ENNReal.ofReal (mkKernelX D0 (T - s) x₁ x') := fun x₁ =>
    (lintegral_const_mul _ (mk_kernelX_ofReal_measurable D0 (T - s) x₁)).symm
  simp_rw [e]
  exact lintegral_lintegral_swap (hjm.comp (f := fun q : ℝ × ℝ => q) measurable_id).aemeasurable

/-- The real form of the CK integral and its continuity on `[0, ∞)`. -/
theorem mk_ck_integral_continuousOn {D0 : ℝ} (hD0 : 0 < D0) {s T : ℝ} (hs : 0 < s)
    (hsT : s < T) {x : ℝ} (hx : 0 ≤ x) :
    ContinuousOn (fun x'' => ∫ x₁, mkKernelX D0 s x x₁ * mkKernelX D0 (T - s) x₁ x'')
      (Ici 0) := by
  have hTs : 0 < T - s := by linarith
  set C := mkDiagBound (D0 * (T - s) / 2)
  refine continuousOn_of_dominated (bound := fun x₁ => mkKernelX D0 s x x₁ * C) ?_ ?_
    ((mk_integrable_kernelX hD0 hs hx).mul_const C) ?_
  · intro x'' _
    exact ((mk_kernelX_measurable_snd D0 s x).mul ((mk_kernelX_measurable D0).comp
      (f := fun x₁ : ℝ => (T - s, x₁, x'')) (by fun_prop))).aestronglyMeasurable
  · intro x'' _
    refine ae_of_all _ fun x₁ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mk_kernelX_nonneg hD0 _ _ _)
      (mk_kernelX_nonneg hD0 _ _ _))]
    exact mul_le_mul_of_nonneg_left (mk_kernelX_le_diag hD0 hTs _ _)
      (mk_kernelX_nonneg hD0 _ _ _)
  · refine ae_of_all _ fun x₁ => ?_
    refine continuousOn_const.mul ?_
    refine ((mk_hypRadial_continuous (by positivity : 0 < D0 * (T - s) / 2) x₁).continuousOn
      (s := Ici 0)).congr fun x'' hx'' => ?_
    exact mk_kernelX_eq hTs hx''

theorem mk_ck_lintegral_eq_ofReal {D0 : ℝ} (hD0 : 0 < D0) {s T : ℝ} (hs : 0 < s)
    (hsT : s < T) {x : ℝ} (hx : 0 ≤ x) (x'' : ℝ) :
    ∫⁻ x₁, ENNReal.ofReal (mkKernelX D0 s x x₁) * ENNReal.ofReal (mkKernelX D0 (T - s) x₁ x'') =
      ENNReal.ofReal (∫ x₁, mkKernelX D0 s x x₁ * mkKernelX D0 (T - s) x₁ x'') := by
  have hTs : 0 < T - s := by linarith
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact lintegral_congr fun x₁ => (ENNReal.ofReal_mul (mk_kernelX_nonneg hD0 _ _ _)).symm
  · refine (mk_integrable_kernelX hD0 hs hx).mul_bdd ((mk_kernelX_measurable D0).comp
      (f := fun x₁ : ℝ => (T - s, x₁, x'')) (by fun_prop)).aestronglyMeasurable
      (c := mkDiagBound (D0 * (T - s) / 2)) (ae_of_all _ fun x₁ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mk_kernelX_nonneg hD0 _ _ _)]
    exact mk_kernelX_le_diag hD0 hTs _ _
  · exact ae_of_all _ fun x₁ =>
      mul_nonneg (mk_kernelX_nonneg hD0 _ _ _) (mk_kernelX_nonneg hD0 _ _ _)

/-- **Chapman–Kolmogorov for the X factor at all points of the half-line.** For `0 < s < T`,
`x ≥ 0`, `x'' ≥ 0`: `∫ pX_s(x, x') pX_{T-s}(x', x'') dx' = pX_T(x, x'')`. -/
theorem mk_kernelX_chapmanKolmogorov {D0 : ℝ} (hD0 : 0 < D0) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) {s T : ℝ} (hs : 0 < s) (hsT : s < T) {x x'' : ℝ}
    (hx : 0 ≤ x) (hx'' : 0 ≤ x'') :
    ∫⁻ x', ENNReal.ofReal (mkKernelX D0 s x x') * ENNReal.ofReal (mkKernelX D0 (T - s) x' x'') =
      ENNReal.ofReal (mkKernelX D0 T x x'') := by
  have hT0 : 0 < T := hs.trans hsT
  set F : ℝ → ℝ≥0∞ := fun x'' => ENNReal.ofReal (mkKernelX D0 T x x'') with hF
  set G : ℝ → ℝ≥0∞ := fun x'' => ∫⁻ x₁, ENNReal.ofReal (mkKernelX D0 s x x₁) *
    ENNReal.ofReal (mkKernelX D0 (T - s) x₁ x'') with hG
  have hjm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (mkKernelX D0 s x q.1) *
      ENNReal.ofReal (mkKernelX D0 (T - s) q.1 q.2) :=
    ((mk_kernelX_ofReal_measurable D0 s x).comp measurable_fst).mul
      ((mk_kernelX_measurable D0).comp (f := fun q : ℝ × ℝ => (T - s, q.1, q.2))
        (by fun_prop)).ennreal_ofReal
  have hae : F =ᵐ[volume] G :=
    ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (mk_kernelX_ofReal_measurable D0 T x)
      hjm.lintegral_prod_left' fun B₁ hB₁ _ =>
        mk_setLIntegral_kernelX_ck hD0 hX hT hs hsT hx hB₁
  have hFc : ContinuousOn F (Ici 0) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      ((mk_hypRadial_continuous (by positivity : 0 < D0 * T / 2) x).continuousOn)).congr
      fun x' hx' => by simp only [hF, Function.comp, mk_kernelX_eq hT0 hx']
  have hGc : ContinuousOn G (Ici 0) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (mk_ck_integral_continuousOn hD0 hs hsT hx)).congr
      fun x' _ => by simp only [hG, Function.comp, mk_ck_lintegral_eq_ofReal hD0 hs hsT hx x']
  have hcl : Ici (0 : ℝ) ⊆ closure (interior (Ici 0)) := by
    rw [interior_Ici, closure_Ioi]
  exact (Measure.eqOn_of_ae_eq (ae_restrict_of_ae hae) hFc hGc hcl hx'').symm

/-- **Chapman–Kolmogorov at the corner `x'' = 0`** (`ExLbkCornerCKX`, the local copy of
`LbkCornerCKX`), from `McKeanBackwardFacts` and `TimeMollifyDuality`. -/
theorem exLbkCornerCKX_of {D0 : ℝ} (hD0 : 0 < D0) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) : ExLbkCornerCKX D0 :=
  fun _ _ hs hsT _ hx => mk_kernelX_chapmanKolmogorov hD0 hX hT hs hsT hx le_rfl

end BlockBand.Diffusion
