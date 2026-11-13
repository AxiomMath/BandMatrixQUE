module

public import BlockBand.Endpoints.Response.BridgeOccupationProofDefs

/-!
# Version independence and factorisation of the bridge occupation

## Main results

* `bop_occupation_eq_lbk`: for a jointly measurable `p` with `IsBaseDensity D₀ p`, given the
  transition law `LbkBaseTransitionLaw D₀`, the occupation of `p` from a strip point equals that
  of the explicit kernel `lbkKernel D₀` on every `(a, b) ⊆ (0, T)`. (The law gives
  `ofReal p_t(z,·) = ofReal lbk_t(z,·)` a.e.; continuity on the strip, which is the closure of its
  interior, determines all strip values, in particular the corner values `p_t(z',(0,0))`; off the
  strip the first factor vanishes a.e.)
* `bop_meanTotal_lbk_eq`: for the explicit kernel the one-time occupation density factorises,
  `E^{br}[X_s + Y_s] = (A_X B_Y + B_X A_Y) / (pX_T(x₀,0) pY_T(y₀,0))` with the masses `B`
  (`bopXMass`, `bopYMass`) and first moments `A` (`bopXMoment`, `bopYMoment`).
* `bop_meanTotal_lbk_bounds`: from the corner Chapman–Kolmogorov identity and the two hyperbolic
  bridge-mean bounds, `c g(s) ≤ E^{br}[X_s+Y_s] ≤ C e^{(1-s/T)r₀} + 1` (the sphere coordinate
  contributes at most `1` because `Y ∈ [0, 1]`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Filter
open scoped ENNReal

/-!
### Version independence
-/

theorem bop_lbk_off_strip {D0 t : ℝ} {z z' : ℝ × ℝ} (h : z' ∉ baseStrip) :
    lbkKernel D0 t z z' = 0 := by
  unfold lbkKernel
  by_cases hx : 0 ≤ z'.1
  · have hy : z'.2 ∉ Icc (0 : ℝ) 1 := fun hy => h ⟨hx, hy⟩
    have : lbkKernelY D0 t z.2 z'.2 = 0 := by
      unfold lbkKernelY
      split_ifs with hh
      · exact absurd hh.2.2 hy
      · rfl
    rw [this, mul_zero]
  · have : lbkKernelX D0 t z.1 z'.1 = 0 := by
      unfold lbkKernelX
      split_ifs with hh
      · exact absurd hh.2 hx
      · rfl
    rw [this, zero_mul]

theorem bop_strip_subset_closure_interior : baseStrip ⊆ closure (interior baseStrip) := by
  unfold baseStrip
  rw [interior_prod_eq, closure_prod_eq, interior_Ici, interior_Icc, closure_Ioi,
    closure_Ioo zero_ne_one]

theorem bop_measurable_section {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ}
    (hpm : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2) (t : ℝ) (z : ℝ × ℝ) :
    Measurable fun z' => p t z z' :=
  hpm.comp (f := fun z' : ℝ × ℝ => (t, z, z')) (by fun_prop)

/-- The densities agree a.e. (as `ofReal`). -/
theorem bop_ofReal_ae_eq {D0 : ℝ} (hD0 : 0 < D0) (hlaw : LbkBaseTransitionLaw D0)
    {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ} (hp : IsBaseDensity D0 p)
    (hpm : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2) {t : ℝ} (ht : 0 < t)
    {z : ℝ × ℝ} (hz : z ∈ baseStrip) :
    (fun z' => ENNReal.ofReal (p t z z')) =ᵐ[volume]
      fun z' => ENNReal.ofReal (lbkKernel D0 t z z') := by
  obtain ⟨Ω, m, 𝓖, P, Z, hZ⟩ := hp.exists_ z hz
  have ht' : 0 < t.toNNReal := Real.toNNReal_pos.2 ht
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (bop_measurable_section hpm t z).ennreal_ofReal
    ((bop_measurable_section (lbk_kernel_measurable hD0) t z).ennreal_ofReal) fun B hB _ => ?_
  have h1 := hp.law t.toNNReal ht' z hz Ω m 𝓖 P Z hZ B hB
  have h2 := hlaw t.toNNReal ht' z hz Ω m 𝓖 P Z hZ B hB
  rw [Real.coe_toNNReal _ ht.le] at h1 h2
  rw [← h1, h2]

/-- The densities agree (as `ofReal`) at every strip point. -/
theorem bop_ofReal_eq_on_strip {D0 : ℝ} (hD0 : 0 < D0) (hlaw : LbkBaseTransitionLaw D0)
    {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ} (hp : IsBaseDensity D0 p)
    (hpm : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2) {t : ℝ} (ht : 0 < t)
    {z : ℝ × ℝ} (hz : z ∈ baseStrip) {z' : ℝ × ℝ} (hz' : z' ∈ baseStrip) :
    ENNReal.ofReal (p t z z') = ENNReal.ofReal (lbkKernel D0 t z z') :=
  Measure.eqOn_of_ae_eq (μ := volume)
    (ae_restrict_of_ae (bop_ofReal_ae_eq hD0 hlaw hp hpm ht hz))
    (ENNReal.continuous_ofReal.comp_continuousOn (hp.cont t ht z hz))
    (ENNReal.continuous_ofReal.comp_continuousOn (lbk_kernel_continuousOn hD0 ht hz))
    bop_strip_subset_closure_interior hz'

/-- The one-time occupation density in integral form over `ℝ²`. -/
theorem bop_meanTotal_eq (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (z : ℝ × ℝ) (T s : ℝ) :
    bridgeMeanTotal p z T s = ∫⁻ z', ENNReal.ofReal (z'.1 + z'.2) *
      (ENNReal.ofReal (p s z z') * ENNReal.ofReal (p (T - s) z' (0, 0)) /
        ENNReal.ofReal (p T z (0, 0))) := by
  unfold bridgeMeanTotal
  simp_rw [bop_bridgeFdd_one]
  exact (volume_preserving_funUnique (Fin 1) (ℝ × ℝ)).lintegral_comp_emb
    (MeasurableEquiv.funUnique (Fin 1) (ℝ × ℝ)).measurableEmbedding
    (fun z' => ENNReal.ofReal (z'.1 + z'.2) *
      (ENNReal.ofReal (p s z z') * ENNReal.ofReal (p (T - s) z' (0, 0)) /
        ENNReal.ofReal (p T z (0, 0))))

/-- Version independence of the one-time occupation density. -/
theorem bop_meanTotal_eq_lbk {D0 : ℝ} (hD0 : 0 < D0) (hlaw : LbkBaseTransitionLaw D0)
    {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ} (hp : IsBaseDensity D0 p)
    (hpm : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2)
    {z : ℝ × ℝ} (hz : z ∈ baseStrip) {T s : ℝ} (hs : 0 < s) (hsT : s < T) :
    bridgeMeanTotal p z T s = bridgeMeanTotal (lbkKernel D0) z T s := by
  rw [bop_meanTotal_eq, bop_meanTotal_eq]
  have hT : 0 < T := hs.trans hsT
  have hden := bop_ofReal_eq_on_strip hD0 hlaw hp hpm hT hz bop_corner_mem
  refine lintegral_congr_ae ?_
  filter_upwards [bop_ofReal_ae_eq hD0 hlaw hp hpm hs hz] with z' hz'
  rw [hden]
  by_cases hS : z' ∈ baseStrip
  · rw [hz', bop_ofReal_eq_on_strip hD0 hlaw hp hpm (sub_pos.2 hsT) hS bop_corner_mem]
  · have h0 : ENNReal.ofReal (lbkKernel D0 s z z') = 0 := by
      rw [bop_lbk_off_strip hS, ENNReal.ofReal_zero]
    rw [hz', h0, zero_mul, zero_mul, ENNReal.zero_div]

/-- Version independence of the occupation on `(a, b) ⊆ (0, T)`. -/
theorem bop_occupation_eq_lbk {D0 : ℝ} (hD0 : 0 < D0) (hlaw : LbkBaseTransitionLaw D0)
    {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ} (hp : IsBaseDensity D0 p)
    (hpm : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2)
    {z : ℝ × ℝ} (hz : z ∈ baseStrip) {T a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ T) :
    bridgeOccupation p z T a b = bridgeOccupation (lbkKernel D0) z T a b :=
  setLIntegral_congr_fun measurableSet_Ioo fun _ hs =>
    bop_meanTotal_eq_lbk hD0 hlaw hp hpm hz (ha.trans_lt hs.1) (hs.2.trans_le hb)

/-!
### Factorisation for the explicit kernel
-/

theorem bop_kernelY_off {D0 t y y' : ℝ} (h : y' ∉ Icc (0 : ℝ) 1) : lbkKernelY D0 t y y' = 0 := by
  unfold lbkKernelY
  split_ifs with hh
  · exact absurd hh.2.2 h
  · rfl

theorem bop_kernelX_off {D0 t x x' : ℝ} (h : x' < 0) : lbkKernelX D0 t x x' = 0 := by
  unfold lbkKernelX
  split_ifs with hh
  · exact absurd hh.2 (not_le.2 h)
  · rfl

theorem bop_measurable_kX (D0 x T s : ℝ) :
    Measurable fun x' => ENNReal.ofReal (lbkKernelX D0 s x x') *
      ENNReal.ofReal (lbkKernelX D0 (T - s) x' 0) :=
  ((lbk_kernelX_measurable D0).comp (f := fun x' : ℝ => (s, x, x')) (by fun_prop)).ennreal_ofReal.mul
    ((lbk_kernelX_measurable D0).comp (f := fun x' : ℝ => (T - s, x', (0 : ℝ)))
      (by fun_prop)).ennreal_ofReal

theorem bop_measurable_kY {D0 : ℝ} (hD0 : 0 < D0) (y T s : ℝ) :
    Measurable fun y' => ENNReal.ofReal (lbkKernelY D0 s y y') *
      ENNReal.ofReal (lbkKernelY D0 (T - s) y' 0) :=
  ((lbk_kernelY_measurable hD0).comp (f := fun y' : ℝ => (s, y, y')) (by fun_prop)).ennreal_ofReal.mul
    ((lbk_kernelY_measurable hD0).comp (f := fun y' : ℝ => (T - s, y', (0 : ℝ)))
      (by fun_prop)).ennreal_ofReal

/-- The product of the two transition factors splits into the coordinate factors. -/
theorem bop_lbk_pair_eq {D0 : ℝ} (hD0 : 0 < D0) (z z' : ℝ × ℝ)
    (T s : ℝ) :
    ENNReal.ofReal (lbkKernel D0 s z z') * ENNReal.ofReal (lbkKernel D0 (T - s) z' (0, 0)) =
      (ENNReal.ofReal (lbkKernelX D0 s z.1 z'.1) * ENNReal.ofReal (lbkKernelX D0 (T - s) z'.1 0)) *
        (ENNReal.ofReal (lbkKernelY D0 s z.2 z'.2) *
          ENNReal.ofReal (lbkKernelY D0 (T - s) z'.2 0)) := by
  simp only [lbkKernel]
  rw [ENNReal.ofReal_mul (lbk_kernelX_nonneg hD0 _ _ _),
    ENNReal.ofReal_mul (lbk_kernelX_nonneg hD0 _ _ _)]
  ring

theorem bop_lbk_corner_eq {D0 : ℝ} (hD0 : 0 < D0) (z : ℝ × ℝ) (T : ℝ) :
    ENNReal.ofReal (lbkKernel D0 T z (0, 0)) =
      ENNReal.ofReal (lbkKernelX D0 T z.1 0) * ENNReal.ofReal (lbkKernelY D0 T z.2 0) := by
  simp only [lbkKernel]
  rw [ENNReal.ofReal_mul (lbk_kernelX_nonneg hD0 _ _ _)]

/-- The two-dimensional bridge mass factorises. -/
theorem bop_mass_prod {D0 : ℝ} (hD0 : 0 < D0) (z : ℝ × ℝ)
    (T s : ℝ) :
    ∫⁻ z', ENNReal.ofReal (lbkKernel D0 s z z') * ENNReal.ofReal (lbkKernel D0 (T - s) z' (0, 0)) =
      bopXMass D0 z.1 T s * bopYMass D0 z.2 T s := by
  simp_rw [bop_lbk_pair_eq hD0 z _ T s]
  rw [Measure.volume_eq_prod]
  exact lintegral_prod_mul (bop_measurable_kX D0 z.1 T s).aemeasurable
    (bop_measurable_kY hD0 z.2 T s).aemeasurable

/-- Factorisation of the one-time occupation density for the explicit kernel. -/
theorem bop_meanTotal_lbk_eq {D0 : ℝ} (hD0 : 0 < D0) (z : ℝ × ℝ) (T s : ℝ) :
    bridgeMeanTotal (lbkKernel D0) z T s =
      (bopXMoment D0 z.1 T s * bopYMass D0 z.2 T s + bopXMass D0 z.1 T s * bopYMoment D0 z.2 T s) /
        (ENNReal.ofReal (lbkKernelX D0 T z.1 0) * ENNReal.ofReal (lbkKernelY D0 T z.2 0)) := by
  rw [bop_meanTotal_eq, ← bop_lbk_corner_eq hD0 z T]
  set c := ENNReal.ofReal (lbkKernel D0 T z (0, 0))
  set gX : ℝ → ℝ≥0∞ := fun x' => ENNReal.ofReal (lbkKernelX D0 s z.1 x') *
    ENNReal.ofReal (lbkKernelX D0 (T - s) x' 0) with hgX
  set gY : ℝ → ℝ≥0∞ := fun y' => ENNReal.ofReal (lbkKernelY D0 s z.2 y') *
    ENNReal.ofReal (lbkKernelY D0 (T - s) y' 0) with hgY
  have hgXm : Measurable gX := bop_measurable_kX D0 z.1 T s
  have hgYm : Measurable gY := bop_measurable_kY hD0 z.2 T s
  have hpt : ∀ z' : ℝ × ℝ, ENNReal.ofReal (z'.1 + z'.2) *
      (ENNReal.ofReal (lbkKernel D0 s z z') * ENNReal.ofReal (lbkKernel D0 (T - s) z' (0, 0)) / c) =
      (ENNReal.ofReal z'.1 * gX z'.1 * gY z'.2 + gX z'.1 * (ENNReal.ofReal z'.2 * gY z'.2)) *
        c⁻¹ := by
    intro z'
    rw [bop_lbk_pair_eq hD0 z z' T s, div_eq_mul_inv]
    change ENNReal.ofReal (z'.1 + z'.2) * (gX z'.1 * gY z'.2 * c⁻¹) = _
    by_cases hx : z'.1 < 0
    · have : gX z'.1 = 0 := by
        simp only [hgX, bop_kernelX_off hx, ENNReal.ofReal_zero, zero_mul]
      rw [this]
      simp only [mul_zero, zero_mul, add_zero]
    · by_cases hy : z'.2 < 0
      · have : gY z'.2 = 0 := by
          simp only [hgY, bop_kernelY_off (fun h => not_le.2 hy h.1), ENNReal.ofReal_zero,
            zero_mul]
        rw [this]
        simp only [mul_zero, zero_mul, add_zero]
      · rw [ENNReal.ofReal_add (not_lt.1 hx) (not_lt.1 hy)]
        ring
  simp_rw [hpt]
  have hF1 : Measurable fun z' : ℝ × ℝ => ENNReal.ofReal z'.1 * gX z'.1 * gY z'.2 :=
    (measurable_fst.ennreal_ofReal.mul (hgXm.comp measurable_fst)).mul (hgYm.comp measurable_snd)
  have hF2 : Measurable fun z' : ℝ × ℝ => gX z'.1 * (ENNReal.ofReal z'.2 * gY z'.2) :=
    (hgXm.comp measurable_fst).mul (measurable_snd.ennreal_ofReal.mul (hgYm.comp measurable_snd))
  have hF : Measurable fun z' : ℝ × ℝ =>
      ENNReal.ofReal z'.1 * gX z'.1 * gY z'.2 + gX z'.1 * (ENNReal.ofReal z'.2 * gY z'.2) :=
    hF1.add hF2
  rw [lintegral_mul_const _ hF, lintegral_add_left hF1, Measure.volume_eq_prod,
    lintegral_prod_mul (f := fun x => ENNReal.ofReal x * gX x) (g := gY)
      (measurable_id.ennreal_ofReal.mul hgXm).aemeasurable hgYm.aemeasurable,
    lintegral_prod_mul (f := gX) (g := fun y => ENNReal.ofReal y * gY y)
      hgXm.aemeasurable (measurable_id.ennreal_ofReal.mul hgYm).aemeasurable,
    div_eq_mul_inv]
  rfl

/-- The sphere moment is at most the sphere mass (`Y ≤ 1`). -/
theorem bop_yMoment_le_mass (D0 y T s : ℝ) : bopYMoment D0 y T s ≤ bopYMass D0 y T s := by
  unfold bopYMoment bopYMass
  refine lintegral_mono fun y' => ?_
  by_cases hy : y' ≤ 1
  · calc ENNReal.ofReal y' * (ENNReal.ofReal (lbkKernelY D0 s y y') *
          ENNReal.ofReal (lbkKernelY D0 (T - s) y' 0))
        ≤ 1 * (ENNReal.ofReal (lbkKernelY D0 s y y') *
          ENNReal.ofReal (lbkKernelY D0 (T - s) y' 0)) := by
          gcongr; exact ENNReal.ofReal_le_one.2 hy
      _ = _ := one_mul _
  · rw [bop_kernelY_off (fun h => hy h.2), ENNReal.ofReal_zero, zero_mul, mul_zero]

/-- Pointwise bounds on the one-time occupation density for the explicit kernel, from the
corner Chapman–Kolmogorov identity and the hyperbolic bridge-mean bounds (in multiplied-out
form, with the bridge masses `B_X`). -/
theorem bop_meanTotal_lbk_bounds {D0 : ℝ} (hD0 : 0 < D0) (hpos : LbkSphereKernelPos D0)
    (hCK : LbkCornerChapmanKolmogorov D0) {z : ℝ × ℝ} (hz : z ∈ baseStrip) {T s : ℝ}
    (hs : 0 < s) (hsT : s < T) {a b : ℝ≥0∞}
    (hlow : a * bopXMass D0 z.1 T s ≤ bopXMoment D0 z.1 T s)
    (hup : bopXMoment D0 z.1 T s ≤ b * bopXMass D0 z.1 T s) :
    a ≤ bridgeMeanTotal (lbkKernel D0) z T s ∧ bridgeMeanTotal (lbkKernel D0) z T s ≤ b + 1 := by
  have hT : 0 < T := hs.trans hsT
  set Q := ENNReal.ofReal (lbkKernelX D0 T z.1 0) * ENNReal.ofReal (lbkKernelY D0 T z.2 0) with hQ
  have hQ0 : Q ≠ 0 := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hY : 0 < lbkKernelY D0 T z.2 0 := by
      rw [lbk_kernelY_eq hT hz.2 h0]; exact hpos T hT z.2 hz.2 0 h0
    exact mul_ne_zero (ENNReal.ofReal_pos.2 (lbk_kernelX_zero_pos hD0 hT z.1)).ne'
      (ENNReal.ofReal_pos.2 hY).ne'
  have hQt : Q ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hmass : bopXMass D0 z.1 T s * bopYMass D0 z.2 T s = Q := by
    rw [← bop_mass_prod hD0 z T s, hCK T s hs hsT z hz, bop_lbk_corner_eq hD0 z T]
  rw [bop_meanTotal_lbk_eq hD0 z T s, ← hQ]
  constructor
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hQ0) (Or.inl hQt)]
    calc a * Q = a * bopXMass D0 z.1 T s * bopYMass D0 z.2 T s := by rw [← hmass, mul_assoc]
      _ ≤ bopXMoment D0 z.1 T s * bopYMass D0 z.2 T s := by gcongr
      _ ≤ _ := le_self_add
  · refine ENNReal.div_le_of_le_mul ?_
    calc bopXMoment D0 z.1 T s * bopYMass D0 z.2 T s + bopXMass D0 z.1 T s * bopYMoment D0 z.2 T s
        ≤ b * bopXMass D0 z.1 T s * bopYMass D0 z.2 T s +
            bopXMass D0 z.1 T s * bopYMass D0 z.2 T s := by
          gcongr
          exact bop_yMoment_le_mass D0 z.2 T s
      _ = (b + 1) * Q := by rw [← hmass]; ring

end BlockBand.Endpoints
