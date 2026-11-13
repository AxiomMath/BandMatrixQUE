module

public import BlockBand.DeterminantScore.MinorTailInversePair

/-!
# The inverse spread on the good event

`inner_good` (fixed outer data `θ` with Hermitian blocks and unit `v`, `s = splitS p`,
`t = s/(2W)`, `β = q/(q+1)`, `0 < r < 2β`):
`E_{G'}[det² 1{sector α} 1_{𝒢_α}(θ) q_B^{-r}] ≤ (1 + r K''/(2β - r)) Σ_{ℓ=α-1}^{α+1} 𝔷_ℓ(θ)`,
`K'' = (2 + 2/s + C_q c^{-q}) (4/s² + 2/s)^β`, with `C_q ≥ 0` a constant of the `inverse_moment`
field of `NegativeSpreadStatement` at exponent `q`.

Proof: `q_B² ≥ t` and `q_B² ≥ t²V_B` on Hermitian `G'` (`minorQSq_ge`), so `Y = q_B⁻¹ = (q_B²)^{-1/2}`
satisfies `{Y > u} ⊆ {V_B ≤ 1/(t²u²)}` and `{Y > u} = ∅` for `tu² ≥ 1`; the fixed-`θ` tail bound
`MinorTail.inner_tail` with the splitting parameter of `MinorTail.tail_constant` gives the level
bound `tail_level`; the layer-cake formula (`lintegral_rpow_eq_lintegral_meas_lt_mul`) against
`det² 1{sector α} dGUE` and the two power integrals over `(0,1]` and `(1,∞)` conclude.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.MinorTailInverse

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.MinorTail
open scoped NNReal ENNReal

variable {p : Parameters} {i : ZMod p.n}

/-- `q_B² ≥ t`, `q_B² ≥ t²V_B` and `V_B ≥ 0` for Hermitian blocks and Hermitian `G'`. -/
theorem minorQSq_ge (s : ℝ) (U : FrameMap p i) {θ : OuterData p i} (hR : θ.1.1.IsHermitian)
    (hV : θ.1.2.2.IsHermitian) (w : OuterData p i → (FrameIndex p → ℂ))
    (Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ) {G' : FrameMatrix p}
    (hG' : G'.IsHermitian) :
    (pairTime p s : ℝ) ≤ minorQSq s U w Uw θ G' ∧
      (pairTime p s : ℝ) ^ 2 * minorV U w Uw θ G' ≤ minorQSq s U w Uw θ G' ∧
      0 ≤ minorV U w Uw θ G' := by
  have hM : (outerM U θ G').IsHermitian := by
    rw [outerM_eq]; exact (outerKs_isHermitian U hR hV).add hG'
  have hB : (minorB U w Uw θ G').IsHermitian := isHermitian_conjTranspose_mul_mul _ hM
  have hVn : 0 ≤ minorV U w Uw θ G' := invSq_nonneg hB
  have h1 := sq_nonneg (rowMean U w θ - (pairTime p s : ℝ) * (minorB U w Uw θ G')⁻¹.trace.re)
  have h2 : 0 ≤ (pairTime p s : ℝ) ^ 2 * minorV U w Uw θ G' := mul_nonneg (sq_nonneg _) hVn
  have ht : (0 : ℝ) ≤ pairTime p s := NNReal.coe_nonneg _
  simp only [minorQSq]
  refine ⟨by linarith, by linarith, hVn⟩

theorem measurable_minorB_G (U : FrameMap p i) (w : OuterData p i → (FrameIndex p → ℂ))
    (Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ) (θ : OuterData p i) :
    Measurable fun G' : FrameMatrix p => minorB U w Uw θ G' := by
  unfold minorB
  simp_rw [outerM_eq]
  exact ((continuous_const.matrix_mul (continuous_const.add continuous_id)).matrix_mul
    continuous_const).measurable

theorem measurable_minorQSq_G (s : ℝ) (U : FrameMap p i) (w : OuterData p i → (FrameIndex p → ℂ))
    (Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ) (θ : OuterData p i) :
    Measurable fun G' : FrameMatrix p => minorQSq s U w Uw θ G' := by
  have hB := measurable_minorB_G U w Uw θ
  have hBi := measurable_inv_matrix.comp hB
  have htr : Measurable fun G' : FrameMatrix p => (minorB U w Uw θ G')⁻¹.trace.re :=
    Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp hBi)
  have hV : Measurable fun G' : FrameMatrix p => minorV U w Uw θ G' := measurable_invSq.comp hB
  unfold minorQSq
  exact (((measurable_const.sub (measurable_const.mul htr)).pow_const 2).add measurable_const).add
    (measurable_const.mul hV)

/-- `(X^{-1/2})² = X⁻¹` for `X > 0`. -/
theorem rpow_neg_half_sq {X : ℝ} (hX : 0 < X) : (X ^ (-(1 / 2 : ℝ))) ^ 2 = X⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
  norm_num [Real.rpow_neg_one]

/-- `u < X^{-1/2}` with `X > 0`, `u ≥ 0` gives `u² X < 1`. -/
theorem sq_mul_lt_one {X u : ℝ} (hX : 0 < X) (hu : 0 ≤ u) (h : u < X ^ (-(1 / 2 : ℝ))) :
    u ^ 2 * X < 1 := by
  have h0 : 0 ≤ X ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hX.le _
  have h2 : u ^ 2 < (X ^ (-(1 / 2 : ℝ))) ^ 2 := by
    exact pow_lt_pow_left₀ h hu (by norm_num)
  rw [rpow_neg_half_sq hX] at h2
  calc u ^ 2 * X < X⁻¹ * X := mul_lt_mul_of_pos_right h2 hX
    _ = 1 := inv_mul_cancel₀ hX.ne'

theorem pairTime_splitS_eq (p : Parameters) :
    (pairTime p (splitS p) : ℝ) = splitS p / (2 * (p.W : ℝ)) := by
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  unfold pairTime
  rw [Real.coe_toNNReal _ (by positivity)]

/-- The level parameter: for `tu² ≤ 1`, `(1/(t²u²) + W)/W² ≤ (4/s² + 2/s)/u²`. -/
theorem level_le {s W u : ℝ} (hs : 0 < s) (hW : 0 < W) (hu : 0 < u)
    (htu : s / (2 * W) * u ^ 2 ≤ 1) :
    (1 / ((s / (2 * W)) ^ 2 * u ^ 2) + W) / W ^ 2 ≤ (4 / s ^ 2 + 2 / s) / u ^ 2 := by
  have hsu : s * u ^ 2 ≤ 2 * W := by
    have h := mul_le_mul_of_nonneg_left htu (by positivity : (0 : ℝ) ≤ 2 * W)
    field_simp at h
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : (1 / ((s / (2 * W)) ^ 2 * u ^ 2) + W) * u ^ 2 = 4 * W ^ 2 / s ^ 2 + W * u ^ 2 := by
    field_simp
    ring
  rw [e]
  have e2 : (4 / s ^ 2 + 2 / s) * W ^ 2 = 4 * W ^ 2 / s ^ 2 + 2 * W ^ 2 / s := by ring
  rw [e2]
  have : W * u ^ 2 ≤ 2 * W ^ 2 / s := by
    rw [le_div_iff₀ hs]
    nlinarith
  linarith

/-- `(D/u²)^β = D^β u^{-2β}`. -/
theorem div_sq_rpow {D u β : ℝ} (hD : 0 ≤ D) (hu : 0 < u) :
    (D / u ^ 2) ^ β = D ^ β * u ^ (-(2 * β)) := by
  rw [Real.div_rpow hD (by positivity), ← Real.rpow_natCast u 2, ← Real.rpow_mul hu.le,
    Real.rpow_neg hu.le, div_eq_mul_inv]
  norm_num

/-- The level constant `K'' = (2 + 2/s + C c^{-q})(4/s² + 2/s)^{q/(q+1)}`. -/
def levelConst (s C c q : ℝ) : ℝ :=
  (2 + 2 / s + C * (c ^ q)⁻¹) * (4 / s ^ 2 + 2 / s) ^ (q / (q + 1))

/-- **Level bound** at fixed `θ ∈ 𝒢_α`: `E_{G'}[det² 1{sector α} 1{q_B^{-1} > u}] ≤
K'' u^{-2q/(q+1)} Σ_{ℓ=α-1}^{α+1} 𝔷_ℓ(θ)` for every `u > 0`. -/
theorem tail_level {q C : ℝ}
    (hCq : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
      K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
        (∫⁻ x, ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) ∂sectorLaw m t K ℓ) ≤
          ENNReal.ofReal C * ((∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) ^ q)⁻¹)
    (hC : 0 ≤ C) (hq : 0 < q) (α : Fin p.N) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian) (hv : l2Norm θ.2.2 = 1)
    {w : OuterData p i → (FrameIndex p → ℂ)} (hw : IsOuterEigenvector U w)
    {Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ} (hUw : IsMinorFrame Uw)
    (κ c : ℝ) (hc : 0 < c) (hG : SpreadGood α (splitS p) U κ c θ) {u : ℝ} (hu : 0 < u) :
    (∫⁻ G' in {G' : FrameMatrix p | u < minorQSq (splitS p) U w Uw θ G' ^ (-(1 / 2 : ℝ))},
        ENNReal.ofReal (sectorWeight α U θ G') ∂gueMeasure (FrameIndex p) (pairTime p (splitS p))) ≤
      ENNReal.ofReal (levelConst (splitS p) C c q * u ^ (-(2 * (q / (q + 1))))) *
        (zNat (splitS p) U (α.val - 1) θ + zNat (splitS p) U α.val θ +
          zNat (splitS p) U (α.val + 1) θ) := by
  set s := splitS p with hsdef
  set t : ℝ := (pairTime p s : ℝ) with htdef
  have ht : 0 < pairTime p s := pairTime_splitS_pos p
  have ht' : (0 : ℝ) < t := ht
  have hs : 0 < s := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hteq : t = s / (2 * (p.W : ℝ)) := pairTime_splitS_eq p
  set X := fun G' : FrameMatrix p => minorQSq s U w Uw θ G' with hXdef
  have hXm : Measurable X := measurable_minorQSq_G s U w Uw θ
  have hS : MeasurableSet {G' : FrameMatrix p | u < X G' ^ (-(1 / 2 : ℝ))} :=
    measurableSet_lt measurable_const (hXm.pow_const _)
  rw [← lintegral_indicator hS]
  by_cases htu : t * u ^ 2 < 1
  · set A := 1 / (t ^ 2 * u ^ 2) with hAdef
    have hA : 0 ≤ A := by positivity
    set ρ := (A + p.W) / (p.W : ℝ) ^ 2 with hρdef
    set a := (p.W : ℝ) ^ 2 * ρ ^ (1 / (q + 1)) with hadef
    have ha : 0 < a := by positivity
    have hpt : ∀ᵐ G' ∂gueMeasure (FrameIndex p) (pairTime p s),
        {G' : FrameMatrix p | u < X G' ^ (-(1 / 2 : ℝ))}.indicator
            (fun G' => ENNReal.ofReal (sectorWeight α U θ G')) G' ≤
          ENNReal.ofReal (sectorWeight α U θ G') *
            ind (fun x : OuterData p i × FrameMatrix p =>
              SpreadGood α s U κ c x.1 ∧ minorV U w Uw x.1 x.2 ≤ A) (θ, G') := by
      filter_upwards [ae_isHermitian_gue (pairTime p s)] with G' hG'
      by_cases hin : u < X G' ^ (-(1 / 2 : ℝ))
      · obtain ⟨hXt, hXV, -⟩ := minorQSq_ge s U hR hV w Uw hG'
        have hXpos : 0 < X G' := lt_of_lt_of_le ht' hXt
        have h1 := sq_mul_lt_one hXpos hu.le hin
        have hVA : minorV U w Uw θ G' ≤ A := by
          rw [hAdef, le_div_iff₀ (by positivity)]
          have : u ^ 2 * (t ^ 2 * minorV U w Uw θ G') ≤ u ^ 2 * X G' :=
            mul_le_mul_of_nonneg_left hXV (by positivity)
          nlinarith
        have hind : ind (fun x : OuterData p i × FrameMatrix p =>
            SpreadGood α s U κ c x.1 ∧ minorV U w Uw x.1 x.2 ≤ A) (θ, G') = 1 := by
          simp [ind, hG, hVA]
        rw [hind, mul_one, indicator_of_mem (by exact hin)]
      · rw [indicator_of_notMem (by exact hin)]
        exact zero_le
    have hρ : ρ ≤ (4 / s ^ 2 + 2 / s) / u ^ 2 := by
      have := level_le hs hW hu (by rw [← hteq]; exact htu.le)
      rw [hρdef, hAdef, hteq]
      exact this
    have hρ0 : 0 ≤ ρ := by positivity
    have hq1 : 0 ≤ q / (q + 1) := by positivity
    calc _ ≤ ∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
            ind (fun x : OuterData p i × FrameMatrix p =>
              SpreadGood α s U κ c x.1 ∧ minorV U w Uw x.1 x.2 ≤ A) (θ, G')
            ∂gueMeasure (FrameIndex p) (pairTime p s) := lintegral_mono_ae hpt
      _ ≤ ENNReal.ofReal (a⁻¹ * (2 * A + (t)⁻¹) + a ^ q * (C * ((c * (p.W : ℝ) ^ 2) ^ q)⁻¹)) *
            (zNat s U (α.val - 1) θ + zNat s U α.val θ + zNat s U (α.val + 1) θ) :=
          inner_tail hCq hC hq α s hU hR hV hv hw hUw ht κ c hc hA ha
      _ ≤ _ := by
          gcongr ?_ * _
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : a⁻¹ * (2 * A + t⁻¹) + a ^ q * (C * ((c * (p.W : ℝ) ^ 2) ^ q)⁻¹) ≤
              (2 + 2 / s + C * (c ^ q)⁻¹) * ρ ^ (q / (q + 1)) := by
            rw [htdef, hsdef, inv_pairTime_eq]
            exact tail_constant hA hW hs hc hq
          have hK : 0 ≤ 2 + 2 / s + C * (c ^ q)⁻¹ := by
            have : 0 ≤ C * (c ^ q)⁻¹ := mul_nonneg hC (inv_nonneg.mpr (Real.rpow_nonneg hc.le _))
            positivity
          have h2 : ρ ^ (q / (q + 1)) ≤ ((4 / s ^ 2 + 2 / s) / u ^ 2) ^ (q / (q + 1)) :=
            Real.rpow_le_rpow hρ0 hρ hq1
          rw [div_sq_rpow (by positivity) hu] at h2
          unfold levelConst
          calc _ ≤ _ := h1
            _ ≤ (2 + 2 / s + C * (c ^ q)⁻¹) * ((4 / s ^ 2 + 2 / s) ^ (q / (q + 1)) *
                u ^ (-(2 * (q / (q + 1))))) := mul_le_mul_of_nonneg_left h2 hK
            _ = _ := by ring
  · refine le_trans (le_of_eq ?_) zero_le
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [ae_isHermitian_gue (pairTime p s)] with G' hG'
    obtain ⟨hXt, -, -⟩ := minorQSq_ge s U hR hV w Uw hG'
    have hXpos : 0 < X G' := lt_of_lt_of_le ht' hXt
    have hnot : ¬ u < X G' ^ (-(1 / 2 : ℝ)) := by
      intro hin
      have h1 := sq_mul_lt_one hXpos hu.le hin
      have : u ^ 2 * t ≤ u ^ 2 * X G' := mul_le_mul_of_nonneg_left hXt (by positivity)
      exact htu (by nlinarith)
    simp only [Pi.zero_apply]
    exact indicator_of_notMem (by exact hnot) _

/-- `∫_{(0,1]} u^{r-1} du = 1/r`. -/
theorem lintegral_Ioc_rpow {r : ℝ} (hr : 0 < r) :
    (∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ (r - 1))) = ENNReal.ofReal (1 / r) := by
  have hi : IntegrableOn (fun u : ℝ => u ^ (r - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r - 1)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : -1 < r - 1))]
    congr 1
    rw [show r - 1 + 1 = r by ring, Real.one_rpow, Real.zero_rpow hr.ne']
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact Real.rpow_nonneg hu.1.le _

/-- `∫_{(1,∞)} u^a du = -1/(a+1)` for `a < -1`. -/
theorem lintegral_Ioi_rpow {a : ℝ} (ha : a < -1) :
    (∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (u ^ a)) = ENNReal.ofReal (-1 / (a + 1)) := by
  have hi : IntegrableOn (fun u : ℝ => u ^ a) (Ioi 1) := integrableOn_Ioi_rpow_of_lt ha one_pos
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_Ioi_rpow_of_lt ha one_pos, Real.one_rpow]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact Real.rpow_nonneg (zero_le_one.trans hu.le) _

/-- The good-event constant `1 + r K''/(2q/(q+1) - r)`. -/
def goodConst (s C c q r : ℝ) : ℝ :=
  1 + r * levelConst s C c q / (2 * (q / (q + 1)) - r)

/-- **Fixed-`θ` inverse spread on the good event**: for `0 < r < 2q/(q+1)`,
`E_{G'}[det² 1{sector α} 1_{𝒢_α}(θ) q_B^{-r}] ≤ (1 + rK''/(2q/(q+1) - r)) Σ_{ℓ=α-1}^{α+1} 𝔷_ℓ(θ)`. -/
theorem inner_good {q C r : ℝ}
    (hCq : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
      K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
        (∫⁻ x, ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) ∂sectorLaw m t K ℓ) ≤
          ENNReal.ofReal C * ((∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) ^ q)⁻¹)
    (hC : 0 ≤ C) (hq : 0 < q) (hr : 0 < r) (hrq : r < 2 * (q / (q + 1)))
    (α : Fin p.N) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian) (hv : l2Norm θ.2.2 = 1)
    {w : OuterData p i → (FrameIndex p → ℂ)} (hw : IsOuterEigenvector U w)
    {Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ} (hUw : IsMinorFrame Uw)
    (κ c : ℝ) (hc : 0 < c) :
    (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        (ind (fun θ' => SpreadGood α (splitS p) U κ c θ') θ *
          ENNReal.ofReal (minorQSq (splitS p) U w Uw θ G' ^ (-(r / 2))))
        ∂gueMeasure (FrameIndex p) (pairTime p (splitS p))) ≤
      ENNReal.ofReal (goodConst (splitS p) C c q r) *
        (zNat (splitS p) U (α.val - 1) θ + zNat (splitS p) U α.val θ +
          zNat (splitS p) U (α.val + 1) θ) := by
  set s := splitS p with hsdef
  set gue := gueMeasure (FrameIndex p) (pairTime p s) with hgue
  set Z3 := zNat s U (α.val - 1) θ + zNat s U α.val θ + zNat s U (α.val + 1) θ with hZ3
  by_cases hG : SpreadGood α s U κ c θ
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun G' => ?_)
    simp [ind, hG]
  have hind : ind (fun θ' => SpreadGood α s U κ c θ') θ = 1 := by simp [ind, hG]
  simp_rw [hind, one_mul]
  have ht : 0 < pairTime p s := pairTime_splitS_pos p
  have ht' : (0 : ℝ) < (pairTime p s : ℝ) := ht
  set sw := fun G' : FrameMatrix p => ENNReal.ofReal (sectorWeight α U θ G') with hswdef
  have hswm : Measurable sw := measurable_sectorWeight_G α hU.1 θ
  set μ := gue.withDensity sw with hμ
  set X := fun G' : FrameMatrix p => minorQSq s U w Uw θ G' with hXdef
  have hXm : Measurable X := measurable_minorQSq_G s U w Uw θ
  set f := fun G' : FrameMatrix p => X G' ^ (-(1 / 2 : ℝ)) with hfdef
  have hfm : Measurable f := hXm.pow_const _
  have haeG : ∀ᵐ G' ∂gue, (pairTime p s : ℝ) ≤ X G' := by
    filter_upwards [ae_isHermitian_gue (pairTime p s)] with G' hG'
    exact (minorQSq_ge s U hR hV w Uw hG').1
  have hae : ∀ᵐ G' ∂μ, (pairTime p s : ℝ) ≤ X G' :=
    (withDensity_absolutelyContinuous gue sw).ae_le haeG
  have e1 : (∫⁻ G', sw G' * ENNReal.ofReal (X G' ^ (-(r / 2))) ∂gue) =
      ∫⁻ G', ENNReal.ofReal (f G' ^ r) ∂μ := by
    have hm : Measurable fun G' => ENNReal.ofReal (f G' ^ r) :=
      ENNReal.measurable_ofReal.comp (hfm.pow_const r)
    rw [hμ, lintegral_withDensity_eq_lintegral_mul _ hswm hm]
    refine lintegral_congr_ae ?_
    filter_upwards [haeG] with G' h
    simp only [Pi.mul_apply, hfdef]
    rw [← Real.rpow_mul (ht'.le.trans h)]
    congr 3
    ring
  have hfnn : 0 ≤ᵐ[μ] f := by
    filter_upwards [hae] with G' h
    exact Real.rpow_nonneg (ht'.le.trans h) _
  have e2 := lintegral_rpow_eq_lintegral_meas_lt_mul μ hfnn hfm.aemeasurable hr
  -- the two level bounds
  have hlev1 : ∀ u : ℝ, μ {G' | u < f G'} ≤ Z3 := by
    intro u
    calc μ {G' | u < f G'} ≤ μ univ := measure_mono (subset_univ _)
      _ = zNat s U α.val θ := by
          rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
          rfl
      _ ≤ Z3 := le_add_right (le_add_left le_rfl)
  have hlev2 : ∀ u : ℝ, 0 < u →
      μ {G' | u < f G'} ≤ ENNReal.ofReal (levelConst s C c q * u ^ (-(2 * (q / (q + 1))))) * Z3 := by
    intro u hu
    rw [hμ, withDensity_apply _ (measurableSet_lt measurable_const hfm)]
    exact tail_level hCq hC hq α hU hR hV hv hw hUw κ c hc hG hu
  set β := q / (q + 1) with hβ
  set K := levelConst s C c q with hKdef
  have hK : 0 ≤ K := by
    have hs : 0 < s := BlockBand.Angular.PairCoareaBridge.splitS_pos p
    have : 0 ≤ C * (c ^ q)⁻¹ := mul_nonneg hC (inv_nonneg.mpr (Real.rpow_nonneg hc.le _))
    show 0 ≤ levelConst s C c q
    unfold levelConst
    have : 0 ≤ (4 / s ^ 2 + 2 / s) ^ (q / (q + 1)) := Real.rpow_nonneg (by positivity) _
    positivity
  have hgap : 0 < 2 * β - r := by linarith
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hm1 : Measurable fun u : ℝ => ENNReal.ofReal (u ^ (r - 1)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hm2 : Measurable fun u : ℝ => ENNReal.ofReal (u ^ (r - 1 - 2 * β)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have I1 : (∫⁻ u in Ioc (0 : ℝ) 1, μ {G' | u < f G'} * ENNReal.ofReal (u ^ (r - 1))) ≤
      Z3 * ENNReal.ofReal (1 / r) := by
    calc _ ≤ ∫⁻ u in Ioc (0 : ℝ) 1, Z3 * ENNReal.ofReal (u ^ (r - 1)) := by
          refine lintegral_mono fun u => ?_
          gcongr
          exact hlev1 u
      _ = _ := by rw [lintegral_const_mul _ hm1, lintegral_Ioc_rpow hr]
  have I2 : (∫⁻ u in Ioi (1 : ℝ), μ {G' | u < f G'} * ENNReal.ofReal (u ^ (r - 1))) ≤
      Z3 * (ENNReal.ofReal K * ENNReal.ofReal (1 / (2 * β - r))) := by
    calc _ ≤ ∫⁻ u in Ioi (1 : ℝ), Z3 * (ENNReal.ofReal K * ENNReal.ofReal (u ^ (r - 1 - 2 * β))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
          have hu0 : 0 < u := zero_lt_one.trans hu
          calc μ {G' | u < f G'} * ENNReal.ofReal (u ^ (r - 1))
              ≤ ENNReal.ofReal (K * u ^ (-(2 * β))) * Z3 * ENNReal.ofReal (u ^ (r - 1)) := by
                gcongr
                exact hlev2 u hu0
            _ = Z3 * (ENNReal.ofReal K * ENNReal.ofReal (u ^ (r - 1 - 2 * β))) := by
                have : K * u ^ (r - 1 - 2 * β) = K * u ^ (-(2 * β)) * u ^ (r - 1) := by
                  rw [mul_assoc, ← Real.rpow_add hu0]; ring_nf
                rw [← ENNReal.ofReal_mul hK, this,
                  ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg hu0.le _))]
                ring
      _ = _ := by
          rw [lintegral_const_mul _ (hm2.const_mul _), lintegral_const_mul _ hm2,
            lintegral_Ioi_rpow (by linarith : r - 1 - 2 * β < -1)]
          rw [show r - 1 - 2 * β + 1 = -(2 * β - r) by ring, div_neg, neg_div, neg_neg]
  calc (∫⁻ G', sw G' * ENNReal.ofReal (X G' ^ (-(r / 2))) ∂gue)
      = ENNReal.ofReal r * ∫⁻ u in Ioi 0, μ {G' | u < f G'} * ENNReal.ofReal (u ^ (r - 1)) := by
        rw [e1, e2]
    _ ≤ ENNReal.ofReal r * (Z3 * ENNReal.ofReal (1 / r) +
          Z3 * (ENNReal.ofReal K * ENNReal.ofReal (1 / (2 * β - r)))) := by
        rw [hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
        gcongr
    _ = ENNReal.ofReal (goodConst s C c q r) * Z3 := by
        rw [← mul_add, ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add (by positivity)
          (by positivity), mul_comm Z3, ← mul_assoc, ← ENNReal.ofReal_mul hr.le]
        congr 2
        unfold goodConst
        rw [← hKdef, ← hβ]
        field_simp
