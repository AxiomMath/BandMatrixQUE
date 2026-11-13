module

public import BlockBand.DeterminantScore.ScoreMomentsRow
public import BlockBand.DeterminantScore.MinorTailInverse

/-!
# Moments of the diagonal inverse entry `w*Rw` under the pair law

**`cornerMoment_holds`**: for `b, T, ϑ, κ` and `0 < r < 2` there is `C` such that for
`4 ≤ n ≤ TW`, every model, `ϑ`-bulk rank `α`, pair, splitting law, pair frame, measurable unit
eigenvector `w(θ)` of `K` (`IsOuterEigenvector`) and minor frame (`IsMinorFrame`):
`E♯_{α,S} 1{E ∈ I} |w*Rw|^r ≤ C`, `R = M⁻¹` in frame coordinates.

Proof. At fixed outer data, `ScoreMoments.corner_gue` bounds the selected numerator by the three
neighbouring sector numerators of `q_B^{-r}` (`corner_fixed`), and `pairExpect_restore_le`
integrates this over the outer data, giving `Σ_{β ∈ {α-1, α, α+1}} E♯_β 1{E ∈ I} q_B^{-r}`.
If `ϑN ≥ 2` the neighbours are `ϑ/2`-bulk (`bulk_neighbour`) and
`PhysicalMinorTailStatement.inverse_spread` at `ϑ/2` applies; otherwise `W < 2/ϑ` and the
diagonal floor `q_B² ≥ t = s/(2W)` (`MinorTailInverse.minorQSq_ge`) with mass at most one
(`pairExpect_one_le`) gives `(2W/s)^{r/2} ≤ (4/(sϑ))^{r/2}`. The top neighbour `α + 1` is a
rank since `α` is bulk.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.ScoreMoments

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.MinorTail
open BlockBand.DeterminantScore.MinorTailInverse
open scoped NNReal ENNReal

variable {p : Parameters} {i : ZMod p.n}

/-!
## Outer integration of a fixed-`θ` restoration
-/

/-- **Restoration under the pair law.** If at every outer point of the support the selected
`G'`-integral of `Ψ` is at most the sum of three sector integrals of a jointly measurable `Φ`,
then `E♯_α Ψ ≤ Σ_j E♯_{β_j} Φ`. -/
theorem pairExpect_restore_le {model : p.GaussianRingModel} {s : ℝ}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model s Pω)
    {U : FrameMap p i} (hU : Measurable U) (α β₁ β₂ β₃ : Fin p.N)
    (Ψ Φ : OuterData p i → FrameMatrix p → ℝ≥0∞)
    (hΦ : Measurable fun z : OuterData p i × FrameMatrix p => Φ z.1 z.2)
    (h : ∀ θ : OuterData p i, θ.1.1.IsHermitian → θ.1.2.2.IsHermitian → l2Norm θ.2.2 = 1 →
      (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') * Ψ θ G'
          ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤
        ∫⁻ G', (ENNReal.ofReal (sectorWeight β₁ U θ G') + ENNReal.ofReal (sectorWeight β₂ U θ G') +
          ENNReal.ofReal (sectorWeight β₃ U θ G')) * Φ θ G'
          ∂gueMeasure (FrameIndex p) (pairTime p s)) :
    pairExpect α s U Pω Ψ ≤
      pairExpect β₁ s U Pω Φ + pairExpect β₂ s U Pω Φ + pairExpect β₃ s U Pω Φ := by
  have := isProbabilityMeasure_gue (FrameIndex p) (pairTime p s)
  have hj : ∀ β : Fin p.N, Measurable fun z : OuterData p i × FrameMatrix p =>
      ENNReal.ofReal (angularWeight p i s z.1.1 z.1.2.1 z.1.2.2) *
        ENNReal.ofReal (sectorWeight β U z.1 z.2) * Φ z.1 z.2 := fun β =>
    ((ENNReal.measurable_ofReal.comp ((measurable_angularWeight s).comp measurable_fst)).mul
      (measurable_sectorWeight β hU)).mul hΦ
  set g : Fin p.N → OuterData p i → ℝ≥0∞ := fun β θ => ∫⁻ G',
    ENNReal.ofReal (angularWeight p i s θ.1 θ.2.1 θ.2.2) * ENNReal.ofReal (sectorWeight β U θ G') *
      Φ θ G' ∂gueMeasure (FrameIndex p) (pairTime p s) with hg
  have hmg : ∀ β, Measurable (g β) := fun β => (hj β).lintegral_prod_right'
  have hgG : ∀ β (θ : OuterData p i), Measurable fun G' : FrameMatrix p =>
      ENNReal.ofReal (sectorWeight β U θ G') * Φ θ G' := fun β θ =>
    (measurable_sectorWeight_G β hU θ).mul (hΦ.comp measurable_prodMk_left)
  have hgβ : ∀ β, pairExpect β s U Pω Φ = outerInt Pω (g β) := fun β => rfl
  have step : pairExpect α s U Pω Ψ ≤ outerInt Pω (fun θ => g β₁ θ + g β₂ θ + g β₃ θ) := by
    unfold pairExpect outerInt
    refine lintegral_mono_ae ?_
    filter_upwards [ae_hermitian_of_isPairSplitting p i hPω] with om hom
    refine lintegral_mono fun E => ?_
    refine lintegral_mono_ae ?_
    filter_upwards [BlockBand.Angular.ProjectiveStein.ae_projectiveHaar_unit
      (ι := PairSite p i)] with v hv
    have hl2 := l2Norm_of_normSqSum hv
    set a := ENNReal.ofReal (angularWeight p i s om E v)
    have ha : a ≠ ⊤ := ENNReal.ofReal_ne_top
    have hgi : ∀ β, g β (om, E, v) = a * ∫⁻ G', ENNReal.ofReal (sectorWeight β U (om, E, v) G') *
        Φ (om, E, v) G' ∂gueMeasure (FrameIndex p) (pairTime p s) := by
      intro β
      rw [hg, ← lintegral_const_mul' _ _ ha]
      exact lintegral_congr fun G' => by ring
    calc (∫⁻ G', a * ENNReal.ofReal (sectorWeight α U (om, E, v) G') * Ψ (om, E, v) G'
          ∂gueMeasure (FrameIndex p) (pairTime p s))
        = a * ∫⁻ G', ENNReal.ofReal (sectorWeight α U (om, E, v) G') * Ψ (om, E, v) G'
          ∂gueMeasure (FrameIndex p) (pairTime p s) := by
          rw [← lintegral_const_mul' _ _ ha]
          exact lintegral_congr fun G' => by ring
      _ ≤ a * ∫⁻ G', (ENNReal.ofReal (sectorWeight β₁ U (om, E, v) G') +
            ENNReal.ofReal (sectorWeight β₂ U (om, E, v) G') +
            ENNReal.ofReal (sectorWeight β₃ U (om, E, v) G')) * Φ (om, E, v) G'
          ∂gueMeasure (FrameIndex p) (pairTime p s) := by
          exact mul_le_mul' le_rfl (h (om, E, v) hom.1 hom.2 hl2)
      _ = g β₁ (om, E, v) + g β₂ (om, E, v) + g β₃ (om, E, v) := by
          rw [hgi, hgi, hgi]
          simp only [add_mul]
          have hm12 : Measurable fun G' : FrameMatrix p =>
              ENNReal.ofReal (sectorWeight β₁ U (om, E, v) G') * Φ (om, E, v) G' +
                ENNReal.ofReal (sectorWeight β₂ U (om, E, v) G') * Φ (om, E, v) G' :=
            (hgG β₁ _).add (hgG β₂ _)
          rw [lintegral_add_left hm12, lintegral_add_left (hgG β₁ _)]
          ring
  calc _ ≤ _ := step
    _ = outerInt Pω (g β₁) + outerInt Pω (g β₂) + outerInt Pω (g β₃) := by
        rw [outerInt_add Pω (g β₃) (f := fun θ => g β₁ θ + g β₂ θ) ((hmg β₁).add (hmg β₂)),
          outerInt_add Pω (g β₂) (hmg β₁)]
    _ = _ := by rw [hgβ, hgβ, hgβ]

/-!
## The fixed-`θ` corner bound
-/

/-- The corner integrand `1{E ∈ I}|w*Rw|^r`. -/
def cornerObs (κ r : ℝ) (U : FrameMap p i) (w : OuterData p i → (FrameIndex p → ℂ))
    (θ : OuterData p i) (G' : FrameMatrix p) : ℝ≥0∞ :=
  (bulkInterval κ).indicator 1 θ.2.1 *
    ENNReal.ofReal (‖star (w θ) ⬝ᵥ ((outerM U θ G')⁻¹ *ᵥ w θ)‖ ^ r)

/-- The restored integrand `1{E ∈ I} q_B^{-r}` of the physical inverse-spread bound. -/
def spreadObs (κ r s : ℝ) (U : FrameMap p i) (w : OuterData p i → (FrameIndex p → ℂ))
    (Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ)
    (θ : OuterData p i) (G' : FrameMatrix p) : ℝ≥0∞ :=
  (bulkInterval κ).indicator 1 θ.2.1 * ENNReal.ofReal (minorQSq s U w Uw θ G' ^ (-(r / 2)))

theorem star_dot_self_of_l2Norm {ι : Type} [Fintype ι] [DecidableEq ι] {x : ι → ℂ} (hx : l2Norm x = 1) :
    star x ⬝ᵥ x = 1 := by
  rw [← ofReal_sum_norm_sq, ← l2Norm_sq', hx]; simp

/-- **Fixed-`θ` corner bound.** At fixed outer data, the selected integral of `1{E ∈ I}|w*Rw|^r` is
at most the three neighbouring sector integrals of `1{E ∈ I} q_B^{-r}`. -/
theorem corner_fixed (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian) (hv : l2Norm θ.2.2 = 1)
    {w : OuterData p i → (FrameIndex p → ℂ)} (hw : IsOuterEigenvector U w)
    {Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ} (hUw : IsMinorFrame Uw)
    (ht : 0 < pairTime p s) (κ : ℝ) {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2)
    (β₁ β₂ β₃ : Fin p.N) (h₁ : β₁.val = α.val - 1) (h₂ : β₂ = α) (h₃ : β₃.val = α.val + 1) :
    (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') * cornerObs κ r U w θ G'
        ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤
      ∫⁻ G', (ENNReal.ofReal (sectorWeight β₁ U θ G') + ENNReal.ofReal (sectorWeight β₂ U θ G') +
        ENNReal.ofReal (sectorWeight β₃ U θ G')) * spreadObs κ r s U w Uw θ G'
        ∂gueMeasure (FrameIndex p) (pairTime p s) := by
  subst β₂
  set t := pairTime p s
  set K := outerKs U θ
  have hK : K.IsHermitian := outerKs_isHermitian U hR hV
  have hM : ∀ G', outerM U θ G' = K + G' := outerM_eq U θ
  have hKH : (outerK U θ).IsHermitian := by
    rw [← outerKs_eq_outerK hU hv]; exact hK
  obtain ⟨hw1, μ, hμ⟩ := hw.2 θ hv hKH
  set V := Uw (w θ)
  obtain ⟨hVV, hVw⟩ := hUw.2 (w θ) hw1
  have hKw : K *ᵥ w θ = ((μ : ℝ) : ℂ) • w θ := by
    change outerKs U θ *ᵥ w θ = _
    rw [outerKs_eq_outerK hU hv]; exact hμ
  have hmk : 2 * p.W - 1 = (2 * p.W - 2) + 1 := by have := p.W_pos; omega
  have hfin := frameIndex_neZero p
  have hrow : rowMean U w θ = μ := by
    unfold rowMean
    rw [hμ, dotProduct_smul, star_dot_self_of_l2Norm hw1, smul_eq_mul, mul_one,
      Complex.ofReal_re]
  set ind := (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) θ.2.1
  have hcor := corner_gue hmk hK ht hw1 hKw hVV hVw (nR θ) α.val hr0 hr2
  have hL : (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') * cornerObs κ r U w θ G'
      ∂gueMeasure (FrameIndex p) t) =
      ind * ∫⁻ G', cornerW (w θ) (nR θ) α.val r (K + G') ∂gueMeasure (FrameIndex p) t := by
    rw [← lintegral_const_mul' _ _ (by simp [ind, Set.indicator]; split_ifs <;> simp)]
    refine lintegral_congr fun G' => ?_
    simp only [cornerObs, cornerW, sectorWeight_eq, hM]
    ring
  have hR' : (∫⁻ G', (ENNReal.ofReal (sectorWeight ⟨α.val - 1, by omega⟩ U θ G') +
      ENNReal.ofReal (sectorWeight α U θ G') +
      ENNReal.ofReal (sectorWeight β₃ U θ G')) * spreadObs κ r s U w Uw θ G'
      ∂gueMeasure (FrameIndex p) t) =
      ind * ∫⁻ G', restoreW V (nR θ) α.val t μ r (K + G') ∂gueMeasure (FrameIndex p) t := by
    rw [← lintegral_const_mul' _ _ (by simp [ind, Set.indicator]; split_ifs <;> simp)]
    refine lintegral_congr fun G' => ?_
    have hq : minorQSq s U w Uw θ G' = qMinorSq (t : ℝ) μ (Vᴴ * (K + G') * V) := by
      unfold minorQSq qMinorSq minorV minorB invSq
      rw [hrow, hM]
    simp only [spreadObs, restoreW, sectorWeight_eq, hM, hq, h₃]
    ring
  have hβ₁ : β₁ = ⟨α.val - 1, by omega⟩ := Fin.ext h₁
  rw [hβ₁, hL, hR']
  exact mul_le_mul' le_rfl hcor

/-!
## Neighbouring bulk ranks
-/

theorem succ_lt_of_bulk {ϑ : ℝ} (hϑ : 0 < ϑ) {α : Fin p.N} (hα : IsBulkRank p ϑ α) :
    α.val + 1 < p.N := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have h := hα.2
  rw [div_le_iff₀ hN] at h
  have : ((α.val + 1 : ℕ) : ℝ) < p.N := by nlinarith
  exact_mod_cast this

theorem bulk_neighbour {ϑ : ℝ} {α : Fin p.N} (hα : IsBulkRank p ϑ α)
    (hN : 2 ≤ ϑ * p.N) (β : Fin p.N) (hlo : α.val ≤ β.val + 1) (hhi : β.val ≤ α.val + 1) :
    IsBulkRank p (ϑ / 2) β := by
  have hNp : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  obtain ⟨h1, h2⟩ := hα
  rw [le_div_iff₀ hNp] at h1
  rw [div_le_iff₀ hNp] at h2
  have hlo' : ((α.val + 1 : ℕ) : ℝ) ≤ ((β.val + 1 : ℕ) : ℝ) + 1 := by
    push_cast; exact_mod_cast (by omega : α.val + 1 ≤ β.val + 1 + 1)
  have hhi' : ((β.val + 1 : ℕ) : ℝ) ≤ ((α.val + 1 : ℕ) : ℝ) + 1 := by
    push_cast; exact_mod_cast (by omega : β.val + 1 ≤ α.val + 1 + 1)
  constructor
  · rw [le_div_iff₀ hNp]; nlinarith
  · rw [div_le_iff₀ hNp]; nlinarith

/-!
## The corner moment
-/

/-- The crude constant `(4/(sϑ))^{r/2}` for `ϑN < 2`. -/
def crudeConst (b ϑ r : ℝ) : ℝ := (2 / min (1 - 2 * b) b) ^ (r / 2) * (2 / ϑ) ^ (r / 2)

/-- The crude bound `E♯_β 1{E ∈ I} q_B^{-r} ≤ (2W/s)^{r/2}` from the diagonal floor `q_B² ≥ t`. -/
theorem spread_crude (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (β : Fin p.N) (κ : ℝ) {r : ℝ} (hr0 : 0 < r)
    (w : OuterData p i → (FrameIndex p → ℂ))
    (Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ) :
    pairExpect β (splitS p) U Pω (spreadObs κ r (splitS p) U w Uw) ≤
      ENNReal.ofReal ((2 / splitS p) ^ (r / 2) * (p.W : ℝ) ^ (r / 2)) := by
  set t := pairTime p (splitS p)
  have htpos := pairTime_splitS_pos p
  have htpos' : (0 : ℝ) < t := htpos
  calc pairExpect β (splitS p) U Pω (spreadObs κ r (splitS p) U w Uw)
      ≤ pairExpect β (splitS p) U Pω (fun _ _ => ENNReal.ofReal (((t : ℝ)⁻¹) ^ (r / 2)) * 1) := by
        refine pairExpect_mono_ae hPω β U fun θ hR hV _ _ => ?_
        filter_upwards [ae_isHermitian_gue t] with G' hG' _
        have hq := (minorQSq_ge (splitS p) U hR hV w Uw hG').1
        have hqpos : 0 < minorQSq (splitS p) U w Uw θ G' := lt_of_lt_of_le htpos' hq
        rw [mul_one]
        unfold spreadObs
        refine le_trans (mul_le_of_le_one_left zero_le ?_) ?_
        · simp only [Set.indicator]; split_ifs <;> simp
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.rpow_neg hqpos.le, ← Real.inv_rpow hqpos.le]
        exact Real.rpow_le_rpow (inv_nonneg.mpr hqpos.le) (inv_anti₀ htpos' hq) (by linarith)
    _ = ENNReal.ofReal (((t : ℝ)⁻¹) ^ (r / 2)) * pairExpect β (splitS p) U Pω (fun _ _ => 1) :=
        pairExpect_const_mul β _ U Pω ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal (((t : ℝ)⁻¹) ^ (r / 2)) * 1 := by
        gcongr; exact pairExpect_one_le hC hPω hU β
    _ = _ := by rw [mul_one, inv_pairTime_rpow p r]

/-- **The corner moment** `E♯_α 1{E ∈ I}|w*Rw|^r ≤ C`, uniformly in the model, the bulk rank and the frames. -/
theorem cornerMoment_holds (hC : CoareaContract) (hMT : PhysicalMinorTailStatement) :
    ∀ b T ϑ κ r : ℝ, 0 < ϑ → 0 < κ → 0 < r → r < 2 → ∃ C : ℝ,
      ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
      ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
      ∀ U : FrameMap p i, IsPairFrame p i U →
      ∀ w : OuterData p i → (FrameIndex p → ℂ), IsOuterEigenvector U w →
      ∀ Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ, IsMinorFrame Uw →
        pairExpect α (splitS p) U Pω (fun θ G' =>
            (bulkInterval κ).indicator 1 θ.2.1 *
              ENNReal.ofReal (‖star (w θ) ⬝ᵥ ((outerM U θ G')⁻¹ *ᵥ w θ)‖ ^ r)) ≤
          ENNReal.ofReal C := by
  intro b T ϑ κ r hϑ hκ hr0 hr2
  obtain ⟨C₁, hC₁⟩ := hMT.inverse_spread b T (ϑ / 2) κ r (by linarith) hκ hr0 hr2
  refine ⟨3 * (max C₁ 0 + crudeConst b ϑ r), ?_⟩
  intro p hb hn model α hα i Pω hPω U hU w hw Uw hUw
  have hC₂ : 0 ≤ crudeConst b ϑ r := by
    unfold crudeConst
    have hsb : 0 < min (1 - 2 * b) b := by
      rw [← hb]; exact lt_min (by linarith [p.b_lt_half]) p.b_pos
    exact mul_nonneg (Real.rpow_nonneg (div_pos two_pos hsb).le _)
      (Real.rpow_nonneg (by positivity) _)
  have hlt := succ_lt_of_bulk hϑ hα
  set β₁ : Fin p.N := ⟨α.val - 1, by omega⟩
  set β₃ : Fin p.N := ⟨α.val + 1, hlt⟩
  have hΦ : Measurable fun z : OuterData p i × FrameMatrix p =>
      spreadObs κ r (splitS p) U w Uw z.1 z.2 := by
    unfold spreadObs
    exact ((measurable_one.indicator measurableSet_Icc).comp
      (measurable_fst.comp measurable_snd |>.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp
        ((measurable_minorQSq (splitS p) hU.1 hw.1 hUw.1).pow_const _))
  have hmain := pairExpect_restore_le hPω hU.1 α β₁ α β₃ (cornerObs κ r U w)
    (spreadObs κ r (splitS p) U w Uw) hΦ (fun θ hR hV hv =>
      corner_fixed α (splitS p) hU hR hV hv hw hUw (pairTime_splitS_pos p) κ hr0 hr2 β₁ α β₃
        rfl rfl rfl)
  -- each neighbour term is at most `max C₁ 0 + crudeConst`
  have hterm : ∀ β : Fin p.N, α.val ≤ β.val + 1 → β.val ≤ α.val + 1 →
      pairExpect β (splitS p) U Pω (spreadObs κ r (splitS p) U w Uw) ≤
        ENNReal.ofReal (max C₁ 0 + crudeConst b ϑ r) := by
    intro β hlo hhi
    by_cases hN : 2 ≤ ϑ * p.N
    · refine le_trans (hC₁ p hb hn model β (bulk_neighbour hα hN β hlo hhi) i Pω hPω U hU
        w hw Uw hUw) (ENNReal.ofReal_le_ofReal ?_)
      linarith [le_max_left C₁ 0]
    · refine le_trans (spread_crude hC hPω hU β κ hr0 w Uw) (ENNReal.ofReal_le_ofReal ?_)
      have hW : (p.W : ℝ) ≤ 2 / ϑ := by
        have hWN : (p.W : ℝ) ≤ p.N := by
          have : p.W ≤ p.N := by
            unfold Parameters.N; exact Nat.le_mul_of_pos_left _ p.n_pos
          exact_mod_cast this
        rw [le_div_iff₀ hϑ]; have hN' := not_le.mp hN; nlinarith
      have hs : splitS p = min (1 - 2 * b) b := by
        unfold splitS Parameters.c; rw [hb]
      have hle : (2 / splitS p) ^ (r / 2) * (p.W : ℝ) ^ (r / 2) ≤ crudeConst b ϑ r := by
        unfold crudeConst
        rw [← hs]
        have hsp := BlockBand.Angular.PairCoareaBridge.splitS_pos p
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hW (by linarith))
          (Real.rpow_nonneg (by positivity) _)
      linarith [le_max_right C₁ 0]
  have e3 : (3 : ℝ≥0∞) * ENNReal.ofReal (max C₁ 0 + crudeConst b ϑ r) =
      ENNReal.ofReal (3 * (max C₁ 0 + crudeConst b ϑ r)) := three_mul_ofReal _
  calc _ = pairExpect α (splitS p) U Pω (cornerObs κ r U w) := rfl
    _ ≤ _ := hmain
    _ ≤ ENNReal.ofReal (max C₁ 0 + crudeConst b ϑ r) +
        ENNReal.ofReal (max C₁ 0 + crudeConst b ϑ r) +
        ENNReal.ofReal (max C₁ 0 + crudeConst b ϑ r) := by
        gcongr
        · exact hterm β₁ (by simp [β₁]; omega) (by simp [β₁]; omega)
        · exact hterm α (by omega) (by omega)
        · exact hterm β₃ (by simp [β₃]; omega) (by simp [β₃])
    _ = _ := by rw [← e3]; ring

end BlockBand.DeterminantScore.ScoreMoments
