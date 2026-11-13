module

public import BlockBand.DeterminantScore.RealLoopSector
public import BlockBand.DeterminantScore.MinorTailInversePair

/-!
# The physical real loop: completing the square and the good event

`physicalRealLoop_of_weightedTrace (hC : CoareaContract) (hWT : PhysicalWeightedTraceStatement) :
PhysicalRealLoopStatement`. The proof has three parts: (1) the physical weighted trace bound,
(2) the indexed Gaussian loop identity, (3) completing the square and Markov. This file proves
(2)–(3) and takes (1) as the named hypothesis `PhysicalWeightedTraceStatement`:

1. `PhysicalWeightedTraceStatement`: `E♯ 1{E ∈ I}|Tr G_dR − sE Tr R − (sd − 1)| ≤ C W^{49/50}`,
   with the quantifiers of `PhysicalRealLoopStatement.error`. In frame coordinates
   `Tr G_dR = Tr G'R` (`R` embedded by zero on `v`, `G' = U_v*G_dU_v`, `G_d` the reconstructed
   fresh Gaussian), so the integrand is `weightedTraceError`. It is proved in
   `physicalWeightedTrace_holds`, from `CoareaContract`, `PhysicalLocalWindowStatement` and
   `SelectedResolventStatement` (the local window applied to the cut-off deformation, the averaged
   local law at height `η = W^{-3/5}`, Gaussian integration by parts and `L^p` Poincaré for
   `Tr G_dR_η`, the centre bound and the score unsmoothing).
2. `gue_sector_loop` (unnormalized, from the sector integration by parts);
3. `realLoopError_mul_sectorZ`: at fixed Hermitian `θ` with `𝔷_ℓ(θ) ≠ 0`,
   `e_θ 𝔷_ℓ(θ) = ∫ w (Tr G'R − sE Tr R − (sd − 1))` (complete the square, `s = td`, `d = 2W`);
   `fiber_error_le` and `pairExpect_mono_fiber` then give `error` with the same constant
   (`|⟨X⟩_θ| ≤ ⟨|X|⟩_θ`); `realLoopError_le_of_bad`: on `{E ∈ I} \ 𝒢_α` with `c_b = κ/2`,
   `e_θ ≤ 1 − sκW/2` (the square is nonnegative and `1 − E²/4 ≥ κ/2` on `I`), so Markov gives
   `good` for `W ≥ 4/(sκ)`; for smaller `W` the pair law has mass `≤ 1` (`pairExpect_one_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.RealLoop

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.MinorTailInverse
open scoped NNReal ENNReal

variable {p : Parameters} {i : ZMod p.n}

/-- The integrand of the physical weighted trace bound, `Tr G_dR − sE Tr R − (sd − 1)` (`d = 2W`),
in the frame coordinates of `v^⊥`: with `R` embedded by zero on `v` and `G' = U_v*G_dU_v`,
`Tr G_dR = Tr G'R`. -/
def weightedTraceError (s : ℝ) (U : FrameMap p i) (θ : OuterData p i) (G' : FrameMatrix p) : ℝ :=
  (G' * (outerM U θ G')⁻¹).trace.re - s * θ.2.1 * invTrace U θ G' - (s * (2 * p.W) - 1)

/-- `sectorZ = ∫ sectorWeight` (the determinant factor is the unnormalized sector mass). -/
theorem sectorZ_eq_integral (α : Fin p.N) (s : ℝ) (U : FrameMap p i)
    (θ : OuterData p i) :
    sectorZ α s U θ = ∫ G', sectorWeight α U θ G' ∂gueMeasure (FrameIndex p) (pairTime p s) := by
  have hnn : ∀ G', 0 ≤ sectorWeight α U θ G' := fun G' => by
    rw [sectorWeight_eq]; exact secW_nonneg _ _ _
  have hm : Measurable fun G' => sectorWeight α U θ G' := by
    simp only [sectorWeight_eq, outerM_eq]
    exact (measurable_secW _ _).comp (measurable_const_add _)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hm.aestronglyMeasurable]
  unfold sectorZ detFactor
  congr 1
  refine lintegral_congr fun G' => ?_
  unfold sectorWeight outerM
  split_ifs <;> simp

theorem pairTime_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < pairTime p s := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  unfold pairTime
  exact Real.toNNReal_pos.mpr (by positivity)

theorem coe_pairTime_of_pos {s : ℝ} (hs : 0 < s) : (pairTime p s : ℝ) = s / (2 * p.W) := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  unfold pairTime
  exact Real.coe_toNNReal _ (by positivity)

theorem loop_algebra {Z A1 A2 A3 A4 t s d E : ℝ} (hZ : Z ≠ 0) (hts : t * d = s)
    (hloop : A4 = 2 * t * A3 - t * A2) :
    (2 * t * (A3 / Z) - t * ((A2 + d * E * A1 + (d * E / 2) ^ 2 * Z) / Z) -
      (s * d * (1 - E ^ 2 / 4) - 1)) * Z = A4 - s * E * A1 - (s * d - 1) * Z := by
  have k1 : A3 / Z * Z = A3 := div_mul_cancel₀ _ hZ
  have k2 : (A2 + d * E * A1 + (d * E / 2) ^ 2 * Z) / Z * Z =
      A2 + d * E * A1 + (d * E / 2) ^ 2 * Z := div_mul_cancel₀ _ hZ
  rw [hloop]
  linear_combination 2 * t * k1 - t * k2 + (-(E * A1 + d * E ^ 2 * Z / 4)) * hts

/-- **Completing the square at fixed `θ`** (from the indexed Gaussian loop identity, `s = td`): if
`𝔷_ℓ(θ) ≠ 0` then `e_θ 𝔷_ℓ(θ) = ∫ w(G') (Tr G'R − sE Tr R − (sd − 1)) dGUE(G')`, `w` the sector
weight. -/
theorem realLoopError_mul_sectorZ (α : Fin p.N) {s : ℝ} (hs : 0 < s) (U : FrameMap p i)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian)
    (hZ : sectorZ α s U θ ≠ 0) :
    realLoopError α s U θ * sectorZ α s U θ =
      ∫ G', sectorWeight α U θ G' * weightedTraceError s U θ G'
        ∂gueMeasure (FrameIndex p) (pairTime p s) := by
  have ht := pairTime_pos_of_pos (p := p) hs
  have htv := coe_pairTime_of_pos (p := p) hs
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  obtain ⟨i1, i2, i3, i4, i5, hloop⟩ :=
    gue_sector_loop (outerKs_isHermitian U hR hV) (nR θ) α.val ht
  have hZe := sectorZ_eq_integral α s U θ
  simp only [sectorWeight_eq, outerM_eq] at hZe
  set Z := sectorZ α s U θ
  set E := θ.2.1
  set μ := gueMeasure (FrameIndex p) (pairTime p s)
  set t : ℝ := (pairTime p s : ℝ)
  set d : ℝ := 2 * (p.W : ℝ)
  have hsq : (∫ G', secW (nR θ) α.val (outerKs U θ + G') *
      (((outerKs U θ + G')⁻¹).trace.re + d * E / 2) ^ 2 ∂μ) =
      (∫ G', secW (nR θ) α.val (outerKs U θ + G') * ((outerKs U θ + G')⁻¹).trace.re ^ 2 ∂μ) +
        (d * E) * (∫ G', secW (nR θ) α.val (outerKs U θ + G') *
          ((outerKs U θ + G')⁻¹).trace.re ∂μ) +
        (d * E / 2) ^ 2 * ∫ G', secW (nR θ) α.val (outerKs U θ + G') ∂μ := by
    calc _ = ∫ G', (secW (nR θ) α.val (outerKs U θ + G') * ((outerKs U θ + G')⁻¹).trace.re ^ 2 +
          (d * E) * (secW (nR θ) α.val (outerKs U θ + G') * ((outerKs U θ + G')⁻¹).trace.re)) +
          (d * E / 2) ^ 2 * secW (nR θ) α.val (outerKs U θ + G') ∂μ :=
          integral_congr_ae (ae_of_all _ fun G' => by ring)
      _ = _ := by
          have i32 : Integrable (fun G' => secW (nR θ) α.val (outerKs U θ + G') *
              ((outerKs U θ + G')⁻¹).trace.re ^ 2 + (d * E) * (secW (nR θ) α.val (outerKs U θ + G') *
                ((outerKs U θ + G')⁻¹).trace.re)) μ := i3.add (i2.const_mul _)
          rw [integral_add i32 (i1.const_mul _), integral_add i3
            (i2.const_mul _), integral_const_mul, integral_const_mul]
  have hX : (∫ G', sectorWeight α U θ G' * weightedTraceError s U θ G' ∂μ) =
      (∫ G', secW (nR θ) α.val (outerKs U θ + G') * (G' * (outerKs U θ + G')⁻¹).trace.re ∂μ) -
        (s * E) * (∫ G', secW (nR θ) α.val (outerKs U θ + G') *
          ((outerKs U θ + G')⁻¹).trace.re ∂μ) -
        (s * d - 1) * ∫ G', secW (nR θ) α.val (outerKs U θ + G') ∂μ := by
    calc _ = ∫ G', (secW (nR θ) α.val (outerKs U θ + G') * (G' * (outerKs U θ + G')⁻¹).trace.re -
          (s * E) * (secW (nR θ) α.val (outerKs U θ + G') * ((outerKs U θ + G')⁻¹).trace.re)) -
          (s * d - 1) * secW (nR θ) α.val (outerKs U θ + G') ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun G' => ?_)
          simp only [sectorWeight_eq, outerM_eq, weightedTraceError, invTrace]
          ring
      _ = _ := by
          have i52 : Integrable (fun G' => secW (nR θ) α.val (outerKs U θ + G') *
              (G' * (outerKs U θ + G')⁻¹).trace.re - (s * E) * (secW (nR θ) α.val (outerKs U θ + G') *
                ((outerKs U θ + G')⁻¹).trace.re)) μ := i5.sub (i2.const_mul _)
          rw [integral_sub i52 (i1.const_mul _), integral_sub i5
            (i2.const_mul _), integral_const_mul, integral_const_mul]
  rw [hX]
  unfold realLoopError sectorAvg
  simp only [sectorWeight_eq, outerM_eq, invSqTrace, invTrace]
  rw [hsq, ← hZe]
  have hts : t * d = s := by
    simp only [t, d, htv]; field_simp
  exact loop_algebra hZ hts hloop

theorem measurable_sectorWeight_ofReal (α : Fin p.N) (U : FrameMap p i) (θ : OuterData p i) :
    Measurable fun G' => ENNReal.ofReal (sectorWeight α U θ G') := by
  simp only [sectorWeight_eq, outerM_eq]
  exact ENNReal.measurable_ofReal.comp ((measurable_secW _ _).comp (measurable_const_add _))

/-- **Fiberwise real loop error from the physical weighted trace bound** (conditioning on `θ`,
`|⟨X⟩_θ| ≤ ⟨|X|⟩_θ`): at Hermitian exterior data, for every constant `a`,
`∫ w (a |e_θ|) ≤ ∫ w (a |Tr G'R − sE Tr R − (sd − 1)|)`. -/
theorem fiber_error_le (α : Fin p.N) {s : ℝ} (hs : 0 < s) (U : FrameMap p i)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian) (a : ℝ≥0∞) :
    (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        (a * ENNReal.ofReal |realLoopError α s U θ|) ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤
      ∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        (a * ENNReal.ofReal |weightedTraceError s U θ G'|)
        ∂gueMeasure (FrameIndex p) (pairTime p s) := by
  set μ := gueMeasure (FrameIndex p) (pairTime p s)
  have ht := pairTime_pos_of_pos (p := p) hs
  have hm := measurable_sectorWeight_ofReal α U θ
  have hnn : ∀ G', 0 ≤ sectorWeight α U θ G' := fun G' => by
    rw [sectorWeight_eq]; exact secW_nonneg _ _ _
  have hint : Integrable (fun G' => sectorWeight α U θ G') μ := by
    have h := (gue_sector_loop (outerKs_isHermitian U hR hV) (nR θ) α.val ht).1
    simpa only [sectorWeight_eq, outerM_eq] using h
  have hlin : (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') ∂μ) =
      ENNReal.ofReal (sectorZ α s U θ) := by
    rw [sectorZ_eq_integral, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)]
  have hZ0 : 0 ≤ sectorZ α s U θ := ENNReal.toReal_nonneg
  have core : ENNReal.ofReal |realLoopError α s U θ| * ENNReal.ofReal (sectorZ α s U θ) ≤
      ∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        ENNReal.ofReal |weightedTraceError s U θ G'| ∂μ := by
    by_cases hZ : sectorZ α s U θ = 0
    · simp [hZ]
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_of_nonneg hZ0, ← abs_mul,
      realLoopError_mul_sectorZ α hs U hR hV hZ]
    calc ENNReal.ofReal |∫ G', sectorWeight α U θ G' * weightedTraceError s U θ G' ∂μ|
        = ‖∫ G', sectorWeight α U θ G' * weightedTraceError s U θ G' ∂μ‖ₑ :=
          (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ G', ‖sectorWeight α U θ G' * weightedTraceError s U θ G'‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ = _ := lintegral_congr fun G' => by
          rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hnn G'),
            ENNReal.ofReal_mul (hnn G')]
  calc (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        (a * ENNReal.ofReal |realLoopError α s U θ|) ∂μ)
      = (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') ∂μ) *
          (a * ENNReal.ofReal |realLoopError α s U θ|) := lintegral_mul_const _ hm
    _ = a * (ENNReal.ofReal |realLoopError α s U θ| * ENNReal.ofReal (sectorZ α s U θ)) := by
        rw [hlin]; ring
    _ ≤ a * ∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
          ENNReal.ofReal |weightedTraceError s U θ G'| ∂μ := by gcongr
    _ ≤ ∫⁻ G', a * (ENNReal.ofReal (sectorWeight α U θ G') *
          ENNReal.ofReal |weightedTraceError s U θ G'|) ∂μ := lintegral_const_mul_le _ _
    _ = _ := lintegral_congr fun G' => by ring

/-- **Fiberwise monotonicity of `pairExpect`** on the support of the pair law (Hermitian
exterior blocks). -/
theorem pairExpect_mono_fiber {model : p.GaussianRingModel} {s : ℝ}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model s Pω) (α : Fin p.N)
    (U : FrameMap p i) {Ψ Φ : OuterData p i → FrameMatrix p → ℝ≥0∞}
    (h : ∀ θ : OuterData p i, θ.1.1.IsHermitian → θ.1.2.2.IsHermitian →
      (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') * Ψ θ G'
          ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤
        ∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') * Φ θ G'
          ∂gueMeasure (FrameIndex p) (pairTime p s)) :
    pairExpect α s U Pω Ψ ≤ pairExpect α s U Pω Φ := by
  unfold pairExpect
  refine lintegral_mono_ae ?_
  filter_upwards [ae_hermitian_of_isPairSplitting p i hPω] with om hom
  refine lintegral_mono fun E => lintegral_mono fun v => ?_
  simp only [mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul_right (h (om, E, v) hom.1 hom.2) _

theorem pairExpect_mono_pt (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (Pω : Measure (SplitState p i))
    {Ψ Φ : OuterData p i → FrameMatrix p → ℝ≥0∞} (h : ∀ θ G', Ψ θ G' ≤ Φ θ G') :
    pairExpect α s U Pω Ψ ≤ pairExpect α s U Pω Φ := by
  unfold pairExpect
  exact lintegral_mono fun _ => lintegral_mono fun _ => lintegral_mono fun _ =>
    lintegral_mono fun _ => by gcongr; exact h _ _

/-!
## The physical weighted trace and the reduction
-/

/-- **The physical weighted trace bound**, the first part of the proof of the physical real loop:
for `b, T, ϑ, κ` there is `C` with `E♯ 1{E ∈ I} |Tr G_dR − sE Tr R − (sd − 1)| ≤ C W^{49/50}`,
uniformly in `4 ≤ n ≤ TW`, models, `ϑ`-bulk ranks, pairs, splitting laws and frames (same
quantifiers as `PhysicalRealLoopStatement.error`). -/
def PhysicalWeightedTraceStatement : Prop :=
  ∀ b T ϑ κ : ℝ, 0 < ϑ → 0 < κ → ∃ C : ℝ, ∀ p : Parameters, p.b = b →
    (p.n : ℝ) ≤ T * (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
    ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
      pairExpect α (splitS p) U Pω (fun θ G' =>
          (bulkInterval κ).indicator 1 θ.2.1 *
            ENNReal.ofReal |weightedTraceError (splitS p) U θ G'|) ≤
        ENNReal.ofReal (C * (p.W : ℝ) ^ (49 / 50 : ℝ))

/-- The real loop error bound from the physical weighted trace bound (same constant). -/
theorem realLoop_error (hWT : PhysicalWeightedTraceStatement) :
    ∀ b T ϑ κ : ℝ, 0 < ϑ → 0 < κ → ∃ C : ℝ, ∀ p : Parameters, p.b = b →
    (p.n : ℝ) ≤ T * (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
    ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
      pairExpect α (splitS p) U Pω (fun θ _ =>
          (bulkInterval κ).indicator 1 θ.2.1 *
            ENNReal.ofReal |realLoopError α (splitS p) U θ|) ≤
        ENNReal.ofReal (C * (p.W : ℝ) ^ (49 / 50 : ℝ)) := by
  intro b T ϑ κ hϑ hκ
  obtain ⟨C, hC⟩ := hWT b T ϑ κ hϑ hκ
  refine ⟨C, fun p hb hn model α hα i Pω hPω U hU => ?_⟩
  refine le_trans ?_ (hC p hb hn model α hα i Pω hPω U hU)
  exact pairExpect_mono_fiber hPω α U fun θ hR hV =>
    fiber_error_le α (BlockBand.Angular.PairCoareaBridge.splitS_pos p) U hR hV _

theorem ind_le {X : Type*} {P : X → Prop} {x : X} {B : ℝ≥0∞} (h : P x → 1 ≤ B) : ind P x ≤ B := by
  unfold ind
  by_cases hx : P x
  · simpa [Set.indicator, hx] using h hx
  · simp [Set.indicator, hx]

theorem one_sub_sq_div_four_ge {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    κ / 2 ≤ 1 - E ^ 2 / 4 := by
  obtain ⟨h1, h2⟩ := hE
  have hk : κ ≤ 2 := by linarith
  have := mul_nonneg (sub_nonneg.2 h2) (by linarith : 0 ≤ E + (2 - κ))
  have := mul_nonneg hκ.le (sub_nonneg.2 hk)
  nlinarith

/-- On `{E ∈ I} \ 𝒢_α` (`c = κ/2`): `e_θ ≤ 1 - sκW/2` (the square is nonnegative, the
source `sd(1 - E²/4) ≥ sκW`). -/
theorem realLoopError_le_of_bad (α : Fin p.N) {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (U : FrameMap p i)
    {θ : OuterData p i} (hE : θ.2.1 ∈ bulkInterval κ)
    (hbad : ¬ SpreadGood α s U κ (κ / 2) θ) :
    realLoopError α s U θ ≤ 1 - s * κ * p.W / 2 := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have htv := coe_pairTime_of_pos (p := p) hs
  have hU : sectorAvg α s U (invSqTrace U θ) θ < κ / 2 * (p.W : ℝ) ^ 2 := by
    by_contra h
    exact hbad ⟨hE, not_lt.mp h⟩
  have hZ0 : 0 ≤ sectorZ α s U θ := ENNReal.toReal_nonneg
  have hsq : 0 ≤ sectorAvg α s U (fun G' => (invTrace U θ G' + 2 * p.W * θ.2.1 / 2) ^ 2) θ :=
    div_nonneg (integral_nonneg fun G' => mul_nonneg (by rw [sectorWeight_eq]; exact secW_nonneg _ _ _)
      (sq_nonneg _)) hZ0
  have hsrc := one_sub_sq_div_four_ge hκ hE
  unfold realLoopError
  simp only
  rw [htv]
  have ht0 : 0 ≤ s / (2 * p.W) := by positivity
  have h1 : 2 * (s / (2 * p.W)) * sectorAvg α s U (invSqTrace U θ) θ ≤
      2 * (s / (2 * p.W)) * (κ / 2 * (p.W : ℝ) ^ 2) := by
    gcongr
  have h2 : 2 * (s / (2 * p.W)) * (κ / 2 * (p.W : ℝ) ^ 2) = s * κ * p.W / 2 := by
    field_simp
  have h3 : s * (2 * p.W) * (κ / 2) ≤ s * (2 * p.W) * (1 - θ.2.1 ^ 2 / 4) := by
    gcongr
  have h4 := mul_nonneg ht0 hsq
  nlinarith

/-- **The physical real loop** (`PhysicalRealLoopStatement`) from the physical weighted trace
bound, under `CoareaContract` (only for `pairExpect_one_le`, the pair law has mass at most one).
`error` has the constant of the weighted trace bound; `good` takes `c_b = κ/2` and
`C = max(4C₁/(s_bκ), (4/(s_bκ))^{1/50})`, `s_b = min(1 - 2b, b)`, by Markov. -/
theorem physicalRealLoop_of_weightedTrace (hC : CoareaContract)
    (hWT : PhysicalWeightedTraceStatement) : PhysicalRealLoopStatement where
  error := realLoop_error hWT
  good := by
    intro b κ hκ
    refine ⟨κ / 2, by positivity, fun T ϑ hϑ => ?_⟩
    obtain ⟨C₁, hC₁⟩ := realLoop_error hWT b T ϑ κ hϑ hκ
    set sb := min (1 - 2 * b) b
    refine ⟨max (4 * C₁ / (sb * κ)) ((4 / (sb * κ)) ^ (1 / 50 : ℝ)), ?_⟩
    intro p hb hn model α hα i Pω hPω U hU
    have hs : splitS p = sb := by unfold splitS Parameters.c; rw [hb]
    have hsp := BlockBand.Angular.PairCoareaBridge.splitS_pos p
    have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
    have hE := hC₁ p hb hn model α hα i Pω hPω U hU
    rw [← hs]
    set s := splitS p
    have hWr : 0 < (p.W : ℝ) ^ (-(1 / 50 : ℝ)) := Real.rpow_pos_of_pos hW _
    have hsk : 0 < s * κ := mul_pos hsp hκ
    by_cases hbig : 4 / (s * κ) ≤ p.W
    · have hskW : 4 ≤ s * κ * p.W := by
        rw [div_le_iff₀ hsk] at hbig; linarith
      have hpt : ∀ (θ : OuterData p i) (_ : FrameMatrix p),
          ind (fun θ' => θ'.2.1 ∈ bulkInterval κ ∧ ¬ SpreadGood α s U κ (κ / 2) θ') θ ≤
            ENNReal.ofReal (4 / (s * κ * p.W)) * ((bulkInterval κ).indicator 1 θ.2.1 *
              ENNReal.ofReal |realLoopError α s U θ|) := by
        intro θ _
        refine ind_le fun hθ => ?_
        have hle := realLoopError_le_of_bad α hsp hκ U hθ.1 hθ.2
        rw [Set.indicator_of_mem hθ.1, Pi.one_apply, one_mul,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have habs : s * κ * p.W / 4 ≤ |realLoopError α s U θ| :=
          le_abs.mpr (Or.inr (by linarith))
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith
      calc _ ≤ pairExpect α s U Pω (fun θ _ => ENNReal.ofReal (4 / (s * κ * p.W)) *
            ((bulkInterval κ).indicator 1 θ.2.1 * ENNReal.ofReal |realLoopError α s U θ|)) :=
            pairExpect_mono_pt α s U Pω hpt
        _ = ENNReal.ofReal (4 / (s * κ * p.W)) * pairExpect α s U Pω (fun θ _ =>
            (bulkInterval κ).indicator 1 θ.2.1 * ENNReal.ofReal |realLoopError α s U θ|) :=
            pairExpect_const_mul α s U Pω ENNReal.ofReal_ne_top _
        _ ≤ ENNReal.ofReal (4 / (s * κ * p.W)) *
            ENNReal.ofReal (C₁ * (p.W : ℝ) ^ (49 / 50 : ℝ)) := by gcongr
        _ = ENNReal.ofReal (4 / (s * κ * p.W) * (C₁ * (p.W : ℝ) ^ (49 / 50 : ℝ))) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            have hrw : (p.W : ℝ) ^ (49 / 50 : ℝ) = p.W * (p.W : ℝ) ^ (-(1 / 50 : ℝ)) := by
              rw [show (49 / 50 : ℝ) = 1 + (-(1 / 50 : ℝ)) by norm_num, Real.rpow_add hW,
                Real.rpow_one]
            have heq : 4 / (s * κ * p.W) * (C₁ * (p.W : ℝ) ^ (49 / 50 : ℝ)) =
                4 * C₁ / (s * κ) * (p.W : ℝ) ^ (-(1 / 50 : ℝ)) := by
              rw [hrw]; field_simp
            rw [heq]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) hWr.le
    · have hlt : (p.W : ℝ) < 4 / (s * κ) := not_le.mp hbig
      calc _ ≤ pairExpect α s U Pω (fun _ _ => 1) :=
            pairExpect_mono_pt α s U Pω fun θ _ => ind_le fun _ => le_rfl
        _ ≤ 1 := pairExpect_one_le hC hPω hU α
        _ ≤ _ := by
            rw [← ENNReal.ofReal_one]
            apply ENNReal.ofReal_le_ofReal
            have h1 : (p.W : ℝ) ^ (1 / 50 : ℝ) ≤ (4 / (s * κ)) ^ (1 / 50 : ℝ) :=
              Real.rpow_le_rpow hW.le hlt.le (by norm_num)
            have h2 : 0 < (p.W : ℝ) ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos hW _
            have h3 : (4 / (s * κ)) ^ (1 / 50 : ℝ) * (p.W : ℝ) ^ (-(1 / 50 : ℝ)) =
                (4 / (s * κ)) ^ (1 / 50 : ℝ) / (p.W : ℝ) ^ (1 / 50 : ℝ) := by
              rw [Real.rpow_neg hW.le, ← div_eq_mul_inv]
            calc (1 : ℝ) ≤ (4 / (s * κ)) ^ (1 / 50 : ℝ) / (p.W : ℝ) ^ (1 / 50 : ℝ) :=
                  (one_le_div h2).mpr h1
              _ = _ := h3.symm
              _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hWr.le

end BlockBand.DeterminantScore.RealLoop
