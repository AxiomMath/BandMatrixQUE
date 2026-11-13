module

public import BlockBand.SourceProcess.PhysApprox.B3BoundCovMean
public import BlockBand.SourceProcess.PhysApprox.B3LayerKMean
public import BlockBand.SourceProcess.PhysApprox.B3BoundJet

/-!
# `B3ClosedKLayerMean2` from the closed `δ₀` jet at `p = 2`

**`b3ClosedKLayerMean2_of_jet : GaussianAbsorptionContract → GaussianLpGradient →
ClosedJet0LpLe P → 2 ≤ P → B3ClosedKLayerMean2`** (proved). `ClosedJet0LpLe` is the bounded
jet statement, used at `p = 2`. The proof is that of
`b3ClosedKLayerMean_of_jet` with the `L⁶` bound of the error field
`err = 1_{A_j}(δ₀(X_cl) + W⁻¹)` replaced by its `L²` bound, and the arithmetic
`kLayer_arith2` (the pointwise bound `C₂ err·S_j + R C₁(err² + W^{-3/2})` never used
the sixth power: `kLayer_arith` added it as a nonnegative term). The lemmas
(`kStopStep_ae_eq_bilinear`, `integrable_b3_of_fresh_ae`, `kLayer_inv_sq_le`) are reused.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ClosedLimit
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.PhysApprox.ClosedForm
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W np K : ℕ}

/-- The arithmetic of the pointwise bound (`kLayer_arith` without the sixth power). -/
theorem kLayer_arith2 {C C1 C2 Cf δ w S : ℝ} (hC : 0 ≤ C) (hCa : C2 ≤ C) (hCb : Cf ^ 2 * C1 ≤ C)
    (hδ : 0 ≤ δ) (hS : 0 ≤ S) (hw : 0 ≤ w) {w2 κ : ℝ} (hw2 : w2 ≤ w)
    (hw2' : w2 ≤ κ) (hw20 : 0 ≤ w2) :
    Cf ^ 2 * (C1 * (δ ^ 2 + w2)) + C2 * (δ + w2) * S ≤
      C * ((δ + w) * S + (δ + w) ^ 2 + κ) := by
  have t1 : Cf ^ 2 * (C1 * (δ ^ 2 + w2)) ≤ C * ((δ + w) ^ 2 + κ) := by
    have h1 : δ ^ 2 + w2 ≤ (δ + w) ^ 2 + κ :=
      add_le_add (pow_le_pow_left₀ hδ (by linarith) 2) hw2'
    calc Cf ^ 2 * (C1 * (δ ^ 2 + w2)) = (Cf ^ 2 * C1) * (δ ^ 2 + w2) := by ring
      _ ≤ C * ((δ + w) ^ 2 + κ) :=
        mul_le_mul hCb h1 (by positivity) hC
  have t2 : C2 * (δ + w2) * S ≤ C * ((δ + w) * S) := by
    rcases le_total 0 C2 with h | h
    · calc C2 * (δ + w2) * S ≤ C * (δ + w) * S :=
            mul_le_mul_of_nonneg_right (mul_le_mul hCa (by linarith) (by positivity) hC) hS
        _ = C * ((δ + w) * S) := by ring
    · have : C2 * (δ + w2) * S ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h (by positivity)) hS
      have : 0 ≤ C * ((δ + w) * S) := by positivity
      linarith
  have e : C * ((δ + w) * S + (δ + w) ^ 2 + κ) =
      C * ((δ + w) * S) + C * ((δ + w) ^ 2 + κ) := by ring
  rw [e]
  linarith

/-- **`B3ClosedKLayerMean2` from the contract hypotheses and the closed `δ₀` jet at `p = 2`.** -/
theorem b3ClosedKLayerMean2_of_jet (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {P : ℝ} (h0 : ClosedJet0LpLe P) (hP : 2 ≤ P) : B3ClosedKLayerMean2 := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hF.1
  have hh : h ^ 2 < 1 := by nlinarith [hF.2.2.2.1, hF.2.2.2.2.1]
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  obtain ⟨C1, W1, hC1, hR1⟩ := ContractingWords.deltaMean_refined hGA hLp b hb0 hb κ hκ
  obtain ⟨C2, W2, hC2, hM2⟩ := ContractingWords.deltaMean_all hGA hLp b hb0 hb κ hκ
  obtain ⟨Cm, Cfl, W3, -, -, hD⟩ := RawTag.delta_fresh_bounds hGA hLp b hb0 hb κ hκ 1 le_rfl
  obtain ⟨Cd, W4, hCd, hmom⟩ := FullSource.delta_moments hGA b hb0 hb κ hκ 1 le_rfl
  obtain ⟨C0, hC0, hev0⟩ := h0 b E np τ m T s h K Vs hF R 2 (by norm_num) hP
  set Cf := Real.sqrt R with hCf
  set C := max (max C2 (Cf ^ 2 * C1)) (C0 + 1) with hCdef
  have hCpos : 0 ≤ C := le_max_of_le_right (by linarith)
  have hCa : C2 ≤ C := le_max_of_le_left (le_max_left _ _)
  have hCb : Cf ^ 2 * C1 ≤ C := le_max_of_le_left (le_max_right _ _)
  have hCc : C0 + 1 ≤ C := le_max_right _ _
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hev0, hF.2.2.2.2.2, eventually_ge_atTop (max (max W1 W2) (max (max W3 W4) 1)),
    B3Cur.eventually_one_le_closeLen hF.2.1] with W hW0 hVW hWW hs1 j hj ij
  simp only [max_le_iff] at hWW
  obtain ⟨⟨hW1, hW2⟩, ⟨hW3, hW4⟩, hW⟩ := hWW
  unfold B3LayerMeanAt2
  simp only [indicator_b3dX_inr_eq, cDrift, mul_zero, sub_zero]
  have hsj : closeLen s W ≤ j := (Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1
  have hVs : Measurable[growthSigma W (closeLen s W)] (Vs W) := hVW.1
  have hmV : Measurable (Vs W) :=
    hVs.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ ω, Vs W (extPast W j (pastCoords W j ω)) = Vs W ω :=
    fun ω => growth_fun_extPast hsj hVs ω
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j (Vs W)
  set X := b3ClosedX b E s h τ m W j
  have hS0 : ∀ y, 0 ≤ b3ContrSum b E s h τ m R W j (Vs W) y :=
    fun y => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨A.indicator (fun y => jetDistance0 b E (X y) + (W : ℝ)⁻¹), ?_, ?_⟩
  · -- the `L²` bound of the error field
    have hsplit : A.indicator (fun y => jetDistance0 b E (X y) + (W : ℝ)⁻¹) =
        A.indicator (fun y => jetDistance0 b E (X y)) + A.indicator (fun _ => (W : ℝ)⁻¹) := by
      funext y
      by_cases hy : y ∈ A <;> simp [hy]
    have hconst : eLpNorm (A.indicator (fun _ => (W : ℝ)⁻¹)) 2 μ ≤ ENNReal.ofReal (W : ℝ)⁻¹ := by
      refine (eLpNorm_indicator_le _
        (nullMeasurableSet_b3Alive (by linarith) hE1 hE2 s h τ m R W j hmV)).trans (le_of_eq ?_)
      rw [eLpNorm_const _ (by norm_num) (NeZero.ne μ), measure_univ, ENNReal.one_rpow, mul_one,
        Real.enorm_of_nonneg (by positivity)]
    have h6 := hW0 j hj
    rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by norm_num] at h6
    rw [hsplit]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    calc eLpNorm (A.indicator fun y => jetDistance0 b E (X y)) 2 μ +
          eLpNorm (A.indicator fun _ => (W : ℝ)⁻¹) 2 μ ≤
          ENNReal.ofReal (C0 / W) + ENNReal.ofReal (W : ℝ)⁻¹ := add_le_add h6 hconst
      _ = ENNReal.ofReal ((C0 + 1) / W) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (C / W) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCc hWpos.le)
  -- the pointwise bound
  by_cases hlive : ⌊(W : ℝ) * τ ij.1⌋₊ < j ∧ ⌊(W : ℝ) * τ ij.2⌋₊ < j
  swap
  · have hnb := (Finset.mem_filter.1 hj).2
    have hn1 : ⌊(W : ℝ) * τ ij.1⌋₊ ≠ j := fun h' => hnb ⟨ij.1, h'⟩
    have hn2 : ⌊(W : ℝ) * τ ij.2⌋₊ ≠ j := fun h' => hnb ⟨ij.2, h'⟩
    have hd : j + 1 ≤ ⌊(W : ℝ) * τ ij.1⌋₊ ∨ j + 1 ≤ ⌊(W : ℝ) * τ ij.2⌋₊ := by
      rw [not_and_or, not_lt, not_lt] at hlive
      omega
    refine Eventually.of_forall fun y => ?_
    rw [kStopStep_dead b E s h τ m R j (Vs W) ij hd, condExp_zero]
    have := hS0 y
    refine le_of_eq_of_le ?_ (show (0 : ℝ) ≤ _ by positivity)
    simp
  obtain ⟨hl1, hl2⟩ := hlive
  have hj1 : 1 ≤ j := hs1.trans hsj
  set Al := b3AliveM (np := np) b E s h τ m R W j (Vs W) with hAl
  set u := Al.indicator (closedNearU b E s h τ m W j ij.1) with hu
  set v := Al.indicator (closedNearV b E s h τ m W j ij.2) with hv
  have hEq := kStopStep_ae_eq_bilinear hb0 hb hE1 hE2 s h hh τ m hW (Vs W) R hj1 ij hl1 hl2
  have hAlm : MeasurableSet Al := measurableSet_b3AliveM b E s h τ m R W j hmV
  have hAlinv : ∀ y, b3Ext W j y ∈ Al ↔ y ∈ Al :=
    mem_b3AliveM_b3Ext b E s h τ m R hsj le_rfl hVinv
  have hum : Measurable u := (measurable_closedNearU b E s h τ m j ij.1).indicator hAlm
  have hvm : Measurable v := (measurable_closedNearV b E s h τ m j ij.2).indicator hAlm
  have hu' : ∀ y, u (b3Ext W j y) = u y := fun y => by
    by_cases hy : y ∈ Al
    · simp only [u, Set.indicator_of_mem hy, Set.indicator_of_mem ((hAlinv y).2 hy),
        closedNearU_b3Ext hsj le_rfl]
    · simp only [u, Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (fun h' => hy ((hAlinv y).1 h'))]
  have hv' : ∀ y, v (b3Ext W j y) = v y := fun y => by
    by_cases hy : y ∈ Al
    · simp only [v, Set.indicator_of_mem hy, Set.indicator_of_mem ((hAlinv y).2 hy),
        closedNearV_b3Ext hsj le_rfl]
    · simp only [v, Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (fun h' => hy ((hAlinv y).1 h'))]
  have hXm : Measurable X := measurable_b3ClosedX b E s h τ m j
  have hX' : ∀ y, X (b3Ext W j y) = X y := fun y => b3ClosedX_b3Ext hsj le_rfl y
  have hpas := ae_passive_b3ClosedX hb0 hb hE1 hE2 s h hh τ m hW j
  have hvec0 : vecNorm (0 : Fin W → ℂ) = 0 := by simp [vecNorm]
  have hub : ∀ y, vecNorm (u y) ≤ Cf := fun y => by
    by_cases hy : y ∈ Al
    · rw [hu, Set.indicator_of_mem hy]
      exact norm_closedNearU_le b E s h τ m j (Vs W) ij.1 y (hy.2 j hsj le_rfl)
    · rw [hu, Set.indicator_of_notMem hy, hvec0]
      exact Real.sqrt_nonneg R
  have hvb : ∀ᵐ y ∂μ, vecNorm (v y) ≤ Cf := by
    filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
      ae_closedPhase_good (W := W) (np := np) b E s h j] with y hP hQ
    by_cases hy : y ∈ Al
    · rw [hv, Set.indicator_of_mem hy]
      exact norm_closedNearV_le b E s h hh τ m j (Vs W) ij.2 y (hP.2.2.2 j)
        (isUnit_iff_ne_zero.2 hQ.1) (hy.2 j hsj le_rfl)
    · rw [hv, Set.indicator_of_notMem hy, hvec0]
      exact Real.sqrt_nonneg R
  -- integrability (Tonelli)
  have hint : Integrable (fun y => bilinear (u y) (freshDelta b E (X y) (freshSample W j y.1.1))
      (v y)) μ := by
    set Φ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort →
        ℂ := fun z => bilinear (u (b3Rebuild W j z.1))
          (freshDelta b E (X (b3Rebuild W j z.1)) z.2) (v (b3Rebuild W j z.1))
    have hR' : Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
        LayerSample W .oneBlockOnePort => b3Rebuild W j z.1 :=
      (measurable_b3Rebuild W j).comp measurable_fst
    have hΦ : Measurable Φ :=
      RawTag.measurable_bilinear_jt (hum.comp hR')
        (FullSource.measurable_freshDelta_comp b E (hXm.comp hR') measurable_snd) (hvm.comp hR')
    have hcomp : (fun y => Φ (b3Past W j y, freshSample W j y.1.1)) =
        fun y => bilinear (u y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v y) := by
      funext y
      simp only [Φ, b3Rebuild_b3Past, hu', hv', hX']
    rw [← hcomp]
    refine integrable_b3_of_fresh_ae b j hΦ (Cf ^ 2 * Cd) ?_
    filter_upwards [hpas, hvb] with y hy hyv
    simp only [Φ, b3Rebuild_b3Past, hu', hv', hX']
    have hΔm : Measurable fun f => ‖freshDelta b E (X y) f‖ :=
      (FullSource.measurable_freshDelta_comp b E measurable_const measurable_id).norm
    have h1 : ∫⁻ F, ‖‖freshDelta b E (X y) F‖‖ₑ ∂freshLaw W b ≤ ENNReal.ofReal Cd := by
      rw [← eLpNorm_one_eq_lintegral_enorm (hmom W hW4 E hEκ (X y) hy).1]
      simpa only [ENNReal.ofReal_one] using (hmom W hW4 E hEκ (X y) hy).2
    calc ∫⁻ f, ‖bilinear (u y) (freshDelta b E (X y) f) (v y)‖ₑ ∂freshLaw W b ≤
          ∫⁻ f, ENNReal.ofReal (Cf ^ 2) * ENNReal.ofReal ‖freshDelta b E (X y) f‖
            ∂freshLaw W b := by
          refine lintegral_mono fun f => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (sq_nonneg Cf)]
          exact ENNReal.ofReal_le_ofReal (norm_bilinear_le_of_vecNorm (hub y) hyv)
      _ = ENNReal.ofReal (Cf ^ 2) * ∫⁻ f, ENNReal.ofReal ‖freshDelta b E (X y) f‖
            ∂freshLaw W b := lintegral_const_mul _ (ENNReal.measurable_ofReal.comp hΔm)
      _ ≤ ENNReal.ofReal (Cf ^ 2) * ENNReal.ofReal Cd := by
          gcongr
          refine le_of_eq_of_le (lintegral_congr fun f => ?_) h1
          simp only [enorm_norm, ofReal_norm]
      _ = ENNReal.ofReal (Cf ^ 2 * Cd) := (ENNReal.ofReal_mul (sq_nonneg Cf)).symm
  have hΔi : ∀ᵐ y ∂μ, ∀ x x', Integrable (fun F => freshDelta b E (X y) F x x')
      (freshLaw W b) := by
    filter_upwards [hpas] with y hy
    exact (hD W hW3 E hEκ (X y) hy).1
  have hce := condExp_closed_bilinear_fresh b E j hum hvm hXm hu' hv' hX' hΔi hint
  have hce0 : μ[kStopStep b E s h τ m R W j (Vs W) ij | b3Sigma W j np] =ᵐ[μ]
      μ[fun y => bilinear (u y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v y) |
        b3Sigma W j np] := condExp_congr_ae hEq
  filter_upwards [hce0, hce, hpas, hvb, ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
    ae_closedPhase_good (W := W) (np := np) b E s h j,
    b3Alive_ae_eq (by linarith) hE1 hE2 s h τ m R W j (Vs W)] with y hy0 hy1 hyp hyv hyg hyq hyA
  by_cases hyA' : y ∈ A
  swap
  · rw [Set.indicator_of_notMem hyA', norm_zero]
    have := hS0 y
    positivity
  have hyAl : y ∈ Al := (Iff.of_eq hyA).mp hyA'
  rw [Set.indicator_of_mem hyA', hy0, hy1, Set.indicator_of_mem hyA']
  set M := matrixExpect (freshLaw W b) (freshDelta b E (X y))
  set mm := ContractingWords.avgTr M
  have hsplit : bilinear (u y) M (v y) =
      bilinear (u y) (M - mm • 1) (v y) + mm * (star (u y) ⬝ᵥ v y) := by
    simp only [bilinear, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    ring
  have hQ : star (u y) ⬝ᵥ v y =
      b3ContrCoord b E s h τ m W j (Vs W) 0 (Sum.inr ij.1) (Sum.inr ij.2) y := by
    rw [hu, hv, Set.indicator_of_mem hyAl, Set.indicator_of_mem hyAl,
      b3ContrCoord_zero_inr b E s h hh τ m j (Vs W) ij.1 ij.2 y (hyg.2.2.2 j)
        (isUnit_iff_ne_zero.2 hyq.1)]
  have hQS : ‖b3ContrCoord b E s h τ m W j (Vs W) 0 (Sum.inr ij.1) (Sum.inr ij.2) y‖ ≤
      b3ContrSum b E s h τ m R W j (Vs W) y := by
    have hyA'' : y ∈ b3Alive b E s h τ m R W j (Vs W) := hyA'
    have hx : ‖b3ContrCoord b E s h τ m W j (Vs W) 0 (Sum.inr ij.1) (Sum.inr ij.2) y‖ =
        ‖b3ContrAlive b E s h τ m R W j (Vs W) ((0 : Fin 4), Sum.inr ij.1, Sum.inr ij.2) y‖ := by
      rw [b3ContrAlive, Set.indicator_of_mem hyA'']
    rw [hx]
    exact Finset.single_le_sum (f := fun x : ContrIdx K np =>
      ‖b3ContrAlive b E s h τ m R W j (Vs W) x y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ ((0 : Fin 4), Sum.inr ij.1, Sum.inr ij.2))
  have hR1y := hR1 W hW1 E hEκ (X y) hyp
  have hM2y := hM2 W hW2 E hEκ (X y) hyp
  have hmm : ‖mm‖ ≤ ‖M‖ := ContractingWords.norm_avgTr_le hW M
  have hb1 : ‖bilinear (u y) (M - mm • 1) (v y)‖ ≤ Cf ^ 2 * ‖M - mm • 1‖ :=
    norm_bilinear_le_of_vecNorm (hub y) hyv
  set δ := jetDistance0 b E (X y)
  have hδ : 0 ≤ δ := norm_nonneg _
  obtain ⟨hw1, hw2⟩ := kLayer_inv_sq_le hW
  rw [Real.norm_of_nonneg (by positivity), hsplit]
  calc ‖bilinear (u y) (M - mm • 1) (v y) + mm * (star (u y) ⬝ᵥ v y)‖ ≤
        ‖bilinear (u y) (M - mm • 1) (v y)‖ + ‖mm‖ * ‖star (u y) ⬝ᵥ v y‖ :=
        (norm_add_le _ _).trans (le_of_eq (by rw [norm_mul]))
    _ ≤ Cf ^ 2 * (C1 * (δ ^ 2 + ((W : ℝ)⁻¹) ^ 2)) +
        C2 * (δ + ((W : ℝ)⁻¹) ^ 2) * b3ContrSum b E s h τ m R W j (Vs W) y := by
        refine add_le_add (hb1.trans (mul_le_mul_of_nonneg_left hR1y (sq_nonneg _))) ?_
        rw [hQ]
        exact mul_le_mul (hmm.trans hM2y) hQS (norm_nonneg _) (by positivity)
    _ ≤ _ := kLayer_arith2 hCpos hCa hCb hδ (hS0 y) (by positivity) hw1 hw2 (by positivity)

/-- **`ComplexClosedSummed` through the closed chain at `N = 2` from the bounded
jets**: with `B3ClosedKLayerMean2` from
`ClosedJet0LpLe 4`. -/
theorem complexClosedSummed_of_chain2_jet (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hB : GenReqBirth)
    (hCh : B3ClosedChainPin) (h0 : ClosedJet0LpLe 4)
    (hKG : CovLayerHypKG2 b3CovErr b3CovZ) (hE : CovErrMoments2 b3CovErr)
    (hD : B3ClosedContrDecay) : ComplexClosedSummed :=
  complexClosedSummed_of_chain2_decay hGA hLp hP hB hCh
    (b3ClosedKLayerMean2_of_jet hGA hLp h0 (by norm_num)) hKG hE hD

end BlockBand.SourceProcess.PhysApprox.B3
