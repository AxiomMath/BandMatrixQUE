module

public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubPlug
public import BlockBand.SourceProcess.PhysApprox.B3BoundJet

/-!
# The fresh `𝒦` diagonal from the closed jet at `p = 1`

* `ClosedJet0One`: the `p = 1` instance of the closed `δ₀` jet, `‖δ₀(X_cl,j)‖₁ ≤ C/W`;
  `closedJet0One_of_fam` (from `ClosedJet0Fam`) and `closedJet0One_of_le` (from
  `ClosedJet0FamLe 1`).
* **`complexBirthKDiag_of_jetOne`**: the proof of `complexBirthKDiag_of_jet`,
  restated because that theorem takes the `∀ p` family and uses only `p = 1`;
  **`complexBirthKDiag_of_jetLe`** with `ClosedJet0FamLe 1`.
* **`genReqBirth_of_closedBirth_jetLe`**: `GenReqBirth` from the input hypotheses,
  `KCorrStepFourAt`, `ClosedGramStepFourSmall`, `ComplexBirthGramDiag` and `ClosedJet0FamLe 1` (no
  `ComplexBirthKClosing`, no `ComplexBirthKDiag` hypothesis).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingLeak BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.PhysApprox.ClosedForm BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ClosingAux
open scoped NNReal ENNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
open BirthKSub

variable {W np : ℕ}

/-- The closed `δ₀` jet at `p = 1`. -/
def ClosedJet0One : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        eLpNorm (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y)) (ENNReal.ofReal 1)
          (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

theorem closedJet0One_of_fam (hJ : ClosedJet0Fam) : ClosedJet0One :=
  fun b E np τ m T s h K Vs hD => hJ b E np τ m T s h K Vs hD 1 le_rfl

theorem closedJet0One_of_le (hJ : ClosedJet0FamLe 1) : ClosedJet0One :=
  fun b E np τ m T s h K Vs hD => hJ b E np τ m T s h K Vs hD 1 le_rfl le_rfl

/-- **`ComplexBirthKDiag` from the closed jet at `p = 1` only** (with
`GaussianAbsorptionContract` and `GaussianLpGradient`). The proof is that of
`complexBirthKDiag_of_jet`, which uses its jet hypothesis only at `p = 1`.
-/
theorem complexBirthKDiag_of_jetOne (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hJ : ClosedJet0One) : ComplexBirthKDiag := by
  intro b E np τ m T s h K Vs hDom R θ hθ i
  have hDom' := hDom
  obtain ⟨hCSL, hs, -, hh0, hh1, -⟩ := hDom
  obtain ⟨hb0, hb, hE1, hE2, -, -, hm, -⟩ := hCSL
  have hh : h ^ 2 < 1 := by nlinarith
  have hη : 0 < etaZ b E := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  obtain ⟨CJ, hCJ⟩ := hJ b E np τ m T s h K Vs hDom'
  obtain ⟨C₂, W₀, hC₂, hMom⟩ := lintegral_m_le hGA hb0 hb hE1 hE2
  obtain ⟨A, B, W₁, hA, hB, hTr⟩ := lintegral_trace_fresh_le hGA hLp hb0 hb hE1 hE2
  set e : ℝ := (etaZ b E)⁻¹
  have he : 0 ≤ e := inv_nonneg.2 hη.le
  set q : ℝ := C₂ / etaZ b E
  have hq : 0 ≤ q := div_nonneg hC₂ hη.le
  set CJ' : ℝ := max CJ 0
  set c1 : ℝ := m i * e * (1 + q) + m i * B
  set c2 : ℝ := m i * A * CJ'
  have hc1 : 0 ≤ c1 := by have := hm i; positivity
  have hc2 : 0 ≤ c2 := by have := hm i; have : 0 ≤ CJ' := le_max_right _ _; positivity
  have hTot : Tendsto (fun W : ℕ => c1 * (Real.sqrt W)⁻¹ + c2 * ((W : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_sqrt_nat.const_mul c1).add (tendsto_inv_nat.const_mul c2)
  have hcl : ∀ᶠ W : ℕ in atTop, 1 ≤ closeLen s W :=
    (tendsto_nat_floor_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hs)).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (max (max W₀ W₁) 1), hcl, hCJ,
    hTot.eventually (gt_mem_nhds hθ)] with W hW hclW hJW hTW
  intro j hj1 hj2 hji
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans (le_of_max_le_left hW)
  have hW1' : W₁ ≤ W := (le_max_right _ _).trans (le_of_max_le_left hW)
  have hj : 1 ≤ j := hclW.trans hj1
  have hmW : 0 ≤ m i / W := div_nonneg (hm i) (Nat.cast_nonneg W)
  set Gp := gcl b E s h W j
  -- the probe average
  have hmain : ∫⁻ y, ‖b3ClosedKAt b E s h τ m W (j + 1) y i i - matchedA E * (m i : ℂ)‖ₑ
      ∂closedLaw b W np ≤
      ∫⁻ y, (ENNReal.ofReal (m i / W) * ENNReal.ofReal (Real.sqrt
          (Gp (y.1.1, y.2) * (Gp (y.1.1, y.2))ᴴ).trace.re) +
        ENNReal.ofReal (m i) * ‖(W : ℂ)⁻¹ * (Gp (y.1.1, y.2)).trace - matchedA E‖ₑ)
        ∂closedLaw b W np := by
    refine lintegral_closed_single_le i
      (Φ := fun p g => ENNReal.ofReal (m i / W) *
        ‖Counting.complexQuadraticForm (Gp p) g - (Gp p).trace‖ₑ +
        ENNReal.ofReal (m i) * ‖(W : ℂ)⁻¹ * (Gp p).trace - matchedA E‖ₑ)
      (D := fun p => ENNReal.ofReal (m i / W) * ENNReal.ofReal (Real.sqrt
          (Gp p * (Gp p)ᴴ).trace.re) +
        ENNReal.ofReal (m i) * ‖(W : ℂ)⁻¹ * (Gp p).trace - matchedA E‖ₑ) ?_ ?_ ?_ ?_
    · filter_upwards [ae_birth_good (np := np) hb0 hb hE1 hE2 s h hh τ m hW1 hj] with y hy0
      obtain ⟨hblk, hX, -, -⟩ := hy0
      exact closedK_diag_split b E s h τ m hm y hblk hη hX hji
    · have hGm := measurable_gcl b E s h W j
      exact (measurable_const.mul ((measurable_quad_gcl b E s h W j).sub
        (measurable_trace_comp (hGm.comp measurable_fst))).enorm).add
        (measurable_const.mul ((measurable_const.mul (measurable_trace_comp
          (hGm.comp measurable_fst))).sub_const _).enorm)
    · intro p
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      exact Birth.lintegral_quad_sub_le (Gp p)
    · have hGm := measurable_gcl b E s h W j
      refine (measurable_const.mul (Real.continuous_sqrt.measurable.comp
        (Complex.measurable_re.comp (measurable_trace_comp (measurable_matrix_mul' hGm
          (measurable_matrix_conjTranspose' hGm))))).ennreal_ofReal).add ?_
      exact measurable_const.mul ((measurable_const.mul (measurable_trace_comp hGm)).sub_const
        _).enorm
  -- the two expectations
  have hGm := measurable_gcl b E s h W j
  have hp1m : Measurable fun y : ProbedPath W np × ℝ => ENNReal.ofReal (m i / W) *
      ENNReal.ofReal (Real.sqrt (Gp (y.1.1, y.2) * (Gp (y.1.1, y.2))ᴴ).trace.re) :=
    measurable_const.mul (Real.continuous_sqrt.measurable.comp
      (Complex.measurable_re.comp (measurable_trace_comp (measurable_matrix_mul'
        (hGm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        (measurable_matrix_conjTranspose'
          (hGm.comp ((measurable_fst.comp measurable_fst).prodMk
            measurable_snd))))))).ennreal_ofReal
  have hP1 : ∫⁻ y, ENNReal.ofReal (m i / W) * ENNReal.ofReal (Real.sqrt
        (Gp (y.1.1, y.2) * (Gp (y.1.1, y.2))ᴴ).trace.re) ∂closedLaw b W np ≤
      ENNReal.ofReal (m i * (Real.sqrt W)⁻¹ * e) * ENNReal.ofReal (1 + q) := by
    refine (lintegral_hs_gcl_le (np := np) hb0 hb hE1 hE2 s h hh hW1 j (hm i)).trans ?_
    gcongr
    exact (hMom W hW0 hW1 s h hh np j hj1).1
  have hP2 := hTr W hW1' hW1 s h hh np j hj1
  have hδ : ∫⁻ y, ENNReal.ofReal (jetDistance0 b E (xcl b E s h W j (y.1.1, y.2)))
      ∂closedLaw b W np ≤ ENNReal.ofReal (CJ' / W) := by
    have h0 := hJW j (Finset.mem_Ico.2 ⟨hj1, hj2⟩)
    have hmeas : AEStronglyMeasurable (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y))
        (closedLaw b W np) := by
      unfold jetDistance0 passiveResolvent
      exact ((measurable_const.mul (measurable_trace_comp (measurable_matrix_inv.comp
        (measurable_matrix_sub measurable_const (measurable_b3ClosedX b E s h τ m j))))).sub_const
        _).norm.aestronglyMeasurable
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hmeas] at h0
    refine le_trans (le_of_eq ?_) (h0.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg W))))
    refine lintegral_congr fun y => ?_
    have hd : 0 ≤ jetDistance0 b E (b3ClosedX b E s h τ m W j y) := norm_nonneg _
    rw [Real.enorm_eq_ofReal hd]
    rfl
  have hP2' : ∫⁻ y, ENNReal.ofReal (A * jetDistance0 b E (xcl b E s h W j (y.1.1, y.2)) +
      B / Real.sqrt W) ∂closedLaw b W np ≤
      ENNReal.ofReal (A * (CJ' / W) + B / Real.sqrt W) := by
    have hsplit : ∀ y : ProbedPath W np × ℝ,
        ENNReal.ofReal (A * jetDistance0 b E (xcl b E s h W j (y.1.1, y.2)) + B / Real.sqrt W) =
          ENNReal.ofReal A * ENNReal.ofReal (jetDistance0 b E (xcl b E s h W j (y.1.1, y.2))) +
            ENNReal.ofReal (B / Real.sqrt W) := fun y => by
      have hd : 0 ≤ jetDistance0 b E (xcl b E s h W j (y.1.1, y.2)) := norm_nonneg _
      rw [ENNReal.ofReal_add (mul_nonneg hA hd) (by positivity),
        ENNReal.ofReal_mul hA]
    simp_rw [hsplit]
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_add (by positivity)
        (by positivity), ENNReal.ofReal_mul hA]
    gcongr
  calc ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
          b3ClosedKAt b E s h τ m W (j + 1) y i i - matchedA E * (m i : ℂ)) y‖ₑ
          ∂closedLaw b W np
      ≤ ∫⁻ y, ‖b3ClosedKAt b E s h τ m W (j + 1) y i i - matchedA E * (m i : ℂ)‖ₑ
          ∂closedLaw b W np := lintegral_mono fun y => by
        by_cases hy : y ∈ b3Alive b E s h τ m R W j (Vs W)
        · rw [Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy, enorm_zero]
          exact zero_le
    _ ≤ _ := hmain
    _ = ∫⁻ y, ENNReal.ofReal (m i / W) * ENNReal.ofReal (Real.sqrt
          (Gp (y.1.1, y.2) * (Gp (y.1.1, y.2))ᴴ).trace.re) ∂closedLaw b W np +
        ENNReal.ofReal (m i) * ∫⁻ y, ‖(W : ℂ)⁻¹ * (Gp (y.1.1, y.2)).trace - matchedA E‖ₑ
          ∂closedLaw b W np := by
        rw [lintegral_add_left hp1m,
          lintegral_const_mul' (ENNReal.ofReal (m i)) _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (m i * (Real.sqrt W)⁻¹ * e) * ENNReal.ofReal (1 + q) +
        ENNReal.ofReal (m i) * ENNReal.ofReal (A * (CJ' / W) + B / Real.sqrt W) := by
        exact add_le_add hP1 (by gcongr; exact hP2.trans hP2')
    _ = ENNReal.ofReal (c1 * (Real.sqrt W)⁻¹ + c2 * ((W : ℝ))⁻¹) := by
        have hA' : 0 ≤ A * (CJ' / W) + B / Real.sqrt W := by
          have : 0 ≤ CJ' := le_max_right _ _
          positivity
        rw [← ENNReal.ofReal_mul (by have := hm i; positivity), ← ENNReal.ofReal_mul (hm i),
          ← ENNReal.ofReal_add (by have := hm i; positivity) (mul_nonneg (hm i) hA')]
        congr 1
        simp only [c1, c2, div_eq_mul_inv]
        ring
    _ ≤ ENNReal.ofReal θ := ENNReal.ofReal_le_ofReal hTW.le

/-- **`ComplexBirthKDiag` from `ClosedJet0FamLe 1`.** -/
theorem complexBirthKDiag_of_jetLe (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hJ : ClosedJet0FamLe 1) : ComplexBirthKDiag :=
  complexBirthKDiag_of_jetOne hGA hLp (closedJet0One_of_le hJ)

/-- **`GenReqBirth` from the input hypotheses, `KCorrStepFourAt`, `ClosedGramStepFourSmall`,
`ComplexBirthGramDiag` and `ClosedJet0FamLe 1`** (no `ComplexBirthKClosing`). -/
theorem genReqBirth_of_closedBirth_jetLe (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hC : KCorrStepFourAt) (hG : ClosedGramStepFourSmall)
    (hGd : ComplexBirthGramDiag) (hJ : ClosedJet0FamLe 1) : GenReqBirth :=
  genReqBirth_of_closedBirth hMT hGA hLp hSR hC hG hGd (complexBirthKDiag_of_jetLe hGA hLp hJ)

end BlockBand.SourceProcess.PhysApprox.B3
