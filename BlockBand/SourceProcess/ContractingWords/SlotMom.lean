module

public import BlockBand.SourceProcess.ContractingWords.WordPos
public import BlockBand.SourceProcess.ContractingWords.IdProjFinal
public import BlockBand.SourceProcess.ContractingWords.SummedPath
public import BlockBand.SourceProcess.ContractingWords.LayerPins
public import BlockBand.SourceProcess.ContractingWords.SepAll

/-!
# The slots of an ordinary word at one fresh layer

Measure `freshLaw W b`; deterministic Hermitian old two-port `𝕏`; `e = layerErr`. For an ordinary
word `w`, slot `p` carries the old separator `σ_p = sepOf 𝕏 s_p ∈ {I, P}` and the increment
`Δ_p = N σ_p N* - σ_p` (`slotDelta`).

`slot_basic hGA hLp`: for `M ≥ 1` there are `C, W₀` (from `b, κ, M`) such that for `W ≥ W₀`,
`E ∈ bulkInterval κ`, every `s`, every Hermitian `𝕏` and every ordinary `w`:
`SlotMoments (freshLaw W b) Δ M (C(W^{-1/2} + e))`, the entries are integrable and
`‖EΔ_p‖ ≤ C e`. Inputs: `sepMeanIdProj_holds`, `sepFluctIdProj_holds`, `fresh_basic`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance
open scoped ENNReal Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

/-- The old separators of the slots of `w`. -/
def slotSep (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (w : TraceWord nT nI) :
    Fin w.length → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  fun i => sepOf b E XX (w.get i).2

/-- The slot increments `Δ_p = N σ_p N* - σ_p`. -/
def slotDelta (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (w : TraceWord nT nI)
    (y : LayerSample W .oneBlockOnePort) : Fin w.length → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  fun i => transportedSep b E XX (w.get i).2 y - sepOf b E XX (w.get i).2

theorem slot_ord {w : TraceWord nT nI} (hw : IsOrdinaryWord w) (i : Fin w.length) :
    (w.get i).2.unconj + (w.get i).2.conj = 0 := by
  rcases hw.2 _ (List.get_mem w i) with h | h <;> rw [h] <;> rfl

/-- `eLpNorm` at `M` to all integer moments `≤ M`. -/
theorem moments_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) {M : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (h : eLpNorm f (M : ℝ≥0∞) μ ≤ ENNReal.ofReal β) (m : ℕ) (hm : 1 ≤ m) (hmM : m ≤ M) :
    Integrable (fun ω => ‖f ω‖ ^ m) μ ∧ ∫ ω, ‖f ω‖ ^ m ∂μ ≤ β ^ m := by
  have hle : eLpNorm f (m : ℝ≥0∞) μ ≤ ENNReal.ofReal β :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast hmM : (m : ℝ≥0∞) ≤ M)).trans h
  have hlt : eLpNorm f (m : ℝ≥0∞) μ < ⊤ := lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  have hmem : MemLp f (m : ℝ≥0∞) μ := hlt
  have hint := hmem.integrable_norm_pow (by omega)
  refine ⟨hint, ?_⟩
  have hl := lintegral_pow_le_of_eLpNorm (f := fun ω => ‖f ω‖) (B := ENNReal.ofReal β)
    (fun _ => norm_nonneg _) hf.norm hm (by rw [eLpNorm_norm] <;> first | exact hle | exact hf)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity)
    (hint.aestronglyMeasurable)]
  have e : ∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ m) ∂μ = ∫⁻ ω, ENNReal.ofReal ‖f ω‖ ^ m ∂μ :=
    lintegral_congr fun ω => (ENNReal.ofReal_pow (norm_nonneg _) m)
  rw [e]
  calc (∫⁻ ω, ENNReal.ofReal ‖f ω‖ ^ m ∂μ).toReal ≤ (ENNReal.ofReal β ^ m).toReal :=
        ENNReal.toReal_mono (by simp) hl
    _ = β ^ m := by rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hβ]

theorem layerErr_parts (b E : ℝ) (s : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hg : 0 ≤ conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))) :
    0 ≤ jetDistance0 b E (nearSchur (boundaryZ b E) XX) ∧
      jetDistance0 b E (nearSchur (boundaryZ b E) XX) ≤ layerErr b E s XX ∧
      conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) / W ≤
        layerErr b E s XX ∧ (W : ℝ)⁻¹ ≤ layerErr b E s XX ∧ 0 ≤ layerErr b E s XX ∧
      jetDistance0 b E (nearSchur (boundaryZ b E) XX) +
        conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) / W + (W : ℝ)⁻¹ ≤
        layerErr b E s XX := by
  have h0 : 0 ≤ jetDistance0 b E (nearSchur (boundaryZ b E) XX) := norm_nonneg _
  have h1 : 0 ≤ jetDistance1 b E s (nearSchur (boundaryZ b E) XX) := norm_nonneg _
  have h2 : 0 ≤ conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) / W :=
    div_nonneg hg (Nat.cast_nonneg _)
  have h3 : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  simp only [layerErr]
  refine ⟨h0, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **The slot data of an ordinary word**, bulk-uniform. -/
theorem slot_basic (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (M : ℕ) (hM : 1 ≤ M) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (nT nI : ℕ) (w : TraceWord nT nI), IsOrdinaryWord w →
        SlotMoments (freshLaw W b) (slotDelta b E XX w) M
            (C * (1 / Real.sqrt W + layerErr b E s XX)) ∧
          (∀ p i j, Integrable (fun y => slotDelta b E XX w y p i j) (freshLaw W b)) ∧
          ∀ p, ‖slotMean (freshLaw W b) (slotDelta b E XX w) p‖ ≤ C * layerErr b E s XX := by
  obtain ⟨C₁, W₁, hC₁, hm⟩ := sepMeanIdProj_holds hGA hLp b hb0 hb κ hκ
  obtain ⟨C₂, W₂, hC₂, hf⟩ := sepFluctIdProj_holds hGA hLp b hb0 hb κ hκ M (by exact_mod_cast hM)
  obtain ⟨μb, W₃, -, hfb⟩ := fresh_basic hGA hb0 hb hκ
  refine ⟨C₁ + C₂ + 1, max (max W₁ W₂) (max W₃ 1), by positivity, ?_⟩
  intro W hW E hE s XX hXX nT nI w hw
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW3, hW4⟩ := hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  obtain ⟨hδ0, hδe, hge, hWe, he0, hsum⟩ := layerErr_parts b E s XX hg (W := W)
  set e := layerErr b E s XX
  have hWpos : (1 : ℝ) ≤ W := by exact_mod_cast hW4
  have hW2' : ((W : ℝ)⁻¹) ^ 2 ≤ (W : ℝ)⁻¹ := by
    have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWpos
    nlinarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) W)]
  have hent : ∀ p i j, Integrable (fun y => slotDelta b E XX w y p i j) (freshLaw W b) :=
    fun p i j => ((hfb W hW3 E hE XX hXX _).1 i j).sub (integrable_const _)
  have hmean : ∀ p, slotMean (freshLaw W b) (slotDelta b E XX w) p =
      matrixExpect (freshLaw W b) (transportedSep b E XX (w.get p).2) - sepOf b E XX (w.get p).2 :=
    fun p => matrixExpect_sub_const _ _ ((hfb W hW3 E hE XX hXX _).1)
  have hmb : ∀ p, ‖slotMean (freshLaw W b) (slotDelta b E XX w) p‖ ≤ C₁ * e := fun p => by
    rw [hmean]
    refine (hm W hW1 E hE XX hXX _ (slot_ord hw p)).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hC₁
  refine ⟨?_, hent, fun p => (hmb p).trans (mul_le_mul_of_nonneg_right (by linarith) he0)⟩
  intro p u v hu hv
  have hTm := measurable_transportedSep b E XX (w.get p).2
  have hmeas : AEStronglyMeasurable (fun y => bilinear u (slotDelta b E XX w y p) v)
      (freshLaw W b) := by
    have hc : Continuous fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => bilinear u M v :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact (hc.measurable.comp (hTm.sub measurable_const)).aestronglyMeasurable
  refine ⟨hmeas, fun m hm1 hmM => moments_of_eLpNorm hmeas (by positivity) ?_ m hm1 hmM⟩
  set ET := matrixExpect (freshLaw W b) (transportedSep b E XX (w.get p).2)
  set c0 := bilinear u (slotMean (freshLaw W b) (slotDelta b E XX w) p) v
  have hsplit : (fun y => bilinear u (slotDelta b E XX w y p) v) =
      fun y => c0 + bilinear u (transportedSep b E XX (w.get p).2 y - ET) v := funext fun y => by
    simp only [c0, hmean, ← bilinear_add_mat, slotDelta]
    congr 1; abel
  have hcm : AEStronglyMeasurable (fun y => bilinear u (transportedSep b E XX (w.get p).2 y - ET) v)
      (freshLaw W b) := by
    have hc : Continuous fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => bilinear u M v :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact (hc.measurable.comp (hTm.sub measurable_const)).aestronglyMeasurable
  have hfl := hf W hW2 E hE XX hXX _ (slot_ord hw p) u v
  rw [ENNReal.ofReal_natCast] at hfl
  have hc0 : ‖c0‖ ≤ C₁ * e := by
    have h := norm_bilinear_le u (slotMean (freshLaw W b) (slotDelta b E XX w) p) v
    have := hmb p
    have := vecNorm_nonneg u; have := vecNorm_nonneg v
    calc ‖c0‖ ≤ vecNorm u * ‖slotMean (freshLaw W b) (slotDelta b E XX w) p‖ * vecNorm v := h
      _ ≤ 1 * (C₁ * e) * 1 := by gcongr
      _ = C₁ * e := by ring
  rw [hsplit]
  refine (eLpNorm_add_le (f := fun _ => c0) (by exact_mod_cast hM)).trans ?_
  rw [eLpNorm_const _ (by positivity) (NeZero.ne _), measure_univ, ENNReal.one_rpow, mul_one]
  have hmin : min 1 (jetDistance0 b E (nearSchur (boundaryZ b E) XX)) ≤ e :=
    (min_le_right _ _).trans hδe
  have hsq : 0 ≤ 1 / Real.sqrt W := by positivity
  calc ‖c0‖ₑ + eLpNorm (fun y => bilinear u (transportedSep b E XX (w.get p).2 y - ET) v) (M : ℝ≥0∞)
        (freshLaw W b) ≤ ENNReal.ofReal (C₁ * e) + ENNReal.ofReal (C₂ * (1 / Real.sqrt W +
          min 1 (jetDistance0 b E (nearSchur (boundaryZ b E) XX))) * vecNorm u * vecNorm v) := by
        refine add_le_add ?_ hfl
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hc0
    _ ≤ ENNReal.ofReal ((C₁ + C₂ + 1) * (1 / Real.sqrt W + e)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by
          have := vecNorm_nonneg u; have := vecNorm_nonneg v
          have : 0 ≤ min 1 (jetDistance0 b E (nearSchur (boundaryZ b E) XX)) := le_min zero_le_one hδ0
          positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hu0 := vecNorm_nonneg u; have hv0 := vecNorm_nonneg v
        have hmin0 : 0 ≤ min 1 (jetDistance0 b E (nearSchur (boundaryZ b E) XX)) :=
          le_min zero_le_one hδ0
        have h1 : C₂ * (1 / Real.sqrt W + min 1 (jetDistance0 b E (nearSchur (boundaryZ b E) XX))) *
            vecNorm u * vecNorm v ≤ C₂ * (1 / Real.sqrt W + e) := by
          calc _ ≤ C₂ * (1 / Real.sqrt W + e) * 1 * 1 := by gcongr
            _ = _ := by ring
        nlinarith

end BlockBand.SourceProcess.ContractingWords
