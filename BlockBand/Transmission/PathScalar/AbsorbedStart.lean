module

public import BlockBand.Transmission.PathScalar.LayerPerturb
public import BlockBand.Transmission.PathScalar.AbsorbedMoment

/-!
# The start of the absorbed recursion (`r = 1`)

`absorbedStartBound_holds`: under `MatchedTracesContract` and `PassiveBoundsStatement`, the first
length of the absorbed near-end growth has `‖δ₀(X_1)‖_q ≤ C/W`. The absorption shift of the
first step is controlled by the layer moments at `w = z_∂` and Hölder's inequality.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer
open scoped ENNReal NNReal Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem measurable_layerAt (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable fun f : LayerSample W .oneBlockOnePort => layerAt E w X f := by
  have hB := measurable_bondMatrix (W := W) .oneBlockOnePort
    (B := fun f : LayerSample W .oneBlockOnePort => f.2) measurable_snd
  have hD := measurable_blockDiag (W := W) (A := fun f : LayerSample W .oneBlockOnePort => f.1)
    measurable_fst
  refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun u v => ?_)
  rcases u with u | u <;> rcases v with v | v
  · simp only [layerMatrix, Matrix.fromBlocks_apply₁₁, Matrix.sub_apply]
    exact (hD.eval_matrix.sub measurable_const).sub measurable_const
  · simp only [layerMatrix, Matrix.fromBlocks_apply₁₂]; exact hB.eval_matrix
  · simp only [layerMatrix, Matrix.fromBlocks_apply₂₁]
    exact (measurable_matrix_conjTranspose' hB).eval_matrix
  · simp only [layerMatrix, Matrix.fromBlocks_apply₂₂]; exact measurable_const

/-- The physical block is a.s. invertible (GUE block, any deterministic `X`). -/
theorem ae_isUnit_layerF {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ)
    (X : Matrix (Fin W) (Fin W) ℂ) : ∀ᵐ f ∂freshLaw W b, IsUnit (layerF E X f) := by
  let e : Fin W ≃ Fin 1 × Fin W := (Equiv.uniqueProd (Fin W) (Fin 1)).symm
  have hA := ae_det_gue_add_ne_zero W (gueVariance_ne_zero hb hW) (-((E : ℂ) • 1) - X)
  rw [← freshLaw_map_block W b] at hA
  refine (ae_of_ae_map ((measurable_pi_apply 0).comp measurable_fst).aemeasurable hA).mono
    fun f hf => ?_
  have hsub : (layerF E X f).submatrix e e = f.1 0 + (-((E : ℂ) • 1) - X) := by
    ext x y; simp [e, layerF, liftX, BlockBand.Internal.Contracts.Layers.blockDiag,
      Matrix.one_apply]; ring
  rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_submatrix_equiv_self e, hsub]
  exact isUnit_iff_ne_zero.mpr hf

/-- The far-lead input as a function of the past coordinates at length `0`. -/
def startInput (b E : ℝ) (p : PastSample W 0) : Matrix (Fin W) (Fin W) ℂ :=
  (boundaryZ b E)⁻¹ • (p.2 0 * (p.2 0)ᴴ)

theorem measurable_startInput (b E : ℝ) : Measurable (startInput (W := W) b E) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [startInput, Matrix.smul_apply]
  have h0 : Measurable fun p : PastSample W 0 => p.2 0 := (measurable_pi_apply 0).comp measurable_snd
  exact (measurable_matrix_mul' h0 (measurable_matrix_conjTranspose' h0)).eval_matrix.const_mul _

/-- The absorption shift at the first step, on `pastSample × freshSample`. -/
def startShift (b E ε : ℝ) (q : PastSample W 0 × LayerSample W .oneBlockOnePort) : ℝ :=
  ‖freshPortTrace b E (startInput b E q.1 - (((ε : ℂ) * Complex.I)) • 1) q.2 -
    freshPortTrace b E (startInput b E q.1) q.2‖

theorem measurable_startShift (b E ε : ℝ) : Measurable (startShift (W := W) b E ε) := by
  have hX : Measurable fun q : PastSample W 0 × LayerSample W .oneBlockOnePort =>
      startInput b E q.1 := (measurable_startInput (W := W) b E).comp measurable_fst
  have hX' : Measurable fun q : PastSample W 0 × LayerSample W .oneBlockOnePort =>
      startInput b E q.1 - (((ε : ℂ) * Complex.I)) • 1 :=
    Measurable.of_eval_matrix _ fun x y => hX.eval_matrix.sub measurable_const
  exact ((measurable_freshPortTrace_comp b E hX' measurable_snd).sub
    (measurable_freshPortTrace_comp b E hX measurable_snd)).norm

theorem passiveY_startInput {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (p : PastSample W 0) : (passiveY (startInput b E p)).PosSemidef := by
  have h := passiveY_initialInput hb hE1 hE2 (extendPast p)
  have he : initialInput b E (extendPast p) = startInput b E p := by
    simp [initialInput, startInput, extendPast]
  rwa [he] at h

theorem holderTriple_two (q : ℝ) (hq : 0 < q) :
    ENNReal.HolderTriple (ENNReal.ofReal (2 * q)) (ENNReal.ofReal (2 * q)) (ENNReal.ofReal q) := by
  constructor
  rw [← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; field_simp; ring

theorem eLpNorm_startShift_section_le {b E q CG ε : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (hq : 0 < q) (hCG : 0 ≤ CG) (hε : 0 ≤ ε)
    (hdet : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ᵐ f ∂freshLaw W b, IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) f).det)
    (hG : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun f => ‖layerAt E (boundaryZ b E) X f‖) (ENNReal.ofReal (2 * q)) (freshLaw W b) ≤
        ENNReal.ofReal CG)
    (p : PastSample W 0) :
    eLpNorm (fun f => startShift b E ε (p, f)) (ENNReal.ofReal q) (freshLaw W b) ≤
      ENNReal.ofReal (ε * CG ^ 2) := by
  set X := startInput b E p
  have hX := passiveY_startInput (b := b) (by linarith) hE1 hE2 p
  have hX' := passiveY_absorb hX hε
  have := holderTriple_two q hq
  have hmG : ∀ Y : Matrix (Fin W) (Fin W) ℂ, Measurable fun f => ‖layerAt E (boundaryZ b E) Y f‖ :=
    fun Y => (measurable_layerAt E _ Y).norm
  have hae : ∀ᵐ f ∂freshLaw W b, ‖startShift b E ε (p, f)‖ ≤
      ε * (‖layerAt E (boundaryZ b E) (X - (((ε : ℂ) * Complex.I)) • 1) f‖ *
        ‖layerAt E (boundaryZ b E) X f‖) := by
    filter_upwards [ae_isUnit_layerF hb hW E X, ae_isUnit_layerF hb hW E (X - (((ε : ℂ) * Complex.I)) • 1),
      hdet X hX, hdet _ hX'] with f h1 h2 h3 h4
    rw [Real.norm_of_nonneg (by unfold startShift; exact norm_nonneg _), ← mul_assoc]
    exact norm_freshPortTrace_absorb_le b E X hε f h1 h2 h3 h4
  refine (eLpNorm_mono_ae_real ((measurable_startShift b E ε).comp measurable_prodMk_left).aestronglyMeasurable hae).trans ?_
  have hsm : (fun f => ε * (‖layerAt E (boundaryZ b E) (X - (((ε : ℂ) * Complex.I)) • 1) f‖ *
        ‖layerAt E (boundaryZ b E) X f‖)) =
      ε • ((fun f => ‖layerAt E (boundaryZ b E) (X - (((ε : ℂ) * Complex.I)) • 1) f‖) •
        fun f => ‖layerAt E (boundaryZ b E) X f‖) := by
    funext f; simp [smul_eq_mul]
  rw [hsm, eLpNorm_const_smul, Real.enorm_eq_ofReal hε]
  calc ENNReal.ofReal ε * eLpNorm ((fun f => ‖layerAt E (boundaryZ b E) (X - (((ε : ℂ) * Complex.I)) • 1) f‖) •
        fun f => ‖layerAt E (boundaryZ b E) X f‖) (ENNReal.ofReal q) (freshLaw W b)
      ≤ ENNReal.ofReal ε * (ENNReal.ofReal CG * ENNReal.ofReal CG) := by
        gcongr
        exact (eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal (2 * q)) (q := ENNReal.ofReal (2 * q))
          (hmG _).aestronglyMeasurable (hmG _).aestronglyMeasurable).trans
          (mul_le_mul' (hG _ hX') (hG _ hX))
    _ = ENNReal.ofReal (ε * CG ^ 2) := by
        rw [← ENNReal.ofReal_mul hCG, ← ENNReal.ofReal_mul hε]; ring_nf

theorem absorbedStartBound_holds (hMT : MatchedTracesContract) (hPB : PassiveBoundsStatement) :
    AbsorbedStartBound := by
  intro b hb hb' κ' K q hκ' hK hq
  obtain ⟨C0, W0, hC0⟩ := passiveInitialScalar_moment hMT b hb hb' κ' 1 q hκ' hq
  obtain ⟨CG, WG, hG⟩ := hPB.moments b hb hb' κ' hκ' (2 * q) (by linarith)
  set CGp := max CG 0 with hCGp
  have hCGp0 : 0 ≤ CGp := le_max_right _ _
  refine ⟨max C0 0 + K * CGp ^ 2, max (max W0 WG) 1, by positivity, ?_⟩
  intro W hW E hE κ hκ
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hWG⟩, hW1⟩ := hW
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx0 : (0 : ℝ) < W := by linarith
  obtain ⟨h1, h2⟩ := bulk_bounds hκ' hE
  have hq0 : (0 : ℝ) < q := by linarith
  set ε := layerAbsorption W κ 1 0 with hεdef
  have hε0 : 0 ≤ ε := div_nonneg (hκ _).1 (sq_nonneg _)
  have hεK : ε ≤ K / (W : ℝ) ^ 2 := div_le_div_of_nonneg_right (hκ _).2 (sq_nonneg _)
  have hz : boundaryZ b E ∈ paramDisk b E :=
    Metric.mem_closedBall_self (by have := etaZ_pos b E (by linarith) h1 h2; positivity)
  have hdet : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ᵐ f ∂freshLaw W b, IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) f).det :=
    fun X hX => (hG W hWG E hE _ hz X hX).1
  have hGb : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun f => ‖layerAt E (boundaryZ b E) X f‖) (ENNReal.ofReal (2 * q)) (freshLaw W b) ≤
        ENNReal.ofReal CGp :=
    fun X hX => (hG W hWG E hE _ hz X hX).2.1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hae : ∀ᵐ ω ∂growthPathLaw W b, absorbedDelta b E κ W 1 ω ≤
      absorbedDelta b E (fun _ => 0) W 1 ω +
        startShift b E ε (pastCoords W 0 ω, freshSample W 0 ω) := by
    filter_upwards [ae_pathNearSchur_one hb' h1 h2 hW1 (fun s => (hκ s).1),
      ae_pathNearSchur_one hb' h1 h2 hW1 (κ := fun _ => 0) (fun _ => le_rfl)] with ω hk h0
    have hz0 : layerAbsorption W (fun _ => 0) 1 0 = 0 := by simp [layerAbsorption]
    rw [absorbedDelta, absorbedDelta, hk, h0, jetDistance0_freshSchur, jetDistance0_freshSchur,
      hz0]
    simp only [Complex.ofReal_zero, zero_mul, zero_smul, sub_zero]
    have hin : initialInput b E ω = startInput b E (pastCoords W 0 ω) := rfl
    rw [hin, startShift, add_comm]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hg := (measurable_pastCoords W 0).prodMk (measurable_freshSample W 0)
  have hshift : eLpNorm (fun ω => startShift b E ε (pastCoords W 0 ω, freshSample W 0 ω))
      (ENNReal.ofReal q) (growthPathLaw W b) ≤ ENNReal.ofReal (ε * CGp ^ 2) := by
    have : (fun ω => startShift b E ε (pastCoords W 0 ω, freshSample W 0 ω)) =
        startShift b E ε ∘ fun ω => (pastCoords W 0 ω, freshSample W 0 ω) := rfl
    rw [this, ← eLpNorm_map_measure (measurable_startShift b E ε).aestronglyMeasurable
      hg.aemeasurable, growthPathLaw_map_past_fresh]
    exact eLpNorm_prod_le_of_section _ _ (measurable_startShift b E ε) hq0
      (Filter.Eventually.of_forall fun p => eLpNorm_startShift_section_le hb' h1 h2 hW1 hq0 hCGp0
        hε0 hdet hGb p)
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  have hδ0 : eLpNorm (absorbedDelta b E (fun _ => 0) W 1) (ENNReal.ofReal q) (growthPathLaw W b) ≤
      ENNReal.ofReal (max C0 0 / W) :=
    (hC0 W hW0 E hE 1 le_rfl (by simpa using hx)).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le))
  calc eLpNorm (absorbedDelta b E κ W 1) (ENNReal.ofReal q) (growthPathLaw W b)
      ≤ eLpNorm (absorbedDelta b E (fun _ => 0) W 1 +
          fun ω => startShift b E ε (pastCoords W 0 ω, freshSample W 0 ω)) (ENNReal.ofReal q)
          (growthPathLaw W b) := by
        refine eLpNorm_mono_ae_real (measurable_absorbedDelta b E κ 1).aestronglyMeasurable
          (hae.mono fun ω h => ?_)
        rw [Real.norm_of_nonneg (absorbedDelta_nonneg b E κ 1 ω)]; exact h
    _ ≤ _ := eLpNorm_add_le hq1
    _ ≤ ENNReal.ofReal (max C0 0 / W) + ENNReal.ofReal (ε * CGp ^ 2) := add_le_add hδ0 hshift
    _ = ENNReal.ofReal (max C0 0 / W + ε * CGp ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((max C0 0 + K * CGp ^ 2) / W) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h2' : ε * CGp ^ 2 ≤ K * CGp ^ 2 / W := by
          have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
          have : K / (W : ℝ) ^ 2 ≤ K / W := div_le_div_of_nonneg_left hK hx0 hWW
          calc ε * CGp ^ 2 ≤ K / W * CGp ^ 2 := by gcongr; linarith
            _ = K * CGp ^ 2 / W := by ring
        rw [add_div]; linarith

end BlockBand.Transmission.PathScalar

