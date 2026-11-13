module

public import BlockBand.SourceProcess.FullSource.SqIter
public import BlockBand.SourceProcess.FullSource.BirthZero

/-!
# Births of the tag square

* `sqOf_le_card`: `W⁻¹Tr(D*D)² ≤ W⁻¹ |rows D| ‖D‖⁴`;
* `birth_sq_succ` (`k ≥ 1`): `Y_{k+1;k} = D₊*D₊` (`D₊` has `W` rows), so `h_{k+1} ≤ ‖D₊‖⁴` and
  `E h_{k+1}^q ≤ C_D^{4q}` from the `freshD` moments of `FullSourceEstimates` (Fubini);
* `birth_sq_zero` (`k = 0`): `h_1 ≤ ‖G‖⁴` for the layer `.oneBlockTwoPorts` at `X = 0`, from
  `GaussianAbsorptionContract`.

A tag starts with `C₊`, and `E_j Tr C₊² ≤ CW`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

theorem sqOf_le_card {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (W : ℕ) (D : Matrix m n ℂ) :
    sqOf W D ≤ (W : ℝ)⁻¹ * (Fintype.card m * ‖D‖ ^ 4) := by
  have h1 := (Complex.re_le_norm _).trans (norm_trace_factor_le D (Dᴴ * D))
  have h2 := re_trace_le_card D
  have h3 : ‖Dᴴ * D‖ ≤ ‖D‖ ^ 2 :=
    (Matrix.l2_opNorm_mul Dᴴ D).trans (le_of_eq (by rw [Matrix.l2_opNorm_conjTranspose, sq]))
  have hT := trace_factor_re_nonneg D
  have h4 : (Dᴴ * D * (Dᴴ * D)).trace.re ≤ Fintype.card m * ‖D‖ ^ 4 := by
    calc (Dᴴ * D * (Dᴴ * D)).trace.re ≤ ‖Dᴴ * D‖ * (Dᴴ * D).trace.re := h1
      _ ≤ ‖D‖ ^ 2 * (Fintype.card m * ‖D‖ ^ 2) :=
        mul_le_mul h3 h2 hT (by positivity)
      _ = Fintype.card m * ‖D‖ ^ 4 := by ring
  unfold sqOf
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

variable {W : ℕ}

/-- **Birth of a tag square at `k ≥ 1`.** -/
theorem birth_sq_succ {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {k q : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q) {CD : ℝ} (hCD : 0 ≤ CD)
    (hD : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      eLpNorm (fun ω => ‖freshD b E XX ω‖) (ENNReal.ofReal ((4 * q : ℕ) : ℝ)) (freshLaw W b) ≤
        ENNReal.ofReal CD) :
    ∫⁻ ω, ENNReal.ofReal (tagSq b E W (k + 1) k ω ^ q) ∂growthPathLaw W b ≤
      ENNReal.ofReal (CD ^ (4 * q)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set Φ : PastSample W k × LayerSample W .oneBlockOnePort → ℝ≥0∞ := fun q' =>
    ENNReal.ofReal (‖freshD b E (pastXX E W k q'.1) q'.2‖ ^ (4 * q))
  have hmΦ : Measurable Φ := ((measurable_freshD_comp b E ((measurable_pastXX E k).comp
    measurable_fst) measurable_snd).norm.pow_const _).ennreal_ofReal
  have hZ : ∀ᵐ ω ∂growthPathLaw W b, pastCoords W k ω ∈ (Set.univ : Set (PastSample W k)) →
      ENNReal.ofReal (tagSq b E W (k + 1) k ω ^ q) ≤ Φ (pastCoords W k ω, freshSample W k ω) := by
    filter_upwards [ae_tagResponse_succ_new_full hb0 hb hE1 hE2 hW] with ω h _
    refine ENNReal.ofReal_le_ofReal ?_
    have e : tagSq b E W (k + 1) k ω =
        sqOf W (freshD b E (pastXX E W k (pastCoords W k ω)) (freshSample W k ω)) := by
      rw [tagSq, h k hk, pastXX_eq]; rfl
    rw [e, pow_mul]
    refine pow_le_pow_left₀ (sqOf_nonneg _ _) ?_ q
    refine (sqOf_le_card W _).trans (le_of_eq ?_)
    rw [Fintype.card_fin]; field_simp
  have hstep : ∀ᵐ p ∂pastLaw W k b, p ∈ (Set.univ : Set (PastSample W k)) →
      ∫⁻ f, Φ (p, f) ∂freshLaw W b ≤ ENNReal.ofReal (CD ^ (4 * q)) := by
    filter_upwards [ae_pastLaw_hermitian W k b] with p hp _
    have hm : Measurable fun f => ‖freshD b E (pastXX E W k p) f‖ :=
      (measurable_freshD_comp b E measurable_const measurable_id).norm
    obtain ⟨hi, hb'⟩ := integral_abs_pow_le (ν := freshLaw W b) (n := 4 * q) (by omega) hCD
      ⟨hm.aestronglyMeasurable, hD _ (pastXX_isHermitian E hp)⟩
    simp only [Φ]
    rw [← ofReal_integral_eq_lintegral_ofReal (by simpa using hi)
      (Filter.Eventually.of_forall fun f => by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq_of_le (integral_congr_ae
      (Filter.Eventually.of_forall fun f => ?_)) hb')
    simp only [abs_of_nonneg (norm_nonneg _)]
  have h := lintegral_indicator_step (μ := growthPathLaw W b) (μP := pastLaw W k b)
    (ν := freshLaw W b) (measurable_pastCoords W k) (measurable_freshSample W k)
    (growthPathLaw_map_past_fresh W k b) MeasurableSet.univ hmΦ measurable_const hZ hstep
  simp only [Set.preimage_univ, Set.indicator_univ] at h
  refine h.trans (le_of_eq ?_)
  rw [lintegral_const, measure_univ, mul_one]

/-- **Birth of the first tag square** (`k = 0`), from `GaussianAbsorptionContract`. -/
theorem birth_sq_zero (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {q : ℕ} (hq : 1 ≤ q) :
    ∃ (B : ℝ) (W₀ : ℕ), 0 ≤ B ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∫⁻ ω, ENNReal.ofReal (tagSq b E W 1 0 ω ^ q) ∂growthPathLaw W b ≤ ENNReal.ofReal B := by
  obtain ⟨ε₁, C, hε₁, hC, hGA'⟩ := hGA b hb0 hb (etaLow b κ) 2 (etaLow_pos (by linarith) hκ)
  refine ⟨C ^ (4 * q), ⌈(4 * q : ℝ) / ε₁⌉₊ + 1, by positivity, fun W hW E hE => ?_⟩
  have hW0 : 0 < W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hpW : ((4 * q : ℕ) : ℝ) ≤ ε₁ * W := by
    have h1 := Nat.le_ceil ((4 * q : ℝ) / ε₁)
    have h2 : (((⌈(4 * q : ℝ) / ε₁⌉₊ + 1 : ℕ)) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2 ⊢
    rw [div_le_iff₀ hε₁] at h1
    nlinarith
  obtain ⟨-, hmom⟩ := hGA' W hW0 .oneBlockTwoPorts
    (0 : Matrix (PhysSite W .oneBlockTwoPorts) (PhysSite W .oneBlockTwoPorts) ℂ)
    Matrix.isHermitian_zero E (boundaryZ b E)
    (etaLow_le (by linarith) hκ hE) (bulk_norm_z hb0 hb hκ hE)
  have hm := hmom ((4 * q : ℕ) : ℝ) (by exact_mod_cast (show 1 ≤ 4 * q by omega)) hpW
  have hmG : Measurable fun s : LayerSample W .oneBlockTwoPorts =>
      ‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 s‖ :=
    (measurable_layerResolvent_two E _).norm
  have := isProbabilityMeasure_layerLaw W b .oneBlockTwoPorts
  obtain ⟨hi, hbd⟩ := integral_abs_pow_le (ν := layerLaw W b .oneBlockTwoPorts) (n := 4 * q)
    (by omega) hC.le ⟨hmG.aestronglyMeasurable, hm⟩
  have hpt : ∀ ω, tagSq b E W 1 0 ω ^ q ≤
      ‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 (sampleOne ω)‖ ^ (4 * q) := by
    intro ω
    set G := layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 (sampleOne ω)
    have hU : boundaryToInterior b E W 1 ω = G.toBlocks₁₂ := by
      rw [boundaryToInterior, fullInverse, fullPathMatrix_one_eq]; rfl
    have hnU : ‖G.toBlocks₁₂‖ ≤ ‖G‖ :=
      norm_submatrix_le G (f := Sum.inl) (g := Sum.inr) Sum.inl_injective Sum.inr_injective
    have hs := sqOf_le_card W G.toBlocks₁₂
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, one_mul] at hs
    have ht : tagSq b E W 1 0 ω ≤ ‖G‖ ^ 4 := by
      have e : tagSq b E W 1 0 ω = sqOf W G.toBlocks₁₂ := by
        rw [tagSq, tagResponse, tagProjection_one_zero, Matrix.mul_one, hU]; rfl
      rw [e]
      refine hs.trans ?_
      calc (W : ℝ)⁻¹ * (W * ‖G.toBlocks₁₂‖ ^ 4) = ‖G.toBlocks₁₂‖ ^ 4 := by field_simp
        _ ≤ ‖G‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hnU 4
    rw [pow_mul]
    exact pow_le_pow_left₀ (tagSq_nonneg b E 1 0 ω) ht q
  calc ∫⁻ ω, ENNReal.ofReal (tagSq b E W 1 0 ω ^ q) ∂growthPathLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal (‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0
          (sampleOne ω)‖ ^ (4 * q)) ∂growthPathLaw W b :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ∫⁻ s, ENNReal.ofReal (‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 s‖ ^ (4 * q))
          ∂layerLaw W b .oneBlockTwoPorts := by
        rw [← growthPathLaw_map_sampleOne, lintegral_map ((hmG.pow_const _).ennreal_ofReal)
          measurable_sampleOne]
    _ = ENNReal.ofReal (∫ s, |‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 s‖| ^ (4 * q)
          ∂layerLaw W b .oneBlockTwoPorts) := by
        rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun s => by
          positivity)]
        congr 1; funext s; rw [abs_of_nonneg (norm_nonneg _)]
    _ ≤ ENNReal.ofReal (C ^ (4 * q)) := ENNReal.ofReal_le_ofReal hbd

end BlockBand.SourceProcess.FullSource
