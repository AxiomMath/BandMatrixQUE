module

public import BlockBand.Transmission.PassiveLayer.WeightedLetters
public import BlockBand.Transmission.PassiveLayer.MomentAlgebra
public import BlockBand.Transmission.PassiveLayer.BlockNorms
public import BlockBand.Transmission.PassiveCovariance.Scalars

/-!
# The `moments` clause of the passive bounds lemma

`moments_holds (hGA : Layers.GaussianAbsorptionContract)` proves the field
`PassiveBoundsStatement.moments`: for `0 < b < 1/2`, `κ > 0`, `p ≥ 1` there are
`C, W₀` such that for `W ≥ W₀`, `E ∈ bulkInterval κ`, `w ∈ paramDisk b E` and every passive `X`,
under `freshLaw W b` the layer matrix is a.s. invertible and `‖𝒢‖`, `‖K𝒢₁₁‖`, `‖L‖` have
`L^p` norm `≤ C` (operator norm).

Proof (the lemmas cited from sibling modules are `layerAt_moment`, `gue_moment`, `ginibre_moment` and
`weighted_letters_le`):
* `disk_bounds`: `Im w ≥ η₀ = (1-b)κ/4`, `|w| ≤ 3`, `|E| < 2` on the disk;
* the cited `layerAt_moment` (Poisson average of `GaussianAbsorptionContract`) for `‖𝒢‖` at all
  exponents `≤ 4p ≤ ε₁W`;
* the cited `gue_moment`, `ginibre_moment` (by an ε-net) for `‖A‖`, `‖B‖`
  (`blockA_mom`, `bondB_mom`);
* the cited `weighted_letters_le`, with `weightBound_le`: a.e. domination of `‖K𝒢₁₁‖` and
  `‖L‖` by polynomials in `‖A‖, ‖B‖, ‖𝒢‖`;
* Minkowski and Hölder with explicit constants (`weight_mom`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.CoareaPalm
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal

open BlockBand.Transmission

variable {W : ℕ}

/-- On the parameter disk over `bulkInterval κ`: `Im w ≥ (1-b)κ/4`, `|w| ≤ 3`, `|E| < 2`. -/
theorem disk_bounds {b κ E : ℝ} {w : ℂ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) (hw : w ∈ paramDisk b E) :
    (1 - b) * κ / 4 ≤ w.im ∧ ‖w‖ ≤ 3 ∧ -2 < E ∧ E < 2 := by
  obtain ⟨hE1, hE2⟩ := hE
  have h1 : -2 < E := by linarith
  have h2 : E < 2 := by linarith
  have hη : etaZ b E = (1 - b) * Real.sqrt (4 - E ^ 2) / 2 :=
    Bridge.boundaryZ_im b E (by nlinarith)
  have hs : κ ≤ Real.sqrt (4 - E ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs2 : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hd : ‖w - boundaryZ b E‖ ≤ etaZ b E / 2 := by
    have := hw; rw [paramDisk, Metric.mem_closedBall, dist_eq_norm] at this; exact this
  have him : |w.im - (boundaryZ b E).im| ≤ etaZ b E / 2 := by
    have := Complex.abs_im_le_norm (w - boundaryZ b E)
    rw [Complex.sub_im] at this
    exact this.trans hd
  have hz : ‖boundaryZ b E‖ ≤ 1 + b := by
    rw [boundaryZ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_inv, norm_mul, norm_matchedA E h1 h2, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    simp
  refine ⟨?_, ?_, h1, h2⟩
  · have : (boundaryZ b E).im = etaZ b E := rfl
    rw [abs_le] at him
    rw [hη] at him this
    nlinarith
  · have := norm_le_norm_add_norm_sub' w (boundaryZ b E)
    rw [hη] at hd
    nlinarith

theorem measurable_layerAt (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (layerAt E w X) :=
  Bridge.measurable_matrix_inv.comp (measurable_layerMatrix E w X)

theorem measurable_g11 (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (g11 E w X) :=
  Measurable.of_eval_matrix _ fun _ _ => (measurable_layerAt E w X).eval_matrix
theorem measurable_g12 (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (g12 E w X) :=
  Measurable.of_eval_matrix _ fun _ _ => (measurable_layerAt E w X).eval_matrix
theorem measurable_g21 (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (g21 E w X) :=
  Measurable.of_eval_matrix _ fun _ _ => (measurable_layerAt E w X).eval_matrix
theorem measurable_g22 (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (g22 E w X) :=
  Measurable.of_eval_matrix _ fun _ _ => (measurable_layerAt E w X).eval_matrix
theorem measurable_kG11 (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (kG11 E w X) :=
  (continuous_const.matrix_mul continuous_id).measurable.comp (measurable_g11 E w X)
theorem measurable_lAt (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (lAt E w X) :=
  (continuous_const.matrix_mul continuous_id).measurable.comp (measurable_g12 E w X)

/-- Every letter is measurable (as needed for the `MemLp` bounds). -/
theorem measurable_passiveLetter (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (i : Fin 6) :
    Measurable fun ω => passiveLetter E w X ω i := by
  fin_cases i
  exacts [measurable_g11 E w X, measurable_g12 E w X, measurable_g21 E w X, measurable_g22 E w X,
    measurable_kG11 E w X, measurable_lAt E w X]

theorem blockA_mom {b : ℝ} (hb : b < 1 / 2) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℕ, 1 ≤ W → MomBd (freshLaw W b) (fun ω => ‖ω.1 0‖) p C := by
  obtain ⟨C, hC⟩ := gue_moment (c := 1 - 2 * b) (by linarith) hp
  have hp0 : 0 < p := by linarith
  refine ⟨(max C 0) ^ (1 / p), by positivity, fun W hW => ?_⟩
  have hm : Measurable fun ω : LayerSample W .oneBlockOnePort => ω.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  refine MomBd.of_lintegral (continuous_norm.measurable.comp hm).aestronglyMeasurable hp0
    (le_max_right _ _) ?_
  show ∫⁻ x, ‖‖x.1 0‖‖ₑ ^ p ∂freshLaw W b ≤ _
  simp only [enorm_norm]
  rw [show (∫⁻ x, ‖x.1 0‖ₑ ^ p ∂freshLaw W b) = ∫⁻ A, ‖A‖ₑ ^ p
      ∂((freshLaw W b).map fun ω => ω.1 0) from
      (lintegral_map (measurable_enorm.pow_const p) hm).symm, layerLaw_map_block]
  exact (hC W hW).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

theorem bondB_mom {b : ℝ} (hb0 : 0 < b) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℕ, 1 ≤ W → MomBd (freshLaw W b) (fun ω => ‖ω.2 0 0‖) p C := by
  obtain ⟨C, hC⟩ := ginibre_moment hb0 hp
  have hp0 : 0 < p := by linarith
  refine ⟨(max C 0) ^ (1 / p), by positivity, fun W hW => ?_⟩
  have hm : Measurable fun ω : LayerSample W .oneBlockOnePort => ω.2 0 0 :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp measurable_snd)
  refine MomBd.of_lintegral (continuous_norm.measurable.comp hm).aestronglyMeasurable hp0
    (le_max_right _ _) ?_
  show ∫⁻ x, ‖‖x.2 0 0‖‖ₑ ^ p ∂freshLaw W b ≤ _
  simp only [enorm_norm]
  rw [show (∫⁻ x, ‖x.2 0 0‖ₑ ^ p ∂freshLaw W b) = ∫⁻ A, ‖A‖ₑ ^ p
      ∂((freshLaw W b).map fun ω => ω.2 0 0) from
      (lintegral_map (measurable_enorm.pow_const p) hm).symm, layerLaw_map_bond]
  exact (hC W hW).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

theorem weight_mom {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {fA fB fG : Ω → ℝ} {q cA cB cG η : ℝ} (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hA : MomBd μ fA (2 * q) cA) (hB : MomBd μ fB (4 * q) cB) (hG : MomBd μ fG (2 * q) cG)
    (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) (hcG : 0 ≤ cG) :
    MomBd μ (fun x => 1 + (5 + fA x + η * (fB x * fB x)) * fG x) q
      (1 + (5 + cA + η * (cB * cB)) * cG) := by
  have hq0 : 0 < q := by linarith
  have hB' : MomBd μ fB (2 * (2 * q)) cB := by rwa [show 2 * (2 * q) = 4 * q by ring]
  have hBB : MomBd μ (fun x => fB x * fB x) (2 * q) (cB * cB) := MomBd.mul (by positivity) hB' hB' hcB
  have hηBB := hBB.const_mul hη
  have h5 : MomBd μ (fun _ => (5 : ℝ)) (2 * q) 5 := by
    simpa using MomBd.const (μ := μ) (5 : ℝ) (2 * q) (by positivity)
  have hP : MomBd μ (fun x => 5 + fA x + η * (fB x * fB x)) (2 * q) (5 + cA + η * (cB * cB)) :=
    (h5.add (by linarith) hA (by norm_num) hcA).add (by linarith) hηBB (by positivity)
      (by positivity)
  have hPG := hP.mul hq0 hG (by positivity)
  have h1 : MomBd μ (fun _ => (1 : ℝ)) q 1 := by simpa using MomBd.const (μ := μ) (1 : ℝ) q hq0
  exact h1.add hq hPG zero_le_one (by positivity)

theorem weightBound_le {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} {η₀ : ℝ} (hη₀ : 0 < η₀) (hw1 : η₀ ≤ w.im)
    (hw2 : ‖w‖ ≤ 3) (hE : |E| ≤ 2) :
    weightBound E w X ω ≤
      1 + (5 + ‖ω.1 0‖ + η₀⁻¹ * (‖ω.2 0 0‖ * ‖ω.2 0 0‖)) * ‖layerAt E w X ω‖ ∧
    ‖w‖⁻¹ ≤ η₀⁻¹ := by
  have hwn : η₀ ≤ ‖w‖ := hw1.trans (Complex.im_le_norm w)
  have hinv : ‖w‖⁻¹ ≤ η₀⁻¹ := inv_anti₀ hη₀ hwn
  refine ⟨?_, hinv⟩
  rw [weightBound]
  gcongr
  · linarith
  · rw [sq]

/-- **The `moments` clause of the passive bounds lemma**, from
`Layers.GaussianAbsorptionContract`. -/
theorem moments_holds (hGA : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        (∀ᵐ ω ∂freshLaw W b, IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω).det) ∧
        eLpNorm (fun ω => ‖layerAt E w X ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal C ∧
        eLpNorm (fun ω => ‖kG11 E w X ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal C ∧
        eLpNorm (fun ω => ‖lAt E w X ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal C := by
  intro b hb0 hb κ hκ p hp
  set η₀ := (1 - b) * κ / 4
  have hη₀ : 0 < η₀ := by have : 0 < 1 - b := by linarith
                          positivity
  have hp0 : 0 < p := by linarith
  obtain ⟨ε₁, CG, hε, hCG, hG⟩ := layerAt_moment hGA hb0 hb (M := 3) hη₀
  obtain ⟨CA, hCA0, hCA⟩ := blockA_mom hb (p := 4 * p) (by linarith)
  obtain ⟨CB, hCB0, hCB⟩ := bondB_mom hb0 (p := 8 * p) (by linarith)
  set Ck := 1 + (5 + CA + η₀⁻¹ * (CB * CB)) * CG
  set CL := η₀⁻¹ * (Ck * CB)
  refine ⟨CG + Ck + CL, ⌈4 * p / ε₁⌉₊ + 1, fun W hW E hE w hw X hY => ?_⟩
  obtain ⟨hw1, hw2, hE1, hE2⟩ := disk_bounds hb0 hb hκ hE hw
  have hW1 : 1 ≤ W := by omega
  have hpW : ∀ q, q ≤ 4 * p → q ≤ ε₁ * W := by
    intro q hq
    have h1 : 4 * p / ε₁ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈4 * p / ε₁⌉₊ ≤ W))
    rw [div_le_iff₀ hε] at h1; linarith
  have hGq : ∀ q, 1 ≤ q → q ≤ 4 * p →
      MomBd (freshLaw W b) (fun ω => ‖layerAt E w X ω‖) q CG := fun q hq hq4 =>
    ⟨(continuous_norm.measurable.comp (measurable_layerAt E w X)).aestronglyMeasurable,
      (hG W hW1 E w hw1 hw2 X hY q hq (hpW q hq4)).2⟩
  have hEabs : |E| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hCk0 : 0 ≤ Ck := by positivity
  have hdom : ∀ᵐ ω ∂freshLaw W b, ‖kG11 E w X ω‖ ≤
        1 + (5 + ‖ω.1 0‖ + η₀⁻¹ * (‖ω.2 0 0‖ * ‖ω.2 0 0‖)) * ‖layerAt E w X ω‖ ∧
      ‖lAt E w X ω‖ ≤ η₀⁻¹ * ((1 + (5 + ‖ω.1 0‖ + η₀⁻¹ * (‖ω.2 0 0‖ * ‖ω.2 0 0‖)) *
        ‖layerAt E w X ω‖) * ‖ω.2 0 0‖) := by
    filter_upwards [ae_good W hb0 hW1] with ω hω
    obtain ⟨hk, hl⟩ := weighted_letters_le E (lt_of_lt_of_le hη₀ hw1) hY hω.1 hω.2
    obtain ⟨hwb, hinv⟩ := weightBound_le (X := X) (ω := ω) hη₀ hw1 hw2 hEabs
    refine ⟨hk.trans hwb, hl.trans ?_⟩
    rw [mul_assoc]
    exact mul_le_mul hinv (mul_le_mul_of_nonneg_right hwb (norm_nonneg _))
      (mul_nonneg ((norm_nonneg _).trans hk) (norm_nonneg _)) (by positivity)
  -- kG11 at p
  have hk : MomBd (freshLaw W b) (fun ω => ‖kG11 E w X ω‖) p Ck := by
    refine MomBd.mono (weight_mom hp (by positivity)
      ((hCA W hW1).exponent_mono (by linarith)) ((hCB W hW1).exponent_mono (by linarith))
      (hGq (2 * p) (by linarith) (by linarith)) hCA0 hCB0 hCG.le)
      (continuous_norm.measurable.comp (measurable_kG11 E w X)).aestronglyMeasurable ?_
    filter_upwards [hdom] with ω h
    rw [norm_norm]; exact h.1
  -- lAt at p
  have hg2 := weight_mom (q := 2 * p) (by linarith) (inv_nonneg.mpr hη₀.le)
    ((hCA W hW1).exponent_mono (by linarith)) ((hCB W hW1).exponent_mono (by linarith))
    (hGq (2 * (2 * p)) (by linarith) (by linarith)) hCA0 hCB0 hCG.le
  have hl : MomBd (freshLaw W b) (fun ω => ‖lAt E w X ω‖) p CL := by
    have hgB := (hg2.mul hp0 ((hCB W hW1).exponent_mono (by linarith)) hCk0).const_mul
      (inv_nonneg.mpr hη₀.le)
    refine MomBd.mono hgB
      (continuous_norm.measurable.comp (measurable_lAt E w X)).aestronglyMeasurable ?_
    filter_upwards [hdom] with ω h
    rw [norm_norm]; exact h.2
  have hGp := hGq p hp (by linarith)
  have hCL0 : 0 ≤ CL := by positivity
  refine ⟨(hG W hW1 E w hw1 hw2 X hY p hp (hpW p (by linarith))).1,
    (hGp.of_le (by linarith)).2, (hk.of_le (by linarith)).2, (hl.of_le (by linarith)).2⟩

end BlockBand.Transmission.PassiveLayer
