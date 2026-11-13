module

public import BlockBand.Layers.CompensatedHeat
public import BlockBand.Layers.CoreTraces
public import BlockBand.Layers.CompensatedRing

/-!
# The compensated phase of the cores; assembly of the compensated contracts

The starting constant of the compensated-phase lemma: the input `CphCore` for the one- and
two-block cores, and then `CompensatedIncrementContract`, `CompensatedPhaseContract` and
`RingCompensatedPhaseContract` from `ConditionalBlockGUECount`, `GaussianLpGradient` and the two
mean-square hypotheses `ChtMeanSquare` and `ChtCoreMeanSquare` (proved as `chtMeanSquare_holds`
and `chtCoreMeanSquare_holds`).

Laws: `pathLaw W r₀ b`, `r₀ ∈ {1, 2}`; the one-block core is the image of
`layerLaw W b .oneBlockTwoPorts` under `coreOne` (`X = 0`), the two-block core the image of
`coreLaw2 W b` (internal bond `Gin(b/W)` ⊗ `.separate` layer, `X = -coreOff β`) under `coreTwo`
(`BlockBand.Layers.CoreTraces`). `E ∈ bulkInterval κ`, `z = z_∂(E)`.

* §1–3 **Core fluctuation** (not stated as such in the paper; the log-det gradient argument of
  `cpl_fluct_core`): `r₀ = 1` by `cpl_layer_bound` (`cht_core_one_fluct`);
  `r₀ = 2` in the core coordinates, internal bond included (`chtCoreF`, gradient
  `≤ 5‖(𝒢⁻¹+iκ)⁻¹‖/π` from `core_weighted_le`, `κ → 0` by `cpl_tendsto_phase`, Fatou;
  `cht_core2_fluct_core`, `cht_core_two_fluct`); `‖Ψ_{r₀} - EΨ_{r₀}‖_p ≤ C_p`.
* §4 `cht_main_general` (the heat step for any affine Gaussian path) and
  `cht_logDet_eq_of_tendsto` (the phase of a dissipative invertible matrix is the limit of its
  regularizations).
* §5–7 **Core means**: every Gaussian entry by `√t`, every diagonal by `a⁻¹ + t s_i a`
  (`chtCoreHeat1`, `chtCoreHeat2`); constant `(W/2) a² (r₀ + 2b)` (`cht_core1_integrand`,
  `cht_core2_integrand`), `φ(0) = π (r₀+2) W ℓ`, `φ(1) = π EΨ_{r₀}`; with the hypothesis
  `ChtCoreMeanSquare` (core trace errors `O_{L²}(W⁻¹)` uniformly in `t`):
  `EΨ_{r₀} = W[(r₀+2)ℓ + (r₀+2b)h/2] + O(W⁻¹)` (`cphCore_of_meanSquare`). Sections 1–7 do not
  use `CompensatedPhaseContract` or anything derived from it.
* §8 **Assembly**: `compensatedIncrement_holds_of_meanSquare`,
  `compensatedPhase_holds_of_meanSquare`, `ringCompensatedPhase_holds_of_meanSquare`
  (with `cphIncrementFluctuation_holds`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient)
open BlockBand.Internal.Contracts.CoareaPalm (negativeCount)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator InnerProductSpace

/-!
## 1. Transfer of the centered phase along a measure-preserving map
-/

section Transfer

theorem cht_transfer {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {W r : ℕ} {b E : ℝ}
    {Φ : Ω → PathSample W r} (hΦ : MeasurePreserving Φ μ (pathLaw W r b)) {p : ℝ≥0∞} {B : ℝ≥0∞}
    (hB : eLpNorm (fun q => cphPsiM b E (Φ q) - ∫ q', cphPsiM b E (Φ q') ∂μ) p μ ≤ B) :
    eLpNorm (fun ω => compensatedPhase b E ω - ∫ ω', compensatedPhase b E ω' ∂pathLaw W r b) p
      (pathLaw W r b) ≤ B := by
  have hae := cph_psi_ae_eq b E W r
  have hm := cph_measurable_psiM b E W r
  have hI : ∫ ω', compensatedPhase b E ω' ∂pathLaw W r b = ∫ q', cphPsiM b E (Φ q') ∂μ := by
    rw [integral_congr_ae hae, ← hΦ.map_eq, integral_map hΦ.measurable.aemeasurable
      hm.aestronglyMeasurable]
  rw [hI]
  have h1 : eLpNorm (fun ω => compensatedPhase b E ω - ∫ q', cphPsiM b E (Φ q') ∂μ) p
      (pathLaw W r b) = eLpNorm (fun ω => cphPsiM b E ω - ∫ q', cphPsiM b E (Φ q') ∂μ) p
      (pathLaw W r b) := eLpNorm_congr_ae (hae.mono fun ω hω => by simp only [hω])
  rw [h1, ← eLpNorm_comp_measurePreserving (hm.sub_const _).aestronglyMeasurable hΦ]
  exact hB

end Transfer

/-!
## 2. The fluctuation of the one-block core
-/

section CoreOne

theorem cht_coreOne_psi {b E : ℝ} {W : ℕ} (ℓ : LayerSample W .oneBlockTwoPorts)
    (hA : ∀ j, (ℓ.1 j).IsHermitian) :
    cphPsiM b E (coreOne ℓ) = (negativeCount (cplTop E 0 ℓ) : ℝ) +
      phaseCount (boundaryZ b E) (layerSchur .oneBlockTwoPorts E 0 ℓ) := by
  rw [← cph_psi_eq (ω := coreOne ℓ) hA]
  unfold compensatedPhase pathCount pathSchur
  rw [coreOne_pathMatrix, coreOne_portCoupling, layerSchur, sub_zero, cplTop, sub_zero]

/-- **Core fluctuation, `r₀ = 1`**: the one-block path is a `.oneBlockTwoPorts` layer with
`X = 0` (`coreOne`), so `cpl_layer_bound` applies. -/
theorem cht_core_one_fluct (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, ∀ (W : ℕ), 0 < W → ∀ E ∈ bulkInterval κ,
      eLpNorm (fun ω => compensatedPhase b E ω - ∫ ω', compensatedPhase b E ω' ∂pathLaw W 1 b)
        (ENNReal.ofReal p) (pathLaw W 1 b) ≤ ENNReal.ofReal C := by
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  have habs := gaussianAbsorption_holds hcount
  rcases (bulkInterval κ).eq_empty_or_nonempty with he | ⟨E₀, hE₀⟩
  · exact ⟨0, fun W _ E hE => by rw [he] at hE; exact absurd hE (Set.notMem_empty E)⟩
  set η₀ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
  have hη : 0 < η₀ := (commonZ_im_pos_of_mem_bulkInterval hb1 hκ hE₀).1
  obtain ⟨ε₁, CA, hε₁, -, habs'⟩ := habs b hb0 hb1 η₀ 3 hη
  refine ⟨max (Cg * Real.sqrt p * (8 / Real.pi) * CA) (8 * p / ε₁), fun W hW E hE => ?_⟩
  obtain ⟨-, hzη, hz3, -, -⟩ := cht_bulk_facts hb0 hb1 hκ hE
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη hzη
  obtain ⟨hinv, hmom⟩ := habs' W hW .oneBlockTwoPorts 0 isHermitian_zero E (boundaryZ b E) hzη hz3
  have hmp := coreOne_measurePreserving W b
  have hGm : Measurable (fun ℓ : LayerSample W .oneBlockTwoPorts => cphPsiM b E (coreOne ℓ)) :=
    (cph_measurable_psiM b E W 1).comp hmp.measurable
  have hGb : ∀ ℓ : LayerSample W .oneBlockTwoPorts, |cphPsiM b E (coreOne ℓ)| ≤ 4 * W := by
    intro ℓ
    have h := cph_abs_psiM_le hz.le (coreOne ℓ)
    have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    push_cast at h
    linarith
  refine cht_transfer hmp ?_
  exact cpl_layer_bound hCg.le hgr hε₁ hW hb0 hb1 .oneBlockTwoPorts isHermitian_zero E hz hp hinv
    hmom hGm hGb (fun ℓ hA => cht_coreOne_psi ℓ hA) (c := 0) (ae_of_all _ fun ℓ => by ring)

end CoreOne

/-!
## 3. The fluctuation of the two-block core (gradient argument in the core coordinates)
-/

section CoreTwo

theorem cht_reg_coercive {W : ℕ} {σ : LayerShape} (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) {ω : LayerSample W σ}
    (hA : (Internal.Contracts.Layers.blockDiag ω.1).IsHermitian) {κ : ℝ} (hκ : 0 < κ) :
    cplCoercive κ (tflReg κ (layerMatrix σ E z X ω)) := by
  rw [cpl_tflReg_layerMatrix]
  have hD : (cplTop E X ω).IsHermitian := layerDiag_isHermitian E X hX ω hA
  have hA' := cpl_coercive_herm_add hD (κ := κ)
  have hZ : cplCoercive κ ((z + (κ : ℂ) * Complex.I) • (1 : Matrix (PortSite W σ) _ ℂ)) := by
    refine cpl_coercive_mono ?_ cpl_coercive_scalar
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one]
    linarith
  have h := cpl_coercive_schurPath hκ hA' hZ (bondMatrix σ ω.2) zero_le_one le_rfl
  simpa using h

theorem cht_corePsi_eq (W : ℕ) (b E : ℝ) (z : ℂ) (κ : ℝ) (x : CoreCoord W → ℝ) :
    corePsi (coreC0 W E z) (coreLin W b) κ x =
      tflReg κ (layerMatrix .separate E z (-coreOff (coreEmbed W b x).1) (coreEmbed W b x).2) := by
  rw [← core_matrix_eq, corePsi, tflReg]; abel

theorem cht_corePsi_coercive (W : ℕ) (b E : ℝ) {z : ℂ} (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : CoreCoord W → ℝ) : cplCoercive κ (corePsi (coreC0 W E z) (coreLin W b) κ x) := by
  rw [cht_corePsi_eq]
  exact cht_reg_coercive E hz (coreOff_isHermitian _).neg
    (tflEmbed_blockDiag_isHermitian W b .separate _) hκ

/-- The regularized phase `π⁻¹ Im L(𝒢⁻¹ + iκ)` of the two-block core in its coordinates. -/
def chtCoreF (W : ℕ) (b E : ℝ) (z : ℂ) (κ : ℝ) (x : CoreCoord W → ℝ) : ℂ :=
  cplOut (cplLogDet (corePsi (coreC0 W E z) (coreLin W b) κ x))

theorem chtCoreF_contDiff (W : ℕ) (b E : ℝ) {z : ℂ} (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ 1 (chtCoreF W b E z κ) := by
  have hL : ContDiff ℝ 1 (corePsi (coreC0 W E z) (coreLin W b) κ) :=
    contDiff_const.add (coreLin W b).contDiff
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have h := cpl_contDiffAt_logDet ⟨κ, hκ, cht_corePsi_coercive W b E hz hκ x⟩
  exact cplOut.contDiff.contDiffAt.comp x (h.comp x hL.contDiffAt)

theorem chtCoreF_fderiv (W : ℕ) (b E : ℝ) {z : ℂ} (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x v : CoreCoord W → ℝ) :
    fderiv ℝ (chtCoreF W b E z κ) x v =
      cplOut ((Ring.inverse (corePsi (coreC0 W E z) (coreLin W b) κ x) * coreLin W b v).trace) := by
  have hL : HasFDerivAt (corePsi (coreC0 W E z) (coreLin W b) κ) (coreLin W b) x :=
    (coreLin W b).hasFDerivAt.const_add _
  have h1 := (cpl_hasFDerivAt_logDet ⟨κ, hκ, cht_corePsi_coercive W b E hz hκ x⟩).comp x hL
  have h2 := cplOut.hasFDerivAt.comp x h1
  rw [show chtCoreF W b E z κ = cplOut ∘ (cplLogDet ∘ corePsi (coreC0 W E z) (coreLin W b) κ)
    from rfl, h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, cplTrMul_apply]

theorem chtCoreF_norm_le (W : ℕ) (b E : ℝ) {z : ℂ} (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : CoreCoord W → ℝ) : ‖chtCoreF W b E z κ x‖ ≤ 4 * W := by
  have hb := cpl_im_logDet_bounds ⟨κ, hκ, cht_corePsi_coercive W b E hz hκ x⟩
  have hc := tfl_card_layerSite_le W .separate
  rw [chtCoreF, cplOut_apply, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos,
    abs_of_nonneg hb.1, div_le_iff₀ Real.pi_pos]
  exact hb.2.trans (mul_le_mul_of_nonneg_right hc Real.pi_pos.le)

/-- **Gradient bound** in the core coordinates: `≤ 5 ‖(𝒢⁻¹ + iκ)⁻¹‖ / π` (`core_weighted_le`). -/
theorem chtCoreF_gradient_le {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (E : ℝ)
    {z : ℂ} (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) (x : CoreCoord W → ℝ) :
    weightedGradientNorm (coreVar W b) (chtCoreF W b E z κ) x ≤
      5 * ‖Ring.inverse (corePsi (coreC0 W E z) (coreLin W b) κ x)‖ / Real.pi := by
  set R := Ring.inverse (corePsi (coreC0 W E z) (coreLin W b) κ x) with hR
  have hder : ∀ i, ‖fderiv ℝ (chtCoreF W b E z κ) x (Pi.single i 1)‖ ^ 2 ≤
      ‖(R * coreLin W b (Pi.single i 1)).trace‖ ^ 2 / Real.pi ^ 2 := by
    intro i
    rw [chtCoreF_fderiv W b E hz hκ, ← hR, ← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (cpl_norm_out_le _) 2
  have hsum : ∑ i, (coreVar W b i : ℝ) * ‖fderiv ℝ (chtCoreF W b E z κ) x (Pi.single i 1)‖ ^ 2 ≤
      (5 * ‖R‖ / Real.pi) ^ 2 := by
    calc ∑ i, (coreVar W b i : ℝ) * ‖fderiv ℝ (chtCoreF W b E z κ) x (Pi.single i 1)‖ ^ 2
        ≤ ∑ i, (coreVar W b i : ℝ) * (‖(R * coreLin W b (Pi.single i 1)).trace‖ ^ 2 /
            Real.pi ^ 2) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hder i) (NNReal.coe_nonneg _)
      _ = (∑ i, (coreVar W b i : ℝ) * ‖(R * coreLin W b (Pi.single i 1)).trace‖ ^ 2) /
            Real.pi ^ 2 := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (5 ^ 2 * ‖R‖ ^ 2) / Real.pi ^ 2 := by
          gcongr; exact core_weighted_le hW hb0 hb1 R
      _ = (5 * ‖R‖ / Real.pi) ^ 2 := by ring
  unfold weightedGradientNorm
  calc Real.sqrt (∑ i, (coreVar W b i : ℝ) *
        ‖fderiv ℝ (chtCoreF W b E z κ) x (Pi.single i 1)‖ ^ 2)
      ≤ Real.sqrt ((5 * ‖R‖ / Real.pi) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 5 * ‖R‖ / Real.pi := Real.sqrt_sq (by positivity)

/-- **The `κ → 0` limit** in the core coordinates. -/
theorem chtCoreF_tendsto (W : ℕ) (b E : ℝ) {z : ℂ} (hz : 0 < z.im) (x : CoreCoord W → ℝ)
    (hD : IsUnit (cplTop E (-coreOff (coreEmbed W b x).1) (coreEmbed W b x).2).det) :
    Tendsto (fun j => chtCoreF W b E z (cplKappa j) x) atTop
      (𝓝 (((negativeCount (cplTop E (-coreOff (coreEmbed W b x).1) (coreEmbed W b x).2) : ℝ) +
        phaseCount z (layerSchur .separate E (-coreOff (coreEmbed W b x).1)
          (coreEmbed W b x).2) : ℝ) : ℂ)) := by
  have hDh : (cplTop E (-coreOff (coreEmbed W b x).1) (coreEmbed W b x).2).IsHermitian :=
    layerDiag_isHermitian E _ (coreOff_isHermitian _).neg _
      (tflEmbed_blockDiag_isHermitian W b .separate _)
  have h := cpl_tendsto_phase hDh hD (bondMatrix .separate (coreEmbed W b x).2.2) hz
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h
  refine h2.congr fun j => ?_
  simp only [Function.comp_apply, chtCoreF, cplOut_apply]
  rw [cht_corePsi_eq, cpl_tflReg_layerMatrix]

/-- **Core fluctuation bound, `r₀ = 2`** (the argument of `cpl_fluct_core` in the core
coordinates, internal bond included): `‖G - EG‖_p ≤ C_g √p (10/π) C_A`. -/
theorem cht_core2_fluct_core {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (E : ℝ) {z : ℂ}
    (hz : 0 < z.im) {p : ℝ} (hp : 1 ≤ p) {CA : ℝ}
    (hinv : ∀ᵐ q ∂coreLaw2 W b, IsUnit (layerMatrix .separate E z (-coreOff q.1) q.2).det)
    (hD : ∀ᵐ q ∂coreLaw2 W b, IsUnit (cplTop E (-coreOff q.1) q.2).det)
    (hmom : eLpNorm (fun q => ‖coreG2 E z q‖) (ENNReal.ofReal p) (coreLaw2 W b) ≤ ENNReal.ofReal CA)
    {G : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate → ℝ} (hG : Measurable G)
    (hGeq : ∀ q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate,
      (∀ j, (q.2.1 j).IsHermitian) →
      G q = (negativeCount (cplTop E (-coreOff q.1) q.2) : ℝ) +
        phaseCount z (layerSchur .separate E (-coreOff q.1) q.2)) :
    eLpNorm (fun q => G q - ∫ q', G q' ∂coreLaw2 W b) (ENNReal.ofReal p) (coreLaw2 W b) ≤
      ENNReal.ofReal (Cg * Real.sqrt p * (10 / Real.pi) * CA) := by
  set μ := gaussianProduct (coreVar W b) with hμ
  set Φ := coreEmbed W b with hΦdef
  have hΦ : Measurable Φ := core_measurable_embed W b
  have hlaw : coreLaw2 W b = μ.map Φ := by rw [coreLaw2, core_law_eq_map]
  have hz0 : 0 ≤ z.im := hz.le
  set Gc : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate → ℂ := fun q => (G q : ℂ) with hGcdef
  have hGc : Measurable Gc := Complex.measurable_ofReal.comp hG
  have hreal : eLpNorm (fun q => G q - ∫ q', G q' ∂coreLaw2 W b) (ENNReal.ofReal p)
      (coreLaw2 W b) =
      eLpNorm (fun q => Gc q - ∫ q', Gc q' ∂coreLaw2 W b) (ENNReal.ofReal p) (coreLaw2 W b) := by
    have hint : ∫ q', Gc q' ∂coreLaw2 W b = ((∫ q', G q' ∂coreLaw2 W b : ℝ) : ℂ) :=
      integral_ofReal
    refine eLpNorm_congr_norm_ae (hG.sub_const _).aestronglyMeasurable
      (hGc.sub_const _).aestronglyMeasurable (ae_of_all _ fun q => ?_)
    rw [hint, hGcdef, ← Complex.ofReal_sub, Complex.norm_real]
  rw [hreal]
  set F : (CoreCoord W → ℝ) → ℂ := fun x => Gc (Φ x) with hFdef
  have hF : Measurable F := hGc.comp hΦ
  have htransfer : eLpNorm (fun q => Gc q - ∫ q', Gc q' ∂coreLaw2 W b) (ENNReal.ofReal p)
      (coreLaw2 W b) = eLpNorm (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ := by
    rw [hlaw, integral_map hΦ.aemeasurable hGc.aestronglyMeasurable,
      eLpNorm_map_measure (hGc.sub_const _).aestronglyMeasurable hΦ.aemeasurable]
    rfl
  rw [htransfer]
  have hinvμ : ∀ᵐ x ∂μ, IsUnit (coreC0 W E z + coreLin W b x).det := core_ae_coords hinv
  have hDμ : ∀ᵐ x ∂μ, IsUnit (cplTop E (-coreOff (Φ x).1) (Φ x).2).det := by
    rw [hlaw] at hD
    exact ae_of_ae_map hΦ.aemeasurable hD
  have hmomμ : eLpNorm (fun x => ‖(coreC0 W E z + coreLin W b x)⁻¹‖) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal CA := by
    rw [hlaw, eLpNorm_map_measure (measurable_coreG2 E z).norm.aestronglyMeasurable
      hΦ.aemeasurable] at hmom
    refine le_of_eq_of_le ?_ hmom
    congr 1
    funext x
    simp only [Function.comp_apply, hΦdef, coreG2_embed]
  set c : ℝ := 10 / Real.pi with hc
  have hc0 : 0 ≤ c := by positivity
  set Bd : ℝ≥0∞ := ENNReal.ofReal (Cg * Real.sqrt p * c * CA) with hBd
  have hstep : ∀ κ : ℝ, 0 < κ →
      eLpNorm (fun x => chtCoreF W b E z κ x - ∫ y, chtCoreF W b E z κ y ∂μ)
        (ENNReal.ofReal p) μ ≤ Bd := by
    intro κ hκ
    have hC := chtCoreF_contDiff W b E hz0 hκ
    have hcont : Continuous (chtCoreF W b E z κ) := hC.continuous
    have hmem : MemLp (chtCoreF W b E z κ) (ENNReal.ofReal p) μ :=
      MemLp.of_bound hcont.aestronglyMeasurable (4 * W)
        (ae_of_all _ fun x => chtCoreF_norm_le W b E hz0 hκ x)
    have h1 := hgr p hp (CoreCoord W) (coreVar W b) (chtCoreF W b E z κ) hC hmem
    refine h1.trans ?_
    have hwc : Continuous (weightedGradientNorm (coreVar W b) (chtCoreF W b E z κ)) := by
      have hd := hC.continuous_fderiv one_ne_zero
      unfold weightedGradientNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    have hwle : ∀ᵐ x ∂μ, ‖weightedGradientNorm (coreVar W b) (chtCoreF W b E z κ) x‖ ≤
        ‖c * ‖(coreC0 W E z + coreLin W b x)⁻¹‖‖ := by
      filter_upwards [hinvμ] with x hx
      have hg := chtCoreF_gradient_le hW hb0 hb1 E hz0 hκ x
      have h2 := coreG_le_two (core_reg W b E hz0) hκ hx
      have hg0 : 0 ≤ weightedGradientNorm (coreVar W b) (chtCoreF W b E z κ) x :=
        Real.sqrt_nonneg _
      rw [Real.norm_of_nonneg hg0, Real.norm_of_nonneg (by positivity)]
      refine hg.trans ?_
      calc 5 * ‖Ring.inverse (corePsi (coreC0 W E z) (coreLin W b) κ x)‖ / Real.pi
          ≤ 5 * (2 * ‖(coreC0 W E z + coreLin W b x)⁻¹‖) / Real.pi := by
            gcongr; exact h2
        _ = c * ‖(coreC0 W E z + coreLin W b x)⁻¹‖ := by rw [hc]; ring
    have h4 := eLpNorm_mono_ae (p := ENNReal.ofReal p) hwc.aestronglyMeasurable hwle
    have h5 : eLpNorm (fun x => c * ‖(coreC0 W E z + coreLin W b x)⁻¹‖) (ENNReal.ofReal p) μ =
        ENNReal.ofReal c * eLpNorm (fun x => ‖(coreC0 W E z + coreLin W b x)⁻¹‖)
          (ENNReal.ofReal p) μ := by
      rw [show (fun x => c * ‖(coreC0 W E z + coreLin W b x)⁻¹‖) =
        c • (fun x => ‖(coreC0 W E z + coreLin W b x)⁻¹‖) from rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal hc0]
    calc ENNReal.ofReal (Cg * Real.sqrt p) *
          eLpNorm (weightedGradientNorm (coreVar W b) (chtCoreF W b E z κ)) (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal (Cg * Real.sqrt p) * (ENNReal.ofReal c * ENNReal.ofReal CA) := by
          gcongr
          exact h4.trans (h5.le.trans (by gcongr))
      _ = Bd := by
          rw [hBd, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
  set Fm : ℕ → (CoreCoord W → ℝ) → ℂ := fun j => chtCoreF W b E z (cplKappa j) with hFm
  have hFmc : ∀ j, Continuous (Fm j) := fun j =>
    (chtCoreF_contDiff W b E hz0 (cpl_kappa_pos j)).continuous
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun j => Fm j x) atTop (𝓝 (F x)) := by
    filter_upwards [hDμ] with x hx
    have h := chtCoreF_tendsto W b E hz x hx
    have hFx : F x = (((negativeCount (cplTop E (-coreOff (coreEmbed W b x).1)
        (coreEmbed W b x).2) : ℝ) + phaseCount z (layerSchur .separate E
          (-coreOff (coreEmbed W b x).1) (coreEmbed W b x).2) : ℝ) : ℂ) := by
      simp only [hFdef, hGcdef, hΦdef]
      rw [hGeq _ fun j => gueOfCoords_isHermitian _ _ _]
    rw [hFx]
    exact h
  have hbound : ∀ j, ∀ᵐ x ∂μ, ‖Fm j x‖ ≤ 4 * W := fun j =>
    ae_of_all _ fun x => chtCoreF_norm_le W b E hz0 (cpl_kappa_pos j) x
  have hint : Tendsto (fun j => ∫ x, Fm j x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (4 * W : ℝ))
      (fun j => (hFmc j).aestronglyMeasurable) (integrable_const _) hbound hconv
  have hconv2 : ∀ᵐ x ∂μ, Tendsto (fun j => Fm j x - ∫ y, Fm j y ∂μ) atTop
      (𝓝 (F x - ∫ y, F y ∂μ)) := hconv.mono fun x hx => hx.sub hint
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun j => ((hFmc j).sub continuous_const).aestronglyMeasurable)
    (fun x => F x - ∫ y, F y ∂μ) (hF.sub_const _).aestronglyMeasurable hconv2
  refine hfatou.trans (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun j => ?_))
  exact hstep (cplKappa j) (cpl_kappa_pos j)

theorem cht_coreTwo_psi {b E : ℝ} {W : ℕ} (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate)
    (hA : ∀ j, (q.2.1 j).IsHermitian) :
    cphPsiM b E (coreTwo q) = (negativeCount (cplTop E (-coreOff q.1) q.2) : ℝ) +
      phaseCount (boundaryZ b E) (layerSchur .separate E (-coreOff q.1) q.2) := by
  rw [← cph_psi_eq (ω := coreTwo q) hA]
  have e : pathMatrix (coreTwo q) - (E : ℂ) • 1 = cplTop E (-coreOff q.1) q.2 := by
    rw [coreTwo_pathMatrix, cplTop, sub_neg_eq_add]; abel
  unfold compensatedPhase pathCount pathSchur
  rw [e, coreTwo_portCoupling, layerSchur]

theorem cht_ae_top2 {W : ℕ} {b : ℝ} (hb : b < 1 / 2) (E : ℝ) :
    ∀ᵐ q ∂coreLaw2 W b, IsUnit (cplTop E (-coreOff q.1) q.2).det := by
  have hm : Measurable (fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate =>
      (cplTop E (-coreOff q.1) q.2).det) := by
    refine (continuous_id.matrix_det).measurable.comp ?_
    exact (((srec_continuous_blockDiag 2 W).measurable.comp
      (measurable_fst.comp measurable_snd)).sub measurable_const).sub
      ((measurable_coreOff W).comp measurable_fst).neg
  have hmeas : MeasurableSet {q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate |
      IsUnit (cplTop E (-coreOff q.1) q.2).det} := by
    have : {q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate |
        IsUnit (cplTop E (-coreOff q.1) q.2).det} =
        (fun q => (cplTop E (-coreOff q.1) q.2).det) ⁻¹' {0}ᶜ := by
      ext q; simp [isUnit_iff_ne_zero]
    rw [this]
    exact hm (measurableSet_singleton 0).compl
  rw [coreLaw2]
  exact core_ae_prod _ _ hmeas fun β => srec_ae_isUnit_top hb .separate E (-coreOff β)

/-- **Core fluctuation, `r₀ = 2`**: `‖Ψ₂ - EΨ₂‖_p ≤ C_p` uniformly in `W ≥ 1` and `E ∈ I`. -/
theorem cht_core_two_fluct (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, ∀ (W : ℕ), 0 < W → ∀ E ∈ bulkInterval κ,
      eLpNorm (fun ω => compensatedPhase b E ω - ∫ ω', compensatedPhase b E ω' ∂pathLaw W 2 b)
        (ENNReal.ofReal p) (pathLaw W 2 b) ≤ ENNReal.ofReal C := by
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  have habs := gaussianAbsorption_holds hcount
  rcases (bulkInterval κ).eq_empty_or_nonempty with he | ⟨E₀, hE₀⟩
  · exact ⟨0, fun W _ E hE => by rw [he] at hE; exact absurd hE (Set.notMem_empty E)⟩
  set η₀ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
  have hη : 0 < η₀ := (commonZ_im_pos_of_mem_bulkInterval hb1 hκ hE₀).1
  obtain ⟨ε₁, CA, hε₁, -, habs'⟩ := habs b hb0 hb1 η₀ 3 hη
  refine ⟨max (Cg * Real.sqrt p * (10 / Real.pi) * CA) (8 * p / ε₁), fun W hW E hE => ?_⟩
  obtain ⟨-, hzη, hz3, -, -⟩ := cht_bulk_facts hb0 hb1 hκ hE
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη hzη
  have hmp : MeasurePreserving (coreTwo (W := W)) (coreLaw2 W b) (pathLaw W 2 b) :=
    coreTwo_measurePreserving W b
  have hGm : Measurable (fun q => cphPsiM b E (coreTwo (W := W) q)) :=
    (cph_measurable_psiM b E W 2).comp hmp.measurable
  refine cht_transfer hmp ?_
  by_cases hpW : p ≤ ε₁ * W
  · have hinv := core_ae_unit2 (b := b) (E := E) (z := boundaryZ b E)
      (fun X hX => (habs' W hW .separate X hX E (boundaryZ b E) hzη hz3).1)
    have hp0 : ENNReal.ofReal p ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
    have hmom := core_mom2 (b := b) (E := E) (z := boundaryZ b E) hp0 ENNReal.ofReal_ne_top
      (fun X hX => (habs' W hW .separate X hX E (boundaryZ b E) hzη hz3).2 p hp hpW)
    exact (cht_core2_fluct_core hCg.le hgr hW hb0 hb1 E hz hp hinv (cht_ae_top2 hb1 E) hmom hGm
      (fun q hA => cht_coreTwo_psi q hA)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · have hW' : (W : ℝ) < p / ε₁ := by
      rw [lt_div_iff₀ hε₁]; linarith [not_le.mp hpW]
    have hGb : ∀ q, |cphPsiM b E (coreTwo (W := W) q)| ≤ 4 * W := by
      intro q
      have h := cph_abs_psiM_le hz.le (coreTwo q)
      push_cast at h
      linarith
    have hIb : |∫ q', cphPsiM b E (coreTwo (W := W) q') ∂coreLaw2 W b| ≤ 4 * W :=
      cph_abs_integral_le hGb
    have hb : ∀ᵐ q ∂coreLaw2 W b, ‖cphPsiM b E (coreTwo q) -
        ∫ q', cphPsiM b E (coreTwo (W := W) q') ∂coreLaw2 W b‖ ≤ 8 * W :=
      ae_of_all _ fun q => by
        rw [Real.norm_eq_abs]
        have := hGb q
        rw [abs_le] at this hIb ⊢
        constructor <;> linarith
    refine (eLpNorm_le_of_ae_bound (hGm.sub_const _).aestronglyMeasurable hb).trans ?_
    rw [measure_univ, ENNReal.one_rpow, one_mul]
    refine ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans' ?_)
    rw [mul_div_assoc]
    linarith

end CoreTwo

/-!
## 4. General mean step and the phase of a dissipative limit
-/

section General

/-- **The heat step, abstract form**: under coercivity on `[0, 1)` and a.s. invertibility at
`t = 1`, `‖φ'_ℂ(t) - c₀‖ ≤ K` on `(0, 1)` gives `|φ(1) - φ(0) - Im c₀| ≤ K`. -/
theorem cht_main_general {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
    {n : Type} [Fintype n] [DecidableEq n] {C₀ C₁ : Matrix n n ℂ}
    {Lin : (ι → ℝ) →L[ℝ] Matrix n n ℂ} (hL : ∀ x, (Lin x).IsHermitian)
    (hcoer : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ cplCoercive δ (C₀ + t • C₁))
    (hunit : ∀ᵐ x ∂gaussianProduct v, IsUnit (C₀ + C₁ + Lin x)) {c₀ : ℂ} {K : ℝ}
    (hbd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ‖chtDeriv v C₀ C₁ Lin t - c₀‖ ≤ K) :
    |chtPhi v C₀ C₁ Lin 1 - chtPhi v C₀ C₁ Lin 0 - c₀.im| ≤ K := by
  refine cht_mvt (cht_phi_continuousOn v hL hcoer hunit)
    (fun t ht => cht_hasDerivAt_phi v hL hcoer ht) fun t ht => ?_
  rw [← Complex.sub_im]
  exact (Complex.abs_im_le_norm _).trans (hbd t ht)

theorem cht_form_reg {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (κ : ℝ)
    (v : n → ℂ) : cplForm (tflReg κ M) v = cplForm M v + κ * cplSq v := by
  have e : ((κ : ℂ) * Complex.I) • (1 : Matrix n n ℂ) = κ • (Complex.I • (1 : Matrix n n ℂ)) := by
    rw [← Complex.coe_smul, smul_smul]
  rw [tflReg, cpl_form_add, e, cpl_form_smul, cpl_form_I_one]

/-- **The phase of a dissipative invertible matrix** is the limit of its regularizations:
if `π⁻¹ Im L(M + iκ_j) → y` then `Im L(M) = π y` (`cht_continuousAt_logDet`). -/
theorem cht_logDet_eq_of_tendsto {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hreg : cplCoercive 1 (tflReg 1 M)) (hMu : IsUnit M) {y : ℝ}
    (h : Tendsto (fun j => cplOut (cplLogDet (tflReg (cplKappa j) M))) atTop (𝓝 (y : ℂ))) :
    (cplLogDet M).im = Real.pi * y := by
  have hdis : ∀ v, 0 ≤ cplForm M v := by
    intro v
    have := hreg v
    rw [cht_form_reg] at this
    linarith
  have h1 := (cplOut.continuous.tendsto _).comp
    ((cht_continuousAt_logDet hdis hMu).tendsto.comp (cht_tendsto_reg M))
  have h2 := tendsto_nhds_unique h1 h
  rw [cplOut_apply, Complex.ofReal_inj] at h2
  rw [← h2]
  field_simp

end General

/-!
## 5. The heat paths of the cores
-/

section CorePath

variable {W : ℕ} (σ : LayerShape) (b E : ℝ)

/-- `C₀ = a⁻¹` on every site of a core. -/
def chtKC0 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := (matchedA E)⁻¹ • 1

/-- **The heat matrix of the one-block core** (every Gaussian entry by `√t`, every diagonal by
`a⁻¹ + t s_i a`, `s_i` the variance row sum: `1` on the block, `b` on the ports):
`a⁻¹ + t [[a, 0], [0, ba]] + √t [[A, B], [Bᴴ, 0]]` on the `.oneBlockTwoPorts` layer. -/
def chtCoreHeat1 (t : ℝ) (ω : LayerSample W .oneBlockTwoPorts) :
    Matrix (LayerSite W .oneBlockTwoPorts) (LayerSite W .oneBlockTwoPorts) ℂ :=
  chtKC0 .oneBlockTwoPorts E + t • chtC1 .oneBlockTwoPorts 0 E b +
    Real.sqrt t • chtLinS .oneBlockTwoPorts ω

/-- **The heat matrix of the two-block core**, internal bond `β` included. -/
def chtCoreHeat2 (t : ℝ) (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate) :
    Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  chtKC0 .separate E + t • chtC1 .separate 0 E b +
    Real.sqrt t • (chtLinS .separate q.2 + coreLb q.1)

variable {σ b E}

theorem cht_core_coercive (hb0 : 0 ≤ b) (hb1 : b < 1 / 2) (hE : |E| < 2) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧
      cplCoercive δ (chtKC0 (W := W) σ E + t • chtC1 σ 0 E b) := by
  intro t ht
  have ha := matchedA_im_neg hE
  set γ := -(matchedA E).im with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hinv : ((matchedA E)⁻¹).im = γ := by
    rw [inv_matchedA hE.le, Complex.conj_im]
  have h1 : 0 < (1 - t) * γ := by
    have : 0 < 1 - t := by linarith [ht.2]
    positivity
  have h2 : 0 < (1 - t * b) * γ := by
    have : t * b ≤ 1 * b := mul_le_mul_of_nonneg_right ht.2.le hb0
    have : 0 < 1 - t * b := by linarith
    positivity
  refine ⟨min ((1 - t) * γ) ((1 - t * b) * γ), lt_min h1 h2, ?_⟩
  have heq : chtKC0 (W := W) σ E + t • chtC1 σ 0 E b =
      fromBlocks (((matchedA E)⁻¹ + (t : ℂ) * matchedA E) • 1) 0 0
        (((matchedA E)⁻¹ + (t : ℂ) * ((b : ℂ) * matchedA E)) • 1) := by
    rw [chtKC0, chtC1, ← fromBlocks_one, fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
    simp only [smul_zero, add_zero]
    congr 1
    · ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        Complex.real_smul]
      split_ifs <;> push_cast <;> ring
    · ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        Complex.real_smul]
      split_ifs <;> ring
  rw [heq]
  refine cht_coercive_fromBlocks (lt_min h1 h2) ?_ ?_
  · refine cpl_coercive_mono (min_le_left _ _) (cpl_coercive_mono (le_of_eq ?_) cpl_coercive_scalar)
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, hinv, hγ]
    ring
  · refine cpl_coercive_mono (min_le_right _ _) (cpl_coercive_mono (le_of_eq ?_) cpl_coercive_scalar)
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, hinv, Complex.mul_re, sub_zero, hγ]
    ring

theorem cht_core_C0_add_C1 (hE : |E| ≤ 2) :
    chtKC0 (W := W) σ E + chtC1 σ 0 E b = tflConst σ E (boundaryZ b E) 0 := by
  have h := matchedA_add_inv hE
  rw [chtKC0, chtC1, tflConst, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  simp only [smul_zero, add_zero, sub_zero]
  congr 1
  · rw [← add_smul, ← neg_smul, ← h]
    congr 1; push_cast; ring
  · rw [← add_smul, boundaryZ]

theorem cht_logDet_KC0 (hE : |E| < 2) :
    (cplLogDet (chtKC0 (W := W) σ E)).im =
      Real.pi * (((σ.blocks + σ.ports) * W : ℕ) * phaseEll E) := by
  have hinv : 0 < ((matchedA E)⁻¹).im := by
    rw [inv_matchedA hE.le, Complex.conj_im]; linarith [matchedA_im_neg hE]
  rw [chtKC0, cht_logDet_scalar hinv]
  unfold phaseEll
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  push_cast
  field_simp

end CorePath

/-!
## 6. The heat derivative of the cores
-/

section CoreDeriv

variable {W : ℕ}

/-- The derivative bound from an integrand bound and a mean-square bound at time `t`. -/
theorem cht_deriv_bound {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0) {σ : LayerShape}
    {C₀ C₁ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    {Lin : (ι → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hL : ∀ x, (Lin x).IsHermitian)
    {E t δ : ℝ} (hδ : 0 < δ) (hc : cplCoercive δ (C₀ + t • C₁)) {c₀ : ℂ}
    (hint : ∀ G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ‖(G * C₁).trace - (coreS v Lin G * G).trace / 2 - c₀‖ ≤ W * chtErr σ E G) {K : ℝ}
    (hK : ∫ x, chtErr σ E (Ring.inverse (chtPath C₀ C₁ Lin t x)) ∂gaussianProduct v ≤ K) :
    ‖chtDeriv v C₀ C₁ Lin t - c₀‖ ≤ W * K := by
  set μ := gaussianProduct v
  have hcP : ∀ x, cplCoercive δ (chtPath C₀ C₁ Lin t x) := cht_path_coercive hL hc
  have hP : Continuous (fun x => chtPath C₀ C₁ Lin t x) := by unfold chtPath; fun_prop
  have hGc := cht_continuous_inv hδ hP hcP
  set G : (ι → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => Ring.inverse (chtPath C₀ C₁ Lin t x) with hG
  have hiC := cht_integrable_trace_mul_const v hδ hP hcP C₁
  have hiS := cht_integrable_trace_S v (Lin := Lin) hδ hP hcP
  have hEn : ∀ G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖G‖ ≤ δ⁻¹ →
      chtErr σ E G ≤ (σ.blocks + σ.ports) * (δ⁻¹ + ‖matchedA E‖) ^ 2 := by
    intro G hG
    have h1 : ∀ k, ‖physBlockTrace G k - matchedA E‖ ^ 2 ≤ (δ⁻¹ + ‖matchedA E‖) ^ 2 := fun k =>
      pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
        (add_le_add ((meq_norm_physBlockTrace_le G k).trans hG) le_rfl)) 2
    have h2 : ∀ j, ‖portBlockTrace G j - matchedA E‖ ^ 2 ≤ (δ⁻¹ + ‖matchedA E‖) ^ 2 := fun j =>
      pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
        (add_le_add ((meq_norm_portBlockTrace_le G j).trans hG) le_rfl)) 2
    unfold chtErr
    calc _ ≤ ∑ _k : Fin σ.blocks, (δ⁻¹ + ‖matchedA E‖) ^ 2 +
          ∑ _j : Fin σ.ports, (δ⁻¹ + ‖matchedA E‖) ^ 2 :=
          add_le_add (Finset.sum_le_sum fun k _ => h1 k) (Finset.sum_le_sum fun j _ => h2 j)
      _ = _ := by simp; ring
  have hErrI : Integrable (fun x => chtErr σ E (G x)) μ :=
    Integrable.of_bound ((cht_continuous_err E).comp hGc).aestronglyMeasurable
      ((σ.blocks + σ.ports) * (δ⁻¹ + ‖matchedA E‖) ^ 2) (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (cht_err_nonneg E _)]
        exact hEn _ (cht_norm_inv_le hδ (hcP x)))
  have hD : chtDeriv v C₀ C₁ Lin t - c₀ =
      ∫ x, ((G x * C₁).trace - (coreS v Lin (G x) * G x).trace / 2 - c₀) ∂μ := by
    unfold chtDeriv
    have hi1 : Integrable (fun x => (G x * C₁).trace - (coreS v Lin (G x) * G x).trace / 2) μ :=
      hiC.sub (hiS.div_const 2)
    rw [integral_sub hi1 (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [hD]
  refine (norm_integral_le_integral_norm _).trans ?_
  have h1 : ∫ x, ‖(G x * C₁).trace - (coreS v Lin (G x) * G x).trace / 2 - c₀‖ ∂μ ≤
      ∫ x, (W : ℝ) * chtErr σ E (G x) ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) (hErrI.const_mul _)
      (ae_of_all _ fun x => hint (G x))
  refine h1.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _)

/-- **The one-block core integrand** (constant `(W/2) a² (1 + 2b)`). -/
theorem cht_core1_integrand (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (E : ℝ)
    (G : Matrix (LayerSite W .oneBlockTwoPorts) (LayerSite W .oneBlockTwoPorts) ℂ) :
    ‖(G * chtC1 .oneBlockTwoPorts 0 E b).trace -
        (coreS (tflVar W b .oneBlockTwoPorts) (meqLc W b .oneBlockTwoPorts) G * G).trace / 2 -
        (W : ℂ) * (matchedA E ^ 2 * ((1 + 2 * b : ℝ) : ℂ) / 2)‖ ≤
      W * chtErr .oneBlockTwoPorts E G := by
  have hC := cht_trace_C1 hW 0 E b G
  have hS := cht_trace_S hW G (b := b)
  rw [meq_coefA hW hb1, meq_coefB hW hb0] at hS
  have hS' : coreS (tflVar W b .oneBlockTwoPorts) (meqLc W b .oneBlockTwoPorts) G =
      meqS W b .oneBlockTwoPorts G := rfl
  rw [hS']
  simp only [Fin.sum_univ_two, Fin.sum_univ_one, meqInc, LayerShape.incident, ite_true,
    one_mul] at hC hS
  unfold chtErr
  simp only [Fin.sum_univ_two, Fin.sum_univ_one]
  set a := matchedA E
  set g := physBlockTrace G 0
  set u0 := portBlockTrace G 0
  set u1 := portBlockTrace G 1
  have key : (G * chtC1 .oneBlockTwoPorts 0 E b).trace -
      (meqS W b .oneBlockTwoPorts G * G).trace / 2 -
      (W : ℂ) * (a ^ 2 * ((1 + 2 * b : ℝ) : ℂ) / 2) =
      (W : ℂ) * (-((((1 - 2 * b) / 2 : ℝ) : ℂ) * (g - a) ^ 2) -
        (b : ℂ) * ((g - a) * (u0 - a) + (g - a) * (u1 - a))) := by
    rw [hC, hS]; push_cast; ring
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ (1 - 2 * b) / 2 := by linarith
  rw [key, norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ hW0
  have h1 : ‖(((1 - 2 * b) / 2 : ℝ) : ℂ) * (g - a) ^ 2‖ ≤ (1 - 2 * b) / 2 * ‖g - a‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, norm_pow]
  have h2 : ‖(b : ℂ) * ((g - a) * (u0 - a) + (g - a) * (u1 - a))‖ ≤
      b * ((‖g - a‖ ^ 2 + ‖u0 - a‖ ^ 2) / 2 + (‖g - a‖ ^ 2 + ‖u1 - a‖ ^ 2) / 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
      (add_le_add (cht_norm_mul_le_sq _ _) (cht_norm_mul_le_sq _ _))) hb0
  have h3 := norm_sub_le (-((((1 - 2 * b) / 2 : ℝ) : ℂ) * (g - a) ^ 2))
    ((b : ℂ) * ((g - a) * (u0 - a) + (g - a) * (u1 - a)))
  rw [norm_neg] at h3
  have hA := sq_nonneg ‖g - a‖
  have hB := sq_nonneg ‖u0 - a‖
  have hC' := sq_nonneg ‖u1 - a‖
  nlinarith [mul_nonneg hb0 hA, mul_nonneg hb0 hB, mul_nonneg hb0 hC']

/-- `Tr(S(G) G)` of the two-block core: the `.separate` layer part plus `2W b g₀ g₁`. -/
theorem cht_trace_coreS (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (G : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    (coreS (coreVar W b) (coreLin W b) G * G).trace =
      (meqS W b .separate G * G).trace +
        (W : ℂ) * (2 * (b : ℂ) * physBlockTrace G 0 * physBlockTrace G 1) := by
  rw [coreS_eq hW hb0 hb1, ← meq_coefA hW hb1, ← meq_coefB hW hb0, ← meqS_eq hW, Matrix.add_mul,
    trace_add]
  congr 1
  rw [Matrix.smul_mul, trace_smul, Matrix.add_mul, trace_add, Matrix.smul_mul, Matrix.smul_mul,
    trace_smul, trace_smul]
  have h0 : (meqPhysProj (W := W) (σ := .separate) 0 * G).trace = (W : ℂ) * physBlockTrace G 0 := by
    rw [lct_phys_eq_trace, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hW.ne'), one_mul]
  have h1 : (meqPhysProj (W := W) (σ := .separate) 1 * G).trace = (W : ℂ) * physBlockTrace G 1 := by
    rw [lct_phys_eq_trace, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hW.ne'), one_mul]
  rw [h0, h1, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The two-block core integrand** (constant `(W/2) a² (2 + 2b)`). -/
theorem cht_core2_integrand (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (E : ℝ)
    (G : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    ‖(G * chtC1 .separate 0 E b).trace - (coreS (coreVar W b) (coreLin W b) G * G).trace / 2 -
        (W : ℂ) * (matchedA E ^ 2 * ((2 + 2 * b : ℝ) : ℂ) / 2)‖ ≤
      W * chtErr .separate E G := by
  have hC := cht_trace_C1 hW 0 E b G
  have hS := cht_trace_S hW G (b := b)
  rw [meq_coefA hW hb1, meq_coefB hW hb0] at hS
  rw [cht_trace_coreS hW hb0 hb1]
  simp only [Fin.sum_univ_two, meqInc, LayerShape.incident, Fin.val_zero, Fin.val_one,
    Fin.isValue, decide_true, ite_true, one_mul, zero_ne_one, one_ne_zero, decide_false,
    Bool.false_eq_true, ite_false, zero_mul, add_zero, zero_add] at hC hS
  unfold chtErr
  simp only [Fin.sum_univ_two]
  set a := matchedA E
  set g0 := physBlockTrace G 0
  set g1 := physBlockTrace G 1
  set u0 := portBlockTrace G 0
  set u1 := portBlockTrace G 1
  have key : (G * chtC1 .separate 0 E b).trace -
      ((meqS W b .separate G * G).trace + (W : ℂ) * (2 * (b : ℂ) * g0 * g1)) / 2 -
      (W : ℂ) * (a ^ 2 * ((2 + 2 * b : ℝ) : ℂ) / 2) =
      (W : ℂ) * (-((((1 - 2 * b) / 2 : ℝ) : ℂ) * ((g0 - a) ^ 2 + (g1 - a) ^ 2)) -
        (b : ℂ) * ((g0 - a) * (u0 - a) + (g1 - a) * (u1 - a) + (g0 - a) * (g1 - a))) := by
    rw [hC, hS]; push_cast; ring
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ (1 - 2 * b) / 2 := by linarith
  rw [key, norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ hW0
  have h1 : ‖(((1 - 2 * b) / 2 : ℝ) : ℂ) * ((g0 - a) ^ 2 + (g1 - a) ^ 2)‖ ≤
      (1 - 2 * b) / 2 * (‖g0 - a‖ ^ 2 + ‖g1 - a‖ ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hc
    rw [norm_pow, norm_pow]
  have h2 : ‖(b : ℂ) * ((g0 - a) * (u0 - a) + (g1 - a) * (u1 - a) + (g0 - a) * (g1 - a))‖ ≤
      b * ((‖g0 - a‖ ^ 2 + ‖u0 - a‖ ^ 2) / 2 + (‖g1 - a‖ ^ 2 + ‖u1 - a‖ ^ 2) / 2 +
        (‖g0 - a‖ ^ 2 + ‖g1 - a‖ ^ 2) / 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (cht_norm_mul_le_sq _ _) (cht_norm_mul_le_sq _ _)))
      (cht_norm_mul_le_sq _ _))) hb0
  have h3 := norm_sub_le (-((((1 - 2 * b) / 2 : ℝ) : ℂ) * ((g0 - a) ^ 2 + (g1 - a) ^ 2)))
    ((b : ℂ) * ((g0 - a) * (u0 - a) + (g1 - a) * (u1 - a) + (g0 - a) * (g1 - a)))
  rw [norm_neg] at h3
  have hA := sq_nonneg ‖g0 - a‖
  have hB := sq_nonneg ‖g1 - a‖
  have hC' := sq_nonneg ‖u0 - a‖
  have hD := sq_nonneg ‖u1 - a‖
  nlinarith [mul_nonneg hb0 hA, mul_nonneg hb0 hB, mul_nonneg hb0 hC', mul_nonneg hb0 hD]

end CoreDeriv

/-!
## 7. The mean-square input of the cores and the core means
-/

section CoreMean

/-- **Isolated input: the core trace errors along the interpolation** (in the paper:
"The constant mean is `a` and the finite core stability was proved in the matched-traces theorem";
the heat derivative has "an `O(W⁻¹)` remainder"). For `b ∈ (0, 1/2)` and the bulk `I` there are
`C`, `W₀`; for `W ≥ W₀`, `E ∈ I` and `t ∈ (0, 1)`, the block traces of the inverse core heat
matrix (`chtCoreHeat1`: one block, two ports, law `layerLaw W b .oneBlockTwoPorts`;
`chtCoreHeat2`: two blocks with their internal bond, law `coreLaw2 W b`) satisfy
`E[Σ_β |g_β - a|²] ≤ C W⁻²`. -/
structure ChtCoreMeanSquare : Prop where
  one : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ∫ ω, chtErr .oneBlockTwoPorts E (chtCoreHeat1 b E t ω)⁻¹ ∂layerLaw W b .oneBlockTwoPorts ≤
        C / (W : ℝ) ^ 2
  two : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ∫ q, chtErr .separate E (chtCoreHeat2 b E t q)⁻¹ ∂coreLaw2 W b ≤ C / (W : ℝ) ^ 2

variable {W : ℕ}

theorem cht_measurable_coreLb : Measurable (fun β : Matrix (Fin W) (Fin W) ℂ => coreLb β) := by
  have hc : Continuous (fun A : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ =>
      (fromBlocks A 0 0 0 : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)) :=
    continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const
  exact hc.measurable.comp (measurable_coreOff W)

theorem cht_coreLin_isHermitian (b : ℝ) (x : CoreCoord W → ℝ) : (coreLin W b x).IsHermitian := by
  rw [coreLin_apply, coreLb]
  refine (IsHermitian.fromBlocks (coreOff_isHermitian _) (by simp) isHermitian_zero).add ?_
  exact cht_lin_isHermitian (W := W) .separate b (fun c => x (Sum.inr c))

/-- **Mean of the one-block core**: `|φ(1) - φ(0) - (W/2)(1+2b) Im a²| ≤ C/W` with
`φ(1) = π EΨ₁`, `φ(0) = 3πWℓ`. -/
theorem cht_core_one_mean (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hcms : ChtCoreMeanSquare) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      |Real.pi * (∫ ω, compensatedPhase b E ω ∂pathLaw W 1 b) -
          Real.pi * ((3 * W : ℕ) * phaseEll E) -
          ((W : ℂ) * (matchedA E ^ 2 * ((1 + 2 * b : ℝ) : ℂ) / 2)).im| ≤ W * (C / (W : ℝ) ^ 2) := by
  obtain ⟨C, W₀, hC⟩ := hcms.one b hb0 hb1 κ hκ
  have habs := gaussianAbsorption_holds hcount
  rcases (bulkInterval κ).eq_empty_or_nonempty with he | ⟨E₀, hE₀⟩
  · exact ⟨0, 0, fun W _ _ E hE => by rw [he] at hE; exact absurd hE (Set.notMem_empty E)⟩
  set η₀ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
  have hη : 0 < η₀ := (commonZ_im_pos_of_mem_bulkInterval hb1 hκ hE₀).1
  obtain ⟨ε₁, CA, hε₁, -, habs'⟩ := habs b hb0 hb1 η₀ 3 hη
  refine ⟨C, W₀, fun W hW hW₀ E hE => ?_⟩
  obtain ⟨hE2, hzη, hz3, -, -⟩ := cht_bulk_facts hb0 hb1 hκ hE
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη hzη
  set σ : LayerShape := .oneBlockTwoPorts
  set v := tflVar W b σ
  set μ := gaussianProduct v
  set C₀ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := chtKC0 σ E
  set C₁ := chtC1 (W := W) σ 0 E b
  set Lin := meqLc W b σ
  have hL : ∀ x, (Lin x).IsHermitian := cht_lin_isHermitian σ b
  have hcoer := cht_core_coercive (W := W) (σ := σ) hb0.le hb1 hE2
  have hlaw : layerLaw W b σ = μ.map (tflEmbed W b σ) := tfl_layerLaw_eq_map W b σ
  have hΦ := tfl_measurable_embed W b σ
  have h1M : ∀ x, chtPath C₀ C₁ Lin 1 x = layerMatrix σ E (boundaryZ b E) 0 (tflEmbed W b σ x) := by
    intro x
    rw [cht_path_one, cht_core_C0_add_C1 hE2.le, tfl_layerMatrix_embed, meqLc_apply]
  have hinv := (habs' W hW σ 0 isHermitian_zero E (boundaryZ b E) hzη hz3).1
  have hunitγ : ∀ᵐ x ∂μ, IsUnit (layerMatrix σ E (boundaryZ b E) 0 (tflEmbed W b σ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  have hunit : ∀ᵐ x ∂μ, IsUnit (C₀ + C₁ + Lin x) := by
    filter_upwards [hunitγ] with x hx
    rw [← cht_path_one, h1M, Matrix.isUnit_iff_isUnit_det]; exact hx
  -- the main step
  have hmain := cht_main_general v hL hcoer hunit
    (c₀ := (W : ℂ) * (matchedA E ^ 2 * ((1 + 2 * b : ℝ) : ℂ) / 2)) (K := W * (C / (W : ℝ) ^ 2))
    (fun t ht => by
      obtain ⟨δ, hδ, hc⟩ := hcoer t ⟨ht.1.le, ht.2⟩
      refine cht_deriv_bound v hL hδ hc (cht_core1_integrand hW hb0.le hb1.le E) ?_
      have hm : Measurable (fun ω : LayerSample W σ => chtErr σ E (chtCoreHeat1 b E t ω)⁻¹) := by
        refine (cht_continuous_err E).measurable.comp (measurable_matrix_inv.comp ?_)
        unfold chtCoreHeat1
        exact measurable_const.add ((continuous_const_smul (Real.sqrt t)).measurable.comp
          (cht_measurable_linS σ))
      have htr : ∫ x, chtErr σ E (Ring.inverse (chtPath C₀ C₁ Lin t x)) ∂μ =
          ∫ ω, chtErr σ E (chtCoreHeat1 b E t ω)⁻¹ ∂layerLaw W b σ := by
        rw [hlaw, integral_map hΦ.aemeasurable hm.aestronglyMeasurable]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [Matrix.nonsing_inv_eq_ringInverse]
        rfl
      rw [htr]
      exact hC W hW hW₀ E hE t ht)
  -- the endpoints
  have h0 : chtPhi v C₀ C₁ Lin 0 = Real.pi * ((3 * W : ℕ) * phaseEll E) := by
    have hc : ∀ x, chtPath C₀ C₁ Lin 0 x = C₀ := by intro x; simp [chtPath]
    unfold chtPhi
    simp only [hc, integral_const, probReal_univ, one_smul]
    rw [cht_logDet_KC0 hE2]
    rfl
  have hDγ : ∀ᵐ x ∂μ, IsUnit (cplTop E 0 (tflEmbed W b σ x)).det := by
    have h := srec_ae_isUnit_top (W := W) hb1 σ E 0
    rw [hlaw] at h
    exact ae_of_ae_map hΦ.aemeasurable h
  have hpt : ∀ᵐ x ∂μ, (cplLogDet (chtPath C₀ C₁ Lin 1 x)).im =
      Real.pi * cphPsiM b E (coreOne (tflEmbed W b σ x)) := by
    filter_upwards [hunitγ, hDγ] with x hx hDx
    rw [h1M]
    refine cht_logDet_eq_of_tendsto ?_ ((Matrix.isUnit_iff_isUnit_det _).mpr hx) ?_
    · rw [← tflPsi_eq]
      exact cpl_tflPsi_coercive W b σ E (boundaryZ b E) isHermitian_zero hz.le one_pos x
    · have h := cplF_tendsto W b σ E (boundaryZ b E) isHermitian_zero hz x hDx
      rw [← cht_coreOne_psi _ fun j => gueOfCoords_isHermitian _ _ _] at h
      refine h.congr fun j => ?_
      simp only [cplF, tflPsi_eq]
  have h1 : chtPhi v C₀ C₁ Lin 1 = Real.pi * ∫ ω, compensatedPhase b E ω ∂pathLaw W 1 b := by
    have hmp := coreOne_measurePreserving W b
    unfold chtPhi
    rw [integral_congr_ae hpt, integral_const_mul,
      integral_congr_ae (cph_psi_ae_eq b E W 1), ← hmp.map_eq,
      integral_map hmp.measurable.aemeasurable (cph_measurable_psiM b E W 1).aestronglyMeasurable,
      hlaw]
    rw [integral_map (f := fun ω => cphPsiM b E (coreOne ω)) hΦ.aemeasurable
        ((cph_measurable_psiM b E W 1).comp hmp.measurable).aestronglyMeasurable]
  rw [h0, h1] at hmain
  exact hmain

/-- **Mean of the two-block core**: `|φ(1) - φ(0) - (W/2)(2+2b) Im a²| ≤ C/W` with
`φ(1) = π EΨ₂`, `φ(0) = 4πWℓ`. -/
theorem cht_core_two_mean (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hcms : ChtCoreMeanSquare) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      |Real.pi * (∫ ω, compensatedPhase b E ω ∂pathLaw W 2 b) -
          Real.pi * ((4 * W : ℕ) * phaseEll E) -
          ((W : ℂ) * (matchedA E ^ 2 * ((2 + 2 * b : ℝ) : ℂ) / 2)).im| ≤ W * (C / (W : ℝ) ^ 2) := by
  obtain ⟨C, W₀, hC⟩ := hcms.two b hb0 hb1 κ hκ
  have habs := gaussianAbsorption_holds hcount
  rcases (bulkInterval κ).eq_empty_or_nonempty with he | ⟨E₀, hE₀⟩
  · exact ⟨0, 0, fun W _ _ E hE => by rw [he] at hE; exact absurd hE (Set.notMem_empty E)⟩
  set η₀ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
  have hη : 0 < η₀ := (commonZ_im_pos_of_mem_bulkInterval hb1 hκ hE₀).1
  obtain ⟨ε₁, CA, hε₁, -, habs'⟩ := habs b hb0 hb1 η₀ 3 hη
  refine ⟨C, W₀, fun W hW hW₀ E hE => ?_⟩
  obtain ⟨hE2, hzη, hz3, -, -⟩ := cht_bulk_facts hb0 hb1 hκ hE
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη hzη
  set v := coreVar W b
  set μ := gaussianProduct v
  set C₀ : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ := chtKC0 .separate E
  set C₁ := chtC1 (W := W) .separate 0 E b
  set Lin := coreLin W b
  have hL : ∀ x, (Lin x).IsHermitian := cht_coreLin_isHermitian b
  have hcoer := cht_core_coercive (W := W) (σ := .separate) hb0.le hb1 hE2
  have hlaw : coreLaw2 W b = μ.map (coreEmbed W b) := by rw [coreLaw2, core_law_eq_map]
  have hΦ := core_measurable_embed W b
  have h1M : ∀ x, chtPath C₀ C₁ Lin 1 x = coreC0 W E (boundaryZ b E) + coreLin W b x := by
    intro x
    rw [cht_path_one, cht_core_C0_add_C1 hE2.le]
    rfl
  have hinv := core_ae_unit2 (b := b) (E := E) (z := boundaryZ b E)
    (fun X hX => (habs' W hW .separate X hX E (boundaryZ b E) hzη hz3).1)
  have hunitγ := core_ae_coords hinv
  have hunit : ∀ᵐ x ∂μ, IsUnit (C₀ + C₁ + Lin x) := by
    filter_upwards [hunitγ] with x hx
    rw [← cht_path_one, h1M, Matrix.isUnit_iff_isUnit_det]; exact hx
  have hmain := cht_main_general v hL hcoer hunit
    (c₀ := (W : ℂ) * (matchedA E ^ 2 * ((2 + 2 * b : ℝ) : ℂ) / 2)) (K := W * (C / (W : ℝ) ^ 2))
    (fun t ht => by
      obtain ⟨δ, hδ, hc⟩ := hcoer t ⟨ht.1.le, ht.2⟩
      refine cht_deriv_bound v hL hδ hc (cht_core2_integrand hW hb0.le hb1.le E) ?_
      have hm : Measurable (fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate =>
          chtErr .separate E (chtCoreHeat2 b E t q)⁻¹) := by
        refine (cht_continuous_err E).measurable.comp (measurable_matrix_inv.comp ?_)
        unfold chtCoreHeat2
        exact measurable_const.add ((continuous_const_smul (Real.sqrt t)).measurable.comp
          (((cht_measurable_linS .separate).comp measurable_snd).add
            (cht_measurable_coreLb.comp measurable_fst)))
      have htr : ∫ x, chtErr .separate E (Ring.inverse (chtPath C₀ C₁ Lin t x)) ∂μ =
          ∫ q, chtErr .separate E (chtCoreHeat2 b E t q)⁻¹ ∂coreLaw2 W b := by
        rw [hlaw, integral_map hΦ.aemeasurable hm.aestronglyMeasurable]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [Matrix.nonsing_inv_eq_ringInverse]
        congr 2
        rw [chtCoreHeat2, chtPath, coreLin_apply, add_comm (coreLb _)]
        rfl
      rw [htr]
      exact hC W hW hW₀ E hE t ht)
  have h0 : chtPhi v C₀ C₁ Lin 0 = Real.pi * ((4 * W : ℕ) * phaseEll E) := by
    have hc : ∀ x, chtPath C₀ C₁ Lin 0 x = C₀ := by intro x; simp [chtPath]
    unfold chtPhi
    simp only [hc, integral_const, probReal_univ, one_smul]
    rw [cht_logDet_KC0 hE2]
    rfl
  have hDγ : ∀ᵐ x ∂μ, IsUnit (cplTop E (-coreOff (coreEmbed W b x).1) (coreEmbed W b x).2).det := by
    have h := cht_ae_top2 (W := W) hb1 E
    rw [hlaw] at h
    exact ae_of_ae_map hΦ.aemeasurable h
  have hpt : ∀ᵐ x ∂μ, (cplLogDet (chtPath C₀ C₁ Lin 1 x)).im =
      Real.pi * cphPsiM b E (coreTwo (coreEmbed W b x)) := by
    filter_upwards [hunitγ, hDγ] with x hx hDx
    have hreg : ∀ κ' : ℝ, tflReg κ' (coreC0 W E (boundaryZ b E) + coreLin W b x) =
        corePsi (coreC0 W E (boundaryZ b E)) (coreLin W b) κ' x := by
      intro κ'; rw [tflReg, corePsi]; abel
    rw [h1M]
    refine cht_logDet_eq_of_tendsto ?_ ((Matrix.isUnit_iff_isUnit_det _).mpr hx) ?_
    · rw [hreg]
      exact cht_corePsi_coercive W b E hz.le one_pos x
    · have h := chtCoreF_tendsto W b E hz x hDx
      rw [← cht_coreTwo_psi _ fun j => gueOfCoords_isHermitian _ _ _] at h
      refine h.congr fun j => ?_
      simp only [chtCoreF, hreg]
  have h1 : chtPhi v C₀ C₁ Lin 1 = Real.pi * ∫ ω, compensatedPhase b E ω ∂pathLaw W 2 b := by
    have hmp : MeasurePreserving (coreTwo (W := W)) (coreLaw2 W b) (pathLaw W 2 b) :=
      coreTwo_measurePreserving W b
    unfold chtPhi
    rw [integral_congr_ae hpt, integral_const_mul,
      integral_congr_ae (cph_psi_ae_eq b E W 2), ← hmp.map_eq,
      integral_map hmp.measurable.aemeasurable (cph_measurable_psiM b E W 2).aestronglyMeasurable,
      hlaw]
    rw [integral_map (f := fun q => cphPsiM b E (coreTwo q)) hΦ.aemeasurable
        ((cph_measurable_psiM b E W 2).comp hmp.measurable).aestronglyMeasurable]
  rw [h0, h1] at hmain
  exact hmain

/-- Conversion of a core heat bound into the `CphCore.mean` form (`F_sc = ℓ + h/2`). -/
theorem cht_core_mean_conv {W : ℕ} (hW : 0 < W) {r : ℝ} {N : ℕ} (hN : (N : ℝ) = (r + 2) * W)
    {s b I : ℝ} (hs : s = r + 2 * b) (E : ℝ) {C K : ℝ} (hK : max C 0 / Real.pi ≤ K)
    (h : |Real.pi * I - Real.pi * ((N : ℕ) * phaseEll E) -
      ((W : ℂ) * (matchedA E ^ 2 * ((s : ℝ) : ℂ) / 2)).im| ≤ W * (C / (W : ℝ) ^ 2)) :
    |I - r * W * semicircleCDF E - W * (2 * phaseEll E + b * phaseH E)| ≤ K / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hpi := Real.pi_pos
  have him : ((W : ℂ) * (matchedA E ^ 2 * ((s : ℝ) : ℂ) / 2)).im =
      W * s / 2 * (matchedA E ^ 2).im := by
    simp [Complex.mul_im, Complex.div_ofNat_im]; ring
  have heq : I - r * W * semicircleCDF E - W * (2 * phaseEll E + b * phaseH E) =
      (Real.pi * I - Real.pi * ((N : ℕ) * phaseEll E) -
        ((W : ℂ) * (matchedA E ^ 2 * ((s : ℝ) : ℂ) / 2)).im) / Real.pi := by
    rw [him, hN, hs, BlockBand.RankLocation.semicircleCDF_eq_phase_of_real E]
    unfold phaseH
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
  have e : (W : ℝ) * (C / (W : ℝ) ^ 2) = C / W := by field_simp
  rw [e] at h
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  calc _ ≤ C / W := h
    _ ≤ max C 0 / W := div_le_div_of_nonneg_right (le_max_left _ _) hWr.le
    _ = max C 0 / Real.pi / W * Real.pi := by field_simp
    _ ≤ K / W * Real.pi := by gcongr

theorem cht_core_small {W W₀ : ℕ} (hW : 0 < W) (hW₀ : W < W₀) {r : ℕ} (hr : r = 1 ∨ r = 2)
    {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE : |E| ≤ 2) {K : ℝ} (hK : 9 * (W₀ : ℝ) ^ 2 ≤ K) :
    |(∫ ω, compensatedPhase b E ω ∂pathLaw W r b) - r * W * semicircleCDF E -
        W * (2 * phaseEll E + b * phaseH E)| ≤ K / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hlt : (W : ℝ) < W₀ := by exact_mod_cast hW₀
  have hz : 0 ≤ (boundaryZ b E).im := by
    rw [boundaryZ_im hE]
    have := rl_matchedA_im_nonpos E
    nlinarith
  have hI : |∫ ω, compensatedPhase b E ω ∂pathLaw W r b| ≤ (r + 2) * W := by
    rw [integral_congr_ae (cph_psi_ae_eq b E W r)]
    exact cph_abs_integral_le fun ω => cph_abs_psiM_le hz ω
  have hr2 : (r : ℝ) ≤ 2 := by rcases hr with rfl | rfl <;> norm_num
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hF := cph_abs_semicircleCDF_le E
  have hl := cph_abs_phaseEll_le E
  have hh := cph_abs_phaseH_le hE
  have h3 : |(W : ℝ) * (2 * phaseEll E + b * phaseH E)| ≤ 3 * W := by
    rw [abs_mul, abs_of_pos hWr]
    have := abs_add_le (2 * phaseEll E) (b * phaseH E)
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hb0] at this
    have hq : |2 * phaseEll E + b * phaseH E| ≤ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hh hb0.le]
    calc (W : ℝ) * |2 * phaseEll E + b * phaseH E| ≤ W * 3 :=
          mul_le_mul_of_nonneg_left hq hWr.le
      _ = 3 * W := by ring
  have h4 : |(r : ℝ) * W * semicircleCDF E| ≤ 2 * W := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r * W)]
    have := mul_le_mul_of_nonneg_left hF (by positivity : (0 : ℝ) ≤ r * W)
    nlinarith
  have hcrude : |(∫ ω, compensatedPhase b E ω ∂pathLaw W r b) - r * W * semicircleCDF E -
      W * (2 * phaseEll E + b * phaseH E)| ≤ 9 * W := by
    have := abs_sub (∫ ω, compensatedPhase b E ω ∂pathLaw W r b - r * W * semicircleCDF E)
      (W * (2 * phaseEll E + b * phaseH E))
    have := abs_sub (∫ ω, compensatedPhase b E ω ∂pathLaw W r b) (r * W * semicircleCDF E)
    nlinarith
  refine hcrude.trans ?_
  rw [le_div_iff₀ hWr]
  nlinarith

/-- **`CphCore`** (the starting constant and the core fluctuation) from
`ConditionalBlockGUECount`, `GaussianLpGradient` and the core mean-square hypothesis
`ChtCoreMeanSquare`. Uses neither `CompensatedPhaseContract` nor anything derived from it. -/
theorem cphCore_of_meanSquare (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) (hcms : ChtCoreMeanSquare) : CphCore where
  fluctuation := by
    intro b hb0 hb1 κ hκ p hp
    obtain ⟨C1, h1⟩ := cht_core_one_fluct hcount hgrad hb0 hb1 hκ hp
    obtain ⟨C2, h2⟩ := cht_core_two_fluct hcount hgrad hb0 hb1 hκ hp
    refine ⟨max C1 C2, fun W hW r₀ hr₀ E hE => ?_⟩
    rcases hr₀ with rfl | rfl
    · exact (h1 W hW E hE).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · exact (h2 W hW E hE).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  mean := by
    intro b hb0 hb1 κ hκ
    obtain ⟨C1, W1, h1⟩ := cht_core_one_mean hcount hcms hb0 hb1 hκ
    obtain ⟨C2, W2, h2⟩ := cht_core_two_mean hcount hcms hb0 hb1 hκ
    set W₀ := max W1 W2
    set K := max (max (max C1 0) (max C2 0) / Real.pi) (9 * (W₀ : ℝ) ^ 2)
    refine ⟨K, fun W hW r₀ hr₀ E hE => ?_⟩
    have hE2 := (abs_lt_two_of_mem_bulkInterval hκ hE).le
    by_cases hW₀ : W₀ ≤ W
    · have hK1 : max C1 0 / Real.pi ≤ K := le_trans (div_le_div_of_nonneg_right
        (le_max_left _ _) Real.pi_pos.le) (le_max_left _ _)
      have hK2 : max C2 0 / Real.pi ≤ K := le_trans (div_le_div_of_nonneg_right
        (le_max_right _ _) Real.pi_pos.le) (le_max_left _ _)
      rcases hr₀ with rfl | rfl
      · have h := h1 W hW (le_trans (le_max_left _ _) hW₀) E hE
        have := cht_core_mean_conv hW (r := 1) (N := 3 * W) (by push_cast; ring) (b := b)
          (s := 1 + 2 * b) (by ring) E hK1 h
        simpa using this
      · have h := h2 W hW (le_trans (le_max_right _ _) hW₀) E hE
        have := cht_core_mean_conv hW (r := 2) (N := 4 * W) (by push_cast; ring) (b := b)
          (s := 2 + 2 * b) (by ring) E hK2 h
        simpa using this
    · exact cht_core_small hW (lt_of_not_ge hW₀) hr₀ hb0 hb1 hE2 (le_max_right _ _)

end CoreMean

/-!
## 8. Assembly of the compensated contracts
-/

section Assembly

/-- `CompensatedIncrementContract` from `ConditionalBlockGUECount` and the mean-square hypothesis
`ChtMeanSquare`: `compensatedIncrement_of_local ∘ cphIncrementLocal_of_meanSquare`. -/
theorem compensatedIncrement_holds_of_meanSquare
    (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount) (_hgrad : GaussianLpGradient)
    (hms : ChtMeanSquare) : CompensatedIncrementContract :=
  compensatedIncrement_of_local (cphIncrementLocal_of_meanSquare hcount hms)

/-- **The compensated-phase lemma** (`CompensatedPhaseContract`) from `ConditionalBlockGUECount`,
`GaussianLpGradient` and the two mean-square hypotheses `ChtMeanSquare` (fresh layers) and
`ChtCoreMeanSquare` (cores), through `compensatedPhase_holds_of` with
`cphIncrementFluctuation_holds`. -/
theorem compensatedPhase_holds_of_meanSquare
    (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hms : ChtMeanSquare) (hcms : ChtCoreMeanSquare) : CompensatedPhaseContract :=
  compensatedPhase_holds_of hcount hgrad (compensatedIncrement_holds_of_meanSquare hcount hgrad hms)
    (cphIncrementFluctuation_holds hcount hgrad) (cphCore_of_meanSquare hcount hgrad hcms)

/-- **The ring display** (`RingCompensatedPhaseContract`) from the same inputs,
through `ringCompensatedPhase_holds_of`. -/
theorem ringCompensatedPhase_holds_of_meanSquare
    (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hms : ChtMeanSquare) (hcms : ChtCoreMeanSquare) : RingCompensatedPhaseContract :=
  ringCompensatedPhase_holds_of hcount hgrad
    (compensatedIncrement_holds_of_meanSquare hcount hgrad hms)
    (cphIncrementFluctuation_holds hcount hgrad) (cphCore_of_meanSquare hcount hgrad hcms)

end Assembly

end BlockBand.Layers
