module

public import BlockBand.SourceProcess.PhysApprox.B3MartMax
public import BlockBand.SourceProcess.RawTag.JointLaw
public import BlockBand.SourceProcess.RawTag.DeltaBounds
public import BlockBand.SourceProcess.RawTag.StepBound
public import BlockBand.SourceProcess.FullSource.DeltaMoments
public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# The one-step mean over the fresh layer under the closed law

Under `closedLaw b W np` with the filtration `b3Sigma W i np` (past at `i`, probes, phase), the
fresh layer `F_i = freshSample W i` of the step `i → i + 1` is independent of the conditioning
coordinates. Proved here:

* `closedLaw_map_past_fresh`: `((pastCoords W i, probes, θ), F_i)` has law
  `(pastLaw ⊗ probes ⊗ phase) ⊗ freshLaw` (reassociation and `RawTag.map_past_tag_fresh`);
* `condExp_closed_fresh`: `E[Ψ(past, F_i) | b3Sigma i] = ∫ Ψ(past, F) dfreshLaw(F)` a.e. (the
  closed-law form of `ContractingWords.condExp_past_fresh`);
* `condExp_closed_bilinear_fresh`: for `b3Ext W i`-invariant Borel `u, v, X`,
  `E[u*Δ(X, F_i)v | b3Sigma i] = u*(E_FΔ(X))v` a.e.;
* `ae_norm_condExp_bilinear_fresh_le`: with `RawTag.delta_fresh_bounds`, for passive `X` and
  frames bounded by `Cf`, `‖E[u*Δv | b3Sigma i]‖ ≤ Cm Cf² (δ₀(X) + W⁻¹)` a.e.

These serve the closed `𝒦` mean and, unchanged, the unclosed means (frames `nearL`, `nearR` and
input `pathX`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W np : ℕ}

/-!
## The joint law of the conditioning coordinates and the fresh layer
-/

/-- The law of the probes and the phase. -/
def probePhaseLaw (W np : ℕ) : Measure ((Fin np → Fin W → ℂ) × ℝ) :=
  (Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)).prod phaseLaw

instance isProbabilityMeasure_probePhaseLaw (W np : ℕ) :
    IsProbabilityMeasure (probePhaseLaw W np) := by
  unfold probePhaseLaw; infer_instance

/-- The coordinates generating `b3Sigma W i`: past at `i`, probes, phase. -/
def b3Past (W i : ℕ) (y : ProbedPath W np × ℝ) :
    PastSample W i × ((Fin np → Fin W → ℂ) × ℝ) :=
  (pastCoords W i y.1.1, (y.1.2, y.2))

theorem measurable_b3Past (W i : ℕ) : Measurable (b3Past (np := np) W i) :=
  measurable_b3Sigma_map W i np

theorem b3Sigma_eq_comap (W i np : ℕ) :
    b3Sigma W i np = MeasurableSpace.comap (b3Past (np := np) W i) inferInstance := rfl

/-- The sample rebuilt from the conditioning coordinates (`b3Ext W i = b3Rebuild ∘ b3Past`). -/
def b3Rebuild (W i : ℕ) (x : PastSample W i × ((Fin np → Fin W → ℂ) × ℝ)) :
    ProbedPath W np × ℝ :=
  ((extPast W i x.1, x.2.1), x.2.2)

theorem measurable_b3Rebuild (W i : ℕ) : Measurable (b3Rebuild (np := np) W i) :=
  (((measurable_extPast i).comp measurable_fst).prodMk
    (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)

theorem b3Rebuild_b3Past (W i : ℕ) (y : ProbedPath W np × ℝ) :
    b3Rebuild W i (b3Past W i y) = b3Ext W i y := rfl

/-- **Joint law**: under `closedLaw`, `((pastCoords W i, probes, θ), freshSample W i)` has law
`(pastLaw ⊗ probes ⊗ phase) ⊗ freshLaw`. -/
theorem closedLaw_map_past_fresh (b : ℝ) (W np i : ℕ) :
    (closedLaw b W np).map (fun y => (b3Past W i y, freshSample W i y.1.1)) =
      ((pastLaw W i b).prod (probePhaseLaw W np)).prod (freshLaw W b) := by
  have := isProbabilityMeasure_growthPathLaw W b
  have hA := measurePreserving_prodAssoc (growthPathLaw W b)
    (Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)) phaseLaw
  have hf : Measurable fun w : GrowthPath W × ((Fin np → Fin W → ℂ) × ℝ) =>
      ((pastCoords W i w.1, w.2), freshSample W i w.1) :=
    (((measurable_pastCoords W i).comp measurable_fst).prodMk measurable_snd).prodMk
      ((measurable_freshSample W i).comp measurable_fst)
  have e : (closedLaw b W np) = ((growthPathLaw W b).prod
      (Measure.pi fun _ : Fin np => circularVectorLaw (Fin W))).prod phaseLaw := rfl
  rw [e, show (fun y : ProbedPath W np × ℝ => (b3Past W i y, freshSample W i y.1.1)) =
      (fun w : GrowthPath W × ((Fin np → Fin W → ℂ) × ℝ) =>
        ((pastCoords W i w.1, w.2), freshSample W i w.1)) ∘ MeasurableEquiv.prodAssoc from rfl,
    ← Measure.map_map hf hA.measurable, hA.map_eq]
  exact RawTag.map_past_tag_fresh W i b (probePhaseLaw W np)

/-- The marginal of the conditioning coordinates. -/
theorem closedLaw_map_b3Past (b : ℝ) (W np i : ℕ) :
    (closedLaw b W np).map (b3Past W i) = (pastLaw W i b).prod (probePhaseLaw W np) := by
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W i y, freshSample W i y.1.1) :=
    (measurable_b3Past W i).prodMk
      ((measurable_freshSample W i).comp (measurable_fst.comp measurable_fst))
  have h := congrArg (fun m => m.map Prod.fst) (closedLaw_map_past_fresh b W np i)
  rw [Measure.map_map measurable_fst hT, Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

/-!
## Conditioning on `b3Sigma` is integration over the fresh layer
-/

/-- **Conditional expectation over the fresh layer under the closed law.** -/
theorem condExp_closed_fresh (b : ℝ) (i : ℕ)
    {Ψ : (PastSample W i × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ}
    (hΨ : Measurable Ψ)
    (hint : Integrable (fun y => Ψ (b3Past W i y, freshSample W i y.1.1)) (closedLaw b W np)) :
    (closedLaw b W np)[fun y => Ψ (b3Past W i y, freshSample W i y.1.1) | b3Sigma W i np] =ᵐ[
      closedLaw b W np] fun y => ∫ F, Ψ (b3Past W i y, F) ∂freshLaw W b := by
  set μ := closedLaw b W np
  set ν := (pastLaw W i b).prod (probePhaseLaw W np)
  set ρ := ν.prod (freshLaw W b)
  have hπ := measurable_b3Past (np := np) W i
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W i y, freshSample W i y.1.1) :=
    hπ.prodMk ((measurable_freshSample W i).comp (measurable_fst.comp measurable_fst))
  have hmap : μ.map (fun y => (b3Past W i y, freshSample W i y.1.1)) = ρ :=
    closedLaw_map_past_fresh b W np i
  have hmapπ : μ.map (b3Past W i) = ν := closedLaw_map_b3Past b W np i
  have hΨi : Integrable Ψ ρ := by
    rw [← hmap]; exact (integrable_map_measure hΨ.aestronglyMeasurable hT.aemeasurable).mpr hint
  set G : PastSample W i × ((Fin np → Fin W → ℂ) × ℝ) → ℂ := fun x => ∫ F, Ψ (x, F) ∂freshLaw W b
  have hG : Measurable G :=
    (hΨ.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  have hGi : Integrable G ν := hΨi.integral_prod_left
  have hGμ : Integrable (fun y => G (b3Past W i y)) μ :=
    (integrable_map_measure hG.aestronglyMeasurable hπ.aemeasurable).mp (by rw [hmapπ]; exact hGi)
  have hgm : Measurable[b3Sigma W i np] fun y => G (b3Past W i y) := by
    rw [b3Sigma_eq_comap]; exact hG.comp (comap_measurable (b3Past W i))
  refine (ae_eq_condExp_of_forall_setIntegral_eq (b3Sigma_le i) hint
    (fun s _ _ => hGμ.integrableOn) (fun s hs _ => ?_) hgm.aestronglyMeasurable).symm
  change MeasurableSet[MeasurableSpace.comap (b3Past (np := np) W i) inferInstance] s at hs
  obtain ⟨B, hB, rfl⟩ := hs
  have hind : ∀ f : ProbedPath W np × ℝ → ℂ, ∫ y in b3Past W i ⁻¹' B, f y ∂μ =
      ∫ y, (b3Past W i ⁻¹' B).indicator f y ∂μ := fun f => (integral_indicator (hπ hB)).symm
  rw [hind, hind]
  set Φ : (PastSample W i × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => B.indicator (fun _ => (1 : ℂ)) z.1 * Ψ z
  have hΦ : Measurable Φ := ((measurable_const.indicator hB).comp measurable_fst).mul hΨ
  have hΦi : Integrable Φ ρ := by
    refine hΨi.norm.mono' hΦ.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    by_cases hz : z.1 ∈ B <;> simp [Φ, hz]
  have e1 : ∫ y, (b3Past W i ⁻¹' B).indicator
      (fun y => Ψ (b3Past W i y, freshSample W i y.1.1)) y ∂μ = ∫ z, Φ z ∂ρ := by
    rw [← hmap, integral_map hT.aemeasurable hΦ.aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : b3Past W i y ∈ B
    · simp [Φ, hy]
    · simp [Φ, hy]
  have e2 : ∫ y, (b3Past W i ⁻¹' B).indicator (fun y => G (b3Past W i y)) y ∂μ =
      ∫ x, B.indicator G x ∂ν := by
    rw [← hmapπ, integral_map hπ.aemeasurable (hG.indicator hB).aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : b3Past W i y ∈ B
    · simp [hy]
    · simp [hy]
  rw [e1, e2, integral_prod Φ hΦi]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ B <;> simp [Φ, G, hx]

/-!
## Bilinear forms in `Δ`
-/

/-- The fresh mean of a bilinear form in `Δ`. -/
theorem integral_bilinear_freshDelta (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (u v : Fin W → ℂ)
    (hX : ∀ x x', Integrable (fun F => freshDelta b E X F x x') (freshLaw W b)) :
    ∫ F, bilinear u (freshDelta b E X F) v ∂freshLaw W b =
      bilinear u (matrixExpect (freshLaw W b) (freshDelta b E X)) v := by
  simp only [bilinear, dotProduct, mulVec, Pi.star_apply, matrixExpect, Matrix.of_apply]
  rw [integral_finsetSum _ fun x _ => ?_]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun y _ => (hX x y).mul_const _]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_mul_const]
  · exact (integrable_finsetSum _ fun y _ => (hX x y).mul_const _).const_mul _

/-- **The conditional mean of `u*Δ(X)v`** for `b3Ext W i`-invariant Borel `u, v, X`. -/
theorem condExp_closed_bilinear_fresh (b E : ℝ) (i : ℕ)
    {u v : ProbedPath W np × ℝ → Fin W → ℂ} {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ}
    (hu : Measurable u) (hv : Measurable v) (hX : Measurable X)
    (hu' : ∀ y, u (b3Ext W i y) = u y) (hv' : ∀ y, v (b3Ext W i y) = v y)
    (hX' : ∀ y, X (b3Ext W i y) = X y)
    (hΔ : ∀ᵐ y ∂closedLaw b W np,
      ∀ x x', Integrable (fun F => freshDelta b E (X y) F x x') (freshLaw W b))
    (hint : Integrable (fun y => bilinear (u y) (freshDelta b E (X y) (freshSample W i y.1.1))
      (v y)) (closedLaw b W np)) :
    (closedLaw b W np)[fun y => bilinear (u y) (freshDelta b E (X y) (freshSample W i y.1.1))
        (v y) | b3Sigma W i np] =ᵐ[closedLaw b W np]
      fun y => bilinear (u y) (matrixExpect (freshLaw W b) (freshDelta b E (X y))) (v y) := by
  set Ψ : (PastSample W i × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => bilinear (u (b3Rebuild W i z.1)) (freshDelta b E (X (b3Rebuild W i z.1)) z.2)
      (v (b3Rebuild W i z.1))
  have hR : Measurable fun z : (PastSample W i × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => b3Rebuild W i z.1 :=
    (measurable_b3Rebuild (np := np) W i).comp measurable_fst
  have hΨ : Measurable Ψ :=
    RawTag.measurable_bilinear_jt (hu.comp hR)
      (FullSource.measurable_freshDelta_comp b E (hX.comp hR) measurable_snd) (hv.comp hR)
  have hcomp : (fun y => Ψ (b3Past W i y, freshSample W i y.1.1)) =
      fun y => bilinear (u y) (freshDelta b E (X y) (freshSample W i y.1.1)) (v y) := by
    funext y
    simp only [Ψ, b3Rebuild_b3Past, hu', hv', hX']
  have h := condExp_closed_fresh b i hΨ (by rw [hcomp]; exact hint)
  rw [hcomp] at h
  filter_upwards [h, hΔ] with y hy hyΔ
  rw [hy]
  simp only [Ψ, b3Rebuild_b3Past, hu', hv', hX']
  exact integral_bilinear_freshDelta b E (X y) (u y) (v y) hyΔ

/-!
## The mean bound from `delta_fresh_bounds`
-/

theorem norm_bilinear_le_of_vecNorm {u v : Fin W → ℂ} {M : Matrix (Fin W) (Fin W) ℂ} {Cf : ℝ}
    (hu : vecNorm u ≤ Cf) (hv : vecNorm v ≤ Cf) : ‖bilinear u M v‖ ≤ Cf ^ 2 * ‖M‖ := by
  refine (Transmission.PassiveCovariance.norm_bilinear_le u M v).trans ?_
  have h0 := Transmission.PassiveCovariance.vecNorm_nonneg u
  have h1 := Transmission.PassiveCovariance.vecNorm_nonneg v
  have hC : 0 ≤ Cf := h0.trans hu
  calc vecNorm u * ‖M‖ * vecNorm v ≤ Cf * ‖M‖ * Cf :=
        mul_le_mul (mul_le_mul_of_nonneg_right hu (norm_nonneg _)) hv h1
          (mul_nonneg hC (norm_nonneg _))
    _ = Cf ^ 2 * ‖M‖ := by ring

/-- **The one-step mean bound** (through `delta_fresh_bounds`):
eventually in `W`, for every step `i`, every passive `b3Ext W i`-invariant input `X` and
frames bounded by `Cf`, `‖E[u*Δ(X)v | b3Sigma i]‖ ≤ Cm Cf² (δ₀(X) + W⁻¹)` a.e. -/
theorem ae_norm_condExp_bilinear_fresh_le (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) :
    ∃ (Cm : ℝ) (W₀ : ℕ), 0 ≤ Cm ∧ ∀ (W np : ℕ), W₀ ≤ W → ∀ (i : ℕ)
      {u v : ProbedPath W np × ℝ → Fin W → ℂ}
      {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ} (Cf : ℝ),
      Measurable u → Measurable v → Measurable X →
      (∀ y, u (b3Ext W i y) = u y) → (∀ y, v (b3Ext W i y) = v y) →
      (∀ y, X (b3Ext W i y) = X y) → (∀ y, vecNorm (u y) ≤ Cf) → (∀ y, vecNorm (v y) ≤ Cf) →
      (∀ᵐ y ∂closedLaw b W np, (passiveY (X y)).PosSemidef) →
      ∀ᵐ y ∂closedLaw b W np,
        ‖(closedLaw b W np)[fun y => bilinear (u y) (freshDelta b E (X y)
            (freshSample W i y.1.1)) (v y) | b3Sigma W i np] y‖ ≤
          Cm * Cf ^ 2 * (jetDistance0 b E (X y) + (W : ℝ)⁻¹) := by
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  obtain ⟨Cm, Cfl, W₁, hCm, -, hD⟩ := RawTag.delta_fresh_bounds hGA hLp b hb0 hb κ hκ 1 le_rfl
  obtain ⟨Cd, W₂, hCd, hmom⟩ := FullSource.delta_moments hGA b hb0 hb κ hκ 1 le_rfl
  refine ⟨Cm, max W₁ W₂, hCm, fun W np hW i u v X Cf hu hv hX hu' hv' hX' hub hvb hXp => ?_⟩
  have hW1 : W₁ ≤ W := le_of_max_le_left hW
  have hW2 : W₂ ≤ W := le_of_max_le_right hW
  set Fi : ProbedPath W np × ℝ → LayerSample W .oneBlockOnePort := fun y => freshSample W i y.1.1
  have hFi : Measurable Fi :=
    (measurable_freshSample W i).comp (measurable_fst.comp measurable_fst)
  have hΔm : Measurable fun y => freshDelta b E (X y) (Fi y) :=
    FullSource.measurable_freshDelta_comp b E hX hFi
  have hfm : Measurable fun y => bilinear (u y) (freshDelta b E (X y) (Fi y)) (v y) :=
    RawTag.measurable_bilinear_jt hu hΔm hv
  -- `∫ ‖Δ(X, F_i)‖ ≤ Cd`: Tonelli through the joint law, the uniform fresh moment
  set g : (PastSample W i × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort →
      ℝ≥0∞ := fun z => ENNReal.ofReal ‖freshDelta b E (X (b3Rebuild W i z.1)) z.2‖
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    (FullSource.measurable_freshDelta_comp b E
      (hX.comp ((measurable_b3Rebuild W i).comp measurable_fst)) measurable_snd).norm
  have hT : Measurable fun y => (b3Past W i y, Fi y) := (measurable_b3Past W i).prodMk hFi
  have hgT : (fun y => g (b3Past W i y, Fi y)) =
      fun y => ENNReal.ofReal ‖freshDelta b E (X y) (Fi y)‖ := by
    funext y; simp only [g, b3Rebuild_b3Past, hX']
  have hL : ∫⁻ y, ENNReal.ofReal ‖freshDelta b E (X y) (Fi y)‖ ∂closedLaw b W np ≤
      ENNReal.ofReal Cd := by
    rw [← hgT, ← lintegral_map hg hT, closedLaw_map_past_fresh,
      lintegral_prod _ hg.aemeasurable, ← closedLaw_map_b3Past b W np i,
      lintegral_map hg.lintegral_prod_right' (measurable_b3Past W i)]
    calc ∫⁻ y, ∫⁻ F, g (b3Past W i y, F) ∂freshLaw W b ∂closedLaw b W np ≤
          ∫⁻ _y, ENNReal.ofReal Cd ∂closedLaw b W np := by
          refine lintegral_mono_ae ?_
          filter_upwards [hXp] with y hy
          have h1 : ∫⁻ F, ‖‖freshDelta b E (X y) F‖‖ₑ ∂freshLaw W b ≤ ENNReal.ofReal Cd := by
            rw [← eLpNorm_one_eq_lintegral_enorm (hmom W hW2 E hEκ (X y) hy).1]
            simpa only [ENNReal.ofReal_one] using (hmom W hW2 E hEκ (X y) hy).2
          refine le_of_eq_of_le (lintegral_congr fun F => ?_) h1
          simp only [g, b3Rebuild_b3Past, hX', enorm_norm, ofReal_norm]
      _ = ENNReal.ofReal Cd := by rw [lintegral_const, measure_univ, mul_one]
  have hint : Integrable (fun y => bilinear (u y) (freshDelta b E (X y) (Fi y)) (v y))
      (closedLaw b W np) := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    show ∫⁻ y, ‖bilinear (u y) (freshDelta b E (X y) (Fi y)) (v y)‖ₑ ∂closedLaw b W np < ⊤
    calc ∫⁻ y, ‖bilinear (u y) (freshDelta b E (X y) (Fi y)) (v y)‖ₑ ∂closedLaw b W np ≤
          ∫⁻ y, ENNReal.ofReal (Cf ^ 2) * ENNReal.ofReal ‖freshDelta b E (X y) (Fi y)‖
            ∂closedLaw b W np := by
          refine lintegral_mono fun y => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (sq_nonneg Cf)]
          exact ENNReal.ofReal_le_ofReal (norm_bilinear_le_of_vecNorm (hub y) (hvb y))
      _ = ENNReal.ofReal (Cf ^ 2) *
            ∫⁻ y, ENNReal.ofReal ‖freshDelta b E (X y) (Fi y)‖ ∂closedLaw b W np :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp hΔm.norm)
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hL.trans_lt ENNReal.ofReal_lt_top)
  have hΔi : ∀ᵐ y ∂closedLaw b W np,
      ∀ x x', Integrable (fun F => freshDelta b E (X y) F x x') (freshLaw W b) := by
    filter_upwards [hXp] with y hy
    exact (hD W hW1 E hEκ (X y) hy).1
  filter_upwards [condExp_closed_bilinear_fresh b E i hu hv hX hu' hv' hX' hΔi hint, hXp]
    with y hy hyp
  rw [hy]
  refine (norm_bilinear_le_of_vecNorm (hub y) (hvb y)).trans ?_
  calc Cf ^ 2 * ‖matrixExpect (freshLaw W b) (freshDelta b E (X y))‖ ≤
        Cf ^ 2 * (Cm * (jetDistance0 b E (X y) + (W : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left (hD W hW1 E hEκ (X y) hyp).2.1 (sq_nonneg _)
    _ = Cm * Cf ^ 2 * (jetDistance0 b E (X y) + (W : ℝ)⁻¹) := by ring

end BlockBand.SourceProcess.PhysApprox.B3
