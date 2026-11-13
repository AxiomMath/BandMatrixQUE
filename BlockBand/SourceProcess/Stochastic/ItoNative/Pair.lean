module
public import BlockBand.SourceProcess.Stochastic.ItoNative.Formula
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The pair of two Itô processes

Sample space `DriverSample S κ`, law `driverLaw μ`, augmented filtration `driverAugmented μ`.

`IsNativeItoProcess.prod`: if `X` (in `E`; `bX`, `σX`) and `Y` (in `F`; `bY`, `σY`) are native
Itô processes on the same driver space, then `(X, Y)` is an Itô process in `E × F` with
drift `(bX, bY)` and diffusion `(σX_a, σY_a)`.

The identity clause cannot be split into the two components (for a functional
`ℓ = ℓ₁ ∘ fst + ℓ₂ ∘ snd` the stopped integrand `ℓ₁ σX + ℓ₂ σY` may be in `L²` without its two
summands being so), so it is obtained from the core identity `CoordRep.ito_identity` applied to
the concatenated coordinate representation `(e₁ X, e₂ Y)` and the linear function
`ψ(t, z) = ℓ(e₁⁻¹ z₁, e₂⁻¹ z₂)`.
-/

namespace BlockBand.SourceProcess.Stochastic.ItoNative
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
variable {d₁ d₂ : ℕ}

/-- The chart `(t, z) ↦ (t, (e₁⁻¹ z₁, e₂⁻¹ z₂))` of `ℝ × ℝ^{d₁ + d₂}`. -/
def pairChartL (e₁ : E ≃L[ℝ] (Fin d₁ → ℝ)) (e₂ : F ≃L[ℝ] (Fin d₂ → ℝ)) :
    ℝ × (Fin (d₁ + d₂) → ℝ) →L[ℝ] ℝ × (E × F) :=
  (ContinuousLinearMap.fst ℝ ℝ (Fin (d₁ + d₂) → ℝ)).prod
    ((((e₁.symm : (Fin d₁ → ℝ) →L[ℝ] E).comp (ContinuousLinearMap.pi fun i : Fin d₁ =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d₁ + d₂) => ℝ) (Fin.castAdd d₂ i))).prod
      ((e₂.symm : (Fin d₂ → ℝ) →L[ℝ] F).comp (ContinuousLinearMap.pi fun j : Fin d₂ =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d₁ + d₂) => ℝ) (Fin.natAdd d₁ j)))).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin (d₁ + d₂) → ℝ)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem pairChartL_apply (e₁ : E ≃L[ℝ] (Fin d₁ → ℝ)) (e₂ : F ≃L[ℝ] (Fin d₂ → ℝ)) (r : ℝ)
    (z : Fin (d₁ + d₂) → ℝ) :
    pairChartL e₁ e₂ (r, z) =
      (r, (e₁.symm (fun i => z (Fin.castAdd d₂ i)), e₂.symm (fun j => z (Fin.natAdd d₁ j)))) :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem pairChartL_concat (e₁ : E ≃L[ℝ] (Fin d₁ → ℝ)) (e₂ : F ≃L[ℝ] (Fin d₂ → ℝ)) (r : ℝ)
    (u : Fin d₁ → ℝ) (v : Fin d₂ → ℝ) :
    pairChartL e₁ e₂ (r, concatCoord u v) = (r, (e₁.symm u, e₂.symm v)) := by
  rw [pairChartL_apply]
  have h1 : (fun i => concatCoord u v (Fin.castAdd d₂ i)) = u :=
    funext fun i => concatCoord_castAdd u v i
  have h2 : (fun j => concatCoord u v (Fin.natAdd d₁ j)) = v :=
    funext fun j => concatCoord_natAdd u v j
  rw [h1, h2]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem pairChartL_one_zero (e₁ : E ≃L[ℝ] (Fin d₁ → ℝ)) (e₂ : F ≃L[ℝ] (Fin d₂ → ℝ)) :
    pairChartL e₁ e₂ ((1 : ℝ), (0 : Fin (d₁ + d₂) → ℝ)) = (1, (0, 0)) := by
  rw [pairChartL_apply]
  have h1 : (fun i => (0 : Fin (d₁ + d₂) → ℝ) (Fin.castAdd d₂ i)) = 0 := rfl
  have h2 : (fun j => (0 : Fin (d₁ + d₂) → ℝ) (Fin.natAdd d₁ j)) = 0 := rfl
  rw [h1, h2, map_zero, map_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem contDiff_snd' : ContDiff ℝ 2 (fun q : ℝ × (E × F) => q.2) := contDiff_snd

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem fderiv_snd' (q v : ℝ × (E × F)) : fderiv ℝ (fun q : ℝ × (E × F) => q.2) q v = v.2 := by
  rw [fderiv_snd]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem fderiv_fderiv_snd' (q v w : ℝ × (E × F)) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × (E × F) => q.2)) q v w = 0 := by
  have h : fderiv ℝ (fun q : ℝ × (E × F) => q.2) =
      fun _ => ContinuousLinearMap.snd ℝ ℝ (E × F) := funext fun q => fderiv_snd
  rw [h]
  simp

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [IsProbabilityMeasure μ] [MeasurableSpace S] [Fintype κ] in
/-- Stopping a sum of integrands. -/
theorem stopIntegrand_add' (ρ : DriverSample S κ → WithTop ℝ≥0)
    (g g' : κ → ℝ × DriverSample S κ → ℝ) :
    stopIntegrand ρ (fun a p => g a p + g' a p) =
      fun a p => stopIntegrand ρ g a p + stopIntegrand ρ g' a p := by
  funext a p
  simp only [stopIntegrand]
  split_ifs <;> simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
/-- **The pair of two Itô processes is an Itô process.** -/
theorem _root_.BlockBand.SourceProcess.Stochastic.IsNativeItoProcess.prod
    {X bX : ℝ≥0 → DriverSample S κ → E} {σX : κ → ℝ≥0 → DriverSample S κ → E}
    {Y bY : ℝ≥0 → DriverSample S κ → F} {σY : κ → ℝ≥0 → DriverSample S κ → F}
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hX : IsNativeItoProcess μ X bX σX) (hY : IsNativeItoProcess μ Y bY σY) :
    IsNativeItoProcess μ (fun t x => (X t x, Y t x)) (fun t x => (bX t x, bY t x))
      (fun a t x => (σX a t x, σY a t x)) := by
  obtain ⟨τX, hτXs, hτXl, hlX⟩ := hX.localizing
  obtain ⟨τY, hτYs, hτYl, hlY⟩ := hY.localizing
  have hsplit : ∀ (ℓ : E × F →L[ℝ] ℝ) (u : E) (v : F),
      ℓ (u, v) = ℓ.comp (ContinuousLinearMap.inl ℝ E F) u +
        ℓ.comp (ContinuousLinearMap.inr ℝ E F) v := by
    intro ℓ u v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← map_add]
    simp
  refine ⟨fun t => (hX.adapted t).prodMk (hY.adapted t),
    fun t => (hX.progressive t).prodMk (hY.progressive t), ?_,
    fun t => (hX.drift_progressive t).prodMk (hY.drift_progressive t),
    fun a t => (hX.diffusion_progressive a t).prodMk (hY.diffusion_progressive a t), ?_,
    ⟨fun n x => min (τX n x) (τY n x), fun n => (hτXs n).min (hτYs n), ?_, fun n ℓ T => ?_⟩, ?_⟩
  · filter_upwards [hX.continuous, hY.continuous] with x h1 h2
    exact h1.prodMk h2
  · filter_upwards [hX.drift_integrable, hY.drift_integrable] with x h1 h2 t
    exact (h1 t).prodMk (h2 t)
  · filter_upwards [hτXl, hτYl] with x h1 h2
    simpa using h1.min h2
  · have e : functionalIntegrand ℓ (fun a t x => (σX a t x, σY a t x)) = fun a p =>
        functionalIntegrand (ℓ.comp (ContinuousLinearMap.inl ℝ E F)) σX a p +
          functionalIntegrand (ℓ.comp (ContinuousLinearMap.inr ℝ E F)) σY a p := by
      funext a p
      exact hsplit ℓ _ _
    beta_reduce
    rw [e, stopIntegrand_add']
    refine NativeSDE.nativeIntegrand_add ?_ ?_
    · rw [← stopIntegrand_stopIntegrand]
      exact stopIntegrand_nativeIntegrand (hlX n _ T) (hτYs n)
    · have e2 : (fun x => min (τX n x) (τY n x)) = fun x => min (τY n x) (τX n x) :=
        funext fun x => min_comm _ _
      rw [e2, ← stopIntegrand_stopIntegrand]
      exact stopIntegrand_nativeIntegrand (hlY n _ T) (hτXs n)
  -- identity clause, through the core identity on the concatenated coordinates
  intro ℓ ρ hρ T hG t ht
  set n₁ := Module.finrank ℝ E
  set n₂ := Module.finrank ℝ F
  let e₁ : E ≃L[ℝ] (Fin n₁ → ℝ) := ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ : F ≃L[ℝ] (Fin n₂ → ℝ) := ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  have hXc : IsNativeItoProcess μ (fun t x => e₁ (X t x)) (fun t x => e₁ (bX t x))
      (fun a t x => e₁ (σX a t x)) := hX.map_clm (e₁ : E →L[ℝ] (Fin n₁ → ℝ))
  have hYc : IsNativeItoProcess μ (fun t x => e₂ (Y t x)) (fun t x => e₂ (bY t x))
      (fun a t x => e₂ (σY a t x)) := hY.map_clm (e₂ : F →L[ℝ] (Fin n₂ → ℝ))
  have HZ := hXc.coordRep.concat hYc.coordRep
  set ψ := affineComp ℓ (fun q : ℝ × (E × F) => q.2) (pairChartL e₁ e₂) 0 with hψdef
  have hψ : ContDiff ℝ 2 ψ := contDiff_affineComp contDiff_snd' _ _ _
  have hI : itoIntegrand ψ (fun t x => concatCoord (e₁ (X t x)) (e₂ (Y t x)))
      (fun a t x => concatCoord (e₁ (σX a t x)) (e₂ (σY a t x))) =
      functionalIntegrand ℓ (fun a t x => (σX a t x, σY a t x)) := by
    funext a p
    simp only [itoIntegrand, functionalIntegrand, hψdef, fderiv_affineComp contDiff_snd',
      pairChartL_concat, fderiv_snd', ContinuousLinearEquiv.symm_apply_apply, zero_apply,
      add_zero]
  rw [← hI] at hG
  obtain ⟨hs, heq⟩ := HZ.ito_identity hψ hρ hG ht
  have e1 : stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
      (itoIntegrand ψ (fun t x => concatCoord (e₁ (X t x)) (e₂ (Y t x)))
        (fun a t x => concatCoord (e₁ (σX a t x)) (e₂ (σY a t x)))) =
      stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
        (functionalIntegrand ℓ (fun a t x => (σX a t x, σY a t x))) := by
    rw [hI]
  refine ⟨e1 ▸ hs, ?_⟩
  rw [← Bridges.nativeIntegralOf_congr e1 hs (e1 ▸ hs)]
  filter_upwards [heq, hX.drift_integrable, hY.drift_integrable] with x h1 h2 h3
  rw [← h1, stoppedDrift_clm ℓ (b := fun t x => (bX t x, bY t x)) ((h2 t).prodMk (h3 t))]
  have hdr : itoDriftProc ψ (fun t x => concatCoord (e₁ (X t x)) (e₂ (Y t x)))
      (fun t x => concatCoord (e₁ (bX t x)) (e₂ (bY t x)))
      (fun a t x => concatCoord (e₁ (σX a t x)) (e₂ (σY a t x))) =
      fun (s : ℝ≥0) x => ℓ (bX s x, bY s x) := by
    funext s x
    simp only [itoDriftProc, itoDrift_covOf, hψdef, fderiv_affineComp contDiff_snd',
      fderiv_fderiv_affineComp contDiff_snd', pairChartL_concat, pairChartL_one_zero,
      fderiv_snd', fderiv_fderiv_snd', ContinuousLinearEquiv.symm_apply_apply, zero_apply,
      add_zero, map_zero, Finset.sum_const_zero, mul_zero]
    rw [Prod.mk_zero_zero, map_zero, zero_add]
  rw [hdr]
  simp only [stoppedProcess_eq_stopTime, hψdef, affineComp, pairChartL_concat,
    ContinuousLinearEquiv.symm_apply_apply, zero_apply, add_zero]

end BlockBand.SourceProcess.Stochastic.ItoNative
