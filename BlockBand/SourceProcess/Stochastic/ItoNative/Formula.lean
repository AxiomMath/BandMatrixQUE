module
public import BlockBand.SourceProcess.Stochastic.ItoNative.Localize
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Itô formula (`ItoFormulaFor`)

Sample space `DriverSample S κ`, law `driverLaw μ`, augmented filtration `driverAugmented μ`.
`X` is an Itô process in a finite-dimensional `E` with drift `b` and diffusion `σ`, and
`φ : ℝ × E → F` is `C²`. With a linear chart `e : E ≃L ℝ^d`, `Z = e X` is a `CoordRep`
(`IsNativeItoProcess.map_clm`, `.coordRep`). For a functional `ℓ : F →L ℝ` the real function
`ψ_ℓ(t, z) = ℓ(φ(t, e⁻¹ z))` is `C²`, and

* `itoIntegrand_chart`: its candidate integrand is `ℓ(D_xφ(t, X_t)[σ_a])`;
* `itoDriftProc_chart`: its Itô drift is `ℓ(∂_tφ + D_xφ[b] + ½ ∑_a D_x²φ[σ_a, σ_a])`.

Then `CoordRep.ito_identity` gives the identity clause for every `ℓ` and stopping time `τ`;
the Itô formula `SemimartingaleItoFormula` applied to `ψ_ℓ` for the coordinate functionals of
`F` gives the a.s. local
integrability of the drift; `IsNativeItoProcess.exists_localizer_comp` gives the localizing
clause; the measurability fields are continuity of `φ` and its first two derivatives.

`itoFormulaFor_native : ItoFormulaFor μ E F` for all `S, κ, μ, E, F`.
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
variable {d : ℕ}

/-- The chart `(t, z) ↦ (t, e⁻¹ z)`. -/
def chartL (e : E ≃L[ℝ] (Fin d → ℝ)) : ℝ × (Fin d → ℝ) →L[ℝ] ℝ × E :=
  (ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ)).prod
    ((e.symm : (Fin d → ℝ) →L[ℝ] E).comp (ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chartL_apply (e : E ≃L[ℝ] (Fin d → ℝ)) (r : ℝ) (z : Fin d → ℝ) :
    chartL e (r, z) = (r, e.symm z) := rfl

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [MeasurableSpace S] [Fintype κ] in
/-- The candidate integrand of `ψ_ℓ` along `e X` is `ℓ(D_xφ(t, X_t)[σ_a])`. -/
theorem itoIntegrand_chart {φ : ℝ × E → F} (hφ : ContDiff ℝ 2 φ) (ℓ : F →L[ℝ] ℝ)
    (e : E ≃L[ℝ] (Fin d → ℝ)) (X : ℝ≥0 → DriverSample S κ → E)
    (σ : κ → ℝ≥0 → DriverSample S κ → E) :
    itoIntegrand (affineComp ℓ φ (chartL e) 0) (fun t x => e (X t x)) (fun a t x => e (σ a t x)) =
      functionalIntegrand ℓ (fun a t x => spaceDeriv φ ((t : ℝ), X t x) (σ a t x)) := by
  funext a p
  simp only [itoIntegrand, functionalIntegrand, fderiv_affineComp hφ, chartL_apply,
    ContinuousLinearEquiv.symm_apply_apply, zero_apply, add_zero,
    spaceDeriv]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [MeasurableSpace S] in
/-- The Itô drift of `ψ_ℓ` along `e X` is `ℓ` of the Itô drift of `φ` along `X`. -/
theorem itoDriftProc_chart {φ : ℝ × E → F} (hφ : ContDiff ℝ 2 φ) (ℓ : F →L[ℝ] ℝ)
    (e : E ≃L[ℝ] (Fin d → ℝ)) (X b : ℝ≥0 → DriverSample S κ → E)
    (σ : κ → ℝ≥0 → DriverSample S κ → E) (s : ℝ≥0) (x : DriverSample S κ) :
    itoDriftProc (affineComp ℓ φ (chartL e) 0) (fun t x => e (X t x)) (fun t x => e (b t x))
        (fun a t x => e (σ a t x)) s x =
      ℓ (timeDeriv φ ((s : ℝ), X s x) + spaceDeriv φ ((s : ℝ), X s x) (b s x) +
        (1 / 2 : ℝ) • ∑ a, spaceDeriv2 φ ((s : ℝ), X s x) (σ a s x) (σ a s x)) := by
  simp only [itoDriftProc, itoDrift_covOf, fderiv_affineComp hφ, fderiv_fderiv_affineComp hφ,
    chartL_apply, ContinuousLinearEquiv.symm_apply_apply, zero_apply,
    add_zero, map_zero, map_add, map_smul, map_sum, smul_eq_mul, timeDeriv, spaceDeriv,
    spaceDeriv2]

variable {μ : Measure S} [IsProbabilityMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem continuous_fderiv_apply_space {φ : ℝ × E → F} (hφ : ContDiff ℝ 2 φ) :
    Continuous fun q : ℝ × E × E => fderiv ℝ φ (q.1, q.2.1) ((0 : ℝ), q.2.2) :=
  ((hφ.continuous_fderiv (by norm_num)).comp (continuous_fst.prodMk
    (continuous_fst.comp continuous_snd))).clm_apply
    (continuous_const.prodMk (continuous_snd.comp continuous_snd))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem continuous_fderiv2_apply_space {φ : ℝ × E → F} (hφ : ContDiff ℝ 2 φ) :
    Continuous fun q : ℝ × E × E =>
      fderiv ℝ (fderiv ℝ φ) (q.1, q.2.1) ((0 : ℝ), q.2.2) ((0 : ℝ), q.2.2) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hc := h1.continuous_fderiv (by norm_num)
  have hq : Continuous fun q : ℝ × E × E => (q.1, q.2.1) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hv : Continuous fun q : ℝ × E × E => ((0 : ℝ), q.2.2) :=
    continuous_const.prodMk (continuous_snd.comp continuous_snd)
  exact ((hc.comp hq).clm_apply hv).clm_apply hv

/-- **The Itô formula** (exported as `itoFormulaFor_holds`). -/
theorem itoFormulaFor_native : ItoFormulaFor (κ := κ) μ E F := by
  intro X b σ hX φ hφ
  set d := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  have hXc : IsNativeItoProcess μ (fun t x => e (X t x)) (fun t x => e (b t x))
      (fun a t x => e (σ a t x)) := hX.map_clm (e : E →L[ℝ] (Fin d → ℝ))
  have HZ := hXc.coordRep
  have HS := HZ.isContinuousSemimartingale
  have hφc : Continuous φ := hφ.continuous
  -- drift integrability, coordinatewise through the semimartingale Itô formula
  have hbint : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ =>
      timeDeriv φ ((s.toNNReal : ℝ), X s.toNNReal x) +
        spaceDeriv φ ((s.toNNReal : ℝ), X s.toNNReal x) (b s.toNNReal x) +
        (1 / 2 : ℝ) • ∑ a, spaceDeriv2 φ ((s.toNNReal : ℝ), X s.toNNReal x)
          (σ a s.toNNReal x) (σ a s.toNNReal x)) (Ioc 0 t) := by
    set m := Module.finrank ℝ F
    let eF : F ≃L[ℝ] (Fin m → ℝ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
    have hk : ∀ k : Fin m, ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ =>
        eF (timeDeriv φ ((s.toNNReal : ℝ), X s.toNNReal x) +
          spaceDeriv φ ((s.toNNReal : ℝ), X s.toNNReal x) (b s.toNNReal x) +
          (1 / 2 : ℝ) • ∑ a, spaceDeriv2 φ ((s.toNNReal : ℝ), X s.toNNReal x)
            (σ a s.toNNReal x) (σ a s.toNNReal x)) k) (Ioc 0 t) := by
      intro k
      have hψ := contDiff_affineComp hφ ((coordFun k).comp (eF : F →L[ℝ] (Fin m → ℝ)))
        (chartL e) 0
      have H1 := isContinuousSemimartingale_ito HS hψ.continuous.measurable hψ
      filter_upwards [H1.integrable] with x hx t
      refine ((hx t).1 0).congr_fun (fun s _ => ?_) measurableSet_Ioc
      exact itoDriftProc_chart hφ _ e X b σ s.toNNReal x
    filter_upwards [ae_all_iff.2 hk] with x hx t
    have h1 := (eF.symm : (Fin m → ℝ) →L[ℝ] F).integrable_comp
      (integrable_pi_iff.2 fun k => hx k t)
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h1
    exact h1
  -- localizing sequence
  have hA : Continuous fun q : ℝ × E => (fderiv ℝ φ q).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    (hφ.continuous_fderiv (by norm_num)).clm_comp continuous_const
  obtain ⟨τ, hτs, hτlim, hloc⟩ := hX.exists_localizer_comp hA
  refine ⟨fun t => hφc.comp_stronglyMeasurable (stronglyMeasurable_const.prodMk (hX.adapted t)),
    isStronglyProgressive_timeComp hX.progressive hφc, ?_, ?_, fun a => ?_, hbint,
    ⟨τ, hτs, hτlim, hloc⟩, ?_⟩
  · filter_upwards [hX.continuous] with x hx
    exact hφc.comp (NNReal.continuous_coe.prodMk hx)
  · have h1 : IsStronglyProgressive (driverAugmented (κ := κ) μ)
        (fun t x => timeDeriv φ ((t : ℝ), X t x)) :=
      isStronglyProgressive_timeComp hX.progressive
        ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    have h2 : IsStronglyProgressive (driverAugmented (κ := κ) μ)
        (fun t x => spaceDeriv φ ((t : ℝ), X t x) (b t x)) :=
      isStronglyProgressive_timeComp (Y := fun t x => (X t x, b t x))
        (fun i => (hX.progressive i).prodMk (hX.drift_progressive i))
        (continuous_fderiv_apply_space hφ)
    have h3 : ∀ a, IsStronglyProgressive (driverAugmented (κ := κ) μ)
        (fun t x => spaceDeriv2 φ ((t : ℝ), X t x) (σ a t x) (σ a t x)) := fun a =>
      isStronglyProgressive_timeComp (Y := fun t x => (X t x, σ a t x))
        (fun i => (hX.progressive i).prodMk (hX.diffusion_progressive a i))
        (continuous_fderiv2_apply_space hφ)
    intro i
    exact ((h1 i).add (h2 i)).add
      ((Finset.stronglyMeasurable_fun_sum _ fun a _ => h3 a i).const_smul _)
  · exact isStronglyProgressive_timeComp (Y := fun t x => (X t x, σ a t x))
      (fun i => (hX.progressive i).prodMk (hX.diffusion_progressive a i))
      (continuous_fderiv_apply_space hφ)
  · intro ℓ ρ hρ T hG t ht
    have hψ := contDiff_affineComp hφ ℓ (chartL e) 0
    have hI := itoIntegrand_chart (S := S) hφ ℓ e X σ
    rw [← hI] at hG
    obtain ⟨hs, heq⟩ := HZ.ito_identity hψ hρ hG ht
    have e1 : stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
        (itoIntegrand (affineComp ℓ φ (chartL e) 0) (fun t x => e (X t x))
          (fun a t x => e (σ a t x))) =
        stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
          (functionalIntegrand ℓ (fun a t x => spaceDeriv φ ((t : ℝ), X t x) (σ a t x))) := by
      rw [hI]
    refine ⟨e1 ▸ hs, ?_⟩
    rw [← Bridges.nativeIntegralOf_congr e1 hs (e1 ▸ hs)]
    filter_upwards [heq, hbint] with x h1 h2
    rw [← h1, stoppedDrift_clm ℓ (h2 t)]
    have hdr : itoDriftProc (affineComp ℓ φ (chartL e) 0) (fun t x => e (X t x))
        (fun t x => e (b t x)) (fun a t x => e (σ a t x)) = fun (s : ℝ≥0) x =>
        ℓ (timeDeriv φ ((s : ℝ), X s x) + spaceDeriv φ ((s : ℝ), X s x) (b s x) +
          (1 / 2 : ℝ) • ∑ a, spaceDeriv2 φ ((s : ℝ), X s x) (σ a s x) (σ a s x)) :=
      funext fun s => funext fun x => itoDriftProc_chart hφ ℓ e X b σ s x
    rw [hdr]
    simp only [stoppedProcess_eq_stopTime, affineComp, chartL_apply,
      ContinuousLinearEquiv.symm_apply_apply, zero_apply, add_zero]

end BlockBand.SourceProcess.Stochastic.ItoNative
