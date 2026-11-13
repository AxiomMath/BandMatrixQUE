module

public import BlockBand.SourceProcess.RankFree.LocMart
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionExit
public import BlockBand.SourceProcess.Stochastic.Assembly.ItoUniverse

/-!
# From Itô processes to `LocMart`

* `IsNativeItoProcess.locMart_disc`: for an Itô process `Y` in a finite-dimensional space
  `E` with drift `b` and diffusion `σ`, a `C²` function `Φ : E → ℝ` and a rate `c`,
  `e^{-ct} Φ(Y_t)` is a `LocMart` with drift
  `e^{-cs} (-c Φ(Y_s) + DΦ(Y_s)[b_s] + ½ ∑_a D²Φ(Y_s)[σ_a(s), σ_a(s)])`.
  Route: coordinates (`IsNativeItoProcess.map_equiv`), the bridge
  (`isContinuousSemimartingale`), the proved Itô contract (`semimartingaleItoFormulaU_holds`)
  for `discFun (t, y) = e^{-ct} Φ(L⁻¹ y)`, and the drift computation `itoDrift_discFun`
  (the computation of `NonexplosionCalculus` without the `1 +`).
* `IsNativeItoProcess.add_const`: adding an `𝓕₀`-measurable random constant.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal BigOperators

section Calculus

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Φ : E → ℝ} (L : E ≃L[ℝ] (Fin d → ℝ)) (c : ℝ)

/-- The discounted test function `e^{-ct} Φ(L⁻¹ y)`. -/
def discFun (Φ : E → ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ := Real.exp (-c * p.1) * Φ (L.symm p.2)

theorem contDiff_discFun (hΦ : ContDiff ℝ 2 Φ) : ContDiff ℝ 2 (discFun L c Φ) :=
  (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)).mul
    (hΦ.comp ((L.symm : (Fin d → ℝ) →L[ℝ] E).contDiff.comp contDiff_snd))

theorem fderiv_discFun_space (hΦ : ContDiff ℝ 2 Φ) (q : ℝ × (Fin d → ℝ)) (w : Fin d → ℝ) :
    fderiv ℝ (discFun L c Φ) q (0, w) =
      Real.exp (-c * q.1) * fderiv ℝ Φ (L.symm q.2) (L.symm w) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hH : HasFDerivAt (fun y : Fin d → ℝ => Φ (L.symm y))
      ((fderiv ℝ Φ (L.symm q.2)).comp (L.symm : (Fin d → ℝ) →L[ℝ] E)) q.2 :=
    (hΦd _).hasFDerivAt.comp q.2 L.symm.hasFDerivAt
  have h := fderiv_mul_prod_apply (G := fun s => Real.exp (-c * s))
    (K := fun y : Fin d → ℝ => Φ (L.symm y)) (t := q.1) (y := q.2)
    (hasDerivAt_expc c _).differentiableAt hH.differentiableAt 0 w
  rw [hH.fderiv] at h
  simp only [zero_mul, zero_add, ContinuousLinearMap.comp_apply] at h
  exact h

theorem fderiv_discFun_time (hΦ : ContDiff ℝ 2 Φ) (q : ℝ × (Fin d → ℝ)) :
    fderiv ℝ (discFun L c Φ) q (1, 0) = -c * Real.exp (-c * q.1) * Φ (L.symm q.2) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hK : DifferentiableAt ℝ (fun y : Fin d → ℝ => Φ (L.symm y)) q.2 :=
    (hΦd _).comp q.2 L.symm.differentiableAt
  have hG := hasDerivAt_expc c q.1
  have h := fderiv_mul_prod_apply (G := fun s => Real.exp (-c * s))
    (K := fun y : Fin d → ℝ => Φ (L.symm y)) (t := q.1) (y := q.2) hG.differentiableAt hK 1 0
  rw [hG.deriv, map_zero, mul_zero, add_zero] at h
  change fderiv ℝ (fun q : ℝ × (Fin d → ℝ) => Real.exp (-c * q.1) * Φ (L.symm q.2))
    (q.1, q.2) (1, 0) = _ at h
  unfold discFun
  rw [h]
  ring

theorem fderiv_fderiv_discFun_space (hΦ : ContDiff ℝ 2 Φ) (p : ℝ × (Fin d → ℝ))
    (v w : Fin d → ℝ) :
    fderiv ℝ (fderiv ℝ (discFun L c Φ)) p (0, v) (0, w) =
      Real.exp (-c * p.1) * fderiv ℝ (fderiv ℝ Φ) (L.symm p.2) (L.symm v) (L.symm w) := by
  have hφ1 : Differentiable ℝ (fderiv ℝ (discFun L c Φ)) :=
    ((contDiff_discFun L c hΦ).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hΦ1 : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [← fderiv_apply_const (hφ1 p) (0, w) (0, v)]
  have hfun : (fun q => fderiv ℝ (discFun L c Φ) q (0, w)) = fun q : ℝ × (Fin d → ℝ) =>
      Real.exp (-c * q.1) * fderiv ℝ Φ (L.symm q.2) (L.symm w) :=
    funext fun q => fderiv_discFun_space L c hΦ q w
  rw [hfun]
  have hK : HasFDerivAt (fun y : Fin d → ℝ => fderiv ℝ Φ (L.symm y) (L.symm w))
      ((fderiv ℝ (fun z => fderiv ℝ Φ z (L.symm w)) (L.symm p.2)).comp
        (L.symm : (Fin d → ℝ) →L[ℝ] E)) p.2 :=
    (((hΦ1 _).clm_apply (differentiableAt_const _)).hasFDerivAt).comp p.2 L.symm.hasFDerivAt
  have h := fderiv_mul_prod_apply (G := fun s => Real.exp (-c * s))
    (K := fun y : Fin d → ℝ => fderiv ℝ Φ (L.symm y) (L.symm w)) (t := p.1) (y := p.2)
    (hasDerivAt_expc c _).differentiableAt hK.differentiableAt 0 v
  rw [hK.fderiv, zero_mul, zero_mul, zero_add, ContinuousLinearMap.comp_apply,
    fderiv_apply_const (hΦ1 _)] at h
  exact h

/-- **Itô drift of the discounted test function.** -/
theorem itoDrift_discFun {κ : Type*} [Fintype κ] (hΦ : ContDiff ℝ 2 Φ) (y : Fin d → ℝ)
    (t : ℝ≥0) (β : Fin d → ℝ) (γ : κ → Fin d → ℝ) :
    itoDrift (discFun L c Φ) y t β (Matrix.of fun i j => ∑ a, γ a i * γ a j) =
      Real.exp (-c * t) * (-c * Φ (L.symm y) + sdeGenerator (fun _ => L.symm β)
        (fun a _ => L.symm (γ a)) Φ (L.symm y)) := by
  unfold itoDrift partialTime partialSpace partialSpace2 sdeGenerator
  simp only [Matrix.of_apply, fderiv_discFun_time L c hΦ, fderiv_discFun_space L c hΦ,
    fderiv_fderiv_discFun_space L c hΦ]
  have h1 : ∑ i, β i * (Real.exp (-c * t) * fderiv ℝ Φ (L.symm y) (L.symm (Pi.single i 1))) =
      Real.exp (-c * t) * fderiv ℝ Φ (L.symm y) (L.symm β) := by
    have h := sum_mul_single ((fderiv ℝ Φ (L.symm y)).comp (L.symm : (Fin d → ℝ) →L[ℝ] E)) β
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 := sum_cov_mul_single (((fderiv ℝ (fderiv ℝ Φ) (L.symm y)).bilinearComp
    (L.symm : (Fin d → ℝ) →L[ℝ] E) (L.symm : (Fin d → ℝ) →L[ℝ] E))) γ (Real.exp (-c * t))
  simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe] at h2
  rw [h1, h2]
  ring

end Calculus

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Discounted `C²` functionals of Itô processes are `LocMart`s.** -/
theorem _root_.BlockBand.SourceProcess.Stochastic.IsNativeItoProcess.locMart_disc
    {Y b : ℝ≥0 → DriverSample S κ → E} {σ : κ → ℝ≥0 → DriverSample S κ → E}
    (hY : IsNativeItoProcess μ Y b σ) {Φ : E → ℝ} (hΦ : ContDiff ℝ 2 Φ) (c : ℝ) :
    LocMart (driverLaw (κ := κ) μ) (driverAugmented (κ := κ) μ)
      (fun t x => Real.exp (-c * t) * Φ (Y t x))
      (fun s x => Real.exp (-c * s) * (-c * Φ (Y s x) +
        sdeGenerator (fun _ => b s x) (fun a _ => σ a s x) Φ (Y s x))) := by
  set L := coordEquiv E
  have hS := (IsNativeItoProcess.map_equiv hY L).isContinuousSemimartingale
  have hφ := contDiff_discFun L c hΦ
  have hZ := SemimartingaleIto.semimartingaleItoFormulaU_holds _ (DriverSample S κ)
    (driverLaw (κ := κ) μ) (driverAugmented (κ := κ) μ) _ _ _ hS univ isOpen_univ
    (Eventually.of_forall fun _ _ => mem_univ _) (discFun L c Φ) hφ.continuous.measurable
    hφ.contDiffOn
  have h := LocMart.of_sm hZ
  simp only [itoDrift_discFun L c hΦ, discFun, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Adding an `𝓕₀`-measurable random constant to an Itô process. -/
theorem _root_.BlockBand.SourceProcess.Stochastic.IsNativeItoProcess.add_const
    {Y b : ℝ≥0 → DriverSample S κ → E} {σ : κ → ℝ≥0 → DriverSample S κ → E}
    (hY : IsNativeItoProcess μ Y b σ) {C : DriverSample S κ → E}
    (hC : StronglyMeasurable[driverAugmented (κ := κ) μ 0] C) :
    IsNativeItoProcess μ (fun t x => Y t x + C x) b σ := by
  have hCp : IsStronglyProgressive (driverAugmented (κ := κ) μ) (fun (_ : ℝ≥0) x => C x) :=
    fun i => (hC.mono ((driverAugmented (κ := κ) μ).mono zero_le)).comp_measurable measurable_snd
  refine ⟨fun t => (hY.adapted t).add (hC.mono ((driverAugmented (κ := κ) μ).mono zero_le)),
    hY.progressive.add hCp, hY.continuous.mono fun x hx => hx.add continuous_const,
    hY.drift_progressive, hY.diffusion_progressive, hY.drift_integrable, hY.localizing, ?_⟩
  intro ℓ τ hτ T hint t ht
  obtain ⟨hs, hid⟩ := hY.identity ℓ τ hτ T hint t ht
  refine ⟨hs, ?_⟩
  filter_upwards [hid] with x hx
  rw [← hx]
  simp only [stoppedProcess, map_add]
  ring

end BlockBand.SourceProcess.RankFree
