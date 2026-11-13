module

public import BlockBand.SourceProcess.RankFree.LocMartShift
public import BlockBand.SourceProcess.RankFree.NativeBridge
public import BlockBand.SourceProcess.Stochastic.SourceSDE.TraceBound

/-!
# The birth cross term `Re⟨W, Y_t - Y_{t∧τ}⟩`

`locMart_reInner_shift`: for an Itô process `Y` (matrix valued, drift `b`), a stopping time
`ρ` and a bounded `𝓕_ρ`-measurable random matrix `B`, the process `Re Tr(Bᴴ(Y_t - Y_{t∧ρ}))` is a
`LocMart` with drift `1{ρ < s} Re Tr(Bᴴ b_s)`. Proof: expand `Re Tr(Bᴴ ·)` in the coordinates of
`coordEquiv` (bounded `𝓕_ρ`-measurable weights), apply `LocMart.shift` to each coordinate of `Y`
(`IsNativeItoProcess.locMart_disc` with a linear `Φ`), and sum.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

/-- The generator of a continuous linear functional is its value on the drift. -/
theorem sdeGenerator_clm {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype κ]
    (b : E → E) (σ : κ → E → E) (ℓ : E →L[ℝ] ℝ) (y : E) :
    sdeGenerator b σ ℓ y = ℓ (b y) := by
  have h1 : fderiv ℝ (⇑ℓ) = fun _ => ℓ := funext fun _ => ℓ.fderiv
  unfold sdeGenerator
  rw [h1]
  simp

variable {ι c : Type*} [Fintype ι] [Fintype c]
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]

/-- **The cross term after a stopping time.** -/
theorem locMart_reInner_shift {Y b : ℝ≥0 → DriverSample S κ → Matrix ι c ℂ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Matrix ι c ℂ} (hY : IsNativeItoProcess μ Y b σ)
    {ρ : DriverSample S κ → WithTop ℝ≥0} (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ)
    {B : DriverSample S κ → Matrix ι c ℂ} (hB : StronglyMeasurable[hρ.measurableSpace] B) {C : ℝ}
    (hBb : ∀ᵐ x ∂driverLaw (κ := κ) μ, ‖B x‖ ≤ C) :
    LocMart (driverLaw (κ := κ) μ) (driverAugmented (κ := κ) μ)
      (fun t x => reInner (B x) (Y t x - stoppedProcess Y ρ t x))
      (fun s x => if ρ x < (s : WithTop ℝ≥0) then reInner (B x) (b s x) else 0) := by
  set L := coordEquiv (Matrix ι c ℂ)
  have hcoord : ∀ e, LocMart (driverLaw (κ := κ) μ) (driverAugmented (κ := κ) μ)
      (fun t x => L (Y t x) e) (fun s x => L (b s x) e) := fun e => by
    have h := hY.locMart_disc
      ((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (Module.finrank ℝ (Matrix ι c ℂ)) => ℝ) e).comp
        L.toContinuousLinearMap).contDiff 0
    simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, zero_add, sdeGenerator_clm,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearEquiv.coe_coe] at h
    exact h
  set ζ : Fin (Module.finrank ℝ (Matrix ι c ℂ)) → DriverSample S κ → ℝ :=
    fun e x => reInner (B x) (L.symm (Pi.single e 1))
  have hζ : ∀ e, StronglyMeasurable[hρ.measurableSpace] (ζ e) := fun e =>
    (reInner.flip (L.symm (Pi.single e 1))).continuous.comp_stronglyMeasurable hB
  have hζb : ∀ e, ∀ᵐ x ∂driverLaw (κ := κ) μ,
      ‖ζ e x‖ ≤ ‖(reInner : Matrix ι c ℂ →L[ℝ] Matrix ι c ℂ →L[ℝ] ℝ)‖ * C *
        ‖L.symm (Pi.single e 1)‖ := fun e => by
    filter_upwards [hBb] with x hx
    refine ((reInner : Matrix ι c ℂ →L[ℝ] Matrix ι c ℂ →L[ℝ] ℝ).le_opNorm₂ _ _).trans ?_
    gcongr
  have hs := LocMart.sum Finset.univ fun e _ => (hcoord e).shift hρ (hζ e) (hζb e)
  have hexp : ∀ (x : DriverSample S κ) (V : Matrix ι c ℂ),
      ∑ e, ζ e x * L V e = reInner (B x) V := fun x V => by
    have h := sum_mul_single ((reInner (B x)).comp
      L.symm.toContinuousLinearMap) (L V)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  have e1 : (fun t x => ∑ e, ζ e x * (L (Y t x) e -
      stoppedProcess (fun t x => L (Y t x) e) ρ t x)) =
      fun t x => reInner (B x) (Y t x - stoppedProcess Y ρ t x) := by
    funext t x
    rw [← hexp x, map_sub]
    rfl
  have e2 : (fun (s : ℝ≥0) (x : DriverSample S κ) => ∑ e, if ρ x < (s : WithTop ℝ≥0) then ζ e x * L (b s x) e else 0) =
      fun (s : ℝ≥0) (x : DriverSample S κ) =>
        if ρ x < (s : WithTop ℝ≥0) then reInner (B x) (b s x) else 0 := by
    funext s x
    split_ifs
    · exact hexp x _
    · simp
  rw [e1, e2] at hs
  exact hs

end BlockBand.SourceProcess.RankFree
