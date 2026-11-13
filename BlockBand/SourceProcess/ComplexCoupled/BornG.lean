module

public import BlockBand.SourceProcess.ComplexCoupled.BornK
public import BlockBand.SourceProcess.Stochastic.GramChar.Conditional
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartLip
public import BlockBand.SourceProcess.Stochastic.SourceSDE.Main

/-!
# The born compensated Gram coordinates are driftless Itô processes

For a constrained ambient solution `Y` (`IsSDESolution`, two-projection constraint at time `0`) with
Gram process `𝒢 = gramPair P Y`:
* `isNativeItoProcess_gramComp`: each compensated coordinate `gramCompensated D₀ 𝖣' 𝒢 e` is an
  Itô process with zero drift and diffusion `gramEntry e (gramNoise(Y))` (the conditional
  Gram characterization `GramChar.Conditional` and `isNativeItoProcess_sub_drift`).
* `isNativeItoProcess_bornGram`: for born coordinates `θ, λ` with `L 𝖣 Lᴴ = 𝖣'` and a frame `X` with
  `X_t = Y_t L_t` at all times a.s., the transformed process `bornRep θ λ (gramCompensated 𝒢) e`
  is an Itô process with zero drift and diffusion `gramEntry e (gramNoise(X))`
  (`gramNoise_mul`). Under `BornRepresents` it is the born compensated coordinate
  (`bornCompensated_eq_bornRep`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SourceAlgebra
open BlockBand.SourceProcess.ModelExist BlockBand.SourceProcess.CoupledFrames
open BlockBand.SourceProcess.ComplexConstruct

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- `gramEntry e` as a continuous real-linear map. -/
def gCLM (e : Fin 2 × c × c) : Matrix c c ℂ × Matrix c c ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := gramEntry e
      map_add' := fun _ _ => by
        simp only [gramEntry, Prod.fst_add, Prod.snd_add, Matrix.add_apply]; split_ifs <;> rfl
      map_smul' := fun _ _ => by
        simp only [gramEntry, Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply, RingHom.id_apply]
        split_ifs <;> rfl }

omit [DecidableEq c] in
theorem gCLM_apply (e : Fin 2 × c × c) (H : Matrix c c ℂ × Matrix c c ℂ) :
    gCLM e H = gramEntry e H := rfl

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ι c' : Type*} [Fintype ι] [DecidableEq ι] [Fintype c'] [DecidableEq c']

omit [DecidableEq c'] in
/-- **Compensated ambient Gram coordinates.** -/
theorem isNativeItoProcess_gramComp {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    (hP : IsNearProjection P Naux) {D' : Matrix c' c' ℂ} (hD : IsSignature D')
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c' ℂ}
    (hξm : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξc : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D' (ξ x))
    {Y : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c' ℂ}
    (hY : IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D') ξ Y)
    (e : Fin 2 × c' × c') :
    IsNativeItoProcess μ (gramCompensated D0 D' (fun t x => gramPair P (Y t x)) e)
      (fun _ _ => 0) (fun a t x => gramEntry e (gramNoise D0 P D' a (Y t x))) := by
  have hcon := SourceSDE.isSDESolution_twoProjection μ hD0 hP hD.1 hξm hξc hY
  have h1 := ((GramChar.gramCharacteristics_of_constraint μ hD0 hP hD hY hcon).1).map_clm
    (gCLM e)
  have h2 : IsNativeItoProcess μ (fun t x => gramEntry e (gramPair P (Y t x)))
      (fun t x => gramDriftEntry D0 D' e (gramPair P (Y t x)))
      (fun a t x => gramEntry e (gramNoise D0 P D' a (Y t x))) := by
    convert h1 using 1 <;> rfl
  exact isNativeItoProcess_sub_drift h2

omit [DecidableEq c] [DecidableEq c'] in
/-- **The born compensated Gram coordinates.** -/
theorem isNativeItoProcess_bornGram {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    (hP : IsNearProjection P Naux) {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ} (hD : IsSignature D')
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c' ℂ}
    (hξm : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξc : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D' (ξ x))
    {Y : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c' ℂ}
    (hY : IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D') ξ Y)
    {θ : c → DriverSample S (SourceNoise ι) → ℝ≥0}
    {lam : c → DriverSample S (SourceNoise ι) → c' → ℂ}
    (hθ : ∀ y, Measurable[driverAugmented (κ := SourceNoise ι) μ 0] (θ y))
    (hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace] (lam y))
    (hsig : ∀ t ω, bornL θ lam t ω * D * (bornL θ lam t ω)ᴴ = D')
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hXp : IsStronglyProgressive (driverAugmented (κ := SourceNoise ι) μ) X)
    (hX : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, X t x = Y t x * bornL θ lam t x)
    (e : Fin 2 × c × c) :
    IsNativeItoProcess μ (bornRep θ lam (gramCompensated D0 D' (fun t x => gramPair P (Y t x))) e)
      (fun _ _ => 0) (fun a t x => gramEntry e (gramNoise D0 P D a (X t x))) := by
  obtain ⟨r, y, z⟩ := e
  have h1 := isNativeItoProcess_bInc hθ hlam (A := fun r x x' =>
      gramCompensated D0 D' (fun t x => gramPair P (Y t x)) (r, x, x'))
    (fun r x x' => isNativeItoProcess_gramComp hD0 hP hD hξm hξc hY (r, x, x')) r y z
  rw [← bornRep_eq_bInc] at h1
  refine isNativeItoProcess_congr_coeff h1 (θ := bTimes θ) (measurable_bTimes hθ)
    (fun _ => stronglyMeasurable_const)
    (fun a => fun T => ((GramUniqueness.continuous_gramEntry _).comp
      (GramUniqueness.GramChart.contDiff_gramNoise D0 P D a
        (k := 0)).continuous).comp_stronglyMeasurable (hXp T)) ?_
  filter_upwards [hX] with x hx t ht
  refine ⟨by simp only [mul_zero, ite_self, Finset.sum_const_zero], fun a => ?_⟩
  rw [hx t, gramNoise_mul D0 P (Y t x) (bornL θ lam t x) (hsig t x) a, gramEntry_congr]
  exact (ite_sum_eq_cf θ lam t x y z _ (ne_bTime (ne_of_ne_bTimes ht) 0 y z)).symm

end BlockBand.SourceProcess.ComplexCoupled
