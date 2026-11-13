module

public import BlockBand.SourceProcess.CoupledFrames.FrameSol

/-!
# The born frame is a born solution

`isBornSDESolution_bornFrame`: if `Y_{τ_k} a_k = w_k` a.s. for every shared birth and `w_k = 0`
when `τ_k = 0`, the born frame is a solution of the finite source equation with births, started at
`ξ_Y Lcur`, with jumps `frameBirthJump`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.Stochastic.SourceSDE

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {K R : ℕ} {π : Type*} [Fintype π] [DecidableEq π] {n : ℕ} (eπ : π ≃ Fin n)
  {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

/-- **The born frame is a born solution of the finite source equation.** -/
theorem isBornSDESolution_bornFrame {D0 : ℝ} {Naux : ℕ}
    {ξY : DriverSample S (SourceNoise (Amb K R)) → Matrix (Amb K R) (ExtCol K R) ℂ}
    {Y : ℝ≥0 → DriverSample S (SourceNoise (Amb K R)) → Matrix (Amb K R) (ExtCol K R) ℂ}
    (hY : IsSDESolution μ (sourceDrift D0 Naux (ambP K R))
      (sourceDiffusion D0 (ambP K R) (extSig K R)) ξY Y)
    {σ' : π → DriverSample S (SourceNoise (Amb K R)) → ℝ}
    (hσ : ∀ i, Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (σ' i))
    {pv : π → DriverSample S (SourceNoise (Amb K R)) → ExtCol K R → ℂ}
    (hpv : ∀ i, StronglyMeasurable[(isStoppingTime_of_meas0 (hσ i).real_toNNReal).measurableSpace]
      (pv i))
    {w : Fin n → DriverSample S (SourceNoise (Amb K R)) → Amb K R → ℂ}
    (hw : ∀ k, StronglyMeasurable[(isStoppingTime_of_meas0
      (hσ (eπ.symm k)).real_toNNReal).measurableSpace] (w k))
    (hgood : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ k,
      Y (bτ eπ σ' k x) x *ᵥ ba eπ pv k x = w k x)
    (h0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ k, bτ eπ σ' k x = 0 → w k x = 0) :
    IsBornSDESolution μ D0 Naux (ambP K R) (srcSignature K π) (fun x => ξY x * lcur K R π)
      (frameBirthJump (bτ eπ σ') (bcol eπ) w) (bornFrame eπ Y σ' pv w) := by
  have hθ0 : ∀ k, Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (bτ eπ σ' k) :=
    fun k => (hσ _).real_toNNReal
  have hτ := fun k => isStoppingTime_of_meas0 (hθ0 k)
  have hN := isNativeItoProcess_frameN hY.1 (lcur K R π) hτ (bcol eπ) (a := ba eπ pv)
    (fun k => hpv (eπ.symm k))
  have hJ := isStronglyProgressive_frameBirthJump hθ0 hτ (bcol (K := K) eπ) hw
  have hXp : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ)
      (bornFrame eπ Y σ' pv w) := hN.progressive.add hJ
  have e : (fun t x => bornFrame eπ Y σ' pv w t x - frameBirthJump (bτ eπ σ') (bcol eπ) w t x) =
      frameN Y (lcur K R π) (bτ eπ σ') (bcol eπ) (ba eπ pv) := by
    funext t x; simp only [bornFrame, add_sub_cancel_right]
  have hsw : ∀ {G : Type} [Zero G] (f : ℝ≥0 → DriverSample S (SourceNoise (Amb K R)) → G) t x,
      switchOff (fun _ => ⊤) f t x = f t x := fun f t x => ite_eq_left le_top
  refine ⟨?_, ?_⟩
  · rw [e]
    refine isNativeItoProcess_congr_coeff hN (θ := fun k x => ((bτ eπ σ' k x : ℝ≥0) : WithTop ℝ≥0))
      (fun k => WithTop.measurable_coe.comp ((hθ0 k).mono ((driverAugmented _).le 0) le_rfl))
      (fun i => ((contDiff_sourceDrift D0 Naux (ambP K R) (k := 0)).continuous).comp_stronglyMeasurable
        (hXp i))
      (fun a i => ((contDiff_sourceDiffusion D0 (ambP K R) (srcSignature K π) a
        (k := 0)).continuous).comp_stronglyMeasurable (hXp i)) ?_
    filter_upwards [hgood] with x hx t ht
    rw [bornFrame_eq eπ Y σ' pv w hx t]
    refine ⟨?_, fun a => ?_⟩
    · rw [sourceDrift_mul, mul_bornL_lt eπ _ σ' pv t x ht]
      unfold frameNc
      rw [frameNc_eq', hsw]
    · rw [sourceDiffusion_mul D0 _ _ _ _ _ (bornL_sig_probe t x) a,
        mul_bornL_lt eπ _ σ' pv t x ht]
      unfold frameNc
      rw [frameNc_eq', hsw]
  · filter_upwards [hY.2, h0] with x hx hz
    unfold bornFrame frameN
    rw [frameN_eq', frameBirthJump_eq]
    have h1 : ∀ k, stoppedProcess Y (fun x => ((bτ eπ σ' k x : ℝ≥0) : WithTop ℝ≥0)) 0 x = Y 0 x :=
      fun k => stoppedProcess_eq_of_le (WithTop.coe_le_coe.2 zero_le)
    have h3 : ∀ k, birthMat (bcol (K := K) eπ k) (0 : Amb K R → ℂ) = 0 := fun k => by
      rw [← birthCLM_apply, map_zero]
    have h2 : ∀ k, (if bτ eπ σ' k x ≤ 0 then birthMat (bcol (K := K) eπ k) (w k x) else 0) = 0 := by
      intro k
      split_ifs with h
      · rw [hz k (le_antisymm h zero_le), h3]
      · rfl
    simp only [h1, sub_self, zero_mulVec, h3, h2, Finset.sum_const_zero, add_zero]
    rw [hx]

end BlockBand.SourceProcess.CoupledFrames
