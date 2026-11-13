module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepGram
public import BlockBand.SourceProcess.ContractingWords.LayerConsts
public import BlockBand.Transmission.FractionalBulk.LayerSample

/-!
# The closed conductance bound `ClosedCondLp` from the closed chain

* `cond_le_of_current` (deterministic): `g(nearSchur 𝕏) ≤ (Re Tr VᴴV)²/2` for a Hermitian `𝕏`
  with `currentOf 𝕏 = V𝖣Vᴴ`;
* **`closedCondLp_of_chain : B3ClosedChainPin → ClosedCondLp`**, with `C = max(R,0)²/2`
  for every `p`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ContractingWords (currentOf)
open BlockBand.SourceProcess.ClosedSummedProof (srcSignature_eq sigVals sigD abs_sigVals_le)
open BlockBand.Transmission.Bridge
open scoped ENNReal ComplexOrder

theorem measurable_conductance_comp {α : Type*} [MeasurableSpace α] (b E : ℝ) {W : ℕ}
    {X : α → Matrix (Fin W) (Fin W) ℂ} (hX : Measurable X) :
    Measurable fun a => conductanceOf (passiveTransmission b E (X a)) := by
  have hT : Measurable fun a => passiveTransmission b E (X a) :=
    (BlockBand.Transmission.FractionalBulk.measurable_passiveTransmission b E).comp hX
  unfold conductanceOf
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  exact Finset.measurable_sum _ fun i _ => Complex.measurable_re.comp hT.eval_matrix

theorem trace_re_gram_nonneg {ι c : Type*} [Fintype ι] [Fintype c]
    (V : Matrix ι c ℂ) : 0 ≤ (Vᴴ * V).trace.re :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self V).trace_nonneg).1

/-- **The conductance of a Hermitian two-port whose current is carried by a frame.** -/
theorem cond_le_of_current {b E κ : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    {W : ℕ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : XX.IsHermitian) {np K : ℕ}
    (V : Matrix (Fin 2 × Fin W) (SrcCol K (Fin np)) ℂ)
    (hJ : currentOf b E XX = V * srcSignature K (Fin np) * Vᴴ) :
    conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) ≤
      (Vᴴ * V).trace.re ^ 2 / 2 := by
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  rw [srcSignature_eq] at hJ
  have hn := BlockBand.SourceProcess.ClosedSummedProof.nuclearNorm_frameCurrent_le V
    (sigVals K (Fin np)) (abs_sigVals_le K _)
  have hD : (diagonal fun x => ((sigVals K (Fin np) x : ℝ) : ℂ)).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by ext x; simp)
  have hJh : (currentOf b E XX).IsHermitian := by
    rw [hJ]; exact isHermitian_mul_mul_conjTranspose V hD
  exact BlockBand.SourceProcess.ContractingWords.cond_le_K hXX hη rfl hJh (by rw [hJ]; exact hn)

/-- **`ClosedCondLp` from the closed chain**: `g_cl ≤ max(R, 0)²/2` on the alive set. -/
theorem closedCondLp_of_chain (hCh : B3ClosedChainPin) : ClosedCondLp := by
  intro b E np τ m T s h K Vs hFD R p hp
  obtain ⟨-, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  obtain ⟨Cch, -, hevC⟩ := hCh b E np τ m T s h K Vs hFD R
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  refine ⟨max R 0 ^ 2 / 2, by positivity, ?_⟩
  filter_upwards [hevC, hFD.2.2.2.2.2] with W hW hVW j hj
  obtain ⟨XX, -, -, hrel⟩ := hW j hj
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j (Vs W)
  have hfm : AEStronglyMeasurable (A.indicator fun y =>
      conductanceOf (passiveTransmission b E (b3ClosedX b E s h τ m W j y))) μ :=
    (measurable_conductance_comp b E (measurable_b3ClosedX b E s h τ m j)).aestronglyMeasurable
      |>.indicator₀ (nullMeasurableSet_b3Alive (by linarith) hE1 hE2 s h τ m R W j hV)
  refine (eLpNorm_le_of_ae_bound hfm (C := max R 0 ^ 2 / 2) ?_).trans (le_of_eq ?_)
  · filter_upwards [hrel] with y hy
    by_cases hyA : y ∈ A
    · rw [Set.indicator_of_mem hyA]
      obtain ⟨hH, hN, -, hJ, -⟩ := hy hyA
      have hc := cond_le_of_current hb hκ hE hH _ hJ
      rw [hN] at hc
      have hg0 : 0 ≤ conductanceOf (passiveTransmission b E (b3ClosedX b E s h τ m W j y)) := by
        rw [← hN]
        exact BlockBand.SourceProcess.FullSourceCovariance.conductance_nonneg b E hη.le
          (BlockBand.SourceProcess.FullSource.nearSchur_passive hη hH)
      have htr0 := trace_re_gram_nonneg (b3ClosedFrameAt b E s h τ m W j (Vs W) y)
      have hR := hyA.2 j (by
        simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj
        exact hj.1.1) le_rfl
      have hR' : ((b3ClosedFrameAt b E s h τ m W j (Vs W) y)ᴴ *
          b3ClosedFrameAt b E s h τ m W j (Vs W) y).trace.re ≤ max R 0 :=
        hR.le.trans (le_max_left _ _)
      rw [Real.norm_of_nonneg hg0]
      refine hc.trans ?_
      have := pow_le_pow_left₀ htr0 hR' 2
      linarith
    · rw [Set.indicator_of_notMem hyA, norm_zero]
      positivity
  · rw [measure_univ, ENNReal.one_rpow, one_mul]

end BlockBand.SourceProcess.PhysApprox.B3
