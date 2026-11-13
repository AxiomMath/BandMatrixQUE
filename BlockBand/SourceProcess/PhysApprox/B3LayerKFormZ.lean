module

public import BlockBand.SourceProcess.PhysApprox.B3LayerKForm
public import BlockBand.SourceProcess.PhysApprox.B3LayerKSepZ

/-!
# The closed layer form `B3ClosedContrLayerForm`

`b3ClosedContrLayerForm_of_cayleyZ` proves `B3ClosedContrLayerForm` from the phase-padded Cayley
chain and its separators, as in `b3ClosedContrLayerForm_of_cayley` with the phase-`z` padding;
with `b3PadTransportZ_holds` and `b3PadGrowthZ_holds` this gives
`b3ClosedContrLayerForm_holds` under `GaussianAbsorptionContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.ContractingWords
open BlockBand.SourceProcess.ClosedLimit
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.PhysApprox.B3LayerMean (b3ChainXXz)
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W np K : ℕ}

/-- **`B3ClosedContrLayerForm` from the phase-padded Cayley chain and its separators.** -/
theorem b3ClosedContrLayerForm_of_cayleyZ (hGA : GaussianAbsorptionContract)
    (hC : B3LayerMean.B3CayleyChainZ) (hS : B3LayerMean.B3CayleySepZ) :
    B3DecayIn.B3ClosedContrLayerForm := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hF.1
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  have hη : 0 < etaZ b E :=
    BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  obtain ⟨C₄, W₀, hC₄, hfp⟩ := ClosedSummedProof.fresh_pow_bound hGA hb0 hb hκ
  refine ⟨2 * max R 0, 0, by positivity, le_rfl, ?_⟩
  filter_upwards [hC b E np τ m T s h K Vs hF R, hS b E np τ m T s h K Vs hF R,
    hF.2.2.2.2.2, eventually_ge_atTop (max W₀ 1)] with W hCW hSW hVW hWW j hj σ k l
  obtain ⟨hW0, hW⟩ := max_le_iff.1 hWW
  have hsj : closeLen s W ≤ j := (Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1
  have hVs : Measurable[growthSigma W (closeLen s W)] (Vs W) := hVW.1
  have hmV : Measurable (Vs W) :=
    hVs.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ ω, Vs W (extPast W j (pastCoords W j ω)) = Vs W ω :=
    fun ω => growth_fun_extPast hsj hVs ω
  obtain ⟨hXm, hXinv, hXae⟩ := hCW j hj
  have hAlm : MeasurableSet (b3AliveM (np := np) b E s h τ m R W j (Vs W)) :=
    measurableSet_b3AliveM b E s h τ m R W j hmV
  have hAlinv : ∀ y, b3Ext W j y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W) ↔
      y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W) :=
    mem_b3AliveM_b3Ext b E s h τ m R hsj le_rfl hVinv
  have hVmeas := measurable_b3ClosedFrameAt b E s h τ m W j hmV (np := np)
  have hVinv' : ∀ y, b3ClosedFrameAt b E s h τ m W j (Vs W) (b3Ext W j y) =
      b3ClosedFrameAt b E s h τ m W j (Vs W) y :=
    fun y => b3ClosedFrameAt_b3Ext b E s h τ m hsj le_rfl hVinv y
  have hcol : ∀ c : SrcCol K (Fin np), Measurable fun y : ProbedPath W np × ℝ =>
      fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x c :=
    fun c => Measurable.of_eval fun x => hVmeas.eval_matrix
  have hXXm : Measurable fun y : ProbedPath W np × ℝ => hermPart (b3ChainXXz b E s h W j y) := by
    have : Measurable fun y : ProbedPath W np × ℝ =>
        b3ChainXXz b E s h W j y + (b3ChainXXz b E s h W j y)ᴴ :=
      ClosingAux.measurable_matrix_add hXm (measurable_matrix_conjTranspose' hXm)
    exact ClosingAux.measurable_matrix_cmul measurable_const this
  refine ⟨2, 0, fun y : ProbedPath W np × ℝ => hermPart (b3ChainXXz b E s h W j y),
    (b3AliveM (np := np) b E s h τ m R W j (Vs W)).indicator (fun y =>
      kLetters (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x l)
        (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x k)),
    fun _ => 0, fun t => [[(TraceLetter.tag t, contrSepOf σ)]], ![1, Complex.I],
    hXXm, ?_, ?_, ?_, fun y => hermPart_isHermitian _, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_,
    ?_, ?_⟩
  · -- measurability of the letters
    intro ℓ
    have e : (fun y => (b3AliveM (np := np) b E s h τ m R W j (Vs W)).indicator (fun y =>
        kLetters (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x l)
          (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x k)) y ℓ) =
        (b3AliveM (np := np) b E s h τ m R W j (Vs W)).indicator (fun y =>
          kLetters (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x l)
            (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x k) ℓ) := by
      funext y
      by_cases hy : y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W) <;> simp [hy]
    rw [e]
    exact (measurable_kLetters (hcol l) (hcol k) ℓ).indicator hAlm
  · intro y
    simp only [hXinv]
  · intro y
    by_cases hy : y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((hAlinv y).2 hy), hVinv']
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (fun h' => hy ((hAlinv y).1 h'))]
  · intro y ℓ
    by_cases hy : y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W)
    · rw [Set.indicator_of_mem hy]; exact kLetters_isHermitian _ _ ℓ
    · rw [Set.indicator_of_notMem hy]; exact isHermitian_zero
  · intro y ℓ
    by_cases hy : y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W)
    · rw [Set.indicator_of_mem hy]
      have htr : ((b3ClosedFrameAt b E s h τ m W j (Vs W) y)ᴴ *
          b3ClosedFrameAt b E s h τ m W j (Vs W) y).trace.re < R := hy.2 j hsj le_rfl
      have h1 := ClosedSummedProof.sum_col_sq_le (b3ClosedFrameAt b E s h τ m W j (Vs W) y) l
      have h2 := ClosedSummedProof.sum_col_sq_le (b3ClosedFrameAt b E s h τ m W j (Vs W) y) k
      refine (kLetters_nuc _ _ ℓ).trans ?_
      have : R ≤ max R 0 := le_max_left _ _
      linarith
    · rw [Set.indicator_of_notMem hy, Pi.zero_apply, nuclearNorm_of_posSemidef PosSemidef.zero,
        trace_zero, Complex.zero_re]
      positivity
  · intro ℓ; simp
  · intro t; simp [IsAdmittedProduct]
  · intro t; simp [productDegree]
  · fin_cases σ <;> decide
  · intro t; fin_cases t <;> simp
  · -- integrability of `1_{A_j}Q_{j+1}`
    set μ := closedLaw b W np
    have hfm := aestronglyMeasurable_contr (b := b) (by linarith) hE1 hE2 s h τ m R W j hmV
      (j + 1) σ k l
    set g : ProbedPath W np × ℝ → ℝ := fun y => Real.sqrt R ^ 2 *
      (1 + ‖freshTransport b E (hermPart (b3ChainXXz b E s h W j y)) (freshSample W j y.1.1)‖ ^ 4)
      with hg
    have hgi : Integrable (fun y => ‖((g y : ℝ) : ℂ)‖) μ := by
      set Ψ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort →
          ℂ := fun z => ((Real.sqrt R ^ 2 * (1 + ‖freshTransport b E
            (hermPart (b3ChainXXz b E s h W j (b3Rebuild W j z.1))) z.2‖ ^ 4) : ℝ) : ℂ)
      have hR' : Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
          LayerSample W .oneBlockOnePort => b3Rebuild W j z.1 :=
        (measurable_b3Rebuild W j).comp measurable_fst
      have hΨm : Measurable Ψ :=
        Complex.measurable_ofReal.comp (measurable_const.mul (measurable_const.add
          ((FullSource.measurable_freshTransport_comp b E (hXXm.comp hR')
            measurable_snd).norm.pow_const 4)))
      have hcomp : (fun y => Ψ (b3Past W j y, freshSample W j y.1.1)) =
          fun y => ((g y : ℝ) : ℂ) := by
        funext y
        simp only [Ψ, g, b3Rebuild_b3Past, hXinv]
      have hB : ∀ x, ∫⁻ f, ‖Ψ (x, f)‖ₑ ∂freshLaw W b ≤
          ENNReal.ofReal (Real.sqrt R ^ 2 * (1 + C₄)) := by
        intro x
        set X0 := hermPart (b3ChainXXz b E s h W j (b3Rebuild W j x))
        obtain ⟨hN1, hN2⟩ := hfp W hW0 E hEκ X0 (hermPart_isHermitian _)
        have hpt : ∀ f, ‖Ψ (x, f)‖ₑ =
            ENNReal.ofReal (Real.sqrt R ^ 2 * (1 + ‖freshTransport b E X0 f‖ ^ 4)) := by
          intro f
          rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hInt : Integrable (fun f => Real.sqrt R ^ 2 * (1 + ‖freshTransport b E X0 f‖ ^ 4))
            (freshLaw W b) := ((integrable_const (1 : ℝ)).add hN2).const_mul _
        rw [lintegral_congr hpt, ← ofReal_integral_eq_lintegral_ofReal hInt
          (Eventually.of_forall fun f => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, integral_add (integrable_const _) hN2, integral_const,
          probReal_univ, one_smul]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have := integrable_b3_of_fresh b j hΨm _ hB
      rw [hcomp] at this
      exact this.norm
    refine hgi.mono' hfm ?_
    filter_upwards [hXae, hSW j hj, ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW] with y hch
      hsep hgood
    by_cases hA : y ∈ b3Alive b E s h τ m R W j (Vs W)
    swap
    · rw [Set.indicator_of_notMem hA, norm_zero]; exact norm_nonneg _
    rw [Set.indicator_of_mem hA]
    obtain ⟨hH, -, hTr, -, -⟩ := hch hA
    obtain ⟨-, hgrow, hs1⟩ := hsep hA
    rw [hgrow] at hs1
    set V := b3ClosedFrameAt b E s h τ m W j (Vs W) y
    set N := freshTransport b E (b3ChainXXz b E s h W j y) (freshSample W j y.1.1)
    set M := transportedSep b E (b3ChainXXz b E s h W j y) (contrSepOf σ) (freshSample W j y.1.1)
    have hQ : b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l y =
        bilinear (fun x => V x k) M (fun x => V x l) := by
      rw [b3ContrCoord_succ_eq b E s h τ m j (Vs W) σ k l y _ hs1 hTr,
        ClosedSummedProof.trace_col, entry_eq_dot]
      rfl
    have hSep : ‖sepOf b E (freshTwoPortSchur E (b3ChainXXz b E s h W j y)
        (freshSample W j y.1.1)) (contrSepOf σ)‖ ≤ 1 :=
      norm_sepOf_le b E (freshTwoPortSchur_isHermitian E hH (hgood.1 j)) hη _
    have hM : ‖M‖ ≤ ‖N‖ ^ 2 := norm_transportedSep_le hSep
    have htr : (Vᴴ * V).trace.re < R := hA.2 j hsj le_rfl
    have hvk : vecNorm (fun x => V x k) ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt ((col_sq_le_trace V k).trans htr.le)
    have hvl : vecNorm (fun x => V x l) ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt ((col_sq_le_trace V l).trans htr.le)
    have hgy : ‖((g y : ℝ) : ℂ)‖ = Real.sqrt R ^ 2 * (1 + ‖N‖ ^ 4) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), hg]
      simp only [hermPart_of_isHermitian hH, N]
    rw [hQ, hgy]
    have hX : ‖N‖ ^ 2 ≤ 1 + ‖N‖ ^ 4 := by nlinarith [sq_nonneg (‖N‖ ^ 2 - 1)]
    have h0 := Transmission.PassiveCovariance.vecNorm_nonneg (fun x => V x k)
    have h0' := Transmission.PassiveCovariance.vecNorm_nonneg (fun x => V x l)
    calc ‖bilinear (fun x => V x k) M (fun x => V x l)‖ ≤
          vecNorm (fun x => V x k) * ‖M‖ * vecNorm (fun x => V x l) :=
          Transmission.PassiveCovariance.norm_bilinear_le _ _ _
      _ ≤ Real.sqrt R * ‖N‖ ^ 2 * Real.sqrt R :=
          mul_le_mul (mul_le_mul hvk hM (norm_nonneg _) (Real.sqrt_nonneg _)) hvl h0'
            (by positivity)
      _ = Real.sqrt R ^ 2 * ‖N‖ ^ 2 := by ring
      _ ≤ Real.sqrt R ^ 2 * (1 + ‖N‖ ^ 4) := mul_le_mul_of_nonneg_left hX (by positivity)
  · -- the a.e. layer form
    filter_upwards [hXae, hSW j hj, b3Alive_ae_eq (by linarith) hE1 hE2 s h τ m R W j (Vs W)]
      with y hch hsep hyA hA
    have hyAl : y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W) := (Iff.of_eq hyA).mp hA
    obtain ⟨hH, hNS, hTr, -, -⟩ := hch hA
    obtain ⟨hs0, hgrow, hs1⟩ := hsep hA
    rw [hgrow] at hs1
    have hXX := hermPart_of_isHermitian hH
    refine ⟨by rw [hXX]; exact hNS, ?_, ?_⟩
    · rw [b3ContrCoord_succ_eq b E s h τ m j (Vs W) σ k l y _ hs1 hTr]
      simp only [b3LayerVal_single, Set.indicator_of_mem hyAl, hXX]
      rw [sum_wt_kLetters]
    · rw [b3ContrCoord_eq_sep b E s h τ m j (Vs W) σ k l y _ hs0]
      simp only [coreProd_single, Set.indicator_of_mem hyAl, hXX]
      rw [sum_wt_kLetters]

/-- **`B3ClosedContrLayerForm` holds** (from `GaussianAbsorptionContract` alone). -/
theorem b3ClosedContrLayerForm_holds (hGA : GaussianAbsorptionContract) :
    B3DecayIn.B3ClosedContrLayerForm :=
  b3ClosedContrLayerForm_of_cayleyZ hGA (B3LayerMean.b3CayleyChainZ_holds b3PadTransportZ_holds)
    (B3LayerMean.b3CayleySepZ_holds b3PadGrowthZ_holds)

end BlockBand.SourceProcess.PhysApprox.B3
