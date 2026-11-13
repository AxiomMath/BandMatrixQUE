module

public import BlockBand.SourceProcess.LengthCont.OneLayer.IncrPast
public import BlockBand.SourceProcess.LengthCont.OneLayer.CondExp
public import BlockBand.SourceProcess.ComplexSourceLaw.Measurability

/-!
# One length: the drift and the martingale difference bounded by past integrals

At a fixed width `W ≥ 1` and length `n ≥ 1` with all
probes born, given the one-layer `Δ` bounds at every passive input with constants `Cm, Cf`
(`DeltaFresh`, the form of `RawTag.delta_fresh_bounds` at `p = 4`) and an integrable increment:

* `∫ |E[incr | 𝓕_n]| ≤ c₁` whenever `∫⁻ ofReal(|μ_{ik}| α(x)) ≤ ofReal c₁`;
* `∫ mart² ≤ c₂` whenever `∫⁻ ofReal((|μ_{ik}| σ(x))²) ≤ ofReal c₂`,
where `α = K(m₀ + t²)N²H`, `σ = K(s₀ + t²)N²H` (`alphaFun`, `sigmaFun`) are the fresh sizes of
`incTerm_size` with `m₀ = Cm(δ₀ + W⁻¹)`, `s₀ = Cf(W^{-1/2} + δ₀)`, `δ₀ = jetDistance0` at the
length-`n` state, `N = ‖f_i‖ + ‖f_k‖` (unit frames), `H = 1 + hsA ℝ + hsB ℝ`
(`window_step`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.RawTag BlockBand.SourceProcess.ComplexSourceLaw
open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- The one-layer `Δ` bounds at width `W`, exponent `4`, every passive input. -/
def DeltaFresh (b E : ℝ) (W : ℕ) (Cm Cf : ℝ) : Prop :=
  ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
    (∀ x y, Integrable (fun ω => freshDelta b E X ω x y) (freshLaw W b)) ∧
    ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤ Cm * (jetDistance0 b E X + (W : ℝ)⁻¹) ∧
    ∀ u v : Fin W → ℂ,
      eLpNorm (fun ω => bilinear u (freshDelta b E X ω -
          matrixExpect (freshLaw W b) (freshDelta b E X)) v) (ENNReal.ofReal 4) (freshLaw W b) ≤
        ENNReal.ofReal (Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E X) * vecNorm u * vecNorm v)

/-- `K = 4 + 2‖(z̄ - z)⁻¹‖`. -/
def sizeK (b E : ℝ) : ℝ := 4 + 2 * ‖(conj (boundaryZ b E) - boundaryZ b E)⁻¹‖

/-- `m₀ = Cm(δ₀ + W⁻¹)` at the length-`n` state. -/
def mFun (b E : ℝ) (W n : ℕ) (Cm : ℝ) (ω : GrowthPath W) : ℝ :=
  Cm * (jetDistance0 b E (pathX b E W n ω) + (W : ℝ)⁻¹)

/-- `s₀ = Cf(W^{-1/2} + δ₀)`. -/
def sFun (b E : ℝ) (W n : ℕ) (Cf : ℝ) (ω : GrowthPath W) : ℝ :=
  Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E (pathX b E W n ω))

/-- `N = ‖f_i‖ + ‖f_k‖`. -/
def nFun {np : ℕ} (b E : ℝ) (W n : ℕ) (τ : Fin np → ℝ) (i k : Fin np) (ω : GrowthPath W)
    (g : Fin np → Fin W → ℂ) : ℝ :=
  vecNorm (frame b E W n (birth W τ i) ω (g i)) + vecNorm (frame b E W n (birth W τ k) ω (g k))

/-- `H = 1 + hsA ℝ + hsB ℝ`. -/
def hFun (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) : ℝ :=
  1 + hsA (boundaryResolvent b E W n ω) + hsB (boundaryResolvent b E W n ω)

/-- The fresh mean size `α`. -/
def alphaFun {np : ℕ} (b E : ℝ) (W n : ℕ) (τ : Fin np → ℝ) (i k : Fin np) (Cm Cf : ℝ)
    (ω : GrowthPath W) (g : Fin np → Fin W → ℂ) : ℝ :=
  sizeK b E * (mFun b E W n Cm ω + (mFun b E W n Cm ω + sFun b E W n Cf ω) ^ 2) *
    nFun b E W n τ i k ω g ^ 2 * hFun b E W n ω

/-- The fresh centred size `σ`. -/
def sigmaFun {np : ℕ} (b E : ℝ) (W n : ℕ) (τ : Fin np → ℝ) (i k : Fin np) (Cm Cf : ℝ)
    (ω : GrowthPath W) (g : Fin np → Fin W → ℂ) : ℝ :=
  sizeK b E * (sFun b E W n Cf ω + (mFun b E W n Cm ω + sFun b E W n Cf ω) ^ 2) *
    nFun b E W n τ i k ω g ^ 2 * hFun b E W n ω

theorem lintegral_sq_le_of_eLpNorm {F : Type*} [MeasurableSpace F] {ρ : Measure F}
    {f : F → ℂ} (hf : AEStronglyMeasurable f ρ) {σ : ℝ} (hσ : 0 ≤ σ)
    (h : eLpNorm f 2 ρ ≤ ENNReal.ofReal σ) :
    ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂ρ ≤ ENNReal.ofReal (σ ^ 2) := by
  have e := eLpNorm_nnreal_pow_eq_lintegral (μ := ρ) (p := 2) two_ne_zero hf
  have h2 : ((2 : NNReal) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [ENNReal.coe_ofNat, h2, ENNReal.rpow_natCast] at e
  have e2 : ∀ y, ENNReal.ofReal (‖f y‖ ^ 2) = ‖f y‖ₑ ^ 2 := fun y => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [e2]
  rw [← e, ENNReal.ofReal_pow hσ]
  exact pow_le_pow_left' h 2

/-- **The fresh bounds at a Hermitian past.** -/
theorem fresh_at_past {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ} (n : ℕ)
    {np : ℕ} (τ m : Fin np → ℝ) (r : Fin 4) (i k : Fin np) (s : Bool) {Cm Cf : ℝ}
    (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf) (hdf : DeltaFresh b E W Cm Cf)
    {q : PastSample W n} (hq : q ∈ hermPast W n) (g : Fin np → Fin W → ℂ) :
    |freshAvg (freshLaw W b) (incPast b E W n τ m r i k s) (q, g)| ≤
        ‖massF m i k‖ * alphaFun b E W n τ i k Cm Cf (extendPast q) g ∧
      ∫⁻ y, ENNReal.ofReal ((incPast b E W n τ m r i k s ((q, g), y) -
          freshAvg (freshLaw W b) (incPast b E W n τ m r i k s) (q, g)) ^ 2) ∂freshLaw W b ≤
        ENNReal.ofReal ((‖massF m i k‖ * sigmaFun b E W n τ i k Cm Cf (extendPast q) g) ^ 2) := by
  set ω := extendPast q
  set X := pathX b E W n ω
  have hY : (passiveY X).PosSemidef := passiveY_pathX_extendPast hb hE1 hE2 hq
  obtain ⟨hint, hmean, hdev⟩ := hdf X hY
  have hδ : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hD : DeltaHyp (freshLaw W b) (freshDelta b E X) (mFun b E W n Cm ω) (sFun b E W n Cf ω) :=
    { meas := BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E measurable_const
        measurable_id
      int := hint
      m_nonneg := by unfold mFun; positivity
      s_nonneg := by unfold sFun; positivity
      mean := hmean
      dev := fun u v => by
        have h4 : ENNReal.ofReal 4 = 4 := by norm_num
        rw [← h4]; exact hdev u v }
  have hA := isHermitian_extendPast hq
  obtain ⟨a1, c1, d1, e1⟩ := vecNorm_parts_le b E n (birth W τ i) ω (g i) hA
  obtain ⟨a2, c2, d2, e2⟩ := vecNorm_parts_le b E n (birth W τ k) ω (g k) hA
  have hfi := vecNorm_nonneg (frame b E W n (birth W τ i) ω (g i))
  have hfk := vecNorm_nonneg (frame b E W n (birth W τ k) ω (g k))
  have hN : 0 ≤ nFun b E W n τ i k ω g := add_nonneg hfi hfk
  have hNi : vecNorm (frame b E W n (birth W τ i) ω (g i)) ≤ nFun b E W n τ i k ω g := by
    unfold nFun; linarith
  have hNk : vecNorm (frame b E W n (birth W τ k) ω (g k)) ≤ nFun b E W n τ i k ω g := by
    unfold nFun; linarith
  have FS := hD.incTerm_size b E (boundaryResolvent b E W n ω) _ _ _ _ _ _ _ _ hN
    (a1.trans hNi) (a2.trans hNk) (c1.trans hNi) (c2.trans hNk) (d1.trans hNi) (d2.trans hNk)
    (e1.trans hNi) (e2.trans hNk) r
  set Xf := fun y => incTerm b E r (freshDelta b E X y) (boundaryResolvent b E W n ω)
    (nearL b E W n (birth W τ i) ω (g i)) (nearL b E W n (birth W τ k) ω (g k))
    (nearR b E W n (birth W τ i) ω (g i)) (nearR b E W n (birth W τ k) ω (g k))
    (farL b E W n (birth W τ i) ω (g i)) (farL b E W n (birth W τ k) ω (g k))
    (farR b E W n (birth W τ i) ω (g i)) (farR b E W n (birth W τ k) ω (g k))
  have hDp : ∀ y, incPast b E W n τ m r i k s ((q, g), y) = part s (massF m i k * Xf y) :=
    fun y => rfl
  have havg : freshAvg (freshLaw W b) (incPast b E W n τ m r i k s) (q, g) =
      part s (massF m i k * ∫ y, Xf y ∂freshLaw W b) := by
    rw [freshAvg]
    simp only [hDp]
    rw [integral_part s (FS.int.const_mul _), integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [havg]
    refine (abs_part_le _ _).trans ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left FS.mean (norm_nonneg _)
  · have hpt : ∀ y, ENNReal.ofReal ((incPast b E W n τ m r i k s ((q, g), y) -
        freshAvg (freshLaw W b) (incPast b E W n τ m r i k s) (q, g)) ^ 2) ≤
        ENNReal.ofReal (‖massF m i k‖ ^ 2) *
          ENNReal.ofReal (‖Xf y - ∫ y', Xf y' ∂freshLaw W b‖ ^ 2) := by
      intro y
      rw [← ENNReal.ofReal_mul (by positivity), hDp, havg, ← part_sub, ← mul_sub]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← mul_pow, ← norm_mul, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_part_le _ _) 2
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right (lintegral_sq_le_of_eLpNorm
      (FS.meas.sub aestronglyMeasurable_const) FS.σ_nonneg FS.dev) _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [sigmaFun, sizeK, hFun]
    ring

theorem alphaFun_extendPast {np : ℕ} (b E : ℝ) (W n : ℕ) (τ : Fin np → ℝ) (i k : Fin np)
    (Cm Cf : ℝ) (ω : GrowthPath W) (g : Fin np → Fin W → ℂ) :
    alphaFun b E W n τ i k Cm Cf (pastExt W n ω) g = alphaFun b E W n τ i k Cm Cf ω g := by
  simp only [alphaFun, mFun, sFun, nFun, hFun, pathX_extendPast, frame_extendPast,
    boundaryResolvent_extendPast]

theorem sigmaFun_extendPast {np : ℕ} (b E : ℝ) (W n : ℕ) (τ : Fin np → ℝ) (i k : Fin np)
    (Cm Cf : ℝ) (ω : GrowthPath W) (g : Fin np → Fin W → ℂ) :
    sigmaFun b E W n τ i k Cm Cf (pastExt W n ω) g = sigmaFun b E W n τ i k Cm Cf ω g := by
  simp only [sigmaFun, mFun, sFun, nFun, hFun, pathX_extendPast, frame_extendPast,
    boundaryResolvent_extendPast]

/-- **One length**: drift and martingale difference bounded by the past integrals. -/
theorem window_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {W : ℕ} (hW : 1 ≤ W) {np : ℕ} (τ m : Fin np → ℝ) (hm : ∀ j, 0 ≤ m j) {n : ℕ}
    (hn : 1 ≤ n) (hβ : ∀ j, birth W τ j < n) {Cm Cf : ℝ} (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf)
    (hdf : DeltaFresh b E W Cm Cf) (r : Fin 4) (i k : Fin np) (s : Bool)
    (hint : Integrable (incr (sourceCoord b E W τ m r i k s) n) (probedPathLaw W np b))
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hD : ∫⁻ x, ENNReal.ofReal (‖massF m i k‖ * alphaFun b E W n τ i k Cm Cf x.1 x.2)
      ∂probedPathLaw W np b ≤ ENNReal.ofReal c₁)
    (hV : ∫⁻ x, ENNReal.ofReal ((‖massF m i k‖ * sigmaFun b E W n τ i k Cm Cf x.1 x.2) ^ 2)
      ∂probedPathLaw W np b ≤ ENNReal.ofReal c₂) :
    ∫ x, |(probedPathLaw W np b)[incr (sourceCoord b E W τ m r i k s) n |
        probedSigma W np n] x| ∂probedPathLaw W np b ≤ c₁ ∧
      ∫ x, mart (probedPathLaw W np b) (probedSigma W np) (sourceCoord b E W τ m r i k s) n x ^ 2
        ∂probedPathLaw W np b ≤ c₂ := by
  set ν := Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)
  set μ := probedPathLaw W np b
  set νP := (pastLaw W n b).prod ν
  set ρ := freshLaw W b
  have hνP : IsProbabilityMeasure νP := by
    rw [show νP = (pastLaw W n b).prod ν from rfl]; infer_instance
  have hsfν : SFinite ν := inferInstance
  have hsfP : SFinite (pastLaw W n b) := inferInstance
  have hsf : SFinite νP := inferInstance
  have hμP : IsProbabilityMeasure μ := by
    rw [show μ = (growthPathLaw W b).prod ν from rfl]; infer_instance
  set π : ProbedPath W np → PastSample W n × (Fin np → Fin W → ℂ) :=
    fun x => (pastCoords W n x.1, x.2)
  set φ : ProbedPath W np → LayerSample W .oneBlockOnePort := fun x => freshSample W n x.1
  have hπ : Measurable π := ((measurable_pastCoords W n).comp measurable_fst).prodMk measurable_snd
  have hφ : Measurable φ := (measurable_freshSample W n).comp measurable_fst
  have hlaw : μ.map (fun x => (π x, φ x)) = νP.prod ρ := map_past_tag_fresh W n b ν
  have hmapπ : μ.map π = νP := map_fst_of_law hπ hφ hlaw
  have hσ : probedSigma W np n = MeasurableSpace.comap π inferInstance := rfl
  set D := incPast b E W n τ m r i k s
  have hDm : StronglyMeasurable D := (measurable_incPast b E W n τ m r i k s).stronglyMeasurable
  have hae := ae_incr_eq_incPast hb0 hb hE1 hE2 hW τ m hm hn hβ r i k s
  have hDi : Integrable D (νP.prod ρ) := by
    have h1 : Integrable (fun x => D (π x, φ x)) μ := hint.congr hae
    rw [← hlaw]
    exact (integrable_map_measure hDm.aestronglyMeasurable (hπ.prodMk hφ).aemeasurable).mpr h1
  have hb1 : b < 1 := by linarith
  -- the Hermitian pasts
  have hpas : ∀ᵐ p ∂νP, p.1 ∈ hermPast W n :=
    (Measure.quasiMeasurePreserving_fst (μ := pastLaw W n b) (ν := ν)).ae
      (ae_pastLaw_hermitian W n b)
  have hce : μ[incr (sourceCoord b E W τ m r i k s) n | probedSigma W np n] =ᵐ[μ]
      μ[fun x => D (π x, φ x) | MeasurableSpace.comap π inferInstance] := by
    rw [hσ]; exact condExp_congr_ae hae
  refine ⟨?_, ?_⟩
  · rw [integral_congr_ae (hce.mono fun x h => by rw [h]),
      integral_abs_condExp hπ hφ hlaw hDm hDi]
    have hGm : StronglyMeasurable (freshAvg ρ D) := hDm.integral_prod_right'
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => abs_nonneg _)
      hGm.norm.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal hc₁ ?_
    calc ∫⁻ p, ENNReal.ofReal |freshAvg ρ D p| ∂νP
        ≤ ∫⁻ p, ENNReal.ofReal (‖massF m i k‖ * alphaFun b E W n τ i k Cm Cf
            (extendPast p.1) p.2) ∂νP := by
          refine lintegral_mono_ae (hpas.mono fun p hp => ENNReal.ofReal_le_ofReal ?_)
          exact (fresh_at_past hb1 hE1 hE2 n τ m r i k s hCm hCf hdf hp p.2).1
      _ ≤ ∫⁻ x, ENNReal.ofReal (‖massF m i k‖ * alphaFun b E W n τ i k Cm Cf
            (extendPast (π x).1) (π x).2) ∂μ := by
          rw [← hmapπ]; exact lintegral_map_le _ hπ.aemeasurable
      _ = ∫⁻ x, ENNReal.ofReal (‖massF m i k‖ * alphaFun b E W n τ i k Cm Cf x.1 x.2) ∂μ := by
          refine lintegral_congr fun x => ?_
          simp only [π]
          rw [show extendPast (pastCoords W n x.1) = pastExt W n x.1 from rfl, alphaFun_extendPast]
      _ ≤ ENNReal.ofReal c₁ := hD
  · have hmart : ∫ x, mart μ (probedSigma W np) (sourceCoord b E W τ m r i k s) n x ^ 2 ∂μ =
        ∫ x, (D (π x, φ x) - μ[fun x => D (π x, φ x) |
          MeasurableSpace.comap π inferInstance] x) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hae, hce] with x h1 h2
      simp only [mart]; rw [h1, h2]
    rw [hmart, integral_sub_condExp_sq hπ hφ hlaw hDm hDi]
    have hGm : StronglyMeasurable (freshAvg ρ D) := hDm.integral_prod_right'
    have hFm : Measurable fun q : (PastSample W n × (Fin np → Fin W → ℂ)) ×
        LayerSample W .oneBlockOnePort => (D q - freshAvg ρ D q.1) ^ 2 :=
      (hDm.measurable.sub (hGm.measurable.comp measurable_fst)).pow_const 2
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      hFm.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal hc₂ ?_
    rw [lintegral_prod _ hFm.ennreal_ofReal.aemeasurable]
    calc ∫⁻ p, ∫⁻ y, ENNReal.ofReal ((D (p, y) - freshAvg ρ D (p, y).1) ^ 2) ∂ρ ∂νP
        ≤ ∫⁻ p, ENNReal.ofReal ((‖massF m i k‖ * sigmaFun b E W n τ i k Cm Cf
            (extendPast p.1) p.2) ^ 2) ∂νP := by
          refine lintegral_mono_ae (hpas.mono fun p hp => ?_)
          exact (fresh_at_past hb1 hE1 hE2 n τ m r i k s hCm hCf hdf hp p.2).2
      _ ≤ ∫⁻ x, ENNReal.ofReal ((‖massF m i k‖ * sigmaFun b E W n τ i k Cm Cf
            (extendPast (π x).1) (π x).2) ^ 2) ∂μ := by
          rw [← hmapπ]; exact lintegral_map_le _ hπ.aemeasurable
      _ = ∫⁻ x, ENNReal.ofReal ((‖massF m i k‖ * sigmaFun b E W n τ i k Cm Cf x.1 x.2) ^ 2)
            ∂μ := by
          refine lintegral_congr fun x => ?_
          simp only [π]
          rw [show extendPast (pastCoords W n x.1) = pastExt W n x.1 from rfl, sigmaFun_extendPast]
      _ ≤ ENNReal.ofReal c₂ := hV

end BlockBand.SourceProcess.LengthCont.OneLayer
