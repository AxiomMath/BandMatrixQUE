module

public import BlockBand.SourceProcess.CutoffLimit.Estimate
public import BlockBand.SourceProcess.CutoffLimit.Moment

/-!
# The coupled comparison with explicit parameters

`IsCutoffCoupling.abs_sub_le_four`: with the trace level, distance level and tail mass of the
cutoff chosen in terms of `ε`, the birth mass and the moment bound, two coupled finite source model
values differ by at most `4ε`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourcePins
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal

/-- The total birth mass `B = Σ_{a,k} d_* m_a / M` of the model. -/
def birthMass (b s T : ℝ) {p : ℕ} (q : Fin p → ℝ → ℝ) (M : ℕ) : ℝ :=
  ∑ i : Fin p × Fin M, dStar b * sourceMass s T (q i.1) / M

/-- `8Γ + 2B`. -/
def momentBound (ent : Measure (Measure unitInterval)) (b s T : ℝ) {p : ℕ}
    (q : Fin p → ℝ → ℝ) (M : ℕ) : ℝ≥0∞ :=
  8 * (∫⁻ ν, ∫⁻ y, psiP (1 / 2) y ∂ν ∂ent) + ENNReal.ofReal (2 * birthMass b s T q M)

/-- `E_ent ∫ψ_{1/2}1_{y ≤ h²}`. -/
def tailMass (ent : Measure (Measure unitInterval)) (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ ν, ∫⁻ y, tailPsi h y ∂ν ∂ent

variable {b E s T : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ} {h₁ h₂ : ℝ} {K M : ℕ}
  {ent : Measure (Measure unitInterval)} {ι S : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {Naux : ℕ} {P : Matrix ι ι ℂ}
  {Emb : Matrix ι (Fin K × Fin 2) ℂ}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DriverSample S (SourceNoise ι)))}
  {tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ}
  {σb : DriverSample S (SourceNoise ι) → Fin p × Fin M → ℝ} {nb : ℕ}
  {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → SrcCol K (Fin p × Fin M)}
  {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ} {β : Fin nb → ℝ}
  {X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι (SrcCol K (Fin p × Fin M)) ℂ}

/-- **The coupled values differ by at most `4ε`.** -/
theorem IsCutoffCoupling.abs_sub_le_four
    (hC : IsCutoffCoupling b E s T q h₁ h₂ K M ent μ Naux P Emb 𝓖 tseq σb τ col w β X₁ X₂)
    (hb0 : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) (h0 : 0 ≤ h₁) (h12 : h₁ ≤ h₂)
    {J : ℕ} {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) {ε L u lev δ : ℝ} (hε : 0 < ε)
    (hL : 0 < L) (hu : 0 < u) (hlev : 0 < lev)
    (hδ : ∀ A B : Matrix (Fin p × Fin M) (Fin p × Fin M) ℂ, A ∈ psdBox _ L → B ∈ psdBox _ L →
      (∀ i j, ‖A i j - B i j‖ < δ) →
        |probeVal (fun j (i : Fin p × Fin M) => a j i.1) A -
          probeVal (fun j (i : Fin p × Fin M) => a j i.1) B| < ε)
    (huL : 2 * (Real.sqrt u * Real.sqrt L) < δ)
    (hAL : momentBound ent b s T q M / ENNReal.ofReal L ≤ ENNReal.ofReal ε)
    (hAlev : momentBound ent b s T q M / ENNReal.ofReal lev ≤ ENNReal.ofReal ε)
    (htail : ENNReal.ofReal (Real.exp (transportD0 b E * lev ^ 2 * ((T - s).toNNReal : ℝ) / 2)) *
      (4 * tailMass ent h₂) / ENNReal.ofReal u ≤ ENNReal.ofReal ε)
    {v₁ v₂ : ℝ} (hv₁ : FiniteSourceModelValue b E s T q h₁ K M ent a v₁)
    (hv₂ : FiniteSourceModelValue b E s T q h₂ K M ent a v₂) :
    |v₁ - v₂| ≤ 4 * ε := by
  have H := hC.abs_sub_le ha hε hδ huL hv₁ hv₂
  have T1 := hC.meas_trace_le hb0 hE1 hE2 (T - s).toNNReal hL
  have T2 := hC.meas_dist_le hb0 hE1 hE2 (T - s).toNNReal hlev hu
  have I0 : initTrace μ Emb tseq p M h₁ h₂ + ENNReal.ofReal (2 * ∑ k, β k) ≤
      momentBound ent b s T q M := by
    rw [hC.birth_total, momentBound, birthMass]
    exact add_le_add hC.initTrace_le le_rfl
  have I2 := hC.initDist_le h0 h12
  have k1 := T1.trans ((ENNReal.div_le_div_right I0 _).trans hAL)
  have k2 : ENNReal.ofReal (Real.exp (transportD0 b E * lev ^ 2 * ((T - s).toNNReal : ℝ) / 2)) *
      initDist μ Emb tseq p M h₁ h₂ / ENNReal.ofReal u ≤ ENNReal.ofReal ε := by
    refine le_trans ?_ htail
    rw [tailMass]
    gcongr
  have k3 := T2.trans (add_le_add ((ENNReal.div_le_div_right I0 _).trans hAlev) k2)
  have hsum := H.trans (add_le_add le_rfl (add_le_add k1 k3))
  have h4 : ENNReal.ofReal ε + (ENNReal.ofReal ε + (ENNReal.ofReal ε + ENNReal.ofReal ε)) =
      ENNReal.ofReal (4 * ε) := by
    rw [← ENNReal.ofReal_add hε.le hε.le, ← ENNReal.ofReal_add hε.le (by linarith),
      ← ENNReal.ofReal_add hε.le (by linarith)]
    congr 1
    ring
  rw [h4] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hsum

end BlockBand.SourceProcess.CutoffLimit
