module

public import BlockBand.SourceProcess.ClosedSummedProof.StepPrep

/-!
# The conditional increment at one closed step is a fresh-layer integral

**`condExp_step`**: let `Am = aliveM ∩ noBirth` at a step `j ≥ n_s` (the Borel version of the
event of `ClosedSummed`). If an integrand `g` equals, a.s. on `Am`, a fresh-layer functional
`Q(X j(cpast j), V_j, fresh j)` of a measurable Hermitian state `X j` and of the closed frame
`V_j`, and `Q` has a bounded fresh-layer `L¹` norm for `Re Tr VᴴV ≤ R`, then a.s. on `Am`,
`E[1_{Am} g | closedSigma j] = ∫ Q(X j(cpast j), V_j, f) dfresh(f)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedSumProof
open BlockBand.SourceProcess.ClosedPath BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {W p K M : ℕ}

/-- A closed past in `A'` is realized by a sample in `Am = cpast⁻¹ A'`. -/
theorem trace_framePast_le (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) {j : ℕ}
    (hj : closeLen s W ≤ j) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {A' : Set (ClosedPast W j p M)}
    (hA' : cpast j ⁻¹' A' = am b E s T h q R W Vs j) {x : ClosedPast W j p M} (hx : x ∈ A') :
    ((framePast b E s T h q W j Vs x)ᴴ * framePast b E s T h q W j Vs x).trace.re ≤ R := by
  set y₀ : SampledPath W p M × ℝ := ((extPast W j x.1, x.2.1), x.2.2)
  have hc : cpast j y₀ = x := by
    simp only [cpast, y₀, pastCoords_extPast]
  have hy : y₀ ∈ am b E s T h q R W Vs j := by rw [← hA', Set.mem_preimage, hc]; exact hx
  have hR := hy.1.2 j hj le_rfl
  rw [closedGramAt, closedFrameAt_eq_framePast b E s T h q hj hVs, hc] at hR
  exact hR.le

/-- **The conditional increment is a fresh-layer integral.** -/
theorem condExp_step (b E s T h : ℝ) {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (R : ℝ)
    {j : ℕ} (hj : closeLen s W ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs)
    {X : ClosedPast W j p M → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXh : ∀ x, (X x).IsHermitian)
    (Q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →
      Matrix (Fin 2 × Fin W) (SrcCol K (Fin p × Fin M)) ℂ → LayerSample W .oneBlockOnePort → ℂ)
    (hQm : Measurable fun z : ClosedPast W j p M × LayerSample W .oneBlockOnePort =>
      Q (X z.1) (framePast b E s T h q W j Vs z.1) z.2)
    (B : ℝ) (hB : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ V : Matrix (Fin 2 × Fin W) (SrcCol K (Fin p × Fin M)) ℂ, (Vᴴ * V).trace.re ≤ R →
        ∫⁻ f, ‖Q XX V f‖ₑ ∂freshLaw W b ≤ ENNReal.ofReal B)
    (g : SampledPath W p M × ℝ → ℂ)
    (hg : ∀ᵐ y ∂lawW b T q M W, y ∈ am b E s T h q R W Vs j →
      g y = Q (X (cpast j y)) (closedFrameAt b E s T h q W j Vs y) (freshSample W j y.1.1)) :
    ∀ᵐ y ∂lawW b T q M W, y ∈ am b E s T h q R W Vs j →
      (lawW b T q M W)[(am b E s T h q R W Vs j).indicator g | closedSigma W j p M] y =
        ∫ f, Q (X (cpast j y)) (closedFrameAt b E s T h q W j Vs y) f ∂freshLaw W b := by
  set μ := lawW b T q M W
  set Am := am b E s T h q R W Vs j
  set Fr := framePast b E s T h q W j Vs (p := p) (M := M)
  have hAm : MeasurableSet[closedSigma W j p M] Am :=
    (measurableSet_aliveM b E s T h q R hj hVs).inter (measurableSet_noBirth j)
  obtain ⟨A', hA'm, hA'⟩ := hAm
  set Ψ : ClosedPast W j p M × LayerSample W .oneBlockOnePort → ℂ :=
    (A' ×ˢ Set.univ).indicator fun z => Q (X z.1) (Fr z.1) z.2
  have hΨm : Measurable Ψ := hQm.indicator (hA'm.prod MeasurableSet.univ)
  have hΨ1 : ∀ x f, x ∈ A' → Ψ (x, f) = Q (X x) (Fr x) f := fun x f hx =>
    Set.indicator_of_mem (Set.mk_mem_prod hx (Set.mem_univ f)) _
  have hΨ0 : ∀ x f, x ∉ A' → Ψ (x, f) = 0 := fun x f hx =>
    Set.indicator_of_notMem (fun h => hx (Set.mem_prod.mp h).1) _
  have hfr : ∀ y, closedFrameAt b E s T h q W j Vs y = Fr (cpast j y) :=
    closedFrameAt_eq_framePast b E s T h q hj hVs
  have heq : Am.indicator g =ᵐ[μ] fun y => Ψ (cpast j y, freshSample W j y.1.1) := by
    filter_upwards [hg] with y hy
    by_cases hyA : y ∈ Am
    · have hx : cpast j y ∈ A' := by rw [← hA'] at hyA; exact hyA
      rw [Set.indicator_of_mem hyA, hy hyA, hΨ1 _ _ hx, hfr]
    · have hx : cpast j y ∉ A' := fun hx => hyA (by rw [← hA']; exact hx)
      rw [Set.indicator_of_notMem hyA, hΨ0 _ _ hx]
  have hint : Integrable (fun y => Ψ (cpast j y, freshSample W j y.1.1)) μ := by
    refine integrable_closed_of_fresh b T hq j hΨm B fun x => ?_
    by_cases hx : x ∈ A'
    · simp only [hΨ1 x _ hx]
      exact hB _ (hXh x) _ (trace_framePast_le b E s T h q R hj hVs hA' hx)
    · simp [hΨ0 x _ hx]
  have h1 := condExp_congr_ae (m := closedSigma W j p M) heq
  have h2 := condExp_closed_fresh b T hq j hΨm hint
  filter_upwards [h1, h2] with y hy1 hy2 hyA
  rw [hy1, hy2]
  have hx : cpast j y ∈ A' := by rw [← hA'] at hyA; exact hyA
  refine integral_congr_ae (Filter.Eventually.of_forall fun f => ?_)
  show Ψ (cpast j y, f) = _
  rw [hΨ1 _ _ hx, hfr]

end BlockBand.SourceProcess.ClosedSummedProof
