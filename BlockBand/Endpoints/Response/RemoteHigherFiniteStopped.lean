module

public import BlockBand.Endpoints.Response.RemoteHigherFiniteSteps

/-!
# The finite-width higher generator from the summed contract and an exit-removal inequality

This file proves `RhlFiniteTraceGenerator` from the `summed` clause of `ContractingWordsContract`,
`FullSourceStopsContract` and the exit and stop-removal inequality `RhfStoppedExitRemoval`
(`rhlFiniteTraceGenerator_of_exitRemoval`). `RhfStoppedExitRemoval` bounds the exit value, end
value and after-stop dissipation of the composite `G(Φ_π)`, in the same form as
`NssStoppedExitRemoval` (its `r = 1` instance up to the constant `ε^p`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset Polynomial
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## The exit and stop-removal inequality
-/

/-- The stopped composite value `Re G(Φ_π)(A_{j₂∧σ})`, `σ = σ_K` the trace stop of the one-source
family from `(u₁/2)W`. -/
def rhfStoppedValue (b E : ℝ) (q : ℝ → ℝ) (K u₁ : ℝ) (a : ℕ → ℝ) (N : ℕ) (G : ℝ[X])
    (W j₂ : ℕ) (ω : GrowthPath W) : ℝ :=
  (polyValue b E (noTags W) (fun _ => q) W
    (nssStopIdx j₂ (traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω)) ω
    (rhfComposite a N G)).re

/-- **Exit value, end value and after-stop dissipation of the higher functional** (the
`r`-analogue of `NssStoppedExitRemoval`).
Same data as `RhlFiniteTraceGenerator` (`0 < b < 1/2`, bulk `E`, `0 < p < 1`, `r ≥ 1`, `pr < 1`,
a unit source, `ε > 0`, `t₁ + R < u₁ ≤ u₂`, `θ > 0`).
There are `K > 0` and `δ₀ > 0` such that
for every `δ ∈ (0, δ₀]`, every polynomial `π(x) = Σ_r a_r x^{r+1}` with `|π - f_ε| ≤ δx` on
`[0, K+1]` and every real polynomial `G` with `|G(y) - (y+ε^p)^r| ≤ δ` on
`rhfRange p ε K = [-ε^p/2, pε^{p-1}(K+1) + K + 1]` (values only), for all large `W`, with
`j_i = ⌊Wu_i⌋` and the stop `σ_K` from `(u₁/2)W`:
`E (Tr f_ε(A_{j₂}) + ε^p)^r + Σ_{j₁≤j≤j₂} W⁻¹ E[1{j≥σ}(-𝒢Φ_ε(j))⁺]
 ≤ E[1{σ>j₁} Re G(Φ_π)(A_{j₂∧σ})] + θ`
(`𝒢Φ_ε = rhlGenExpr`), the right expectation written as `E[1{σ>j₁}(·)⁺] - E[1{σ>j₁}(·)⁻]`
(the negative part on the left).

It is proved as `rhfStoppedExitRemoval_holds`, choosing `K`, then `δ₀`, then `W₀(π, G)`.

Why smaller than `RhlFiniteTraceGenerator`: the word generator `𝒜 G(Φ_π)` before the stop, the
`summed`, the tower property and pull-out on the adapted stop, the telescoping, the chain
rule for `wordGenerator`, the `wordCarre` evaluation on clock polynomials, the generator and
bracket comparisons, the sign `rhlGenExpr ≤ 0`, the start value, the endpoint term, the `C²`
approximants of `f_ε` and of `x^r` and the Riemann form are removed and proved
(`rhlFiniteTraceGenerator_of_exitRemoval`); only values of `π` on `[0, K+1]` and of `G` on
`rhfRange` enter.
Not equivalent to it modulo the proved lemmas: the classes of `π` and `G` are
larger (values only), and the converse needs the exit and `σ ≤ j₁` control (`tight`,
`tail`, `supMoments`), as for `NssStoppedExitRemoval`.
-/
def RhfStoppedExitRemoval : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 →
    ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ ε : ℝ, 0 < ε → ∀ u₁ u₂ : ℝ, t₁ + R < u₁ → u₁ ≤ u₂ → ∀ θ : ℝ, 0 < θ →
    ∃ K : ℝ, 0 < K ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (a : ℕ → ℝ) (N : ℕ) (G : ℝ[X]),
      (∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x) →
      (∀ y ∈ rhfRange p ε K, |G.eval y - rhfH (ε ^ p) r y| ≤ δ) →
      ∀ᶠ W : ℕ in atTop,
        ∫⁻ ω, ENNReal.ofReal ((nsClockSum (nsRegKernel p ε)
            (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω) + ε ^ p) ^ r) ∂growthPathLaw W b +
          ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
            ∫⁻ ω, (nsfAlive b E q K u₁ W j)ᶜ.indicator
              (fun ω => ENNReal.ofReal (-rhlGenExpr b E p r ε q W j ω)) ω ∂growthPathLaw W b +
          ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
              (-rhfStoppedValue b E q K u₁ a N G W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b ≤
        ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
            (rhfStoppedValue b E q K u₁ a N G W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b +
          ENNReal.ofReal θ

/-!
## The reduction at a fixed width
-/

/-- The reduction at a fixed width `W` (Riemann-sum form). -/
theorem rhf_reduction_fixedW (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b E p r ε : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hp : 0 < p)
    (hp1 : p < 1) (hr : 1 ≤ r) (hpr : p * r < 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    {u₁ u₂ K δ θ : ℝ} (hu₁0 : 0 < u₁) (hu₂ : u₁ ≤ u₂) (hK : 0 < K) (hδ : 0 < δ) (hθ : 0 < θ)
    {a : ℕ → ℝ} {N : ℕ} {G : ℝ[X]}
    (h1 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x ∧
      |nsfPolyD1 a N x - nsgDeriv p ε x| ≤ δ)
    (h2 : ∀ x ∈ Icc 0 (K + 1), ∀ y ∈ Icc 0 (K + 1),
      |nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y - nsgDivDiff p ε x y| ≤ δ)
    (hG : ∀ y ∈ rhfRange p ε K, |G.eval y - rhfH (ε ^ p) r y| ≤ δ ∧
      |(derivative G).eval y - rhfH1 (ε ^ p) r y| ≤ δ ∧
      |(derivative (derivative G)).eval y - rhfH2 (ε ^ p) r y| ≤ δ)
    (hδ1 : δ ≤ 1) (hδK : δ * (K + 1) ≤ ε ^ p / 2)
    {W : ℕ} (hW0 : 0 < W)
    (hjW : ∀ j, ⌊(W : ℝ) * u₁⌋₊ ≤ j → u₁ / 2 * W ≤ j)
    (hqt : ∀ j, ⌊(W : ℝ) * u₁⌋₊ ≤ j → q (((j + 1 : ℕ) : ℝ) / W) = 0)
    (hFint : ∀ j, ⌊(W : ℝ) * u₁⌋₊ ≤ j → j ≤ ⌊(W : ℝ) * u₂⌋₊ → Integrable
      (fun ω => polyValue b E (noTags W) (fun _ => q) W j ω (rhfComposite a N G))
      (growthPathLaw W b))
    {e : ℝ} (he0 : 0 ≤ e)
    (hsum : ∑ j ∈ Finset.Ico ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, ∫⁻ ω,
      ‖(nsfAlive b E q K u₁ W j).indicator (fun ω =>
        (growthPathLaw W b)[(nsfAlive b E q K u₁ W j).indicator (fun ω =>
          polyValue b E (noTags W) (fun _ => q) W (j + 1) ω (rhfComposite a N G) -
            polyValue b E (noTags W) (fun _ => q) W j ω (rhfComposite a N G)) | growthSigma W j] ω -
          (W : ℂ)⁻¹ * polyValue b E (noTags W) (fun _ => q) W j ω
            (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhfComposite a N G))) ω‖ₑ
        ∂growthPathLaw W b ≤ ENNReal.ofReal e)
    (hRW : ∫⁻ ω, ENNReal.ofReal ((nsClockSum (nsRegKernel p ε)
            (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω) + ε ^ p) ^ r) ∂growthPathLaw W b +
          ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
            ∫⁻ ω, (nsfAlive b E q K u₁ W j)ᶜ.indicator
              (fun ω => ENNReal.ofReal (-rhlGenExpr b E p r ε q W j ω)) ω ∂growthPathLaw W b +
          ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
              (-rhfStoppedValue b E q K u₁ a N G W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b ≤
        ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
            (rhfStoppedValue b E q K u₁ a N G W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b +
          ENNReal.ofReal (θ / 2))
    (hsmall : θ / 2 + (e + (W : ℝ)⁻¹ * (rhfC0 b E p r ε K + 2 * (δ * rhfKappa b E p r ε K)) +
        (u₂ - u₁ + 1) * (δ * rhfKappa b E p r ε K)) + δ * (rhfB p r ε K * K + 1) ≤ θ) :
    ∫⁻ ω, ENNReal.ofReal ((nsClockSum (nsRegKernel p ε)
        (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω) + ε ^ p) ^ r) ∂growthPathLaw W b +
      ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
        ∫⁻ ω, ENNReal.ofReal (-rhlGenExpr b E p r ε q W j ω) ∂growthPathLaw W b ≤
    ∫⁻ ω, ENNReal.ofReal ((nsClockSum (nsRegKernel p ε)
        (nearClock b E W ⌊(W : ℝ) * u₁⌋₊ q ω) + ε ^ p) ^ r) ∂growthPathLaw W b +
      ENNReal.ofReal θ := by
  have hP := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW0
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW0
  set j₁ := ⌊(W : ℝ) * u₁⌋₊ with hj₁
  set j₂ := ⌊(W : ℝ) * u₂⌋₊ with hj₂
  have h12 : j₁ ≤ j₂ := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hu₂ hW'.le)
  have hj₁lt : (W : ℝ) * u₁ < (j₁ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hj₂le : (j₂ : ℝ) ≤ W * u₂ := Nat.floor_le (mul_nonneg hW'.le (by linarith))
  obtain ⟨-, -, -, -, hκ0, hC₀0⟩ := rhf_consts_nonneg (r := r) hb hE hE' hp.le hε hK.le
  have hL0 : 0 ≤ u₂ - u₁ + 1 := by linarith
  set c := δ * rhfKappa b E p r ε K with hc
  set C₀ := rhfC0 b E p r ε K with hC₀
  have hc0 : 0 ≤ c := mul_nonneg hδ.le hκ0
  -- the pre-stop steps
  have hpre : ∀ j, j₁ ≤ j → ∃ r' : ℝ, Integrable ((nsfAlive b E q K u₁ W j).indicator fun ω =>
        polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhfComposite a N G)))
        (growthPathLaw W b) ∧ 0 ≤ r' ∧
      ∫⁻ ω, ENNReal.ofReal (-rhlGenExpr b E p r ε q W j ω) ∂growthPathLaw W b ≤
        ENNReal.ofReal r' + ∫⁻ ω, (nsfAlive b E q K u₁ W j)ᶜ.indicator
          (fun ω => ENNReal.ofReal (-rhlGenExpr b E p r ε q W j ω)) ω ∂growthPathLaw W b ∧
      r' ≤ -∫ ω, (nsfAlive b E q K u₁ W j).indicator (fun ω =>
          (polyValue b E (noTags W) (fun _ => q) W j ω
            (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhfComposite a N G))).re) ω
          ∂growthPathLaw W b + c ∧
      r' ≤ C₀ + 2 * c := by
    intro j hj1
    obtain ⟨hI, r', hr'⟩ := rhf_preStop_abstract (μ := growthPathLaw W b)
      (X := fun ω => rhlGenExpr b E p r ε q W j ω)
      (nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W j)
      (nss_measurable_polyValue b E (noTags W) _ W j _) hc0 hC₀0 (by
        filter_upwards [nsg_ae_scattering_unitary hCount hb1 hE hE' hW0 j] with ω hS hal
        exact rhf_preStop_key hb hE hE' hp.le hp1.le hr hpr hε hq0 (fun x hx => (h1 x hx).1)
          (fun x hx => (h1 x hx).2) h2 (fun y hy => (hG y hy).2.1) (fun y hy => (hG y hy).2.2)
          hδ1 hδK hal (hjW j hj1) hS (hqt j hj1))
    exact ⟨r', hI, hr'⟩
  choose! r' hGI hr0 hrPre hrUp hrC using hpre
  have hTel := nss_telescope_bound (μ := growthPathLaw W b) (growthSigma W) (tcx_growthSigma_le W)
    (fun ω => traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω)
    (fun j => nsfAlive b E q K u₁ W j) (fun j ω => Iff.rfl)
    (fun j => nss_measurableSet_alive_growthSigma b E (noTags W) q K (u₁ / 2) W j) h12
    (fun j ω => polyValue b E (noTags W) (fun _ => q) W j ω (rhfComposite a N G))
    (fun j ω => (W : ℂ)⁻¹ * polyValue b E (noTags W) (fun _ => q) W j ω
      (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhfComposite a N G)))
    hFint (fun j hj => ((hGI j (Finset.mem_Ico.1 hj).1).const_mul (W : ℂ)⁻¹).congr
      (Eventually.of_forall fun ω => by
        by_cases h : ω ∈ nsfAlive b E q K u₁ W j
        · simp [Set.indicator_of_mem h]
        · simp [Set.indicator_of_notMem h])) he0 hsum
  -- the real bookkeeping
  set Y := ∫ ω, (nsfAlive b E q K u₁ W j₁).indicator (fun ω =>
    (polyValue b E (noTags W) (fun _ => q) W j₁ ω (rhfComposite a N G)).re) ω ∂growthPathLaw W b
    with hY
  set S := ∫ ω, (nsfAlive b E q K u₁ W j₁).indicator
    (fun ω => rhfStoppedValue b E q K u₁ a N G W j₂ ω) ω ∂growthPathLaw W b with hS
  have hAm₁ := nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W j₁
  have hIY : Integrable ((nsfAlive b E q K u₁ W j₁).indicator (fun ω =>
      (polyValue b E (noTags W) (fun _ => q) W j₁ ω (rhfComposite a N G)).re))
      (growthPathLaw W b) :=
    ((hFint j₁ le_rfl h12).indicator hAm₁).re.congr
      (Eventually.of_forall fun ω => nss_re_indicator _ _ ω)
  have hIS : Integrable ((nsfAlive b E q K u₁ W j₁).indicator
      (fun ω => rhfStoppedValue b E q K u₁ a N G W j₂ ω)) (growthPathLaw W b) :=
    (nss_integrable_stopped (μ := growthPathLaw W b)
      (fun ω => traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω)
      (fun j => nsfAlive b E q K u₁ W j) (fun j ω => Iff.rfl)
      (fun j => nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W j) h12
      (fun j ω => polyValue b E (noTags W) (fun _ => q) W j ω (rhfComposite a N G))
      hFint).re.congr (Eventually.of_forall fun ω => nss_re_indicator _ _ ω)
  have hTel' : S - Y - e ≤ ∑ j ∈ Finset.Ico j₁ j₂, (W : ℝ)⁻¹ *
      ∫ ω, (nsfAlive b E q K u₁ W j).indicator (fun ω =>
        (polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhfComposite a N G))).re) ω
        ∂growthPathLaw W b := by
    have hdiff : ∫ ω, (nsfAlive b E q K u₁ W j₁).indicator (fun ω =>
        (polyValue b E (noTags W) (fun _ => q) W (nssStopIdx j₂
          (traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω)) ω
            (rhfComposite a N G)).re -
          (polyValue b E (noTags W) (fun _ => q) W j₁ ω (rhfComposite a N G)).re) ω
          ∂growthPathLaw W b = S - Y := by
      rw [hS, hY, ← integral_sub hIS hIY]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases h : ω ∈ nsfAlive b E q K u₁ W j₁
      · simp [Set.indicator_of_mem h, rhfStoppedValue]
      · simp [Set.indicator_of_notMem h]
    have hre : ∀ j, ∫ ω, (nsfAlive b E q K u₁ W j).indicator (fun ω =>
        ((W : ℂ)⁻¹ * polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhfComposite a N G))).re) ω
          ∂growthPathLaw W b = (W : ℝ)⁻¹ *
        ∫ ω, (nsfAlive b E q K u₁ W j).indicator (fun ω =>
          (polyValue b E (noTags W) (fun _ => q) W j ω
            (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhfComposite a N G))).re) ω
          ∂growthPathLaw W b := fun j => by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases h : ω ∈ nsfAlive b E q K u₁ W j
      · simp only [Set.indicator_of_mem h]
        rw [show ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
      · simp [Set.indicator_of_notMem h]
    have := hTel
    simp only [hre] at this
    rw [hdiff] at this
    exact this
  -- assembly
  have hWi : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.2 hW'.le
  have e1 : ((W : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((W : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hW', ENNReal.ofReal_natCast]
  have hcard : ((j₂ - j₁ : ℕ) : ℝ) * ((W : ℝ)⁻¹ * c) ≤ (u₂ - u₁ + 1) * c := by
    rw [Nat.cast_sub h12, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hc0
    rw [← div_eq_mul_inv, div_le_iff₀ hW']
    linarith
  obtain ⟨hSeq, hPn, hNn⟩ := nss_integral_indicator_eq hIS
  have hYle := rhf_startValue_le hCount hb1 hE hE' hp.le hp1.le hε hq0 (fun x hx => (h1 x hx).1)
    (fun y hy => (hG y hy).1) hδ1 hδK hW0 (hjW j₁ le_rfl) hIY
  have hB := rhf_B_nonneg (p := p) (r := r) (K := K) hε
  rw [e1] at hRW
  have hA := nss_assemble (Pre := fun j => ENNReal.ofReal (r' j)) h12 hWi
    (I := fun j => ∫ ω, (nsfAlive b E q K u₁ W j).indicator
      (fun ω => (polyValue b E (noTags W) (fun _ => q) W j ω (wordGenerator b E (fun _ => q)
        (((j + 1 : ℕ) : ℝ) / W) (rhfComposite a N G))).re) ω ∂growthPathLaw W b)
    hr0 (fun j _ => le_rfl) hrUp (hrC j₂ h12) hTel' hcard hRW
    hPn hNn hSeq hYle hθ he0 hc0 (by positivity) hL0
    (mul_nonneg hδ.le (by positivity)) hsmall
  refine le_trans ?_ hA
  simp only [e1]
  gcongr with j hj
  exact hrPre j (Finset.mem_Icc.1 hj).1

/-!
## The reduction
-/

/-- **`RhlFiniteTraceGenerator` from the summed contract and the exit and stop-removal
inequality.** Inputs:
`ContractingWordsContract.summed` (stopped one-step
drift of the ordinary composite `G(Φ_π)`), `FullSourceStopsContract.supMoments` (integrability
of `G(Φ_π)(A_j)` only), `ConditionalBlockGUECount` (a.s. unitarity) and
`RhfStoppedExitRemoval`.
-/
theorem rhlFiniteTraceGenerator_of_exitRemoval (hCW : ContractingWordsContract)
    (hStops : FullSourceStopsContract)
    (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hR : RhfStoppedExitRemoval) : RhlFiniteTraceGenerator := by
  intro b hb hb1 E hE hE' p r hp hp1 hr hpr t₁ R q hq ε hε u₁ u₂ hu₁ hu₂ θ hθ
  have hq0 : ∀ x, 0 ≤ q x := hq.2.2.2.1.1
  have hqoff : ∀ x, t₁ + R < x → q x = 0 := fun x hx =>
    hq.2.2.2.1.2.1 x fun h => by linarith [h.2]
  have hu₁0 : 0 < u₁ := by linarith [hq.1, hq.2.1]
  have hIT : IsIntervalTests (fun _ : Fin 1 => q) := fun _ => ⟨t₁, t₁ + R, hq.2.2.2.1⟩
  obtain ⟨K, hK, δR, hδR, hRK⟩ :=
    hR b hb hb1 E hE hE' p r hp hp1 hr hpr t₁ R q hq ε hε u₁ u₂ hu₁ hu₂ (θ / 2) (by positivity)
  obtain ⟨-, -, -, -, hκ0, hC₀0⟩ := rhf_consts_nonneg (r := r) hb hE hE' hp.le hε hK.le
  have hB := rhf_B_nonneg (p := p) (r := r) (K := K) hε
  have hL0 : 0 ≤ u₂ - u₁ + 1 := by linarith
  have hεp := Real.rpow_pos_of_pos hε p
  set κ := rhfKappa b E p r ε K with hκ
  set C₀ := rhfC0 b E p r ε K with hC₀
  set B := rhfB p r ε K with hBdef
  set Dd := κ * (u₂ - u₁ + 1) + B * K + 1 with hDd
  have hDd0 : 0 < Dd := by positivity
  set δ := min (min δR 1) (min (ε ^ p / (2 * (K + 1))) (θ / (4 * Dd))) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδR one_pos) (lt_min (by positivity) (by positivity))
  have hδR' : δ ≤ δR := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδK : δ * (K + 1) ≤ ε ^ p / 2 := by
    have h' : δ ≤ ε ^ p / (2 * (K + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h'
    linarith
  have hδsmall : δ * (B * K + 1) + (u₂ - u₁ + 1) * (δ * κ) ≤ θ / 4 := by
    have h' : δ ≤ θ / (4 * Dd) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h'
    have : δ * (B * K + 1) + (u₂ - u₁ + 1) * (δ * κ) = δ * Dd := by rw [hDd]; ring
    rw [this]
    linarith
  obtain ⟨a, N, hA1, hA2⟩ := nsf_exists_poly_approx (p := p) hε (L := K + 1) (by linarith) hδ
  obtain ⟨G, hG⟩ := rhf_exists_rpow_approx (r := r) hp.le hε hK.le hδ
  obtain ⟨Cs, Ws, hs⟩ := hCW.summed b hb hb1 E hE hE' 0 1 (fun _ => q) hIT (rhfComposite a N G)
    (rhf_isOrdinaryPoly_composite a N G) (u₁ / 2) (u₂ + 1) K (by positivity) (by linarith)
  obtain ⟨Cm, Wm, hm⟩ := hStops.supMoments b hb hb1 E hE hE' 0 1 (fun _ => q) hIT (u₁ / 2)
    (u₂ + 1) (((N + 1) * (G.natDegree + 1) : ℕ) : ℝ) (by positivity) (by linarith)
    (by positivity)
  set c := δ * κ with hc
  have hc0 : 0 ≤ c := mul_nonneg hδ.le hκ0
  have htend : Tendsto (fun W : ℕ => max (Cs * (1 / Real.sqrt W + 1 / W)) 0 +
      (W : ℝ)⁻¹ * (C₀ + 2 * c)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun W : ℕ => (W : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hsq : Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h3 := (((hsq.add hinv).const_mul Cs).max (tendsto_const_nhds (x := (0 : ℝ)))).add
      (hinv.mul_const (C₀ + 2 * c))
    simp only [add_zero, mul_zero, max_self, zero_mul] at h3
    simpa only [one_div] using h3
  filter_upwards [hRK δ hδ hδR' a N G (fun x hx => (hA1 x hx).1) (fun y hy => (hG y hy).1),
    eventually_ge_atTop Ws, eventually_ge_atTop Wm, eventually_gt_atTop 0,
    eventually_ge_atTop ⌈2 / u₁⌉₊, (tendsto_order.1 htend).2 (θ / 4) (by positivity)]
    with W hRW hWs hWm hW0 hWu hWe
  have hP := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW0
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW0
  have hWu' : 2 / u₁ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWu)
  set j₁ := ⌊(W : ℝ) * u₁⌋₊ with hj₁
  set j₂ := ⌊(W : ℝ) * u₂⌋₊ with hj₂
  have hj₁lt : (W : ℝ) * u₁ < (j₁ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hj₂le : (j₂ : ℝ) ≤ W * u₂ := Nat.floor_le (mul_nonneg hW'.le (by linarith))
  have hjW : ∀ j, j₁ ≤ j → u₁ / 2 * W ≤ j := by
    intro j hj1
    have h2 : (j₁ : ℝ) ≤ j := by exact_mod_cast hj1
    have h3 : 2 ≤ u₁ * W := by rw [div_le_iff₀ hu₁0] at hWu'; linarith
    nlinarith
  have hqt : ∀ j, j₁ ≤ j → q (((j + 1 : ℕ) : ℝ) / W) = 0 := by
    intro j hj1
    refine hqoff _ ?_
    have h2 : (j₁ : ℝ) ≤ j := by exact_mod_cast hj1
    rw [lt_div_iff₀ hW']
    push_cast
    nlinarith
  have hjT : ∀ j, j ≤ j₂ + 1 → (j : ℝ) ≤ (u₂ + 1) * W := by
    intro j hj
    have : (j : ℝ) ≤ j₂ + 1 := by exact_mod_cast hj
    nlinarith
  -- integrability of the composite
  have hFint : ∀ j, j₁ ≤ j → j ≤ j₂ → Integrable
      (fun ω => polyValue b E (noTags W) (fun _ => q) W j ω (rhfComposite a N G))
      (growthPathLaw W b) := by
    intro j hj1 hj2
    refine rhf_integrable_polyValue_composite b E hq0 a N G ?_
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((lintegral_mono fun ω => ?_).trans (hm W hWm (noTags W) (Sum.inr 0)))
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    have e : sourceTrace b E (noTags W) (fun _ : Fin 1 => q) W j ω (Sum.inr 0) =
        (intervalSource b E W j q ω).trace.re := by
      simp [sourceTrace, sourceLetter, letterMatrix]
    rw [← e]
    exact le_iSup₂ (f := fun (i : ℕ) (_ : u₁ / 2 * W ≤ i ∧ (i : ℝ) ≤ (u₂ + 1) * W) =>
      ‖sourceTrace b E (noTags W) (fun _ : Fin 1 => q) W i ω (Sum.inr 0)‖ₑ) j
      ⟨hjW j hj1, hjT j (by omega)⟩
  -- the summed contract on the steps `j₁ ≤ j < j₂`
  have hsum : ∑ j ∈ Finset.Ico j₁ j₂, ∫⁻ ω, ‖(nsfAlive b E q K u₁ W j).indicator (fun ω =>
      (growthPathLaw W b)[(nsfAlive b E q K u₁ W j).indicator (fun ω =>
        polyValue b E (noTags W) (fun _ => q) W (j + 1) ω (rhfComposite a N G) -
          polyValue b E (noTags W) (fun _ => q) W j ω (rhfComposite a N G)) | growthSigma W j] ω -
        (W : ℂ)⁻¹ * polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhfComposite a N G))) ω‖ₑ
        ∂growthPathLaw W b ≤
      ENNReal.ofReal (max (Cs * (1 / Real.sqrt W + 1 / W)) 0) := by
    obtain ⟨hs1, -⟩ := hs W hWs (noTags W) (fun a => a.elim0)
    refine le_trans (Finset.sum_le_sum_of_subset ?_)
      (hs1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hjW j hj1, fun a => a.elim0⟩
    exact Nat.lt_of_succ_le (Nat.le_floor (by exact_mod_cast hjT (j + 1) (by omega)))
  have hfix := rhf_reduction_fixedW hCount hb hb1 hE hE' hp hp1 hr hpr hε hq0 hu₁0 hu₂ hK hδ hθ
    hA1 hA2 (fun y hy => hG y hy) hδ1 hδK hW0 hjW hqt hFint (le_max_right _ _) hsum hRW
    (by rw [hc] at hWe; linarith)
  -- the Riemann form
  refine le_trans ?_ hfix
  gcongr
  exact nsf_lintegral_floor_le_sum hW0 hu₁0.le
    (fun j => ∫⁻ ω, ENNReal.ofReal (-rhlGenExpr b E p r ε q W j ω) ∂growthPathLaw W b)

end BlockBand.Endpoints
