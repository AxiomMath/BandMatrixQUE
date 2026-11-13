module

public import BlockBand.Endpoints.Response.NearSchattenStoppedSteps

/-!
# The stopped energy inequality from the summed contract

This file derives `NsfStoppedWordEnergy` from the `summed` clause of `ContractingWordsContract`,
`FullSourceStopsContract` and the exit and stop-removal inequality `NssStoppedExitRemoval`, and
composes it into `NearSchattenDecayContract` (`nearSchattenDecay_of_chain`).

The ingredients are:
  - `summed` on the stop for `Φ_π`, telescoped with the tower property and pull-out on the
    adapted survival events (`nss_telescope_bound`, `nss_measurableSet_alive_growthSigma`): the
    case `σ ≤ j₁` cancels;
  - the truncation `(-Re 𝒜Φ_π)⁺ ≤ -Re 𝒜Φ_π + cδ` (the reverse bridge `nss_polyGen_le_genExpr`
    and `𝒢_ε ≤ 0`), and the extra endpoint `j = j₂` by `|𝒜Φ_π| ≤ C_εK² + cδ` on the stop;
  - the start value `Φ_π(A_{j₁}) ≤ Tr f_ε(A_{j₁}) + δK` on `{σ > j₁}` (`|π - f_ε| ≤ δx`);
  - the order of choices: `K` (from the remainder), then `δ₀`, then `π`, then `W`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## The exit and stop-removal inequality
-/

/-- The stopped clock value `Re Φ_π(A_{j₂∧σ})`, `σ = σ_K` the trace stop of the one-source
family from `(u₁/2)W`. -/
def nssStoppedClock (b E : ℝ) (q : ℝ → ℝ) (K u₁ : ℝ) (a : ℕ → ℝ) (N W j₂ : ℕ)
    (ω : GrowthPath W) : ℝ :=
  (polyValue b E (noTags W) (fun _ => q) W
    (nssStopIdx j₂ (traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω)) ω
    (nsfClockPoly a N)).re

/-- NSG §2.4 steps 4–5;
The fixed clock/current moments
remove the stops").
Same data as `NsfStoppedWordEnergy`.
There are `K > 0` and `δ₀ > 0` such that for every
`δ ∈ (0, δ₀]` and every polynomial `π(x) = Σ_r a_r x^{r+1}` with `|π - f_ε| ≤ δx` on `[0, K+1]`
(values only), for all large `W`, with `j_i = ⌊Wu_i⌋` and the stop `σ_K` from `(u₁/2)W`:
`E Tr f_ε(A_{j₂}) + Σ_{j₁≤j≤j₂} W⁻¹ E[1{j≥σ}(-𝒢_ε(j))⁺] ≤ E[1{σ>j₁} Re Φ_π(A_{j₂∧σ})] + θ`,
the right expectation written as `E[1{σ>j₁}(·)⁺] - E[1{σ>j₁}(·)⁻]` (the negative part on the left).

Truth: on `{σ > j₂}`, `Φ_π(A_{j₂}) ≥ Tr f_ε(A_{j₂}) - δK`; on
`{j₁ < σ ≤ j₂}`, `Φ_π(A_σ) ≥ -δ(K+1)` off the event that one step of `Tr(QP)` jumps by more than
`1` (`FullSourceGeneratorContract.tight`), whose contribution vanishes as `W → ∞` for fixed `π`
(Cauchy–Schwarz with `FullSourceStopsContract.supMoments`);
`E[Tr f_ε(A_{j₂}); σ ≤ j₂] ≤
pε^{p-1}E[Tr Q_{j₂}; σ ≤ j₂]` and the after-stop dissipation
(`-𝒢_ε ≤ C_ε(g Tr A + (Tr A)²)`, `nss_abs_genExpr_le`; the `g Tr A` part is the drift of the word
`Tr QP`, uniformly integrable by `compensatorUI`) are small in `K` uniformly in `W` by `tail`
and `supMoments`.

Why strictly smaller than `NsfStoppedWordEnergy`: the word generator `𝒜Φ_π` before the stop,
the `summed`, the tower property and pull-out on the adapted stop, the telescoping, the
truncation `(·)⁺` (reverse bridge), the endpoint term and the start value are removed and proved
(`nsfStoppedWordEnergy_of_exitRemoval`); only the values of `π` on `[0, K+1]` are used.
-/
def NssStoppedExitRemoval : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ ε : ℝ, 0 < ε → ∀ u₁ u₂ : ℝ, t₁ + R < u₁ → u₁ ≤ u₂ → ∀ θ : ℝ, 0 < θ →
    ∃ K : ℝ, 0 < K ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (a : ℕ → ℝ) (N : ℕ),
      (∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x) →
      ∀ᶠ W : ℕ in atTop,
        ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
            (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω)) ∂growthPathLaw W b +
          ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
            ∫⁻ ω, (nsfAlive b E q K u₁ W j)ᶜ.indicator
              (fun ω => ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω)) ω ∂growthPathLaw W b +
          ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
              (-nssStoppedClock b E q K u₁ a N W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b ≤
        ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
            (nssStoppedClock b E q K u₁ a N W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b +
          ENNReal.ofReal θ

/-!
## Bookkeeping
-/

/-- The final `ℝ≥0∞` arithmetic: from `L + N ≤ P + θ₁` (`P, N < ∞`, `S = P - N`),
`Pre ≤ X ≤ Y - S + η` and `Y ≤ L₁ + η'`, `L + Pre ≤ L₁ + (θ₁ + η + η')`. -/
theorem nss_ennreal_combine {L Nn Pn Pre L₁ : ℝ≥0∞} {θ₁ S X Y η η' : ℝ} (hθ₁ : 0 ≤ θ₁)
    (hη : 0 ≤ η) (hη' : 0 ≤ η') (hR : L + Nn ≤ Pn + ENNReal.ofReal θ₁) (hPn : Pn ≠ ⊤)
    (hNn : Nn ≠ ⊤) (hS : S = Pn.toReal - Nn.toReal) (hPre : Pre ≤ ENNReal.ofReal X) (hX0 : 0 ≤ X)
    (hX : X ≤ Y - S + η) (hY : ENNReal.ofReal Y ≤ L₁ + ENNReal.ofReal η') :
    L + Pre ≤ L₁ + ENNReal.ofReal (θ₁ + η + η') := by
  have hRt : Pn + ENNReal.ofReal θ₁ ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hPn, ENNReal.ofReal_ne_top⟩
  have hL : L ≠ ⊤ := ne_top_of_le_ne_top hRt (le_self_add.trans hR)
  have hLt : L.toReal ≤ S + θ₁ := by
    have := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hL, hNn⟩) hRt).2 hR
    rw [ENNReal.toReal_add hL hNn, ENNReal.toReal_add hPn ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hθ₁] at this
    rw [hS]; linarith
  calc L + Pre ≤ ENNReal.ofReal L.toReal + ENNReal.ofReal X := by
        rw [ENNReal.ofReal_toReal hL]; gcongr
    _ = ENNReal.ofReal (L.toReal + X) := (ENNReal.ofReal_add ENNReal.toReal_nonneg hX0).symm
    _ ≤ ENNReal.ofReal (Y + (θ₁ + η)) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal Y + ENNReal.ofReal (θ₁ + η) := ENNReal.ofReal_add_le
    _ ≤ L₁ + ENNReal.ofReal η' + ENNReal.ofReal (θ₁ + η) := by gcongr
    _ = L₁ + ENNReal.ofReal (θ₁ + η + η') := by
        rw [add_assoc, ← ENNReal.ofReal_add hη' (by linarith)]
        congr 2; ring

/-- `E[1_A h] = E[1_A h⁺] - E[1_A h⁻]` in the indicator form, with both parts finite. -/
theorem nss_integral_indicator_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : Set Ω}
    {h : Ω → ℝ} (hI : Integrable (A.indicator h) μ) :
    ∫ ω, A.indicator h ω ∂μ =
        (∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (h ω)) ω ∂μ).toReal -
          (∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (-h ω)) ω ∂μ).toReal ∧
      ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (h ω)) ω ∂μ ≠ ⊤ ∧
      ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (-h ω)) ω ∂μ ≠ ⊤ := by
  have e1 : ∀ ω, A.indicator (fun ω => ENNReal.ofReal (h ω)) ω =
      ENNReal.ofReal (A.indicator h ω) := fun ω => by
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have e2 : ∀ ω, A.indicator (fun ω => ENNReal.ofReal (-h ω)) ω =
      ENNReal.ofReal (-A.indicator h ω) := fun ω => by
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  simp only [e1, e2]
  have hfin := hI.hasFiniteIntegral
  unfold HasFiniteIntegral at hfin
  refine ⟨integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI, ?_, ?_⟩
  · refine ne_top_of_le_ne_top hfin.ne (lintegral_mono fun ω => ?_)
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  · refine ne_top_of_le_ne_top hfin.ne (lintegral_mono fun ω => ?_)
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)

/-- The start value on `{σ > j}`: `E[1_A Φ_π(A_j)] ≤ E Tr f_ε(A_j) + δK`. -/
theorem nss_startValue_le (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b E p ε : ℝ} (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) {K ε' δ : ℝ} (hδ : 0 ≤ δ) {a : ℕ → ℝ} {N : ℕ}
    (h0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x) (κ : Fin 0 → ℕ)
    {W : ℕ} (hW : 0 < W) {j : ℕ} (hj : ε' * W ≤ j)
    (hI : Integrable ((alive b E κ (fun _ : Fin 1 => q) K ε' W j).indicator
      fun ω => (polyValue b E κ (fun _ => q) W j ω (nsfClockPoly a N)).re) (growthPathLaw W b)) :
    ENNReal.ofReal (∫ ω, (alive b E κ (fun _ : Fin 1 => q) K ε' W j).indicator
        (fun ω => (polyValue b E κ (fun _ => q) W j ω (nsfClockPoly a N)).re) ω
          ∂growthPathLaw W b) ≤
      ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω))
          ∂growthPathLaw W b + ENNReal.ofReal (δ * K) := by
  have hP := passDeriv_isProbabilityMeasure_growthPathLaw W b
  obtain ⟨he, hPt, -⟩ := nss_integral_indicator_eq hI
  rw [he]
  refine (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)).trans ?_
  rw [ENNReal.ofReal_toReal hPt]
  calc _ ≤ ∫⁻ ω, (ENNReal.ofReal (nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω)) +
          ENNReal.ofReal (δ * K)) ∂growthPathLaw W b := by
        refine lintegral_mono_ae ?_
        filter_upwards [nsg_ae_scattering_unitary hCount hb1 hE hE' hW j] with ω hS
        by_cases hal : ω ∈ alive b E κ (fun _ : Fin 1 => q) K ε' W j
        · rw [Set.indicator_of_mem hal]
          refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
          have hpsd := ns_nearClock_posSemidef b E W j q hq ω
          obtain ⟨-, -, -, hA⟩ := nsf_alive_bounds κ hq hal hj hS
          rw [nsf_polyValue_clockPoly_path b E hq W j ω κ a N, Complex.ofReal_re,
            nsf_clockSum_regKernel hpsd]
          have hsum : ∑ i, hpsd.1.eigenvalues i = (nearClock b E W j q ω).trace.re := by
            rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
          have hlam : ∀ i, hpsd.1.eigenvalues i ∈ Icc 0 (K + 1) := fun i =>
            ⟨hpsd.eigenvalues_nonneg i, (nsf_eigenvalue_le_trace hpsd i).trans (by linarith)⟩
          have h := (abs_le.1 (nsf_sum_regFun_sub_le h0 hlam)).2
          rw [hsum] at h
          nlinarith
        · rw [Set.indicator_of_notMem hal]; exact zero_le
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- The fixed-`W` assembly (abstract bookkeeping of the reduction). -/
theorem nss_assemble {j₁ j₂ : ℕ} (h12 : j₁ ≤ j₂) {w : ℝ} (hw : 0 ≤ w) {r I : ℕ → ℝ}
    {Pre Post : ℕ → ℝ≥0∞} {Lf₂ Lf₁ Nn Pn : ℝ≥0∞} {S Y e c C L θ η' : ℝ}
    (hr0 : ∀ j, j₁ ≤ j → 0 ≤ r j) (hrPre : ∀ j, j₁ ≤ j → Pre j ≤ ENNReal.ofReal (r j))
    (hrUp : ∀ j, j₁ ≤ j → r j ≤ -I j + c) (hrC : r j₂ ≤ C)
    (hTel : S - Y - e ≤ ∑ j ∈ Finset.Ico j₁ j₂, w * I j)
    (hcard : ((j₂ - j₁ : ℕ) : ℝ) * (w * c) ≤ L * c)
    (hRW : Lf₂ + ∑ j ∈ Finset.Icc j₁ j₂, ENNReal.ofReal w * Post j + Nn ≤
      Pn + ENNReal.ofReal (θ / 2))
    (hPn : Pn ≠ ⊤) (hNn : Nn ≠ ⊤) (hSeq : S = Pn.toReal - Nn.toReal)
    (hYle : ENNReal.ofReal Y ≤ Lf₁ + ENNReal.ofReal η') (hθ : 0 < θ) (he0 : 0 ≤ e)
    (hc0 : 0 ≤ c) (hC0 : 0 ≤ C) (hL0 : 0 ≤ L) (hη' : 0 ≤ η')
    (hsmall : θ / 2 + (e + w * C + L * c) + η' ≤ θ) :
    Lf₂ + ∑ j ∈ Finset.Icc j₁ j₂, ENNReal.ofReal w * (Pre j + Post j) ≤
      Lf₁ + ENNReal.ofReal θ := by
  set X := ∑ j ∈ Finset.Icc j₁ j₂, w * r j with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun j hj => mul_nonneg hw (hr0 j (Finset.mem_Icc.1 hj).1)
  have hXle : X ≤ Y - S + (e + w * C + L * c) := by
    rw [hX, ← Finset.Ico_insert_right h12, Finset.sum_insert (by simp)]
    have hj₂ : w * r j₂ ≤ w * C := mul_le_mul_of_nonneg_left hrC hw
    have hIco : ∑ j ∈ Finset.Ico j₁ j₂, w * r j ≤
        ∑ j ∈ Finset.Ico j₁ j₂, (-(w * I j) + w * c) := Finset.sum_le_sum fun j hj =>
      (mul_le_mul_of_nonneg_left (hrUp j (Finset.mem_Ico.1 hj).1) hw).trans_eq (by ring)
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Nat.card_Ico,
      nsmul_eq_mul] at hIco
    linarith
  have hPre : ∑ j ∈ Finset.Icc j₁ j₂, ENNReal.ofReal w * Pre j ≤ ENNReal.ofReal X := by
    rw [hX, ENNReal.ofReal_sum_of_nonneg (fun j hj =>
      mul_nonneg hw (hr0 j (Finset.mem_Icc.1 hj).1))]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [ENNReal.ofReal_mul hw]
    gcongr
    exact hrPre j (Finset.mem_Icc.1 hj).1
  have hη : 0 ≤ e + w * C + L * c := by positivity
  have hcomb := nss_ennreal_combine (by positivity : (0 : ℝ) ≤ θ / 2) hη hη' hRW hPn hNn hSeq
    hPre hX0 hXle hYle
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show ∀ x y z : ℝ≥0∞, x + (y + z) = x + z + y from fun x y z => by ring]
  exact hcomb.trans (by gcongr)

/-!
## The reduction
-/

/-- The reduction at a fixed width `W`. -/
theorem nss_reduction_fixedW (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b E p ε : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hp : 0 < p)
    (hp1 : p < 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x) {u₁ u₂ K δ θ : ℝ}
    (hu₁0 : 0 < u₁) (hu₂ : u₁ ≤ u₂) (hK : 0 < K) (hδ : 0 < δ) (hθ : 0 < θ) {a : ℕ → ℝ} {N : ℕ}
    (h1 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x ∧
      |nsfPolyD1 a N x - nsgDeriv p ε x| ≤ δ)
    (h2 : ∀ x ∈ Icc 0 (K + 1), ∀ y ∈ Icc 0 (K + 1),
      |nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y - nsgDivDiff p ε x y| ≤ δ)
    {W : ℕ} (hW0 : 0 < W)
    (hjW : ∀ j, ⌊(W : ℝ) * u₁⌋₊ ≤ j → u₁ / 2 * W ≤ j)
    (hqt : ∀ j, ⌊(W : ℝ) * u₁⌋₊ ≤ j → q (((j + 1 : ℕ) : ℝ) / W) = 0)
    (hFint : ∀ j, ⌊(W : ℝ) * u₁⌋₊ ≤ j → j ≤ ⌊(W : ℝ) * u₂⌋₊ → Integrable
      (fun ω => polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N))
      (growthPathLaw W b))
    {e : ℝ} (he0 : 0 ≤ e)
    (hsum : ∑ j ∈ Finset.Ico ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, ∫⁻ ω, ‖(nsfAlive b E q K u₁ W j).indicator (fun ω =>
      (growthPathLaw W b)[(nsfAlive b E q K u₁ W j).indicator (fun ω =>
        polyValue b E (noTags W) (fun _ => q) W (j + 1) ω (nsfClockPoly a N) -
          polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N)) | growthSigma W j] ω -
        (W : ℂ)⁻¹ * polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N))) ω‖ₑ
        ∂growthPathLaw W b ≤
      ENNReal.ofReal e)
    (hRW : ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
            (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω)) ∂growthPathLaw W b +
          ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
            ∫⁻ ω, (nsfAlive b E q K u₁ W j)ᶜ.indicator
              (fun ω => ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω)) ω ∂growthPathLaw W b +
          ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
              (-nssStoppedClock b E q K u₁ a N W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b ≤
        ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
            (nssStoppedClock b E q K u₁ a N W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b +
          ENNReal.ofReal (θ / 2))
    (hsmall : θ / 2 + (e + (W : ℝ)⁻¹ * (transportD0 b E / 2 * nssGenConst p ε *
      (K / 2 * K + K ^ 2) + 2 * (transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2))) +
        (u₂ - u₁ + 1) * (transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2))) + δ * K ≤ θ) :
    ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
        (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω)) ∂growthPathLaw W b +
      ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
        ∫⁻ ω, nsfStoppedDiss b E p ε q K u₁ a N W j ω ∂growthPathLaw W b ≤
    ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
        (nearClock b E W ⌊(W : ℝ) * u₁⌋₊ q ω)) ∂growthPathLaw W b + ENNReal.ofReal θ := by
  have hP := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW0
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW0
  set j₁ := ⌊(W : ℝ) * u₁⌋₊ with hj₁
  set j₂ := ⌊(W : ℝ) * u₂⌋₊ with hj₂
  have h12 : j₁ ≤ j₂ := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hu₂ hW'.le)
  have hj₁lt : (W : ℝ) * u₁ < (j₁ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hj₂le : (j₂ : ℝ) ≤ W * u₂ := Nat.floor_le (mul_nonneg hW'.le (by linarith))
  have hD := (ns_transportD0_pos hb hE hE').le
  have hκ2 : 0 ≤ K / 2 * K + K ^ 2 := by positivity
  have hL0 : 0 ≤ u₂ - u₁ + 1 := by linarith
  set c := transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2) with hc
  set C₀ := transportD0 b E / 2 * nssGenConst p ε * (K / 2 * K + K ^ 2) with hC₀
  have hc0 : 0 ≤ c := by positivity
  have hC₀0 : 0 ≤ C₀ := by
    have : 0 ≤ nssGenConst p ε :=
      (mul_nonneg hp.le (Real.rpow_nonneg hε.le _)).trans (le_max_left _ _)
    positivity
  -- the pre-stop steps
  have hpre : ∀ j, j₁ ≤ j → ∃ r : ℝ, Integrable ((nsfAlive b E q K u₁ W j).indicator fun ω =>
        polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N)))
        (growthPathLaw W b) ∧ 0 ≤ r ∧
      ∫⁻ ω, (nsfAlive b E q K u₁ W j).indicator (fun ω => ENNReal.ofReal
          (-(polyValue b E (noTags W) (fun _ => q) W j ω
            (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N))).re)) ω
          ∂growthPathLaw W b ≤ ENNReal.ofReal r ∧
      r ≤ -∫ ω, (nsfAlive b E q K u₁ W j).indicator (fun ω =>
          (polyValue b E (noTags W) (fun _ => q) W j ω
            (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N))).re) ω
          ∂growthPathLaw W b + c ∧
      r ≤ C₀ + 2 * c := by
    intro j hj1
    obtain ⟨hI, r, hr⟩ := nss_preStop_abstract (μ := growthPathLaw W b)
      (nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W j)
      (nss_measurable_polyValue b E (noTags W) _ W j _) hc0 hC₀0 (by
        filter_upwards [nsg_ae_scattering_unitary hCount hb1 hE hE' hW0 j] with ω hS hal
        exact nss_preStop_key hb hE hE' hp.le hp1.le hε hq0 (fun x hx => (h1 x hx).2) h2
          (noTags W) hal (hjW j hj1) hS (hqt j hj1))
    exact ⟨r, hI, hr⟩
  choose! r hGI hr0 hrPre hrUp hrC using hpre
  have hTel := nss_telescope_bound (μ := growthPathLaw W b) (growthSigma W) (tcx_growthSigma_le W)
    (fun ω => traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω)
    (fun j => nsfAlive b E q K u₁ W j) (fun j ω => Iff.rfl)
    (fun j => nss_measurableSet_alive_growthSigma b E (noTags W) q K (u₁ / 2) W j) h12
    (fun j ω => polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N))
    (fun j ω => (W : ℂ)⁻¹ * polyValue b E (noTags W) (fun _ => q) W j ω
      (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N)))
    hFint (fun j hj => ((hGI j (Finset.mem_Ico.1 hj).1).const_mul (W : ℂ)⁻¹).congr
      (Eventually.of_forall fun ω => by
        by_cases h : ω ∈ nsfAlive b E q K u₁ W j
        · simp [Set.indicator_of_mem h]
        · simp [Set.indicator_of_notMem h])) he0 hsum
  -- the real bookkeeping
  set Y := ∫ ω, (nsfAlive b E q K u₁ W j₁).indicator (fun ω =>
    (polyValue b E (noTags W) (fun _ => q) W j₁ ω (nsfClockPoly a N)).re) ω ∂growthPathLaw W b
    with hY
  set S := ∫ ω, (nsfAlive b E q K u₁ W j₁).indicator
    (fun ω => nssStoppedClock b E q K u₁ a N W j₂ ω) ω ∂growthPathLaw W b with hS
  have hAm₁ := nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W j₁
  have hIY : Integrable ((nsfAlive b E q K u₁ W j₁).indicator (fun ω =>
      (polyValue b E (noTags W) (fun _ => q) W j₁ ω (nsfClockPoly a N)).re))
      (growthPathLaw W b) :=
    ((hFint j₁ le_rfl h12).indicator hAm₁).re.congr
      (Eventually.of_forall fun ω => nss_re_indicator _ _ ω)
  have hIS : Integrable ((nsfAlive b E q K u₁ W j₁).indicator
      (fun ω => nssStoppedClock b E q K u₁ a N W j₂ ω)) (growthPathLaw W b) :=
    (nss_integrable_stopped (μ := growthPathLaw W b)
      (fun ω => traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω)
      (fun j => nsfAlive b E q K u₁ W j) (fun j ω => Iff.rfl)
      (fun j => nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W j) h12
      (fun j ω => polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N))
      hFint).re.congr (Eventually.of_forall fun ω => nss_re_indicator _ _ ω)
  have hTel' : S - Y - e ≤ ∑ j ∈ Finset.Ico j₁ j₂, (W : ℝ)⁻¹ *
      ∫ ω, (nsfAlive b E q K u₁ W j).indicator (fun ω =>
        (polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N))).re) ω
        ∂growthPathLaw W b := by
    have hdiff : ∫ ω, (nsfAlive b E q K u₁ W j₁).indicator (fun ω =>
        (polyValue b E (noTags W) (fun _ => q) W (nssStopIdx j₂
          (traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω)) ω
            (nsfClockPoly a N)).re -
          (polyValue b E (noTags W) (fun _ => q) W j₁ ω (nsfClockPoly a N)).re) ω
          ∂growthPathLaw W b = S - Y := by
      rw [hS, hY, ← integral_sub hIS hIY]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases h : ω ∈ nsfAlive b E q K u₁ W j₁
      · simp [Set.indicator_of_mem h, nssStoppedClock]
      · simp [Set.indicator_of_notMem h]
    have hre : ∀ j, ∫ ω, (nsfAlive b E q K u₁ W j).indicator (fun ω =>
        ((W : ℂ)⁻¹ * polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N))).re) ω
          ∂growthPathLaw W b = (W : ℝ)⁻¹ *
        ∫ ω, (nsfAlive b E q K u₁ W j).indicator (fun ω =>
          (polyValue b E (noTags W) (fun _ => q) W j ω
            (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N))).re) ω
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
  have hYle := nss_startValue_le hCount hb1 hE hE' hq0 hδ.le (fun x hx => (h1 x hx).1)
    (noTags W) hW0 (hjW j₁ le_rfl) hIY
  have hsplit : ∀ j, ∫⁻ ω, nsfStoppedDiss b E p ε q K u₁ a N W j ω ∂growthPathLaw W b =
      ∫⁻ ω, (nsfAlive b E q K u₁ W j).indicator (fun ω => ENNReal.ofReal (-(polyValue b E (noTags W) (fun _ => q) W j ω (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N))).re)) ω
        ∂growthPathLaw W b +
      ∫⁻ ω, (nsfAlive b E q K u₁ W j)ᶜ.indicator
        (fun ω => ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω)) ω ∂growthPathLaw W b := by
    intro j
    unfold nsfStoppedDiss
    exact lintegral_add_left ((ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp
      (nss_measurable_polyValue b E (noTags W) _ W j _)).neg).indicator
      (nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W j)) _
  rw [e1] at hRW
  simp only [hsplit, e1]
  exact nss_assemble h12 hWi (I := fun j => ∫ ω, (nsfAlive b E q K u₁ W j).indicator
      (fun ω => (polyValue b E (noTags W) (fun _ => q) W j ω (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N))).re) ω ∂growthPathLaw W b) hr0 hrPre hrUp (hrC j₂ h12) hTel' hcard hRW
    hPn hNn hSeq hYle hθ he0 hc0 (by positivity) hL0 (mul_nonneg hδ.le hK.le)
    hsmall

/-- **`NsfStoppedWordEnergy` from the summed contract and the exit and stop-removal
inequality.** Inputs: `ContractingWordsContract.summed` (stopped one-step drift),
`FullSourceStopsContract.supMoments` (integrability of `Φ_π(A_j)` only),
`ConditionalBlockGUECount` (a.s. unitarity) and `NssStoppedExitRemoval` (proved from
`FullSourceGeneratorContract`, `ConditionalBlockGUECount` and `FullSourceStopsContract` as
`nssStoppedExitRemoval_holds`).
-/
theorem nsfStoppedWordEnergy_of_exitRemoval (hCW : ContractingWordsContract)
    (hStops : FullSourceStopsContract)
    (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hR : NssStoppedExitRemoval) : NsfStoppedWordEnergy := by
  intro b hb hb1 E hE hE' p hp hp1 t₁ R q hq ε hε u₁ u₂ hu₁ hu₂ θ hθ
  have hq0 : ∀ x, 0 ≤ q x := hq.2.2.2.1.1
  have hqoff : ∀ x, t₁ + R < x → q x = 0 := fun x hx =>
    hq.2.2.2.1.2.1 x fun h => by linarith [h.2]
  have hu₁0 : 0 < u₁ := by linarith [hq.1, hq.2.1]
  have hIT : IsIntervalTests (fun _ : Fin 1 => q) := fun _ => ⟨t₁, t₁ + R, hq.2.2.2.1⟩
  obtain ⟨K, hK, δR, hδR, hRK⟩ :=
    hR b hb hb1 E hE hE' p hp hp1 t₁ R q hq ε hε u₁ u₂ hu₁ hu₂ (θ / 2) (by positivity)
  have hD := (ns_transportD0_pos hb hE hE').le
  have hκ2 : 0 ≤ K / 2 * K + K ^ 2 := by positivity
  have hL0 : 0 ≤ u₂ - u₁ + 1 := by linarith
  have hB0 : 0 < transportD0 b E / 2 * (K / 2 * K + K ^ 2) * (u₂ - u₁ + 1) + K + 1 := by
    positivity
  refine ⟨K, hK, min δR (θ / (4 * (transportD0 b E / 2 * (K / 2 * K + K ^ 2) *
    (u₂ - u₁ + 1) + K + 1))), lt_min hδR (by positivity), ?_⟩
  intro δ hδ hδle a N h1 h2
  have hδR' : δ ≤ δR := hδle.trans (min_le_left _ _)
  have hδsmall : δ * K + (u₂ - u₁ + 1) * (transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2)) ≤
      θ / 4 := by
    have h := hδle.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  obtain ⟨Cs, Ws, hs⟩ := hCW.summed b hb hb1 E hE hE' 0 1 (fun _ => q) hIT (nsfClockPoly a N)
    (nsf_isOrdinaryPoly_clockPoly a N) (u₁ / 2) (u₂ + 1) K (by positivity) (by linarith)
  obtain ⟨Cm, Wm, hm⟩ := hStops.supMoments b hb hb1 E hE hE' 0 1 (fun _ => q) hIT (u₁ / 2)
    (u₂ + 1) ((N + 1 : ℕ) : ℝ) (by positivity) (by linarith) (by positivity)
  set c := transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2) with hc
  set C₀ := transportD0 b E / 2 * nssGenConst p ε * (K / 2 * K + K ^ 2) with hC₀
  have hc0 : 0 ≤ c := by positivity
  have hC₀0 : 0 ≤ C₀ := by
    have : 0 ≤ nssGenConst p ε :=
      (mul_nonneg hp.le (Real.rpow_nonneg hε.le _)).trans (le_max_left _ _)
    positivity
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
  filter_upwards [hRK δ hδ hδR' a N (fun x hx => (h1 x hx).1), eventually_ge_atTop Ws,
    eventually_ge_atTop Wm, eventually_gt_atTop 0, eventually_ge_atTop ⌈2 / u₁⌉₊,
    (tendsto_order.1 htend).2 (θ / 4) (by positivity)] with W hRW hWs hWm hW0 hWu hWe
  have hP := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW0
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW0
  have hWu' : 2 / u₁ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWu)
  set j₁ := ⌊(W : ℝ) * u₁⌋₊ with hj₁
  set j₂ := ⌊(W : ℝ) * u₂⌋₊ with hj₂
  have h12 : j₁ ≤ j₂ := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hu₂ hW'.le)
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
  -- integrability of the clock polynomial
  have hFint : ∀ j, j₁ ≤ j → j ≤ j₂ → Integrable
      (fun ω => polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N))
      (growthPathLaw W b) := by
    intro j hj1 hj2
    refine nss_integrable_polyValue_clockPoly b E hq0 (noTags W) a N ?_
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
        polyValue b E (noTags W) (fun _ => q) W (j + 1) ω (nsfClockPoly a N) -
          polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N)) | growthSigma W j] ω -
        (W : ℂ)⁻¹ * polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N))) ω‖ₑ
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
  exact nss_reduction_fixedW hCount hb hb1 hE hE' hp hp1 hε hq0 hu₁0 hu₂ hK hδ hθ h1 h2 hW0 hjW
    hqt hFint (le_max_right _ _) hsum hRW
    (by rw [hc, hC₀] at hWe; rw [hc] at hδsmall; linarith)

/-!
## The composite
-/

/-- `NearSchattenDecayContract` from `ClockFractionalEntranceContract`,
`FullSourceGeneratorContract`, `ConditionalBlockGUECount`, `ContractingWordsContract`,
`FullSourceStopsContract` and `NssStoppedExitRemoval`.
-/
theorem nearSchattenDecay_of_chain (hEnt : ClockFractionalEntranceContract)
    (hGen : FullSourceGeneratorContract)
    (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hCW : ContractingWordsContract) (hStops : FullSourceStopsContract)
    (hR : NssStoppedExitRemoval) : NearSchattenDecayContract :=
  nearSchattenDecay_of_stoppedWordEnergy hEnt hGen hCount
    (nsfStoppedWordEnergy_of_exitRemoval hCW hStops hCount hR)

end BlockBand.Endpoints
