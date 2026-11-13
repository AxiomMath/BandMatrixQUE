module

public import BlockBand.Endpoints.Response.NearSchattenExitValue
public import BlockBand.Endpoints.Response.NearSchattenExitMass

/-!
# The exit and stop removal of the near-Schatten stopped energy

Part of the proof of the near-Schatten decay theorem: on a trace stop, the fixed clock/current
moments remove the stops.

**Proved here.**
* `nsx_afterStop_small`: the after-stop dissipation mass
  `Σ_{j₁≤j≤j₂} W⁻¹ E[1{j≥σ_K}(-𝒢_ε(j))⁺]` is `≤ θ` for every `K ≥ K₀(θ)` and all large `W`
  (`compensatorUI` for the drift of `Tr(QP)`, `supMoments` for `(sup Tr Q)²`, `tail` for
  `P(σ_K ≤ j₂)`; a.s. unitarity from `ConditionalBlockGUECount`).
* `nsx_endValue_small`: the end value `E[1{σ_K≤j₂} sup Tr Q]` is `≤ θ` for every `K ≥ K₀(θ)` and
  all large `W` (`supMoments`, `tail`).
* `nsx_jump_value_small`: for a fixed polynomial, the exit overshoot
  `(Σ|a_r|)(P(J) + E[1_J (sup Tr Q)^{N+1}])` on the jump event `J` is `≤ θ` for all large `W`
  (`FullSourceGeneratorContract.tight` at modulus `η = 1`, `supMoments`).
* `nssStoppedExitRemoval_holds`: the isolated `NssStoppedExitRemoval` from
  `FullSourceGeneratorContract`, `ConditionalBlockGUECount` and `FullSourceStopsContract`.
* `nearSchattenDecay_of_contracts`: `NearSchattenDecayContract` from
  `ClockFractionalEntranceContract`, `FullSourceGeneratorContract`, `ConditionalBlockGUECount`,
  `ContractingWordsContract` and `FullSourceStopsContract` (no isolated input).
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
## Bookkeeping
-/

/-- `ofReal c * X ≤ θ` from `X ≤ θ/(c+1)`. -/
theorem nsx_const_mul_le {X : ℝ≥0∞} {c θ : ℝ} (hc : 0 ≤ c) (hθ : 0 ≤ θ)
    (hX : X ≤ ENNReal.ofReal (θ / (c + 1))) : ENNReal.ofReal c * X ≤ ENNReal.ofReal θ := by
  calc ENNReal.ofReal c * X ≤ ENNReal.ofReal c * ENNReal.ofReal (θ / (c + 1)) := by gcongr
    _ = ENNReal.ofReal (c * (θ / (c + 1))) := (ENNReal.ofReal_mul hc).symm
    _ ≤ ENNReal.ofReal θ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

theorem nsx_ofReal_quarters {θ : ℝ} (hθ : 0 ≤ θ) :
    ENNReal.ofReal θ = ENNReal.ofReal (θ / 4) + ENNReal.ofReal (θ / 4) + ENNReal.ofReal (θ / 4) +
      ENNReal.ofReal (θ / 4) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

/-- The final `ℝ≥0∞` arithmetic. -/
theorem nsx_final_combine {Lf Diss Neg Pos x₁ x₂ x₃ : ℝ≥0∞} {θ : ℝ} (hθ : 0 ≤ θ)
    (hV : Lf + Neg ≤ Pos + (x₁ + x₂ + x₃)) (hD : Diss ≤ ENNReal.ofReal (θ / 4))
    (h1 : x₁ ≤ ENNReal.ofReal (θ / 4)) (h2 : x₂ ≤ ENNReal.ofReal (θ / 4))
    (h3 : x₃ ≤ ENNReal.ofReal (θ / 4)) : Lf + Diss + Neg ≤ Pos + ENNReal.ofReal θ := by
  rw [nsx_ofReal_quarters hθ]
  calc Lf + Diss + Neg = (Lf + Neg) + Diss := by ring
    _ ≤ Pos + (x₁ + x₂ + x₃) + Diss := by gcongr
    _ ≤ Pos + (ENNReal.ofReal (θ / 4) + ENNReal.ofReal (θ / 4) + ENNReal.ofReal (θ / 4)) +
        ENNReal.ofReal (θ / 4) := by gcongr
    _ = _ := by ring

/-- The index conditions for large `W`: `W > 0`, `u₁W/2 ≤ j₁`, and the source vanishes after
`j₁`. -/
theorem nsx_eventually_index {t₁ R : ℝ} {q : ℝ → ℝ} (hq : IsUnitSource t₁ R q) {u₁ : ℝ}
    (hu₁ : t₁ + R < u₁) :
    ∀ᶠ W : ℕ in atTop, 0 < W ∧ u₁ / 2 * W ≤ ⌊(W : ℝ) * u₁⌋₊ ∧
      ∀ j, ⌊(W : ℝ) * u₁⌋₊ ≤ j → q (((j + 1 : ℕ) : ℝ) / W) = 0 := by
  have hu₁0 : 0 < u₁ := by linarith [hq.1, hq.2.1]
  have hqoff : ∀ x, t₁ + R < x → q x = 0 := fun x hx =>
    hq.2.2.2.1.2.1 x fun h => by linarith [h.2]
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop ⌈2 / u₁⌉₊] with W hW0 hWu
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW0
  have hWu' : 2 / u₁ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWu)
  have hj₁lt : (W : ℝ) * u₁ < (⌊(W : ℝ) * u₁⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : 2 ≤ u₁ * W := by rw [div_le_iff₀ hu₁0] at hWu'; linarith
  refine ⟨hW0, by nlinarith, fun j hj1 => hqoff _ ?_⟩
  have h2 : (⌊(W : ℝ) * u₁⌋₊ : ℝ) ≤ j := by exact_mod_cast hj1
  rw [lt_div_iff₀ hW']
  push_cast
  nlinarith

/-!
## The three small terms
-/

/-- **The after-stop dissipation mass is small for large `K`.** -/
theorem nsx_afterStop_small (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hStops : FullSourceStopsContract) {b E p ε : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2)
    (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) {t₁ R : ℝ}
    {q : ℝ → ℝ} (hq : IsUnitSource t₁ R q) {u₁ u₂ : ℝ} (hu₁ : t₁ + R < u₁) (hu : u₁ ≤ u₂)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ᶠ W : ℕ in atTop,
      ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
          ∫⁻ ω, (nsfAlive b E q K u₁ W j)ᶜ.indicator
            (fun ω => ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω)) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal θ := by
  have hq0 : ∀ x, 0 ≤ q x := hq.2.2.2.1.1
  have hu₁0 : 0 < u₁ := by linarith [hq.1, hq.2.1]
  have hIT : IsIntervalTests (fun _ : Fin 1 => q) := fun _ => ⟨t₁, t₁ + R, hq.2.2.2.1⟩
  have hM : 0 ≤ nssGenConst p ε :=
    (mul_nonneg hp0 (Real.rpow_nonneg hε.le _)).trans (le_max_left _ _)
  have hD := (ns_transportD0_pos hb hE hE').le
  have hL : 0 ≤ (u₂ - u₁ + 2) * (transportD0 b E / 2 * nssGenConst p ε) := by
    have : 0 ≤ u₂ - u₁ + 2 := by linarith
    positivity
  have hUId : ∀ η : ℝ, 0 < η → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∫⁻ ω, {ω | ENNReal.ofReal M < nsxDrift b E q u₁ u₂ W ω}.indicator
        (nsxDrift b E q u₁ u₂ W) ω ∂growthPathLaw W b ≤ ENNReal.ofReal η := fun η hη => by
    obtain ⟨M, W₀, h⟩ := hStops.compensatorUI b hb hb1 E hE hE' 0 1 (fun _ => q) hIT
      nsxClockOne nsx_isOrdinaryPoly_clockOne (u₁ / 2) (u₂ + 1) η (by positivity) (by linarith) hη
    exact ⟨M, W₀, fun W hW => (h W hW (noTags W)).1⟩
  have hUIS := nsx_ui_of_moment (b := b) (fun W ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ 2)
    (nsx_supQ_moment hStops hb hb1 hE hE' hIT (by positivity : 0 < u₁ / 2) (by linarith) 1)
  obtain ⟨K₁, hK₁, h1⟩ := nsx_dead_small hStops hb hb1 hE hE' hIT hu₁0 hu _ hUId
    (θ := θ / 2 / (nssGenConst p ε + 1)) (by positivity)
  obtain ⟨K₂, hK₂, h2⟩ := nsx_dead_small hStops hb hb1 hE hE' hIT hu₁0 hu _ hUIS
    (θ := θ / 2 / ((u₂ - u₁ + 2) * (transportD0 b E / 2 * nssGenConst p ε) + 1))
    (by positivity)
  refine ⟨max K₁ K₂, lt_max_of_lt_left hK₁, fun K hK => ?_⟩
  filter_upwards [h1 K ((le_max_left _ _).trans hK), h2 K ((le_max_right _ _).trans hK),
    nsx_eventually_index hq hu₁] with W hW1 hW2 ⟨hW0, hjW, hqt⟩
  refine (nsx_mass_le hCount hb hb1 hE hE' hp0 hp1 hε hq0 hu₁0 hu hW0 hjW hqt).trans ?_
  calc _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
        add_le_add (nsx_const_mul_le hM (by positivity) hW1)
          (nsx_const_mul_le hL (by positivity) hW2)
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- **The end value is small for large `K`.** -/
theorem nsx_endValue_small (hStops : FullSourceStopsContract) {b E : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {t₁ R : ℝ} {q : ℝ → ℝ}
    (hq : IsUnitSource t₁ R q) {u₁ u₂ : ℝ} (hu₁ : t₁ + R < u₁) (hu : u₁ ≤ u₂) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ᶠ W : ℕ in atTop,
      ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
          (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ 1) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal θ := by
  have hu₁0 : 0 < u₁ := by linarith [hq.1, hq.2.1]
  have hIT : IsIntervalTests (fun _ : Fin 1 => q) := fun _ => ⟨t₁, t₁ + R, hq.2.2.2.1⟩
  exact nsx_dead_small hStops hb hb1 hE hE' hIT hu₁0 hu _
    (nsx_ui_of_moment (b := b) (fun W ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ 1)
      (nsx_supQ_moment hStops hb hb1 hE hE' hIT (by positivity : 0 < u₁ / 2) (by linarith) 0))
    hθ

/-- **The exit overshoot is small for a fixed polynomial.** -/
theorem nsx_jump_value_small (hGen : FullSourceGeneratorContract)
    (hStops : FullSourceStopsContract) {b E : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2) (hE : -2 < E)
    (hE' : E < 2) {t₁ R : ℝ} {q : ℝ → ℝ} (hq : IsUnitSource t₁ R q) {u₁ u₂ : ℝ}
    (hu₁ : t₁ + R < u₁) (hu : u₁ ≤ u₂) (A : ℝ) (hA : 0 ≤ A) (N : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ W : ℕ in atTop, ENNReal.ofReal A * (growthPathLaw W b (nsxJump b E q u₁ u₂ W) +
        ∫⁻ ω, (nsxJump b E q u₁ u₂ W).indicator
          (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (N + 1)) ω ∂growthPathLaw W b) ≤
      ENNReal.ofReal θ := by
  have hu₁0 : 0 < u₁ := by linarith [hq.1, hq.2.1]
  have hIT : IsIntervalTests (fun _ : Fin 1 => q) := fun _ => ⟨t₁, t₁ + R, hq.2.2.2.1⟩
  have hρ : 0 < θ / (A + 1) / 2 := by positivity
  filter_upwards [nsx_eventually_jump_le hGen hb hb1 hE hE' hq hu₁ hu hρ,
    nsx_jump_small hGen hb hb1 hE hE' hq hu₁ hu _
      (nsx_ui_of_moment (b := b) (fun W ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (N + 1))
        (nsx_supQ_moment hStops hb hb1 hE hE' hIT (by positivity : 0 < u₁ / 2) (by linarith) N))
      hρ] with W hW1 hW2
  refine nsx_const_mul_le hA hθ.le ((add_le_add hW1 hW2).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_add hρ.le hρ.le]; congr 1; ring

/-!
## The isolated clause and the composite
-/

/-- **`NssStoppedExitRemoval`**: the exit value, the end value and the after-stop dissipation of
the stopped clock, from `FullSourceGeneratorContract` (`tight`, one-step form for the word
`Tr(QP)`), `ConditionalBlockGUECount` (a.s. unitarity of `𝕊`) and `FullSourceStopsContract`
(`tail`, `supMoments`, `compensatorUI`). Order of choices: `K` (end value and after-stop mass,
uniform in `π`), then `δ₀ = θ/(4(K+1))`, then `π`, then `W` (exit overshoot on the jump event). -/
theorem nssStoppedExitRemoval_holds (hGen : FullSourceGeneratorContract)
    (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hStops : FullSourceStopsContract) : NssStoppedExitRemoval := by
  intro b hb hb1 E hE hE' p hp hp1 t₁ R q hq ε hε u₁ u₂ hu₁ hu₂ θ hθ
  have hq0 : ∀ x, 0 ≤ q x := hq.2.2.2.1.1
  have hu₁0 : 0 < u₁ := by linarith [hq.1, hq.2.1]
  have hc₀ : 0 ≤ p * ε ^ (p - 1) := mul_nonneg hp.le (Real.rpow_nonneg hε.le _)
  obtain ⟨K₁, hK₁, hA⟩ := nsx_afterStop_small hCount hStops hb hb1 hE hE' hp.le hp1.le hε
    (p := p) (ε := ε) hq hu₁ hu₂ (θ := θ / 4) (by positivity)
  obtain ⟨K₂, hK₂, hB⟩ := nsx_endValue_small hStops hb hb1 hE hE' hq hu₁ hu₂
    (θ := θ / 4 / (p * ε ^ (p - 1) + 1)) (by positivity)
  set K := max K₁ K₂ with hKdef
  have hK : 0 < K := lt_max_of_lt_left hK₁
  refine ⟨K, hK, θ / (4 * (K + 1)), by positivity, fun δ hδ hδle a N h0 => ?_⟩
  have hδK : δ * (K + 1) ≤ θ / 4 := by
    rw [le_div_iff₀ (by positivity)] at hδle
    nlinarith
  have hAπ : 0 ≤ ∑ r ∈ range N, |a r| := Finset.sum_nonneg fun r _ => abs_nonneg _
  filter_upwards [hA K (le_max_left _ _), hB K (le_max_right _ _),
    nsx_jump_value_small hGen hStops hb hb1 hE hE' hq hu₁ hu₂ _ hAπ N (θ := θ / 4)
      (by positivity),
    nsx_eventually_index hq hu₁] with W hWA hWB hWJ ⟨hW0, hjW, _⟩
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW0
  have h12 : ⌊(W : ℝ) * u₁⌋₊ ≤ ⌊(W : ℝ) * u₂⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left hu₂ hW'.le)
  have hj₂T : (⌊(W : ℝ) * u₂⌋₊ : ℝ) ≤ (u₂ + 1) * W := by
    have := Nat.floor_le (mul_nonneg hW'.le (show 0 ≤ u₂ by linarith))
    nlinarith
  have hV := nsx_value_le (b := b) (E := E) hp.le hp1.le hε hq0 hδ.le h0 hjW h12 hj₂T
  exact nsx_final_combine hθ.le hV hWA (ENNReal.ofReal_le_ofReal hδK)
    (nsx_const_mul_le hc₀ (by positivity) hWB) hWJ

/-- **The near-Schatten decay theorem**: `NearSchattenDecayContract` from
`ClockFractionalEntranceContract`, `FullSourceGeneratorContract`, `ConditionalBlockGUECount`,
`ContractingWordsContract` and `FullSourceStopsContract`, with no isolated input
(`nearSchattenDecay_of_chain` with `nssStoppedExitRemoval_holds`). -/
theorem nearSchattenDecay_of_contracts (hEnt : ClockFractionalEntranceContract)
    (hGen : FullSourceGeneratorContract)
    (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hCW : ContractingWordsContract) (hStops : FullSourceStopsContract) :
    NearSchattenDecayContract :=
  nearSchattenDecay_of_chain hEnt hGen hCount hCW hStops
    (nssStoppedExitRemoval_holds hGen hCount hStops)

end BlockBand.Endpoints
