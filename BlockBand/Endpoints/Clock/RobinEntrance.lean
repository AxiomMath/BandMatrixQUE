module

public import BlockBand.Endpoints.Clock.RobinEntrancePhase
public import BlockBand.Endpoints.Clock.NegativeClock

/-!
# The Robin entrance lemma: the closed-port reduction

## Main results

* `robinEntranceLimitUpTo_of (h1 : OpenClockLawUniformInitial) : RobinEntranceLimitUpTo`, the
  closed-port reduction: the closed far port `λ_θ`, the effective initial matrix
  `X₀ = λ_θ⁻¹B₀B₀*` on the one-ended chain, the exact identification of the closed-port clock
  with the one-ended clock started at `X₀`, the Gaussian cutoff `‖B₀‖ < 7`, uniformity in `θ`
  with a uniform interval length `ℓ`, and re-indexing along `ClockSequence` widths.
* `negativeClock_of_upTo (hFSM) (hRobin : RobinEntranceLimitUpTo) : NegativeClockContract`.
* `robinEntranceLimitUpTo_of_robinEntranceLimit : RobinEntranceLimit → RobinEntranceLimitUpTo`.

## Hypotheses

* `OpenClockLawUniformInitial` (h1): the total-mass open-clock law from `X₀ = D` uniformly in
  Hermitian `‖D‖ ≤ ε`, along moving energies, with `ε` uniform on compact `(b, E)` sets and a
  horizon.
* `FullSourceMomentsEnergyUniformContract` (for `negativeClock_of_upTo` only).

The zero-entrance lemma is not a hypothesis of the reduction: it enters only through the
uniform-in-`D` inputs of the open-clock law, i.e. through h1.

## The horizon

`RobinEntranceLimit` asks for one interval per `(b, E)` valid for all `τ > 0`. The proof chooses
`Λ ≥ K²/ε` with `ε` depending on the moment family, hence on the horizon; the interval may be
chosen separately for a fixed set of moment bounds. With `ε` depending on the horizon the reduction
therefore yields `RobinEntranceLimitUpTo`, which is implied by `RobinEntranceLimit` and suffices for
`NegativeClockContract` (`negativeClock_of_upTo`).

Norms are `ℓ²` operator norms on matrices.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology Real
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.CoareaPalm
  BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator BoundedContinuousFunction

namespace RobinEntrance

/-!
## 1. Re-indexing along clock sequences
-/

/-- **Re-indexing along clock sequences.** A property that holds eventually in the width `W` along *every* width-indexed family (`n_W/W → τ`, `n_W ≤ TW`, `E_W → E` in the
bulk interval) holds eventually along every `ClockSequence` (widths `W_j → ∞`, possibly
repeating, energies eventually in the bulk interval).
Proof: a failing subsequence with strictly
increasing widths is completed to a width-indexed family by `n_W = ⌊τW⌋`, `E_W = E`.
-/
theorem eventually_seq_of_eventually_width {κ T τ E : ℝ} (hE : E ∈ bulkInterval κ)
    (hτ : 0 < τ) (hτT : τ < T) (P : (W : ℕ) → ℕ → ℝ → Prop)
    (hOC : ∀ (n : ℕ → ℕ) (Es : ℕ → ℝ), Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 τ) →
      (∀ W, (n W : ℝ) ≤ T * W) → Tendsto Es atTop (𝓝 E) → (∀ W, Es W ∈ bulkInterval κ) →
      ∀ᶠ W in atTop, P W (n W) (Es W))
    (s : ClockSequence τ E) (hev : ∀ᶠ j in atTop, s.energy j ∈ bulkInterval κ) :
    ∀ᶠ j in atTop, P (s.W j) (s.n j) (s.energy j) := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hT : ∀ᶠ j in atTop, (s.n j : ℝ) ≤ T * s.W j := by
    filter_upwards [s.ratio_tendsto.eventually (gt_mem_nhds hτT)] with j hj
    have hW : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
    rw [div_lt_iff₀ hW] at hj; linarith
  set Q : ℕ → Prop := fun j => ¬ P (s.W j) (s.n j) (s.energy j) ∧
    (s.energy j ∈ bulkInterval κ ∧ (s.n j : ℝ) ≤ T * s.W j) with hQdef
  have hQ : ∃ᶠ j in atTop, Q j := hcon.and_eventually (hev.and hT)
  have hnext : ∀ N c : ℕ, ∃ j, N ≤ j ∧ c < s.W j ∧ Q j := by
    intro N c
    obtain ⟨j, hj⟩ := (hQ.and_eventually ((s.width_tendsto.eventually_gt_atTop c).and
      (eventually_ge_atTop N))).exists
    exact ⟨j, hj.2.2, hj.2.1, hj.1⟩
  choose nx hnx1 hnx2 hnx3 using hnext
  let φ : ℕ → ℕ := fun k => Nat.rec (nx 0 0) (fun _ φk => nx (φk + 1) (s.W φk)) k
  have hφs : ∀ k, φ (k + 1) = nx (φ k + 1) (s.W (φ k)) := fun k => rfl
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun k => by
    rw [hφs]; exact lt_of_lt_of_le (Nat.lt_succ_self _) (hnx1 _ _)
  have hWφ : StrictMono (fun k => s.W (φ k)) := strictMono_nat_of_lt_succ fun k => by
    show s.W (φ k) < s.W (φ (k + 1))
    rw [hφs]; exact hnx2 _ _
  have hQφ : ∀ k, Q (φ k) := fun k => by
    cases k with
    | zero => exact hnx3 0 0
    | succ k => rw [hφs]; exact hnx3 _ _
  have hfind : ∀ k (h : ∃ k', s.W (φ k') = s.W (φ k)), Nat.find h = k := fun k h =>
    hWφ.injective (Nat.find_spec h)
  let nW : ℕ → ℕ := fun w => if h : ∃ k, s.W (φ k) = w then s.n (φ (Nat.find h)) else ⌊τ * w⌋₊
  let EW : ℕ → ℝ := fun w => if h : ∃ k, s.W (φ k) = w then s.energy (φ (Nat.find h)) else E
  have hlarge : ∀ K w (h : ∃ k, s.W (φ k) = w), s.W (φ K) ≤ w → K ≤ Nat.find h := by
    intro K w h hw
    by_contra hlt
    have h1 := hWφ (lt_of_not_ge hlt)
    have h2 := Nat.find_spec h
    simp only at h1
    omega
  have hfl : Tendsto (fun w : ℕ => ((⌊τ * (w : ℝ)⌋₊ : ℕ) : ℝ) / (w : ℝ)) atTop (𝓝 τ) :=
    (tendsto_nat_floor_mul_div_atTop hτ.le).comp tendsto_natCast_atTop_atTop
  have hn : Tendsto (fun w => (nW w : ℝ) / w) atTop (𝓝 τ) := by
    rw [Metric.tendsto_atTop]
    intro ε' hε'
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp (s.ratio_tendsto.comp hφ.tendsto_atTop) ε' hε'
    obtain ⟨w₁, hw₁⟩ := Metric.tendsto_atTop.mp hfl ε' hε'
    refine ⟨max w₁ (s.W (φ K)), fun w hw => ?_⟩
    by_cases h : ∃ k, s.W (φ k) = w
    · simp only [nW]
      rw [dite_eq_left h]
      have hk := Nat.find_spec h
      have := hK (Nat.find h) (hlarge K w h (le_of_max_le_right hw))
      have e : (w : ℝ) = s.W (φ (Nat.find h)) := by exact_mod_cast hk.symm
      rw [e]
      exact this
    · simp only [nW]; rw [dite_eq_right h]
      exact hw₁ w (le_of_max_le_left hw)
  have hEW : Tendsto EW atTop (𝓝 E) := by
    rw [Metric.tendsto_atTop]
    intro ε' hε'
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp (s.energy_tendsto.comp hφ.tendsto_atTop) ε' hε'
    refine ⟨s.W (φ K), fun w hw => ?_⟩
    by_cases h : ∃ k, s.W (φ k) = w
    · simp only [EW]; rw [dite_eq_left h]
      exact hK (Nat.find h) (hlarge K w h hw)
    · simp only [EW]; rw [dite_eq_right h, dist_self]
      exact hε'
  have hnT : ∀ w, (nW w : ℝ) ≤ T * w := by
    intro w
    by_cases h : ∃ k, s.W (φ k) = w
    · simp only [nW]; rw [dite_eq_left h]
      have hk := Nat.find_spec h
      have := (hQφ (Nat.find h)).2.2
      rw [hk] at this
      exact this
    · simp only [nW]; rw [dite_eq_right h]
      have h0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
      calc ((⌊τ * (w : ℝ)⌋₊ : ℕ) : ℝ) ≤ τ * w := Nat.floor_le (by positivity)
        _ ≤ T * w := mul_le_mul_of_nonneg_right hτT.le h0
  have hEb : ∀ w, EW w ∈ bulkInterval κ := by
    intro w
    by_cases h : ∃ k, s.W (φ k) = w
    · simp only [EW]; rw [dite_eq_left h]; exact (hQφ (Nat.find h)).2.1
    · simp only [EW]; rw [dite_eq_right h]; exact hE
  obtain ⟨w₀, hw₀⟩ := eventually_atTop.mp (hOC nW EW hn hnT hEW hEb)
  have hP := hw₀ (s.W (φ w₀)) (hWφ.id_le w₀)
  have hex : ∃ k, s.W (φ k) = s.W (φ w₀) := ⟨w₀, rfl⟩
  simp only [nW, EW] at hP
  rw [dite_eq_left hex, dite_eq_left hex, hfind w₀ hex] at hP
  exact (hQφ w₀).1 hP

/-!
## 2. The horizon form and the reduction
-/

/-- Statement. `β, κ, T` first (`b ∈ [β, 1/2 - β]`, `E ∈ bulkInterval κ`, horizon `T`); then one
`ε > 0`; for every such `b, E`, every `τ ∈ (0, T]`, path lengths `n_W` with `n_W/W → τ`,
`n_W ≤ TW`, and energies `E_W → E` in `bulkInterval κ`: for every bounded continuous `f` and
`δ > 0`, eventually in `W`, **for all** deterministic Hermitian `D` with `‖D‖ ≤ ε` (`ℓ²` operator
norm), `|E f(g*Q^1_{n_W}g) - E f(X_τ)| ≤ δ`, where `Q^1_{n_W}` is the one-ended clock
(weight `1`, `Y₀ = 0`) of `n_W` fresh layers at energy `E_W` started at `X₀ = D`
(`openProbeLawFrom`), and `X_τ = d∫₀^τ e^{√D₀B_s - D₀s/2}ds` at the base energy
(`openClockLaw b E τ`, `d = (1-b)⁻¹`, `D₀ = 2/(b(4-E²))`). -/
def OpenClockLawUniformInitial : Prop :=
  ∀ β κ T : ℝ, 0 < β → β < 1 / 4 → 0 < κ → 0 < T → ∃ ε : ℝ, 0 < ε ∧
    ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ E ∈ bulkInterval κ, ∀ τ : ℝ, 0 < τ → τ ≤ T →
      ∀ (n : ℕ → ℕ) (Es : ℕ → ℝ), Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 τ) →
        (∀ W, (n W : ℝ) ≤ T * W) → Tendsto Es atTop (𝓝 E) → (∀ W, Es W ∈ bulkInterval κ) →
          ∀ f : ℝ →ᵇ ℝ, ∀ δ : ℝ, 0 < δ → ∀ᶠ W in atTop,
            ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
              |∫ x, f x ∂openProbeLawFrom W b (Es W) D (n W) - ∫ x, f x ∂openClockLaw b E τ| ≤ δ

/-- **The Robin entrance lemma**, in the moving-energy form of
`RobinEntranceLimit`, **with a horizon**: for compact parameter sets and a
horizon `T₀` there is a uniform `ℓ > 0` and, for each `b, E`, a phase interval
`[θ₁, θ₂] ⊆ [0, 2π]` of length `≥ ℓ`, independent of `W`, such that along every clock sequence
with `τ ∈ (0, T₀]` and energies eventually in `bulkInterval κ`, the closed-port clock law
converges to the law of `X_τ` uniformly in `θ ∈ [θ₁, θ₂]`. -/
def RobinEntranceLimitUpTo : Prop :=
  ∀ β κ T₀ : ℝ, 0 < β → β < 1 / 4 → 0 < κ → 0 < T₀ → ∃ ℓ : ℝ, 0 < ℓ ∧
    ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ E ∈ bulkInterval κ,
      ∃ θ₁ θ₂ : ℝ, 0 ≤ θ₁ ∧ θ₁ + ℓ ≤ θ₂ ∧ θ₂ ≤ 2 * π ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ s : ClockSequence τ E,
          (∀ᶠ j in atTop, s.energy j ∈ bulkInterval κ) →
          ∀ f : ℝ →ᵇ ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ θ ∈ Set.Icc θ₁ θ₂,
            |∫ x, f x ∂closedClockLaw (s.W j) b (s.energy j) (s.n j) θ -
              ∫ x, f x ∂openClockLaw b E τ| ≤ ε

/-- `RobinEntranceLimit` implies the horizon form `RobinEntranceLimitUpTo`. -/
theorem robinEntranceLimitUpTo_of_robinEntranceLimit (h : RobinEntranceLimit) :
    RobinEntranceLimitUpTo := by
  intro β κ T₀ hβ hβ4 hκ _
  obtain ⟨ℓ, hℓ, hI⟩ := h β κ hβ hβ4 hκ
  refine ⟨ℓ, hℓ, fun b hb E hE => ?_⟩
  obtain ⟨θ₁, θ₂, h0, h12, h2, hc⟩ := hI b hb E hE
  exact ⟨θ₁, θ₂, h0, h12, h2, fun τ hτ _ s hs => hc τ hτ s hs⟩

instance isProbabilityMeasure_openProbeLawFrom (W : ℕ) (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : IsProbabilityMeasure (openProbeLawFrom W b E D j) := by
  unfold openProbeLawFrom; infer_instance

instance isProbabilityMeasure_openClockLaw (b E τ : ℝ) :
    IsProbabilityMeasure (openClockLaw b E τ) := by
  unfold openClockLaw; infer_instance

/-- Moving energies move `λ_θ` by little, uniformly on the phase interval. -/
theorem eventually_robinLam_ge {β κ b E Λ τ : ℝ} (hκ : 0 < κ) (hb : b ∈ Set.Icc β (1 / 2 - β))
    (hβ : 0 < β) (hE : E ∈ bulkInterval κ) (hΛ : 0 < Λ) (s : ClockSequence τ E)
    (hev : ∀ᶠ j in atTop, s.energy j ∈ bulkInterval κ) :
    ∀ᶠ j in atTop, ∀ θ ∈ Set.Icc (robinTheta b E Λ) (robinTheta b E (2 * Λ)),
      Λ / 2 ≤ robinLam b (s.energy j) θ := by
  have hb' : β ≤ b ∧ b ≤ 1 / 2 - β := hb
  have hb0 : 0 ≤ b := by linarith
  have hb1 : b ≤ 1 / 2 := by linarith
  obtain ⟨hηlo, -, hx⟩ := etaZ_bounds hb0 hb1 hκ hE
  have hη : 0 < etaZ b E := lt_of_lt_of_le (by positivity) hηlo
  have hE' : -2 + κ ≤ E ∧ E ≤ 2 - κ := hE
  set V : ℝ := (2 * Λ + 2) / (κ / 4) with hV
  have hV0 : 0 ≤ V := by positivity
  -- convergence of `Re z` and `η` along the energies
  have hxT : Tendsto (fun j => (boundaryZ b (s.energy j)).re) atTop
      (𝓝 (boundaryZ b E).re) := by
    have h1 : Tendsto (fun j => -(1 + b) * s.energy j / 2) atTop (𝓝 (-(1 + b) * E / 2)) :=
      ((s.energy_tendsto.const_mul (-(1 + b))).div_const 2)
    rw [re_boundaryZ_eq (by linarith) (by linarith)]
    refine h1.congr' ?_
    filter_upwards [hev] with j hj
    have hj' : -2 + κ ≤ s.energy j ∧ s.energy j ≤ 2 - κ := hj
    rw [re_boundaryZ_eq (by linarith) (by linarith)]
  have hηT : Tendsto (fun j => etaZ b (s.energy j)) atTop (𝓝 (etaZ b E)) := by
    have h1 : Tendsto (fun j => (1 - b) * Real.sqrt (4 - s.energy j ^ 2) / 2) atTop
        (𝓝 ((1 - b) * Real.sqrt (4 - E ^ 2) / 2)) :=
      (((Real.continuous_sqrt.tendsto _).comp
        (tendsto_const_nhds.sub (s.energy_tendsto.pow 2))).const_mul (1 - b)).div_const 2
    rw [etaZ_eq (by linarith) (by linarith)]
    refine h1.congr' ?_
    filter_upwards [hev] with j hj
    have hj' : -2 + κ ≤ s.energy j ∧ s.energy j ≤ 2 - κ := hj
    rw [etaZ_eq (by linarith) (by linarith)]
  have h1 := (Metric.tendsto_nhds.mp hxT) (Λ / 4) (by positivity)
  have h2 := (Metric.tendsto_nhds.mp hηT) (Λ / (4 * (V + 1))) (by positivity)
  filter_upwards [h1, h2] with j hj1 hj2 θ hθ
  rw [Real.dist_eq] at hj1 hj2
  obtain ⟨ht1, ht2⟩ := tan_mem_of_mem hθ
  obtain ⟨hl1, -⟩ := robinLam_mem_of_mem hη hθ
  set t := Real.tan ((θ - π) / 2)
  have htV : |t| ≤ V := by
    have e1 : |t| ≤ (2 * Λ + |(boundaryZ b E).re|) / etaZ b E := by
      rw [abs_le]
      constructor
      · have : -((2 * Λ + |(boundaryZ b E).re|) / etaZ b E) ≤
            (Λ - (boundaryZ b E).re) / etaZ b E := by
          rw [← neg_div]
          refine div_le_div_of_nonneg_right ?_ hη.le
          have := le_abs_self (boundaryZ b E).re
          linarith
        linarith
      · refine ht2.trans (div_le_div_of_nonneg_right ?_ hη.le)
        have := le_abs_self (-(boundaryZ b E).re)
        rw [abs_neg] at this
        linarith
    refine e1.trans ?_
    rw [hV]
    exact div_le_div₀ (by positivity) (by linarith) (by positivity) hηlo
  have hdiff : robinLam b (s.energy j) θ = robinLam b E θ +
      ((boundaryZ b (s.energy j)).re - (boundaryZ b E).re) +
        (etaZ b (s.energy j) - etaZ b E) * t := by
    unfold robinLam; ring
  have hbound : |(etaZ b (s.energy j) - etaZ b E) * t| ≤ Λ / 4 := by
    rw [abs_mul]
    calc |etaZ b (s.energy j) - etaZ b E| * |t| ≤ Λ / (4 * (V + 1)) * (V + 1) :=
          mul_le_mul hj2.le (by linarith) (abs_nonneg _) (by positivity)
      _ = Λ / 4 := by field_simp
  rw [hdiff]
  have := neg_abs_le ((boundaryZ b (s.energy j)).re - (boundaryZ b E).re)
  have := neg_abs_le ((etaZ b (s.energy j) - etaZ b E) * t)
  linarith

/-- Choice of constants: `ε` from `OpenClockLawUniformInitial` at horizon
`T₀ + 1`; cutoff `K = 7` (`ginibre_norm_tail`); `Λ = 98/ε` (so `K²/(Λ/2) = ε`); interval
`[θ(Λ), θ(2Λ)]`, on which `λ_θ ∈ [Λ, 2Λ]` at the base energy and `λ_θ ≥ Λ/2` at the moving
energies eventually, uniformly in `θ` (`eventually_robinLam_ge`); `ℓ = 2Λ(κ/4)/(1 + (2Λ+2)²)`.
At width `W_j`, for `θ` in the interval, `E f(closed clock) = ∫ E f(one-ended from
X₀(B₀)) dGin(B₀)` (`integral_closedClockLaw`); on `‖B₀‖ < 7`, `‖X₀‖ ≤ ε` and the re-indexed
label gives an error `≤ δ/2` (`eventually_seq_of_eventually_width`); the complement costs
`2‖f‖e^{-W_j}`. -/
theorem robinEntranceLimitUpTo_of (h1 : OpenClockLawUniformInitial) : RobinEntranceLimitUpTo := by
  intro β κ T₀ hβ hβ4 hκ hT₀
  obtain ⟨ε, hε, hOC⟩ := h1 β κ (T₀ + 1) hβ hβ4 hκ (by linarith)
  set Λ : ℝ := 98 / ε with hΛ
  have hΛ0 : 0 < Λ := by positivity
  set ℓ : ℝ := 2 * Λ * (κ / 4) / (1 + (2 * Λ + 2) ^ 2) with hℓ
  refine ⟨ℓ, by positivity, fun b hb E hE => ?_⟩
  have hb' : β ≤ b ∧ b ≤ 1 / 2 - β := hb
  have hb0 : 0 < b := by linarith
  have hb1 : b < 1 / 2 := by linarith
  obtain ⟨hηlo, hηhi, hx⟩ := etaZ_bounds hb0.le hb1.le hκ hE
  have hη : 0 < etaZ b E := lt_of_lt_of_le (by positivity) hηlo
  refine ⟨robinTheta b E Λ, robinTheta b E (2 * Λ), (robinTheta_pos _ _ _).le, ?_,
    (robinTheta_lt _ _ _).le, ?_⟩
  · -- the length of the phase interval
    have h := robinTheta_sub_ge hη hΛ0 (b := b) (E := E)
    have e : 2 * ((Λ / etaZ b E) / (1 + ((2 * Λ + |(boundaryZ b E).re|) / etaZ b E) ^ 2)) =
        2 * Λ * etaZ b E / (etaZ b E ^ 2 + (2 * Λ + |(boundaryZ b E).re|) ^ 2) := by
      field_simp
    rw [e] at h
    have h2 : ℓ ≤ 2 * Λ * etaZ b E / (etaZ b E ^ 2 + (2 * Λ + |(boundaryZ b E).re|) ^ 2) := by
      rw [hℓ]
      refine div_le_div₀ (by positivity) (by nlinarith) (by positivity) ?_
      have h3 : (2 * Λ + |(boundaryZ b E).re|) ^ 2 ≤ (2 * Λ + 2) ^ 2 := by
        have := abs_nonneg (boundaryZ b E).re
        nlinarith
      nlinarith
    linarith
  · intro τ hτ hτT s hev f δ hδ
    set m := ∫ x, f x ∂openClockLaw b E τ with hm
    have hB := eventually_seq_of_eventually_width hE hτ (by linarith : τ < T₀ + 1)
      (fun W n e => ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
        |∫ x, f x ∂openProbeLawFrom W b e D n - m| ≤ δ / 2)
      (fun n Es hn hnT hEs hEb => hOC b hb E hE τ hτ (by linarith) n Es hn hnT hEs hEb f (δ / 2)
        (by positivity)) s hev
    have hC : ∀ᶠ j in atTop, 2 * ‖f‖ * Real.exp (-(s.W j : ℝ)) < δ / 2 := by
      have hW : Tendsto (fun j => ((s.W j : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp s.width_tendsto
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hW).const_mul (2 * ‖f‖)
      rw [mul_zero] at h2
      exact h2.eventually (gt_mem_nhds (by positivity))
    filter_upwards [eventually_robinLam_ge hκ hb hβ hE hΛ0 s hev, hB, hC,
      eventually_half_le_ratio s hτ, hev] with j hA hBj hCj hDj hEj θ hθ
    have hEj' : -2 + κ ≤ s.energy j ∧ s.energy j ≤ 2 - κ := hEj
    have hθ0 : 0 < θ := lt_of_lt_of_le (robinTheta_pos _ _ _) hθ.1
    have hθ2 : θ < 2 * π := lt_of_le_of_lt hθ.2 (robinTheta_lt _ _ _)
    set lam := robinLam b (s.energy j) θ with hlam
    have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) (hA θ hθ)
    have hcl := phase_mul_closure b (s.energy j) hθ0 hθ2
    have hn := pos_of_half_le_ratio s hτ hDj
    obtain ⟨hInt, hEq⟩ := integral_closedClockLaw (W := s.W j) hb0 hb1 (by linarith)
      (by linarith) hn hlam0.ne' hcl f
    rw [hEq]
    have hG : MeasurableSet {B : Matrix (Fin (s.W j)) (Fin (s.W j)) ℂ | ‖B‖ < 7} :=
      measurableSet_lt continuous_norm.measurable measurable_const
    have hgood : ∀ B ∈ {B : Matrix (Fin (s.W j)) (Fin (s.W j)) ℂ | ‖B‖ < 7},
        |∫ x, f x ∂openProbeLawFrom (s.W j) b (s.energy j) (robinInitial lam B) (s.n j) - m|
          ≤ δ / 2 := by
      intro B hB7
      refine hBj _ (robinInitial_isHermitian lam B) ?_
      refine (norm_robinInitial_le hlam0 B).trans ?_
      have hB0 := norm_nonneg B
      have hB2 : ‖B‖ ^ 2 ≤ 49 := by
        have : ‖B‖ < 7 := hB7
        nlinarith
      have hl : Λ / 2 ≤ lam := hA θ hθ
      rw [div_le_iff₀ hlam0]
      have : ε * (Λ / 2) = 49 := by rw [hΛ]; field_simp; norm_num
      nlinarith
    have hall : ∀ B : Matrix (Fin (s.W j)) (Fin (s.W j)) ℂ,
        |∫ x, f x ∂openProbeLawFrom (s.W j) b (s.energy j) (robinInitial lam B) (s.n j) - m|
          ≤ 2 * ‖f‖ := by
      intro B
      have h1 := f.norm_integral_le_norm
        (μ := openProbeLawFrom (s.W j) b (s.energy j) (robinInitial lam B) (s.n j))
      have h2 := f.norm_integral_le_norm (μ := openClockLaw b E τ)
      rw [Real.norm_eq_abs] at h1 h2
      calc _ ≤ |∫ x, f x ∂openProbeLawFrom (s.W j) b (s.energy j) (robinInitial lam B) (s.n j)|
            + |m| := abs_sub _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add h1 h2
        _ = 2 * ‖f‖ := by ring
    have hsplit := abs_integral_sub_le_of_good hInt (by positivity : (0 : ℝ) ≤ δ / 2) hG hgood hall
    have hcompl : {B : Matrix (Fin (s.W j)) (Fin (s.W j)) ℂ | ‖B‖ < 7}ᶜ = {B | 7 ≤ ‖B‖} := by
      ext B; simp [not_lt]
    rw [hcompl] at hsplit
    have htail := ginibre_norm_tail (s.W_pos j) hb0 hb1.le
    have htail' : (ginibreMeasure (Fin (s.W j)) (Fin (s.W j)) (Real.toNNReal (b / s.W j))
        {B | 7 ≤ ‖B‖}).toReal ≤ Real.exp (-(s.W j : ℝ)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le htail
    have hf0 := norm_nonneg f
    nlinarith

open NegativeClockAssembly NegativeClockClosure in

/-- **The negative-clock theorem from the horizon form of the Robin entrance**: the proof of
`negativeClock_of`, with the interval taken at the horizon `T₀` of `NegativeClockContract`.
Hypotheses: `FullSourceMomentsEnergyUniformContract` and `RobinEntranceLimitUpTo`.
-/
theorem negativeClock_of_upTo (hFSM : FullSourceMomentsEnergyUniformContract)
    (hRobin : RobinEntranceLimitUpTo) : NegativeClockContract := by
  refine ⟨fun b hb0 hb1 E hE0 hE1 τ hτ s => negativeClock_tight hFSM hb0 hb1 hE0 hE1 hτ s, ?_⟩
  intro β κ T₀ p hβ hβ4 hκ hT₀ hp
  obtain ⟨ℓ, hℓ, hI⟩ := hRobin β κ T₀ hβ hβ4 hκ hT₀
  obtain ⟨CB, hCB0, hCB⟩ := negativeClock_openClock_negMoment β κ T₀ p hβ hβ4 hκ hT₀ hp
  refine ⟨(ℓ / (2 * π)) ^ (-p) * CB, fun b hb E hE τ hτ hτT s hev μ hμ => ?_⟩
  have hb' : β ≤ b ∧ b ≤ 1 / 2 - β := hb
  have hb0 : 0 < b := lt_of_lt_of_le hβ hb'.1
  have hb1 : b < 1 / 2 := lt_of_le_of_lt hb'.2 (by linarith)
  obtain ⟨θ₁, θ₂, h0, hℓ12, h2, hconv⟩ := hI b hb E hE
  have h12 : θ₁ < θ₂ := by linarith
  have hπ : 0 < 2 * π := by positivity
  have hℓa : ℓ / (2 * π) ≤ (θ₂ - θ₁) / (2 * π) := div_le_div_of_nonneg_right (by linarith) hπ.le
  have hℓ0 : 0 < ℓ / (2 * π) := div_pos hℓ hπ
  have ha0 : 0 < (θ₂ - θ₁) / (2 * π) := lt_of_lt_of_le hℓ0 hℓa
  obtain ⟨hprob, φ, hφ, hlim⟩ := hμ
  have hIio : μ (Set.Iio 0) = 0 :=
    negativeClock_limit_Iio_zero (ν := fun k => clockLaw (s.W (φ k)) b (scaledClock b s (φ k)))
      (fun k => clockLaw_scaledClock_Iio b s (φ k)) hlim
  set X := openClockFunctional b E τ with hXdef
  have hXm : Measurable X := measurable_openClockFunctional b E τ
  have hXpos : ∀ ω, 0 < X ω := openClockFunctional_pos (by linarith) E hτ
  -- Laplace domination in the limit
  have hL : ∀ s' : ℝ, 0 < s' → ∫ x, Real.exp (-(s' * max x 0)) ∂μ ≤
      ∫ ω, Real.exp (-(s' * ((θ₂ - θ₁) / (2 * π)) * X ω))
        ∂BlockBand.SourceProcess.canonicalWienerLaw := by
    intro s' hs'
    have hsa : 0 ≤ s' * ((θ₂ - θ₁) / (2 * π)) := mul_nonneg hs'.le ha0.le
    set m := ∫ x, expTest _ hsa x ∂openClockLaw b E τ with hm
    have hmX : m = ∫ ω, Real.exp (-(s' * ((θ₂ - θ₁) / (2 * π)) * X ω))
        ∂BlockBand.SourceProcess.canonicalWienerLaw := by
      rw [hm, openClockLaw, integral_map hXm.aemeasurable
        (expTest _ hsa).continuous.aestronglyMeasurable]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [expTest_apply, max_eq_left (hXpos ω).le]
    have hm0 : 0 ≤ m := integral_nonneg fun x => by rw [expTest_apply]; exact (Real.exp_pos _).le
    rw [← hmX]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hev1 := hconv τ hτ hτT s hev (expTest _ hsa) ε hε
    have hev2 := eventually_half_le_ratio s hτ
    have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have hbd : ∀ᶠ k in atTop, ∫ x, expTest s' hs'.le x
        ∂clockLaw (s.W (φ k)) b (scaledClock b s (φ k)) ≤ m + ε := by
      filter_upwards [hφt.eventually (hev1.and (hev2.and hev))] with k hk
      obtain ⟨hk1, hk2, hk3⟩ := hk
      have hn := pos_of_half_le_ratio s hτ hk2
      have hE' : -2 + κ ≤ s.energy (φ k) ∧ s.energy (φ k) ≤ 2 - κ := hk3
      have hfin := negativeClock_finite_laplace hb0 hb1 (E := s.energy (φ k))
        (by linarith [hE'.1]) (by linarith [hE'.2]) (W := s.W (φ k)) hn h0 h12 h2 hs'.le
      have hRHS : ∫⁻ θ in Set.Ioc θ₁ θ₂, ENNReal.ofReal (∫ x, Real.exp
          (-(s' * ((θ₂ - θ₁) / (2 * π)) * max x 0))
          ∂closedClockLaw (s.W (φ k)) b (s.energy (φ k)) (s.n (φ k)) θ) ≤
          ∫⁻ θ in Set.Ioc θ₁ θ₂, ENNReal.ofReal (m + ε) := by
        refine setLIntegral_mono measurable_const fun θ hθ => ENNReal.ofReal_le_ofReal ?_
        have := hk1 θ ⟨hθ.1.le, hθ.2⟩
        rw [abs_le] at this
        have e : ∫ x, Real.exp (-(s' * ((θ₂ - θ₁) / (2 * π)) * max x 0))
            ∂closedClockLaw (s.W (φ k)) b (s.energy (φ k)) (s.n (φ k)) θ =
            ∫ x, expTest _ hsa x
              ∂closedClockLaw (s.W (φ k)) b (s.energy (φ k)) (s.n (φ k)) θ := by
          simp only [expTest_apply, mul_assoc]
        rw [e]; linarith [this.2]
      rw [setLIntegral_const, Real.volume_Ioc] at hRHS
      have hchain := hfin.trans (mul_le_mul' le_rfl hRHS)
      have e : ENNReal.ofReal (θ₂ - θ₁)⁻¹ * (ENNReal.ofReal (m + ε) *
          ENNReal.ofReal (θ₂ - θ₁)) = ENNReal.ofReal (m + ε) := by
        rw [mul_comm (ENNReal.ofReal (m + ε)), ← mul_assoc,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith)),
          inv_mul_cancel₀ (by linarith : θ₂ - θ₁ ≠ 0), ENNReal.ofReal_one, one_mul]
      rw [e] at hchain
      rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at hchain
      simpa only [expTest_apply, scaledClock_eq_probeClock] using hchain
    have hlimf := hlim (expTest s' hs'.le)
    have := le_of_tendsto hlimf hbd
    simpa only [expTest_apply] using this
  obtain ⟨hIic, hmom⟩ := negativeClock_negMoment_of_laplace (μ := μ) hIio hXm hXpos ha0 hL hp
  refine ⟨hIic, hmom.trans ?_⟩
  have hX := hCB b hb E hE τ hτ hτT
  have hτp : 0 ≤ τ ^ (-p) := Real.rpow_nonneg hτ.le _
  have hapow : ((θ₂ - θ₁) / (2 * π)) ^ (-p) ≤ (ℓ / (2 * π)) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hℓ0 hℓa (by linarith)
  calc ENNReal.ofReal (((θ₂ - θ₁) / (2 * π)) ^ (-p)) *
        ∫⁻ ω, ENNReal.ofReal (X ω ^ (-p)) ∂BlockBand.SourceProcess.canonicalWienerLaw
      ≤ ENNReal.ofReal (((θ₂ - θ₁) / (2 * π)) ^ (-p)) * ENNReal.ofReal (CB * τ ^ (-p)) :=
        mul_le_mul' le_rfl hX
    _ = ENNReal.ofReal (((θ₂ - θ₁) / (2 * π)) ^ (-p) * (CB * τ ^ (-p))) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg ha0.le _)).symm
    _ ≤ ENNReal.ofReal ((ℓ / (2 * π)) ^ (-p) * CB * τ ^ (-p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hapow (mul_nonneg hCB0 hτp)

end RobinEntrance

end BlockBand.Endpoints.Clock
