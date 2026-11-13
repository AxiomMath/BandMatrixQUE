module

public import BlockBand.Internal.Contracts.TransmissionStatements
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The transmission generator theorem: along-energy vocabulary and finite-`W` statements

The finite-`W` random-matrix steps of the proof, as statements. The first three are derived from
the transmission inputs (`powerDriftSummable_holds`, `powerBracketSummable_holds`,
`powerModulusAlong_holds`);
`ProductMartingaleAlong` remains a hypothesis of `transmissionGenerator_of_prod`.
* `PowerDriftSummable`: `Σ_{⌊εW⌋ ≤ r < ⌊TW⌋} ‖E[Δ^k_r ∣ 𝓕_r] - A_k(P_r)/W‖_{L²} → 0`;
* `PowerBracketSummable`: `Σ_r ‖E[Δ^k_rΔ^l_r ∣ 𝓕_r] - B_{kl}(P_r)/W‖_{L¹} → 0`;
* `PowerModulusAlong`: the second clause of `tight` along `e`;
* `ProductMartingaleAlong`: the product half of `martingale` along `e` (a limit-side
  statement).
Here `Δ^k_r = Tr T^k_{r+1} - Tr T^k_r`, `𝓕_r = growthSigma W r`, `P_r = (Tr T^i_r)_i`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

/-- `Tr T_r^k` of the unabsorbed near-end-grown path at energy `E`, at path length `r`
(`powerTrace b E W k t = pathPower b E W k ⌊Wt⌋₊`, by `rfl`). -/
def pathPower (b E : ℝ) (W k r : ℕ) (ω : GrowthPath W) : ℝ :=
  ((pathTransmission b E (fun _ => 0) W r ω) ^ k).trace.re

/-- The power vector `P_r = (Tr T_r^i)_{i ∈ ℕ}` (the argument of `A_k`, `B_{kl}`). -/
def pathPowers (b E : ℝ) (W r : ℕ) (ω : GrowthPath W) : ℕ → ℝ := fun i => pathPower b E W i r ω

/-- The one-step increment `Δ^k_r = Tr T^k_{r+1} - Tr T^k_r`. -/
def powerIncrement (b E : ℝ) (W k r : ℕ) (ω : GrowthPath W) : ℝ :=
  pathPower b E W k (r + 1) ω - pathPower b E W k r ω

/-- The window of lengths `⌊εW⌋ ≤ r < ⌊TW⌋` (all one-step increments inside `[ε, T]`). -/
def lengthWindow (ε T : ℝ) (W : ℕ) : Finset ℕ := Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊

/-- Drift error at length `r`, path energy `E'`, base energy `E`:
`E[Δ^k_r ∣ 𝓕_r] - A_k(P_r)/W` with `A_k` at `D₀(E)`. -/
def driftError (b E E' : ℝ) (W k r : ℕ) : GrowthPath W → ℝ :=
  (growthPathLaw W b)[powerIncrement b E' W k r | growthSigma W r] - fun ω =>
    transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W

/-- Bracket error at length `r`: `E[Δ^k_rΔ^l_r ∣ 𝓕_r] - B_{kl}(P_r)/W` with `B` at `D₀(E)`. -/
def bracketError (b E E' : ℝ) (W k l r : ℕ) : GrowthPath W → ℝ :=
  (growthPathLaw W b)[fun ω => powerIncrement b E' W k r ω * powerIncrement b E' W l r ω |
      growthSigma W r] - fun ω =>
    transmissionBracket (transportD0 b E) k l (pathPowers b E' W r ω) / W

/-- **Summable drift errors** along a moving energy, in `L²`. For `k = 1` the conductance
satisfies `g_{r+1} - g_r = -(D₀/2W)g_r² + ΔM_r + 𝓡_r` with `Σ E|𝓡_r| → 0`. The errors are
fixed powers of `q, δ₀, δ₁, W^{-1/2}`, so every `L^p` works; `L²` is what the product martingale
needs. -/
def PowerDriftSummable : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e →
    ∀ k : ℕ, 1 ≤ k → ∀ ε T : ℝ, 0 < ε → ε < T →
      Tendsto (fun W : ℕ => ∑ r ∈ lengthWindow ε T W,
        eLpNorm (driftError b E (e W) W k r) 2 (growthPathLaw W b)) atTop (𝓝 0)

/-- **Summable bracket errors** along a moving energy, in `L¹` (the eigenbasis tensor
`dT_{ij}dT_{kl} = ½D₀t_it_j(2-t_i-t_j)δ_{il}δ_{jk}dt`, with summable same-sign and `f`-terms). -/
def PowerBracketSummable : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e →
    ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → ∀ ε T : ℝ, 0 < ε → ε < T →
      Tendsto (fun W : ℕ => ∑ r ∈ lengthWindow ε T W,
        eLpNorm (bracketError b E (e W) W k l r) 1 (growthPathLaw W b)) atTop (𝓝 0)

/-- **The modulus clause of `tight`** (vanishing maximum jumps), along a moving energy. At
`e ≡ E` it is the second conjunct of the `tight` field. -/
def PowerModulusAlong : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e →
    ∀ k : ℕ, 1 ≤ k → ∀ ε T : ℝ, 0 < ε → ε < T →
      ∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
          η < |pathPower b (e W) W k ⌊(W : ℝ) * t⌋₊ ω -
            pathPower b (e W) W k ⌊(W : ℝ) * t'⌋₊ ω|} ≤ ENNReal.ofReal θ

/-- **`(P, Π)` is a limit of the power sums along the energies `e W`**: `IsPowerTraceLimit`
with the width-`W` path at energy `e W`. For `e ≡ E` this is `IsPowerTraceLimit b E P Pk`
(`isPowerTraceLimitAlong_const`). -/
structure IsPowerTraceLimitAlong (b : ℝ) (e : ℕ → ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Pk : ℕ → ℝ → Ω → ℝ) : Prop where
  prob : IsProbabilityMeasure P
  measurable : ∀ k, 1 ≤ k → ∀ t, 0 < t → Measurable (Pk k t)
  continuous : ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0)
  fdd : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ (m : ℕ) (ks : Fin m → ℕ) (ts : Fin m → ℝ),
    (∀ l, 1 ≤ ks l ∧ 0 < ts l) → ∀ Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ,
      Tendsto (fun n => ∫ ω, Φ (fun l => pathPower b (e (φ n)) (φ n) (ks l)
          ⌊((φ n : ℕ) : ℝ) * ts l⌋₊ ω) ∂growthPathLaw (φ n) b) atTop
        (𝓝 (∫ ω, Φ (fun l => Pk (ks l) (ts l) ω) ∂P))

/-- **The product half of `martingale`, along a moving energy**: every limit has
`M_kM_l - ∫_s^t B_{kl}(P(u))du` as martingale increments, where
`M_k(s,t) = P_k(t) - P_k(s) - ∫_s^t A_k(P(u))du`. -/
def ProductMartingaleAlong : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Pk : ℕ → ℝ → Ω → ℝ),
      IsPowerTraceLimitAlong b e P Pk →
      let obs : {k : ℕ // 1 ≤ k} → ℝ → Ω → ℝ := fun k => Pk k.1
      let M : ℕ → ℝ → ℝ → Ω → ℝ := fun k s t ω => Pk k t ω - Pk k s ω -
        ∫ u in s..t, transmissionDrift (transportD0 b E) k (fun i => Pk i u ω)
      ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → IsMartingaleIncrements P obs (Set.Ioi 0) fun s t ω =>
        M k s t ω * M l s t ω -
          ∫ u in s..t, transmissionBracket (transportD0 b E) k l (fun i => Pk i u ω)

theorem powerTrace_eq_pathPower (b E : ℝ) (W k : ℕ) (t : ℝ) (ω : GrowthPath W) :
    powerTrace b E W k t ω = pathPower b E W k ⌊(W : ℝ) * t⌋₊ ω := rfl

theorem isPowerTraceLimitAlong_const {b E : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Pk : ℕ → ℝ → Ω → ℝ} (h : IsPowerTraceLimit b E P Pk) :
    IsPowerTraceLimitAlong b (fun _ => E) P Pk :=
  ⟨h.prob, h.measurable, h.continuous, h.fdd⟩

theorem isMovingEnergy_const (E : ℝ) : IsMovingEnergy E 0 (fun _ => E) := fun W _ => by
  simp [IsNearEnergy]

end BlockBand.Transmission.Generator
