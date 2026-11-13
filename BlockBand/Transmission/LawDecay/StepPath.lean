module

public import BlockBand.Transmission.LawDecay.StepInt
public import BlockBand.Transmission.LawDecay.Spectral
public import BlockBand.Transmission.Generator.ModPath
public import BlockBand.Transmission.Generator.BrCond

/-!
# The one-step Lyapunov inequality along the near-end-grown path

Width `W ≥ 1`, path energy `E'` (bulk), base energy `E` (the generator coefficients use
`D₀ = D₀(E)`, as in `driftError`/`bracketError`), `0 < ε ≤ 1`, length `r`,
`y_r = E Φ_ε(g_r, P₂(r))` under `growthPathLaw W b`:

**`step_path`**: `y_{r+1} ≤ y_r - (5D₀/512W)(y_r - 2√ε) + ε^{-5/2}·err_r + E R_r`, where `err_r` is the
sum of `E|driftError|` (`k = 1, 2`) and `E|bracketError|` (`(k,l) = (1,1), (1,2)`), and
`R_r = ε^{-7/2}(|Δ¹_r|³ + (Δ¹_r)²|Δ²_r|)/6`.

This is `step_abstract` with `m = 𝓕_r = growthSigma W r`, `(x, y) = (g_r, P₂(r))`, the
conditional means (definitions of `driftError`, `bracketError`), the almost-sure domain
(`pathPower_mem`, `ae_spectral`; `K = W`) and the generator inequality `lyapGen_le` divided by `W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Generator

variable {W : ℕ}

/-- `E Φ_ε(g_r, P₂(r))`. -/
def lyapMean (b E : ℝ) (W : ℕ) (ε : ℝ) (r : ℕ) : ℝ :=
  ∫ ω, lyap ε (pathPower b E W 1 r ω) (pathPower b E W 2 r ω) ∂growthPathLaw W b

/-- The one-step error `err_r`. -/
def stepErr (b E E' : ℝ) (W r : ℕ) : ℝ :=
  ∫ ω, |driftError b E E' W 1 r ω| ∂growthPathLaw W b +
    ∫ ω, |driftError b E E' W 2 r ω| ∂growthPathLaw W b +
    ∫ ω, |bracketError b E E' W 1 1 r ω| ∂growthPathLaw W b +
    ∫ ω, |bracketError b E E' W 1 2 r ω| ∂growthPathLaw W b

/-- The cubic Taylor remainder `E R_r` (without the factor `ε^{-7/2}/6`). -/
def stepCubic (b E' : ℝ) (W r : ℕ) : ℝ :=
  ∫ ω, (|powerIncrement b E' W 1 r ω| ^ 3 +
    powerIncrement b E' W 1 r ω ^ 2 * |powerIncrement b E' W 2 r ω|) ∂growthPathLaw W b

theorem pathPower_one' (b E : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    pathPower b E W 1 r ω = pathConductance b E W r ω := by
  simp [pathPower, pathConductance, conductanceOf]

theorem ae_dom {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ r : ℕ, Dom W (pathPower b E W 1 r ω) (pathPower b E W 2 r ω) ∧
      0 ≤ pathPower b E W 1 r ω ∧ 0 ≤ pathPower b E W 4 r ω ∧
      pathPower b E W 3 r ω ≤ Real.sqrt (pathPower b E W 2 r ω) * pathPower b E W 2 r ω := by
  filter_upwards [pathPower_mem (W := W) hb h1 h2, ae_spectral (W := W) hb h1 h2] with ω hω hs r
  obtain ⟨a0, a1, a2⟩ := hω 2 r (by norm_num)
  obtain ⟨c0, -, -⟩ := hω 1 r le_rfl
  obtain ⟨d0, -, -⟩ := hω 4 r (by norm_num)
  rw [← pathPower_one'] at a1 a2
  exact ⟨⟨a0, a1, (hs r).1, a2⟩, c0, d0, (hs r).2⟩

theorem integrable_div_W {b : ℝ} {f : GrowthPath W → ℝ} {r : ℕ} (hf : Measurable[growthSigma W r] f)
    {C : ℝ} (hC : ∀ᵐ ω ∂growthPathLaw W b, |f ω| ≤ C) : Integrable f (growthPathLaw W b) :=
  integrable_of_abs_le (hf.mono (growthSigma_le W r) le_rfl) hC

theorem abs_bracket_le {b E' : ℝ} (hb : b < 1) (h1 : -2 < E') (h2 : E' < 2) (D : ℝ) (k l r : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, |transmissionBracket D k l (pathPowers b E' W r ω) / W| ≤
      |D| * k * l * (2 * W) := by
  filter_upwards [pathPower_mem (W := W) hb h1 h2] with ω hω
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  obtain ⟨a0, a1, a2⟩ := hω (k + l + 1) r (by omega)
  have hb1 : |pathPower b E' W (k + l + 1) r ω| ≤ W := by rw [abs_of_nonneg a0]; linarith
  rcases Nat.eq_zero_or_pos (k + l) with hkl | hkl
  · have hk : k = 0 := by omega
    simp [transmissionBracket, hk]
  obtain ⟨b0, b1, b2⟩ := hω (k + l) r hkl
  have hb2 : |pathPower b E' W (k + l) r ω| ≤ W := by rw [abs_of_nonneg b0]; linarith
  simp only [transmissionBracket, pathPowers]
  rw [abs_div, Nat.abs_cast, div_le_iff₀ (by linarith), abs_mul, abs_mul, abs_mul, Nat.abs_cast,
    Nat.abs_cast]
  have : |pathPower b E' W (k + l) r ω - pathPower b E' W (k + l + 1) r ω| ≤ 2 * W :=
    (abs_sub _ _).trans (by linarith)
  have hkl0 : 0 ≤ |D| * k * l := by positivity
  calc |D| * k * l * |pathPower b E' W (k + l) r ω - pathPower b E' W (k + l + 1) r ω| ≤
      |D| * k * l * (2 * W) := mul_le_mul_of_nonneg_left this hkl0
    _ ≤ |D| * k * l * (2 * W) * W := le_mul_of_one_le_right (by positivity) hW1

/-- The generator inequality along the path, divided by `W`. -/
theorem gen_path {ε D : ℝ} {W : ℕ} {P : ℕ → ℝ} (hε : 0 < ε) (hD : 0 ≤ D) (hW : 1 ≤ W)
    (hg : 0 ≤ P 1) (h2 : 0 ≤ P 2) (h2g : P 2 ≤ P 1 ^ 2) (h3x : P 3 ≤ Real.sqrt (P 2) * P 2)
    (h4 : 0 ≤ P 4) :
    coefX ε (P 1) (P 2) * (transmissionDrift D 1 P / W) +
        coefY ε (P 1) * (transmissionDrift D 2 P / W) +
        coefXX ε (P 1) (P 2) * (transmissionBracket D 1 1 P / W) +
        coefXY ε (P 1) * (transmissionBracket D 1 2 P / W) ≤
      -(5 / 512 * D / W) * (lyap ε (P 1) (P 2) - 2 * Real.sqrt ε) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hG := lyapGen_le hε hD hg h2 h2g h3x h4
  have e : coefX ε (P 1) (P 2) * (transmissionDrift D 1 P / W) +
      coefY ε (P 1) * (transmissionDrift D 2 P / W) +
      coefXX ε (P 1) (P 2) * (transmissionBracket D 1 1 P / W) +
      coefXY ε (P 1) * (transmissionBracket D 1 2 P / W) = lyapGen ε D P / W := by
    simp only [lyapGen]; ring
  rw [e, div_le_iff₀ hW0]
  have e2 : -(5 / 512 * D / W) * (lyap ε (P 1) (P 2) - 2 * Real.sqrt ε) * W =
      -(5 / 512) * D * (lyap ε (P 1) (P 2) - 2 * Real.sqrt ε) := by field_simp
  rw [e2]; exact hG

/-- **The one-step Lyapunov inequality along the path.** -/
theorem step_path {b E E' ε : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (h1' : -2 < E') (h2' : E' < 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W) (r : ℕ) :
    lyapMean b E' W ε (r + 1) ≤ lyapMean b E' W ε r -
        5 / 512 * transportD0 b E / W * (lyapMean b E' W ε r - 2 * Real.sqrt ε) +
      (Real.sqrt ε)⁻¹ ^ 5 * stepErr b E E' W r +
      ε ^ (-7 / 2 : ℝ) / 6 * stepCubic b E' W r := by
  have hb1 : b < 1 := by linarith
  have hD := transportD0_nonneg hb0 h1 h2
  set D := transportD0 b E
  set μ := growthPathLaw W b
  have hA : ∀ k, Integrable (fun ω => transmissionDrift D k (pathPowers b E' W r ω) / W) μ :=
    fun k => integrable_div_W (measurable_drift_pathPowers b E E' k r)
      (drift_pathPowers_bound hb1 h1' h2' _ hD k r)
  have hB : ∀ k l, Integrable (fun ω => transmissionBracket D k l (pathPowers b E' W r ω) / W) μ :=
    fun k l => integrable_div_W (measurable_bracket_pathPowers b E E' k l r)
      (abs_bracket_le hb1 h1' h2' D k l r)
  have hd := ae_dom (W := W) hb1 h1' h2'
  have hS := step_abstract (μ := μ) (growthSigma_le W r) (c := 5 / 512 * D / W) (K := W)
    hε hε1 (x := pathPower b E' W 1 r) (y := pathPower b E' W 2 r)
    (x' := pathPower b E' W 1 (r + 1)) (y' := pathPower b E' W 2 (r + 1))
    (e1 := driftError b E E' W 1 r) (e2 := driftError b E E' W 2 r)
    (e11 := bracketError b E E' W 1 1 r) (e12 := bracketError b E E' W 1 2 r)
    (measurable_pathPower_adapted b E' 1 r) (measurable_pathPower_adapted b E' 2 r)
    (measurable_pathPower b E' 1 (r + 1)) (measurable_pathPower b E' 2 (r + 1))
    (hd.mono fun ω h => ⟨(h r).1, (h (r + 1)).1⟩) (hA 1) (hA 2) (hB 1 1) (hB 1 2)
    (integrable_condExp.sub (hA 1)) (integrable_condExp.sub (hA 2))
    (integrable_condExp.sub (hB 1 1)) (integrable_condExp.sub (hB 1 2))
    (sub_add_cancel _ _).symm (sub_add_cancel _ _).symm (sub_add_cancel _ _).symm
    (sub_add_cancel _ _).symm
    (hd.mono fun ω h => gen_path (P := pathPowers b E' W r ω) hε hD hW (h r).2.1 (h r).1.1
      (h r).1.2.2.1 (h r).2.2.2 (h r).2.2.1)
  have eR : ∫ ω, ε ^ (-7 / 2 : ℝ) * (|pathPower b E' W 1 (r + 1) ω - pathPower b E' W 1 r ω| ^ 3 +
      (pathPower b E' W 1 (r + 1) ω - pathPower b E' W 1 r ω) ^ 2 *
        |pathPower b E' W 2 (r + 1) ω - pathPower b E' W 2 r ω|) / 6 ∂μ =
      ε ^ (-7 / 2 : ℝ) / 6 * stepCubic b E' W r := by
    rw [integral_div, integral_const_mul]; simp only [stepCubic, powerIncrement]; ring
  rw [eR] at hS
  simpa only [lyapMean, stepErr] using hS

end BlockBand.Transmission.LawDecay
