module

public import BlockBand.Transmission.LawDecay.Cubic
public import BlockBand.Transmission.LawDecay.Gronwall

/-!
# The Lyapunov bound over the window `[W, ⌊Wt⌋]` at one width

With `c₀ = 5D₀(E)/512` and `y_r = E Φ_ε(g_r, P₂(r))` (`lyapMean`), for `W ≥ max(1, c₀)`, `t ≥ 1`:

**`lyap_window`**: `y_{⌊Wt⌋} - 2√ε ≤ e^{c₀}e^{-c₀(t-1)} max(y_W - 2√ε, 0) + S_W`,
`S_W = Σ_{W ≤ r < ⌊Wt⌋} (ε^{-5/2} err_r + ε^{-7/2}/6 · cubic_r)` — the paper's
`E√g_t ≤ (64/63)e^{-D₀(t-s)/128}E√g_s` at finite `W`, with `s = 1`, the shift `ε`
and the summed one-step errors (`gronwall`, `step_path`).

Also: `sqrt_le_lyapMean` (`E√g_r ≤ (64/63)y_r`, from `Φ_ε ≥ (63/64)√(g+ε)`) and
`lyapMean_le` (`y_r ≤ (E g_r + 2)/2`).
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

theorem stepCubic_nonneg (b E' : ℝ) (W r : ℕ) : 0 ≤ stepCubic b E' W r :=
  integral_nonneg fun ω => by positivity

/-- The summed window error `S_W`. -/
def windowErr (b E E' ε t : ℝ) (W : ℕ) : ℝ :=
  ∑ r ∈ lengthWindow 1 t W, ((Real.sqrt ε)⁻¹ ^ 5 * stepErr b E E' W r +
    ε ^ (-7 / 2 : ℝ) / 6 * stepCubic b E' W r)

/-- **The window bound at one width.** -/
theorem lyap_window {b E E' ε t : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (h1' : -2 < E') (h2' : E' < 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 1 ≤ t) (hW : 1 ≤ W)
    (hWc : 5 / 512 * transportD0 b E ≤ W) :
    lyapMean b E' W ε ⌊(W : ℝ) * t⌋₊ - 2 * Real.sqrt ε ≤
      Real.exp (5 / 512 * transportD0 b E) *
          Real.exp (-(5 / 512 * transportD0 b E * (t - 1))) *
          max (lyapMean b E' W ε W - 2 * Real.sqrt ε) 0 +
        windowErr b E E' ε t W := by
  set c₀ := 5 / 512 * transportD0 b E
  have hc₀ : 0 ≤ c₀ := by have := transportD0_nonneg hb0 h1 h2; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have ha1 : c₀ / W ≤ 1 := (div_le_one hW0).2 hWc
  have hn : W ≤ ⌊(W : ℝ) * t⌋₊ := Nat.le_floor (by nlinarith)
  have hG := gronwall (y := fun r => lyapMean b E' W ε r)
    (err := fun r => (Real.sqrt ε)⁻¹ ^ 5 * stepErr b E E' W r +
      ε ^ (-7 / 2 : ℝ) / 6 * stepCubic b E' W r) (a := c₀ / W) (z := 2 * Real.sqrt ε)
    (by positivity) ha1
    (fun r => add_nonneg (mul_nonneg (by positivity) (stepErr_nonneg _ _ _ _ _))
      (mul_nonneg (div_nonneg (Real.rpow_nonneg hε.le _) (by norm_num)) (stepCubic_nonneg _ _ _ _)))
    W (fun r _ => by
      have := step_path (W := W) hb0 hb h1 h2 h1' h2' hε hε1 hW r
      have e : 5 / 512 * transportD0 b E / W = c₀ / W := rfl
      rw [e] at this
      show _ ≤ _ - _ + (_ + _)
      linarith)
    ⌊(W : ℝ) * t⌋₊ hn
  rw [← lengthWindow_one] at hG
  refine hG.trans (add_le_add (mul_le_mul_of_nonneg_right ?_ (le_max_right _ _)) le_rfl)
  refine (one_sub_pow_le_exp ha1 _).trans ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  have hfl : (W : ℝ) * t - 1 < ⌊(W : ℝ) * t⌋₊ := by
    have := Nat.lt_floor_add_one ((W : ℝ) * t); linarith
  rw [Nat.cast_sub hn]
  have : c₀ / W * ((⌊(W : ℝ) * t⌋₊ : ℝ) - W) ≥ c₀ / W * (W * t - 1 - W) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e : c₀ / W * (W * t - 1 - W) = c₀ * (t - 1) - c₀ / W := by field_simp; ring
  have : c₀ / W ≤ c₀ := div_le_self hc₀ (by exact_mod_cast hW)
  linarith

/-- `E√g_r ≤ (64/63)E Φ_ε(g_r, P₂(r))`. -/
theorem sqrt_le_lyapMean {b E' ε : ℝ} (hb : b < 1) (h1' : -2 < E') (h2' : E' < 2) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (r : ℕ) :
    ∫ ω, Real.sqrt (pathPower b E' W 1 r ω) ∂growthPathLaw W b ≤ 64 / 63 * lyapMean b E' W ε r := by
  have hd := ae_dom (W := W) hb h1' h2'
  have iL : Integrable (fun ω => lyap ε (pathPower b E' W 1 r ω) (pathPower b E' W 2 r ω))
      (growthPathLaw W b) :=
    integrable_of_abs_le ((measurable_lyap ε).comp ((measurable_pathPower b E' 1 r).prodMk
      (measurable_pathPower b E' 2 r))) (C := W + 2) (hd.mono fun ω h =>
        (abs_lyap_le hε hε1 (h r).2.1 (h r).1.1 (h r).1.2.2.1).trans (by linarith [(h r).1.2.2.2]))
  have iS : Integrable (fun ω => Real.sqrt (pathPower b E' W 1 r ω)) (growthPathLaw W b) :=
    integrable_of_abs_le (measurable_pathPower b E' 1 r).sqrt (C := W + 1) (hd.mono fun ω h => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have := Real.sqrt_le_sqrt (h r).1.2.2.2
      have h' : Real.sqrt W ≤ W + 1 := by
        have := Real.sq_sqrt (Nat.cast_nonneg W : (0 : ℝ) ≤ W)
        nlinarith [Real.sqrt_nonneg (W : ℝ)]
      linarith)
  rw [lyapMean, ← integral_const_mul]
  refine integral_mono_ae iS (iL.const_mul _) (hd.mono fun ω h => ?_)
  obtain ⟨hl, -⟩ := lyap_bounds hε (h r).2.1 (h r).1.1 (h r).1.2.2.1
  have : Real.sqrt (pathPower b E' W 1 r ω) ≤ Real.sqrt (pathPower b E' W 1 r ω + ε) :=
    Real.sqrt_le_sqrt (by linarith)
  show _ ≤ 64 / 63 * lyap ε _ _
  linarith

/-- `E Φ_ε(g_r, P₂(r)) ≤ (E g_r + 2)/2`. -/
theorem lyapMean_le {b E' ε : ℝ} (hb : b < 1) (h1' : -2 < E') (h2' : E' < 2) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (r : ℕ) :
    lyapMean b E' W ε r ≤ ((∫ ω, pathPower b E' W 1 r ω ∂growthPathLaw W b) + 2) / 2 := by
  have hd := ae_dom (W := W) hb h1' h2'
  have iL : Integrable (fun ω => lyap ε (pathPower b E' W 1 r ω) (pathPower b E' W 2 r ω))
      (growthPathLaw W b) :=
    integrable_of_abs_le ((measurable_lyap ε).comp ((measurable_pathPower b E' 1 r).prodMk
      (measurable_pathPower b E' 2 r))) (C := W + 2) (hd.mono fun ω h =>
        (abs_lyap_le hε hε1 (h r).2.1 (h r).1.1 (h r).1.2.2.1).trans (by linarith [(h r).1.2.2.2]))
  have iG : Integrable (pathPower b E' W 1 r) (growthPathLaw W b) :=
    integrable_of_abs_le (measurable_pathPower b E' 1 r) (pathPower_bound hb h1' h2' le_rfl r)
  have iR : Integrable (fun ω => (pathPower b E' W 1 r ω + 2) / 2) (growthPathLaw W b) :=
    (iG.add (integrable_const _)).div_const _
  have := integral_mono_ae iL iR (hd.mono fun ω h => by
    obtain ⟨-, hu⟩ := lyap_bounds hε (h r).2.1 (h r).1.1 (h r).1.2.2.1
    have hs := Real.sqrt_nonneg (pathPower b E' W 1 r ω + ε)
    have hsq := Real.sq_sqrt (by linarith [(h r).2.1] : 0 ≤ pathPower b E' W 1 r ω + ε)
    show lyap ε (pathPower b E' W 1 r ω) (pathPower b E' W 2 r ω) ≤ (pathPower b E' W 1 r ω + 2) / 2
    nlinarith [sq_nonneg (Real.sqrt (pathPower b E' W 1 r ω + ε) - 1)])
  rw [integral_div, integral_add iG (integrable_const _), integral_const] at this
  simpa [lyapMean] using this

end BlockBand.Transmission.LawDecay
