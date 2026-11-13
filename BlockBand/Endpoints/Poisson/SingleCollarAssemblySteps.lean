module

public import BlockBand.Endpoints.Poisson.SingleCollarAssemblyAux
public import BlockBand.Endpoints.Poisson.SingleCollarAnalytic
public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificate

/-!
# Assembly of the single-collar log-error bound: sequence-level steps

* `sca2_component_eventually`: one instance of the uniform remote-higher bound along a sequence,
  for the indicator profile of `[R, τ - R]` (when `τ = 0` the window is empty and the profile is
  `0`).
* `sca2_window`: the source window `[(buf-2)/W, (len-buf+2)/W]` of `ScsWardData.paths` lies in
  `[R-1, τ-(R-1)]` once `W ≥ 3`, `buf = ⌊RW⌋` and `(len + 3)/W ≤ τ + 1`.
* `sca2_F_bound`: the square-root bookkeeping `Cp (A + √Cg √A) ≤ C₁ m² e^{-(c₀/2)R}` at
  `A = K₂ m² Cs e^{-c₀(R-1)}` (taking the square root halves the rate: `c' = c/2`).
* `sca2_cond_le`, `sca2_lintegral_le_eLpNorm`, `sca2_measurable_stageLogDiff`, `sca2_scale`:
  small conversions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace intervalSource growthPathLaw)
open BlockBand.Internal.Contracts.Layers (boundaryZ)
open BlockBand.Internal.Contracts.Critical (conductance oldScattering)
open scoped ENNReal

/-!
## 1. One remote-higher instance along a sequence
-/

/-- **One instance of `RemoteHigherUniformStatement` along a sequence.** `hU` is the clause of
`RemoteHigherUniformStatement` at fixed `b, E, q, r, K` (constants `C, c`). Along widths `Wl → ∞`, lengths `nl`
with `nl/Wl → τ ≥ 0` and energies with eventually `|el - E| ≤ K/Wl²`, the moment of the interval source with the
indicator profile `1_{[R, τ-R]}` is eventually at most `max C 0 · e^{-cR} + ε`. For `τ = 0` the profile is `0` (`R
> 0`), so the moment is `0`. -/
theorem sca2_component_eventually {b E K C c q r R τ : ℝ} (hq : 0 < q) (hr : 0 < r) (hR : 2 ≤ R)
    (hτ : 0 ≤ τ) (hK : 0 ≤ K)
    (hU : ∀ τ R : ℝ, 0 < τ → 2 ≤ R →
      ∀ (e : ℕ → ℝ) (n : ℕ → ℕ), (∀ᶠ W : ℕ in atTop, |e W - E| ≤ K / (W : ℝ) ^ 2) →
        Tendsto (fun W : ℕ => (n W : ℝ) / W) atTop (𝓝 τ) →
      ∀ qf : ℝ → ℝ, (∀ x, 0 ≤ qf x) → (∀ x, qf x ≤ 1) → (∀ x, x ∉ Set.Icc R (τ - R) → qf x = 0) →
        limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
            (fracTrace q (intervalSource b (e W) W (n W) qf ω)) ^ r
            ∂growthPathLaw W b) atTop ≤
          ENNReal.ofReal (C * Real.exp (-(c * R))))
    {Wl nl : ℕ → ℕ} {el : ℕ → ℝ} (hW : Tendsto Wl atTop atTop)
    (hn : Tendsto (fun l => (nl l : ℝ) / (Wl l : ℝ)) atTop (𝓝 τ))
    (he : ∀ᶠ l in atTop, |el l - E| ≤ K / (Wl l : ℝ) ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ l in atTop, ∫⁻ ω, ENNReal.ofReal (fracTrace q (intervalSource b (el l) (Wl l) (nl l)
        ((Icc R (τ - R)).indicator 1) ω)) ^ r ∂growthPathLaw (Wl l) b ≤
      ENNReal.ofReal (max C 0 * Real.exp (-(c * R)) + ε) := by
  rcases hτ.eq_or_lt with hτ0 | hτ0
  · -- the empty window, profile `0`
    subst hτ0
    have hI : (Icc R (0 - R)).indicator (1 : ℝ → ℝ) = 0 := by
      rw [Icc_eq_empty (by linarith), indicator_empty]; rfl
    refine Eventually.of_forall fun l => ?_
    rw [hI]
    simp only [rh_intervalSource_zero, rh_fracTrace_zero hq, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos hr, lintegral_zero]
    exact bot_le
  · set qf : ℝ → ℝ := (Icc R (τ - R)).indicator 1 with hqf
    have h0 : ∀ x, 0 ≤ qf x := fun x => by
      simp only [qf, indicator_apply]; split_ifs <;> norm_num
    have h1 : ∀ x, qf x ≤ 1 := fun x => by
      simp only [qf, indicator_apply]; split_ifs <;> norm_num
    have h2 : ∀ x, x ∉ Set.Icc R (τ - R) → qf x = 0 := fun x hx => indicator_of_notMem hx _
    have hev := scs_eventually_le_of_limsup
      (G := fun W e n => ∫⁻ ω, ENNReal.ofReal (fracTrace q (intervalSource b e W n qf ω)) ^ r
        ∂growthPathLaw W b) hK hτ (B := ENNReal.ofReal (C * Real.exp (-(c * R))))
      ENNReal.ofReal_ne_top (fun e n he' hn' => hU τ R hτ0 hR e n he' hn' qf h0 h1 h2) hW hn
      (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    filter_upwards [hev, he] with l hl hel
    refine (hl _ hel).trans ?_
    rw [ENNReal.ofReal_add (by positivity) hε.le]
    gcongr
    exact le_max_left _ _

/-!
## 2. The source window
-/

/-- The source window of `ScsWardData.paths` lies in `[R-1, τ-(R-1)]`, for `W ≥ 3`,
`buf > RW - 1` and `(len + 3)/W ≤ τ + 1` (real form). -/
theorem sca2_window {R τ W buf len : ℝ} (hW : 3 ≤ W) (hbuf : R * W - 1 < buf)
    (hlen : len / W + 3 / W ≤ τ + 1) :
    Icc ((buf - 2) / W) ((len - buf + 2) / W) ⊆ Icc (R - 1) (τ - (R - 1)) := by
  intro y hy
  have hW0 : 0 < W := by linarith
  have h1 : R - 1 ≤ (buf - 2) / W := by
    rw [le_div_iff₀ hW0]; nlinarith
  have hlen' : len + 3 ≤ (τ + 1) * W := by
    have := mul_le_mul_of_nonneg_right hlen hW0.le
    rwa [add_mul, div_mul_cancel₀ _ hW0.ne', div_mul_cancel₀ _ hW0.ne'] at this
  have h2 : (len - buf + 2) / W ≤ τ - (R - 1) := by
    rw [div_le_iff₀ hW0]; nlinarith
  exact ⟨h1.trans hy.1, hy.2.trans h2⟩

/-!
## 3. Square-root bookkeeping
-/

/-- `Cp (A + √Cg √A) ≤ C₁ m² e^{-(c₀/2) R}` at `A = K₂ m² Cs e^{-c₀(R-1)}`, with
`C₁ = (Cp K₂ Cs + Cp √Cg √(K₂ Cs)) e^{c₀/2}`, for `m ≥ 1`, `R ≥ 1`. -/
theorem sca2_F_bound {Cp Cg K₂ Cs c₀ R m : ℝ} (hCp : 0 ≤ Cp) (hK₂ : 0 ≤ K₂)
    (hCs : 0 ≤ Cs) (hc₀ : 0 < c₀) (hR : 1 ≤ R) (hm : 1 ≤ m) :
    Cp * (K₂ * m ^ 2 * (Cs * Real.exp (-(c₀ * (R - 1)))) +
        Real.sqrt Cg * Real.sqrt (K₂ * m ^ 2 * (Cs * Real.exp (-(c₀ * (R - 1)))))) ≤
      (Cp * K₂ * Cs + Cp * (Real.sqrt Cg * Real.sqrt (K₂ * Cs))) * Real.exp (c₀ / 2) * m ^ 2 *
        Real.exp (-(c₀ / 2 * R)) := by
  set u := Real.exp (-(c₀ * (R - 1)) / 2) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hu1 : u ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have husq : Real.exp (-(c₀ * (R - 1))) = u ^ 2 := by
    rw [hu, sq, ← Real.exp_add]; ring_nf
  have hue : Real.exp (c₀ / 2) * Real.exp (-(c₀ / 2 * R)) = u := by
    rw [hu, ← Real.exp_add]; ring_nf
  have hm0 : 0 ≤ m := by linarith
  have hsq : Real.sqrt (K₂ * m ^ 2 * (Cs * u ^ 2)) = Real.sqrt (K₂ * Cs) * (m * u) := by
    rw [show K₂ * m ^ 2 * (Cs * u ^ 2) = (K₂ * Cs) * (m * u) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [husq, hsq]
  have hrhs : (Cp * K₂ * Cs + Cp * (Real.sqrt Cg * Real.sqrt (K₂ * Cs))) * Real.exp (c₀ / 2) *
      m ^ 2 * Real.exp (-(c₀ / 2 * R)) =
      (Cp * K₂ * Cs + Cp * (Real.sqrt Cg * Real.sqrt (K₂ * Cs))) * m ^ 2 * u := by
    rw [← hue]; ring
  rw [hrhs]
  have a1 : 0 ≤ Cp * K₂ * Cs := by positivity
  have a2 : 0 ≤ Cp * (Real.sqrt Cg * Real.sqrt (K₂ * Cs)) := by positivity
  have b1 : m ^ 2 * u ^ 2 ≤ m ^ 2 * u := by
    have : u ^ 2 ≤ u := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have b2 : m * u ≤ m ^ 2 * u := by
    have : m ≤ m ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hu0.le
  calc Cp * (K₂ * m ^ 2 * (Cs * u ^ 2) + Real.sqrt Cg * (Real.sqrt (K₂ * Cs) * (m * u)))
      = Cp * K₂ * Cs * (m ^ 2 * u ^ 2) + Cp * (Real.sqrt Cg * Real.sqrt (K₂ * Cs)) * (m * u) := by
        ring
    _ ≤ Cp * K₂ * Cs * (m ^ 2 * u) + Cp * (Real.sqrt Cg * Real.sqrt (K₂ * Cs)) * (m ^ 2 * u) := by
        gcongr
    _ = _ := by ring

/-!
## 4. Small conversions
-/

/-- `(max 0 g₀)² ≤ |g₀|²`, using `oldScattering = oldResponse` (`collarKc_eq_collarReaction`). -/
theorem sca2_cond_le {W : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ENNReal.ofReal (max 0 (conductance (oldScattering b e X)) ^ 2) ≤
      ‖conductance (oldResponse (boundaryZ b e) X)‖ₑ ^ (2 : ℝ) := by
  rw [(collarKc_eq_collarReaction (W := W) b e (fun _ => 0, fun _ => 0)).2.2 X]
  set g := conductance (oldScattering b e X)
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact pow_le_pow_left₀ (le_max_left _ _) (max_le (abs_nonneg _) (le_abs_self _)) 2

/-- `E|f| ≤ ‖f‖_{L^r}` for a probability measure and `r ≥ 1`. -/
theorem sca2_lintegral_le_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ ≤ eLpNorm f (ENNReal.ofReal r) μ := by
  have h1 : ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ = eLpNorm f 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    exact lintegral_congr fun ω => (Real.enorm_eq_ofReal_abs _).symm
  rw [h1]
  have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
  exact eLpNorm_le_eLpNorm_of_exponent_le h2

theorem sca2_measurable_stageLogDiff (P : Parameters) {m : ℕ} (L : Fin m → ℕ) (π : Pairing)
    (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (buf : ℕ) (κ : ℝ) :
    Measurable (scsStageLogDiff P L π S k e buf κ) := by
  have h : ∀ (T : Finset (Fin m)) (κ' : ℝ), Measurable fun ω : RingCoords P.n P.W =>
      ‖(stageMatrix L 0 π T e (boundaryZ P.b e) buf κ' ω).det‖ := fun T κ' =>
    ((continuous_id.matrix_det).measurable.comp
      (scs_measurable_stageMatrix P L 0 π T e _ buf κ')).norm
  unfold scsStageLogDiff
  exact (Real.measurable_log.comp ((h S κ).div (h S 0))).sub
    (Real.measurable_log.comp ((h _ κ).div (h _ 0)))

/-- The scale relations of the target: with `Λ = nWρ`, `κ = δW²/Λ`, `W ≤ 2n`, `|x| ≤ X`:
`|x/Λ| ≤ (2X/ρ + 1)/W²`, `κ ≤ 2δ/ρ` and `κ n/W = δ/ρ`. -/
theorem sca2_scale {n W ρ δ X x : ℝ} (hn : 0 < n) (hW : 0 < W) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hX : 0 ≤ X) (hx : |x| ≤ X) (hWn : W ≤ 2 * n) :
    |x / (n * W * ρ)| ≤ (2 * X / ρ + 1) / W ^ 2 ∧ δ * W ^ 2 / (n * W * ρ) ≤ 2 * δ / ρ ∧
      δ * W ^ 2 / (n * W * ρ) * n / W = δ / ρ := by
  have hΛ : 0 < n * W * ρ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hΛ, div_le_div_iff₀ hΛ (by positivity)]
    have h1 : |x| * W ^ 2 ≤ X * W ^ 2 := mul_le_mul_of_nonneg_right hx (by positivity)
    have h2 : (2 * X / ρ + 1) * (n * W * ρ) = 2 * X * n * W + n * W * ρ := by
      field_simp
    rw [h2]
    have h3 : X * W ^ 2 ≤ 2 * X * n * W := by
      have := mul_le_mul_of_nonneg_left hWn (by positivity : 0 ≤ X * W); nlinarith
    nlinarith [mul_pos (mul_pos hn hW) hρ]
  · rw [div_le_div_iff₀ hΛ hρ]
    have := mul_le_mul_of_nonneg_left hWn (by positivity : 0 ≤ δ * W * ρ)
    nlinarith
  · field_simp

end BlockBand.Endpoints
