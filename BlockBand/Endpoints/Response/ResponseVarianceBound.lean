module

public import BlockBand.Endpoints.Response.ResponseVariancePass

/-!
# The finite-width bound behind the response-variance bound

For one exact physical parameter set `p` (ring of `n` blocks of width `W`, matched-lead path of
`r = n - 3` blocks, microscopic energies `e(u) = E + u/(Nρ(E))`), a smooth nonnegative unit-mass
weight `w` supported in `[-U, U]` and the cosine source `q_m(s) = cos(2πms/τ)`:
* `rv_ratio_integral_le`: `E_{path,h}|h*B_qh/h*Ah|² ≤ 3 E[n⁻¹Σ_J Φ_m(ℛ_Jν^lead)] + 3ε_W² + 3E a_port`
  (`Φ_m(ν) = |ν(e^{2πim·})|²`, `ε_W` the source-location change);
* `rv_finite_bound`: if, on the window, the signed critical derivative is within `ε` of
  `-8πρ(E)J`, the port fraction is at most `ε`, the multiplier moment is at most `C_m` and
  `ε_W² ≤ ε`, then with `a = 8πρ(E)|J|`:
  `a² - 2aε ≤ C₁²C_m (3 ∫ w(u) E Φ_m(ℛ_Jν^lead(e(u))) du + 6ε)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.ClocksCommonPort
  BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

/-- The source-location error `ε_W = 2π|m|(r |1/(τW) - 1/n| + 1/n)`, `r = n - 3`. -/
def rvGridError (m : ℤ) (τ : ℝ) (n W : ℕ) : ℝ :=
  2 * Real.pi * |(m : ℝ)| * (((n - 3 : ℕ) : ℝ) * |1 / (τ * W) - 1 / n| + 1 / n)

theorem rvGridError_nonneg (m : ℤ) (τ : ℝ) (n W : ℕ) : 0 ≤ rvGridError m τ n W := by
  unfold rvGridError; positivity

theorem rv_ratio_integral_le (m : ℤ) {τ : ℝ} (hτ : 0 < τ) (b e : ℝ) {n W : ℕ} (hn : 4 ≤ n)
    (hW : 0 < W) :
    ∫ z, rvRatio (rvCosineTest τ m) b e W (n - 3) z ^ 2 ∂probedClockLaw W b ≤
      3 * ∫ z, rvLeadAvg m b e n W z ∂probedClockLaw W b + 3 * rvGridError m τ n W ^ 2 +
        3 * ∫ z, portFraction b e W (n - 3) z ∂probedClockLaw W b := by
  have hP := isProbabilityMeasure_probedClockLaw W b
  have hn0 : 0 < n := by omega
  have hZm : Measurable (fun z : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      rvRatio (rvCosineTest τ m) b e W (n - 3) z ^ 2) :=
    (rv_measurable_ratio_of _ b W (n - 3) measurable_const measurable_id).pow_const 2
  have hZint : Integrable (fun z => rvRatio (rvCosineTest τ m) b e W (n - 3) z ^ 2)
      (probedClockLaw W b) :=
    Integrable.of_bound hZm.aestronglyMeasurable 1 (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := rv_abs_ratio_le (rvCosineTest_abs_le τ m) b e W (n - 3) z
      nlinarith [abs_nonneg (rvRatio (rvCosineTest τ m) b e W (n - 3) z),
        sq_abs (rvRatio (rvCosineTest τ m) b e W (n - 3) z)])
  have hLint : Integrable (fun z => rvLeadAvg m b e n W z) (probedClockLaw W b) :=
    Integrable.of_bound (rv_measurable_leadAvg_of m b hn0 W measurable_const
      measurable_id).aestronglyMeasurable 1 (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (rv_leadAvg_nonneg _ _ _ _ _ _)]
        exact rv_leadAvg_le_one _ _ _ _ _ _)
  have hPint : Integrable (fun z => portFraction b e W (n - 3) z) (probedClockLaw W b) :=
    Integrable.of_bound (measurable_portFraction b e W (n - 3)).aestronglyMeasurable 1
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (portFraction_nonneg _ _ _ _ _)]
        exact portFraction_le_one _ _ _ _ _)
  have hpt : ∀ z, rvRatio (rvCosineTest τ m) b e W (n - 3) z ^ 2 ≤
      3 * rvLeadAvg m b e n W z + 3 * rvGridError m τ n W ^ 2 +
        3 * portFraction b e W (n - 3) z := by
    intro z
    have h1 := rv_ratio_sq_le m τ b e (rvGridError_nonneg m τ n W)
      (fun i => rv_cosine_grid_le m hτ hn hW i) z
    have h2 := rv_leadCos_sq_le_leadAvg (b := b) (e := e) m hn0 z
    linarith
  calc ∫ z, rvRatio (rvCosineTest τ m) b e W (n - 3) z ^ 2 ∂probedClockLaw W b
      ≤ ∫ z, (3 * rvLeadAvg m b e n W z + 3 * rvGridError m τ n W ^ 2 +
          3 * portFraction b e W (n - 3) z) ∂probedClockLaw W b :=
        integral_mono hZint (((hLint.const_mul 3).add (integrable_const _)).add
          (hPint.const_mul 3)) hpt
    _ = _ := by
        have i1 : Integrable (fun z => 3 * rvLeadAvg m b e n W z + 3 * rvGridError m τ n W ^ 2)
            (probedClockLaw W b) := (hLint.const_mul 3).add (integrable_const _)
        have i2 : Integrable (fun z => 3 * portFraction b e W (n - 3) z) (probedClockLaw W b) :=
          hPint.const_mul 3
        rw [integral_add i1 i2, integral_add (hLint.const_mul 3) (integrable_const _),
          integral_const_mul, integral_const, probReal_univ, one_smul, integral_const_mul]

/-- Real arithmetic: from `|S + a'| ≤ ε`, `a = |a'|` and `S² ≤ K`: `a² - 2aε ≤ K`. -/
theorem rv_sq_step {S a' ε K : ℝ} (hS : |S + a'| ≤ ε) (hK : S ^ 2 ≤ K) :
    |a'| ^ 2 - 2 * |a'| * ε ≤ K := by
  have ha := abs_nonneg a'
  by_cases hae : ε ≤ |a'|
  · have h1 : |a'| - ε ≤ |S| := by
      have := abs_sub_abs_le_abs_sub a' (-S)
      rw [sub_neg_eq_add, add_comm, abs_neg] at this
      linarith
    have h2 : (|a'| - ε) ^ 2 ≤ S ^ 2 := by
      rw [← sq_abs S]; exact pow_le_pow_left₀ (by linarith) h1 2
    nlinarith [sq_nonneg ε]
  · push Not at hae
    nlinarith [sq_nonneg S]

theorem rv_weight_integrable (w : SpectralWeight) : Integrable (fun u => w u) volume :=
  w.toContinuousMap.continuous.integrable_of_hasCompactSupport w.compactSupport

/-- The finite-width bound at one parameter set. -/
theorem rv_finite_bound (hCount : ConditionalBlockGUECount) (p : Parameters) {E x y τ c cG Cm ε J v U : ℝ}
    (m : ℤ) (w : SpectralWeight) (hE1 : -2 < E) (hE2 : E < 2) (hτ : 0 < τ) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hc : 0 ≤ c) (hcG : 0 < cG) (hCm0 : 0 ≤ Cm)
    (hwU : ∀ u, u ∉ Icc (-U) U → w u = 0)
    (hD : ∀ b e : ℝ, 0 < b → b < 1 / 2 → -2 < e → e < 2 → ∀ (W r : ℕ) (q : ℝ → ℝ)
      (ω : GrowthPath W), (∀ k, (ω.1 k).IsHermitian) → IsUnit (fullPathMatrix b e W r ω).det →
      |rvSignedDeriv b e x y W r q ω| ≤ 4 * etaZ b e *
        ((x + y) * |(rvSourceGram b e W r q ω).trace.re| +
          c * Real.sqrt (rvConductance b e W r ω) * Real.sqrt (hsSq (rvSourceGram b e W r q ω))))
    (hG : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ),
      IsSandwichedOn B A → B.trace.re ^ 2 + hsSq B ≤
        cG * A.trace.re ^ 2 * ∫ h, (quadForm B h / quadForm A h) ^ 2 ∂circularVectorLaw ι)
    (hv : v = 2 * J)
    (hpass : ∀ u ∈ Icc (-U) U,
      |signedPassDerivative p.b (microEnergy p E u) x y p.W (p.n - 3) (rvCosineTest τ m) +
        4 * Real.pi * Parameters.semicircleDensity E * v| ≤ ε)
    (hport : ∀ u ∈ Icc (-U) U,
      ∫ z, portFraction p.b (microEnergy p E u) p.W (p.n - 3) z ∂probedClockLaw p.W p.b ≤ ε)
    (hbulk : ∀ u ∈ Icc (-U) U, -2 < microEnergy p E u ∧ microEnergy p E u < 2)
    (hmom : ∀ u ∈ Icc (-U) U,
      ∫⁻ ω, ENNReal.ofReal ((1 + Real.sqrt (rvConductance p.b (microEnergy p E u) p.W (p.n - 3) ω))
          ^ 2 * (rvLeadClock p.b (microEnergy p E u) p.W (p.n - 3) ω).trace.re ^ 2)
        ∂growthPathLaw p.W p.b ≤ ENNReal.ofReal Cm)
    (hgrid : rvGridError m τ p.n p.W ^ 2 ≤ ε) :
    (8 * Real.pi * Parameters.semicircleDensity E * |J|) ^ 2 -
        2 * (8 * Real.pi * Parameters.semicircleDensity E * |J|) * ε ≤
      (4 * max (x + y) c * Real.sqrt (2 * cG)) ^ 2 * Cm *
        (3 * leadOneMark p E w (rvFourierTest m) + 6 * ε) := by
  have hP := isProbabilityMeasure_probedClockLaw p.W p.b
  have hW : 0 < p.W := p.W_pos
  have hn := p.n_ge_four
  have hn0 : 0 < p.n := by omega
  set C₃ := (4 * max (x + y) c * Real.sqrt (2 * cG)) ^ 2 * Cm with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  set ρ := Parameters.semicircleDensity E
  set a := 8 * Real.pi * ρ * |J|
  set L : ℝ → ℝ := fun u => ∫ z, rvLeadAvg m p.b (microEnergy p E u) p.n p.W z
    ∂probedClockLaw p.W p.b
  have hL0 : ∀ u, 0 ≤ L u := fun u => integral_nonneg fun z => rv_leadAvg_nonneg _ _ _ _ _ _
  have hL1 : ∀ u, L u ≤ 1 := fun u => by
    calc L u ≤ ∫ _z, (1 : ℝ) ∂probedClockLaw p.W p.b :=
          integral_mono_of_nonneg (Eventually.of_forall fun z => rv_leadAvg_nonneg _ _ _ _ _ _)
            (integrable_const _) (Eventually.of_forall fun z => rv_leadAvg_le_one _ _ _ _ _ _)
      _ = 1 := by simp
  -- the bound at one microscopic energy
  have hstep : ∀ u ∈ Icc (-U) U, a ^ 2 - 2 * a * ε ≤ C₃ * (3 * L u + 6 * ε) := by
    intro u hu
    set e := microEnergy p E u
    obtain ⟨he1, he2⟩ := hbulk u hu
    have hinv := rv_ae_isUnit_fullPathMatrix (b := p.b) hCount p.b_lt_half he1 he2 hW (p.n - 3)
    have hsq := rv_signedPassDerivative_sq_le (b := p.b) (e := e) (r := p.n - 3) hc hcG hCm0
      p.b_pos p.b_lt_half he1 he2 hx hy0 hy1 hW (rvCosineTest_abs_le τ m)
      (fun ω hH hM => hD p.b e p.b_pos p.b_lt_half he1 he2 p.W (p.n - 3) _ ω hH hM)
      (hG (Fin 2 × Fin p.W)) hinv (hmom u hu)
    have hZ := rv_ratio_integral_le m hτ p.b e hn hW
    have hI0 : 0 ≤ ∫ z, rvRatio (rvCosineTest τ m) p.b e p.W (p.n - 3) z ^ 2
        ∂probedClockLaw p.W p.b := integral_nonneg fun z => sq_nonneg _
    have hS : |signedPassDerivative p.b e x y p.W (p.n - 3) (rvCosineTest τ m) +
        8 * Real.pi * ρ * J| ≤ ε := by
      have := hpass u hu
      rw [hv] at this
      convert this using 2; ring
    have habs : |8 * Real.pi * ρ * J| = a := by
      have := semicircleDensity_pos hE1 hE2
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 8 * Real.pi * ρ)]
    have h1 := rv_sq_step hS hsq
    rw [habs] at h1
    have h2 : C₃ * ∫ z, rvRatio (rvCosineTest τ m) p.b e p.W (p.n - 3) z ^ 2
        ∂probedClockLaw p.W p.b ≤ C₃ * (3 * L u + 6 * ε) := by
      refine mul_le_mul_of_nonneg_left (hZ.trans ?_) hC₃0
      have := hport u hu
      simp only [L, e] at this ⊢
      nlinarith
    linarith
  -- integrate against `w`
  have hlead : leadOneMark p E w (rvFourierTest m) = ∫ u, w u * L u := rfl
  have hw := rv_weight_integrable w
  have hLm : Measurable L := by
    have hF := rv_measurable_leadAvg_of m p.b hn0 p.W
      (e := fun a : ℝ × (GrowthPath p.W × (Fin 2 × Fin p.W → ℂ)) => microEnergy p E a.1)
      (x := fun a => a.2) ((by unfold microEnergy; fun_prop : Measurable (microEnergy p E)).comp measurable_fst) measurable_snd
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := probedClockLaw p.W p.b)).measurable
  have hwL : Integrable (fun u => w u * L u) volume := by
    refine hw.norm.mono' ((w.toContinuousMap.continuous.measurable.mul hLm).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [norm_mul]
    have : ‖L u‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hL0 u)]; exact hL1 u
    exact mul_le_of_le_one_right (norm_nonneg _) this
  have hI1 : Integrable (fun u => w u * (a ^ 2 - 2 * a * ε)) volume := hw.mul_const _
  have hI2 : Integrable (fun u => w u * (C₃ * (3 * L u + 6 * ε))) volume := by
    refine ((hwL.const_mul (C₃ * 3)).add (hw.const_mul (C₃ * (6 * ε)))).congr
      (Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply]; ring
  have hmono : ∫ u, w u * (a ^ 2 - 2 * a * ε) ≤ ∫ u, w u * (C₃ * (3 * L u + 6 * ε)) := by
    refine integral_mono hI1 hI2 fun u => ?_
    by_cases hu : u ∈ Icc (-U) U
    · exact mul_le_mul_of_nonneg_left (hstep u hu) (w.nonnegative u)
    · simp only [hwU u hu, zero_mul, le_refl]
  have hleft : ∫ u, w u * (a ^ 2 - 2 * a * ε) = a ^ 2 - 2 * a * ε := by
    rw [integral_mul_const, w.integral_eq_one, one_mul]
  have hright : ∫ u, w u * (C₃ * (3 * L u + 6 * ε)) =
      C₃ * (3 * leadOneMark p E w (rvFourierTest m) + 6 * ε) := by
    have e1 : (fun u => w u * (C₃ * (3 * L u + 6 * ε))) =
        fun u => C₃ * 3 * (w u * L u) + C₃ * (6 * ε) * w u := by
      funext u; ring
    rw [e1, integral_add (hwL.const_mul _) (hw.const_mul _), integral_const_mul,
      integral_const_mul, w.integral_eq_one, hlead]
    ring
  rw [hleft, hright] at hmono
  exact hmono

end BlockBand.Endpoints
