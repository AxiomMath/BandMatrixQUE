module

public import BlockBand.Native.ErdosRiabov.VS.TailSum
public import BlockBand.Native.ErdosRiabov.Stochastic.ExpTailCoord

set_option autoImplicit false

/-!
# The propagated exponential tail

A deterministic linear image of the chain martingales, `∫_0^r ∑_α c_α(s) d𝓜^α_s` with `C²`
coefficients `c_α : ℝ → ℂ` (e.g. the coefficients of the propagator `P̂_{s,t}` at a fixed final
time `t`, which are affine in `s`), is represented without a stochastic integral as the
martingale part of the combination `F(r, Y_r) = ∑_α c_α(r) tr(K_α C_α(r, Y_r))`
(`chainComb`): `combMg r = N^Re_r + i N^Im_r`, where `N^Re`, `N^Im` are the compensated parts of
the continuous semimartingales `Re F`, `Im F` of `chainComb_ito_re/_im`. (By integration by
parts, `d(c F) = c' F dt + c dF`, its martingale part is `∫ c d𝓜`; this identification is not
formalized and not used.) The stopping at `τ` (`𝟙_{s<τ}`) enters through the event
`{∃ r ≤ T, r ≤ τ, …}`; `τ` is any `driverAugmented μ`-stopping time.

* **`propagated_tail`**: if a.s., for all `r ≤ T` with `r ≤ τ`, the integrated bracket in
  `d⟨𝓜, 𝓜̄⟩` form `∫_0^r ∑_{a,b} S_ab |∑_α c_α(s) tr(K_α firstVar_α(s)[e_ab])|² ds ≤ y`
  (`y > 0` deterministic), then for every `λ ≥ 0`
  `P(∃ r ≤ T, r ≤ τ, λ ≤ |combMg r|) ≤ 4 exp(-λ²/(4y))`.
  Proof: `measure_exists_norm_complex_compensated_ge_le` with the two
  real brackets, each bounded by the `d⟨𝓜, 𝓜̄⟩` integral (`combBracket_re_add_im` and
  nonnegativity).
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory Set Matrix Function
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.CEH.Flow
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

variable {p : BlockBand.Parameters} {k : ℕ} {ι : Type*} [Fintype ι]

/-- The real part process `Re F(t, Y_t - Y_0)` (one coordinate). -/
abbrev combProcRe (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (c : ι → ℝ → ℂ) : ℝ≥0 → RingSample p → Fin 1 → ℝ :=
  fun t x _ => linComb (combCoef c) (combTestRe A₀ zf B K) ((t : ℝ), vsNoise p t x)

/-- The imaginary part process `Im F(t, Y_t - Y_0)` (one coordinate). -/
abbrev combProcIm (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (c : ι → ℝ → ℂ) : ℝ≥0 → RingSample p → Fin 1 → ℝ :=
  fun t x _ => linComb (combCoef c) (combTestIm A₀ zf B K) ((t : ℝ), vsNoise p t x)

/-- Drift of `Re F` (Itô's formula at zero drift and covariance `diag v`). -/
abbrev combDriftRe (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (c : ι → ℝ → ℂ) : ℝ≥0 → RingSample p → Fin 1 → ℝ :=
  fun t x _ => itoDrift (linComb (combCoef c) (combTestRe A₀ zf B K)) (vsNoise p t x) t 0
    (diagonal (ringVariance p))

/-- Drift of `Im F`. -/
abbrev combDriftIm (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (c : ι → ℝ → ℂ) : ℝ≥0 → RingSample p → Fin 1 → ℝ :=
  fun t x _ => itoDrift (linComb (combCoef c) (combTestIm A₀ zf B K)) (vsNoise p t x) t 0
    (diagonal (ringVariance p))

/-- **The propagated complex martingale** `N^Re_t + i N^Im_t`: the martingale part of
`F(t, Y_t - Y_0) = ∑_α c_α(t) tr(K_α C_α)`. -/
def combMg (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (c : ι → ℝ → ℂ) (t : ℝ≥0) (x : RingSample p) : ℂ :=
  (smCompensated (combProcRe A₀ zf B K c) (combDriftRe A₀ zf B K c) 0 t x : ℂ) +
    (smCompensated (combProcIm A₀ zf B K c) (combDriftIm A₀ zf B K c) 0 t x : ℂ) * Complex.I

/-- **The propagated exponential tail (the complex exponential tail for a deterministic linear
image of `𝟙_{s<τ} d𝓜`).** Hermitian `A₀`, `C²` spectral parameters off the real axis, `C²`
coefficients
`c_α`, a `driverAugmented μ`-stopping time `τ`, a horizon `T` and a deterministic `y > 0` such
that a.s. the integrated `d⟨𝓜, 𝓜̄⟩` bracket is `≤ y` on `{r ≤ T, r ≤ τ}`. Then for `λ ≥ 0`:
`P(∃ r ≤ T, r ≤ τ, λ ≤ |combMg r|) ≤ 4 exp(-λ²/(4y))`. -/
theorem propagated_tail (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] {A₀ : RingMat p}
    (hA₀ : A₀.IsHermitian) {zf : ι → Fin k → ℝ → ℂ} (hzC : ∀ α j, ContDiff ℝ 2 (zf α j))
    (hzim : ∀ α j t, (zf α j t).im ≠ 0) (B : ι → Fin k → RingMat p) (K : ι → RingMat p)
    (c : ι → ℝ → ℂ) (hc : ∀ α, ContDiff ℝ 2 (c α)) {τ : RingSample p → WithTop ℝ≥0}
    (hτ : IsStoppingTime (driverAugmented (κ := Fin (ringDim p)) μ) τ) (T : ℝ≥0) {y : ℝ}
    (hy : 0 < y)
    (hbr : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ t : ℝ≥0, t ≤ T →
      (t : WithTop ℝ≥0) ≤ τ x → ∫ s in Ioc (0 : ℝ) t, ∑ a, ∑ b, shortRingProfile p.b p.n p.W a b *
        ‖combDir A₀ zf B K c (s.toNNReal : ℝ) (vsNoise p s.toNNReal x) (single a b 1)‖ ^ 2 ≤ y)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg A₀ zf B K c t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * y)))) := by
  have H₁ := chainComb_ito_re hA₀ hzC hzim μ B K c hc
  have H₂ := chainComb_ito_im hA₀ hzC hzim μ B K c hc
  have hboth : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ t : ℝ≥0, t ≤ T →
      (t : WithTop ℝ≥0) ≤ τ x →
      (∫ s in Ioc (0 : ℝ) t, combBracketRe A₀ zf B K c (s.toNNReal : ℝ)
          (vsNoise p s.toNNReal x) ≤ y) ∧
      ∫ s in Ioc (0 : ℝ) t, combBracketIm A₀ zf B K c (s.toNNReal : ℝ)
          (vsNoise p s.toNNReal x) ≤ y := by
    filter_upwards [hbr, H₁.integrable, H₂.integrable] with x hx h1 h2 t htT htτ
    have i1 := (h1 t).2 0 0
    have i2 := (h2 t).2 0 0
    simp only [Matrix.of_apply] at i1 i2
    have htot := hx t htT htτ
    have hsum : ∫ s in Ioc (0 : ℝ) t, (combBracketRe A₀ zf B K c (s.toNNReal : ℝ)
        (vsNoise p s.toNNReal x) + combBracketIm A₀ zf B K c (s.toNNReal : ℝ)
          (vsNoise p s.toNNReal x)) ≤ y := by
      simp only [combBracket_re_add_im]
      exact htot
    rw [integral_add i1 i2] at hsum
    have n1 : 0 ≤ ∫ s in Ioc (0 : ℝ) t, combBracketRe A₀ zf B K c (s.toNNReal : ℝ)
        (vsNoise p s.toNNReal x) :=
      setIntegral_nonneg measurableSet_Ioc fun s _ => combBracketRe_nonneg _ _ _ _ _ _ _
    have n2 : 0 ≤ ∫ s in Ioc (0 : ℝ) t, combBracketIm A₀ zf B K c (s.toNNReal : ℝ)
        (vsNoise p s.toNNReal x) :=
      setIntegral_nonneg measurableSet_Ioc fun s _ => combBracketIm_nonneg _ _ _ _ _ _ _
    exact ⟨by linarith, by linarith⟩
  exact measure_exists_norm_complex_compensated_ge_le H₁ H₂ hτ T hy
    (by filter_upwards [hboth] with x hx t htT htτ; exact (hx t htT htτ).1)
    (by filter_upwards [hboth] with x hx t htT htτ; exact (hx t htT htτ).2) hlam

end BlockBand.Native.ErdosRiabov.VS
