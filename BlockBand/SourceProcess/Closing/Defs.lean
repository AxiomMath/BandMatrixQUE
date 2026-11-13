module

public import BlockBand.SourceProcess.SourceProcessLaw.Sampling
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# The closed physical process: omitted far channels closed with a phase

At the closing time `s` (path length `n_s = ⌊Ws⌋`) the far input channels of the omitted
transmission modes `t_i ≤ h²` span the range of `A_- = 1_{[0,h²]}(T_far(s))`, where
`T_far = I - S_ffᴴ S_ff` is the far-input transmission of `𝕊(s)` (Lean port `1` = far). Mode `i`
with far input `e_i` has reflected far output `f_i = S_ff e_i/√(1-t_i)`; `A_+` is spanned by the
`f_i` and the pairing `Π = Σ_i e_i f_i* = g(T_far) S_ffᴴ`, `g(t) = 1_{t≤h²}(1-t)^{-1/2}`, maps the
paired far output back to the far input. Both are basis free (`cfc`).

At the final length `n = ⌊WT⌋` the far port is the same lead (the path grows at the near end), so
closing at time `s` or at final time eliminates the same linear equations. Closing `A`
with one phase `z` imposes `a = zΠ𝕊(h_B + a)` on the omitted inputs `a = A a`, whence the
retained input `h_B = (1-A)h` produces the boundary input `C(z)h` with
`C(z) = (1 - A) + (1 - zN)⁻¹ z T`, `N = Π𝕊A` (`r = S_AA`), `T = Π𝕊(1-A)` (`t = S_AB`); that is
`F_B^cl(z) = F_B + F_A z(I - rz)^{-1} t` with source maps `F = P_k𝒰_n`. A sampled source
`\widehat Q = Σ w v v*` (`v = 𝒰_n*ι_k g`, `sampledSource`) becomes `C(z)ᴴ \widehat Q C(z)`,
and `closedSampledTransform` is the sampled transform of the closed path, with one independent
uniform phase for all probes and factors.

Measurability note: `x ↦ closedSampledTransform`'s integrand involves `cfc` of a discontinuous
function of `T_far`; it is Borel (spectral projections of a measurable Hermitian matrix are
measurable); this is proved as `measurable_closedIntegrand`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Closing

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw
open scoped ENNReal NNReal Matrix

/-!
## The closing map (pure algebra)
-/

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `N = Π𝕊A`: the omitted-to-omitted block `r = S_AA` read through the pairing. -/
def closingN (S A Pi : Matrix ι ι ℂ) : Matrix ι ι ℂ := Pi * S * A

/-- `T = Π𝕊(1-A)`: the retained-to-omitted block `t = S_AB`. -/
def closingT (S A Pi : Matrix ι ι ℂ) : Matrix ι ι ℂ := Pi * S * (1 - A)

/-- **The closing map** `C(z) = (1 - A) + (1 - zN)⁻¹ zT`: the boundary input of the path
whose omitted channels `A` are closed by `a = zΠ𝕊(h_B + a)`, for the retained input `(1-A)h`. -/
def closingMap (S A Pi : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (1 - A) + (1 - z • closingN S A Pi)⁻¹ * (z • closingT S A Pi)

/-- Nothing omitted: closing changes nothing. -/
theorem closingMap_zero (S : Matrix ι ι ℂ) (z : ℂ) : closingMap S 0 0 z = 1 := by
  simp [closingMap, closingN, closingT]

end Algebra

/-!
## Far-port closing data at time `s`
-/

variable {W : ℕ}

/-- The far reflection block `S_ff` of `𝕊` at length `n` (far input to far output). -/
def farReflection (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  portBlock (scatteringMatrix b E W n ω) 1 1

/-- The far-input transmission `T_far = I - S_ffᴴ S_ff` at length `n` (its nonzero eigenvalues
are the transmission eigenvalues `t_i`). -/
def farTransmission (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  1 - (farReflection b E W n ω)ᴴ * farReflection b E W n ω

theorem isHermitian_farTransmission (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    (farTransmission b E W n ω).IsHermitian := by
  unfold farTransmission
  exact isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)

/-- The omitted-mode indicator `1_{t ≤ h²}`. -/
def omitIndicator (h : ℝ) (t : ℝ) : ℝ := if t ≤ h ^ 2 then 1 else 0

/-- The pairing weight `g(t) = 1_{t ≤ h²}(1-t)^{-1/2}`. -/
def pairWeight (h : ℝ) (t : ℝ) : ℝ := if t ≤ h ^ 2 then (Real.sqrt (1 - t))⁻¹ else 0

/-- `A_-`: the far input projection of the omitted modes `t_i ≤ h²` at length `n`. -/
def omittedProj (b E h : ℝ) (W n : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  cfc (omitIndicator h) (farTransmission b E W n ω)

/-- The pairing `Π = Σ_{t_i ≤ h²} e_i f_i* = g(T_far) S_ffᴴ` of the omitted far outputs with the
omitted far inputs at length `n`. -/
def closingPairing (b E h : ℝ) (W n : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  cfc (pairWeight h) (farTransmission b E W n ω) * (farReflection b E W n ω)ᴴ

/-- A far-port matrix placed on the far block of the two-port space. -/
def farEmbed (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  Matrix.of fun x y => if x.1 = 1 ∧ y.1 = 1 then X x.2 y.2 else 0

/-- **The physical closing map**: omitted channels chosen at `n_s = ⌊Ws⌋` (cutoff `h`), closed with
phase `z` at the final length `n = ⌊WT⌋`. -/
def physClosingMap (b E s T h : ℝ) (W : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  closingMap (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)
    (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
    (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)) z

/-!
## The uniform phase and the closed sampled transform
-/

/-- The uniform phase `θ ∈ [0, 2π)`, `z = e^{iθ}`. -/
def phaseLaw : Measure ℝ :=
  ENNReal.ofReal (2 * Real.pi)⁻¹ • volume.restrict (Set.Ico 0 (2 * Real.pi))

/-- `z = e^{iθ}`. -/
def phase (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

instance isProbabilityMeasure_phaseLaw : IsProbabilityMeasure phaseLaw := by
  constructor
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  simp only [phaseLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ico, sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ h2.ne', ENNReal.ofReal_one]

/-- **The closed sampled transform** `E_{path, samples, z} Π_j det(I + C(z)ᴴ(Σ_a a_{j,a}
\widehat Q_{M,a})C(z))⁻¹` of the physical path of length `⌊WT⌋` whose omitted channels
(`t_i ≤ h²` at time `s`) are closed with one uniform phase `z`; the same samples as
`sampledPhysTransform`. -/
def closedSampledTransform (b E s T h : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) (M W : ℕ) : ℝ :=
  ∫ y, ∏ j, (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      (physClosingMap b E s T h W y.1.1 (phase y.2))ᴴ *
        (∑ i, (a j i : ℂ) • sampledSource b E W ⌊(W : ℝ) * T⌋₊ (q i) M
          (fun l => y.1.2.1 (i, l)) (fun l => y.1.2.2 (i, l)) y.1.1) *
        physClosingMap b E s T h W y.1.1 (phase y.2)).det⁻¹).re
    ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw)

end BlockBand.SourceProcess.Closing
