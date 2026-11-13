module

public import BlockBand.SourceProcess.SmallLeak.Sandwich

/-!
# The one-layer source leakage bound

At a deterministic Hermitian old two-port `𝕏`, a far projection `F = farEmbed A` and a positive old
source `Q = R*R` (`γ = Tr Q = ‖R‖₂²`, `ℓ = Re Tr FQF`, `g = Re Tr FP'F`), if the fresh `Δ` has
`‖EΔ‖ ≤ m` and bilinear `L²` fluctuations `≤ σ‖u‖‖v‖`, then (`leak_fresh_mean`)

`E_f Re Tr F N*QN ≤ ℓ + (m/η) γ √g + ((m² + σ²)/(2η²)) γ g`.

With `m = C(δ₀ + W⁻¹)`, `σ = C(W^{-1/2} + δ₀)` this is the paper's bound
`E_jℓ_{A,+} - ℓ_A ≤ Cγ[(δ₀ + W⁻²)√g + (W⁻¹ + δ₀²)g]` (with `W⁻¹` for `W⁻²` in the mean, which
the summation absorbs). The newborn block adds `c Re Tr F D₊*D₊ = c‖(𝒢₁₁K)ιℝF‖₂²`
(`birth_leak_le`): a normalized tag's far birth mass is `O(g/W)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.CompleteSourceGap
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem norm_farEmbed_le {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A) (hA2 : A * A = A) :
    ‖farEmbed A‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (farEmbed A)
  rw [farEmbed_conjTranspose_of hA, farEmbed_mul, hA2] at h
  rcases (norm_nonneg (farEmbed A)).eq_or_lt with h0 | h0
  · rw [← h0]; exact zero_le_one
  · nlinarith

/-- `‖ιℝF‖₂ = √g/(2η)`. -/
theorem hsNorm_leakInput {b E : ℝ} (hη : 0 < etaZ b E)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A) :
    hsNorm (leakInput b E XX (farEmbed A)) = Real.sqrt (farEmbed A *
      ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX) *
        farEmbed A).trace.re / (2 * etaZ b E) := by
  rw [← hsNorm_sq_nearOut XX hA, Real.sqrt_sq (hsNorm_nonneg _), hsNorm_nearScat_eq hη XX A]
  field_simp

/-- **The one-layer leakage bound.** -/
theorem leak_fresh_mean {b E : ℝ} (hη : 0 < etaZ b E)
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : Aᴴ = A) (hA2 : A * A = A) {κ : Type*} [Fintype κ] (R : Matrix κ (Fin 2 × Fin W) ℂ)
    (hΔ : ∀ x y, Integrable (fun f => freshDelta b E (nearSchur (boundaryZ b E) XX) f x y)
      (freshLaw W b))
    (hmeas : Measurable (freshDelta b E (nearSchur (boundaryZ b E) XX)))
    {m σ : ℝ} (hσ : 0 ≤ σ)
    (hm : ‖matrixExpect (freshLaw W b) (freshDelta b E (nearSchur (boundaryZ b E) XX))‖ ≤ m)
    (hfl : ∀ u v : Fin W → ℂ, eLpNorm (fun f => bilinear u
      (freshDelta b E (nearSchur (boundaryZ b E) XX) f -
        matrixExpect (freshLaw W b) (freshDelta b E (nearSchur (boundaryZ b E) XX))) v)
      (ENNReal.ofReal 2) (freshLaw W b) ≤ ENNReal.ofReal (σ * vecNorm u * vecNorm v)) :
    ∫ f, (farEmbed A * ((freshTransport b E XX f)ᴴ * (Rᴴ * R) * freshTransport b E XX f)).trace.re
        ∂freshLaw W b ≤
      (farEmbed A * (Rᴴ * R) * farEmbed A).trace.re +
        m / etaZ b E * hsNorm R ^ 2 * Real.sqrt (farEmbed A *
          ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX) *
            farEmbed A).trace.re +
        (m ^ 2 + σ ^ 2) / (2 * etaZ b E ^ 2) * hsNorm R ^ 2 * (farEmbed A *
          ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX) *
            farEmbed A).trace.re := by
  set F := farEmbed A
  set Q := Rᴴ * R
  set V := leakInput b E XX F
  set Δ := freshDelta b E (nearSchur (boundaryZ b E) XX)
  set D := matrixExpect (freshLaw W b) Δ
  set g := (F * ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX) *
    F).trace.re
  set Y := nearSel W * Q * F
  set U := R * (nearSel W)ᴴ
  have hF : Fᴴ = F := farEmbed_conjTranspose_of hA
  have hF2 : F * F = F := by rw [farEmbed_mul, hA2]
  have hQ : Qᴴ = Q := by simp [Q, Matrix.conjTranspose_mul]
  have hg0 : 0 ≤ g := by
    have : hsNorm (nearSel W * twoPortScattering b E XX * F) ^ 2 = g := hsNorm_sq_nearOut XX hA
    rw [← this]; positivity
  have hV : hsNorm V = Real.sqrt g / (2 * etaZ b E) := hsNorm_leakInput hη XX hA
  -- the pointwise identity
  have hpt : ∀ f, (F * ((freshTransport b E XX f)ᴴ * Q * freshTransport b E XX f)).trace.re =
      (F * Q * F).trace.re + 2 * (Vᴴ * (Δ f)ᴴ * Y).trace.re + hsNorm (U * Δ f * V) ^ 2 := by
    intro f
    rw [leak_step_eq (freshTransport_mul_farEmbed b E XX f A) hF hF2 hQ]
    have e1 : ((nearSel W)ᴴ * (Δ f * V))ᴴ * Q * F = Vᴴ * (Δ f)ᴴ * Y := by
      simp only [Y, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have e2 : (((nearSel W)ᴴ * (Δ f * V))ᴴ * Q * ((nearSel W)ᴴ * (Δ f * V))).trace.re =
        hsNorm (U * Δ f * V) ^ 2 := by
      have h := trace_conjTranspose_mul_self (U * Δ f * V)
      have e : (U * Δ f * V)ᴴ * (U * Δ f * V) =
          ((nearSel W)ᴴ * (Δ f * V))ᴴ * Q * ((nearSel W)ᴴ * (Δ f * V)) := by
        simp only [U, Q, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      rw [e] at h
      rw [h, Complex.ofReal_re]
    rw [e1, e2]
  obtain ⟨hlinI, hlin⟩ := integral_trace_lin (μ := freshLaw W b) Δ hΔ V Y
  -- the norms
  have hYle : hsNorm Y ≤ hsNorm R ^ 2 := by
    have h1 : hsNorm Y ≤ hsNorm (Q * F) := by
      have := hsNorm_mul_le_opNorm (nearSel W) (Q * F)
      have hn : ‖nearSel W‖ ≤ 1 := norm_nearSel_le
      rw [show Y = nearSel W * (Q * F) from Matrix.mul_assoc _ _ _]
      nlinarith [hsNorm_nonneg (Q * F)]
    have h2 : hsNorm (Q * F) ≤ hsNorm R ^ 2 := by
      have hRF : hsNorm (R * F) ≤ hsNorm R := by
        rw [← hsNorm_conjTranspose (R * F), Matrix.conjTranspose_mul, hF,
          ← hsNorm_conjTranspose R]
        have := hsNorm_mul_le_opNorm F Rᴴ
        have hn := norm_farEmbed_le hA hA2
        nlinarith [hsNorm_nonneg Rᴴ]
      rw [show Q * F = Rᴴ * (R * F) from Matrix.mul_assoc _ _ _]
      refine (hsNorm_mul_le _ _).trans ?_
      rw [hsNorm_conjTranspose, sq]
      exact mul_le_mul_of_nonneg_left hRF (hsNorm_nonneg _)
    exact h1.trans h2
  have hU : hsNorm U ≤ hsNorm R := by
    rw [← hsNorm_conjTranspose U]
    simp only [U, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have := hsNorm_mul_le_opNorm (nearSel W) Rᴴ
    have hn : ‖nearSel W‖ ≤ 1 := norm_nearSel_le
    rw [← hsNorm_conjTranspose R]
    nlinarith [hsNorm_nonneg Rᴴ]
  have hsq : Real.sqrt g * Real.sqrt g = g := Real.mul_self_sqrt hg0
  have hlin_le : 2 * (Vᴴ * Dᴴ * Y).trace.re ≤ m / etaZ b E * hsNorm R ^ 2 * Real.sqrt g := by
    have h1 := (abs_le.mp (abs_trace_lin_le D V Y)).2
    have hm0 : 0 ≤ m := (norm_nonneg _).trans hm
    have h2 : ‖D‖ * hsNorm V * hsNorm Y ≤ m * (Real.sqrt g / (2 * etaZ b E)) * hsNorm R ^ 2 := by
      rw [hV]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hm (by positivity)) hYle (hsNorm_nonneg _)
        (by positivity)
    have h3 : m * (Real.sqrt g / (2 * etaZ b E)) * hsNorm R ^ 2 =
        m / etaZ b E * hsNorm R ^ 2 * Real.sqrt g / 2 := by
      field_simp
    linarith
  have hquad := integral_hsNorm_sq_le (μ := freshLaw W b) Δ hmeas U V hσ hm hfl
  have hquad' : 2 * (m ^ 2 + σ ^ 2) * hsNorm U ^ 2 * hsNorm V ^ 2 ≤
      (m ^ 2 + σ ^ 2) / (2 * etaZ b E ^ 2) * hsNorm R ^ 2 * g := by
    rw [hV, div_pow, Real.sq_sqrt hg0]
    have hU2 : hsNorm U ^ 2 ≤ hsNorm R ^ 2 := pow_le_pow_left₀ (hsNorm_nonneg _) hU 2
    have e : 2 * (m ^ 2 + σ ^ 2) * hsNorm R ^ 2 * (g / (2 * etaZ b E) ^ 2) =
        (m ^ 2 + σ ^ 2) / (2 * etaZ b E ^ 2) * hsNorm R ^ 2 * g := by
      field_simp
    rw [← e]
    gcongr
  have hℓ : 0 ≤ (F * Q * F).trace.re := by
    have : F * Q * F = (R * F)ᴴ * (R * F) := by
      simp only [Q, Matrix.conjTranspose_mul, hF, Matrix.mul_assoc]
    rw [this]; exact FullSource.trace_factor_re_nonneg _
  by_cases hI : Integrable (fun f => (F * ((freshTransport b E XX f)ᴴ * Q *
      freshTransport b E XX f)).trace.re) (freshLaw W b)
  · have hsqI : Integrable (fun f => hsNorm (U * Δ f * V) ^ 2) (freshLaw W b) := by
      have := (hI.sub (integrable_const ((F * Q * F).trace.re))).sub (hlinI.const_mul 2)
      refine this.congr (Filter.Eventually.of_forall fun f => ?_)
      simp only [Pi.sub_apply]; rw [hpt f]; ring
    calc _ = ∫ f, ((F * Q * F).trace.re + 2 * (Vᴴ * (Δ f)ᴴ * Y).trace.re +
          hsNorm (U * Δ f * V) ^ 2) ∂freshLaw W b := integral_congr_ae
            (Filter.Eventually.of_forall hpt)
      _ = (F * Q * F).trace.re + 2 * (Vᴴ * Dᴴ * Y).trace.re +
          ∫ f, hsNorm (U * Δ f * V) ^ 2 ∂freshLaw W b := by
          have hI1 : Integrable (fun f => (F * Q * F).trace.re +
              2 * (Vᴴ * (Δ f)ᴴ * Y).trace.re) (freshLaw W b) :=
            (integrable_const _).add (hlinI.const_mul 2)
          rw [integral_add hI1 hsqI, integral_add (integrable_const _) (hlinI.const_mul 2),
            integral_const, integral_const_mul, hlin]
          simp [D]
      _ ≤ _ := by linarith
  · rw [integral_undef hI]
    have : 0 ≤ m / etaZ b E * hsNorm R ^ 2 * Real.sqrt g := by
      have hm0 : 0 ≤ m := (norm_nonneg _).trans hm
      positivity
    have : 0 ≤ (m ^ 2 + σ ^ 2) / (2 * etaZ b E ^ 2) * hsNorm R ^ 2 * g := by positivity
    linarith

end BlockBand.SourceProcess.SmallLeak
