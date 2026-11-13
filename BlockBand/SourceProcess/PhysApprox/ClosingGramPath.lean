module

public import BlockBand.SourceProcess.PhysApprox.ClosingGramCavity
public import BlockBand.SourceProcess.PhysApprox.Meas
public import BlockBand.SourceProcess.Closing.PhysHardy
public import BlockBand.Transmission.Bridge.Scattering
public import BlockBand.Transmission.Bridge.Current

/-!
# The Gram closing errors at one path, probe sample and phase

Fix a probed path `x`, a phase `z`, and write `V = probeFrame`, `C = physClosingMap`,
`V_cl = CᴴV`, `D = V_cl - V`, `H = P𝕊Z(z)V` (`Z = closingZ`, `P = nearProjection`). For `r ≠ 0`
(`gramErr_le`):
`|closedSourceData r - complexSourceData r|ᵢₖ ≤ (aᵢdₖ + dᵢaₖ + dᵢdₖ) + (aᵢeₖ + eᵢaₖ + eᵢeₖ)`,
`a = ‖V·‖`, `d = ‖D·‖`, `e = ‖H·‖` (column norms). `r = 1, 2`: Gram differences of `V + D`
(`P` contracts). `r = 3`: `P𝕊CV_cl = P𝕊(1 + Z + Zᴴ)V = P𝕊V + H` (`closingMap_mul_conj`,
`P𝕊Zᴴ = 0`), so `J_cl - J` is the Gram difference of `P𝕊V + H` minus that of `r = 2`. The
hypotheses of `r = 3` (`A² = A`, `ΠΠᴴ = A`, `𝕊` unitary, `1 - zN` invertible, `|z| = 1`) hold
almost surely for `h² < 1` and large `W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingLeak BlockBand.Transmission.Bridge

section Generic

variable {ρ c κ : Type*} [Fintype ρ]

theorem mul_transpose_apply_eq (M : Matrix κ ρ ℂ) (F : Matrix ρ c ℂ) (k : c) :
    (M * F)ᵀ k = M *ᵥ Fᵀ k := by
  ext x
  simp [Matrix.mul_apply, mulVec, dotProduct]

end Generic

theorem gram_bound_mono {xi xk yi yk Xi Xk Yi Yk : ℝ} (hxi : xi ≤ Xi) (hxk : xk ≤ Xk)
    (hyi : yi ≤ Yi) (hyk : yk ≤ Yk) (h0xi : 0 ≤ xi) (h0xk : 0 ≤ xk) (h0yi : 0 ≤ yi)
    (h0yk : 0 ≤ yk) : xi * yk + yi * xk + yi * yk ≤ Xi * Yk + Yi * Xk + Yi * Yk :=
  add_le_add (add_le_add (mul_le_mul hxi hyk h0yk (h0xi.trans hxi))
    (mul_le_mul hyi hxk h0xk (h0yi.trans hyi))) (mul_le_mul hyi hyk h0yk (h0yi.trans hyi))

variable {W : ℕ}

theorem nearProjection_mul_farEmbed (Y : Matrix (Fin W) (Fin W) ℂ) :
    nearProjection W * farEmbed Y = 0 := by
  ext x y
  simp only [nearProjection, farEmbed, Matrix.diagonal_mul, Matrix.of_apply, Matrix.zero_apply]
  by_cases hx : x.1 = 0
  · simp [hx]
  · simp [hx]

/-- The closing data of the physical path at `(ns, n)`. -/
structure ClosingHyp (b E h : ℝ) (ns n : ℕ) (ω : GrowthPath W) (z : ℂ) : Prop where
  unitary : scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1
  unitary' : (scatteringMatrix b E W n ω)ᴴ * scatteringMatrix b E W n ω = 1
  hh : h ^ 2 < 1
  unit : IsUnit (1 - z • closingN (scatteringMatrix b E W n ω)
    (farEmbed (omittedProj b E h W ns ω)) (farEmbed (closingPairing b E h W ns ω))).det
  norm_one : z * star z = 1

/-- **Pathwise Gram closing bound** for `r ≠ 0`. -/
theorem gramErr_le (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (x : ProbedPath W np) (z : ℂ)
    (hH : ClosingHyp b E h ⌊(W : ℝ) * s⌋₊ ⌊(W : ℝ) * T⌋₊ x.1 z) (r : Fin 4) (hr : r ≠ 0)
    (i k : Fin np) :
    ‖closedSourceData b E s T h τ m W z x r i k -
        complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m x r i k‖ ≤
      (l2 ((probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ i) *
          l2 ((closedFrame b E s T h τ m W z x - probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ k) +
        l2 ((closedFrame b E s T h τ m W z x - probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ i) *
          l2 ((probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ k) +
        l2 ((closedFrame b E s T h τ m W z x - probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ i) *
          l2 ((closedFrame b E s T h τ m W z x - probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ k)) +
      (l2 ((probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ i) *
          l2 ((nearProjection W * scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 *
            closingZ (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1)
              (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ x.1))
              (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1)) z *
            probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ k) +
        l2 ((nearProjection W * scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 *
            closingZ (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1)
              (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ x.1))
              (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1)) z *
            probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ i) *
          l2 ((probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ k) +
        l2 ((nearProjection W * scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 *
            closingZ (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1)
              (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ x.1))
              (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1)) z *
            probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ i) *
          l2 ((nearProjection W * scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 *
            closingZ (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1)
              (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ x.1))
              (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1)) z *
            probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ k)) := by
  -- names
  set S := scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 with hSdef
  set A := farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ x.1) with hAdef
  set Pi := farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1) with hPidef
  set P := nearProjection W with hPdef
  set V := probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x with hVdef
  set Vc := closedFrame b E s T h τ m W z x with hVcdef
  set C := physClosingMap b E s T h W x.1 z with hCdef
  set Z := closingZ S A Pi z with hZdef
  set H := P * S * Z * V with hHdef
  have hP2 : P * P = P := nearProjection_mul_self
  have hPH : Pᴴ = P := nearProjection_conjTranspose
  have hVc : Vc = V + (Vc - V) := (add_sub_cancel V Vc).symm
  have hPcol : ∀ (F : Matrix (Fin 2 × Fin W) (Fin np) ℂ) (j : Fin np),
      l2 ((P * F)ᵀ j) ≤ l2 (Fᵀ j) := fun F j => by
    rw [mul_transpose_apply_eq]
    exact l2_mulVec_le_of_proj hP2 hPH _
  have hPV : ∀ F : Matrix (Fin 2 × Fin W) (Fin np) ℂ, Fᴴ * P * F = (P * F)ᴴ * (P * F) := by
    intro F
    rw [conjTranspose_mul, hPH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P F, hP2]
  -- the `r = 2` bound
  have hB : ‖(Vcᴴ * P * Vc - Vᴴ * P * V) i k‖ ≤
      l2 (Vᵀ i) * l2 ((Vc - V)ᵀ k) + l2 ((Vc - V)ᵀ i) * l2 (Vᵀ k) +
        l2 ((Vc - V)ᵀ i) * l2 ((Vc - V)ᵀ k) := by
    rw [hPV, hPV]
    conv_lhs => rw [hVc]
    rw [Matrix.mul_add]
    exact (norm_gram_sub_apply_le _ _ i k).trans (gram_bound_mono (hPcol V i) (hPcol V k)
      (hPcol (Vc - V) i) (hPcol (Vc - V) k) (l2_nonneg _) (l2_nonneg _) (l2_nonneg _)
      (l2_nonneg _))
  have hM : ‖(Vcᴴ * Vc - Vᴴ * V) i k‖ ≤
      l2 (Vᵀ i) * l2 ((Vc - V)ᵀ k) + l2 ((Vc - V)ᵀ i) * l2 (Vᵀ k) +
        l2 ((Vc - V)ᵀ i) * l2 ((Vc - V)ᵀ k) := by
    conv_lhs => rw [hVc]
    exact norm_gram_sub_apply_le V (Vc - V) i k
  have he0 : 0 ≤ l2 (Vᵀ i) * l2 (Hᵀ k) + l2 (Hᵀ i) * l2 (Vᵀ k) + l2 (Hᵀ i) * l2 (Hᵀ k) := by
    have := l2_nonneg (Vᵀ i); have := l2_nonneg (Hᵀ k); have := l2_nonneg (Hᵀ i)
    have := l2_nonneg (Vᵀ k)
    positivity
  fin_cases r
  · exact (hr rfl).elim
  · change ‖(Vcᴴ * Vc - Vᴴ * V) i k‖ ≤ _
    linarith
  · change ‖(Vcᴴ * P * Vc - Vᴴ * P * V) i k‖ ≤ _
    linarith
  · -- `r = 3`
    have hA2 : A * A = A := by rw [hAdef, farEmbed_mul, omittedProj_mul_self]
    have hAH : Aᴴ = A := by rw [hAdef, farEmbed_conjTranspose, omittedProj_conjTranspose]
    have hPi : Pi * Piᴴ = A := by
      rw [hPidef, hAdef, farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hH.hh]
    have hSS : S * Sᴴ = 1 := hH.unitary
    have hCC : C * Cᴴ = 1 + Z + Zᴴ :=
      closingMap_mul_conj hA2 hAH hPi hH.unitary hH.norm_one hH.unit
    have hPZ : P * S * Zᴴ = 0 := by
      rw [hZdef, closingZ, conjTranspose_smul, conjTranspose_mul, conjTranspose_mul,
        Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc P S,
        hSS, Matrix.mul_one, hPidef, farEmbed_conjTranspose, hPdef,
        nearProjection_mul_farEmbed, Matrix.zero_mul, smul_zero]
    have hG : P * S * C * Vc = P * S * V + H := by
      rw [hVcdef, closedFrame, ← hCdef, ← hVdef, ← Matrix.mul_assoc, Matrix.mul_assoc (P * S) C,
        hCC, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.add_mul, hPZ,
        Matrix.zero_mul, add_zero, hHdef]
    have hJ : Vcᴴ * (Cᴴ * Sᴴ * P * S * C - P) * Vc - Vᴴ * (Sᴴ * P * S - P) * V =
        ((P * S * V + H)ᴴ * (P * S * V + H) - (P * S * V)ᴴ * (P * S * V)) -
          (Vcᴴ * P * Vc - Vᴴ * P * V) := by
      have e1 : Vcᴴ * (Cᴴ * Sᴴ * P * S * C - P) * Vc =
          (P * S * C * Vc)ᴴ * (P * S * C * Vc) - Vcᴴ * P * Vc := by
        have : Cᴴ * Sᴴ * P * S * C = (P * S * C)ᴴ * (P * S * C) := by
          rw [conjTranspose_mul, conjTranspose_mul, hPH]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc P P, hP2]
        rw [this, Matrix.mul_sub, Matrix.sub_mul, conjTranspose_mul (P * S * C) Vc]
        simp only [Matrix.mul_assoc]
      have e2 : Vᴴ * (Sᴴ * P * S - P) * V = (P * S * V)ᴴ * (P * S * V) - Vᴴ * P * V := by
        rw [Matrix.mul_sub, Matrix.sub_mul, conjTranspose_mul, conjTranspose_mul, hPH]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P P, hP2]
      rw [e1, e2, hG]
      abel
    have hcl : closedSourceData b E s T h τ m W z x 3 = Vcᴴ * (Cᴴ * Sᴴ * P * S * C - P) * Vc := rfl
    have hph : complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m x 3 = Vᴴ * (Sᴴ * P * S - P) * V := rfl
    change ‖closedSourceData b E s T h τ m W z x 3 i k -
        complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m x 3 i k‖ ≤ _
    rw [← Matrix.sub_apply, hcl, hph, hJ, Matrix.sub_apply]
    refine (norm_sub_le _ _).trans ?_
    have hJG := norm_gram_sub_apply_le (P * S * V) H i k
    have hSV : ∀ j, l2 ((P * S * V)ᵀ j) ≤ l2 (Vᵀ j) := fun j => by
      rw [Matrix.mul_assoc, mul_transpose_apply_eq, mul_transpose_apply_eq]
      exact (l2_mulVec_le_of_proj hP2 hPH _).trans (l2_mulVec_of_unitary hH.unitary' _).le
    have hmono := gram_bound_mono (hSV i) (hSV k) (le_refl (l2 (Hᵀ i))) (le_refl (l2 (Hᵀ k)))
      (l2_nonneg _) (l2_nonneg _) (l2_nonneg _) (l2_nonneg _)
    linarith

end BlockBand.SourceProcess.PhysApprox
