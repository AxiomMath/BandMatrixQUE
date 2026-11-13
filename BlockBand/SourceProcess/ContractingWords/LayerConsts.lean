module

public import BlockBand.SourceProcess.ContractingWords.InjMeanAll
public import BlockBand.Transmission.LawClauses.JetGap
public import BlockBand.SourceProcess.FullSourceGenerator.LoadBound

/-!
# Scalar facts for the one-layer hypotheses

* `fscK_same_le`: the same-sign coefficients `κ₂ = -σ₋/(4η²W)`, `κ₃ = -σ̄₋/(4η²W)` satisfy
  `|κ₂|, |κ₃| ≤ C/W`, `C = σ₊/(4η₀²)`, `η₀ = (1-b)κ/4` (`|σ₋| < σ₊`);
* `half_trace_current`: `½ Tr J² = g` as complex numbers for `J = A_J = currentOf 𝕏` Hermitian
  (`conductanceOf_eq_half_trace_sq`);
* `cond_le_K`: `g ≤ K²/2` when `Tr|J| ≤ K` (`Re Tr J² ≤ (Tr|J|)²`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.Bridge

variable {W nT nI : ℕ}

/-- **The same-sign coefficients are `O(W⁻¹)`**, bulk-uniform. -/
theorem fscK_same_le {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℕ) (E : ℝ), E ∈ bulkInterval κ → ∀ s : ℂ, IsStationaryJet b E s →
      ‖fscK b E s W 2‖ ≤ C * (W : ℝ)⁻¹ ∧ ‖fscK b E s W 3‖ ≤ C * (W : ℝ)⁻¹ := by
  set η₀ := (1 - b) * κ / 4
  have hη₀ : 0 < η₀ := by have : 0 < 1 - b := by linarith
                          positivity
  have hσ : 0 < sigmaPlus b := by
    simp only [sigmaPlus, kPlus]; have : 0 < 1 - 2 * b := by linarith
    positivity
  refine ⟨sigmaPlus b / (4 * η₀ ^ 2), by positivity, fun W E hE s hs => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hm := (BlockBand.Transmission.LawClauses.norm_sigmaMinus_lt_sigmaPlus hb0 hb h1 h2 hs).le
  have hη := BlockBand.SourceProcess.FullSource.etaZ_ge hb0 hb hκ hE
  have hη2 : η₀ ^ 2 ≤ etaZ b E ^ 2 := pow_le_pow_left₀ hη₀.le hη 2
  have key : ∀ z : ℂ, ‖z‖ ≤ sigmaPlus b →
      ‖-(z / ((4 * etaZ b E ^ 2 * W : ℝ) : ℂ))‖ ≤ sigmaPlus b / (4 * η₀ ^ 2) * (W : ℝ)⁻¹ := by
    intro z hz
    rw [norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rcases Nat.eq_zero_or_pos W with hW | hW
    · subst hW; simp
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    have hηp : 0 < etaZ b E := lt_of_lt_of_le hη₀ hη
    rw [div_le_iff₀ (by positivity)]
    calc ‖z‖ ≤ sigmaPlus b := hz
      _ = sigmaPlus b / (4 * η₀ ^ 2) * (W : ℝ)⁻¹ * (4 * η₀ ^ 2 * W) := by field_simp
      _ ≤ sigmaPlus b / (4 * η₀ ^ 2) * (W : ℝ)⁻¹ * (4 * etaZ b E ^ 2 * W) := by gcongr
  refine ⟨key _ hm, ?_⟩
  have : ‖(starRingEnd ℂ) (sigmaMinus b E s)‖ ≤ sigmaPlus b := by rw [Complex.norm_conj]; exact hm
  exact key _ this

/-- `½ Tr J² = g` for the current `J = currentOf 𝕏` of a Hermitian old two-port. -/
theorem half_trace_current {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) {J : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hJ : J = currentOf b E XX) (hJh : J.IsHermitian) :
    (1 / 2 : ℂ) * (J * J).trace =
      ((conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) : ℝ) : ℂ) := by
  rw [conductanceOf_eq_half_trace_sq b E XX hXX hη, ← currentOf, ← hJ, sq]
  have e : (J * J).trace = (((J * J).trace.re : ℝ) : ℂ) := by
    have h := BlockBand.SourceProcess.FullSource.trace_factor_eq_re J
    rwa [hJh.eq] at h
  conv_lhs => rw [e]
  push_cast; ring

/-- `g ≤ K²/2` when the current letter has `Tr|J| ≤ K`. -/
theorem cond_le_K {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) {J : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hJ : J = currentOf b E XX) (hJh : J.IsHermitian) {K : ℝ}
    (hJK : nuclearNorm J ≤ K) :
    conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) ≤ K ^ 2 / 2 := by
  rw [conductanceOf_eq_half_trace_sq b E XX hXX hη, ← currentOf, ← hJ, sq]
  have h1 := BlockBand.SourceProcess.FullSourceGenerator.trace_mul_self_re_le hJh
  have h2 : nuclearNorm J ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (BlockBand.SourceProcess.FullSourceGenerator.nuclearNorm_nonneg' J) hJK 2
  linarith

end BlockBand.SourceProcess.ContractingWords
