module

public import BlockBand.SourceProcess.ContractingWords.LayerConsts

/-!
# The one-layer drift at one old two-port: assembly of the pieces

Identities and arithmetic used to assemble the one-layer drift bound at a fixed old two-port. They are
deterministic: they hold pointwise in the layer sample `y`, whose law is `freshLaw W b`.

* `posTr_new0`, `posTr_old`: the positional values are `newWord` (no injection)
  and `coreProd` (`Tr w(𝕏)`);
* `slot_mean_form`: `slot_mean` in the form of `first_match`;
* `drift_alg`: the exact splitting of the drift error into the injection, expansion,
  first-order and second-order remainders.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.SourceProcess.FullSourceGenerator BlockBand.Transmission.Bridge
open scoped Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

theorem posTr_new0 (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (w : TraceWord nT nI)
    (y : LayerSample W .oneBlockOnePort) :
    posTr (wl A w) (slotSep b E XX w + slotDelta b E XX w y) =
      layerNew b E A (fun _ => 0) XX w y := by
  have e : slotSep b E XX w + slotDelta b E XX w y =
      fun i => transportedSep b E XX (w.get i).2 y := funext fun i => by
    simp [slotSep, slotDelta]
  rw [e, posTr_word_const A (fun σ => transportedSep b E XX σ y) w, layerNew, newWord_zero]
  simp [wval, segProd, matWord, letWord, transportedSep, List.map_map, Function.comp_def]

theorem posTr_old (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (w : TraceWord nT nI) :
    posTr (wl A w) (slotSep b E XX w) = coreProd A (sepOf b E XX) [w] := by
  rw [coreProd_one]; exact posTr_word_const A (sepOf b E XX) w

/-- `slot_mean` in the form of `first_match`. -/
theorem slot_mean_form (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {M₁ M₂ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {Ω Ω' γ : ℂ} {ρ₁ ρ₂ : ℝ}
    (h1 : ‖M₁ - 1 - (Ω • (nearProjection W * twoPortScattering b E XX) +
      Ω' • ((twoPortScattering b E XX)ᴴ * nearProjection W))‖ ≤ ρ₁)
    (h2 : ‖M₂ - nearProjection W - (Ω • (nearProjection W * twoPortScattering b E XX *
      nearProjection W) + Ω' • (nearProjection W * (twoPortScattering b E XX)ᴴ * nearProjection W) -
        γ • nearProjection W)‖ ≤ ρ₂) (hρ : ρ₁ ≤ ρ₂)
    {s : Separator} (hs : s = .id ∨ s = .proj) (m : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hm : m = (if s = .proj then M₂ else M₁) - sepOf b E XX s) :
    ‖m - (Ω • sepOf b E XX (aSep s) + Ω' • sepOf b E XX (bSep s) -
      (if s = .proj then γ else 0) • sepOf b E XX s)‖ ≤ ρ₂ := by
  rcases hs with rfl | rfl
  · simp only [hm, aSep, bSep, reduceCtorEq, ↓reduceIte, zero_smul, sub_zero, sepOf]
    exact h1.trans hρ
  · simp only [hm, aSep, bSep, ↓reduceIte, sepOf]
    exact h2

/-- The exact splitting of the drift error. -/
theorem drift_alg (Ic I0 old Fi Se inj pC cnt Wi D g γ : ℂ) (hγ : γ = Wi * (D * g)) :
    Ic - old - Wi * (-(D * g * cnt * old) + pC + inj) =
      (Ic - I0 - Wi * inj) + (I0 - old - Fi - Se) + (Fi + γ * cnt * old) + (Se - Wi * pC) := by
  subst hγ; ring

theorem norm_add4_le (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a + b + c) d
  have h2 := norm_add_le (a + b) c
  have h3 := norm_add_le a b
  linarith

/-- The arithmetic of the final drift bound. -/
theorem drift_final {nI nE nF nS e R S₁ S₂ Ci Cx Cm Ck G d Γ g K : ℝ}
    (hI : nI ≤ Ci * e ^ 2) (hX : nE ≤ Cx * (1 + g) ^ 2 * R)
    (hF : nF ≤ (Cm * e + Cm * e) * S₁ + d * (Γ * (Cm * (1 + g) * e ^ 2)))
    (hS : nS ≤ 2 * (Ck * (W : ℝ)⁻¹) * S₂) (hWe : (W : ℝ)⁻¹ ≤ e) (he2 : e ^ 2 ≤ R)
    (hg0 : 0 ≤ g) (hg : g ≤ K ^ 2 / 2) (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂) (hCi : 0 ≤ Ci) (hCx : 0 ≤ Cx)
    (hCm : 0 ≤ Cm) (hCk : 0 ≤ Ck) (hd : 0 ≤ d) (hΓ : 0 ≤ Γ) (hΓG : Γ ≤ G) (he : 0 ≤ e) :
    nI + nE + nF + nS ≤ (2 * Cm + 2 * Ck) * e * (S₁ + S₂) +
      (Ci + Cx * (1 + K ^ 2 / 2) ^ 2 + d * G * Cm * (1 + K ^ 2 / 2)) * R := by
  have hR : 0 ≤ R := (sq_nonneg e).trans he2
  have h1 : Ci * e ^ 2 ≤ Ci * R := mul_le_mul_of_nonneg_left he2 hCi
  have hg2 : (1 + g) ^ 2 ≤ (1 + K ^ 2 / 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : Cx * (1 + g) ^ 2 * R ≤ Cx * (1 + K ^ 2 / 2) ^ 2 * R :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg2 hCx) hR
  have h3 : d * (Γ * (Cm * (1 + g) * e ^ 2)) ≤ d * G * Cm * (1 + K ^ 2 / 2) * R := by
    have : Cm * (1 + g) * e ^ 2 ≤ Cm * (1 + K ^ 2 / 2) * R :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCm) he2 (sq_nonneg _) (by positivity)
    calc d * (Γ * (Cm * (1 + g) * e ^ 2)) ≤ d * (G * (Cm * (1 + K ^ 2 / 2) * R)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hΓG this (by positivity) (hΓ.trans hΓG)) hd
      _ = _ := by ring
  have h4 : 2 * (Ck * (W : ℝ)⁻¹) * S₂ ≤ 2 * Ck * e * S₂ := by
    have := mul_le_mul_of_nonneg_left hWe hCk
    nlinarith
  have h5 : 0 ≤ 2 * Cm * e * S₂ := by positivity
  have h6 : 0 ≤ 2 * Ck * e * S₁ := by positivity
  nlinarith

end BlockBand.SourceProcess.ContractingWords
