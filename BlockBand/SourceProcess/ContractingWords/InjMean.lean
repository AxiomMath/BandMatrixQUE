module

public import BlockBand.SourceProcess.ContractingWords.InjMoments
public import BlockBand.SourceProcess.ContractingWords.AliveLetters
public import BlockBand.SourceProcess.ContractingWords.IncrementHolds

/-!
# The mean injection into a one-letter word

Measure `freshLaw W b`; deterministic Hermitian
`𝕏`; tests `|q_a| ≤ c₀`; `e = layerErr`. The injection: `Tr Q_a` and `Tr(Q_aP)` of an
interval source receive `d_*q_a(t)`, no other word.

`inj_single_mean`: for `w = [(ℓ, s)]`, `s ∈ {I, P}`, the injection is `c_ℓ Tr(D*D S_s)` exactly
(`newWord_single_sub`); for an interval letter `c = q/W²`, and given
`|W⁻¹E Tr(D*DP) - d_*| ≤ C_n(δ + g/W)` and `|E Tr(D*D(1-P))| ≤ C_f g` (supplied in `InjMeanAll` by
the hypothesis `InjNearMeanW2`, with `δ = δ₀ + W⁻²`, and by `InjFarTrace`),
`|E new_c w - E new_0 w - W⁻¹ inj_w(t)| ≤ c₀(C_n + C_f)e²` (the far part enters as `O(g/W²)`).
Arithmetic: `inj_proj_arith`, `inj_far_arith`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.Transmission.Bridge
open scoped ENNReal Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

theorem inj_proj_arith {t c₀ Cn δ g e : ℝ} {d : ℝ} {IP : ℂ} (hW : 1 ≤ W) (ht : |t| ≤ c₀)
    (hCn : 0 ≤ Cn) (hn : ‖(W : ℂ)⁻¹ * IP - (d : ℂ)‖ ≤ Cn * (δ + g / W)) (hδe : δ + g / W ≤ e)
    (hWe : (W : ℝ)⁻¹ ≤ e) :
    ‖((t / (W : ℝ) ^ 2 : ℝ) : ℂ) * IP - (W : ℂ)⁻¹ * ((d * t : ℝ) : ℂ)‖ ≤ c₀ * Cn * e ^ 2 := by
  have hW0 : (W : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ W := by exact_mod_cast hW
                               linarith
  have e1 : ((t / (W : ℝ) ^ 2 : ℝ) : ℂ) * IP - (W : ℂ)⁻¹ * ((d * t : ℝ) : ℂ) =
      ((t / W : ℝ) : ℂ) * ((W : ℂ)⁻¹ * IP - (d : ℂ)) := by
    have : (W : ℂ) ≠ 0 := by exact_mod_cast hW0
    push_cast; field_simp
  rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, Nat.abs_cast]
  have hδ0 : 0 ≤ Cn * (δ + g / W) := (norm_nonneg _).trans hn
  have h1 : |t| / W ≤ c₀ * e := by
    rw [div_eq_mul_inv]; exact mul_le_mul ht hWe (by positivity) ((abs_nonneg t).trans ht)
  have h2 : Cn * (δ + g / W) ≤ Cn * e := mul_le_mul_of_nonneg_left hδe hCn
  calc |t| / W * ‖(W : ℂ)⁻¹ * IP - (d : ℂ)‖ ≤ (c₀ * e) * (Cn * e) :=
        mul_le_mul h1 (hn.trans h2) (norm_nonneg _) (by
          have := (abs_nonneg t).trans ht; have := (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) W))
          nlinarith)
    _ = c₀ * Cn * e ^ 2 := by ring

theorem inj_far_arith {t c₀ Cf g e : ℝ} {IF : ℂ} (hW : 1 ≤ W) (ht : |t| ≤ c₀) (hCf : 0 ≤ Cf)
    (hg : 0 ≤ g) (hf : ‖IF‖ ≤ Cf * g) (hge : g / W ≤ e) (hWe : (W : ℝ)⁻¹ ≤ e) :
    ‖((t / (W : ℝ) ^ 2 : ℝ) : ℂ) * IF‖ ≤ c₀ * Cf * e ^ 2 := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (W : ℝ) ^ 2)]
  have hg0 : 0 ≤ Cf * g := (norm_nonneg _).trans hf
  have hc0 : 0 ≤ c₀ := (abs_nonneg t).trans ht
  have e1 : |t| / (W : ℝ) ^ 2 * (Cf * g) = (|t| * Cf) * ((g / W) * (W : ℝ)⁻¹) := by
    field_simp
  have hgW0 : 0 ≤ g / W := div_nonneg hg (by positivity)
  have he0 : 0 ≤ e := hgW0.trans hge
  calc |t| / (W : ℝ) ^ 2 * ‖IF‖ ≤ |t| / (W : ℝ) ^ 2 * (Cf * g) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
    _ = (|t| * Cf) * ((g / W) * (W : ℝ)⁻¹) := e1
    _ ≤ (c₀ * Cf) * (e * e) := by
        gcongr
    _ = c₀ * Cf * e ^ 2 := by ring

/-- **One-letter words**: the injected mean matches `W⁻¹ inj_w(t)` up to `O(e²)`. -/
theorem inj_single_mean {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hW : 1 ≤ W) (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (q : Fin nI → ℝ → ℝ) (j : ℕ) {c₀ Cn Cf δ g e : ℝ} (hc₀ : 0 ≤ c₀) (hq : ∀ a x, |q a x| ≤ c₀)
    (hCn : 0 ≤ Cn) (hCf : 0 ≤ Cf) (hg : 0 ≤ g) (hδe : δ + g / W ≤ e) (hge : g / W ≤ e)
    (hWe : (W : ℝ)⁻¹ ≤ e)
    (hG2 : Integrable (fun y => freshG b E XX y ^ 2) (freshLaw W b))
    (hn : ‖(W : ℂ)⁻¹ * ∫ y, ((freshD b E XX y)ᴴ * freshD b E XX y * nearProjection W).trace
      ∂freshLaw W b - (dStar b : ℂ)‖ ≤ Cn * (δ + g / W))
    (hf : ‖∫ y, ((freshD b E XX y)ᴴ * freshD b E XX y * (1 - nearProjection W)).trace
      ∂freshLaw W b‖ ≤ Cf * g)
    (ℓ : TraceLetter nT nI) {s : Separator} (hs : s = .id ∨ s = .proj)
    (hic : Integrable (fun y => layerNew b E A (injCoef q W j) XX [(ℓ, s)] y) (freshLaw W b))
    (hi0 : Integrable (fun y => layerNew b E A (fun _ => 0) XX [(ℓ, s)] y) (freshLaw W b)) :
    ‖∫ y, layerNew b E A (injCoef q W j) XX [(ℓ, s)] y ∂freshLaw W b -
        ∫ y, layerNew b E A (fun _ => 0) XX [(ℓ, s)] y ∂freshLaw W b -
        (W : ℂ)⁻¹ * wordInjection b q (stepTime W j) [(ℓ, s)]‖ ≤ c₀ * (Cn + Cf) * e ^ 2 := by
  have he0 : 0 ≤ e := (inv_nonneg.mpr (Nat.cast_nonneg _)).trans hWe
  have hpt : ∀ y, layerNew b E A (injCoef q W j) XX [(ℓ, s)] y -
      layerNew b E A (fun _ => 0) XX [(ℓ, s)] y = (injCoef q W j ℓ : ℂ) *
        ((freshD b E XX y)ᴴ * freshD b E XX y * sepOf b E (freshTwoPortSchur E XX y) s).trace :=
    fun y => newWord_single_sub _ _ _ _ _ ℓ s
  rw [← integral_sub hic hi0]
  simp only [hpt]
  rw [integral_const_mul]
  have hR : 0 ≤ c₀ * (Cn + Cf) * e ^ 2 := by positivity
  cases ℓ with
  | current => simpa [injCoef, wordInjection] using hR
  | tag a => simpa [injCoef, wordInjection] using hR
  | interval a =>
    have hw : wordInjection b q (stepTime W j) [((TraceLetter.interval a : TraceLetter nT nI), s)] =
        ((dStar b * q a (stepTime W j) : ℝ) : ℂ) := by simp [wordInjection, hs]
    rw [hw]
    simp only [injCoef]
    rcases hs with rfl | rfl
    · have e1 : ∀ y, ((freshD b E XX y)ᴴ * freshD b E XX y * sepOf b E (freshTwoPortSchur E XX y)
          .id).trace = ((freshD b E XX y)ᴴ * freshD b E XX y * nearProjection W).trace +
            ((freshD b E XX y)ᴴ * freshD b E XX y * (1 - nearProjection W)).trace := fun y => by
        rw [← Matrix.trace_add, ← Matrix.mul_add, add_sub_cancel]; rfl
      simp only [e1]
      rw [integral_add (integrable_trace_DD hG2 _) (integrable_trace_DD hG2 _), mul_add,
        add_sub_right_comm]
      refine (norm_add_le _ _).trans ?_
      have h1 := inj_proj_arith hW (hq a (stepTime W j)) hCn hn hδe hWe
      have h2 := inj_far_arith hW (hq a (stepTime W j)) hCf hg hf hge hWe
      have : c₀ * Cn * e ^ 2 + c₀ * Cf * e ^ 2 = c₀ * (Cn + Cf) * e ^ 2 := by ring
      linarith
    · have h1 := inj_proj_arith hW (hq a (stepTime W j)) hCn hn hδe hWe
      refine h1.trans ?_
      have : c₀ * Cn * e ^ 2 ≤ c₀ * Cn * e ^ 2 + c₀ * Cf * e ^ 2 :=
        le_add_of_nonneg_right (by positivity)
      linarith

end BlockBand.SourceProcess.ContractingWords
