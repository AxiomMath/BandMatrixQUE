module

public import BlockBand.Transmission.Generator.PowCond

/-!
# The one-step conditional bracket along the path

* `freshBr`: the clamped `Ψ(x, y) = (cl Tr T(x₊)^k - cl Tr T(x)^k)(cl Tr T(x₊)^l - cl Tr T(x)^l)`;
* **`condExp_powerIncrement_mul`**: `E[Δ^k_rΔ^l_r ∣ 𝓕_r] =
  ∫(Tr T(X_r₊)^k - Tr T(X_r)^k)(Tr T(X_r₊)^l - Tr T(X_r)^l)dfresh` a.s.;
* **`bracketError_ae`**: a.s. `bracketError_r = [that - B^{E'}(P(X_r))/W] + (B^{E'} - B^{E})(P(X_r))/W`;
* `transmissionBracket_sub_le`: `|B^D_{kl}(P) - B^{D'}_{kl}(P)| ≤ |D - D'|klg` (`0 ≤ P_m ≤ g`);
* `measurable_bracket_pathPowers`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- The clamped one-step bracket functional. -/
def freshBr (b E : ℝ) (k l : ℕ)
    (x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort) : ℝ :=
  (freshPow b E k x - clampW W ((passiveTransmission b E x.1) ^ k).trace.re) *
    (freshPow b E l x - clampW W ((passiveTransmission b E x.1) ^ l).trace.re)

theorem measurable_freshBr (b E : ℝ) (k l : ℕ) : Measurable (freshBr (W := W) b E k l) := by
  have h0 : ∀ m : ℕ, Measurable fun x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      clampW W ((passiveTransmission b E x.1) ^ m).trace.re := fun m =>
    continuous_clampW.measurable.comp ((measurable_trace_pow_transmission b E m).comp measurable_fst)
  exact ((measurable_freshPow b E k).sub (h0 k)).mul ((measurable_freshPow b E l).sub (h0 l))

theorem abs_clampW_sub_le (x y : ℝ) : |clampW W x - clampW W y| ≤ W := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hx : 0 ≤ clampW W x ∧ clampW W x ≤ W := ⟨le_max_left _ _, max_le hW (min_le_right _ _)⟩
  have hy : 0 ≤ clampW W y ∧ clampW W y ≤ W := ⟨le_max_left _ _, max_le hW (min_le_right _ _)⟩
  rw [abs_le]; constructor <;> linarith

theorem abs_freshBr_le (b E : ℝ) (k l : ℕ)
    (x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort) :
    |freshBr b E k l x| ≤ (W : ℝ) * W := by
  rw [freshBr, abs_mul]
  exact mul_le_mul (abs_clampW_sub_le _ _) (abs_clampW_sub_le _ _) (abs_nonneg _) (Nat.cast_nonneg _)

/-- On a passive input the clamps are inactive after integration. -/
theorem integral_freshBr {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W)
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ∫ y, freshBr b E k l (X, y) ∂freshLaw W b =
      ∫ y, (((passiveTransmission b E (freshSchur E X y)) ^ k).trace.re -
          ((passiveTransmission b E X) ^ k).trace.re) *
        (((passiveTransmission b E (freshSchur E X y)) ^ l).trace.re -
          ((passiveTransmission b E X) ^ l).trace.re) ∂freshLaw W b := by
  refine integral_congr_ae ?_
  filter_upwards [PassiveLayer.ae_good W hb0 hW] with y hy
  have hY := PathScalar.passiveY_freshSchur E hX y hy.1
  obtain ⟨a0, a1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hY hk
  obtain ⟨b0, b1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hY hl
  obtain ⟨c0, c1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hX hk
  obtain ⟨d0, d1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hX hl
  simp only [freshBr, freshPow]
  rw [clampW_of_mem a0 a1, clampW_of_mem b0 b1, clampW_of_mem c0 c1, clampW_of_mem d0 d1]

/-- **`E[Δ^k_rΔ^l_r ∣ 𝓕_r]`**, `r, k, l ≥ 1`. -/
theorem condExp_powerIncrement_mul {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) (hW : 1 ≤ W) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) {r : ℕ} (hr : 1 ≤ r) :
    (growthPathLaw W b)[fun ω => powerIncrement b E W k r ω * powerIncrement b E W l r ω |
        growthSigma W r] =ᵐ[growthPathLaw W b]
      fun ω => ∫ y, (((passiveTransmission b E (freshSchur E (pathX b E W r ω) y)) ^ k).trace.re -
          ((passiveTransmission b E (pathX b E W r ω)) ^ k).trace.re) *
        (((passiveTransmission b E (freshSchur E (pathX b E W r ω) y)) ^ l).trace.re -
          ((passiveTransmission b E (pathX b E W r ω)) ^ l).trace.re) ∂freshLaw W b := by
  have hae : (fun ω => powerIncrement b E W k r ω * powerIncrement b E W l r ω)
      =ᵐ[growthPathLaw W b] fun ω => freshBr b E k l (pathX b E W r ω, freshSample W r ω) := by
    filter_upwards [ae_pathX_succ hb h1 h2 hW, pathPower_mem (W := W) (by linarith) h1 h2]
      with ω hω hm
    have e : ∀ m : ℕ, 1 ≤ m → powerIncrement b E W m r ω =
        freshPow b E m (pathX b E W r ω, freshSample W r ω) -
          clampW W ((passiveTransmission b E (pathX b E W r ω)) ^ m).trace.re := by
      intro m hm1
      obtain ⟨a0, a1, a3⟩ := hm m (r + 1) hm1
      obtain ⟨b0, b1, b3⟩ := hm m r hm1
      have e1 : pathPower b E W m (r + 1) ω =
          ((passiveTransmission b E (freshSchur E (pathX b E W r ω) (freshSample W r ω))) ^
            m).trace.re := by
        show ((passiveTransmission b E (pathX b E W (r + 1) ω)) ^ m).trace.re = _
        rw [hω r hr]
      have e0 : pathPower b E W m r ω =
          ((passiveTransmission b E (pathX b E W r ω)) ^ m).trace.re := rfl
      rw [powerIncrement, freshPow, ← e1, ← e0, clampW_of_mem a0 (a1.trans a3),
        clampW_of_mem b0 (b1.trans b3)]
    rw [freshBr, e k hk, e l hl]
  refine (condExp_congr_ae hae).trans ?_
  refine (condExp_fresh b E (measurable_freshBr b E k l) (M := (W : ℝ) * W)
    (fun x => abs_freshBr_le b E k l x) r).trans ?_
  filter_upwards [mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r] with ω hω
  exact integral_freshBr hb0 hb hW h1 h2 hω hk hl

/-- **The bracket error**, a.s. -/
theorem bracketError_ae {b E E' : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E')
    (h2 : E' < 2) (hW : 1 ≤ W) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) {r : ℕ} (hr : 1 ≤ r) :
    bracketError b E E' W k l r =ᵐ[growthPathLaw W b] fun ω =>
      (∫ y, (((passiveTransmission b E' (freshSchur E' (pathX b E' W r ω) y)) ^ k).trace.re -
          ((passiveTransmission b E' (pathX b E' W r ω)) ^ k).trace.re) *
        (((passiveTransmission b E' (freshSchur E' (pathX b E' W r ω) y)) ^ l).trace.re -
          ((passiveTransmission b E' (pathX b E' W r ω)) ^ l).trace.re) ∂freshLaw W b -
        transmissionBracket (transportD0 b E') k l
          (fun m => ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re) / W) +
      (transmissionBracket (transportD0 b E') k l
          (fun m => ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re) -
        transmissionBracket (transportD0 b E) k l
          (fun m => ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re)) / W := by
  filter_upwards [condExp_powerIncrement_mul hb0 hb h1 h2 hW hk hl hr] with ω e
  show (growthPathLaw W b)[fun ω => powerIncrement b E' W k r ω * powerIncrement b E' W l r ω |
      growthSigma W r] ω - transmissionBracket (transportD0 b E) k l (pathPowers b E' W r ω) / W = _
  rw [e]
  show _ - transmissionBracket (transportD0 b E) k l
      (fun m => ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re) / W = _
  ring

/-- **`|B^D_{kl}(P) - B^{D'}_{kl}(P)| ≤ |D - D'|klg`** for `0 ≤ P_m ≤ g` (`m ≥ 1`). -/
theorem transmissionBracket_sub_le {k l : ℕ} (hk : 1 ≤ k) {P : ℕ → ℝ} {g : ℝ}
    (hP : ∀ m, 1 ≤ m → 0 ≤ P m ∧ P m ≤ g) (D D' : ℝ) :
    |transmissionBracket D k l P - transmissionBracket D' k l P| ≤
      |D - D'| * ((k : ℝ) * l * g) := by
  have e : transmissionBracket D k l P - transmissionBracket D' k l P =
      (D - D') * ((k : ℝ) * l * (P (k + l) - P (k + l + 1))) := by
    simp only [transmissionBracket]; ring
  rw [e, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  obtain ⟨a0, a1⟩ := hP (k + l) (by omega)
  obtain ⟨b0, b1⟩ := hP (k + l + 1) (by omega)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * l)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [abs_le]; constructor <;> linarith

theorem measurable_bracket_pathPowers (b E E' : ℝ) (k l r : ℕ) :
    Measurable[growthSigma W r] fun ω =>
      transmissionBracket (transportD0 b E) k l (pathPowers b E' W r ω) / W := by
  simp only [transmissionBracket, pathPowers]
  exact (((measurable_pathPower_adapted b E' (k + l) r).sub
    (measurable_pathPower_adapted b E' (k + l + 1) r)).const_mul _).div_const _

end BlockBand.Transmission.Generator
