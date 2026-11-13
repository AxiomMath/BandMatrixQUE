module

public import BlockBand.Transmission.Generator.DriftCond
public import BlockBand.Transmission.Generator.StepExact
public import BlockBand.Transmission.PathScalar.MeanStepLimit

/-!
# The one-step conditional mean of `Tr T^k` along the path

* `condExp_pathPower_succ`: `E[Tr T_{r+1}^k ∣ 𝓕_r] = ∫ Re Tr T(freshSchur X_r y)^k dfresh(y)` a.s.
  (`condExp_fresh` with the clamped `Ψ = clamp_{[0,W]} Re Tr T(freshSchur x y)^k`; the clamp is
  inactive on passive inputs and Hermitian samples, `trace_pow_le_card`).
* `driftError_pow_ae`: a.s. `driftError_r = [∫Ψ(X_r,·) - P_k(X_r) - A_k^{E'}(P(X_r))/W] +
  (A_k^{E'} - A_k^{E})(P(X_r))/W`, `A^{E}` at `D₀(E)`.
* `transmissionDrift_sub_le`: `|A_k^D(P) - A_k^{D'}(P)| ≤ |D - D'|k²g²` for `0 ≤ P_m ≤ g = P₁`.
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

/-- Clamp to `[0, W]`. -/
def clampW (W : ℕ) (x : ℝ) : ℝ := max 0 (min x W)

theorem clampW_abs_le (x : ℝ) : |clampW W x| ≤ W := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  rw [clampW, abs_of_nonneg (le_max_left _ _)]
  exact max_le hW (min_le_right _ _)

theorem clampW_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ W) : clampW W x = x := by
  rw [clampW, min_eq_left h1, max_eq_right h0]

theorem continuous_clampW : Continuous (clampW W) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- `0 ≤ Re Tr T(X)^k ≤ W` for passive `X`, `k ≥ 1`. -/
theorem trace_pow_le_card {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ ((passiveTransmission b E X) ^ k).trace.re ∧
      ((passiveTransmission b E X) ^ k).trace.re ≤ W := by
  have hT := passiveTransmission_posSemidef hb h1 h2 hX
  have hT1 := one_sub_passiveTransmission_posSemidef b E X
  obtain ⟨ha, hb'⟩ := trace_pow_mem hT hT1 k hk
  have h2' := hT1.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin] at h2'
  have := (Complex.nonneg_iff.mp h2').1
  simp only [Complex.sub_re, Complex.natCast_re] at this
  exact ⟨ha, by linarith⟩

/-- The clamped one-step functional. -/
def freshPow (b E : ℝ) (k : ℕ) (x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort) :
    ℝ :=
  clampW W ((passiveTransmission b E (freshSchur E x.1 x.2)) ^ k).trace.re

theorem measurable_freshPow (b E : ℝ) (k : ℕ) : Measurable (freshPow (W := W) b E k) :=
  continuous_clampW.measurable.comp
    ((measurable_trace_pow_transmission b E k).comp (measurable_freshSchur_prod E))

/-- On a passive input the clamp is inactive after integration. -/
theorem integral_freshPow {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W)
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    {k : ℕ} (hk : 1 ≤ k) :
    ∫ y, freshPow b E k (X, y) ∂freshLaw W b =
      ∫ y, ((passiveTransmission b E (freshSchur E X y)) ^ k).trace.re ∂freshLaw W b := by
  refine integral_congr_ae ?_
  filter_upwards [PassiveLayer.ae_good W hb0 hW] with y hy
  obtain ⟨h0, h1'⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2
    (PathScalar.passiveY_freshSchur E hX y hy.1) hk
  exact clampW_of_mem h0 h1'

/-- **`E[Tr T_{r+1}^k ∣ 𝓕_r]`**, `r ≥ 1`, `k ≥ 1`. -/
theorem condExp_pathPower_succ {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) (hW : 1 ≤ W) {k : ℕ} (hk : 1 ≤ k) {r : ℕ} (hr : 1 ≤ r) :
    (growthPathLaw W b)[pathPower b E W k (r + 1) | growthSigma W r] =ᵐ[growthPathLaw W b]
      fun ω => ∫ y, ((passiveTransmission b E (freshSchur E (pathX b E W r ω) y)) ^ k).trace.re
        ∂freshLaw W b := by
  have hae : pathPower b E W k (r + 1) =ᵐ[growthPathLaw W b]
      fun ω => freshPow b E k (pathX b E W r ω, freshSample W r ω) := by
    filter_upwards [ae_pathX_succ hb h1 h2 hW, pathPower_mem (W := W) (by linarith) h1 h2]
      with ω hω hm
    obtain ⟨h0, h1', h3⟩ := hm k (r + 1) hk
    have e : pathPower b E W k (r + 1) ω =
        ((passiveTransmission b E (freshSchur E (pathX b E W r ω) (freshSample W r ω))) ^
          k).trace.re := by
      show ((passiveTransmission b E (pathX b E W (r + 1) ω)) ^ k).trace.re = _
      rw [hω r hr]
    rw [freshPow, ← e, clampW_of_mem h0 (h1'.trans h3)]
  refine (condExp_congr_ae hae).trans ?_
  refine (condExp_fresh b E (measurable_freshPow b E k) (M := W) (fun x => clampW_abs_le _)
    r).trans ?_
  filter_upwards [mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r] with ω hω
  exact integral_freshPow hb0 hb hW h1 h2 hω hk

theorem integrable_pathPower {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) {k : ℕ}
    (hk : 1 ≤ k) (r : ℕ) : Integrable (pathPower b E W k r) (growthPathLaw W b) := by
  refine Integrable.of_bound (measurable_pathPower b E k r).aestronglyMeasurable (W : ℝ) ?_
  filter_upwards [pathPower_mem (W := W) hb h1 h2] with ω hm
  obtain ⟨h0, h1', h3⟩ := hm k r hk
  rw [Real.norm_eq_abs, abs_of_nonneg h0]; linarith

/-- **The drift error at power `k`**, a.s. -/
theorem driftError_pow_ae {b E E' : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E')
    (h2 : E' < 2) (hW : 1 ≤ W) {k : ℕ} (hk : 1 ≤ k) {r : ℕ} (hr : 1 ≤ r) :
    driftError b E E' W k r =ᵐ[growthPathLaw W b] fun ω =>
      (∫ y, ((passiveTransmission b E' (freshSchur E' (pathX b E' W r ω) y)) ^ k).trace.re
          ∂freshLaw W b - ((passiveTransmission b E' (pathX b E' W r ω)) ^ k).trace.re -
        transmissionDrift (transportD0 b E') k
          (fun m => ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re) / W) +
      (transmissionDrift (transportD0 b E') k
          (fun m => ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re) -
        transmissionDrift (transportD0 b E) k
          (fun m => ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re)) / W := by
  set μ := growthPathLaw W b
  have hI1 := integrable_pathPower (W := W) (b := b) (by linarith) h1 h2 hk (r + 1)
  have hI0 := integrable_pathPower (W := W) (b := b) (by linarith) h1 h2 hk r
  have hc0 : μ[pathPower b E' W k r | growthSigma W r] = pathPower b E' W k r :=
    condExp_of_stronglyMeasurable (growthSigma_le W r)
      (measurable_pathPower_adapted b E' k r).stronglyMeasurable hI0
  have hce : μ[powerIncrement b E' W k r | growthSigma W r] =ᵐ[μ]
      μ[pathPower b E' W k (r + 1) | growthSigma W r] - pathPower b E' W k r := by
    have := condExp_sub hI1 hI0 (growthSigma W r) (μ := μ)
    rw [hc0] at this
    exact this
  filter_upwards [hce, condExp_pathPower_succ hb0 hb h1 h2 hW hk hr] with ω e1 e2
  show μ[powerIncrement b E' W k r | growthSigma W r] ω -
    transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W = _
  rw [e1, Pi.sub_apply, e2]
  show _ - ((passiveTransmission b E' (pathX b E' W r ω)) ^ k).trace.re -
    transmissionDrift (transportD0 b E) k
      (fun m => ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re) / W = _
  ring

/-- `A_k` is linear in `D`. -/
theorem transmissionDrift_eq_mul (D : ℝ) (k : ℕ) (P : ℕ → ℝ) :
    transmissionDrift D k P = D * transmissionDrift 1 k P := by
  simp only [transmissionDrift]; ring

/-- `|A_k^1(P)| ≤ k²g²` for `0 ≤ P_m ≤ g = P₁` (`m ≥ 1`). -/
theorem abs_transmissionDrift_one_le {k : ℕ} (hk : 1 ≤ k) {P : ℕ → ℝ}
    (hP : ∀ m, 1 ≤ m → 0 ≤ P m ∧ P m ≤ P 1) :
    |transmissionDrift 1 k P| ≤ (k : ℝ) ^ 2 * P 1 ^ 2 := by
  set g := P 1
  have hg : 0 ≤ g := (hP 1 le_rfl).1
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hprod : ∀ m n, 1 ≤ m → 1 ≤ n → 0 ≤ P m * P n ∧ P m * P n ≤ g ^ 2 := fun m n hm hn => by
    obtain ⟨a0, a1⟩ := hP m hm
    obtain ⟨b0, b1⟩ := hP n hn
    exact ⟨mul_nonneg a0 b0, by rw [sq]; exact mul_le_mul a1 b1 b0 hg⟩
  have hsum : |∑ j ∈ Finset.Ico 1 k, (P j * P (k - j) - P (j + 1) * P (k - j))| ≤ k * g ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j ∈ Finset.Ico 1 k, |P j * P (k - j) - P (j + 1) * P (k - j)| ≤ g ^ 2 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      obtain ⟨x0, x1⟩ := hprod j (k - j) hj.1 (by omega)
      obtain ⟨y0, y1⟩ := hprod (j + 1) (k - j) (by omega) (by omega)
      rw [abs_le]; constructor <;> linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  obtain ⟨p0, p1⟩ := hprod 1 k le_rfl hk
  simp only [transmissionDrift]
  have e : -(1 * (k : ℝ) / 2) * P 1 * P k = -((k : ℝ) / 2) * (P 1 * P k) := by ring
  have e2 : 1 * (k : ℝ) / 2 * ∑ j ∈ Finset.Ico 1 k, (P j * P (k - j) - P (j + 1) * P (k - j)) =
      (k : ℝ) / 2 * ∑ j ∈ Finset.Ico 1 k, (P j * P (k - j) - P (j + 1) * P (k - j)) := by ring
  rw [e, e2]
  refine (abs_add_le _ _).trans ?_
  have hk2 : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
  have a1 : |-((k : ℝ) / 2) * (P 1 * P k)| = (k : ℝ) / 2 * (P 1 * P k) := by
    rw [abs_mul, abs_neg, abs_of_nonneg hk2, abs_of_nonneg p0]
  have a2 : |(k : ℝ) / 2 * ∑ j ∈ Finset.Ico 1 k, (P j * P (k - j) - P (j + 1) * P (k - j))| =
      (k : ℝ) / 2 * |∑ j ∈ Finset.Ico 1 k, (P j * P (k - j) - P (j + 1) * P (k - j))| := by
    rw [abs_mul, abs_of_nonneg hk2]
  rw [a1, a2]
  have h3 : (k : ℝ) / 2 * |∑ j ∈ Finset.Ico 1 k, (P j * P (k - j) - P (j + 1) * P (k - j))| ≤
      (k : ℝ) / 2 * (k * g ^ 2) := mul_le_mul_of_nonneg_left hsum (by positivity)
  have h4 : (k : ℝ) / 2 * (P 1 * P k) ≤ (k : ℝ) / 2 * g ^ 2 :=
    mul_le_mul_of_nonneg_left p1 (by positivity)
  have h5 : (k : ℝ) / 2 * g ^ 2 + (k : ℝ) / 2 * (k * g ^ 2) ≤ (k : ℝ) ^ 2 * g ^ 2 := by
    have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  linarith

/-- **`|A_k^D(P) - A_k^{D'}(P)| ≤ |D - D'|k²g²`.** -/
theorem transmissionDrift_sub_le {k : ℕ} (hk : 1 ≤ k) {P : ℕ → ℝ}
    (hP : ∀ m, 1 ≤ m → 0 ≤ P m ∧ P m ≤ P 1) (D D' : ℝ) :
    |transmissionDrift D k P - transmissionDrift D' k P| ≤
      |D - D'| * ((k : ℝ) ^ 2 * P 1 ^ 2) := by
  rw [transmissionDrift_eq_mul D, transmissionDrift_eq_mul D', ← sub_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_transmissionDrift_one_le hk hP) (abs_nonneg _)

end BlockBand.Transmission.Generator
