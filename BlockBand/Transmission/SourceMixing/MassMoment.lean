module

public import BlockBand.Transmission.SourceMixing.MassPath
public import BlockBand.Transmission.SourceMixing.MassStatement
public import BlockBand.Transmission.LengthUniform.DeltaZero

/-!
# The `T`-free mass moment bound

Law `growthPathLaw W b` (the unabsorbed near-end-grown path), `q_r = passiveMass b E (pathX b E W r)`,
fixed `0 < b < 1/2`, `-2 < E < 2`. Hypotheses `MatchedTracesContract`, `GaussianAbsorptionContract`
and `GaussianLpGradient`, used through `passiveBounds_holds` and
`deltaZeroLengthUniform_holds`.

Proves `MassMomentBound b E`: `‖q_r‖_p ≤ K(1 + W/r)` along the growth path for `1 ≤ r ≤ TW`,
with `K` independent of `T`.

Proof outline, for the integer `n = ⌈p⌉`, `x_r = E qc(X_r)ⁿ` (`qc = max q 0 = q` a.s.):
* `mm_path_step`: `massLayer_step` integrated over the path (Fubini `mp_integral_path_le`) gives,
  for `r ≥ 1` and every `l ≥ 0`, `x_{r+1} ≤ x_r(1 - cl/W) + (clⁿ⁺¹ + D₁ + D₂C_δⁿ⁺¹)/W`, where
  `E δ₀(X_r)ⁿ⁺¹ ≤ (C_δ/W)ⁿ⁺¹` (`DeltaZeroLengthUniform`, `C_δ` before `T`);
* `x_1 ≤ (W/(4η))ⁿ`; `logistic_bound` gives `x_r ≤ K'(1 + W/r)ⁿ` for `1 ≤ r ≤ TW`, with `K'`
  depending on `n, c, D, η` only, so `K = K'^{1/n}` is chosen before `T`;
* `massMomentBound_holds`: `‖q_r‖_p ≤ ‖qc(X_r)‖_n ≤ K(1 + W/r)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- Passivity of `X_r` almost surely. -/
theorem mm_ae_passive {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (r : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, (passiveY (pathX b E W r ω)).PosSemidef :=
  (ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb h1 h2).mono fun _ h =>
    pathNearSchur_passive h r

theorem mm_integrable_qc {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (n r : ℕ) :
    Integrable (fun ω => qc b E (pathX b E W r ω) ^ n) (growthPathLaw W b) :=
  Integrable.of_bound
    (((measurable_qc b E).comp (PathJet.measurable_pathX b E r)).pow_const n).aestronglyMeasurable
    ((W / (4 * etaZ b E)) ^ n) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (qc_nonneg b E _) n)]
      exact pow_le_pow_left₀ (qc_nonneg b E _) (qc_le hb h1 h2 _) n)

theorem mm_integrable_delta {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (k r : ℕ) :
    Integrable (fun ω => jetDistance0 b E (pathX b E W r ω) ^ k) (growthPathLaw W b) := by
  refine Integrable.of_bound
    (((measurable_jetDistance0 b E).comp (PathJet.measurable_pathX b E r)).pow_const
      k).aestronglyMeasurable (((etaZ b E)⁻¹ + 1) ^ k) ?_
  filter_upwards [mm_ae_passive (W := W) (by linarith) h1 h2 r] with ω hω
  have h0 : 0 ≤ jetDistance0 b E (pathX b E W r ω) := norm_nonneg _
  rw [Real.norm_of_nonneg (pow_nonneg h0 k)]
  exact pow_le_pow_left₀ h0 (jetDistance0_le_bound hb0 hb h1 h2 hω) k

/-- One path step of the mass-moment recursion. -/
theorem mm_path_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {n : ℕ} {c D₁ D₂ l Cδ : ℝ} (hD₂ : 0 ≤ D₂) (hW : 1 ≤ W)
    (hstep : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∫ ω, qc b E (freshSchur E X ω) ^ n ∂freshLaw W b ≤
        qc b E X ^ n * (1 - c * l / W) +
          (c * l ^ (n + 1) + D₁ + D₂ * (W * jetDistance0 b E X) ^ (n + 1)) / W)
    {j : ℕ} (hj : 1 ≤ j)
    (hδ : ∫ ω, jetDistance0 b E (pathX b E W j ω) ^ (n + 1) ∂growthPathLaw W b ≤
      (Cδ / W) ^ (n + 1)) :
    ∫ ω, qc b E (pathX b E W (j + 1) ω) ^ n ∂growthPathLaw W b ≤
      (∫ ω, qc b E (pathX b E W j ω) ^ n ∂growthPathLaw W b) * (1 - c * l / W) +
        (c * l ^ (n + 1) + (D₁ + D₂ * Cδ ^ (n + 1))) / W := by
  set P := growthPathLaw W b
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hb1 : b < 1 := by linarith
  set a := 1 - c * l / W
  set β := (c * l ^ (n + 1) + D₁) / W
  set γ := D₂ * (W : ℝ) ^ (n + 1) / W
  have hγ : 0 ≤ γ := by positivity
  set g : Matrix (Fin W) (Fin W) ℂ → ℝ := fun X =>
    a * qc b E X ^ n + (β + γ * jetDistance0 b E X ^ (n + 1))
  have hg : Measurable g := (((measurable_qc b E).pow_const n).const_mul a).add
    (measurable_const.add (((measurable_jetDistance0 b E).pow_const (n + 1)).const_mul γ))
  have hqi := mm_integrable_qc (W := W) hb1 h1 h2 n j
  have hδi := mm_integrable_delta (W := W) hb0 hb h1 h2 (n + 1) j
  have hgi : Integrable (fun ω => g (pathX b E W j ω)) P :=
    (hqi.const_mul a).add ((integrable_const β).add (hδi.const_mul γ))
  set Ψ : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort → ℝ :=
    fun q => qc b E (freshSchur E q.1 q.2) ^ n
  have hΨ : Measurable Ψ := ((measurable_qc b E).comp (measurable_freshSchur_prod E)).pow_const n
  have hΨM : ∀ x, ‖Ψ x‖ ≤ (W / (4 * etaZ b E)) ^ n := fun x => by
    rw [Real.norm_of_nonneg (pow_nonneg (qc_nonneg b E _) n)]
    exact pow_le_pow_left₀ (qc_nonneg b E _) (qc_le hb1 h1 h2 _) n
  have hbd : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∫ ω, Ψ (X, ω) ∂freshLaw W b ≤ g X := fun X hX => by
    refine (hstep X hX).trans_eq ?_
    simp only [g, a, β, γ, mul_pow]
    field_simp
  have hsucc : ∫ ω, qc b E (pathX b E W (j + 1) ω) ^ n ∂P =
      ∫ ω, Ψ (pathX b E W j ω, freshSample W j ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [ae_pathX_succ (W := W) (b := b) hb h1 h2 hW] with ω hω
    simp only [Ψ, hω j hj]
  have hmain := mp_integral_path_le hb1 h1 h2 hΨ hΨM hg j hgi hbd
  have hint : ∫ ω, g (pathX b E W j ω) ∂P = a * ∫ ω, qc b E (pathX b E W j ω) ^ n ∂P +
      (β + γ * ∫ ω, jetDistance0 b E (pathX b E W j ω) ^ (n + 1) ∂P) := by
    have i1 : Integrable (fun ω => a * qc b E (pathX b E W j ω) ^ n) P := hqi.const_mul a
    have i3 : Integrable (fun ω => γ * jetDistance0 b E (pathX b E W j ω) ^ (n + 1)) P :=
      hδi.const_mul γ
    have i2 : Integrable (fun ω => β + γ * jetDistance0 b E (pathX b E W j ω) ^ (n + 1)) P :=
      (integrable_const β).add i3
    simp only [g]
    rw [integral_add i1 i2, integral_const_mul, integral_add (integrable_const β) i3,
      integral_const_mul, integral_const, probReal_univ, one_smul]
  have hγδ : γ * ∫ ω, jetDistance0 b E (pathX b E W j ω) ^ (n + 1) ∂P ≤
      D₂ * Cδ ^ (n + 1) / W := by
    calc γ * ∫ ω, jetDistance0 b E (pathX b E W j ω) ^ (n + 1) ∂P ≤ γ * (Cδ / W) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left hδ hγ
      _ = D₂ * Cδ ^ (n + 1) / W := by
          simp only [γ, div_pow]; field_simp
  rw [hsucc]
  refine hmain.trans ?_
  rw [hint]
  have e : (c * l ^ (n + 1) + (D₁ + D₂ * Cδ ^ (n + 1))) / W = β + D₂ * Cδ ^ (n + 1) / W := by
    simp only [β]; ring
  rw [e]
  linarith

/-- The `T`-free mass moment bound `MassMomentBound b E`. -/
theorem massMomentBound_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) : MassMomentBound b E := by
  intro p hp
  set n := ⌈p⌉₊
  have hpn : p ≤ n := Nat.le_ceil p
  have hn : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := hp.trans hpn
    exact_mod_cast this
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  obtain ⟨c, D₁, D₂, W₁, hc, hD₁, hD₂, hstep⟩ := massLayer_step hA hb0 hb h1 h2 n hn
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hE := PassiveLayer.mem_bulkInterval_min E
  obtain ⟨Cδ, hCδ, hδT⟩ := LengthUniform.deltaZeroLengthUniform_holds hMT hGA hLp b hb0 hb _
    (((n + 1 : ℕ) : ℝ)) hκ (by norm_cast; omega)
  have hη := etaZ_pos b E (by linarith) h1 h2
  set D := D₁ + D₂ * Cδ ^ (n + 1)
  have hD : 0 ≤ D := by positivity
  obtain ⟨K', hK', hlog⟩ := logistic_bound n hn hc hD
    (by positivity : 0 ≤ ((4 * etaZ b E)⁻¹) ^ n)
  refine ⟨K' ^ (n : ℝ)⁻¹, by positivity, fun T => ?_⟩
  obtain ⟨Wδ, hδW⟩ := hδT T
  refine ⟨max (max W₁ Wδ) 1, fun W hW r hr1 hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWδ⟩, hW1⟩ := hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  set P := growthPathLaw W b
  set x : ℕ → ℝ := fun r => ∫ ω, qc b E (pathX b E W r ω) ^ n ∂P
  have hx0 : ∀ r, 0 ≤ x r := fun r => integral_nonneg fun ω => pow_nonneg (qc_nonneg b E _) n
  have hx1 : x 1 ≤ ((4 * etaZ b E)⁻¹) ^ n * (1 + W) ^ n := by
    have hbd : ∀ ω, qc b E (pathX b E W 1 ω) ^ n ≤ ((4 * etaZ b E)⁻¹ * (1 + W)) ^ n := fun ω => by
      refine pow_le_pow_left₀ (qc_nonneg b E _) ((qc_le (by linarith) h1 h2 _).trans ?_) n
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc x 1 ≤ ∫ _ω, ((4 * etaZ b E)⁻¹ * (1 + W)) ^ n ∂P :=
          integral_mono (mm_integrable_qc (by linarith) h1 h2 n 1) (integrable_const _) hbd
      _ = ((4 * etaZ b E)⁻¹) ^ n * (1 + W) ^ n := by
          rw [integral_const, probReal_univ, one_smul, mul_pow]
  have hrec : ∀ j, 1 ≤ j → j < ⌊T * W⌋₊ → ∀ l : ℝ, 0 ≤ l →
      x (j + 1) ≤ x j * (1 - c * l / W) + (c * l ^ (n + 1) + D) / W := by
    intro j hj hjN l hl
    have hTW : (1 : ℝ) ≤ T * W := Nat.floor_pos.mp (by omega)
    have hjT : (j : ℝ) ≤ T * W :=
      (Nat.cast_le.mpr hjN.le).trans (Nat.floor_le (by linarith))
    have hδj := hδW W hWδ E hE j hj hjT
    have hδint := mp_integral_pow_le (ae_of_all _ fun ω => (norm_nonneg _ :
      0 ≤ jetDistance0 b E (pathX b E W j ω))) (n + 1) (by omega) (by positivity) hδj
    exact mm_path_step hb0 hb h1 h2 hD₂ hW1 (fun X hX => hstep W hW₁ X hX l hl) hj hδint
  have hxr := hlog (W : ℝ) hW1' x ⌊T * W⌋₊ hx0 hx1 hrec r hr1 (Nat.le_floor hrT)
  -- back to `L^p`
  have hpn' : ENNReal.ofReal p ≤ (n : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hpn
  have hcongr : eLpNorm (fun ω => passiveMass b E (pathX b E W r ω)) (n : ℝ≥0∞) P =
      eLpNorm (fun ω => qc b E (pathX b E W r ω)) (n : ℝ≥0∞) P := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [mm_ae_passive (W := W) (by linarith) h1 h2 r] with ω hω
    exact (qc_eq hω).symm
  have hv : 0 ≤ 1 + (W : ℝ) / r := by positivity
  refine (eLpNorm_le_eLpNorm_of_exponent_le hpn').trans ?_
  rw [hcongr]
  refine (mp_eLpNorm_le ((measurable_qc b E).comp
    (PathJet.measurable_pathX b E r)).aestronglyMeasurable (fun ω => qc_nonneg b E _)
    (fun ω => qc_le (by linarith) h1 h2 _) n hn hxr).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Real.mul_rpow hK' (by positivity), Real.pow_rpow_inv_natCast hv (by omega)]

end BlockBand.Transmission.SourceMixing
