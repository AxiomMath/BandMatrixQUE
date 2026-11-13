module

public import BlockBand.Transmission.PathJet.DiskSD

/-!
# The one-port mean equations on the parameter disk

With `v = vW b E w X = E⟨𝒢₁₁(w)⟩`, `u = uW b E w X = E⟨𝒢₂₂(w)⟩`, `ζ = -E - cv - bu` and
`f = W⁻¹Tr(· - X)⁻¹` (`stieltjes`), for strictly passive `X`:
* `meanEq_port_w`: `|u(w - bv) - 1| ≤ C/W²`.

The companion bound `|v - f(ζ)| ≤ C/W²` whenever `Im ζ ≥ ι₀` (`C` depends on `ι₀`) is proved in the
sibling module, `meanEq_phys_w`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `⟨𝒢₁₁(w)⟩`. -/
abbrev physTrW (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  (W : ℂ)⁻¹ * (passiveLetter E w X ω 0).trace

/-- `⟨𝒢₂₂(w)⟩`. -/
abbrev portTrW (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  (W : ℂ)⁻¹ * (passiveLetter E w X ω 3).trace

theorem trace_letter0_w (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    (passiveLetter E w X ω 0).trace = ∑ y, gW E w X ω (phys y) (phys y) := rfl

theorem trace_letter3_w (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    (passiveLetter E w X ω 3).trace = ∑ y, gW E w X ω (port y) (port y) := rfl

/-- The layer moments of `PassiveBoundsStatement` on the disk, uniformly on `bulkInterval κ`. -/
theorem layer_moments_w (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (p : ℝ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖gW E w X ω‖) (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, W₀, h⟩ := hA.moments b hb0 hb κ hκ p hp
  exact ⟨C, W₀, fun W hW E hE w hw X hX => (h W hW E hE w hw X hX).2.1⟩

/-- One-letter traces against a word with one deterministic insertion, on the disk. -/
theorem wordCov_w (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Kd : ℝ) (hKd : 1 ≤ Kd) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (k m : Fin 6) (D : Matrix (Fin W) (Fin W) ℂ), ‖D‖ ≤ Kd →
        let μ := layerLaw W b .oneBlockOnePort
        let f := fun ω => (W : ℂ)⁻¹ * (passiveLetter E w X ω k).trace
        let U := fun ω => D * passiveLetter E w X ω m
        Integrable f μ ∧ (∀ x y, Integrable (fun ω => U ω x y) μ) ∧
          (∀ x y, Integrable (fun ω => f ω * U ω x y) μ) ∧
          ‖matrixExpect μ (fun ω => f ω • U ω) - (∫ ω, f ω ∂μ) • matrixExpect μ U‖ ≤
            C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₀, h⟩ := hA.traceMatrix b hb0 hb κ hκ 1 Kd
  refine ⟨C, W₀, fun W hW E hE w hw X hX k m D hD => ?_⟩
  have hD1 : ∀ j : Fin 2, ‖(fun _ : Fin 2 => (1 : Matrix (Fin W) (Fin W) ℂ)) j‖ ≤ Kd :=
    fun _ => norm_one_matrix_le.trans hKd
  have hD2 : ∀ j : Fin 2, ‖(![D, 1] : Fin 2 → Matrix (Fin W) (Fin W) ℂ) j‖ ≤ Kd := by
    intro j; fin_cases j
    · simpa using hD
    · simpa using norm_one_matrix_le.trans hKd
  have := h W hW E hE w hw X hX 1 1 le_rfl le_rfl
    (fun _ => (k, false)) (fun _ => 1) (fun _ => (m, false)) ![D, 1] hD1 hD2
  have hw' : passiveWord E w X (fun _ : Fin 1 => (m, false)) ![D, 1] =
      fun ω => D * passiveLetter E w X ω m := by
    funext ω; simp [passiveWord, List.ofFn_succ]
  simp only [passiveWord_single_fun, hw'] at this
  exact this

theorem uW_eq_sum {b E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    (hint : ∀ x, Integrable (fun ω => gW E w X ω (port x) (port x)) (layerLaw W b .oneBlockOnePort)) :
    uW b E w X = (W : ℂ)⁻¹ * ∑ x, ∫ ω, gW E w X ω (port x) (port x) ∂layerLaw W b .oneBlockOnePort := by
  rw [← integral_finsetSum _ (fun x _ => hint x), ← integral_const_mul]
  rfl

/-- **The port mean equation on the disk**: `|u(w - bv) - 1| ≤ C/W²`. -/
theorem meanEq_port_w (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      0 < w.im → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
        ‖uW b E w X * (w - (b : ℂ) * vW b E w X) - 1‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C2, W2, m2⟩ := layer_moments_w hA hb0 hb hκ (2 * (1 : ℕ)) (by norm_num)
  obtain ⟨C4, W4, m4⟩ := layer_moments_w hA hb0 hb hκ (2 * (2 : ℕ)) (by norm_num)
  obtain ⟨C, W₁, hcov⟩ := wordCov_w hA hb0 hb hκ 1 le_rfl
  refine ⟨b * max C 0, max (max W₁ W2) (max W4 1), by positivity,
    fun W hW E hE w hwD hw X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW4, hW0⟩ := hW
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW0
  set μ := layerLaw W b .oneBlockOnePort
  set v := vW b E w X
  set g : Fin W → ℂ := fun x => ∫ ω, gW E w X ω (port x) (port x) ∂μ
  have hc := hcov W hW1 E hE w hwD X hX.posSemidef 0 3 1 (by simpa using norm_one_matrix_le)
  have hint : ∀ x, Integrable (fun ω => gW E w X ω (port x) (port x)) μ := fun x => by
    have h' := hc.2.1 x x; simp only [one_mul] at h'; exact h'
  have hentry : ∀ x, ‖1 - w * g x + (b : ℂ) * v * g x‖ ≤ b * max C 0 / (W : ℝ) ^ 2 := by
    intro x
    have hSD := meanSD_port_w hw hX (m2 W hW2 E hE w hwD X hX.posSemidef)
      (m4 W hW4 E hE w hwD X hX.posSemidef) x (port x)
    have hl : ∫ ω, (layerLin ω * gW E w X ω) (port x) (port x) ∂μ = 1 - w * g x := by
      rw [integral_congr_ae ((ae_layerLin_mul_w b E hw hX).mono fun ω h => by
        rw [h, Matrix.sub_apply, H0_port, Matrix.one_apply_eq])]
      rw [integral_sub (integrable_const _) ((hint x).const_mul _), integral_const_mul]
      have h1' : ∫ _ω, (1 : ℂ) ∂μ = 1 := by simp
      rw [h1']
    have hr : ∫ ω, (∑ y, gW E w X ω (phys y) (phys y)) * gW E w X ω (port x) (port x) ∂μ =
        (W : ℂ) * ∫ ω, physTrW E w X ω * gW E w X ω (port x) (port x) ∂μ := by
      rw [← integral_const_mul]; congr 1; funext ω
      have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      simp only [physTrW, trace_letter0_w]; field_simp
    obtain ⟨-, -, -, hn⟩ := hc
    have hn' : ‖(∫ ω, physTrW E w X ω * gW E w X ω (port x) (port x) ∂μ) - v * g x‖ ≤
        C / (W : ℝ) ^ 2 := by
      refine le_trans (le_of_eq ?_) ((norm_entry_le' _ x x).trans hn)
      simp [matrixExpect, Matrix.sub_apply, Matrix.smul_apply, v, g, vW, μ]
      rfl
    rw [hl, hr, ginVar_cast hb0] at hSD
    have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have e : 1 - w * g x + (b : ℂ) * v * g x =
        -(b : ℂ) * ((∫ ω, physTrW E w X ω * gW E w X ω (port x) (port x) ∂μ) - v * g x) := by
      rw [hSD]; field_simp; ring
    rw [e, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    calc b * _ ≤ b * (max C 0 / (W : ℝ) ^ 2) := by
          gcongr; exact hn'.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
      _ = _ := by ring
  rw [uW_eq_sum hint]
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have e : ((W : ℂ)⁻¹ * ∑ x, g x) * (w - (b : ℂ) * v) - 1 =
      -((W : ℂ)⁻¹ * ∑ x, (1 - w * g x + (b : ℂ) * v * g x)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    field_simp; ring
  show ‖((W : ℂ)⁻¹ * ∑ x, g x) * (w - (b : ℂ) * v) - 1‖ ≤ _
  rw [e, norm_neg, norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖∑ x, (1 - w * g x + (b : ℂ) * v * g x)‖
      ≤ (W : ℝ)⁻¹ * ∑ _x : Fin W, b * max C 0 / (W : ℝ) ^ 2 := by
        gcongr; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => hentry x)
    _ = b * max C 0 / (W : ℝ) ^ 2 := by simp; field_simp

end BlockBand.Transmission.PathJet
