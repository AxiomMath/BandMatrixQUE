module

public import BlockBand.SourceProcess.FullSource.SqBound

/-!
# The tag-square bound, uniformly on a bulk interval

* `SqBirthMoments`: moments of the tag square at its birth length, uniformly in `k`;
* `TagSqBulk`: `E h_{j;k} ≤ C(j+1)` for `k < j ≤ TW` (`C` depends on `b, κ, T`);
* `tagSqBulk_of`: `TagSqBulk` from `FullSourceEstimates`, `PassiveMeanStep`,
  `PassiveFluctuationStep`, SUPX, `SqBirthMoments` and the tag bound `TagPropagationBulk`
  (which pays the additive `E t_j²`, without stopping).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

/-- Moments of a tag square at its birth length `k+1`, uniformly in `k` and on a bulk
interval. -/
def SqBirthMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ q : ℕ, 1 ≤ q →
    ∃ (B : ℝ) (W₀ : ℕ), 0 ≤ B ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ k : ℕ,
      ∫⁻ ω, ENNReal.ofReal (tagSq b E W (k + 1) k ω ^ q) ∂growthPathLaw W b ≤ ENNReal.ofReal B

/-- The tag-square bound `E h_{j;k} ≤ C(j+1)` on a bulk interval. -/
def TagSqBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧
    ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ j k : ℕ, k < j → (j : ℝ) ≤ T * W →
      ∫⁻ ω, ENNReal.ofReal (tagSq b E W j k ω) ∂growthPathLaw W b ≤
        ENNReal.ofReal (C * ((j : ℝ) + 1))

/-- **The uniform tag-square bound.** -/
theorem tagSqBulk_of (hFS : FullSourceEstimates) (hMS : PassiveMeanStep)
    (hFl : PassiveFluctuationStep) (hSX : SuperexpExit) (hSB : SqBirthMoments)
    (hTP : TagPropagationBulk) : TagSqBulk := by
  intro b hb0 hb κ T hκ
  obtain ⟨Ca, C₂, Cn, CN₂, CN, Cf, Cm, ρ, d₀, WL, hCa, hC₂, hCn, hCN, hCf, hCm, hρ0, hρ1, hd₀,
    hL⟩ := tagLayerBounds_of hFS hMS hFl hb0 hb hκ (n := 2) le_rfl
  obtain ⟨B₁, Wb1, hB₁, hb1⟩ := hSB b hb0 hb κ hκ 1 le_rfl
  obtain ⟨B₂, Wb2, hB₂, hb2⟩ := hSB b hb0 hb κ hκ 2 (by norm_num)
  set L := lsq Ca
  have hL0 : 0 ≤ L := lsq_nonneg hCa
  set K := 2 * L / (1 - ρ)
  have hK : 0 ≤ K := div_nonneg (by linarith) (by linarith)
  have hKL : L ≤ K * (1 - ρ) / 2 := by
    simp only [K]; rw [div_mul_cancel₀ _ (by linarith : (1 - ρ) ≠ 0)]; linarith
  set d := min (min d₀ 1) ((1 - ρ) / (2 * (ρ * L + 1)))
  have hden : 0 < 2 * (ρ * L + 1) := by nlinarith [mul_nonneg hρ0 hL0]
  have hd0 : 0 < d := lt_min (lt_min hd₀ one_pos) (div_pos (by linarith) hden)
  have hd1 : d ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hdd₀ : d ≤ d₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρLd : ρ * L * d ≤ (1 - ρ) / 2 := by
    have h1 : d ≤ (1 - ρ) / (2 * (ρ * L + 1)) := min_le_right _ _
    have h2 : ρ * L * d ≤ ρ * L * ((1 - ρ) / (2 * (ρ * L + 1))) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hρ0 hL0)
    have h3 : ρ * L * ((1 - ρ) / (2 * (ρ * L + 1))) ≤ (1 - ρ) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
      nlinarith [mul_nonneg hρ0 hL0]
    linarith
  set α := alphaSq K Cm Ca Cf CN
  have hα : 0 ≤ α := alphaSq_nonneg hK hCm hCa hCN
  set D := dsq K Cm C₂ ρ
  have hD : 0 ≤ D := by simp only [D, dsq]; positivity
  set T₀ := max T 0
  obtain ⟨Ct, hCt⟩ := hTP b hb0 hb κ T₀ 2 hκ (by norm_num)
  obtain ⟨Wt, hWt⟩ := hCt T
  set τ := (max Ct 0) ^ 2
  have hτ0 : 0 ≤ τ := sq_nonneg _
  obtain ⟨c, Ws, hc, hSup⟩ := hSX b hb0 hb κ T hκ d hd0
  obtain ⟨W₃, hW₃⟩ := superexp_absorbs (A := max (CN ^ (2 * (2 * 2))) 1) (B := B₂) (c := c)
    (T := T) (R := T₀) (le_max_right _ _) hB₂ hc
  set C := Real.exp (α * T₀) * ((1 + K * d) * B₁ + D * τ) + 1
  have hKd : 0 ≤ 1 + K * d := add_nonneg zero_le_one (mul_nonneg hK hd0.le)
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, max (max (max WL Wb1) (max Wb2 Ws)) (max (max W₃ Wt) 1), hC0,
    fun W hW E hE j k hkj hjT => ?_⟩
  have hWL : WL ≤ W := le_trans (by simp) hW
  have hWb1 : Wb1 ≤ W := le_trans (by simp) hW
  have hWb2 : Wb2 ≤ W := le_trans (by simp) hW
  have hWs : Ws ≤ W := le_trans (by simp) hW
  have hW3 : W₃ ≤ W := le_trans (by simp) hW
  have hWt' : Wt ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := le_trans (by simp) hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  obtain ⟨hE1, hE2⟩ := bulk_bounds hκ hE
  obtain ⟨m, rfl⟩ : ∃ m, j = k + 1 + m := ⟨j - k - 1, by omega⟩
  have hTT : T * W ≤ T₀ * W := mul_le_mul_of_nonneg_right (le_max_left _ _) hW0.le
  have hcast : ((k + 1 + m : ℕ) : ℝ) = k + 1 + m := by push_cast; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hmR : (m : ℝ) ≤ T₀ * W := by linarith
  have hτ : ∀ i, i < m →
      ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1 + i) k ω ^ 2) ∂growthPathLaw W b ≤
        ENNReal.ofReal τ := by
    intro i hi
    have hi' : (i : ℝ) < m := by exact_mod_cast hi
    have hci : ((k + 1 + i : ℕ) : ℝ) = k + 1 + i := by push_cast; ring
    have h := hWt W hWt' E hE (k + 1 + i) k (by omega) (by rw [hci]; linarith)
      (by rw [hci]; linarith)
    exact eLpNorm_two_tag b E _ k (le_max_right _ _)
      (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  set P := (⌊T * W⌋₊ : ℝ) * Real.exp (-(c * W * Real.log W))
  have hP0 : 0 ≤ P := by positivity
  have hP : growthPathLaw W b (stopEv b E W k d (k + 1 + m))ᶜ ≤ ENNReal.ofReal P :=
    (measure_mono (stopEv_compl_subset b E k d T hjT)).trans (hSup W hWs E hE)
  have hbound := sq_moment_bound hb0 hb hE1 hE2 hW1 (hL W hWL E hE) hCa hC₂ hCN hCf hCm
    hK hρ0 hρ1 hKL hd1 hρLd hdd₀ hd0.le m hB₁ hB₂ hτ0 hP0 (hb1 W hWb1 E hE k)
    (hb2 W hWb2 E hE k) hτ hP
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : (1 + α / W) ^ m ≤ Real.exp (α * T₀) := one_add_pow_le_exp hα m hW0 hmR
  have h2 : (B₂ * (CN ^ (2 * (2 * 2))) ^ m * P) ^ (1 / 2 : ℝ) ≤ 1 := by
    refine Real.rpow_le_one (by positivity) ?_ (by norm_num)
    have := hW₃ W hW3 m hmR
    have hA : (CN ^ (2 * (2 * 2))) ^ m ≤ (max (CN ^ (2 * (2 * 2))) 1) ^ m :=
      pow_le_pow_left₀ (by positivity) (le_max_left _ _) m
    calc B₂ * (CN ^ (2 * (2 * 2))) ^ m * P ≤ B₂ * (max (CN ^ (2 * (2 * 2))) 1) ^ m * P := by
          gcongr
      _ = P * ((max (CN ^ (2 * (2 * 2))) 1) ^ m * B₂) := by ring
      _ ≤ 1 := this
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h3 : (1 + K * d) * B₁ + m * (D * τ) ≤ ((m : ℝ) + 1) * ((1 + K * d) * B₁ + D * τ) := by
    have a1 : (1 + K * d) * B₁ ≤ ((m : ℝ) + 1) * ((1 + K * d) * B₁) :=
      le_mul_of_one_le_left (mul_nonneg hKd hB₁) (by linarith)
    have a2 : (m : ℝ) * (D * τ) ≤ ((m : ℝ) + 1) * (D * τ) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hD hτ0)
    have a3 : ((m : ℝ) + 1) * ((1 + K * d) * B₁ + D * τ) =
        ((m : ℝ) + 1) * ((1 + K * d) * B₁) + ((m : ℝ) + 1) * (D * τ) := by ring
    linarith only [a1, a2, a3]
  have h4 := mul_le_mul h1 h3 (by positivity) (Real.exp_pos _).le
  have h5 : (m : ℝ) + 1 ≤ ((k + 1 + m : ℕ) : ℝ) + 1 := by rw [hcast]; linarith
  have h6 : C * ((m : ℝ) + 1) ≤ C * (((k + 1 + m : ℕ) : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left h5 hC0
  have e : C * ((m : ℝ) + 1) = Real.exp (α * T₀) * (((m : ℝ) + 1) * ((1 + K * d) * B₁ + D * τ)) +
      ((m : ℝ) + 1) := by simp only [C]; ring
  linarith only [h4, h2, e, h6, hm0]

end BlockBand.SourceProcess.FullSource
