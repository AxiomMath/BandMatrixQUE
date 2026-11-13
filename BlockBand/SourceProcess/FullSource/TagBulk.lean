module

public import BlockBand.SourceProcess.FullSource.TagLayer

/-!
# `TagPropagationBulk` from the one-layer inputs, superexponential exit and the birth moments

`tagPropagationBulk_of hFS hMS hFl hSUPX hBirth : TagPropagationBulk`. Inputs:
`FullSourceEstimates`, `PassiveMeanStep` and `PassiveFluctuationStep` (proved in
`PathScalar` / `PassiveLayer`), the superexponential exit (SUPX) bound in the form of
`PathScalar.passiveInitialScalar_superexp_of_scalarRecursion`, and `TagBirthMoments` (the
moments of a tag at its birth length). The constant is `(e^{αR}(1+Kd)B_n + 1)^{1/n}`; it does not
depend on the birth index nor on the total length `T`; only `W₀` does (through SUPX and
`superexp_absorbs`).
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

/-- The SUPX exit bound (the conclusion of
`PathScalar.passiveInitialScalar_superexp_of_scalarRecursion`). -/
def SuperexpExit : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∀ d : ℝ, 0 < d → ∃ (c : ℝ) (W₀ : ℕ), 0 < c ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      growthPathLaw W b {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ T * W ∧
        d < jetDistance0 b E (pathX b E W r ω)} ≤
        ENNReal.ofReal ((⌊T * W⌋₊ : ℝ) * Real.exp (-(c * W * Real.log W)))

/-- Moments of a tag at its birth length `k+1`, uniformly in `k` and on a bulk interval. -/
def TagBirthMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ q : ℕ, 1 ≤ q →
    ∃ (B : ℝ) (W₀ : ℕ), 0 ≤ B ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ k : ℕ,
      ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ q) ∂growthPathLaw W b ≤ ENNReal.ofReal B

theorem one_add_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (m : ℕ) {W R : ℝ} (hW : 0 < W)
    (hm : (m : ℝ) ≤ R * W) : (1 + x / W) ^ m ≤ Real.exp (x * R) := by
  calc (1 + x / W) ^ m ≤ Real.exp (x / W) ^ m :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (x / W)]) m
    _ = Real.exp (x / W * m) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (x * R) := by
        refine Real.exp_le_exp.2 ?_
        have : x / W * m ≤ x / W * (R * W) := mul_le_mul_of_nonneg_left hm (by positivity)
        rwa [show x / W * (R * W) = x * R by field_simp] at this

/-- **The uniform tag bound.** -/
theorem tagPropagationBulk_of (hFS : FullSourceEstimates) (hMS : PassiveMeanStep)
    (hFl : PassiveFluctuationStep) (hSX : SuperexpExit) (hBirth : TagBirthMoments) :
    TagPropagationBulk := by
  intro b hb0 hb κ R p hκ hp
  set n : ℕ := max 2 ⌈p⌉₊
  have hn : 2 ≤ n := le_max_left _ _
  have hpn : p ≤ n := (Nat.le_ceil p).trans (by exact_mod_cast le_max_right 2 ⌈p⌉₊)
  obtain ⟨Ca, C₂, Cn, CN₂, CN, Cf, Cm, ρ, d₀, WL, hCa, hC₂, hCn, hCN, hCf, hCm, hρ0, hρ1, hd₀,
    hL⟩ := tagLayerBounds_of hFS hMS hFl hb0 hb hκ hn
  obtain ⟨Bn, Wbn, hBn, hbn⟩ := hBirth b hb0 hb κ hκ n (by omega)
  obtain ⟨B2n, Wb2n, hB2n, hb2n⟩ := hBirth b hb0 hb κ hκ (2 * n) (by omega)
  set L := lcoef Ca n
  have hL0 : 0 ≤ L := lcoef_nonneg hCa n
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
  set α := alphaW K Cm Ca C₂ Cn Cf CN n
  have hα : 0 ≤ α := by
    have := acoef_nonneg (C₂ := C₂) hCa hCn n
    simp only [α, alphaW]; positivity
  set R₀ := max R 0
  set X := Real.exp (α * R₀) * ((1 + K * d) * Bn) + 1
  have hX : 0 ≤ X := by positivity
  refine ⟨X ^ (1 / (n : ℝ)), fun T => ?_⟩
  obtain ⟨c, Ws, hc, hSup⟩ := hSX b hb0 hb κ T hκ d hd0
  obtain ⟨W₃, hW₃⟩ := superexp_absorbs (A := max (CN ^ (2 * (2 * n))) 1) (B := B2n) (c := c)
    (T := T) (R := R₀) (le_max_right _ _) hB2n hc
  refine ⟨max (max (max WL Wbn) (max Wb2n Ws)) (max W₃ 1), fun W hW E hE j k hkj hjT hjR => ?_⟩
  have hWL : WL ≤ W := le_trans (by simp) hW
  have hWbn : Wbn ≤ W := le_trans (by simp) hW
  have hWb2n : Wb2n ≤ W := le_trans (by simp) hW
  have hWs : Ws ≤ W := le_trans (by simp) hW
  have hW3 : W₃ ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := le_trans (by simp) hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  obtain ⟨hE1, hE2⟩ := bulk_bounds hκ hE
  obtain ⟨m, rfl⟩ : ∃ m, j = k + 1 + m := ⟨j - k - 1, by omega⟩
  have hmR : (m : ℝ) ≤ R₀ * W := by
    have : ((k + 1 + m : ℕ) : ℝ) = k + 1 + m := by push_cast; ring
    have hRW : R * W ≤ R₀ * W := mul_le_mul_of_nonneg_right (le_max_left _ _) hW0.le
    linarith
  set P := (⌊T * W⌋₊ : ℝ) * Real.exp (-(c * W * Real.log W))
  have hP0 : 0 ≤ P := by positivity
  have hP : growthPathLaw W b (stopEv b E W k d (k + 1 + m))ᶜ ≤ ENNReal.ofReal P :=
    (measure_mono (stopEv_compl_subset b E k d T hjT)).trans (hSup W hWs E hE)
  have hbound := tag_moment_bound hb0 hb hE1 hE2 hW1 hn (hL W hWL E hE) hCa hC₂ hCn hCN hCf hCm
    hK hρ0 hρ1 hKL hd1 hρLd hdd₀ hd0.le m hBn hB2n hP0 (hbn W hWbn E hE k) (hb2n W hWb2n E hE k)
    hP
  refine eLpNorm_tag_le b E _ k hp hpn hX (hbound.trans (ENNReal.ofReal_le_ofReal ?_))
  have h1 : (1 + α / W) ^ m ≤ Real.exp (α * R₀) := one_add_pow_le_exp hα m hW0 hmR
  have h2 : (B2n * (CN ^ (2 * (2 * n))) ^ m * P) ^ (1 / 2 : ℝ) ≤ 1 := by
    refine Real.rpow_le_one (by positivity) ?_ (by norm_num)
    have := hW₃ W hW3 m hmR
    have hA : (CN ^ (2 * (2 * n))) ^ m ≤ (max (CN ^ (2 * (2 * n))) 1) ^ m :=
      pow_le_pow_left₀ (by positivity) (le_max_left _ _) m
    calc B2n * (CN ^ (2 * (2 * n))) ^ m * P ≤ B2n * (max (CN ^ (2 * (2 * n))) 1) ^ m * P := by
          gcongr
      _ = P * ((max (CN ^ (2 * (2 * n))) 1) ^ m * B2n) := by ring
      _ ≤ 1 := this
  have h3 : 0 ≤ (1 + K * d) * Bn := mul_nonneg (by nlinarith [mul_nonneg hK hd0.le]) hBn
  have := mul_le_mul_of_nonneg_right h1 h3
  simp only [X]
  linarith

end BlockBand.SourceProcess.FullSource
