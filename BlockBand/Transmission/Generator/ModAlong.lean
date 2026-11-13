module

public import BlockBand.Transmission.Generator.ModPath
public import BlockBand.Transmission.Generator.PowSum

/-!
# `PowerModulusAlong`: vanishing maximum jumps

* martingale and `G` parts: `nb·4L²/W²·R ≤ 8(T+1)R·δ ≤ θ/2`, with
  `R = 320·1296·K₄/η⁴ + 9(D₀k²)²C_g/η²` (`fourth_increment_bound`, conductance moments at
  `p = 4`), for `δ = min(1/4, θ/(2(8(T+1)R + 1)))`;
* drift-error part: `Σ‖e_u‖₁ ≤ Σ_{lengthWindow ε T'}‖e_u‖₂ ≤ (θ/2)(η/3)` eventually
  (`powerDriftSummable_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Finset Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

theorem modL_le {δ : ℝ} {W : ℕ} (hδ : 0 ≤ δ) (hWδ : 1 ≤ δ * W) :
    (modL δ W : ℝ) ≤ 2 * δ * W := by
  have := Nat.floor_le (mul_nonneg (Nat.cast_nonneg W) hδ)
  simp only [modL]; push_cast; nlinarith

theorem modNb_mul_le {T δ : ℝ} {W : ℕ} (hT : 0 ≤ T) :
    (modNb T δ W : ℝ) * modL δ W ≤ T * W + modL δ W := by
  have h1 : modNb T δ W * modL δ W ≤ ⌊(W : ℝ) * T⌋₊ + modL δ W := by
    show (⌊(W : ℝ) * T⌋₊ / modL δ W + 1) * modL δ W ≤ _
    rw [add_mul, one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  have h2 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg W) hT)
  have h3 : ((modNb T δ W * modL δ W : ℕ) : ℝ) ≤ ((⌊(W : ℝ) * T⌋₊ + modL δ W : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h3; nlinarith

/-- The block range lies in `[εW/2, (ε+T+1)W]`, inside `lengthWindow ε (ε+T+1)`. -/
theorem modulus_range {ε T δ : ℝ} {W : ℕ} (hε : 0 < ε) (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (hδ4 : δ ≤ 1 / 4) (hWε : 2 ≤ ε * W) (hWδ : 1 ≤ δ * W) :
    ∀ u < (modNb T δ W + 1) * modL δ W, 1 ≤ modA ε W + u ∧
      ε / 2 * W ≤ ((modA ε W + u : ℕ) : ℝ) ∧ ((modA ε W + u : ℕ) : ℝ) ≤ (ε + T + 1) * W ∧
        modA ε W + u + 1 ≤ ⌊(W : ℝ) * (ε + T + 1)⌋₊ := by
  intro u hu
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hL1 := modL_le hδ hWδ
  have hnbL := modNb_mul_le (δ := δ) (W := W) hT
  have ha1 : (modA ε W : ℝ) ≤ W * ε := Nat.floor_le (mul_nonneg hW0 hε.le)
  have ha2 : W * ε < modA ε W + 1 := Nat.lt_floor_add_one _
  have hu' : ((u + 1 : ℕ) : ℝ) ≤ ((modNb T δ W + 1) * modL δ W : ℕ) := by exact_mod_cast hu
  push_cast at hu'
  have htop : (modA ε W : ℝ) + u + 1 ≤ W * (ε + T + 1) := by nlinarith
  have ha0 : 1 ≤ modA ε W := by
    have : (1 : ℝ) ≤ modA ε W := by linarith
    exact_mod_cast this
  refine ⟨by omega, ?_, ?_, ?_⟩
  · push_cast; nlinarith
  · push_cast; nlinarith
  · apply Nat.le_floor; push_cast; linarith

/-- The real bookkeeping of the martingale and `G` parts. -/
theorem modulus_real_le {nb L W T δ K c Cg η : ℝ} (hL : 0 ≤ L) (hW : 0 < W)
    (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1 / 4) (hK : 0 ≤ K) (hCg : 0 ≤ Cg) (hη : 0 < η)
    (hnbL : nb * L ≤ T * W + L) (hL1 : L ≤ 2 * δ * W) :
    nb * (320 * (2 * L) ^ 2 * (K / W ^ 2) / (η / 6) ^ 4 +
        (2 * L) ^ 2 * ((c / W) ^ 2 * Cg) / (η / 3) ^ 2) ≤
      δ * (8 * (T + 1) * (320 * 1296 * K / η ^ 4 + 9 * c ^ 2 * Cg / η ^ 2)) := by
  set R := 320 * 1296 * K / η ^ 4 + 9 * c ^ 2 * Cg / η ^ 2
  have hR : 0 ≤ R := by positivity
  have e1 : nb * (320 * (2 * L) ^ 2 * (K / W ^ 2) / (η / 6) ^ 4 +
      (2 * L) ^ 2 * ((c / W) ^ 2 * Cg) / (η / 3) ^ 2) = nb * L * L / W ^ 2 * (4 * R) := by
    simp only [R]; field_simp; ring
  rw [e1]
  have hnL : nb * L * L ≤ 2 * δ * (T + 1) * W ^ 2 := by
    calc nb * L * L ≤ (T * W + L) * L := mul_le_mul_of_nonneg_right hnbL hL
      _ ≤ (T * W + 2 * δ * W) * (2 * δ * W) :=
          mul_le_mul (by linarith) hL1 hL (by positivity)
      _ ≤ 2 * δ * (T + 1) * W ^ 2 := by
          have h12 : 0 ≤ 1 - 2 * δ := by linarith
          have : 0 ≤ 2 * δ * W ^ 2 * (1 - 2 * δ) := by positivity
          nlinarith
  have : nb * L * L / W ^ 2 ≤ 2 * δ * (T + 1) := by
    rw [div_le_iff₀ (by positivity)]; linarith
  calc nb * L * L / W ^ 2 * (4 * R) ≤ 2 * δ * (T + 1) * (4 * R) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = δ * (8 * (T + 1) * R) := by ring

/-- The drift-error part lies inside `lengthWindow`. -/
theorem modulus_drift_le (b E E' : ℝ) (W k : ℕ) {ε T' : ℝ} {n : ℕ}
    (hn : modA ε W + n ≤ ⌊(W : ℝ) * T'⌋₊) :
    ∑ u ∈ range n, eLpNorm (driftError b E E' W k (modA ε W + u)) 1 (growthPathLaw W b) ≤
      ∑ r ∈ lengthWindow ε T' W, eLpNorm (driftError b E E' W k r) 2 (growthPathLaw W b) := by
  have hsum : ∑ u ∈ range n, eLpNorm (driftError b E E' W k (modA ε W + u)) 1
      (growthPathLaw W b) = ∑ r ∈ Ico (modA ε W) (modA ε W + n),
        eLpNorm (driftError b E E' W k r) 1 (growthPathLaw W b) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  rw [hsum]
  calc ∑ r ∈ Ico (modA ε W) (modA ε W + n), eLpNorm (driftError b E E' W k r) 1
        (growthPathLaw W b)
      ≤ ∑ r ∈ Ico (modA ε W) (modA ε W + n), eLpNorm (driftError b E E' W k r) 2
        (growthPathLaw W b) :=
        Finset.sum_le_sum fun r _ => eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hn)

/-- **`PowerModulusAlong`** from the input hypotheses `hMT, hGA, hLp, hP`. -/
theorem powerModulusAlong_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) : PowerModulusAlong := by
  intro b hb0 hb E hE1 hE2 Ce e he k hk ε T hε hεT η θ hη hθ
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hκ, -⟩ := mem_bulk_min hE1 hE2
  have hT0 : 0 < T := by linarith
  obtain ⟨K4, W4, hK4, h4⟩ := fourth_increment_bound hMT hGA hLp
    (κ := min (2 + E) (2 - E) / 2) (ε := ε / 2) (T := ε + T + 1) hb0 hb (by positivity)
    (by positivity) (by linarith) j
  obtain ⟨Cg, hgT⟩ := (LengthUniform.transmissionLengthUniform_holds hMT hGA hLp).conductance b
    hb0 hb (min (2 + E) (2 - E) / 2) (ε / 2) ((4 : ℕ) : ℝ) (by positivity) (by positivity)
    (by norm_num)
  obtain ⟨Wg, hg⟩ := hgT (ε + T + 1)
  have hDS := powerDriftSummable_holds hMT hGA hLp hP b hb0 hb E hE1 hE2 Ce e he (j + 1)
    (by omega) ε (ε + T + 1) hε (by linarith)
  have hD : 0 ≤ transportD0 b E := transportD0_nonneg hb0 hE1 hE2
  have hCg : 0 ≤ max Cg 0 := le_max_right _ _
  obtain ⟨Q, hQ, hQdef⟩ : ∃ Q : ℝ, 0 ≤ Q ∧ Q = 8 * (T + 1) * (320 * 1296 * K4 / η ^ 4 +
      9 * (transportD0 b E * ((j + 1 : ℕ) : ℝ) ^ 2) ^ 2 * max Cg 0 / η ^ 2) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨δ, hδ, hδ4, hδQ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ δ * Q ≤ θ / 2 := by
    refine ⟨min (1 / 4) (θ / (2 * (Q + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    have h1 : min (1 / 4) (θ / (2 * (Q + 1))) ≤ θ / (2 * (Q + 1)) := min_le_right _ _
    have h3 : θ / (2 * (Q + 1)) * Q ≤ θ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  refine ⟨δ, hδ, ?_⟩
  have hc : (0 : ℝ≥0∞) < ENNReal.ofReal (θ / 2 * (η / 3)) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨W1, hW1⟩ := eventually_atTop.1 (hDS.eventually (Iic_mem_nhds hc))
  refine ⟨max (max W4 Wg) (max W1 (max (EnergyUniform.windowWidth (min (2 + E) (2 - E)) Ce)
    ⌈2 / ε + 1 / δ⌉₊)), fun W hW => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW4, hWg⟩, hW1', hWw, hWc⟩ := hW
  have hmem := along_mem_bulk hE1 hE2 he hWw
  obtain ⟨he1, he2⟩ := bulk_bounds' (by positivity) hmem
  have hWr : 2 / ε + 1 / δ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWc)
  have hεd : 0 < 2 / ε := by positivity
  have hδd : 0 < 1 / δ := by positivity
  have hWpos : (0 : ℝ) < W := by linarith
  have hWε : 2 ≤ ε * W := by
    have : 2 / ε ≤ W := by linarith
    rw [div_le_iff₀ hε] at this; linarith
  have hWδ : 1 ≤ δ * W := by
    have : 1 / δ ≤ W := by linarith
    rw [div_le_iff₀ hδ] at this; linarith
  have hrange := modulus_range hε hT0.le hδ.le hδ4 hWε hWδ
  have H4 : ∀ u < (modNb T δ W + 1) * modL δ W, ∫ ω, powerIncrement b (e W) W (j + 1)
      (modA ε W + u) ω ^ 4 ∂growthPathLaw W b ≤ K4 / (W : ℝ) ^ 2 := fun u hu => by
    obtain ⟨r1, r2, r3, -⟩ := hrange u hu
    exact h4 W hW4 (e W) hmem _ r1 r2 r3
  have Hg : ∀ u < (modNb T δ W + 1) * modL δ W, ∫ ω, pathConductance b (e W) W
      (modA ε W + u) ω ^ 4 ∂growthPathLaw W b ≤ max Cg 0 := fun u hu => by
    obtain ⟨-, r2, r3, -⟩ := hrange u hu
    refine integral_pow_le_of_lintegral (SourceMixing.measurable_pathConductance b (e W) _) ?_ 4
      hCg ((hg W hWg (e W) hmem _ r2 r3).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    filter_upwards [pathPower_mem (W := W) (b := b) (by linarith) he1 he2] with ω hm
    obtain ⟨a0, a1, -⟩ := hm 1 (modA ε W + u) le_rfl
    exact a0.trans a1
  refine (modulus_fixedW hb0 hb hE1 hE2 he1 he2 (by omega : 1 ≤ j + 1) hε.le hη H4 Hg).trans ?_
  rw [show ENNReal.ofReal θ = ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf]
  refine add_le_add (ENNReal.ofReal_le_ofReal ?_) ?_
  · refine (modulus_real_le (Nat.cast_nonneg _) hWpos hT0.le hδ.le hδ4 hK4
      hCg hη (modNb_mul_le hT0.le) (modL_le hδ.le hWδ)).trans ?_
    rw [← hQdef]; exact hδQ
  · refine ENNReal.div_le_of_le_mul ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    have hn : modA ε W + (modNb T δ W + 1) * modL δ W ≤ ⌊(W : ℝ) * (ε + T + 1)⌋₊ := by
      have hpos : 0 < (modNb T δ W + 1) * modL δ W :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
      have := (hrange ((modNb T δ W + 1) * modL δ W - 1) (by omega)).2.2.2
      omega
    exact (modulus_drift_le b E (e W) W (j + 1) hn).trans (hW1 W hW1')

end BlockBand.Transmission.Generator
