module

public import BlockBand.Transmission.Generator.ModBlock
public import BlockBand.Transmission.Generator.ModMoment
public import BlockBand.Transmission.Generator.Discrete

/-!
# The modulus at one width `W`, along the unabsorbed path

* `growthFiltration W`: `growthSigma W` as a Mathlib `Filtration ℕ`;
* `modA ε W = ⌊Wε⌋₊`, `modL δ W = ⌊Wδ⌋₊ + 1`, `modNb T δ W = ⌊WT⌋₊ / modL δ W + 1`;
* `modulus_subset`: the `[ε, T]`, `|t - t'| ≤ δ` event lies in `modBad X a L nb η` (floor
  bookkeeping);
* **`modulus_fixedW`**: `meas_modBad_le` with `G_u = D k² g_u²/W` (`|A_k(P)| ≤ Dk²g²`) and
  `e_u = driftError_u`, given `E Δ⁴_u ≤ K₄/W²` and `E g_u⁴ ≤ C_g` on the block range.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Finset
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal

/-- The growth filtration. -/
def growthFiltration (W : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (GrowthPath W)) where
  seq := growthSigma W
  mono' _ _ h := growthSigma_mono h
  le' := growthSigma_le W

def modA (ε : ℝ) (W : ℕ) : ℕ := ⌊(W : ℝ) * ε⌋₊
def modL (δ : ℝ) (W : ℕ) : ℕ := ⌊(W : ℝ) * δ⌋₊ + 1
def modNb (T δ : ℝ) (W : ℕ) : ℕ := ⌊(W : ℝ) * T⌋₊ / modL δ W + 1

/-- **Floor bookkeeping.** -/
theorem modulus_subset {Ω : Type*} (X : ℕ → Ω → ℝ) {W : ℕ} {ε T δ η : ℝ} (hε : 0 ≤ ε) :
    {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |X ⌊(W : ℝ) * t⌋₊ ω - X ⌊(W : ℝ) * t'⌋₊ ω|} ⊆
      modBad X (modA ε W) (modL δ W) (modNb T δ W) η := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hL : 0 < modL δ W := Nat.succ_pos _
  have key : ∀ t t' : ℝ, ε ≤ t → t ≤ t' → t' ≤ T → t' - t ≤ δ →
      modA ε W ≤ ⌊(W : ℝ) * t⌋₊ ∧ ⌊(W : ℝ) * t⌋₊ ≤ ⌊(W : ℝ) * t'⌋₊ ∧
        ⌊(W : ℝ) * t⌋₊ < modA ε W + modNb T δ W * modL δ W ∧
        ⌊(W : ℝ) * t'⌋₊ ≤ ⌊(W : ℝ) * t⌋₊ + modL δ W := by
    intro t t' h1 h2 h3 h4
    have ht0 : 0 ≤ t := hε.trans h1
    refine ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left h1 hW),
      Nat.floor_mono (mul_le_mul_of_nonneg_left h2 hW), ?_, ?_⟩
    · have hr : ⌊(W : ℝ) * t⌋₊ ≤ ⌊(W : ℝ) * T⌋₊ :=
        Nat.floor_mono (mul_le_mul_of_nonneg_left (h2.trans h3) hW)
      have := Nat.lt_div_mul_add (a := ⌊(W : ℝ) * T⌋₊) hL
      simp only [modNb, add_mul, one_mul]
      omega
    · have a1 := Nat.floor_le (mul_nonneg hW (ht0.trans h2))
      have a2 := Nat.lt_floor_add_one ((W : ℝ) * t)
      have a3 := Nat.lt_floor_add_one ((W : ℝ) * δ)
      have a4 : (W : ℝ) * t' ≤ W * t + W * δ := by nlinarith
      have : (⌊(W : ℝ) * t'⌋₊ : ℝ) < ⌊(W : ℝ) * t⌋₊ + (modL δ W : ℝ) + 1 := by
        simp only [modL]; push_cast; linarith
      have : ⌊(W : ℝ) * t'⌋₊ < ⌊(W : ℝ) * t⌋₊ + modL δ W + 1 := by exact_mod_cast this
      omega
  rintro ω ⟨t, ⟨ht1, ht2⟩, t', ⟨ht1', ht2'⟩, hδt, hη⟩
  rcases le_total t t' with h | h
  · obtain ⟨a1, a2, a3, a4⟩ := key t t' ht1 h ht2' (by rw [abs_le] at hδt; linarith)
    exact ⟨_, _, a1, a2, a3, a4, by rwa [abs_sub_comm]⟩
  · obtain ⟨a1, a2, a3, a4⟩ := key t' t ht1' h ht2 (by rw [abs_le] at hδt; linarith)
    exact ⟨_, _, a1, a2, a3, a4, hη⟩

theorem transportD0_nonneg {b E : ℝ} (hb0 : 0 < b) (h1 : -2 < E) (h2 : E < 2) :
    0 ≤ transportD0 b E := by
  have : 0 < 4 - E ^ 2 := by nlinarith
  unfold transportD0; positivity

/-- **The modulus at one width.** -/
theorem modulus_fixedW {b E E' : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (h1 : -2 < E') (h2 : E' < 2) {W : ℕ} {k : ℕ} (hk : 1 ≤ k) {ε T δ η K₄ Cg : ℝ} (hε : 0 ≤ ε) (hη : 0 < η)
    (h4 : ∀ u < (modNb T δ W + 1) * modL δ W,
      ∫ ω, powerIncrement b E' W k (modA ε W + u) ω ^ 4 ∂growthPathLaw W b ≤ K₄ / (W : ℝ) ^ 2)
    (hg : ∀ u < (modNb T δ W + 1) * modL δ W,
      ∫ ω, pathConductance b E' W (modA ε W + u) ω ^ 4 ∂growthPathLaw W b ≤ Cg) :
    growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |pathPower b E' W k ⌊(W : ℝ) * t⌋₊ ω - pathPower b E' W k ⌊(W : ℝ) * t'⌋₊ ω|} ≤
      ENNReal.ofReal (modNb T δ W * (320 * (2 * modL δ W : ℝ) ^ 2 * (K₄ / (W : ℝ) ^ 2) /
          (η / 6) ^ 4 + (2 * modL δ W : ℝ) ^ 2 *
            ((transportD0 b E * k ^ 2 / W) ^ 2 * Cg) / (η / 3) ^ 2)) +
        (∑ u ∈ range ((modNb T δ W + 1) * modL δ W),
          eLpNorm (driftError b E E' W k (modA ε W + u)) 1 (growthPathLaw W b)) /
            ENNReal.ofReal (η / 3) := by
  set μ := growthPathLaw W b
  set X : ℕ → GrowthPath W → ℝ := fun r => pathPower b E' W k r
  set ℱ := growthFiltration W
  set D := transportD0 b E
  have hD : 0 ≤ D := transportD0_nonneg hb0 hE1 hE2
  have hX : ∀ r, StronglyMeasurable[ℱ r] (X r) := fun r =>
    (measurable_pathPower_adapted b E' k r).stronglyMeasurable
  have hmem := pathPower_mem (W := W) (b := b) (by linarith) h1 h2
  have hB : ∀ r, ∀ᵐ ω ∂μ, |X r ω| ≤ W := fun r => by
    filter_upwards [hmem] with ω hm
    obtain ⟨a0, a1, a3⟩ := hm k r hk
    rw [abs_of_nonneg a0]; exact a1.trans a3
  have hgB : ∀ u, ModBdd μ (pathConductance b E' W u) := fun u =>
    ⟨(SourceMixing.measurable_pathConductance b E' u).aestronglyMeasurable, W, by
      filter_upwards [hmem] with ω hm
      obtain ⟨a0, a1, a3⟩ := hm 1 u le_rfl
      rw [abs_of_nonneg (a0.trans a1)]; exact a3⟩
  set c : ℝ := D * k ^ 2 / W
  set G : ℕ → GrowthPath W → ℝ := fun u ω => c * pathConductance b E' W u ω ^ 2
  set e : ℕ → GrowthPath W → ℝ := fun u => driftError b E E' W k u
  have hG2 : ∀ u, Integrable (fun ω => G u ω ^ 2) μ := fun u =>
    ((((hgB u).pow 2).const_mul c).pow 2).integrable
  have he : ∀ u, AEStronglyMeasurable (e u) μ := fun u =>
    (stronglyMeasurable_condExp.mono (growthSigma_le W u)).aestronglyMeasurable.sub
      ((measurable_drift_pathPowers b E E' k u).mono (growthSigma_le W u)
        le_rfl).aestronglyMeasurable
  have hd : ∀ u, ∀ᵐ ω ∂μ, |(μ[modInc X u | ℱ u]) ω| ≤ G u ω + |e u ω| := fun u => by
    filter_upwards [hmem] with ω hm
    have e1 : (μ[modInc X u | ℱ u]) ω = e u ω +
        transmissionDrift D k (pathPowers b E' W u ω) / W := by
      show (μ[powerIncrement b E' W k u | growthSigma W u]) ω = _
      simp only [e, driftError, Pi.sub_apply, D]; ring
    have hA : |transmissionDrift D k (pathPowers b E' W u ω)| ≤
        D * k ^ 2 * pathConductance b E' W u ω ^ 2 :=
      abs_transmissionDrift_le hD k fun j hj1 _ => by
        obtain ⟨a0, a1, -⟩ := hm j u hj1
        show |pathPower b E' W j u ω| ≤ _
        rw [abs_of_nonneg a0]; exact a1
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, Nat.abs_cast]
    have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    have : |transmissionDrift D k (pathPowers b E' W u ω)| / W ≤ G u ω := by
      simp only [G, c]
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hA hW0
    linarith
  have hL : 0 < modL δ W := Nat.succ_pos _
  have hGM : ∀ u < (modNb T δ W + 1) * modL δ W,
      ∫ ω, G (modA ε W + u) ω ^ 2 ∂μ ≤ c ^ 2 * Cg := fun u hu => by
    have e2 : (fun ω => G (modA ε W + u) ω ^ 2) =
        fun ω => c ^ 2 * pathConductance b E' W (modA ε W + u) ω ^ 4 := by
      funext ω; simp only [G]; ring
    rw [e2, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hg u hu) (sq_nonneg _)
  refine (measure_mono (modulus_subset X hε)).trans ?_
  exact meas_modBad_le ℱ hX hB G e hG2 he hd hL hη h4 hGM

end BlockBand.Transmission.Generator
