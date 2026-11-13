module

public import BlockBand.Internal.Contracts.TransmissionUniform
public import BlockBand.SourceProcess.FullSource.Statement

/-!
# The energy window and `FullSourceMomentsEnergyUniformContract` from the bulk-uniform form

The full clock moments and full tag clock moments, uniformly in the energy window.

* `window_mem_bulkInterval`: for `W ≥ windowWidth κI Ce`, every `E ∈ bulkInterval κI` and every
  `E'` with `|E' - E| ≤ Ce W⁻²` (`IsNearEnergy Ce W E E'`) has `E' ∈ bulkInterval (κI/2)`.
* `fullSourceMomentsEnergyUniform_of_bulk`: `FullSourceMomentsEnergyUniformContract`
  from the bulk-uniform `FullSourceMomentsBulk`, applied at the margin `κI/2`, with
  `W₀ := max W₀(κI/2) (windowWidth κI Ce)` and the same constant `C`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.EnergyUniform

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.SourceProcess.FullSource
open scoped ENNReal

/-- The width beyond which the window `|E' - E| ≤ Ce W⁻²` has radius at most `κI / 2`. -/
def windowWidth (κI Ce : ℝ) : ℕ := ⌈2 * max Ce 0 / κI⌉₊ + 1

theorem window_radius_le {κI Ce : ℝ} (hκ : 0 < κI) {W : ℕ} (hW : windowWidth κI Ce ≤ W) :
    Ce / (W : ℝ) ^ 2 ≤ κI / 2 := by
  have hW1 : (1 : ℝ) ≤ W := by
    have : 1 ≤ W := le_trans (Nat.le_add_left 1 _) hW
    exact_mod_cast this
  have hWpos : (0 : ℝ) < W := by linarith
  have hceil : 2 * max Ce 0 / κI ≤ W := by
    have h1 := Nat.le_ceil (2 * max Ce 0 / κI)
    have h2 : ((⌈2 * max Ce 0 / κI⌉₊ : ℕ) : ℝ) + 1 ≤ W := by exact_mod_cast hW
    linarith
  have hmax : max Ce 0 ≤ κI / 2 * W := by
    rw [div_le_iff₀ hκ] at hceil; nlinarith
  have hsq : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
  have hW2 : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ hW2]
  have hκ2 : 0 ≤ κI / 2 := by linarith
  calc Ce ≤ max Ce 0 := le_max_left _ _
    _ ≤ κI / 2 * W := hmax
    _ ≤ κI / 2 * (W : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hκ2

/-- **Window lemma**: near energies of a bulk energy stay in the half-margin bulk. -/
theorem window_mem_bulkInterval {κI Ce : ℝ} (hκ : 0 < κI) {W : ℕ}
    (hW : windowWidth κI Ce ≤ W) {E E' : ℝ} (hE : E ∈ bulkInterval κI)
    (hE' : IsNearEnergy Ce W E E') : E' ∈ bulkInterval (κI / 2) := by
  have hr := window_radius_le hκ hW
  have hab := abs_le.mp (le_trans hE' hr)
  obtain ⟨h1, h2⟩ := hE
  exact ⟨by linarith [hab.1], by linarith [hab.2]⟩

/-- **`FullSourceMomentsEnergyUniformContract`** from `FullSourceMomentsBulk`. -/
theorem fullSourceMomentsEnergyUniform_of_bulk (h : FullSourceMomentsBulk) :
    FullSourceMomentsEnergyUniformContract where
  clock b hb hb' κI Ce T p hκ hp := by
    obtain ⟨C, W₀, hC⟩ := h.clock b hb hb' (κI / 2) T p (by linarith) hp
    refine ⟨C, max W₀ (windowWidth κI Ce), fun W hW E hE E' hE' j hj => ?_⟩
    exact hC W (le_of_max_le_left hW) E'
      (window_mem_bulkInterval hκ (le_of_max_le_right hW) hE hE') j hj
  clockSquare b hb hb' κI Ce T hκ := by
    obtain ⟨C, W₀, hC⟩ := h.clockSquare b hb hb' (κI / 2) T (by linarith)
    refine ⟨C, max W₀ (windowWidth κI Ce), fun W hW E hE E' hE' j hj => ?_⟩
    exact hC W (le_of_max_le_left hW) E'
      (window_mem_bulkInterval hκ (le_of_max_le_right hW) hE hE') j hj
  tag b hb hb' κI Ce T p hκ hp := by
    obtain ⟨C, W₀, hC⟩ := h.tag b hb hb' (κI / 2) T p (by linarith) hp
    refine ⟨C, max W₀ (windowWidth κI Ce), fun W hW E hE E' hE' j hj k hk => ?_⟩
    exact hC W (le_of_max_le_left hW) E'
      (window_mem_bulkInterval hκ (le_of_max_le_right hW) hE hE') j hj k hk

end BlockBand.Transmission.EnergyUniform
