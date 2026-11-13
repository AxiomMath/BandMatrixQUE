module

public import BlockBand.DeterminantScore.SelectedResolventTransfer

/-!
# Polynomial grids of symmetric intervals

Finite grids of `[-L, L]` with spacing `h`, with at most `2L/h + 2` points, every point of the
interval lying within `h` of the grid.

## Main results

* `intervalGrid L h = bulkGrid (2 - L) h` (`bulkInterval (2 - L) = [-L, L]`).
* `intervalGrid_mem` (`L ≥ 0`): grid points lie in `[-L, L]`.
* `intervalGrid_card_le` (`L ≥ 0`, `h > 0`): at most `2L/h + 2` points.
* `exists_intervalGrid_near` (`h > 0`): every `|x| ≤ L` is within `h` of a grid point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open BlockBand.DeterminantScore.SelectedResolvent BlockBand.Internal.Contracts.Layers

/-- A grid of `[-L, L]` of spacing `h` (the grid `bulkGrid (2 - L) h` of
`bulkInterval (2 - L) = [-L, L]`). -/
def intervalGrid (L h : ℝ) : Finset ℝ := bulkGrid (2 - L) h

theorem mem_bulkInterval_two_sub_iff {L x : ℝ} : x ∈ bulkInterval (2 - L) ↔ |x| ≤ L := by
  unfold bulkInterval
  rw [Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Grid points lie in `[-L, L]`. -/
theorem intervalGrid_mem {L h : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) {g : ℝ}
    (hg : g ∈ intervalGrid L h) : |g| ≤ L :=
  mem_bulkInterval_two_sub_iff.mp (bulkGrid_mem (by linarith) hh hg)

/-- The grid of `[-L, L]` of spacing `h > 0` has at most `2L/h + 2` points. -/
theorem intervalGrid_card_le {L h : ℝ} (hL : 0 ≤ L) (hh : 0 < h) :
    ((intervalGrid L h).card : ℝ) ≤ 2 * L / h + 2 := by
  unfold intervalGrid bulkGrid
  have h1 : (((Finset.range (⌈(4 - 2 * (2 - L)) / h⌉₊ + 1)).image
      fun j : ℕ => min (-2 + (2 - L) + j * h) (2 - (2 - L))).card : ℝ) ≤
      ((⌈(4 - 2 * (2 - L)) / h⌉₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_image_le).trans (Finset.card_range _).le
  have e : (4 - 2 * (2 - L)) / h = 2 * L / h := by ring_nf
  have h2 : ((⌈(4 - 2 * (2 - L)) / h⌉₊ : ℕ) : ℝ) < 2 * L / h + 1 :=
    calc ((⌈(4 - 2 * (2 - L)) / h⌉₊ : ℕ) : ℝ) < (4 - 2 * (2 - L)) / h + 1 :=
          Nat.ceil_lt_add_one (by rw [e]; positivity)
      _ = 2 * L / h + 1 := by rw [e]
  push_cast at h1
  linarith

/-- Every `|x| ≤ L` is within `h` of the grid. -/
theorem exists_intervalGrid_near {L h : ℝ} (hh : 0 < h) {x : ℝ} (hx : |x| ≤ L) :
    ∃ g ∈ intervalGrid L h, |x - g| ≤ h :=
  exists_bulkGrid_near hh (mem_bulkInterval_two_sub_iff.mpr hx)

end BlockBand.LocalWindow.ProofPartTwo
