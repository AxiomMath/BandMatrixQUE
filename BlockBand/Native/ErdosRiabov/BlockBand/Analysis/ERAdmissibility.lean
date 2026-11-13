module

public import BlockBand.Native.ErdosRiabov.BlockBand.Model.GaussianRing

/-!
# The Erdős–Riabov profile hypotheses for the block band profile

The deterministic variance-profile conditions of Erdős–Riabov (Definition 2.1 and the cyclic
block structure of Example 2.3) hold for the block band variance profile.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing

open scoped BigOperators

/-- The deterministic variance-matrix part of Erdős–Riabov Definition 2.1,
with the bandwidth parameter of Erdős–Riabov equal to the block width `W` and
with the uniform flatness constant fixed to the exact value `C_W = 1`.

ER writes the stochasticity condition as a column sum.  Both row and column
normalizations are retained here so that no symmetry conversion is hidden. -/
structure ERDefinition21Profile (p : Params) : Prop where
  symmetric : ∀ x y : Site p.n p.W,
    varianceProfile p x y = varianceProfile p y x
  nonnegative : ∀ x y : Site p.n p.W, 0 ≤ varianceProfile p x y
  rowStochastic : ∀ x : Site p.n p.W,
    let _ := p.nNeZero
    ∑ y : Site p.n p.W, varianceProfile p x y = 1
  columnStochastic : ∀ y : Site p.n p.W,
    let _ := p.nNeZero
    ∑ x : Site p.n p.W, varianceProfile p x y = 1
  flat : ∀ x y : Site p.n p.W,
    varianceProfile p x y ≤ 1 / (p.W : ℝ)

/-- The exact block-band factorization required by Erdős–Riabov Example 2.3.
The paper has `S_ab = W⁻¹ σ_{⌈a/W⌉,⌈b/W⌉}`; in the product indexing used here this
is `varianceProfile = blockWeight / W`.
`support` says that the block
kernel has cyclic range one.
-/
structure ERBlockBandProfile (p : Params) : Prop where
  symmetric : ∀ k l : ZMod p.n, blockWeight p k l = blockWeight p l k
  nonnegative : ∀ k l : ZMod p.n, 0 ≤ blockWeight p k l
  stochastic : ∀ k : ZMod p.n,
    let _ := p.nNeZero
    ∑ l : ZMod p.n, blockWeight p k l = 1
  translationInvariant : ∀ k l t : ZMod p.n,
    blockWeight p (k + t) (l + t) = blockWeight p k l
  support : ∀ k l : ZMod p.n, blockWeight p k l ≠ 0 →
    l = k ∨ l = k + 1 ∨ l = k - 1
  factorization : ∀ x y : Site p.n p.W,
    varianceProfile p x y = blockWeight p x.1 y.1 / (p.W : ℝ)

/-- Each block coefficient is bounded above by the exactly normalized block-row
mass `c + 2b = 1`.  This proof does not identify coincident neighbours, and hence
is valid a fortiori uniformly in the parity of the cyclic block count. -/
theorem blockWeight_le_one (p : Params) (k l : ZMod p.n) :
    blockWeight p k l ≤ 1 := by
  have hc : 0 ≤ p.c := p.c_pos.le
  have hb : 0 ≤ p.b := p.b_pos.le
  have hdiag : (if l = k then p.c else 0) ≤ p.c := by
    split <;> simp [hc]
  have hplus : (if l = k + 1 then p.b else 0) ≤ p.b := by
    split <;> simp [hb]
  have hminus : (if l = k - 1 then p.b else 0) ≤ p.b := by
    split <;> simp [hb]
  rw [blockWeight]
  rw [← p.c_add_two_b]
  linarith

/-- The deterministic hypotheses of Erdős–Riabov Definition 2.1 for the Gaussian ring profile,
with flatness constant `C_W = 1`.
-/
theorem varianceProfile_erDefinition21 (p : Params) : ERDefinition21Profile p := by
  let _ := p.nNeZero
  refine
    { symmetric := varianceProfile_comm p
      nonnegative := varianceProfile_nonneg p
      rowStochastic := sum_varianceProfile p
      columnStochastic := ?_
      flat := ?_ }
  · intro y
    calc
      ∑ x : Site p.n p.W, varianceProfile p x y =
          ∑ x : Site p.n p.W, varianceProfile p y x := by
            apply Finset.sum_congr rfl
            intro x hx
            exact varianceProfile_comm p x y
      _ = 1 := sum_varianceProfile p y
  · intro x y
    rw [varianceProfile]
    have hW : 0 < (p.W : ℝ) := by exact_mod_cast p.W_pos
    exact (div_le_div_iff_of_pos_right hW).2 (blockWeight_le_one p x.1 y.1)

/-- The cyclic block kernel is invariant under simultaneous translation.  This is
the finite Toeplitz/circulant clause of ER Example 2.3 and is independent of whether
`n` is even or odd. -/
theorem blockWeight_add_right (p : Params) (k l t : ZMod p.n) :
    blockWeight p (k + t) (l + t) = blockWeight p k l := by
  simp only [blockWeight]
  have hdiag : l + t = k + t ↔ l = k := by
    exact add_right_cancel_iff
  have hplus : l + t = k + t + 1 ↔ l = k + 1 := by
    constructor <;> intro h
    · apply add_right_cancel (b := t)
      simpa [add_assoc, add_comm, add_left_comm] using h
    · simp [h, add_assoc, add_comm, add_left_comm]
  have hminus : l + t = k + t - 1 ↔ l = k - 1 := by
    constructor <;> intro h
    · apply add_right_cancel (b := t)
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    · simp [h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  simp only [hdiag, hplus, hminus]

/-- The cyclic block kernel is supported on the diagonal and the two
nearest-neighbour block diagonals.
-/
theorem blockWeight_support (p : Params) (k l : ZMod p.n)
    (h : blockWeight p k l ≠ 0) : l = k ∨ l = k + 1 ∨ l = k - 1 := by
  by_cases hdiag : l = k
  · exact Or.inl hdiag
  by_cases hplus : l = k + 1
  · exact Or.inr (Or.inl hplus)
  by_cases hminus : l = k - 1
  · exact Or.inr (Or.inr hminus)
  exact False.elim (h (by simp [blockWeight, hdiag, hplus, hminus]))

/-- The Gaussian ring profile has the block-band form of Erdős–Riabov Example 2.3,
for every `Params`, hence uniformly for all `n ≥ 4` and both parities.
-/
theorem varianceProfile_erBlockBand (p : Params) : ERBlockBandProfile p := by
  let _ := p.nNeZero
  refine
    { symmetric := blockWeight_comm p
      nonnegative := ?_
      stochastic := sum_blockWeight p
      translationInvariant := blockWeight_add_right p
      support := blockWeight_support p
      factorization := fun _ _ => rfl }
  intro k l
  have hc : 0 ≤ p.c := p.c_pos.le
  have hb : 0 ≤ p.b := p.b_pos.le
  unfold blockWeight
  split_ifs <;> positivity

/-- The deterministic premises of Erdős–Riabov Proposition 2.8(ii) that are stated here:
the normalized profile of Definition 2.1 and the cyclic block-band factorization of
Example 2.3.
-/
theorem erProfilePrerequisites (p : Params) :
    ERDefinition21Profile p ∧ ERBlockBandProfile p :=
  ⟨varianceProfile_erDefinition21 p, varianceProfile_erBlockBand p⟩

end GaussianRing
end ERNative.BlockBand
