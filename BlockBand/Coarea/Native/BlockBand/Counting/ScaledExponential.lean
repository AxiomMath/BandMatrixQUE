module

public import BlockBand.Coarea.Native.BlockBand.Counting.Exponential

/-!
# Exponential counts on the unfolded spectral scale

This file specializes the PSSS exponential-moment bound to the
unfolded window `[-R,R]`, whose physical preimage has radius `R / (L ρ)`.
The only size hypothesis is `dimension ≤ L`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory

universe u

/-- Count in the physical interval corresponding to the unfolded spectral
window `[-R,R]` centered at energy `e`, with unfolding slope `Lρ`. -/
def BlockGUE.unfoldedIntervalCount
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ R : ℝ) (ω : M.Ω) : ℕ :=
  BlockGUE.intervalCount M A₀
    (Set.Icc (e - R / (L * ρ)) (e + R / (L * ρ))) ω

/-- The exponential count estimate on the unfolded scale, conditional on the
PSSS factorial-moment input.  The constant `𝕂` is `input.C / ρ`; the bound is independent of `L`, the block sizes, and the
deterministic Hermitian deformation. -/
theorem psss_unfoldedCountExponential
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ R t : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hdim : (Fintype.card (BlockGUE.Index d) : ℝ) ≤ L)
    (ht : 0 ≤ t) :
    ∫ ω, Real.exp
        (t * (BlockGUE.unfoldedIntervalCount M A₀ e L ρ R ω : ℝ)) ∂M.P ≤
      Real.exp (2 * R * (input.C / ρ) * (Real.exp t - 1)) := by
  let a : ℝ := e - R / (L * ρ)
  let b : ℝ := e + R / (L * ρ)
  have hLρ : 0 < L * ρ := mul_pos hL hρ
  have hab : a ≤ b := by
    dsimp [a, b]
    have : 0 ≤ R / (L * ρ) := div_nonneg hR hLρ.le
    linarith
  have hbase := psss_countExponential input hd M A₀ a b t hab ht
  change (∫ ω, Real.exp
      (t * (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)) ∂M.P) ≤ _
  calc
    (∫ ω, Real.exp
        (t * (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)) ∂M.P) ≤
      Real.exp
        ((input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) *
          (Real.exp t - 1)) := hbase
    _ ≤ Real.exp (2 * R * (input.C / ρ) * (Real.exp t - 1)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _
        (sub_nonneg.mpr (Real.one_le_exp ht))
      have hCdim :
          input.C * (Fintype.card (BlockGUE.Index d) : ℝ) ≤
            input.C * L :=
        mul_le_mul_of_nonneg_left hdim input.C_nonneg
      have hwidth : b - a = 2 * R / (L * ρ) := by
        dsimp [a, b]
        ring
      rw [hwidth]
      calc
        input.C * (Fintype.card (BlockGUE.Index d) : ℝ) *
            (2 * R / (L * ρ)) ≤
          (input.C * L) * (2 * R / (L * ρ)) := by
            exact mul_le_mul_of_nonneg_right hCdim
              (div_nonneg (mul_nonneg (by norm_num) hR) hLρ.le)
        _ = 2 * R * (input.C / ρ) := by
          field_simp

end CoareaNative.BlockBand
