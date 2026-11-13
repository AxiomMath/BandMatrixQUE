module

public import BlockBand.Palm.MomentFlow.IndBase
public import BlockBand.Palm.MomentFlow.IndFinal

/-!
# The induction on `r` and the reduction of the conditional-moments lemma to the step

If the induction step `CMWin (r - 1) → CMWin r` holds for every `r ≥ 1`, then `CMWin r M` holds
for all `r` and `M` (`cmWin_all_of_step`), and the conditional-moments lemma follows
(`conditionalMoments_of_step`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open BlockBand.Internal.Contracts.Transmission

/-- **Induction on `r`.** -/
theorem cmWin_all_of_step (hstep : ∀ r : ℕ, 1 ≤ r → (∀ M : ℝ, CMWin (r - 1) M) → ∀ M : ℝ, CMWin r M) :
    ∀ r : ℕ, ∀ M : ℝ, CMWin r M := by
  intro r
  induction r with
  | zero => exact cmWin_zero
  | succ n ih => exact hstep (n + 1) (by omega) (by simpa using ih)

/-- **Reduction of the conditional-moments lemma to the induction step.** -/
theorem conditionalMoments_of_step (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    (hstep : ∀ r : ℕ, 1 ≤ r → (∀ M : ℝ, CMWin (r - 1) M) → ∀ M : ℝ, CMWin r M) :
    BlockBand.Palm.FreshPalmAssembly.ConditionalMomentsStatement :=
  conditionalMoments_of_CM hDBM fun r _ => cmWin_all_of_step hstep r 1

end BlockBand.Palm.MomentFlow
