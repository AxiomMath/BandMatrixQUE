module

public import BlockBand.Endpoints.Response.TaggedConvexOrderCoreDefs

/-!
# The bounded-variation one-step input of the tagged convex order theorem

Law and notation as in `TaggedConvexOrderCoreDefs`: `probedClockLaw W b`, `Z_{l;k} = W⁻¹h*Y_{l;k}h`,
`tcc_psi b e W l k ψ = E ψ(Z_{l;k})`, `tcc_gen D₀ ψ = (D₀/2)X²ψ''`.

`TcoOneStepAlongBV` is the summed one-step inequality restricted to families whose coefficients
additionally have total variation `≤ A` along the summation range:
`∀ i, Σ_{k+1 ≤ l < n} |coeff_i(ψ_{l+1}) - coeff_i(ψ_l)| ≤ A`. It is weaker than
`TcoOneStepAlong` (`tcs_oneStepAlongBV_of_oneStepAlong`; the family set is smaller). With it, Abel
summation (`tcs_abel_bound`) reduces the summed remainder to fixed monomial tests, whose partial
sums telescope after the stop.

The backward family `u_{l+1}` satisfies the restriction (its coefficients are monotone in `l`;
`tcs_backward_family_bv`), so the comparison follows from the variant
(`tcoTagComparisonCoreFixed_of_BV`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks

/-- `TcoOneStepAlong` with the extra hypothesis on the test family that each coefficient has total
variation at most `A` along the summation range `k+1 ≤ l < n`: for every `M`, `A`, `δ > 0`,
eventually in `j`: for every family `(ψ_l)` of polynomials convex on `[0,∞)` with `deg ψ_l ≤ M`,
`|coeff_i ψ_l| ≤ A` and `Σ_{k+1≤l<n} |coeff_i ψ_{l+1} - coeff_i ψ_l| ≤ A` for every `i`,
`Σ_{k+1 ≤ l < n} [E Ψ_{ψ_l}(Q_{l+1}) - E Ψ_{ψ_l}(Q_l) - W⁻¹ E Ψ_{(D₀/2)x²ψ_l''}(Q_l)] ≤ δ`,
with `D₀ = D₀(E)` at the base energy. Weaker than `TcoOneStepAlong`
(`tcs_oneStepAlongBV_of_oneStepAlong`). -/
def TcoOneStepAlongBV (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) : Prop :=
  ∀ (M : ℕ) (A δ : ℝ), 0 < δ → ∀ᶠ j in atTop, ∀ ψ : ℕ → ℝ[X],
    (∀ l, ConvexOn ℝ (Set.Ici 0) (fun x => (ψ l).eval x)) → (∀ l, (ψ l).natDegree ≤ M) →
    (∀ l i, |(ψ l).coeff i| ≤ A) →
    (∀ i, ∑ l ∈ Finset.Ico (σ.k j + 1) (σ.n j), |(ψ (l + 1)).coeff i - (ψ l).coeff i| ≤ A) →
    ∑ l ∈ Finset.Ico (σ.k j + 1) (σ.n j),
      (tcc_psi b (σ.energy j) (σ.W j) (l + 1) (σ.k j) (ψ l) -
        tcc_psi b (σ.energy j) (σ.W j) l (σ.k j) (ψ l) -
        (σ.W j : ℝ)⁻¹ * tcc_psi b (σ.energy j) (σ.W j) l (σ.k j)
          (tcc_gen (transportD0 b E) (ψ l))) ≤ δ

/-- `TcoOneStepAlongBV` along every tagged sequence at the constant energy `E` (fixed
`0 < b < 1/2`, bulk `E`, `s > 0`). Weaker than `TcoOneStepCoreFixed`
(`tcs_oneStepCoreFixedBV_of_oneStepCoreFixed`). -/
def TcoOneStepCoreFixedBV : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ : ℝ, 0 < s →
    ∀ σ : TcoTagSequence s τ E, (∀ j, σ.energy j = E) → TcoOneStepAlongBV b σ

/-- The bounded-variation reading is implied by the original one (it tests fewer families). -/
theorem tcs_oneStepAlongBV_of_oneStepAlong {b : ℝ} {s τ E : ℝ} {σ : TcoTagSequence s τ E}
    (h : TcoOneStepAlong b σ) : TcoOneStepAlongBV b σ := by
  intro M A δ hδ
  filter_upwards [h M A δ hδ] with j hj ψ h1 h2 h3 _
  exact hj ψ h1 h2 h3

theorem tcs_oneStepCoreFixedBV_of_oneStepCoreFixed (h : TcoOneStepCoreFixed) :
    TcoOneStepCoreFixedBV :=
  fun b hb hb' E hE1 hE2 s τ hs σ hσ =>
    tcs_oneStepAlongBV_of_oneStepAlong (h b hb hb' E hE1 hE2 s τ hs σ hσ)

end BlockBand.Endpoints
