module

public import BlockBand.SourceProcess.PhysApprox.B3BoundCovErr
public import BlockBand.SourceProcess.PhysApprox.B3CovLayer
public import BlockBand.SourceProcess.PhysApprox.B3CovRepGram
public import BlockBand.SourceProcess.PhysApprox.B3CovRepKBound
public import BlockBand.SourceProcess.PhysApprox.B3CovRepCurrent
public import BlockBand.SourceProcess.PhysApprox.B3CovRepDecay

/-!
# The covariance hypotheses at fixed `N = 2`

As stated, `CovLayerHyp`, `CovLayerHypGram`, `CovLayerHypK`, `CovLayerHypKK`, `CovLayerHypKG`
and `ConjLayerHyp` have the shape `C e|Z| + C(W^{-3/2} + e² + e^N)` with an existential `N`, and
`CovErrMoments` asks `‖1_A e^n‖₄ ≤ (C_n/W)^n` for every `n`: jet moments of every order. Here:

* **Fixed-`N` hypotheses** (`N = 2`): `CovLayerHyp2`, `ConjLayerHyp2`, `CovLayerHypGram2`,
  `CovLayerHypK2`, `CovLayerHypKK2`, `CovLayerHypKG2`. The pointwise shape is `CovLayerAt … C 2`
  (resp. `ConjLayerAt … C 2`), i.e. `C e|Z| + C(W^{-3/2} + e² + e²)`.
* **Lowering** (`cov_bound_lower`, `covLayerAt_lower`): if `0 ≤ e ≤ M` on `A`, then
  `e^N ≤ M^{N-2}e²`, so a bound with `(C, N)` gives one with `(C(1 + M^{N-2}), 2)`. With
  `covErrBdd_b3CovErr` every `∃ N` hypothesis for `b3CovErr` implies its fixed-`N` form:
  `covLayerHyp2_of_bdd`, …, **`covLayerHypKG2_of_bdd`** (the mixed pairs).
* **Fixed-`N` proofs**: `covLayerHypKK2_holds`,
  `conjLayerHyp2_holds`, `covLayerHypGram2_of_chain`, the assemblies `covLayerHypK2_of_parts`,
  `covLayerHyp2_of_gramK`, `covLayerHypK2_of_mixed`, `covLayerHyp2_of_chain`.
* **Moments at `p = 4` only** (`CovErrMoments2 e`): `‖1_A e‖₄ ≤ C/W`. At `N = 2` this is all the
  lift uses: the `e|Z|` term is Hölder `(4, 4)`, and the remainder `e² + e²` is used through
  `‖1_A e²‖₂ = ‖1_A e‖₄²` (`eLpNorm_sq_two_le`); the output is `L¹`
  (`cov_lift_lintegral_le2`). `CovErrMoments e ⇒ CovErrMoments2 e` (`n = 1`).
* **Consumer bridges at `N = 2`**: `covStepBracketAll_of_layer2`, `kStepConj_of_layer2`,
  `kStepBracket_of_layer2`, `gramSumStepBracket_of_layer2`, the targets `kStepCov_of_layer2`,
  `kStepConjCov_of_layer2`, `gramSumStepCov_of_layer2`, `complexClosedSummed_of_layer2`, and the
  chain version `complexClosedSummed_of_chain2` (inputs: `CovLayerHypKG2`,
  `CovErrMoments2 b3CovErr`;
  `ConjLayerHyp2` and the `𝒦𝒦` pairs are proved from the contract hypotheses).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## The conjugate pointwise shape
-/

/-- The pointwise `LayerCov` shape of the raw closed conjugate bracket of `(ij, kl)` with `(C, N)`
(the body of `ConjLayerHyp`). -/
def ConjLayerAt (e Z : CovField) (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (s h R : ℝ) {K W : ℕ}
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (j : ℕ) (C : ℝ) (N : ℕ)
    (ij kl : Fin np × Fin np) : Prop :=
  ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
    ‖(closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
        b3dX b E s h τ m W j Vs (Sum.inr ij : CIdx K np) y *
          conj (b3dX b E s h τ m W j Vs (Sum.inr kl : CIdx K np) y)) |
        b3Sigma W j np] y -
      (W : ℂ)⁻¹ * kConjCov b E ij kl (b3ClosedGramAt b E s h τ m W j Vs y)‖ ≤
    C * (e b E np τ m s h K W Vs j y * ‖Z b E np τ m s h K W Vs j y‖) +
      C * ((W : ℝ)⁻¹ / Real.sqrt W + e b E np τ m s h K W Vs j y ^ 2 +
        e b E np τ m s h K W Vs j y ^ N)

theorem conjLayerHyp_iff (e Z : CovField) :
    ConjLayerHyp e Z ↔ ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ 2 ≤ N ∧
      ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij kl : Fin np × Fin np,
        ConjLayerAt e Z b E τ m s h R (Vs W) j C N ij kl := Iff.rfl

/-!
## The fixed-`N` hypotheses
-/

/-- **`CovLayerHyp` at `N = 2`**: all coordinate pairs, shape `C e|Z| + C(W^{-3/2} + e² + e²)`. -/
def CovLayerHyp2 (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c c' : CIdx K np,
      CovLayerAt e Z b E τ m s h R (Vs W) j C 2 c c'

/-- **`ConjLayerHyp` at `N = 2`.** -/
def ConjLayerHyp2 (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij kl : Fin np × Fin np,
      ConjLayerAt e Z b E τ m s h R (Vs W) j C 2 ij kl

/-- **`CovLayerHypGram` at `N = 2`** (the Gram pairs). -/
def CovLayerHypGram2 (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ g g' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
        CovLayerAt e Z b E τ m s h R (Vs W) j C 2 (Sum.inl g) (Sum.inl g')

/-- **`CovLayerHypK` at `N = 2`** (the pairs with a `𝒦` coordinate). -/
def CovLayerHypK2 (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c c' : CIdx K np,
      ((∃ ij, c = Sum.inr ij) ∨ (∃ ij, c' = Sum.inr ij)) →
        CovLayerAt e Z b E τ m s h R (Vs W) j C 2 c c'

/-- **`CovLayerHypKK` at `N = 2`** (the `𝒦𝒦` pairs). -/
def CovLayerHypKK2 (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij kl : Fin np × Fin np,
      CovLayerAt e Z b E τ m s h R (Vs W) j C 2 (Sum.inr ij) (Sum.inr kl)

/-- **`CovLayerHypKG` at `N = 2`** (the mixed `(𝒦, Gram)` pairs, both orders). -/
def CovLayerHypKG2 (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ (ij : Fin np × Fin np) (g : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
        CovLayerAt e Z b E τ m s h R (Vs W) j C 2 (Sum.inr ij) (Sum.inl g) ∧
        CovLayerAt e Z b E τ m s h R (Vs W) j C 2 (Sum.inl g) (Sum.inr ij)

/-!
## Fixed `N` is a special case of `∃ N`
-/

theorem covLayerHyp_of_two {e Z : CovField} (h : CovLayerHyp2 e Z) : CovLayerHyp e Z := by
  intro b E np τ m T s h' K Vs hFD R
  obtain ⟨C, hC, hev⟩ := h b E np τ m T s h' K Vs hFD R
  exact ⟨C, 2, hC, le_rfl, hev⟩

theorem conjLayerHyp_of_two {e Z : CovField} (h : ConjLayerHyp2 e Z) : ConjLayerHyp e Z := by
  intro b E np τ m T s h' K Vs hFD R
  obtain ⟨C, hC, hev⟩ := h b E np τ m T s h' K Vs hFD R
  exact ⟨C, 2, hC, le_rfl, hev⟩

theorem covLayerHypKG_of_two {e Z : CovField} (h : CovLayerHypKG2 e Z) : CovLayerHypKG e Z := by
  intro b E np τ m T s h' K Vs hFD R
  obtain ⟨C, hC, hev⟩ := h b E np τ m T s h' K Vs hFD R
  exact ⟨C, 2, hC, le_rfl, hev⟩

/-!
## Lowering `N` with `0 ≤ e ≤ M`
-/

/-- **`e^N ≤ M^{N-2}e²`**: a `(C, N)` bound gives a `(C(1 + M^{N-2}), 2)` bound. -/
theorem cov_bound_lower {C ev zv w M : ℝ} {N : ℕ} (hC : 0 ≤ C) (hev : 0 ≤ ev) (hM : ev ≤ M)
    (hzv : 0 ≤ zv) (hw : 0 ≤ w) (hN : 2 ≤ N) {x : ℝ}
    (hx : x ≤ C * (ev * zv) + C * (w + ev ^ 2 + ev ^ N)) :
    x ≤ C * (1 + M ^ (N - 2)) * (ev * zv) + C * (1 + M ^ (N - 2)) * (w + ev ^ 2 + ev ^ 2) := by
  have hM0 : 0 ≤ M := hev.trans hM
  set P := M ^ (N - 2) with hP
  have hP0 : 0 ≤ P := pow_nonneg hM0 _
  have hpow : ev ^ N ≤ P * ev ^ 2 := by
    have e1 : ev ^ N = ev ^ (N - 2) * ev ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hN]
    rw [e1]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hev hM _) (sq_nonneg ev)
  have hez : 0 ≤ ev * zv := mul_nonneg hev hzv
  have h1 : C * (1 + P) * (ev * zv) = C * (ev * zv) + C * P * (ev * zv) := by ring
  have h1' : 0 ≤ C * P * (ev * zv) := mul_nonneg (mul_nonneg hC hP0) hez
  have h3 : w + ev ^ 2 + ev ^ N ≤ (1 + P) * (w + ev ^ 2 + ev ^ 2) := by
    have e2 : (1 + P) * (w + ev ^ 2 + ev ^ 2) =
        w + ev ^ 2 + P * ev ^ 2 + (ev ^ 2 + P * w + P * ev ^ 2) := by ring
    have : 0 ≤ ev ^ 2 + P * w + P * ev ^ 2 := by positivity
    rw [e2]
    linarith
  have h2 : C * (w + ev ^ 2 + ev ^ N) ≤ C * (1 + P) * (w + ev ^ 2 + ev ^ 2) := by
    calc C * (w + ev ^ 2 + ev ^ N) ≤ C * ((1 + P) * (w + ev ^ 2 + ev ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 hC
      _ = C * (1 + P) * (w + ev ^ 2 + ev ^ 2) := by ring
  linarith

/-- **Lowering `CovLayerAt` to `N = 2`** under `0 ≤ e ≤ M` on the alive set. -/
theorem covLayerAt_lower {e Z : CovField} {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {s h R : ℝ}
    {K W : ℕ} {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {j : ℕ}
    {C M : ℝ} {N : ℕ} {c c' : CIdx K np} (hC : 0 ≤ C) (hN : 2 ≤ N)
    (hB : ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
      0 ≤ e b E np τ m s h K W Vs j y ∧ e b E np τ m s h K W Vs j y ≤ M)
    (hL : CovLayerAt e Z b E τ m s h R Vs j C N c c') :
    CovLayerAt e Z b E τ m s h R Vs j (C * (1 + M ^ (N - 2))) 2 c c' := by
  filter_upwards [hL, hB] with y hy hyB hyA
  exact cov_bound_lower hC (hyB hyA).1 (hyB hyA).2 (norm_nonneg _) (by positivity) hN (hy hyA)

/-- **Lowering `ConjLayerAt` to `N = 2`** under `0 ≤ e ≤ M` on the alive set. -/
theorem conjLayerAt_lower {e Z : CovField} {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {s h R : ℝ}
    {K W : ℕ} {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {j : ℕ}
    {C M : ℝ} {N : ℕ} {ij kl : Fin np × Fin np} (hC : 0 ≤ C) (hN : 2 ≤ N)
    (hB : ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
      0 ≤ e b E np τ m s h K W Vs j y ∧ e b E np τ m s h K W Vs j y ≤ M)
    (hL : ConjLayerAt e Z b E τ m s h R Vs j C N ij kl) :
    ConjLayerAt e Z b E τ m s h R Vs j (C * (1 + M ^ (N - 2))) 2 ij kl := by
  filter_upwards [hL, hB] with y hy hyB hyA
  exact cov_bound_lower hC (hyB hyA).1 (hyB hyA).2 (norm_nonneg _) (by positivity) hN (hy hyA)

/-- **`CovLayerHyp + (0 ≤ e ≤ M) ⇒ CovLayerHyp2`.** -/
theorem covLayerHyp2_of_bdd {e Z : CovField} (hL : CovLayerHyp e Z) (hB : CovErrBdd e) :
    CovLayerHyp2 e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C, N, hC, hN, hev⟩ := (covLayerHyp_iff e Z).1 hL b E np τ m T s h K Vs hFD R
  obtain ⟨M, hM, hevB⟩ := hB b E np τ m T s h K Vs hFD
  refine ⟨C * (1 + M ^ (N - 2)), by positivity, ?_⟩
  filter_upwards [hev, hevB R] with W hW hWB j hj c c'
  exact covLayerAt_lower hC hN (hWB j hj) (hW j hj c c')

/-- **`ConjLayerHyp + (0 ≤ e ≤ M) ⇒ ConjLayerHyp2`.** -/
theorem conjLayerHyp2_of_bdd {e Z : CovField} (hL : ConjLayerHyp e Z) (hB : CovErrBdd e) :
    ConjLayerHyp2 e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C, N, hC, hN, hev⟩ := (conjLayerHyp_iff e Z).1 hL b E np τ m T s h K Vs hFD R
  obtain ⟨M, hM, hevB⟩ := hB b E np τ m T s h K Vs hFD
  refine ⟨C * (1 + M ^ (N - 2)), by positivity, ?_⟩
  filter_upwards [hev, hevB R] with W hW hWB j hj ij kl
  exact conjLayerAt_lower hC hN (hWB j hj) (hW j hj ij kl)

/-- **`CovLayerHypGram + (0 ≤ e ≤ M) ⇒ CovLayerHypGram2`.** -/
theorem covLayerHypGram2_of_bdd {e Z : CovField} (hL : CovLayerHypGram e Z) (hB : CovErrBdd e) :
    CovLayerHypGram2 e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C, N, hC, hN, hev⟩ := hL b E np τ m T s h K Vs hFD R
  obtain ⟨M, hM, hevB⟩ := hB b E np τ m T s h K Vs hFD
  refine ⟨C * (1 + M ^ (N - 2)), by positivity, ?_⟩
  filter_upwards [hev, hevB R] with W hW hWB j hj g g'
  exact covLayerAt_lower hC hN (hWB j hj) (hW j hj g g')

/-- **`CovLayerHypK + (0 ≤ e ≤ M) ⇒ CovLayerHypK2`.** -/
theorem covLayerHypK2_of_bdd {e Z : CovField} (hL : CovLayerHypK e Z) (hB : CovErrBdd e) :
    CovLayerHypK2 e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C, N, hC, hN, hev⟩ := hL b E np τ m T s h K Vs hFD R
  obtain ⟨M, hM, hevB⟩ := hB b E np τ m T s h K Vs hFD
  refine ⟨C * (1 + M ^ (N - 2)), by positivity, ?_⟩
  filter_upwards [hev, hevB R] with W hW hWB j hj c c' hc
  exact covLayerAt_lower hC hN (hWB j hj) (hW j hj c c' hc)

/-- **`CovLayerHypKK + (0 ≤ e ≤ M) ⇒ CovLayerHypKK2`.** -/
theorem covLayerHypKK2_of_bdd {e Z : CovField} (hL : CovLayerHypKK e Z) (hB : CovErrBdd e) :
    CovLayerHypKK2 e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C, N, hC, hN, hev⟩ := hL b E np τ m T s h K Vs hFD R
  obtain ⟨M, hM, hevB⟩ := hB b E np τ m T s h K Vs hFD
  refine ⟨C * (1 + M ^ (N - 2)), by positivity, ?_⟩
  filter_upwards [hev, hevB R] with W hW hWB j hj ij kl
  exact covLayerAt_lower hC hN (hWB j hj) (hW j hj ij kl)

/-- **`CovLayerHypKG + (0 ≤ e ≤ M) ⇒ CovLayerHypKG2`** (the mixed pairs, any `N`). -/
theorem covLayerHypKG2_of_bdd {e Z : CovField} (hL : CovLayerHypKG e Z) (hB : CovErrBdd e) :
    CovLayerHypKG2 e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C, N, hC, hN, hev⟩ := hL b E np τ m T s h K Vs hFD R
  obtain ⟨M, hM, hevB⟩ := hB b E np τ m T s h K Vs hFD
  refine ⟨C * (1 + M ^ (N - 2)), by positivity, ?_⟩
  filter_upwards [hev, hevB R] with W hW hWB j hj ij g
  exact ⟨covLayerAt_lower hC hN (hWB j hj) (hW j hj ij g).1,
    covLayerAt_lower hC hN (hWB j hj) (hW j hj ij g).2⟩

/-!
## The fixed-`N` proofs for `b3CovErr`, `b3CovZ`
-/

/-- **`CovLayerHypKK2 b3CovErr b3CovZ`** from the input hypotheses. -/
theorem covLayerHypKK2_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    CovLayerHypKK2 b3CovErr b3CovZ :=
  covLayerHypKK2_of_bdd (covLayerHypKK_holds hGA hLp) covErrBdd_b3CovErr

/-- **`ConjLayerHyp2 b3CovErr b3CovZ`** from the input hypotheses. -/
theorem conjLayerHyp2_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) : ConjLayerHyp2 b3CovErr b3CovZ :=
  conjLayerHyp2_of_bdd (conjLayerHyp_holds hGA hLp hP) covErrBdd_b3CovErr

/-- **`CovLayerHypGram2 b3CovErr b3CovZ`** from the input hypotheses and the closed chain
`B3ClosedChainPin` (the `N = 6` bound, lowered with `e⁶ ≤ M⁴e²`).
-/
theorem covLayerHypGram2_of_chain (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hCh : B3ClosedChainPin) : CovLayerHypGram2 b3CovErr b3CovZ :=
  covLayerHypGram2_of_bdd (covLayerHypGram_of_chain hGA hLp hP hCh) covErrBdd_b3CovErr

/-- **`CovLayerHypK2` from its `𝒦𝒦` and mixed parts** (fixed `N = 2`). -/
theorem covLayerHypK2_of_parts {e Z : CovField} (hKK : CovLayerHypKK2 e Z)
    (hKG : CovLayerHypKG2 e Z) (hnn : CovErrNonneg e) : CovLayerHypK2 e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C₁, hC₁, hev₁⟩ := hKK b E np τ m T s h K Vs hFD R
  obtain ⟨C₂, hC₂, hev₂⟩ := hKG b E np τ m T s h K Vs hFD R
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  filter_upwards [hev₁, hev₂, hnn b E np τ m T s h K Vs hFD R] with W hW₁ hW₂ hWn j hj c c' hc
  have hw : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by positivity
  have key : ∀ {C₀ : ℝ}, 0 ≤ C₀ → C₀ ≤ C₁ + C₂ →
      CovLayerAt e Z b E τ m s h R (Vs W) j C₀ 2 c c' →
      CovLayerAt e Z b E τ m s h R (Vs W) j (2 * (C₁ + C₂)) 2 c c' := by
    intro C₀ h0 hle hb
    filter_upwards [hb, hWn j hj] with y hy hy0 hyA
    exact cov_bound_weaken h0 hle (hy0 hyA) (norm_nonneg _) hw le_rfl le_rfl (hy hyA)
  rcases c with g | ij
  · rcases hc with ⟨ij, hij⟩ | ⟨kl, hkl⟩
    · exact absurd hij (by simp)
    · subst hkl
      exact key hC₂ (by linarith) (hW₂ j hj kl g).2
  · rcases c' with g | kl
    · exact key hC₂ (by linarith) (hW₂ j hj ij g).1
    · exact key hC₁ (by linarith) (hW₁ j hj ij kl)

/-- **`CovLayerHypGram2 + CovLayerHypK2 + (e ≥ 0) ⇒ CovLayerHyp2`.** -/
theorem covLayerHyp2_of_gramK {e Z : CovField} (hG : CovLayerHypGram2 e Z)
    (hK : CovLayerHypK2 e Z) (hnn : CovErrNonneg e) : CovLayerHyp2 e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨CG, hCG, hevG⟩ := hG b E np τ m T s h K Vs hFD R
  obtain ⟨CK, hCK, hevK⟩ := hK b E np τ m T s h K Vs hFD R
  refine ⟨2 * (CG + CK), by positivity, ?_⟩
  filter_upwards [hevG, hevK, hnn b E np τ m T s h K Vs hFD R] with W hWG hWK hWn j hj c c'
  have hw : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by positivity
  have hKc : ((∃ ij, c = Sum.inr ij) ∨ (∃ ij, c' = Sum.inr ij)) →
      CovLayerAt e Z b E τ m s h R (Vs W) j (2 * (CG + CK)) 2 c c' := by
    intro hc
    filter_upwards [hWK j hj c c' hc, hWn j hj] with y hy hy0 hyA
    exact cov_bound_weaken hCK (by linarith) (hy0 hyA) (norm_nonneg _) hw le_rfl le_rfl
      (hy hyA)
  rcases c with g | ij
  · rcases c' with g' | kl
    · filter_upwards [hWG j hj g g', hWn j hj] with y hy hy0 hyA
      exact cov_bound_weaken hCG (by linarith) (hy0 hyA) (norm_nonneg _) hw le_rfl le_rfl
        (hy hyA)
    · exact hKc (Or.inr ⟨kl, rfl⟩)
  · exact hKc (Or.inl ⟨ij, rfl⟩)

/-- **`CovLayerHypK2 b3CovErr b3CovZ`** from the input hypotheses and the mixed pairs at `N = 2`. -/
theorem covLayerHypK2_of_mixed (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hKG : CovLayerHypKG2 b3CovErr b3CovZ) : CovLayerHypK2 b3CovErr b3CovZ :=
  covLayerHypK2_of_parts (covLayerHypKK2_holds hGA hLp) hKG covErrNonneg_b3CovErr

/-- **`CovLayerHyp2 b3CovErr b3CovZ`** from the input hypotheses, the closed chain and the mixed
pairs at `N = 2`.
-/
theorem covLayerHyp2_of_chain (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hCh : B3ClosedChainPin) (hKG : CovLayerHypKG2 b3CovErr b3CovZ) :
    CovLayerHyp2 b3CovErr b3CovZ :=
  covLayerHyp2_of_gramK (covLayerHypGram2_of_chain hGA hLp hP hCh)
    (covLayerHypK2_of_mixed hGA hLp hKG) covErrNonneg_b3CovErr

/-!
## Moments at `p = 4`
-/

/-- **`CovErrMoments` at `N = 2`**: `‖1_{A_j} e_j‖₄ ≤ C/W`, eventually, at every no-birth step.
This is jet order `p = 4` only. -/
def CovErrMoments2 (e : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator (e b E np τ m s h K W (Vs W) j)) 4
          (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- `CovErrMoments e ⇒ CovErrMoments2 e` (the `n = 1` moment). -/
theorem covErrMoments2_of_moments {e : CovField} (h : CovErrMoments e) : CovErrMoments2 e := by
  intro b E np τ m T s h' K Vs hFD R
  obtain ⟨C, hC, hev⟩ := h b E np τ m T s h' K Vs hFD R 1 le_rfl
  exact ⟨C, hC, hev.mono fun W hW j hj => by simpa only [pow_one] using hW j hj⟩

/-!
## The lift at `N = 2`
-/

section Generic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- `‖g²‖₂ = ‖g‖₄² ≤ a²`. -/
theorem eLpNorm_sq_two_le {g : Ω → ℝ} (hg : AEStronglyMeasurable g μ) {a : ℝ} (ha : 0 ≤ a)
    (h : eLpNorm g 4 μ ≤ ENNReal.ofReal a) :
    eLpNorm (fun y => g y ^ 2) 2 μ ≤ ENNReal.ofReal (a ^ 2) := by
  have hfun : (fun y => ‖g y‖ ^ ((2 : ℕ) : ℝ)) = fun y => ‖g y‖ ^ 2 :=
    funext fun y => Real.rpow_natCast _ _
  have hcongr : eLpNorm (fun y => g y ^ 2) 2 μ =
      eLpNorm (fun y => ‖g y‖ ^ ((2 : ℕ) : ℝ)) 2 μ := by
    rw [hfun]
    refine eLpNorm_congr_norm_ae (hg.pow 2) (hg.norm.pow 2) (ae_of_all _ fun y => ?_)
    rw [norm_pow, norm_pow, norm_norm]
  have h4 : (2 : ℝ≥0∞) * ENNReal.ofReal ((2 : ℕ) : ℝ) = 4 := by
    rw [Nat.cast_ofNat, ENNReal.ofReal_ofNat]; norm_num
  rw [hcongr, eLpNorm_norm_rpow g hg (by norm_num : (0 : ℝ) < ((2 : ℕ) : ℝ)), h4]
  calc eLpNorm g 4 μ ^ ((2 : ℕ) : ℝ) ≤ ENNReal.ofReal a ^ ((2 : ℕ) : ℝ) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal (a ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg ha (by positivity), Real.rpow_natCast]

/-- **The lifted `LayerCov` shape at `N = 2`, from `‖1_A e‖₄` only.** If on `A` the error is at
most `C₁ e|Z| + C₁(c + e² + e²)`, `‖1_A e‖₄ ≤ a₄` and `‖1_A Z‖₄ ≤ z`, then
`E|1_A f| ≤ C₁ a₄ z + C₁(c + a₄² + a₄²)`. -/
theorem cov_lift_lintegral_le2 (A : Set Ω) (f : Ω → ℂ) (e Z : Ω → ℝ)
    {C₁ a₄ z c : ℝ} (hC₁ : 0 ≤ C₁) (ha₄ : 0 ≤ a₄) (hz : 0 ≤ z) (hc : 0 ≤ c)
    (hpt : ∀ᵐ y ∂μ, y ∈ A → ‖f y‖ ≤ C₁ * (e y * ‖Z y‖) + C₁ * (c + e y ^ 2 + e y ^ 2))
    (h4 : eLpNorm (A.indicator e) 4 μ ≤ ENNReal.ofReal a₄)
    (hZ : eLpNorm (A.indicator Z) 4 μ ≤ ENNReal.ofReal z) :
    ∫⁻ y, ‖A.indicator f y‖ₑ ∂μ ≤
      ENNReal.ofReal (C₁ * (a₄ * z) + C₁ * (c + a₄ ^ 2 + a₄ ^ 2)) := by
  have hem : AEStronglyMeasurable (A.indicator e) μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (h4.trans_lt ENNReal.ofReal_lt_top).ne
  have h2' : eLpNorm (fun y => A.indicator e y ^ 2) 2 μ ≤ ENNReal.ofReal (a₄ ^ 2) :=
    eLpNorm_sq_two_le hem ha₄ h4
  have hZA : AEStronglyMeasurable (A.indicator Z) μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (hZ.trans_lt ENNReal.ofReal_lt_top).ne
  let Zc : Unit → Ω → ℂ := fun _ y => ((A.indicator Z y : ℝ) : ℂ)
  have hZcm : ∀ i, AEStronglyMeasurable (Zc i) μ := fun _ =>
    Complex.continuous_ofReal.comp_aestronglyMeasurable hZA
  have hZc : ∀ i ∈ [()], eLpNorm (Set.univ.indicator (Zc i)) 4 μ ≤ ENNReal.ofReal z := by
    intro i _
    rw [Set.indicator_univ]
    refine le_trans (le_of_eq ?_) hZ
    refine eLpNorm_congr_enorm_ae (hZcm i) hZA (Eventually.of_forall fun y => ?_)
    show ‖((A.indicator Z y : ℝ) : ℂ)‖ₑ = ‖A.indicator Z y‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  have hL := BlockBand.SourceProcess.ContractingWords.eLpNorm_lifted_le [()] Zc Set.univ
    MeasurableSet.univ (A.indicator e) hem hZcm 2 hC₁ ha₄ hz hc (a₂ := a₄ ^ 2)
    (aN := a₄ ^ 2) (by positivity) (by positivity) h4 h2' h2' hZc
  have hg : (fun y => C₁ * ([()].map fun i => A.indicator e y *
      ‖Set.univ.indicator (Zc i) y‖).sum + C₁ * (c + A.indicator e y ^ 2 + A.indicator e y ^ 2)) =
      fun y => C₁ * (A.indicator e y * ‖A.indicator Z y‖) +
        C₁ * (c + A.indicator e y ^ 2 + A.indicator e y ^ 2) := by
    funext y
    simp [Zc, Complex.norm_real]
  rw [hg] at hL
  simp only [List.length_singleton, Nat.cast_one, one_mul] at hL
  calc ∫⁻ y, ‖A.indicator f y‖ₑ ∂μ ≤ ∫⁻ y, ‖C₁ * (A.indicator e y * ‖A.indicator Z y‖) +
        C₁ * (c + A.indicator e y ^ 2 + A.indicator e y ^ 2)‖ₑ ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpt] with y hy
        by_cases hyA : y ∈ A
        · rw [Set.indicator_of_mem hyA, ← ofReal_norm, ← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ((hy hyA).trans
            (le_of_eq_of_le ?_ (Real.le_norm_self _)))
          simp only [Set.indicator_of_mem hyA]
        · simp [Set.indicator_of_notMem hyA]
    _ ≤ eLpNorm (fun y => C₁ * (A.indicator e y * ‖A.indicator Z y‖) +
          C₁ * (c + A.indicator e y ^ 2 + A.indicator e y ^ 2)) 1 μ :=
        lintegral_enorm_le_eLpNorm_one
    _ ≤ eLpNorm (fun y => C₁ * (A.indicator e y * ‖A.indicator Z y‖) +
          C₁ * (c + A.indicator e y ^ 2 + A.indicator e y ^ 2)) 2 μ :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    _ ≤ _ := hL

end Generic

/-!
## The consumer bridges at `N = 2`
-/

/-- **`CovLayerHyp2 + CovErrMoments2 + CovDecayHyp ⇒ CovStepBracketAll`.** -/
theorem covStepBracketAll_of_layer2 {e Z : CovField} (hL : CovLayerHyp2 e Z)
    (hE : CovErrMoments2 e) (hD : CovDecayHyp Z) : CovStepBracketAll := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C₁, hC₁, hevL⟩ := hL b E np τ m T s h K Vs hFD R
  obtain ⟨Ce, hCe, hev1⟩ := hE b E np τ m T s h K Vs hFD R
  obtain ⟨Cz, ρ, hCz, hρ0, hρ1, hevZ⟩ := hD b E np τ m T s h K Vs hFD R
  refine ⟨C₁ * 1 * Ce * Cz + C₁ * (1 + Ce ^ 2 + Ce ^ 2), ρ, by positivity, hρ0, hρ1, ?_⟩
  filter_upwards [hevL, hev1, hevZ, eventually_ge_atTop 1]
    with W hWL hW1' hWZ hW1 j hj c c'
  have hr := genStepRate_nonneg hρ0 s τ W j
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hlift := cov_lift_lintegral_le2 (μ := closedLaw b W np)
    (b3Alive b E s h τ m R W j (Vs W)) _ (e b E np τ m s h K W (Vs W) j)
    (Z b E np τ m s h K W (Vs W) j) hC₁ (a₄ := Ce / W)
    (z := Cz * (genStepRate ρ s τ W j + 1 / Real.sqrt W))
    (c := (W : ℝ)⁻¹ / Real.sqrt W) (by positivity) (by positivity) (by positivity)
    (hWL j hj c c') (hW1' j hj) (hWZ j hj)
  unfold genBrStep
  exact cov_step_of_parts hW1 le_rfl hC₁ hr hCe hlift

/-- **`ConjLayerHyp2 + CovErrMoments2 + CovDecayHyp ⇒ KStepConj`.** -/
theorem kStepConj_of_layer2 {e Z : CovField} (hL : ConjLayerHyp2 e Z)
    (hE : CovErrMoments2 e) (hD : CovDecayHyp Z) : KStepConj := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C₁, hC₁, hevL⟩ := hL b E np τ m T s h K Vs hFD R
  obtain ⟨Ce, hCe, hev1⟩ := hE b E np τ m T s h K Vs hFD R
  obtain ⟨Cz, ρ, hCz, hρ0, hρ1, hevZ⟩ := hD b E np τ m T s h K Vs hFD R
  refine ⟨C₁ * 1 * Ce * Cz + C₁ * (1 + Ce ^ 2 + Ce ^ 2), ρ, by positivity, hρ0, hρ1, ?_⟩
  filter_upwards [hevL, hev1, hevZ, eventually_ge_atTop 1]
    with W hWL hW1' hWZ hW1 j hj ij kl
  have hr := genStepRate_nonneg hρ0 s τ W j
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hlift := cov_lift_lintegral_le2 (μ := closedLaw b W np)
    (b3Alive b E s h τ m R W j (Vs W)) _ (e b E np τ m s h K W (Vs W) j)
    (Z b E np τ m s h K W (Vs W) j) hC₁ (a₄ := Ce / W)
    (z := Cz * (genStepRate ρ s τ W j + 1 / Real.sqrt W))
    (c := (W : ℝ)⁻¹ / Real.sqrt W) (by positivity) (by positivity) (by positivity)
    (hWL j hj ij kl) (hW1' j hj) (hWZ j hj)
  unfold genConjStep
  exact cov_step_of_parts hW1 le_rfl hC₁ hr hCe hlift

/-- **`KStepBracket` at `N = 2`.** -/
theorem kStepBracket_of_layer2 {e Z : CovField} (hL : CovLayerHyp2 e Z)
    (hE : CovErrMoments2 e) (hD : CovDecayHyp Z) : KStepBracket :=
  kStepBracket_of_all (covStepBracketAll_of_layer2 hL hE hD)

/-- **`GramSumStepBracket` at `N = 2`.** -/
theorem gramSumStepBracket_of_layer2 {e Z : CovField} (hL : CovLayerHyp2 e Z)
    (hE : CovErrMoments2 e) (hD : CovDecayHyp Z) : GramSumStepBracket :=
  gramSumStepBracket_of_all (covStepBracketAll_of_layer2 hL hE hD)

/-- **Target `KStepCov`** at `N = 2`. -/
theorem kStepCov_of_layer2 {e Z : CovField} (hL2 : GenStepMemL2) (hM : GenStepMeanL2)
    (hL : CovLayerHyp2 e Z) (hE : CovErrMoments2 e) (hD : CovDecayHyp Z) : KStepCov :=
  kStepCov_of_bracket hL2 hM (kStepBracket_of_layer2 hL hE hD)

/-- **Target `KStepConjCov`** at `N = 2`. -/
theorem kStepConjCov_of_layer2 {e Z : CovField} (hL2 : GenStepMemL2) (hM : GenStepMeanL2)
    (hL : ConjLayerHyp2 e Z) (hE : CovErrMoments2 e) (hD : CovDecayHyp Z) : KStepConjCov :=
  kStepConjCov_of_conj hL2 hM (kStepConj_of_layer2 hL hE hD)

/-- **Target `GramSumStepCov`** at `N = 2`. -/
theorem gramSumStepCov_of_layer2 {e Z : CovField} (hL2 : GramSumStepMemL2)
    (hM : GramSumStepMeanL2) (hL : CovLayerHyp2 e Z) (hE : CovErrMoments2 e)
    (hD : CovDecayHyp Z) : GramSumStepCov :=
  gramSumStepCov_of_bracket hL2 hM (gramSumStepBracket_of_layer2 hL hE hD)

/-- **`ComplexClosedSummed` from the layer hypotheses at `N = 2`.** -/
theorem complexClosedSummed_of_layer2 {e Z : CovField} (hGD : GramSumStepDrift)
    (hB : GenReqBirth) (hKD : KStepDrift) (hCL : CovLayerHyp2 e Z) (hCC : ConjLayerHyp2 e Z)
    (hE : CovErrMoments2 e) (hD : CovDecayHyp Z) : ComplexClosedSummed :=
  complexClosedSummed_of_gramSteps hGD (gramSumStepBracket_of_layer2 hCL hE hD) hB hKD
    (kStepBracket_of_layer2 hCL hE hD) (kStepConj_of_layer2 hCC hE hD)

/-- **`ComplexClosedSummed` through the closed chain at `N = 2`**: the inputs are the mixed
pairs `CovLayerHypKG2` and the `p = 4` moment `CovErrMoments2 b3CovErr`; the conjugate and `𝒦𝒦`
pairs are proved. -/
theorem complexClosedSummed_of_chain2 (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hGD : GramSumStepDrift)
    (hB : GenReqBirth) (hKD : KStepDrift) (hCh : B3ClosedChainPin)
    (hKG : CovLayerHypKG2 b3CovErr b3CovZ) (hE : CovErrMoments2 b3CovErr)
    (hD : B3ClosedContrDecay) : ComplexClosedSummed :=
  complexClosedSummed_of_layer2 hGD hB hKD (covLayerHyp2_of_chain hGA hLp hP hCh hKG)
    (conjLayerHyp2_holds hGA hLp hP) hE (covDecayHyp_b3CovZ hD)

end BlockBand.SourceProcess.PhysApprox.B3
