module

public import BlockBand.SourceProcess.ComplexConstruct.BornNoise
public import BlockBand.SourceProcess.ModelExist.TransBound
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AmbientFeasible

/-!
# The transported `𝒦` brackets are the integrands of the model clauses

At a time `s`, with `L = bornL θ λ s` (`L𝖣Lᴴ = 𝖣'`) and an ambient frame `X` with the
two-projection constraint, the born Gram state is `G = congrGram L (gramPair P X)`. The drifts
produced by `cLocMart_tRep_mul` from the ambient brackets (`Σ_a σ_a ⊗ σ̄_a`, `Σ_a σ_a ⊗ dG_a`,
`σ_a = kNoise_a(X)`) with weights `bCoef` and indicator `1{θ_e ∨ θ_e' ≤ s}` are:
* for `𝒦𝒦`: `0` (`sum_kNoise_mul`);
* `kks_transport`: `2η²D₀ G.2_ik (C₀)_lj` (clause `antiholomorphic`);
* `kg_transport`: `-iηD₀ G.2_il (C₀)_kj` for `r = 0` and `-iηD₀ G.2_il (C₁ᴴ)_kj` for `r = 1`
  (clauses `crossM`, `crossB`).
Proof: `kNoise(XL) = Lᴴ kNoise(X) L` (`kNoise_mul`), `gramNoise(XL) = congrGram L gramNoise(X)`
(`gramNoise_mul`), `cf_bornL`, then `born_bracket_star`, `_M`, `_B` at `V = XL`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.ComplexUnique BlockBand.SourceProcess.ModelExist
open scoped NNReal

variable {ι c c' : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c] [Fintype c']

omit [DecidableEq c] in
/-- The Gram noise of a born frame is the congruent ambient Gram noise. -/
theorem gramNoise_mul (D0 : ℝ) (P : Matrix ι ι ℂ) (X : Matrix ι c' ℂ) (L : Matrix c' c ℂ)
    {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ} (hsig : L * D * Lᴴ = D') (a : SourceNoise ι) :
    gramNoise D0 P D a (X * L) = congrGram L (gramNoise D0 P D' a X) := by
  simp only [gramNoise, sourceDiffusion_mul D0 P X L hsig a, gramVariation, nearVariation,
    congrGram, conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- Products of finite double sums. -/
theorem sum_sum_mul_sum_sum {κ : Type*} [Fintype κ] (α β : c' → c' → ℂ) (u v : κ → c' → c' → ℂ) :
    ∑ a, (∑ x, ∑ x', α x x' * u a x x') * (∑ z, ∑ z', β z z' * v a z z') =
      ∑ x, ∑ x', ∑ z, ∑ z', α x x' * β z z' * ∑ a, u a x x' * v a z z' := by
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun a _ => ?_
  ring

variable {Ω : Type*} (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ) (s : ℝ≥0) (ω : Ω)

omit [Fintype c] [DecidableEq c] [Fintype c'] in
theorem ite_mul_ite (e e' : Fin 2 × c × c) (a b : ℂ) :
    (if bTime θ e ω ≤ s then a else 0) * (if bTime θ e' ω ≤ s then b else 0) =
      if max (bTime θ e ω) (bTime θ e' ω) ≤ s then a * b else 0 := by
  by_cases h1 : bTime θ e ω ≤ s <;> by_cases h2 : bTime θ e' ω ≤ s
  · have h3 : max (bTime θ e ω) (bTime θ e' ω) ≤ s := max_le h1 h2
    simp only [h1, h2, h3, ite_true]
  · have h3 : ¬ max (bTime θ e ω) (bTime θ e' ω) ≤ s := fun h => h2 ((le_max_right _ _).trans h)
    simp only [h1, h2, h3, ite_true, ite_false, mul_zero]
  · have h3 : ¬ max (bTime θ e ω) (bTime θ e' ω) ≤ s := fun h => h1 ((le_max_left _ _).trans h)
    simp only [h1, h3, ite_false, zero_mul]
  · have h3 : ¬ max (bTime θ e ω) (bTime θ e' ω) ≤ s := fun h => h1 ((le_max_left _ _).trans h)
    simp only [h1, h3, ite_false, zero_mul]

variable {D0 : ℝ} {η : ℝ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ}

omit [DecidableEq c] in
/-- **The transported `𝒦 conj 𝒦` bracket is the `antiholomorphic` integrand.** -/
theorem kks_transport (hD0 : 0 ≤ D0) (hDh : Dᴴ = D) (hPH : Pᴴ = P) (hPP : P * P = P)
    (hsig : bornL θ lam s ω * D * (bornL θ lam s ω)ᴴ = D') {X : Matrix ι c' ℂ}
    (hX : TwoProjection P D' X) (r r' : Fin 2) (i j k l : c) :
    ∑ x, ∑ x', ∑ z, ∑ z', (if max (bTime θ (r, i, j) ω) (bTime θ (r', k, l) ω) ≤ s then
      bCoef lam (r, i, j) ω x x' * star (bCoef lam (r', k, l) ω z z') *
        ∑ a, kNoise D0 η P D' a X x x' * star (kNoise D0 η P D' a X z z') else 0) =
      ((2 * η ^ 2 * D0 : ℝ) : ℂ) * (congrGram (bornL θ lam s ω) (gramPair P X)).2 i k *
        gramC0 (congrGram (bornL θ lam s ω) (gramPair P X)).1
          (congrGram (bornL θ lam s ω) (gramPair P X)).2 D l j := by
  set L := bornL θ lam s ω
  have hG := gramFeasible_congr hsig (gramFeasible_of_twoProjection hPH hPP hX)
  rw [← born_bracket_star hD0 η hDh hPH hPP hG (gramPair_mul P X L) i j k l]
  simp only [kNoise_mul D0 η P X L hsig, sandwich_apply, star_sum, star_mul']
  symm
  refine (sum_sum_mul_sum_sum _ _ _ _).trans (Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun z' _ => ?_)
  rw [cf_bornL θ lam s ω r i j, cf_bornL θ lam s ω r' k l]
  have e : star (if bTime θ (r', k, l) ω ≤ s then bCoef lam (r', k, l) ω z z' else 0) =
      if bTime θ (r', k, l) ω ≤ s then star (bCoef lam (r', k, l) ω z z') else 0 := by
    split_ifs <;> simp
  rw [e, ite_mul_ite]
  split_ifs <;> simp

omit [DecidableEq c] in
/-- The transported `𝒦`–Gram bracket is the born bracket. -/
theorem kg_transport (hsig : bornL θ lam s ω * D * (bornL θ lam s ω)ᴴ = D')
    (X : Matrix ι c' ℂ) (r r' : Fin 2) (i j k l : c) :
    ∑ x, ∑ x', ∑ z, ∑ z', (if max (bTime θ (r, i, j) ω) (bTime θ (r', k, l) ω) ≤ s then
      bCoef lam (r, i, j) ω x x' * bCoef lam (r', k, l) ω z z' *
        ∑ a, kNoise D0 η P D' a X x x' * gramEntry (r', z, z') (gramNoise D0 P D' a X) else 0) =
      ∑ a, kNoise D0 η P D a (X * bornL θ lam s ω) i j *
        gramEntry (r', k, l) (gramNoise D0 P D a (X * bornL θ lam s ω)) := by
  set L := bornL θ lam s ω
  simp only [kNoise_mul D0 η P X L hsig, gramNoise_mul D0 P X L hsig, sandwich_apply,
    gramEntry_congr]
  symm
  refine (sum_sum_mul_sum_sum _ _ _ _).trans (Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun z' _ => ?_)
  rw [cf_bornL θ lam s ω r i j, cf_bornL θ lam s ω r' k l, ite_mul_ite]
  split_ifs <;> simp

omit [DecidableEq c] in
/-- **The transported `𝒦`–`M` bracket is the `crossM` integrand.** -/
theorem kg_transport_M (hD0 : 0 ≤ D0) (hDh : Dᴴ = D) (hPH : Pᴴ = P) (hPP : P * P = P)
    (hsig : bornL θ lam s ω * D * (bornL θ lam s ω)ᴴ = D') {X : Matrix ι c' ℂ}
    (hX : TwoProjection P D' X) (r : Fin 2) (i j k l : c) :
    ∑ x, ∑ x', ∑ z, ∑ z', (if max (bTime θ (r, i, j) ω) (bTime θ (0, k, l) ω) ≤ s then
      bCoef lam (r, i, j) ω x x' * bCoef lam (0, k, l) ω z z' *
        ∑ a, kNoise D0 η P D' a X x x' * gramEntry (0, z, z') (gramNoise D0 P D' a X) else 0) =
      -(Complex.I * ((η * D0 : ℝ) : ℂ)) * (congrGram (bornL θ lam s ω) (gramPair P X)).2 i l *
        gramC0 (congrGram (bornL θ lam s ω) (gramPair P X)).1
          (congrGram (bornL θ lam s ω) (gramPair P X)).2 D k j := by
  rw [kg_transport θ lam s ω hsig X r 0 i j k l]
  exact born_bracket_M hD0 η hDh hPH hPP (gramFeasible_congr hsig
    (gramFeasible_of_twoProjection hPH hPP hX)) (gramPair_mul P X _) i j k l

omit [DecidableEq c] in
/-- **The transported `𝒦`–`B` bracket is the `crossB` integrand.** -/
theorem kg_transport_B (hD0 : 0 ≤ D0) (hDh : Dᴴ = D) (hPH : Pᴴ = P) (hPP : P * P = P)
    (hsig : bornL θ lam s ω * D * (bornL θ lam s ω)ᴴ = D') {X : Matrix ι c' ℂ}
    (hX : TwoProjection P D' X) (r : Fin 2) (i j k l : c) :
    ∑ x, ∑ x', ∑ z, ∑ z', (if max (bTime θ (r, i, j) ω) (bTime θ (1, k, l) ω) ≤ s then
      bCoef lam (r, i, j) ω x x' * bCoef lam (1, k, l) ω z z' *
        ∑ a, kNoise D0 η P D' a X x x' * gramEntry (1, z, z') (gramNoise D0 P D' a X) else 0) =
      -(Complex.I * ((η * D0 : ℝ) : ℂ)) * (congrGram (bornL θ lam s ω) (gramPair P X)).2 i l *
        (gramC1 (congrGram (bornL θ lam s ω) (gramPair P X)).1
          (congrGram (bornL θ lam s ω) (gramPair P X)).2 D)ᴴ k j := by
  rw [kg_transport θ lam s ω hsig X r 1 i j k l]
  exact born_bracket_B hD0 η hDh hPH hPP (gramFeasible_congr hsig
    (gramFeasible_of_twoProjection hPH hPP hX)) (gramPair_mul P X _) i j k l

end BlockBand.SourceProcess.ComplexConstruct
