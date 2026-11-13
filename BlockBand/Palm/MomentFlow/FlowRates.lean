module

public import BlockBand.Palm.MomentFlow.MaxPrinciple
public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# The moment-flow generator along the eigenvalue paths of the matrix flow

The moment-flow generator `𝓑_σ` with the rates `flowRate` of the matrix flow, its short part `𝓢`
with rates masked to `|i - j| < ℓ`, the maximum principle and uniqueness for both flows along a
sample path, and the identification of the one-particle short flow with the forward mass
equation of `shortGenerator`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem flowRate_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ)
    (k l : Fin N) : 0 ≤ flowRate F a ω σ k l := by
  unfold flowRate; positivity

theorem flowRate_symm (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ)
    (k l : Fin N) : flowRate F a ω σ k l = flowRate F a ω σ l k := by
  unfold flowRate; congr 2; ring

theorem labelDist_comm (k l : Fin N) : labelDist k l = labelDist l k := by
  unfold labelDist; omega

/-- The moment-flow generator `𝓑` at matrix-flow time `σ`. -/
def flowMomentGenerator (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ) :
    (Occ N → ℝ) → Occ N → ℝ :=
  momentGenerator (flowRate F a ω σ)

/-- Short rates `c_ij 1{|i-j| < ℓ}`. -/
def shortFlowRate (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ) :
    Fin N → Fin N → ℝ :=
  maskRate (fun i j => labelDist i j < ℓ) (flowRate F a ω σ)

/-- The short generator `𝓢` (jumps with `|i - j| < ℓ` only). -/
def shortFlowMomentGenerator (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) : (Occ N → ℝ) → Occ N → ℝ :=
  momentGenerator (shortFlowRate F a ω ℓ σ)

theorem shortFlowRate_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (i j : Fin N) : 0 ≤ shortFlowRate F a ω ℓ σ i j := by
  unfold shortFlowRate maskRate; split_ifs
  · exact flowRate_nonneg F a ω σ i j
  · exact le_rfl

theorem shortFlowRate_symm (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (i j : Fin N) : shortFlowRate F a ω ℓ σ i j = shortFlowRate F a ω ℓ σ j i :=
  maskRate_symm _ (flowRate_symm F a ω σ) (fun i j => by rw [labelDist_comm]) i j

/-- The full generator splits as short plus long parts: `𝓑 = 𝓢 + (𝓑 - 𝓢)`, where the long part
uses the rates `c_ij 1{|i-j| ≥ ℓ}` (the long jumps). -/
theorem flowMomentGenerator_eq_short_add_long (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ) (f : Occ N → ℝ) (ξ : Occ N) :
    flowMomentGenerator F a ω σ f ξ = shortFlowMomentGenerator F a ω ℓ σ f ξ +
      momentGenerator (maskRate (fun i j => ¬ labelDist i j < ℓ) (flowRate F a ω σ)) f ξ := by
  unfold flowMomentGenerator shortFlowMomentGenerator shortFlowRate momentGenerator
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold maskRate
  split_ifs <;> simp_all

/-- Self-adjointness of `𝓑` for counting measure on each sector, along every sample path. -/
theorem flowMomentGenerator_symm (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (σ : ℝ) (r : ℕ) (f g : Occ N → ℝ) :
    ∑ ξ ∈ sector N r, g ξ * flowMomentGenerator F a ω σ f ξ =
      ∑ ξ ∈ sector N r, f ξ * flowMomentGenerator F a ω σ g ξ :=
  sum_mul_momentGenerator_symm (flowRate_symm F a ω σ) r f g

/-- Self-adjointness of `𝓢` for counting measure on each sector. -/
theorem shortFlowMomentGenerator_symm (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) (r : ℕ) (f g : Occ N → ℝ) :
    ∑ ξ ∈ sector N r, g ξ * shortFlowMomentGenerator F a ω ℓ σ f ξ =
      ∑ ξ ∈ sector N r, f ξ * shortFlowMomentGenerator F a ω ℓ σ g ξ :=
  sum_mul_momentGenerator_symm (shortFlowRate_symm F a ω ℓ σ) r f g

/-- **Markov property of the full flow along a sample path**: any solution of `∂_σ F = 𝓑_σ F` on
`[s,u]` and the `r`-particle sector stays between the initial extremes. -/
theorem flowMoment_bounds (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (r : ℕ)
    {s u m M : ℝ} {Φ : ℝ → Occ N → ℝ}
    (hΦ : IsMomentFlowSolution (flowRate F a ω) r s u Φ)
    (hm : ∀ ξ ∈ sector N r, m ≤ Φ s ξ) (hM : ∀ ξ ∈ sector N r, Φ s ξ ≤ M) :
    ∀ v ∈ Icc s u, ∀ ξ ∈ sector N r, m ≤ Φ v ξ ∧ Φ v ξ ≤ M := fun v hv ξ hξ =>
  ⟨hΦ.ge_of_initial_ge (fun x _ i j _ => flowRate_nonneg F a ω x i j) hm v hv ξ hξ,
    hΦ.le_of_initial_le (fun x _ i j _ => flowRate_nonneg F a ω x i j) hM v hv ξ hξ⟩

/-- **Markov property of the short flow `𝓢`**: it is positive, preserves constants and contracts
the supremum norm. -/
theorem shortFlowMoment_bounds (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ r : ℕ) {s u m M : ℝ} {Φ : ℝ → Occ N → ℝ}
    (hΦ : IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ)
    (hm : ∀ ξ ∈ sector N r, m ≤ Φ s ξ) (hM : ∀ ξ ∈ sector N r, Φ s ξ ≤ M) :
    ∀ v ∈ Icc s u, ∀ ξ ∈ sector N r, m ≤ Φ v ξ ∧ Φ v ξ ≤ M := fun v hv ξ hξ =>
  ⟨hΦ.ge_of_initial_ge (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j) hm v hv ξ hξ,
    hΦ.le_of_initial_le (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j) hM v hv ξ hξ⟩

/-- Uniqueness of the full moment flow along a sample path. -/
theorem flowMoment_unique (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (r : ℕ)
    {s u : ℝ} {Φ Ψ : ℝ → Occ N → ℝ}
    (hΦ : IsMomentFlowSolution (flowRate F a ω) r s u Φ)
    (hΨ : IsMomentFlowSolution (flowRate F a ω) r s u Ψ)
    (h0 : ∀ ξ ∈ sector N r, Φ s ξ = Ψ s ξ) :
    ∀ v ∈ Icc s u, ∀ ξ ∈ sector N r, Φ v ξ = Ψ v ξ :=
  hΦ.eq_of_initial_eq (fun x _ i j _ => flowRate_nonneg F a ω x i j) hΨ h0

/-!
## The one-particle sector is the one-particle short generator
-/

theorem move_single (k j : Fin N) (hkj : k ≠ j) :
    move (Pi.single k 1 : Occ N) k j = Pi.single j 1 := by
  funext m
  by_cases hmk : m = k
  · subst hmk; rw [move_apply_source _ hkj]; simp [hkj]
  · by_cases hmj : m = j
    · subst hmj; rw [move_apply_target]; simp [hmk]
    · rw [move_apply_of_ne _ hmk hmj]; simp [hmk, hmj]

/-- **One particle** (`r = 1`, configurations `δ_k`): the short moment generator `𝓢` acts as the
matrix `shortGenerator`, the generator of `ForwardMassSolution` in
`RelativeLocalizationContract.short_row` and `short_column`:
`(𝓢 f)(δ_k) = ∑_l shortGenerator(k,l) f(δ_l)`. -/
theorem shortFlowMomentGenerator_single (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ) (f : Occ N → ℝ) (k : Fin N) :
    shortFlowMomentGenerator F a ω ℓ σ f (Pi.single k 1) =
      ∑ l, shortGenerator F a ω ℓ σ k l * f (Pi.single l 1) := by
  classical
  unfold shortFlowMomentGenerator momentGenerator
  rw [Finset.sum_eq_single k]
  · -- the source is `k`
    have hL : ∀ j ∈ Finset.univ.erase k, shortFlowRate F a ω ℓ σ k j *
        jumpCoeff (Pi.single k 1 : Occ N) k j *
        (f (move (Pi.single k 1) k j) - f (Pi.single k 1)) =
        shortFlowRate F a ω ℓ σ k j * (f (Pi.single j 1) - f (Pi.single k 1)) := by
      intro j hj
      have hjk : j ≠ k := (Finset.mem_erase.1 hj).1
      rw [move_single k j (Ne.symm hjk)]
      simp [jumpCoeff, hjk]
    rw [Finset.sum_congr rfl hL]
    have hdiag : shortGenerator F a ω ℓ σ k k =
        -∑ m ∈ Finset.univ.erase k, shortFlowRate F a ω ℓ σ k m := by
      simp only [shortGenerator, ite_true, shortFlowRate, maskRate]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      congr 2
      ext m; simp [and_comm]
    have hoff : ∀ l ∈ Finset.univ.erase k,
        shortGenerator F a ω ℓ σ k l = shortFlowRate F a ω ℓ σ k l := by
      intro l hl
      have hlk : k ≠ l := Ne.symm (Finset.mem_erase.1 hl).1
      simp [shortGenerator, hlk, shortFlowRate, maskRate]
    have hrhs : ∑ l, shortGenerator F a ω ℓ σ k l * f (Pi.single l 1) =
        -(∑ m ∈ Finset.univ.erase k, shortFlowRate F a ω ℓ σ k m) * f (Pi.single k 1) +
          ∑ l ∈ Finset.univ.erase k, shortFlowRate F a ω ℓ σ k l * f (Pi.single l 1) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hdiag]
      congr 1
      exact Finset.sum_congr rfl fun l hl => by rw [hoff l hl]
    rw [hrhs]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  · intro i _ hik
    refine Finset.sum_eq_zero fun j _ => ?_
    have : (Pi.single k 1 : Occ N) i = 0 := by simp [hik]
    simp [jumpCoeff_eq_zero_of_eq_zero _ j this]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem single_mem_sector_one {N : ℕ} (k : Fin N) : (Pi.single k 1 : Occ N) ∈ sector N 1 := by
  rw [mem_sector]; simp

/-- Solution-level form of `shortFlowMomentGenerator_single`: the one-particle short moment
flow restricted to `δ_k` solves the forward mass equation of `shortGenerator`. -/
theorem forwardMassSolution_of_momentFlow {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) {s u : ℝ} {Φ : ℝ → Occ N → ℝ}
    (hΦ : IsMomentFlowSolution (shortFlowRate F a ω ℓ) 1 s u Φ) :
    ForwardMassSolution (shortGenerator F a ω ℓ) s u (fun k => Φ s (Pi.single k 1))
      (fun x k => Φ x (Pi.single k 1)) := by
  refine ⟨rfl, continuousOn_pi.2 fun k => (hΦ _ (single_mem_sector_one k)).1, fun x hx => ?_⟩
  refine hasDerivAt_pi.2 fun k => ?_
  have h := (hΦ _ (single_mem_sector_one k)).2 x hx
  have e := shortFlowMomentGenerator_single F a ω ℓ x (Φ x) k
  unfold shortFlowMomentGenerator at e
  rw [e] at h
  exact h

end BlockBand.Palm.MomentFlow

