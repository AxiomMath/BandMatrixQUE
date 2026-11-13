module

public import BlockBand.SourceProcess.ContractingWords.PosUnits

/-!
# One word at one layer to second order, against a covariance tensor

Setting of `PosDrift`; besides `SlotMoments μ Δ M β` (`r ≤ M`), the means `m_p = EΔ_p` satisfy
`‖m_p‖ ≤ μ₀`, and for slots `p ≠ q` and unit vectors the second moments match a sum of four crossed
tensors up to `ε`: `|E[(x*Δ_p y)(x'*Δ_q y')] - (x*m_p y)(x'*m_q y') - Σ_k κ_k ct(x,y,x',y',G_k,H_k)| ≤ ε`.

This file defines the pair functional `pairF` and the mean slots `slotMean`, with the counting identity
`sum_card_two` and the bound `norm_posTr_pw_mean`. They are used for the following results, proved in
sibling modules:

* `drift_abstract`: `E posTr(σ+Δ) = posTr σ + Σ_p posTr(pw σ m {p})
  + Σ_{p<q} Σ_k κ_k Σ G_{ad}H_{cb} posTr(pw σ (units2 p q a b c d) {p,q}) + O(Γ(2^r r(β³+β^r) + r²(ε+μ₀²)))`;
* `cov_abstract`: the same for the product of two increments, with one slot in each word.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

theorem sum_card_two {r : ℕ} {M : Type*} [AddCommMonoid M] (g : Finset (Fin r) → M) :
    ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => t.card = 2), g t =
      ∑ p, ∑ q ∈ Finset.Ioi p, g {p, q} := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => ({x.1, x.2} : Finset (Fin r))) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_Ioi] at hx
    simp [Finset.card_pair (ne_of_lt hx.2)]
  · rintro ⟨p, q⟩ hx ⟨p', q'⟩ hx' h
    simp only [Finset.mem_sigma, Finset.mem_Ioi, Finset.mem_univ, true_and] at hx hx'
    have h1 : p ∈ ({p', q'} : Finset (Fin r)) := h ▸ by simp
    have h2 : q ∈ ({p', q'} : Finset (Fin r)) := h ▸ by simp
    have h3 : p' ∈ ({p, q} : Finset (Fin r)) := h.symm ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3
    have hp : p = p' := by
      rcases h1 with h1 | h1
      · exact h1
      · rcases h3 with h3 | h3
        · exact h3.symm
        · exfalso; subst h1; subst h3; exact absurd (hx.trans hx') (lt_irrefl _)
    subst hp
    have hq : q = q' := by
      rcases h2 with h2 | h2
      · exact absurd (h2 ▸ hx) (lt_irrefl _)
      · exact h2
    subst hq; rfl
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and] at ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp ht
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨⟨a, b⟩, by simp [h], rfl⟩
    · exact ⟨⟨b, a⟩, by simp [h], Finset.pair_comm _ _⟩
  · intro _ _; rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} {A : Fin r → Matrix n n ℂ}
  {ι : Type} [Fintype ι] {c : ι → ℂ} {x y : ι → Fin r → n → ℂ}

/-- The contracted pair functional of positions `p ≠ q` against `(G, H)`. -/
def pairF (A σ : Fin r → Matrix n n ℂ) (p q : Fin r) (G H : Matrix n n ℂ) : ℂ :=
  ∑ c₁, ∑ b, ∑ a, ∑ d, G a d * H c₁ b * posTr A (pw σ (units2 p q a b c₁ d) {p, q})

/-- The mean slot matrices. -/
def slotMean (μ : Measure Ω) (Δ : Ω → Fin r → Matrix n n ℂ) : Fin r → Matrix n n ℂ :=
  fun q => matrixExpect μ fun ω => Δ ω q

theorem norm_posTr_pw_mean {σ m : Fin r → Matrix n n ℂ}
    (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (hxy : ∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1) (hσ : ∀ p, ‖σ p‖ ≤ 1)
    {μ₀ : ℝ} (hm : ∀ p, ‖m p‖ ≤ μ₀) (t : Finset (Fin r)) :
    ‖posTr A (pw σ m t)‖ ≤ (∑ l, ‖c l‖) * μ₀ ^ t.card := by
  refine (norm_posTr_pw_le hrep hxy hσ m t).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p _ => ?_
  have h := norm_bilinear_le (x l p) (m p) (y l p)
  have h0 := vecNorm_nonneg (x l p)
  have h1 := vecNorm_nonneg (y l p)
  calc _ ≤ vecNorm (x l p) * ‖m p‖ * vecNorm (y l p) := h
    _ ≤ 1 * μ₀ * 1 := by
        have := (hxy l p).1; have := (hxy l p).2; have := hm p; have := norm_nonneg (m p)
        have : 0 ≤ μ₀ := (norm_nonneg _).trans (hm p)
        gcongr
    _ = μ₀ := by ring

end BlockBand.SourceProcess.ContractingWords
