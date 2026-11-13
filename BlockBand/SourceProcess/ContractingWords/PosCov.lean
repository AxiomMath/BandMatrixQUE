module

public import BlockBand.SourceProcess.ContractingWords.PosDrift

/-!
# The random expansion of a product of two word increments

Two words `posTr A`, `posTr A'` with positional cuts, old separators of norm `≤ 1`, random
increments `Δ, Δ'` with `SlotMoments` (same `β`, `M ≥ r + r'`), increments
`U = posTr A (σ+Δ) - posTr A σ = Σ_{t≠∅} X_t`, `U'` likewise:
* `pair_moment`: `E|X_t X'_{t'}| ≤ ΓΓ'(|t|+|t'|)β^{|t|+|t'|}` (slots `Fin r ⊕ Fin r'`);
* `cov_expand` (proved in a sibling module): `|E[UU'] - Σ_{p,q} E[X_{{p}}X'_{{q}}]| ≤
  ΓΓ' 2^{r+r'}(r+r')(β³ + β^{r+r'})`;
* `cross_mean` (proved in a sibling module): `E[X_{{p}}X'_{{q}}] = Σ_{l,l'} c_l c'_{l'} E[δ_{lp}δ'_{l'q}] Π x*σy Π x'*σ'y'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {n : Type} [Fintype n] [DecidableEq n] {r r' : ℕ} {A : Fin r → Matrix n n ℂ}
  {A' : Fin r' → Matrix n n ℂ} {ι ι' : Type} [Fintype ι] [Fintype ι'] {c : ι → ℂ} {c' : ι' → ℂ}
  {x y : ι → Fin r → n → ℂ} {x' y' : ι' → Fin r' → n → ℂ}

theorem sum_card_one {M : Type*} [AddCommMonoid M] (g : Finset (Fin r) → M) :
    ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => t.card = 1), g t =
      ∑ p, g {p} := by
  have h : (Finset.univ : Finset (Fin r)).powerset.filter (fun t => t.card = 1) =
      Finset.univ.map ⟨fun p => ({p} : Finset (Fin r)), Finset.singleton_injective⟩ := by
    ext t; simp [Finset.card_eq_one, eq_comm]
  rw [h, Finset.sum_map]; rfl

variable (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
  (hxy : ∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1)
  (hrep' : ∀ T, posTr A' T = ∑ l, c' l * ∏ p, bilinear (x' l p) (T p) (y' l p))
  (hxy' : ∀ l p, vecNorm (x' l p) ≤ 1 ∧ vecNorm (y' l p) ≤ 1)
  {σ : Fin r → Matrix n n ℂ} {σ' : Fin r' → Matrix n n ℂ} {Δ : Ω → Fin r → Matrix n n ℂ}
  {Δ' : Ω → Fin r' → Matrix n n ℂ} {M : ℕ} {β : ℝ}

include hrep hxy hrep' hxy' in
/-- **A product of two terms.** -/
theorem pair_moment (hσ : ∀ p, ‖σ p‖ ≤ 1) (hσ' : ∀ p, ‖σ' p‖ ≤ 1) (hΔ : SlotMoments μ Δ M β)
    (hΔ' : SlotMoments μ Δ' M β) {t : Finset (Fin r)} {t' : Finset (Fin r')} (ht : t.Nonempty)
    (htM : t.card + t'.card ≤ M) :
    Integrable (fun ω => posTr A (pw σ (Δ ω) t) * posTr A' (pw σ' (Δ' ω) t')) μ ∧
      ∫ ω, ‖posTr A (pw σ (Δ ω) t) * posTr A' (pw σ' (Δ' ω) t')‖ ∂μ ≤
        (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) *
          ((t.card + t'.card : ℕ) * β ^ (t.card + t'.card)) := by
  set s := t.disjSum t'
  have hs : s.Nonempty := by
    obtain ⟨p, hp⟩ := ht; exact ⟨Sum.inl p, Finset.inl_mem_disjSum.mpr hp⟩
  have hcard : s.card = t.card + t'.card := Finset.card_disjSum _ _
  have h1 : 1 ≤ s.card := Finset.card_pos.mpr hs
  have hsM : s.card ≤ M := hcard ▸ htM
  set g : ι × ι' → Fin r ⊕ Fin r' → Ω → ℂ := fun L => Sum.elim
    (fun p ω => bilinear (x L.1 p) (Δ ω p) (y L.1 p))
    (fun q ω => bilinear (x' L.2 q) (Δ' ω q) (y' L.2 q))
  have hg : ∀ L, Integrable (fun ω => ∏ i ∈ s, g L i ω) μ ∧
      ∫ ω, ∏ i ∈ s, ‖g L i ω‖ ∂μ ≤ s.card * β ^ s.card := fun L =>
    prod_moment s hs (g L)
      (fun i _ => by
        cases i with
        | inl p => exact (hΔ p _ _ (hxy L.1 p).1 (hxy L.1 p).2).1
        | inr q => exact (hΔ' q _ _ (hxy' L.2 q).1 (hxy' L.2 q).2).1)
      (fun i _ => by
        cases i with
        | inl p => exact ((hΔ p _ _ (hxy L.1 p).1 (hxy L.1 p).2).2 _ h1 hsM).1
        | inr q => exact ((hΔ' q _ _ (hxy' L.2 q).1 (hxy' L.2 q).2).2 _ h1 hsM).1)
      (fun i _ => by
        cases i with
        | inl p => exact ((hΔ p _ _ (hxy L.1 p).1 (hxy L.1 p).2).2 _ h1 hsM).2
        | inr q => exact ((hΔ' q _ _ (hxy' L.2 q).1 (hxy' L.2 q).2).2 _ h1 hsM).2)
  have hsplit : ∀ L ω, ∏ i ∈ s, g L i ω = (∏ p ∈ t, bilinear (x L.1 p) (Δ ω p) (y L.1 p)) *
      ∏ q ∈ t', bilinear (x' L.2 q) (Δ' ω q) (y' L.2 q) := fun L ω => by
    simp [s, g, Finset.prod_disjSum]
  have hfun : (fun ω => posTr A (pw σ (Δ ω) t) * posTr A' (pw σ' (Δ' ω) t')) = fun ω =>
      ∑ L : ι × ι', c L.1 * c' L.2 * (∏ i ∈ s, g L i ω) *
        ((∏ p ∈ Finset.univ \ t, bilinear (x L.1 p) (σ p) (y L.1 p)) *
          ∏ q ∈ Finset.univ \ t', bilinear (x' L.2 q) (σ' q) (y' L.2 q)) := funext fun ω => by
    rw [posTr_pw hrep, posTr_pw hrep', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    rw [hsplit]; ring
  have hdom : Integrable (fun ω => ∑ L : ι × ι', ‖c L.1‖ * ‖c' L.2‖ * ∏ i ∈ s, ‖g L i ω‖) μ :=
    integrable_finsetSum _ fun L _ => ((hg L).1.norm.congr (Filter.Eventually.of_forall
      fun ω => by simp [norm_prod])).const_mul _
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact integrable_finsetSum _ fun L _ => ((hg L).1.const_mul _).mul_const _
  · have hpt : ∀ ω, ‖posTr A (pw σ (Δ ω) t) * posTr A' (pw σ' (Δ' ω) t')‖ ≤
        ∑ L : ι × ι', ‖c L.1‖ * ‖c' L.2‖ * ∏ i ∈ s, ‖g L i ω‖ := fun ω => by
      rw [norm_mul]
      refine (mul_le_mul (norm_posTr_pw_le hrep hxy hσ (Δ ω) t)
        (norm_posTr_pw_le hrep' hxy' hσ' (Δ' ω) t') (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => by positivity)).trans (le_of_eq ?_)
      rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
      have e := congrArg norm (hsplit (l, l') ω)
      rw [norm_prod, norm_mul, norm_prod, norm_prod] at e
      simp only at e ⊢
      rw [e]; ring
    calc _ ≤ ∫ ω, ∑ L : ι × ι', ‖c L.1‖ * ‖c' L.2‖ * ∏ i ∈ s, ‖g L i ω‖ ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hdom
            (Filter.Eventually.of_forall hpt)
      _ = ∑ L : ι × ι', ‖c L.1‖ * ‖c' L.2‖ * ∫ ω, ∏ i ∈ s, ‖g L i ω‖ ∂μ := by
          rw [integral_finsetSum _ fun L _ => ((hg L).1.norm.congr (Filter.Eventually.of_forall
            fun ω => by simp [norm_prod])).const_mul _]
          exact Finset.sum_congr rfl fun L _ => integral_const_mul _ _
      _ ≤ ∑ L : ι × ι', ‖c L.1‖ * ‖c' L.2‖ * (s.card * β ^ s.card) :=
          Finset.sum_le_sum fun L _ => mul_le_mul_of_nonneg_left (hg L).2 (by positivity)
      _ = _ := by
          rw [← Finset.sum_mul, Fintype.sum_prod_type, hcard]
          simp only [← Finset.sum_mul, ← Finset.mul_sum]

end BlockBand.SourceProcess.ContractingWords
