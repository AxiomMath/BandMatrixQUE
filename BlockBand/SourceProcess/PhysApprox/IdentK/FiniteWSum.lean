module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWStepBound

/-!
# The per-step error terms and their sums

Closed law `μ = closedLaw b W np`, Borel alive sets `A'_j`, steps `n_s ≤ j < ⌊WT⌋`. The summed
errors: `Q_W(R)` (second moments from the brackets), `L_W(R)` (fourth moments from Lindeberg),
the births.

* `exists_lam_bound`: the generator of a test is bounded on admissible states with bounded
  jumps (`C_Λ`, independent of `R`).
* `pinTot`: the total of the summed errors at a level `R`; every summed error is at most
  `pinTot` (`sum_pinE1_le`, `sum_pinE2_le`, `sum_birth_le`).

The per-step moment bounds that these sums control are proved in a sibling module:
* `lint_sq_le`: `∫⁻ 1_{A'_j} ‖β_i‖² ≤ C_R / W + pinE2 j i (σ i)` (the conjugate partner `σ i`).
* `lint_four_le`: `∫⁻ 1_{A'_j} ‖β‖₁⁴ ≤ |BI|³ Σ_i ∫⁻ 1_{A_j} ‖dX_{c(i)}‖⁴`.
* `lint_birth_le`: at a birth step, `∫⁻ 1_{A'_j} |dStep| ≤ 3C Σ_i genBirthStep + C_Λ / W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Finset Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate ENNReal Topology

variable {W np K : ℕ}

/-! ## The generator bound -/

theorem norm_gen_le {I : Type*} [Fintype I] {d : I → ℂ} {B : I → I → ℂ} {x : Jet I} {C Cd : ℝ}
    (hl : ∀ i, ‖x.l i‖ ≤ C) (hq : ∀ i i', ‖x.q i i'‖ ≤ C) (hd : ∀ i, ‖d i‖ ≤ Cd)
    (hB : ∀ i i', ‖B i i'‖ ≤ Cd) (hC : 0 ≤ C) :
    ‖gen d B x‖ ≤ (Fintype.card I : ℝ) * (C * Cd) + (Fintype.card I : ℝ) ^ 2 * (C * Cd) := by
  have hCd : ∀ i, 0 ≤ Cd := fun i => (norm_nonneg _).trans (hd i)
  unfold gen lin
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul (univ : Finset I) (fun i => ‖x.l i * d i‖) (C * Cd)
      (fun i _ => by rw [norm_mul]; exact mul_le_mul (hl i) (hd i) (norm_nonneg _) hC)
    simpa [nsmul_eq_mul] using this
  · refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ i ∈ (univ : Finset I), ‖∑ i', x.q i i' * B i i'‖ ≤
        (Fintype.card I : ℝ) * (C * Cd) := fun i _ => by
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_card_nsmul (univ : Finset I) (fun i' => ‖x.q i i' * B i i'‖) (C * Cd)
        (fun i' _ => by rw [norm_mul]; exact mul_le_mul (hq i i') (hB i i') (norm_nonneg _) hC)
      simpa [nsmul_eq_mul] using this
    have := Finset.sum_le_card_nsmul _ _ _ h1
    simp only [card_univ, nsmul_eq_mul] at this
    nlinarith

/-- **The generator of a test is bounded** on admissible states with bounded jumps (`C_Λ`). -/
theorem exists_lam_bound {χ ξ : ℝ → ℝ} (hχ : ContDiff ℝ 3 χ) (hχs : HasCompactSupport χ)
    (hξ : ContDiff ℝ 3 ξ) (hξs : HasCompactSupport ξ) (b E : ℝ) (κ : KTest K np) {D CJ : ℝ}
    (hD : 0 ≤ D) : ∃ CΛ : ℝ, 0 ≤ CΛ ∧ ∀ (J : GSt K np) (z : ZK K np),
      (∀ e, ‖gramEntry e J‖ ≤ CJ) → Adm D z → ‖κ.lam χ ξ b E (J, z)‖ ≤ CΛ := by
  obtain ⟨C, hC0, hCb, -⟩ := exists_taylor_bound hχ hχs hξ hξs κ hD
  obtain ⟨Rχ0, hRχ0⟩ := exists_cut_radius hχs
  obtain ⟨Rξ0, hRξ0⟩ := exists_cut_radius hξs
  have hRχ : ∀ c, max Rχ0 0 < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0 :=
    fun c hc => hRχ0 c ((le_max_left _ _).trans_lt hc)
  have hRξ : ∀ c, max Rξ0 0 < |c| → ξ c = 0 ∧ deriv ξ c = 0 ∧ deriv (deriv ξ) c = 0 :=
    fun c hc => hRξ0 c ((le_max_left _ _).trans_lt hc)
  obtain ⟨CR, hCR0, hCR⟩ := exists_bound_coef (K := K) (np := np) b E (max Rχ0 0 + D + CJ)
  set n : ℝ := (Fintype.card (BI K np) : ℝ)
  refine ⟨n * (C * CR) + n ^ 2 * (C * CR), by positivity, fun J z hJ hz => ?_⟩
  rw [← gen_jF]
  by_cases hc : CutReg (max Rχ0 0) (max Rξ0 0) ((0 : GSt K np), z)
  · obtain ⟨h1, -, -, -⟩ := hc
    simp only [pyG] at h1
    have hH : ∀ e, ‖gramEntry e (z.1.1 + J)‖ ≤ max Rχ0 0 + D + CJ := fun e => by
      rw [gramEntry_add']
      refine (norm_add_le _ _).trans ?_
      linarith [hz.1 e, hJ e]
    obtain ⟨hd, hB⟩ := hCR _ hH
    exact norm_gen_le (hCb z hz).2.1 (hCb z hz).2.2 hd hB hC0
  · obtain ⟨-, h2, h3⟩ := isZJ_jF hRχ hRξ κ hc
    have : gen (dvec b E (z.1.1 + J)) (Bmat b E (z.1.1 + J)) (jF χ ξ κ z) = 0 := by
      simp [gen, lin, h2, h3]
    rw [this, norm_zero]; positivity

/-! ## The total summed error -/

section Pins

variable (b E s T h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
  (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)

/-- The total of all summed errors at level `R` and horizon `T`. -/
def pinTot : ℝ≥0∞ :=
  ∑ c : CIdx K np, ∑ c' : CIdx K np, b3SummedErr b E s T h τ m R W Vs c c' +
    ∑ ij : Fin np × Fin np, ∑ kl : Fin np × Fin np, b3ConjErr (K := K) b E s T h τ m R W Vs ij kl

theorem summed_le_pinTot (c c' : CIdx K np) :
    b3SummedErr b E s T h τ m R W Vs c c' ≤ pinTot b E s T h τ m R W Vs :=
  le_add_right ((single_le_sum (f := fun c' => b3SummedErr b E s T h τ m R W Vs c c')
    (fun _ _ => zero_le) (mem_univ c')).trans (single_le_sum
      (f := fun c => ∑ c', b3SummedErr b E s T h τ m R W Vs c c') (fun _ _ => zero_le)
      (mem_univ c)))

theorem conj_le_pinTot (ij kl : Fin np × Fin np) :
    b3ConjErr (K := K) b E s T h τ m R W Vs ij kl ≤ pinTot b E s T h τ m R W Vs :=
  le_add_left ((single_le_sum (f := fun kl => b3ConjErr (K := K) b E s T h τ m R W Vs ij kl)
    (fun _ _ => zero_le) (mem_univ kl)).trans (single_le_sum
      (f := fun ij => ∑ kl, b3ConjErr (K := K) b E s T h τ m R W Vs ij kl) (fun _ _ => zero_le)
      (mem_univ ij)))

variable {S : Finset ℕ} (hS : S ⊆ genNoBirthSteps s T τ W)
include hS

theorem sum_drift_le (c : CIdx K np) :
    ∑ j ∈ S, genDriftStep b E s h τ m R W j Vs c ≤ pinTot b E s T h τ m R W Vs :=
  ((sum_le_sum_of_subset hS).trans (le_add_right (le_add_right le_rfl))).trans
    (summed_le_pinTot b E s T h τ m R W Vs c c)

theorem sum_br_le (c c' : CIdx K np) :
    ∑ j ∈ S, genBrStep b E s h τ m R W j Vs c c' ≤ pinTot b E s T h τ m R W Vs :=
  ((sum_le_sum_of_subset hS).trans (le_add_right (le_add_left le_rfl))).trans
    (summed_le_pinTot b E s T h τ m R W Vs c c')

theorem sum_conj_le (ij kl : Fin np × Fin np) :
    ∑ j ∈ S, genConjStep (K := K) b E s h τ m R W j Vs ij kl ≤ pinTot b E s T h τ m R W Vs :=
  (sum_le_sum_of_subset hS).trans (conj_le_pinTot b E s T h τ m R W Vs ij kl)

theorem sum_pinE1_le (i : BI K np) :
    ∑ j ∈ S, pinE1 b E s h τ m R W Vs j i ≤ pinTot b E s T h τ m R W Vs :=
  sum_drift_le b E s T h τ m R W Vs hS (cOf i)

theorem sum_pinE2_le (i i' : BI K np) :
    ∑ j ∈ S, pinE2 b E s h τ m R W Vs j i i' ≤ pinTot b E s T h τ m R W Vs := by
  rcases i with e | a | a <;> rcases i' with e' | a' | a'
  · exact sum_br_le b E s T h τ m R W Vs hS (Sum.inl e) (Sum.inl e')
  · exact sum_br_le b E s T h τ m R W Vs hS (Sum.inl e) (Sum.inr a')
  · exact sum_br_le b E s T h τ m R W Vs hS (Sum.inl (eStar e)) (Sum.inr a')
  · exact sum_br_le b E s T h τ m R W Vs hS (Sum.inr a) (Sum.inl e')
  · exact sum_br_le b E s T h τ m R W Vs hS (Sum.inr a) (Sum.inr a')
  · exact sum_conj_le b E s T h τ m R W Vs hS a a'
  · exact sum_br_le b E s T h τ m R W Vs hS (Sum.inr a) (Sum.inl (eStar e'))
  · exact sum_conj_le b E s T h τ m R W Vs hS a a'
  · exact sum_br_le b E s T h τ m R W Vs hS (Sum.inr a) (Sum.inr a')

omit hS in
theorem sum_birth_le {S : Finset ℕ} (hS : S ⊆ genBirthSteps s T τ W) (c : CIdx K np) :
    ∑ j ∈ S, genBirthStep b E s h τ m R W j Vs c ≤ pinTot b E s T h τ m R W Vs :=
  ((sum_le_sum_of_subset hS).trans (le_add_left le_rfl)).trans
    (summed_le_pinTot b E s T h τ m R W Vs c c)

end Pins

theorem tendsto_pinTot {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T s h : ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hS : ComplexClosedSummed) (hF : FrameDomain b E τ m T s h K Vs) (R : ℝ) :
    Tendsto (fun W => pinTot b E s T h τ m R W (Vs W)) atTop (𝓝 0) := by
  obtain ⟨h1, h2⟩ := hS b E np τ m T s h K Vs hF R
  have := (tendsto_finsetSum (univ : Finset (CIdx K np)) fun c _ =>
    tendsto_finsetSum (univ : Finset (CIdx K np)) fun c' _ => h1 c c').add
    (tendsto_finsetSum (univ : Finset (Fin np × Fin np)) fun ij _ =>
      tendsto_finsetSum (univ : Finset (Fin np × Fin np)) fun kl _ => h2 ij kl)
  simpa [pinTot] using this

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
