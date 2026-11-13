module

public import BlockBand.Endpoints.Sine.MicroscopicTagStepsTags
public import BlockBand.Endpoints.Sine.MicroscopicTagStepsField

/-!
# Palm measurability, Gaussian factors, positivity, truncation

Assembly of Steps 2–3 of the proof of the microscopic tag comparison.

* Item 2 (`mts_measurable_palmExpect`): `a ↦ Â_{F(a), E(a)}[φ_a]` is measurable whenever `F`, `E`
  and `(a, v) ↦ φ_a(v)` are (Borel eigenvalues/eigenvectors, Fubini).
* Item 3:
  - `mts_gram_smul_inv`: `(√c X⁻¹)(√c X⁻¹)* = c (X*X)⁻¹` for **every** square `X` (Lean's
    inverse is totalised, so the singular case is `0 = 0`); hence `M = mts_freshFactor` satisfies
    `MM* = freshGamma F c E` for every `F` (`mts_freshFactor_gram`) and `blockFieldFactor` satisfies
    `MM* = blockMatchedGamma` for every exterior (`mts_blockFieldFactor_gram`);
  - `mts_traceAgainst_pos`: `Tr(c (X*X)⁻¹ D) > 0` when `X` is invertible, `c > 0`, `N > 0` and
    `D - 1 ⪰ 0` (the clocks satisfy `D = Σ_j D_j ⪰ D_k = I`).
* Item 4 (`mts_truncation`): a measurable `Δ` with `|Δ| ≤ ε` on an event and `|Δ| ≤ 2B` has
  `|Δ| ≤ ε + 2B·G` with `G = max(|Δ|-ε,0)/(2B)` measurable, `|G| ≤ 1`, `G = 0` on the event;
  this is the form used by `mts_window_irregular_le` and `mts_prior_irregular_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ENNReal NNReal ComplexOrder

/-!
## Item 3: Gaussian factors and positivity
-/

section Factor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mts_gram_smul_inv {c : ℝ} (hc : 0 ≤ c) (X : Matrix ι ι ℂ) :
    (((Real.sqrt c : ℝ) : ℂ) • X⁻¹) * (((Real.sqrt c : ℝ) : ℂ) • X⁻¹)ᴴ = (c : ℂ) • (Xᴴ * X)⁻¹ := by
  rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_smul_comm,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hc, conjTranspose_nonsing_inv, Matrix.mul_inv_rev]

end Factor

variable {N : ℕ}

/-- The Gaussian factor `M = √c X⁻¹`, `X = F - (E + c m_{F,c}(E))`, of `freshGamma F c E`. -/
def mts_freshFactor (F : Matrix (Fin N) (Fin N) ℂ) (c E : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  ((Real.sqrt c : ℝ) : ℂ) • (F - ((E : ℂ) + (c : ℂ) * freshDyson F c E) • 1)⁻¹

theorem mts_freshFactor_gram (F : Matrix (Fin N) (Fin N) ℂ) {c : ℝ} (hc : 0 ≤ c) (E : ℝ) :
    mts_freshFactor F c E * (mts_freshFactor F c E)ᴴ = freshGamma F c E := by
  unfold mts_freshFactor freshGamma
  exact mts_gram_smul_inv hc _

theorem mts_blockFieldFactor_gram (p : Parameters) (k : ZMod p.n) (ω : BlockState p k) (e : ℝ) :
    blockFieldFactor p k ω e * (blockFieldFactor p k ω e)ᴴ = blockMatchedGamma p k ω e := by
  unfold blockFieldFactor blockMatchedGamma
  exact mts_gram_smul_inv p.c_pos.le _

/-- `Tr(c (X*X)⁻¹ D) > 0` for invertible `X`, `c > 0`, `N > 0`, `D ⪰ 1`. -/
theorem mts_traceAgainst_pos (hN : 0 < N) {c : ℝ} (hc : 0 < c) (X D : Matrix (Fin N) (Fin N) ℂ)
    (hX : IsUnit X.det) (hD : (D - 1).PosSemidef) :
    0 < traceAgainst ((c : ℂ) • (Xᴴ * X)⁻¹) D := by
  set M := ((Real.sqrt c : ℝ) : ℂ) • X⁻¹
  have hΓ : (c : ℂ) • (Xᴴ * X)⁻¹ = M * Mᴴ := (mts_gram_smul_inv hc.le X).symm
  have hsplit : traceAgainst (M * Mᴴ) D = traceAgainst (M * Mᴴ) 1 +
      traceAgainst (M * Mᴴ) (D - 1) := by
    unfold traceAgainst
    rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.mul_add, add_sub_cancel]
  rw [hΓ, hsplit]
  have h2 := mts_traceAgainst_nonneg M (D - 1) hD
  have hM0 : Mᴴ ≠ 0 := by
    intro h0
    have hM : M = 0 := by rw [← conjTranspose_conjTranspose M, h0, conjTranspose_zero]
    have hXi : X⁻¹ = 0 := by
      have hs : ((Real.sqrt c : ℝ) : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero, Real.sqrt_eq_zero hc.le]; exact hc.ne'
      exact (smul_eq_zero.1 hM).resolve_left hs
    have h1 := nonsing_inv_mul X hX
    rw [hXi, Matrix.zero_mul] at h1
    have := congrFun (congrFun h1 ⟨0, hN⟩) ⟨0, hN⟩
    simp at this
  have h1 : 0 < traceAgainst (M * Mᴴ) 1 := by
    unfold traceAgainst
    rw [Matrix.mul_one]
    have hpsd := posSemidef_conjTranspose_mul_self Mᴴ
    rw [conjTranspose_conjTranspose] at hpsd
    have hnn := (Complex.nonneg_iff.1 hpsd.trace_nonneg)
    have hne : (M * Mᴴ).trace ≠ 0 := by
      intro h0
      apply hM0
      have := (trace_conjTranspose_mul_self_eq_zero_iff (A := Mᴴ)).1
      rw [conjTranspose_conjTranspose] at this
      exact this h0
    rcases hnn.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hne
      exact Complex.ext h.symm hnn.2.symm
  linarith

/-!
## Item 2: measurability of the Palm expectation
-/

theorem mts_measurable_palmExpect {α : Type*} [MeasurableSpace α]
    {F : α → Matrix (Fin N) (Fin N) ℂ} (hF : Measurable F) {E : α → ℝ} (hE : Measurable E)
    (c₀ : ℝ) {φ : α → (Fin N → ℂ) → ℝ} (hφ : Measurable (Function.uncurry φ)) :
    Measurable (fun a => palmExpect (F a) c₀ (E a) (φ a)) := by
  have := mts_isProbabilityMeasure_freshTracelessLaw N c₀
  have hadd : Measurable (fun q : α × Matrix (Fin N) (Fin N) ℂ => F q.1 + q.2) :=
    Measurable.of_eval fun i => Measurable.of_eval fun j =>
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hF.comp measurable_fst))).add
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))
  have hw : ∀ ℓ : Fin N, Measurable (fun q : α × Matrix (Fin N) (Fin N) ℂ =>
      palmWeight (F q.1) c₀ (E q.1) ℓ q.2) := by
    intro ℓ
    unfold palmWeight BlockBand.Palm.scalarWeight freshEigenvalue
    exact (measurable_gaussianPDFReal _ _).comp
      ((hE.comp measurable_fst).sub ((measurable_rawIncreasingEigenvalue _).comp hadd))
  have hu : ∀ ℓ : Fin N, Measurable (fun q : α × Matrix (Fin N) (Fin N) ℂ =>
      freshEigenvector (F q.1 + q.2) ℓ) := fun ℓ =>
    Measurable.of_eval fun x => (measurable_rawOrderedColumnSelection _ x).comp hadd
  have hnum : ∀ ℓ : Fin N, Measurable (fun a => ∫ A0, palmWeight (F a) c₀ (E a) ℓ A0 *
      φ a (freshEigenvector (F a + A0) ℓ) ∂freshTracelessLaw N c₀) := by
    intro ℓ
    have h0 : Measurable (fun q : α × Matrix (Fin N) (Fin N) ℂ =>
        palmWeight (F q.1) c₀ (E q.1) ℓ q.2 * φ q.1 (freshEigenvector (F q.1 + q.2) ℓ)) :=
      (hw ℓ).mul (hφ.comp (measurable_fst.prodMk (hu ℓ)))
    exact h0.stronglyMeasurable.integral_prod_right'.measurable
  have hden : ∀ ℓ : Fin N, Measurable (fun a => ∫ A0, palmWeight (F a) c₀ (E a) ℓ A0
      ∂freshTracelessLaw N c₀) := fun ℓ =>
    (hw ℓ).stronglyMeasurable.integral_prod_right'.measurable
  unfold palmExpect palmMass
  exact (Finset.measurable_sum _ fun ℓ _ => hnum ℓ).div (Finset.measurable_sum _ fun ℓ _ => hden ℓ)

/-!
## Item 4: truncation for the irregular event
-/

/-- **Truncation.** For a measurable `Δ` with `|Δ| ≤ 2B` everywhere and `|Δ| ≤ ε` on an event `R`
(`ε ≥ 0`, `B > 0`), `G = max(|Δ| - ε, 0)/(2B)` is measurable, `|G| ≤ 1`, vanishes on `R`, and
`|Δ| ≤ ε + 2B·G`. -/
theorem mts_truncation {α : Type*} [MeasurableSpace α] {Δ : α → ℝ} (hΔ : Measurable Δ)
    {ε B : ℝ} (hε : 0 ≤ ε) (hB : 0 < B) (hbd : ∀ x, |Δ x| ≤ 2 * B) (R : α → Prop)
    (hR : ∀ x, R x → |Δ x| ≤ ε) :
    ∃ G : α → ℝ, Measurable G ∧ (∀ x, |G x| ≤ 1) ∧ (∀ x, R x → G x = 0) ∧
      ∀ x, |Δ x| ≤ ε + 2 * B * G x := by
  refine ⟨fun x => max (|Δ x| - ε) 0 / (2 * B), ?_, ?_, ?_, ?_⟩
  · exact (((continuous_abs.measurable.comp hΔ).sub_const ε).max measurable_const).div_const _
  · intro x
    have h0 : 0 ≤ max (|Δ x| - ε) 0 := le_max_right _ _
    rw [abs_of_nonneg (div_nonneg h0 (by positivity)), div_le_one (by positivity)]
    exact max_le (by linarith [hbd x]) (by positivity)
  · intro x hx
    simp only
    rw [max_eq_right (by linarith [hR x hx]), zero_div]
  · intro x
    simp only
    rw [mul_div_cancel₀ _ (by positivity : (2 * B) ≠ 0)]
    linarith [le_max_left (|Δ x| - ε) 0]

end BlockBand.Endpoints
