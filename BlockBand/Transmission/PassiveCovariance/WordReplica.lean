module

public import BlockBand.Transmission.PassiveCovariance.WordCov

/-!
# The replica identity for dressed bilinear test functionals

Hypothesis `PassiveBoundsStatement` (only `moments`). Law `layerLaw W b .oneBlockOnePort`,
`z = z_∂(E)`, deterministic strictly passive `X`, uniformly.

* `hasLayerDeriv_wordForm`: `Ψ` has the layer derivative `DΨ` (`HasLayerDeriv`).
* `memLp_two_of_poly`: functions bounded by `K(1 + B)^r` are in `L²`, uniformly (by the `moments`
  clause of `PassiveBoundsStatement`).
* These give `replica_wordForm`: `replica_identity_phys` and `replica_identity_port` for every
  dressed `Ψ` of length
  `≤ L_w`, with **all integrability discharged**:
  `E[(V𝒢)_{xβ}Ψ] = Σ_y (c/W)E[𝒢_{yβ}DΨ(E_{yx}) - Ψ𝒢_{yy}𝒢_{xβ}] + Σ_y (b/W)E[…]` and the port
  version. Here `U = LL*` itself is the dressed word `K̂𝒢·P₂·(K̂𝒢)ᴴ` (`P₂` the port projector).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

section Generic
variable {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem continuous_wLetter (Kh : Matrix n n ℂ) (k : Fin 4) :
    Continuous fun G : Matrix n n ℂ => wLetter Kh G k := by
  fin_cases k
  · exact continuous_id
  · exact continuous_const.mul continuous_id
  · exact continuous_id.matrix_conjTranspose
  · exact (continuous_const.mul continuous_id).matrix_conjTranspose

omit [DecidableEq n] in
theorem continuous_wLeft (Kh : Matrix n n ℂ) (k : Fin 4) :
    Continuous fun G : Matrix n n ℂ => wLeft Kh G k := by
  fin_cases k
  · exact continuous_id
  · exact continuous_const.mul continuous_id
  · exact continuous_id.matrix_conjTranspose
  · exact continuous_id.matrix_conjTranspose

omit [DecidableEq n] in
theorem continuous_wRight (Kh : Matrix n n ℂ) (k : Fin 4) :
    Continuous fun G : Matrix n n ℂ => wRight Kh G k := by
  fin_cases k
  · exact continuous_id
  · exact continuous_id
  · exact continuous_id.matrix_conjTranspose
  · exact (continuous_const.mul continuous_id).matrix_conjTranspose

theorem continuous_wordVal (Kh : Matrix n n ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → Matrix n n ℂ) : Continuous fun G : Matrix n n ℂ => wordVal Kh G wd D :=
  (contDiff_wordVal Kh contDiff_id wd D).continuous

omit [DecidableEq n] in
theorem continuous_wordAlpha (Kh : Matrix n n ℂ) :
    ∀ (ℓ : ℕ) (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ) (j : Fin ℓ),
      Continuous fun G : Matrix n n ℂ => wordAlpha Kh G ℓ wd D j := by
  intro ℓ
  induction ℓ with
  | zero => intro _ _ j; exact j.elim0
  | succ ℓ ih =>
    intro wd D j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [wordAlpha, Fin.cons_zero]
      exact continuous_const.mul (continuous_wLeft Kh _)
    · simp only [wordAlpha, Fin.cons_succ]
      exact (continuous_const.mul (continuous_wLetter Kh _)).mul (ih _ _ j)

theorem continuous_wordGamma (Kh : Matrix n n ℂ) :
    ∀ (ℓ : ℕ) (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ) (j : Fin ℓ),
      Continuous fun G : Matrix n n ℂ => wordGamma Kh G ℓ wd D j := by
  intro ℓ
  induction ℓ with
  | zero => intro _ _ j; exact j.elim0
  | succ ℓ ih =>
    intro wd D j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [wordGamma, Fin.cons_zero]
      exact (continuous_wRight Kh _).mul (continuous_wordVal Kh _ _)
    · simp only [wordGamma, Fin.cons_succ]
      exact ih _ _ j

/-- The ℂ-linear derivative `N ↦ -Σ_j a*α_j N γ_j c` of `a*w(G)c`. -/
def wordFormDeriv (Kh : Matrix n n ℂ) (a c : n → ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → Matrix n n ℂ) (G : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] ℂ where
  toFun N := -∑ j, star a ⬝ᵥ ((wordAlpha Kh G ℓ wd D j * N * wordGamma Kh G ℓ wd D j) *ᵥ c)
  map_add' N N' := by
    simp only [Matrix.mul_add, Matrix.add_mul, add_mulVec, dotProduct_add, Finset.sum_add_distrib,
      neg_add]
  map_smul' r N := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_mulVec, dotProduct_smul, smul_eq_mul,
      Finset.mul_sum, RingHom.id_apply, mul_neg]

theorem wordFormDeriv_apply (Kh : Matrix n n ℂ) (a c : n → ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → Matrix n n ℂ) (G N : Matrix n n ℂ) :
    wordFormDeriv Kh a c wd D G N =
      -∑ j, star a ⬝ᵥ ((wordAlpha Kh G ℓ wd D j * N * wordGamma Kh G ℓ wd D j) *ᵥ c) := rfl

theorem norm_wordFormDeriv_le (Kh : Matrix n n ℂ) (a c : n → ℂ) {Kd : ℝ} (hKd : 0 ≤ Kd) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ) (hD : ∀ j, ‖D j‖ ≤ Kd)
    (G N : Matrix n n ℂ) :
    ‖wordFormDeriv Kh a c wd D G N‖ ≤
      ℓ * (Kd ^ (ℓ + 1) * wBound Kh G ^ (ℓ + 1)) * ‖N‖ * (vecNorm a * vecNorm c) := by
  rw [wordFormDeriv_apply, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖star a ⬝ᵥ ((wordAlpha Kh G ℓ wd D j * N * wordGamma Kh G ℓ wd D j) *ᵥ c)‖
      ≤ ∑ _j : Fin ℓ, Kd ^ (ℓ + 1) * wBound Kh G ^ (ℓ + 1) * ‖N‖ * (vecNorm a * vecNorm c) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := norm_bilinear_le a (wordAlpha Kh G ℓ wd D j * N * wordGamma Kh G ℓ wd D j) c
        have hn : ‖wordAlpha Kh G ℓ wd D j * N * wordGamma Kh G ℓ wd D j‖ ≤
            ‖wordAlpha Kh G ℓ wd D j‖ * ‖wordGamma Kh G ℓ wd D j‖ * ‖N‖ := by
          calc _ ≤ ‖wordAlpha Kh G ℓ wd D j * N‖ * ‖wordGamma Kh G ℓ wd D j‖ :=
                Matrix.l2_opNorm_mul _ _
            _ ≤ ‖wordAlpha Kh G ℓ wd D j‖ * ‖N‖ * ‖wordGamma Kh G ℓ wd D j‖ := by
                gcongr; exact Matrix.l2_opNorm_mul _ _
            _ = _ := by ring
        have hb := norm_wordAlpha_mul_le Kh G hKd wd D hD j
        have ha := vecNorm_nonneg a; have hc := vecNorm_nonneg c
        calc _ ≤ vecNorm a * ‖wordAlpha Kh G ℓ wd D j * N * wordGamma Kh G ℓ wd D j‖ *
              vecNorm c := h
          _ ≤ vecNorm a * (Kd ^ (ℓ + 1) * wBound Kh G ^ (ℓ + 1) * ‖N‖) * vecNorm c := by
              gcongr
              exact hn.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
          _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Generic

/-- **The layer derivative of a dressed bilinear form** at a strictly passive input. -/
theorem hasLayerDeriv_wordForm {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hY : (passiveY X).PosDef) (Kh : LayerMat W) (a c : LayerSite W .oneBlockOnePort → ℂ) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W) :
    HasLayerDeriv (fun ω => wordForm Kh a c wd D (gRes b E X ω))
      (fun ω => wordFormDeriv Kh a c wd D (gRes b E X ω)) := by
  intro ω hω Δ hΔ
  have hM := isUnit_layerMatrix_strict (E := E) hη hY ω hω
  have h := (formL a c).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_wordVal_line Kh _ hM wd D (layerLin Δ) (layerLin_isHermitian Δ hΔ))
  have e : (fun s : ℝ => wordForm Kh a c wd D (gRes b E X (ω + (s : ℂ) • Δ))) = fun s : ℝ =>
      formL a c (wordVal Kh ((layerMatrix .oneBlockOnePort E (boundaryZ b E)
        (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω + (s : ℂ) • layerLin Δ)⁻¹) wd D) := by
    funext s
    change formL a c (wordVal Kh (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) (ω + (s : ℂ) • Δ))⁻¹ wd D) = _
    rw [layerMatrix_add_smul]
  rw [e]
  refine h.congr_deriv ?_
  rw [formL_apply, wordFormDeriv_apply, neg_mulVec, dotProduct_neg, sum_mulVec, dotProduct_sum]
  rfl

/-- **`L²` from a polynomial bound in `1 + B`**, uniformly over passive inputs. -/
theorem memLp_two_of_poly (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (r : ℕ) (hr : 1 ≤ r) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (F : LayerSample W .oneBlockOnePort → ℂ), AEStronglyMeasurable F (layerLaw W b .oneBlockOnePort) →
      ∀ K : ℝ, (∀ ω, ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ r) →
        MemLp F 2 (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨C, W₀, hC, hm⟩ := btFun_moment hA hb0 hb h1 h2 (2 * (r : ℕ)) (by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith)
  refine ⟨W₀, fun W hW X hX F hF K hK => ?_⟩
  have hg := eLpNorm_pow_le (μ := layerLaw W b .oneBlockOnePort) (g := fun ω => 1 + btFun b E X ω)
    (fun ω => by have := btFun_nonneg b E X ω; positivity)
    (measurable_const.add (measurable_btFun b E X)).aestronglyMeasurable r hr (hm W hW X hX)
  have hgL : MemLp (fun ω => (1 + btFun b E X ω) ^ r) 2 (layerLaw W b .oneBlockOnePort) :=
    lt_of_le_of_lt hg (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  refine (hgL.const_mul K).of_le hF (Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ (1 + btFun b E X ω) ^ r := by have := btFun_nonneg b E X ω; positivity
  have hK0 : 0 ≤ K := by
    by_contra hneg
    have := hK ω
    have : K * (1 + btFun b E X ω) ^ r < 0 := by
      have h1' : 0 < (1 + btFun b E X ω) ^ r := by have := btFun_nonneg b E X ω; positivity
      nlinarith
    linarith [norm_nonneg (F ω)]
  rw [Real.norm_of_nonneg (mul_nonneg hK0 h0)]
  exact hK ω

end BlockBand.Transmission.PassiveCovariance
