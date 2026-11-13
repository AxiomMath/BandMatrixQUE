module

public import BlockBand.Transmission.PassiveCovariance.SdSite

/-!
# The vector Schwinger–Dyson identity for dressed words

Hypothesis `PassiveBoundsStatement` (`moments` only, for integrability). Law
`layerLaw W b .oneBlockOnePort`, `z = z_∂(E)`, strictly passive `X`; `b, E`, the word length `L_w`, the
insertion bound `K_d` and the test exponent `m` are fixed first, then `W₀`.

**`sd_vector`.** For both sides `𝔊 = gSide adj ∈ {𝒢, 𝒢ᴴ}`, every dressed word `N = w(𝒢)` (`wordVal`,
length `≤ L_w`, letters
`𝒢, K̂𝒢, 𝒢ᴴ, (K̂𝒢)ᴴ`, insertions `≤ K_d`), all vectors `a, c` and every test functional `Ψ`
with a linear layer derivative `DΨ` and polynomial bounds
`|Ψ| ≤ K(1+B)^m`, `|DΨ(N')| ≤ K‖N'‖(1+B)^m` (`B = btFun`):
`E[(a*V𝔊Nc)Ψ] = E[Σ_{α,γ} σ(α,γ) ā_α (𝔊Nc)_γ DΨ(E_{γα})
   - (Σ_j a*S[𝔊α_j]γ_jc + a*S[𝔊]𝔊Nc) Ψ]`,
with `α_j, γ_j` the derivative factors of `N` (`wordAlpha`, `wordGamma`), `S = sdiag`.
The `S[𝒢]` term is the self-energy, the `S[𝒢α_j]` terms are the traces produced by
differentiating the letters of `N` (the ladder), and the `DΨ` term is the crossed contraction.
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

section Alg
variable {n : Type} [Fintype n] [DecidableEq n]

theorem mul_single_mul_mulVec_apply (A B : Matrix n n ℂ) (c : n → ℂ) (γ α δ : n) :
    ((A * Matrix.single γ α 1 * B) *ᵥ c) δ = A δ γ * (B *ᵥ c) α := by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  simp only [mulVec, dotProduct, Matrix.single_apply, Finset.mul_sum]
  simp [ite_and, Finset.sum_ite_eq, mul_comm]

omit [DecidableEq n] in
theorem sum_mul_mulVec (G M : Matrix n n ℂ) (v : n → ℂ) (γ : n) :
    ∑ β, G γ β * (M *ᵥ v) β = ((G * M) *ᵥ v) γ := by
  rw [← mulVec_mulVec]; rfl

omit [DecidableEq n] in
theorem sum_mul_sum_swap (x : ℂ) (s : n → ℂ) (f : n → n → ℂ) :
    ∑ β, x * ∑ γ, s γ * f β γ = ∑ γ, x * s γ * ∑ β, f β γ := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [DecidableEq n] in
theorem sd_alpha (x ψ T : ℂ) (σ P Gd : n → ℂ) {ℓ : ℕ} (Q : Fin ℓ → n → ℂ) :
    ∑ γ, x * σ γ * (P γ - ψ * ∑ j, Q j γ - ψ * Gd γ * T) =
      ∑ γ, σ γ * (x * P γ) - (∑ j, x * (∑ γ, σ γ * Q j γ) + x * (∑ γ, σ γ * Gd γ) * T) * ψ := by
  have e1 : ∑ j, x * (∑ γ, σ γ * Q j γ) = ∑ γ, x * σ γ * ∑ j, Q j γ := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : x * (∑ γ, σ γ * Gd γ) * T = ∑ γ, x * σ γ * Gd γ * T := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, ← Finset.sum_add_distrib, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [DecidableEq n] in
theorem dotProduct_diagonal_mul_mulVec (a c d : n → ℂ) (M : Matrix n n ℂ) [DecidableEq n] :
    star a ⬝ᵥ ((diagonal d * M) *ᵥ c) = ∑ α, star (a α) * (d α * (M *ᵥ c) α) := by
  rw [← mulVec_mulVec]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]

/-- The finite-sum algebra behind `sd_vector`. -/
theorem sd_algebra (σ : n → n → ℂ) (G N : Matrix n n ℂ) {ℓ : ℕ} (A B : Fin ℓ → Matrix n n ℂ)
    (a c : n → ℂ) (ψ : ℂ) (dψ : Matrix n n ℂ →ₗ[ℂ] ℂ) :
    ∑ α, ∑ β, star (a α) * ∑ γ, σ α γ * (G γ β * ((N *ᵥ c) β * dψ (Matrix.single γ α 1) +
        ψ * -∑ j, ((A j * Matrix.single γ α 1 * B j) *ᵥ c) β) -
        (N *ᵥ c) β * ψ * (G γ γ * G α β)) =
      ∑ α, ∑ γ, σ α γ * (star (a α) * ((G * N) *ᵥ c) γ * dψ (Matrix.single γ α 1)) -
        ((∑ j, star a ⬝ᵥ ((diagonal (fun α => ∑ γ, σ α γ * (G * A j) γ γ) * B j) *ᵥ c)) +
          star a ⬝ᵥ ((diagonal (fun α => ∑ γ, σ α γ * G γ γ) * G * N) *ᵥ c)) * ψ := by
  have hin : ∀ α γ, ∑ β, (G γ β * ((N *ᵥ c) β * dψ (Matrix.single γ α 1) +
      ψ * -∑ j, ((A j * Matrix.single γ α 1 * B j) *ᵥ c) β) -
      (N *ᵥ c) β * ψ * (G γ γ * G α β)) =
      ((G * N) *ᵥ c) γ * dψ (Matrix.single γ α 1) -
        ψ * ∑ j, (G * A j) γ γ * (B j *ᵥ c) α - ψ * G γ γ * ((G * N) *ᵥ c) α := by
    intro α γ
    have e1 : ∀ j, ∑ β, G γ β * ((A j * Matrix.single γ α 1 * B j) *ᵥ c) β =
        (G * A j) γ γ * (B j *ᵥ c) α := fun j => by
      rw [sum_mul_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_single_mul_mulVec_apply]
    have e2 : ∑ β, (N *ᵥ c) β * ψ * (G γ γ * G α β) = ψ * G γ γ * ((G * N) *ᵥ c) α := by
      rw [← sum_mul_mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    have e3 : ∑ β, G γ β * ((N *ᵥ c) β * dψ (Matrix.single γ α 1)) =
        ((G * N) *ᵥ c) γ * dψ (Matrix.single γ α 1) := by
      rw [← sum_mul_mulVec, Finset.sum_mul]
      exact Finset.sum_congr rfl fun β _ => by ring
    have e4 : ∑ β, G γ β * (ψ * -∑ j, ((A j * Matrix.single γ α 1 * B j) *ᵥ c) β) =
        -(ψ * ∑ j, (G * A j) γ γ * (B j *ᵥ c) α) := by
      rw [← Finset.sum_congr rfl fun j _ => e1 j]
      simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, e2, e3, e4]
    ring
  have lhs : ∀ α, ∑ β, star (a α) * ∑ γ, σ α γ * (G γ β * ((N *ᵥ c) β * dψ (Matrix.single γ α 1) +
      ψ * -∑ j, ((A j * Matrix.single γ α 1 * B j) *ᵥ c) β) -
      (N *ᵥ c) β * ψ * (G γ γ * G α β)) =
      ∑ γ, star (a α) * σ α γ * (((G * N) *ᵥ c) γ * dψ (Matrix.single γ α 1) -
        ψ * ∑ j, (G * A j) γ γ * (B j *ᵥ c) α - ψ * G γ γ * ((G * N) *ᵥ c) α) := by
    intro α
    rw [sum_mul_sum_swap]
    exact Finset.sum_congr rfl fun γ _ => by rw [hin α γ]
  rw [Finset.sum_congr rfl fun α _ => lhs α]
  simp only [Finset.sum_congr rfl fun α _ => sd_alpha (star (a α)) ψ (((G * N) *ᵥ c) α)
    (σ α) (fun γ => ((G * N) *ᵥ c) γ * dψ (Matrix.single γ α 1)) (fun γ => G γ γ)
    (fun j γ => (G * A j) γ γ * (B j *ᵥ c) α)]
  simp only [dotProduct_diagonal_mul_mulVec, Matrix.mul_assoc]
  rw [Finset.sum_comm (f := fun j α => star (a α) *
    ((∑ γ, σ α γ * (G * A j) γ γ) * (B j *ᵥ c) α)), Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => by ring
  · congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    · simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring

end Alg

section Main
variable {W : ℕ}

theorem vecNorm_single_one {n : Type*} [Fintype n] [DecidableEq n] (k : n) :
    vecNorm (Pi.single k (1 : ℂ)) = 1 := by
  rw [vecNorm, Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
  simp

theorem wordForm_single {n : Type} [Fintype n] [DecidableEq n] (Kh : Matrix n n ℂ) (β : n)
    (c : n → ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ) (G : Matrix n n ℂ) :
    wordForm Kh (Pi.single β 1) c wd D G = (wordVal Kh G wd D *ᵥ c) β := by
  simp [wordForm, dotProduct, Pi.single_apply]

theorem wordFormDeriv_single {n : Type} [Fintype n] [DecidableEq n] (Kh : Matrix n n ℂ) (β : n)
    (c : n → ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ) (G N : Matrix n n ℂ) :
    wordFormDeriv Kh (Pi.single β 1) c wd D G N =
      -∑ j, ((wordAlpha Kh G ℓ wd D j * N * wordGamma Kh G ℓ wd D j) *ᵥ c) β := by
  rw [wordFormDeriv_apply]
  simp [dotProduct, Pi.single_apply]

theorem measurable_wordFormDeriv (Kh : LayerMat W) (a c : LayerSite W .oneBlockOnePort → ℂ) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W) {G : LayerSample W .oneBlockOnePort → LayerMat W}
    (hG : Measurable G) (N : LayerMat W) :
    Measurable fun ω => wordFormDeriv Kh a c wd D (G ω) N := by
  have hc : Continuous fun H : LayerMat W => wordFormDeriv Kh a c wd D H N := by
    simp only [wordFormDeriv_apply]
    refine (continuous_finsetSum _ fun j _ => ?_).neg
    exact continuous_const.dotProduct ((((continuous_wordAlpha Kh _ wd D j).mul
      continuous_const).mul (continuous_wordGamma Kh _ wd D j)).matrix_mulVec continuous_const)
  exact hc.measurable.comp hG

/-- **The vector Schwinger–Dyson identity** (see the module docstring). -/
theorem sd_vector (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw m : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) → ∀ (a c : LayerSite W .oneBlockOnePort → ℂ)
      (Ψ : LayerSample W .oneBlockOnePort → ℂ)
      (DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ) (K : ℝ),
      HasLayerDeriv Ψ DΨ → Measurable Ψ → (∀ N, Measurable fun ω => DΨ ω N) →
      (∀ ω, ‖Ψ ω‖ ≤ K * (1 + btFun b E X ω) ^ m) →
      (∀ ω N, ‖DΨ ω N‖ ≤ K * ‖N‖ * (1 + btFun b E X ω) ^ m) →
        ∫ ω, star a ⬝ᵥ ((layerLin ω * gSide b E X adj ω *
            wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) * Ψ ω ∂layerLaw W b .oneBlockOnePort =
          ∫ ω, (∑ α, ∑ γ, siteVar W b α γ * (star (a α) *
              ((gSide b E X adj ω * wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) γ *
                DΨ ω (Matrix.single γ α 1)) -
            ((∑ j, star a ⬝ᵥ ((sdiag b (gSide b E X adj ω *
                wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) *
                wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) *ᵥ c)) +
              star a ⬝ᵥ ((sdiag b (gSide b E X adj ω) * gSide b E X adj ω *
                wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c)) * Ψ ω)
            ∂layerLaw W b .oneBlockOnePort := by
  obtain ⟨W₀, hP⟩ := memLp_poly hA hb0 hb h1 h2 (Lw + m + 3)
  refine ⟨W₀, fun W hW X hX ℓ hℓ wd D hD a c Ψ DΨ K hΨ hΨm hDm hΨb hDb => ?_⟩
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set Bt : LayerSample W .oneBlockOnePort → ℝ := fun ω => 1 + btFun b E X ω
  have hB1 : ∀ ω, 1 ≤ Bt ω := one_le_one_add_btFun b E X
  have hB0 : ∀ ω, 0 ≤ Bt ω := fun ω => zero_le_one.trans (hB1 ω)
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hSm := measurable_gSide b E X adj
  have hent : ∀ γ δ, Measurable fun ω => gSide b E X adj ω γ δ := fun γ δ => hSm.eval_matrix
  have hGb : ∀ ω γ δ, ‖gSide b E X adj ω γ δ‖ ≤ Bt ω := fun ω γ δ =>
    (norm_entry_le' _ γ δ).trans ((norm_gSide b E X adj ω).trans_le (norm_gRes_le_btFun b E X ω))
  have hGNG : ∀ ω (N : LayerMat W) γ δ,
      ‖(gSide b E X adj ω * N * gSide b E X adj ω) γ δ‖ ≤ ‖N‖ * Bt ω ^ 2 := fun ω N γ δ => by
    refine (norm_entry_le' _ γ δ).trans ((Matrix.l2_opNorm_mul _ _).trans ?_)
    have hG := (norm_gSide b E X adj ω).trans_le (norm_gRes_le_btFun b E X ω)
    calc ‖gSide b E X adj ω * N‖ * ‖gSide b E X adj ω‖ ≤ ‖gSide b E X adj ω‖ * ‖N‖ * ‖gSide b E X adj ω‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ Bt ω * ‖N‖ * Bt ω := mul_le_mul (mul_le_mul_of_nonneg_right hG (norm_nonneg _)) hG
          (norm_nonneg _) (mul_nonneg (hB0 ω) (norm_nonneg _))
      _ = ‖N‖ * Bt ω ^ 2 := by ring
  set K1 := max Kd 1 ^ (Lw + 1)
  set Cφ := K1 * vecNorm c
  have hCφ : 0 ≤ Cφ := mul_nonneg (by positivity) (vecNorm_nonneg c)
  have hK : 0 ≤ K := by
    have h := (norm_nonneg _).trans (hΨb 0)
    exact nonneg_of_mul_nonneg_left h (by have := hB1 0; positivity)
  set Φ : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → ℂ := fun β ω =>
    wordForm Kh (Pi.single β 1) c wd D (gRes b E X ω)
  set DΦ : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ :=
    fun β ω => wordFormDeriv Kh (Pi.single β 1) c wd D (gRes b E X ω)
  have hΦb : ∀ β ω, ‖Φ β ω‖ ≤ Cφ * Bt ω ^ (Lw + 1) := fun β ω => by
    have h := (wordForm_poly_bounds b E X hKd hℓ wd D hD (Pi.single β 1) c ω).1
    rw [vecNorm_single_one, one_mul] at h
    exact h.trans (le_of_eq (by ring))
  have hDΦb : ∀ β ω N, ‖DΦ β ω N‖ ≤ Lw * Cφ * ‖N‖ * Bt ω ^ (Lw + 1) := fun β ω N => by
    have h := (wordForm_poly_bounds b E X hKd hℓ wd D hD (Pi.single β 1) c ω).2 N
    rw [vecNorm_single_one, one_mul] at h
    exact h.trans (le_of_eq (by ring))
  set Ψβ : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → ℂ :=
    fun β ω => Φ β ω * Ψ ω
  set DΨβ : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ :=
    fun β ω => Φ β ω • DΨ ω + Ψ ω • DΦ β ω
  have hΨβd : ∀ β, HasLayerDeriv (Ψβ β) (DΨβ β) := fun β =>
    (hasLayerDeriv_wordForm hη hX Kh _ c wd D).mul hΨ
  have hΦm : ∀ β, Measurable (Φ β) := fun β => measurable_wordForm Kh _ c wd D hGm
  have hΨβm : ∀ β, Measurable (Ψβ β) := fun β => (hΦm β).mul hΨm
  have hDΦm : ∀ β N, Measurable fun ω => DΦ β ω N := fun β N =>
    measurable_wordFormDeriv Kh _ c wd D hGm N
  have hW' := hP W hW X hX.posSemidef
  have hBp : ∀ ω k, 0 ≤ Bt ω ^ k := fun ω k => pow_nonneg (hB0 ω) k
  have hk : ∀ k, k ≤ Lw + m + 3 → ∀ ω, Bt ω ^ k ≤ Bt ω ^ (Lw + m + 3) := fun k hk ω =>
    pow_le_pow_right₀ (hB1 ω) hk
  have hL2 : ∀ β γ, MemLp (fun ω => gSide b E X adj ω γ β * Ψβ β ω) 2 μ := fun β γ => by
    refine hW' (fun ω => gSide b E X adj ω γ β * Ψβ β ω) ((hent γ β).mul (hΨβm β)).aestronglyMeasurable
      (Cφ * K) (Lw + m + 2) (by omega) fun ω => ?_
    simp only [Ψβ]
    rw [norm_mul, norm_mul]
    calc ‖gSide b E X adj ω γ β‖ * (‖Φ β ω‖ * ‖Ψ ω‖) ≤ Bt ω * (Cφ * Bt ω ^ (Lw + 1) * (K * Bt ω ^ m)) :=
          mul_le_mul (hGb ω γ β) (mul_le_mul (hΦb β ω) (hΨb ω) (norm_nonneg _)
            (mul_nonneg hCφ (hBp ω _))) (by positivity)
            (hB0 ω)
      _ = Cφ * K * Bt ω ^ (Lw + m + 2) := by ring
  have hI1 : ∀ β γ N, Integrable (fun ω => gSide b E X adj ω γ β * DΨβ β ω N) μ := fun β γ N => by
    refine (hW' (fun ω => gSide b E X adj ω γ β * DΨβ β ω N)
      ((hent γ β).mul (((hΦm β).mul (hDm N)).add (hΨm.mul (hDΦm β N)))).aestronglyMeasurable
      ((1 + Lw) * Cφ * K * ‖N‖) (Lw + m + 2) (by omega) fun ω => ?_).integrable one_le_two
    simp only [DΨβ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [norm_mul]
    have e1 := norm_add_le (Φ β ω * DΨ ω N) (Ψ ω * DΦ β ω N)
    rw [norm_mul, norm_mul] at e1
    have hb1 : ‖Φ β ω‖ * ‖DΨ ω N‖ ≤ Cφ * Bt ω ^ (Lw + 1) * (K * ‖N‖ * Bt ω ^ m) :=
      mul_le_mul (hΦb β ω) (hDb ω N) (norm_nonneg _) (mul_nonneg hCφ (hBp ω _))
    have hb2 : ‖Ψ ω‖ * ‖DΦ β ω N‖ ≤ K * Bt ω ^ m * (Lw * Cφ * ‖N‖ * Bt ω ^ (Lw + 1)) :=
      mul_le_mul (hΨb ω) (hDΦb β ω N) (norm_nonneg _) (mul_nonneg hK (hBp ω _))
    calc ‖gSide b E X adj ω γ β‖ * ‖Φ β ω * DΨ ω N + Ψ ω * DΦ β ω N‖
        ≤ Bt ω * (Cφ * Bt ω ^ (Lw + 1) * (K * ‖N‖ * Bt ω ^ m) +
            K * Bt ω ^ m * (Lw * Cφ * ‖N‖ * Bt ω ^ (Lw + 1))) :=
          mul_le_mul (hGb ω γ β) (e1.trans (add_le_add hb1 hb2)) (norm_nonneg _) (hB0 ω)
      _ = (1 + Lw) * Cφ * K * ‖N‖ * Bt ω ^ (Lw + m + 2) := by ring
  have hI2 : ∀ β γ N, Integrable (fun ω => Ψβ β ω * (gSide b E X adj ω * N * gSide b E X adj ω) γ β) μ :=
    fun β γ N => by
    refine (hW' (fun ω => Ψβ β ω * (gSide b E X adj ω * N * gSide b E X adj ω) γ β)
      ((hΨβm β).mul ((hSm.mul_const N).mul hSm).eval_matrix).aestronglyMeasurable
      (Cφ * K * ‖N‖) (Lw + m + 3) le_rfl fun ω => ?_).integrable one_le_two
    simp only [Ψβ]
    rw [norm_mul, norm_mul]
    calc ‖Φ β ω‖ * ‖Ψ ω‖ * ‖(gSide b E X adj ω * N * gSide b E X adj ω) γ β‖
        ≤ Cφ * Bt ω ^ (Lw + 1) * (K * Bt ω ^ m) * (‖N‖ * Bt ω ^ 2) :=
          mul_le_mul (mul_le_mul (hΦb β ω) (hΨb ω) (norm_nonneg _) (mul_nonneg hCφ (hBp ω _)))
            (hGNG ω N γ β) (norm_nonneg _)
            (mul_nonneg (mul_nonneg hCφ (hBp ω _)) (mul_nonneg hK (hBp ω _)))
      _ = Cφ * K * ‖N‖ * Bt ω ^ (Lw + m + 3) := by ring
  -- the site identities
  have hsite := fun α β => replica_site_gen b (gSide b E X adj) (hasLayerDeriv_gSide hη hX adj)
    hSm (hΨβd β) (hΨβm β) α β (hL2 β) (hI1 β) (hI2 β)
  set Y : LayerSite W .oneBlockOnePort → LayerSite W .oneBlockOnePort →
      LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → ℂ :=
    fun α β γ ω => gSide b E X adj ω γ β * DΨβ β ω (Matrix.single γ α 1) -
      Ψβ β ω * (gSide b E X adj ω γ γ * gSide b E X adj ω α β)
  have hY : ∀ α β γ, Integrable (Y α β γ) μ := fun α β γ => by
    have e : (fun ω => Ψβ β ω * (gSide b E X adj ω γ γ * gSide b E X adj ω α β)) =
        fun ω => Ψβ β ω * (gSide b E X adj ω * (Matrix.single γ α (1 : ℂ) : LayerMat W) *
          gSide b E X adj ω) γ β := by
      funext ω; rw [mul_single_mul_apply]
    have h2 := hI2 β γ (Matrix.single γ α 1)
    rw [← e] at h2
    exact (hI1 β γ _).sub h2
  -- pointwise expansion of the left side
  have hpt : ∀ ω, star a ⬝ᵥ ((layerLin ω * gSide b E X adj ω * wordVal Kh (gRes b E X ω) wd D) *ᵥ c) *
      Ψ ω = ∑ α, ∑ β, star (a α) * ((layerLin ω * gSide b E X adj ω) α β * Ψβ β ω) := by
    intro ω
    rw [← mulVec_mulVec]
    simp only [Ψβ, Φ, wordForm_single, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum,
      Pi.star_apply]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun x _ => by ring
  have hint : ∀ α β, Integrable (fun ω => star (a α) *
      ((layerLin ω * gSide b E X adj ω) α β * Ψβ β ω)) μ := fun α β => (hsite α β).1.const_mul _
  have hYs : ∀ α β, Integrable (fun ω => star (a α) * ∑ γ, siteVar W b α γ * Y α β γ ω) μ :=
    fun α β => (integrable_finsetSum _ fun γ _ => (hY α β γ).const_mul _).const_mul _
  calc ∫ ω, star a ⬝ᵥ ((layerLin ω * gSide b E X adj ω * wordVal Kh (gRes b E X ω) wd D) *ᵥ c) * Ψ ω ∂μ
      = ∑ α, ∑ β, ∫ ω, star (a α) * ((layerLin ω * gSide b E X adj ω) α β * Ψβ β ω) ∂μ := by
        rw [integral_congr_ae (Eventually.of_forall hpt),
          integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint α β]
        exact Finset.sum_congr rfl fun α _ => integral_finsetSum _ fun β _ => hint α β
    _ = ∑ α, ∑ β, ∫ ω, star (a α) * ∑ γ, siteVar W b α γ * Y α β γ ω ∂μ := by
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
        rw [integral_const_mul, integral_const_mul, (hsite α β).2,
          integral_finsetSum _ fun γ _ => (hY α β γ).const_mul _]
        congr 1
        exact Finset.sum_congr rfl fun γ _ => (integral_const_mul _ _).symm
    _ = ∫ ω, ∑ α, ∑ β, star (a α) * ∑ γ, siteVar W b α γ * Y α β γ ω ∂μ := by
        rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hYs α β]
        exact Finset.sum_congr rfl fun α _ => (integral_finsetSum _ fun β _ => hYs α β).symm
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [Y, DΨβ, Ψβ, Φ, DΦ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          wordForm_single, wordFormDeriv_single]
        exact sd_algebra (siteVar W b) (gSide b E X adj ω) (wordVal Kh (gRes b E X ω) wd D)
          (wordAlpha Kh (gRes b E X ω) ℓ wd D) (wordGamma Kh (gRes b E X ω) ℓ wd D) a c (Ψ ω) (DΨ ω)

end Main

end BlockBand.Transmission.PassiveCovariance
