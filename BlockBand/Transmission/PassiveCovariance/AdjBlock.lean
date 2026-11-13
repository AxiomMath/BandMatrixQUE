module

public import BlockBand.Transmission.PassiveCovariance.M2Near

/-!
# The `𝒢ᴴ`-first expansion, physical block, for every dressed word

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive `X`,
fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, word length `≤ L_w`, insertions `≤ K_d`; constants depend on these
only, uniformly in `W ≥ W₀`, `X` and the word. Operator norm.

* `bilinear_finsum`: `u*(Σ_jA_j)v = Σ_j u*A_jv`.
* **`adjBlock`**: `‖(E[𝒢ᴴw])₀₀ - Mᴴ((Ew)₀₀ + Σ_jσ₁(r_j)(Eγ_j)₀₀)‖ ≤ C/W²` with
  `r_{j,q} = E⟨(𝒢ᴴα_j)_qq⟩` (`sdOne_expand` with `adj = true`, `P₀ = 1`, physical vectors; the
  bilinear bound is turned into an operator-norm bound as in `gsMean_block`, which is the case
  `w = P_p𝒢`). The integrability of `w`, `𝒢ᴴw` and the `γ_j` is assumed entrywise (each use is a
  concrete word, where `wordMean_bound` supplies it).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem bilinear_finsum {n ι : Type*} [Fintype n] (u v : n → ℂ) (s : Finset ι)
    (f : ι → Matrix n n ℂ) : bilinear u (∑ j ∈ s, f j) v = ∑ j ∈ s, bilinear u (f j) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bilinear]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bilinear_add, ih]

/-- **The `𝒢ᴴ`-first expansion, physical block.** -/
theorem adjBlock (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) →
      (∀ α β, Integrable (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D α β)
        (layerLaw W b .oneBlockOnePort)) →
      (∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) wd D) α β)
        (layerLaw W b .oneBlockOnePort)) →
      (∀ j α β, Integrable (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j α β)
        (layerLaw W b .oneBlockOnePort)) →
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => (gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0 -
          (SourceMixing.mOf b E X)ᴴ *
            (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0 +
            ∑ j, sig1 b
                (trMean b (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0)
                (trMean b (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1) •
              blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨Cs, Ws, hCs, hS⟩ := sdOne_expand hA hb0 hb h1 h2 Lw Kd true
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  obtain ⟨CK, WK, hCK, hK⟩ := SourceMixing.norm_kHat_dressedInv hA hb0 hb h1 h2
  refine ⟨Cs * CD, max (max Ws WD) WK, by positivity,
    fun W hW X hX ℓ hℓ wd D hDn hI hI' hIγ => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWs, hWD⟩, hWK⟩ := hW
  obtain ⟨hW1, -, hM, -, -, -, -, -, -, -, -⟩ := hD W hWD X hX
  obtain ⟨hU, -, -, -⟩ := hK W hWK X hX
  obtain ⟨m00, m01⟩ := mbarTrue_blk hW1 hU
  set μ := layerLaw W b .oneBlockOnePort
  set M := SourceMixing.mOf b E X
  refine opNorm_le_of_bilinear _ (by positivity) fun u v => ?_
  have h := hS W hWs X hX ℓ hℓ wd D hDn 1 (physVec u) (physVec v)
  simp only at h
  have hxc : (1 * mbarSide b E X true)ᴴ *ᵥ physVec u = physVec (M *ᵥ u) := by
    rw [Matrix.one_mul, conjT_mulVec_physVec m01, m00, conjTranspose_conjTranspose]
  rw [hxc] at h
  have e1 : ∀ ω, star (physVec u) ⬝ᵥ ((1 * gSide b E X true ω *
      wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ physVec v) =
      star (physVec u) ⬝ᵥ (((gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ
        physVec v) := fun ω => by rw [Matrix.one_mul]; rfl
  simp only [e1] at h
  rw [integral_form _ hI'] at h
  have e2 : ∀ ω, star (physVec u) ⬝ᵥ ((1 * mbarSide b E X true *
      wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ physVec v) =
      star (physVec u) ⬝ᵥ ((mbarSide b E X true * wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ
        physVec v) := fun ω => by rw [Matrix.one_mul]
  simp only [e2] at h
  have hMN : ∀ α β, Integrable
      (fun ω => (mbarSide b E X true * wordVal (kHat b E X) (gRes b E X ω) wd D : LayerMat W) α β)
      μ := fun α β => by
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun k _ => (hI k β).const_mul _
  rw [integral_form _ hMN, ← SourceMixing.mul_matrixExpect' _ _ hI, blkAt_mul, Fin.sum_univ_two,
    m00, m01, Matrix.zero_mul, add_zero] at h
  have e4 : ∀ (j : Fin ℓ) (q : Fin 2), (∫ ω, star (physVec (M *ᵥ u)) ⬝ᵥ ((dRow b q *
      wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) *ᵥ physVec v) ∂layerLaw W b .oneBlockOnePort) =
      sRow b q * bilinear u (Mᴴ * blkAt (matrixExpect μ
        (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)) 0 0) v := fun j q => by
    have e : ∀ ω, star (physVec (M *ᵥ u)) ⬝ᵥ ((dRow b q *
        wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) *ᵥ physVec v) =
        sRow b q * star (physVec (M *ᵥ u)) ⬝ᵥ
          (wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j *ᵥ physVec v) := fun ω =>
      form_dRow q (isPhys_physVec _) _ _
    simp only [e]
    rw [integral_const_mul, integral_form _ (hIγ j), ← bilinear_conjT_left,
      conjTranspose_conjTranspose]
  simp only [e4, Fin.sum_univ_two] at h
  rw [vecNorm_physVec, vecNorm_physVec] at h
  set Y := blkAt (matrixExpect μ
    (fun ω => (gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0
  set N0 := blkAt (matrixExpect μ (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0
  set Γ := fun j => blkAt (matrixExpect μ
    (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)) 0 0
  set r := fun (j : Fin ℓ) (q : Fin 2) =>
    trMean b (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) q
  have eq : bilinear u (Y - Mᴴ * (N0 + ∑ j, sig1 b (r j 0) (r j 1) • Γ j)) v =
      bilinear u Y v - bilinear u (Mᴴ * N0) v -
        ∑ j, (r j 0 * (sRow b 0 * bilinear u (Mᴴ * Γ j) v) +
          r j 1 * (sRow b 1 * bilinear u (Mᴴ * Γ j) v)) := by
    rw [bilinear_sub, Matrix.mul_add, bilinear_add, Matrix.mul_sum, bilinear_finsum,
      sub_add_eq_sub_sub]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, bilinear_smul, sRow_zero, sRow_one]
    simp only [sig1]; push_cast; ring
  rw [eq]
  have hMu : vecNorm (M *ᵥ u) ≤ CD * vecNorm u := (vecNorm_mulVec_le M u).trans
    (mul_le_mul_of_nonneg_right hM (vecNorm_nonneg u))
  refine (h.trans ?_)
  have := vecNorm_nonneg v
  calc Cs / (W : ℝ) ^ 2 * (vecNorm (M *ᵥ u) * vecNorm v) ≤
      Cs / (W : ℝ) ^ 2 * (CD * vecNorm u * vecNorm v) := by gcongr
    _ = _ := by ring

end BlockBand.Transmission.PassiveCovariance
