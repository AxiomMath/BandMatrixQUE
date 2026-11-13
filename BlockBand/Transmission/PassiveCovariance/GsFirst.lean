module

public import BlockBand.Transmission.PassiveCovariance.TqMatched
public import BlockBand.Transmission.PassiveCovariance.SdQExpand

/-!
# The `𝒢ᴴ`-first mean `m7_p = E[𝒢ᴴP_p𝒢]`, physical block

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive `X`,
fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` only, uniformly in `W ≥ W₀`, `X`, `p`.

* `blkTr_cyc`: `⟨(𝒢ᴴP_p𝒢)_qq⟩ = ⟨(𝒢P_q𝒢ᴴ)_pp⟩` pointwise, so `r_{pq} = t^q_p`.
* `opNorm_le_of_bilinear`: a uniform bilinear bound is an operator-norm bound.
* `mbarTrue_blk`: `M̄ᴴ = (D⁻¹)ᴴ` has blocks `(Mᴴ, 0)` in its first row.
* **`gsMean_block`**: `‖(E[𝒢ᴴP_p𝒢])₀₀ - rB_p·Mᴴ(E𝒢)₀₀‖ ≤ C/W²`, `rB_p = [p=0] + σ₁(r_p)`
  (`sdOne_expand` with `adj = true`, `P₀ = 1`, `N = P_p𝒢`).
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

/-- `⟨(Gᴴ P_p G)_qq⟩ = ⟨(G P_q Gᴴ)_pp⟩`. -/
theorem blkTr_cyc (G : LayerMat W) (p q : Fin 2) :
    SourceMixing.blkTr (Gᴴ * (bProj p * G)) q = SourceMixing.blkTr (G * (bProj q * Gᴴ)) p := by
  rw [SourceMixing.blkTr_def, SourceMixing.blkTr_def]
  congr 1
  rw [blkAt_mul, blkAt_mul, Fin.sum_univ_two, Fin.sum_univ_two, blkAt_bProj_mul, blkAt_bProj_mul,
    blkAt_bProj_mul, blkAt_bProj_mul, blkAt_conjTranspose, blkAt_conjTranspose,
    blkAt_conjTranspose, blkAt_conjTranspose]
  fin_cases p <;> fin_cases q <;> simp <;> exact Matrix.trace_mul_comm _ _

theorem opNorm_le_of_bilinear {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ u v : n → ℂ, ‖bilinear u A v‖ ≤ C * (vecNorm u * vecNorm v)) : ‖A‖ ≤ C := by
  refine opNorm_le_of_vec A hC fun x => ?_
  have hx := h (A *ᵥ x) x
  rw [bilinear, star_self_eq, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hx
  have h0 := vecNorm_nonneg (A *ᵥ x)
  have h1 := vecNorm_nonneg x
  rcases h0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

theorem mbarTrue_blk {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hW : 1 ≤ W)
    (hD : IsUnit (dressed b E X)) :
    blkAt (mbarSide b E X true) 0 0 = (SourceMixing.mOf b E X)ᴴ ∧
      blkAt (mbarSide b E X true) 0 1 = 0 := by
  have hinv : dressed b E X * (dressed b E X)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  obtain ⟨-, -, -, -, -, h10⟩ := blkAt_dressed_inv b E X hW _ hinv
  have e : mbarSide b E X true = ((dressed b E X)⁻¹)ᴴ := by
    show ((dressed b E X)ᴴ)⁻¹ = _
    rw [Matrix.conjTranspose_nonsing_inv]
  rw [e, blkAt_conjTranspose, blkAt_conjTranspose, h10, conjTranspose_zero]
  exact ⟨rfl, rfl⟩

/-- **The `𝒢ᴴ`-first mean, physical block.** -/
theorem gsMean_block (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) : LayerMat W) α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) 0 0 -
          rB b E X p • ((SourceMixing.mOf b E X)ᴴ *
            blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨Cs, Ws, hCs, hS⟩ := sdOne_expand hA hb0 hb h1 h2 1 1 true
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  obtain ⟨CK, WK, hCK, hK⟩ := SourceMixing.norm_kHat_dressedInv hA hb0 hb h1 h2
  obtain ⟨Cw, Ww, hCw, hw⟩ := SourceMixing.wordMean_bound hA hb0 hb h1 h2 2 1
  refine ⟨Cs * CD, max (max Ws WD) (max WK Ww), by positivity, fun W hW X hX p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWs, hWD⟩, hWK, hWw⟩ := hW
  obtain ⟨hW1, -, hM, -, -, -, -, -, hG, -, -⟩ := hD W hWD X hX
  obtain ⟨hU, -, -, -⟩ := hK W hWK X hX
  obtain ⟨m00, m01⟩ := mbarTrue_blk hW1 hU
  set μ := layerLaw W b .oneBlockOnePort
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set M := SourceMixing.mOf b E X
  have hent : ∀ α β, Integrable
      (fun ω => ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) : LayerMat W) α β) μ := fun α β => by
    have h := (hw W hWw X hX.posSemidef 2 le_rfl ![2, 0] (dP3 p) (norm_dP3_le p)).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2, 0] (dP3 p) α β) =
        fun ω => ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [dP3, wLetter]
    rw [e] at h; exact h
  refine ⟨hent, ?_⟩
  have hPG : ∀ α β, Integrable (fun ω => (bProj p * gRes b E X ω : LayerMat W) α β) μ :=
    fun α β => by
      simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun k _ => (hG k β).const_mul _
  refine opNorm_le_of_bilinear _ (by positivity) fun u v => ?_
  have h := hS W hWs X hX 1 le_rfl ![0] (dP p) (norm_dP_le p) 1 (physVec u) (physVec v)
  simp only at h
  -- the vector `x̌ = D⁻¹ι₁u = ι₁(Mu)`
  have hxc : (1 * mbarSide b E X true)ᴴ *ᵥ physVec u = physVec (M *ᵥ u) := by
    rw [Matrix.one_mul, conjT_mulVec_physVec m01, m00, conjTranspose_conjTranspose]
  rw [hxc] at h
  -- first term
  have e1 : ∀ ω, star (physVec u) ⬝ᵥ ((1 * gSide b E X true ω *
      wordVal (kHat b E X) (gRes b E X ω) ![0] (dP p)) *ᵥ physVec v) =
      star (physVec u) ⬝ᵥ (((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)) *ᵥ physVec v) :=
    fun ω => by rw [wordVal_PpG, Matrix.one_mul]; rfl
  simp only [e1] at h
  rw [integral_form _ hent] at h
  -- second term
  have e2 : ∀ ω, star (physVec u) ⬝ᵥ ((1 * mbarSide b E X true *
      wordVal (kHat b E X) (gRes b E X ω) ![0] (dP p)) *ᵥ physVec v) =
      star (physVec u) ⬝ᵥ ((mbarSide b E X true * (bProj p * gRes b E X ω)) *ᵥ physVec v) :=
    fun ω => by rw [wordVal_PpG, Matrix.one_mul]
  simp only [e2] at h
  have hMPG : ∀ α β, Integrable
      (fun ω => (mbarSide b E X true * (bProj p * gRes b E X ω) : LayerMat W) α β) μ :=
    fun α β => by
      simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun k _ => (hPG k β).const_mul _
  rw [integral_form _ hMPG, ← SourceMixing.mul_matrixExpect' _ _ hPG,
    ← SourceMixing.mul_matrixExpect' _ _ hG, blkAt_mul, Fin.sum_univ_two, m00, m01,
    Matrix.zero_mul, add_zero, blkAt_bProj_mul] at h
  -- third term
  have e3 : ∀ q : Fin 2, (∫ ω, SourceMixing.blkTr (gSide b E X true ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) q ∂μ) = tP b E X q p := fun q => by
    have e : ∀ ω, SourceMixing.blkTr (gSide b E X true ω *
        wordAlpha (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) q =
        SourceMixing.blkTr (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ)) p := fun ω => by
      rw [wordAlpha_PpG]; exact blkTr_cyc _ p q
    simp only [e]; rfl
  have e4 : ∀ q : Fin 2, (∫ ω, star (physVec (M *ᵥ u)) ⬝ᵥ ((dRow b q *
      wordGamma (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) *ᵥ physVec v) ∂μ) =
      sRow b q * bilinear u (Mᴴ * G0) v := fun q => by
    have e : ∀ ω, star (physVec (M *ᵥ u)) ⬝ᵥ ((dRow b q *
        wordGamma (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) *ᵥ physVec v) =
        sRow b q * star (physVec (M *ᵥ u)) ⬝ᵥ (gRes b E X ω *ᵥ physVec v) := fun ω => by
      rw [wordGamma_PpG]; exact form_dRow q (isPhys_physVec _) _ _
    simp only [e]
    rw [integral_const_mul, integral_form _ hG, ← bilinear_conjT_left, conjTranspose_conjTranspose]
  rw [Fin.sum_univ_one, Fin.sum_univ_two, e3, e3, e4, e4] at h
  rw [vecNorm_physVec, vecNorm_physVec] at h
  -- assemble
  have hrB : rB b E X p = ind 0 p + (sRow b 0 * tP b E X 0 p + sRow b 1 * tP b E X 1 p) := by
    rw [sRow_zero, sRow_one]; simp only [rB, sig1]; push_cast; ring
  have eq : bilinear u (blkAt (matrixExpect μ
      (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) 0 0 - rB b E X p • (Mᴴ * G0)) v =
      bilinear u (blkAt (matrixExpect μ
        (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) 0 0) v -
      bilinear u (Mᴴ * (ind 0 p • G0)) v -
      (tP b E X 0 p * (sRow b 0 * bilinear u (Mᴴ * G0) v) +
        tP b E X 1 p * (sRow b 1 * bilinear u (Mᴴ * G0) v)) := by
    rw [bilinear_sub, bilinear_smul, Matrix.mul_smul, bilinear_smul, hrB]
    change _ = _ - (if (0 : Fin 2) = p then (1 : ℂ) else 0) * _ - _
    simp only [ind]; ring
  rw [eq]
  have hMu : vecNorm (M *ᵥ u) ≤ CD * vecNorm u := (vecNorm_mulVec_le M u).trans
    (mul_le_mul_of_nonneg_right hM (vecNorm_nonneg u))
  refine h.trans ?_
  have := vecNorm_nonneg v
  calc Cs / (W : ℝ) ^ 2 * (vecNorm (M *ᵥ u) * vecNorm v) ≤
      Cs / (W : ℝ) ^ 2 * (CD * vecNorm u * vecNorm v) := by gcongr
    _ = _ := by ring

end BlockBand.Transmission.PassiveCovariance
