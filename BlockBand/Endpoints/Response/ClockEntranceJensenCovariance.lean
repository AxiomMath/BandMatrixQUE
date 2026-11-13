module

public import BlockBand.Endpoints.Response.ClockEntranceLayerLogistic
public import BlockBand.Transmission.PositiveResolvent

/-!
# The clock covariance gap in an arbitrary orthonormal basis

This file proves `cej_covariance_gap`: for retained indices `i, j` (with `T_ii, T_jj ≤ 1/2`) in the
orthonormal basis given by the columns of any unitary `V`, the fresh layer `U = LL*` satisfies
`E_ν|(V*(U - E_νU)V)_{ij}|² ≥ κ/W`.

* `cej_isUnit_K`, `cej_reflection_gram`: for passive `X` (`-Im X ⪰ 0`) and `η = Im z > 0`,
  `K = z - X` is invertible and the old reflection `r = I - 2iηR` satisfies `r*r = I - T`.
* `cej_reflection_eq`: the fast source is `f = -(2iη)⁻¹ r`, i.e. `r = -(2iη) f`.
* `cej_diag_source_sq_le`: the diagonal inequality `|r_ii| ≤ √S_ii`, `S = I - T`, in every
  orthonormal basis, in the form `4η²|f_ii|² ≤ 1 - T_ii`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder ComplexConjugate
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionLaws

variable {W : ℕ}

/-- `Im(z - X) = Y + η` (`Y = -Im X`, `η = Im z`). -/
theorem cej_imPart_K (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    BlockBand.Transmission.matrixImaginaryPart
        (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) =
      passiveY X + etaZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  ext i j
  simp only [BlockBand.Transmission.matrixImaginaryPart, passiveY, etaZ, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, conjTranspose_apply, Matrix.one_apply,
    conjTranspose_sub, conjTranspose_smul, conjTranspose_one, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte, mul_one]
    refine Complex.ext ?_ ?_ <;> simp [Complex.conj_re, Complex.conj_im]
    all_goals ring
  · simp only [h, ↓reduceIte, mul_zero]
    refine Complex.ext ?_ ?_ <;> simp
    all_goals ring

/-- `K - K* = 2iη + 2iY`. -/
theorem cej_balance_K (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) -
        star (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) =
      (2 * Complex.I * ((etaZ b E : ℝ) : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ) +
        (2 * Complex.I) • passiveY X := by
  ext i j
  simp only [BlockBand.Transmission.matrixImaginaryPart, passiveY, etaZ, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, star_apply, Matrix.one_apply,
    conjTranspose_apply, smul_eq_mul, star_sub, star_smul, star_one]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte, mul_one]
    refine Complex.ext ?_ ?_ <;> simp [Complex.conj_re, Complex.conj_im]
    all_goals ring
  · simp only [h, ↓reduceIte, mul_zero]
    refine Complex.ext ?_ ?_ <;> simp
    all_goals ring

/-- For passive `X` and `η > 0`, `K = z - X` is invertible (`Im K = Y + η ≻ 0`). -/
theorem cej_isUnit_K {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) ∧
      (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * passiveResolvent b E X = 1 ∧
      passiveResolvent b E X * (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) = 1 :=
  BlockBand.Transmission.passive_inverse_constructed _ _ (pfi_boundaryZ_im_pos hb hE1 hE2) hX
    (cej_imPart_K b E X)

/-- `r*r = I - T` for the old reflection `r = I - 2iηR` of a passive `X`. -/
theorem cej_reflection_gram {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    star (1 - (2 * Complex.I * ((etaZ b E : ℝ) : ℂ)) • passiveResolvent b E X) *
        (1 - (2 * Complex.I * ((etaZ b E : ℝ) : ℂ)) • passiveResolvent b E X) =
      1 - passiveTransmission b E X := by
  have hi := cej_isUnit_K hb hE1 hE2 hX
  have h := BlockBand.Transmission.passive_scattering_physical _ (passiveResolvent b E X)
    (passiveY X) (etaZ b E) hi.2.1 (cej_balance_K b E X)
  have hT : passiveTransmission b E X =
      (4 * ((etaZ b E : ℝ) : ℂ)) • (star (passiveResolvent b E X) * passiveY X *
        passiveResolvent b E X) := by
    unfold passiveTransmission passiveQ
    push_cast
    rfl
  rw [hT, ← h, sub_sub_cancel]

/-- The fast source `f = -(2iη)⁻¹ r`, i.e. `r = -(2iη) f`. -/
theorem cej_reflection_eq {b E : ℝ} (hη : 0 < etaZ b E) (X : Matrix (Fin W) (Fin W) ℂ) :
    1 - (2 * Complex.I * ((etaZ b E : ℝ) : ℂ)) • passiveResolvent b E X =
      -((2 * Complex.I * ((etaZ b E : ℝ) : ℂ)) • passiveF b E X) := by
  have hc : (2 * Complex.I * ((etaZ b E : ℝ) : ℂ)) ≠ 0 := by
    simp [hη.ne']
  rw [passiveF, cZero, smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul]
  abel

/-- The diagonal inequality `|r_ii| ≤ √S_ii` in the orthonormal basis of the columns of a unitary
`V`, as `4η²|f_ii|² ≤ 1 - T_ii`. -/
theorem cej_diag_source_sq_le {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V ∈ unitaryGroup (Fin W) ℂ) (i : Fin W) :
    4 * etaZ b E ^ 2 * ‖(star V * passiveF b E X * V) i i‖ ^ 2 ≤
      1 - ((star V * passiveTransmission b E X * V) i i).re := by
  have hη := pfi_boundaryZ_im_pos hb hE1 hE2
  set r := 1 - (2 * Complex.I * ((etaZ b E : ℝ) : ℂ)) • passiveResolvent b E X
  set N := star V * r * V
  have hV1 : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  have hV2 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hNN : star N * N = 1 - star V * passiveTransmission b E X * V := by
    have : star N * N = star V * (star r * r) * V := by
      simp only [N, star_mul, star_star, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc V (star V) (r * V), hV1, Matrix.one_mul]
    rw [this, cej_reflection_gram hb hE1 hE2 hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      hV2]
  have hNi : N i i = -(2 * Complex.I * ((etaZ b E : ℝ) : ℂ)) * (star V * passiveF b E X * V) i i := by
    simp only [N, r, cej_reflection_eq hη X, Matrix.mul_neg, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, neg_mul]
  have hdiag : ((star N * N) i i).re = ∑ k, ‖N k i‖ ^ 2 := by
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_apply, Complex.star_def, Complex.conj_mul']
    norm_cast
  have hle : ‖N i i‖ ^ 2 ≤ ∑ k, ‖N k i‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖N k i‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
  have hnorm : ‖N i i‖ ^ 2 = 4 * etaZ b E ^ 2 * ‖(star V * passiveF b E X * V) i i‖ ^ 2 := by
    rw [hNi, norm_mul, norm_neg, mul_pow]
    congr 1
    simp [Complex.norm_real, abs_of_pos hη, etaZ]
    ring
  have h1 : ((star N * N) i i).re = 1 - ((star V * passiveTransmission b E X * V) i i).re := by
    rw [hNN, Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re]
  linarith [hdiag, h1, hle, hnorm]

/-- Bilinear forms between columns of `V` are the entries of `V*MV`. -/
theorem cej_bilinear_col (V M : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) :
    bilinear (fun a => V a i) M (fun a => V a j) = (star V * M * V) i j := by
  simp only [bilinear, dotProduct, mulVec, Matrix.mul_apply, star_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/-- The columns of a unitary matrix are unit vectors. -/
theorem cej_vecNorm_col {V : Matrix (Fin W) (Fin W) ℂ} (hV : V ∈ unitaryGroup (Fin W) ℂ)
    (i : Fin W) : vecNorm (fun a => V a i) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hV) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ∑ a, ‖V a i‖ ^ 2 = 1 := by
    have := congrArg Complex.re h
    rw [Complex.re_sum, Complex.one_re] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_apply, Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [vecNorm, h2, Real.sqrt_one]

/-- The entrywise mean of a Hermitian random matrix is Hermitian. -/
theorem cej_matrixExpect_isHermitian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {U : Ω → Matrix (Fin W) (Fin W) ℂ} (hU : ∀ ω, (U ω).IsHermitian) :
    (matrixExpect μ U).IsHermitian := by
  ext a c
  simp only [conjTranspose_apply, matrixExpect, Matrix.of_apply]
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have := congrFun (congrFun (hU ω) a) c
  simp only [conjTranspose_apply] at this
  simpa [Complex.star_def] using this

/-- `D₀ · 2η² = σ₊`, i.e. `D₀/2 = σ₊/(4η²)`. -/
theorem cej_D0_eq {b E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (hb0 : 0 < b) :
    transportD0 b E * (2 * etaZ b E ^ 2) = sigmaPlus b := by
  have he : E ^ 2 ≤ 4 := by nlinarith
  have h : etaZ b E = (1 - b) * Real.sqrt (4 - E ^ 2) / 2 := by
    rw [etaZ, boundaryZ, Complex.add_im, Complex.inv_im, pfi_matchedA_normSq he, Complex.mul_im]
    simp [matchedA]
    ring
  have h4 : 0 < 4 - E ^ 2 := by nlinarith
  have hs := Real.sq_sqrt h4.le
  rw [h, transportD0, sigmaPlus, kPlus]
  field_simp
  rw [hs]
  ring

/-- The scalar inequality behind the covariance gap: with `4η²x² ≤ S_i`, `4η²y² ≤ S_j`,
`D₀·2η² = σ₊` and `S_i + S_j ≥ 1`,
`D₀/(2W)(S_i + S_j) - 2|σ₋|xy/W ≥ κ₀/W`, `κ₀ = (σ₊ - |σ₋|)/(4η²)`. -/
theorem cej_gap_scalar {η D₀ σp σm x y Si Sj w : ℝ} (hη : 0 < η) (hw : 0 < w) (hσm : 0 ≤ σm)
    (hσ : σm < σp) (hxS : 4 * η ^ 2 * x ^ 2 ≤ Si)
    (hyS : 4 * η ^ 2 * y ^ 2 ≤ Sj) (hD : D₀ * (2 * η ^ 2) = σp) (hS : 1 ≤ Si + Sj) :
    (σp - σm) / (4 * η ^ 2) / w ≤ D₀ / (2 * w) * (Si + Sj) - 2 * σm * (x * y) / w := by
  have h4 : 0 < 4 * η ^ 2 := by positivity
  have hxy : 8 * η ^ 2 * (x * y) ≤ Si + Sj := by nlinarith [sq_nonneg (x - y)]
  rw [div_div, div_le_iff₀ (by positivity)]
  have e : (D₀ / (2 * w) * (Si + Sj) - 2 * σm * (x * y) / w) * (4 * η ^ 2 * w) =
      σp * (Si + Sj) - σm * (8 * η ^ 2 * (x * y)) := by
    field_simp
    rw [← hD]
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hxy hσm]

/-- , in **every** orthonormal basis (the
columns of a unitary `V`): from the `PassiveCovarianceContract` with
`v₁ = v₄ = u_i`, `v₂ = v₃ = u_j` and `σ₊ > |σ₋|` (`TransmissionLawContract.jetGap`),
there are `κ, d > 0`, `W₀` (depending on `b, E, s` only) with
`κ/W ≤ E_ν|(V*(LL* - E_νLL*)V)_ij|²` whenever `(V*TV)_ii, (V*TV)_jj ≤ 1/2`, for every passive
`X` in the jet domain of radius `d`.
The main term is
`σ₊(S_ii+S_jj)/(4η²W) - Re(σ₋r_iir_jj)/(2η²W) ≥ (σ₊-|σ₋|)(S_ii+S_jj)/(4η²W)` with
`S = I - T`, `f = -(2iη)⁻¹r`, `|r_ii| ≤ √S_ii`; the remainder
`C[W⁻² + W⁻¹(δ₀ + δ₁ + q/W)]`, `q = g/(4η) ≤ dW/(4η)`, costs at most half.
-/
theorem cej_covariance_gap (hPC : PassiveCovarianceContract) (hTL : TransmissionLawContract)
    {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {s : ℂ}
    (hs : IsStationaryJet b E s) :
    ∃ (κ d : ℝ) (W₀ : ℕ), 0 < κ ∧ 0 < d ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, cel_InJetDomain b E s d X →
        ∀ V : Matrix (Fin W) (Fin W) ℂ, V ∈ unitaryGroup (Fin W) ℂ → ∀ i j : Fin W,
          ((star V * passiveTransmission b E X * V) i i).re ≤ 1 / 2 →
          ((star V * passiveTransmission b E X * V) j j).re ≤ 1 / 2 →
            κ / W ≤ ∫ ν, ‖(star V * (freshU b E X ν -
              matrixExpect (freshLaw W b) (freshU b E X)) * V) i j‖ ^ 2 ∂freshLaw W b := by
  have hb1' : b < 1 := by linarith
  have hη : 0 < etaZ b E := pfi_boundaryZ_im_pos hb1' hE1 hE2
  obtain ⟨C, W₁, hC⟩ := (hPC b hb0 hb1 E hE1 hE2).2 s hs
  have hgap := (hTL.jetGap b hb0 hb1 E hE1 hE2).2 s hs
  set η := etaZ b E with hηdef
  set σ := sigmaMinus b E s
  set κ₀ := (sigmaPlus b - ‖σ‖) / (4 * η ^ 2) with hκ₀def
  have hκ₀ : 0 < κ₀ := div_pos (by linarith) (by positivity)
  set A := 2 + 1 / (4 * η)
  have hA : 0 < A := by positivity
  set C' := |C|
  have hC' : 0 ≤ C' := abs_nonneg C
  refine ⟨κ₀ / 2, κ₀ / (4 * (C' * A + 1)), max W₁ (⌈4 * C' / κ₀⌉₊ + 1), by positivity,
    by positivity, ?_⟩
  intro W hW X hX V hV i j hi hj
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : ⌈4 * C' / κ₀⌉₊ + 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWpos : (0 : ℝ) < W := by
    have : 1 ≤ W := by omega
    exact_mod_cast this
  have hCW : C' / W ≤ κ₀ / 4 := by
    have h1 : 4 * C' / κ₀ ≤ W := by
      have := Nat.le_ceil (4 * C' / κ₀)
      have h2 : ((⌈4 * C' / κ₀⌉₊ : ℕ) : ℝ) ≤ W := by
        exact_mod_cast (by omega : ⌈4 * C' / κ₀⌉₊ ≤ W)
      linarith
    rw [div_le_iff₀ hWpos]
    rw [div_le_iff₀ hκ₀] at h1
    nlinarith
  set d := κ₀ / (4 * (C' * A + 1))
  have hd : C' * A * d ≤ κ₀ / 4 := by
    simp only [d]
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hC' hA.le]
  obtain ⟨hY, hδ0, hδ1, hg⟩ := hX
  -- the vectors
  set u : Fin W → Fin W → ℂ := fun k a => V a k
  set Ubar := matrixExpect (freshLaw W b) (freshU b E X)
  set M : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ :=
    fun ν => star V * (freshU b E X ν - Ubar) * V
  have hMh : ∀ ν, (M ν).IsHermitian := fun ν => by
    have h1 : (freshU b E X ν - Ubar).IsHermitian :=
      (isHermitian_mul_conjTranspose_self _).sub
        (cej_matrixExpect_isHermitian _ fun ν => isHermitian_mul_conjTranspose_self _)
    have := isHermitian_conjTranspose_mul_mul V h1
    simpa only [M, star_eq_conjTranspose] using this
  have hMji : ∀ ν, M ν j i = star (M ν i j) := fun ν => by
    have := congrFun (congrFun (hMh ν) j) i
    simpa only [conjTranspose_apply] using this.symm
  have hcov := hC W hW1 X hY (u i) (u j) (u j) (u i)
  simp only [] at hcov
  have hcovE : bilinearCovariance (freshLaw W b) (freshU b E X) (u i) (u j) (u j) (u i) =
      ((∫ ν, ‖M ν i j‖ ^ 2 ∂freshLaw W b : ℝ) : ℂ) := by
    rw [bilinearCovariance]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)).trans integral_ofReal
    simp only [u]
    rw [cej_bilinear_col, cej_bilinear_col]
    change M ν i j * M ν j i = _
    rw [hMji, Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  have hfour : fourNorm (u i) (u j) (u j) (u i) = 1 := by
    simp only [fourNorm, u, cej_vecNorm_col hV, mul_one]
  rw [hfour, mul_one, hcovE] at hcov
  -- the main term
  set T := passiveTransmission b E X
  set f := passiveF b E X
  set D := star V * T * V
  set F := star V * f * V
  have hb11 : ∀ k, bilinear (u k) (1 : Matrix (Fin W) (Fin W) ℂ) (u k) = 1 := fun k => by
    simp only [u]
    rw [cej_bilinear_col, Matrix.mul_one, Matrix.mem_unitaryGroup_iff'.mp hV, Matrix.one_apply_eq]
  have hbS : ∀ k, bilinear (u k) (1 - T) (u k) = 1 - D k k := fun k => by
    simp only [u]
    rw [cej_bilinear_col, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mem_unitaryGroup_iff'.mp hV, Matrix.sub_apply, Matrix.one_apply_eq]
  have hbf : ∀ k, bilinear (u k) f (u k) = F k k := fun k => by
    simp only [u]; rw [cej_bilinear_col]
  have hbfh : ∀ k, bilinear (u k) fᴴ (u k) = star (F k k) := fun k => by
    simp only [u]
    rw [cej_bilinear_col]
    have : star V * fᴴ * V = (star V * f * V)ᴴ := by
      rw [conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [this, conjTranspose_apply]
  set main : ℂ := (((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
        (crossedTensor (u i) (u j) (u j) (u i) 1 (1 - T) +
          crossedTensor (u i) (u j) (u j) (u i) (1 - T) 1) +
      σ / W * crossedTensor (u i) (u j) (u j) (u i) f f +
      conj σ / W * crossedTensor (u i) (u j) (u j) (u i) fᴴ fᴴ with hmain
  have hmain' : main = (((transportD0 b E / (2 * W) : ℝ)) : ℂ) * ((1 - D j j) + (1 - D i i)) +
      (σ / W * (F i i * F j j) + conj (σ / W * (F i i * F j j))) := by
    rw [hmain]
    simp only [crossedTensor, hb11, hbS, hbf, hbfh, one_mul, mul_one, map_mul, map_div₀,
      Complex.conj_natCast, Complex.star_def]
    ring
  have hre : (main).re ≥ transportD0 b E / (2 * W) *
      ((1 - (D i i).re) + (1 - (D j j).re)) - 2 * ‖σ‖ * (‖F i i‖ * ‖F j j‖) / W := by
    rw [hmain', Complex.add_re, Complex.add_re, Complex.conj_re, Complex.re_ofReal_mul]
    have h1 : -(‖σ / W * (F i i * F j j)‖) ≤ (σ / W * (F i i * F j j)).re := by
      have := Complex.abs_re_le_norm (σ / W * (F i i * F j j))
      linarith [neg_abs_le (σ / W * (F i i * F j j)).re]
    have h2 : ‖σ / W * (F i i * F j j)‖ = ‖σ‖ * (‖F i i‖ * ‖F j j‖) / W := by
      rw [norm_mul, norm_div, norm_mul, Complex.norm_natCast]
      ring
    have h3 : ((1 - D j j) + (1 - D i i)).re = (1 - (D i i).re) + (1 - (D j j).re) := by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re]; ring
    rw [h3]
    rw [h2] at h1
    have : 2 * ‖σ‖ * (‖F i i‖ * ‖F j j‖) / W = 2 * (‖σ‖ * (‖F i i‖ * ‖F j j‖) / W) := by ring
    linarith
  have hmainlow : κ₀ / W ≤ (main).re := by
    refine le_trans ?_ hre
    have hxi := cej_diag_source_sq_le hb1' hE1 hE2 hY hV i
    have hxj := cej_diag_source_sq_le hb1' hE1 hE2 hY hV j
    have := cej_gap_scalar (D₀ := transportD0 b E) (σp := sigmaPlus b) (σm := ‖σ‖)
      (Si := 1 - (D i i).re) (Sj := 1 - (D j j).re) hη hWpos (norm_nonneg _) hgap
      hxi hxj (cej_D0_eq hE1 hE2 hb0)
      (by simp only [D, T] at hi hj ⊢; linarith)
    simpa only [hκ₀def] using this
  -- the remainder
  have hq : passiveMass b E X / W ≤ d / (4 * η) := by
    have hgq : conductanceOf T = 4 * η * passiveMass b E X := by
      simp only [conductanceOf, T, passiveTransmission, passiveMass, Matrix.trace_smul,
        smul_eq_mul, Complex.re_ofReal_mul]
      rfl
    have : 4 * η * passiveMass b E X ≤ d * W := by rw [← hgq]; exact hg
    rw [div_le_div_iff₀ hWpos (by positivity)]
    nlinarith
  have hq0 : 0 ≤ passiveMass b E X := by
    have hgq : conductanceOf T = 4 * η * passiveMass b E X := by
      simp only [conductanceOf, T, passiveTransmission, passiveMass, Matrix.trace_smul,
        smul_eq_mul, Complex.re_ofReal_mul]
      rfl
    have := cel_conductance_nonneg hb1' hE1 hE2 hY (W := W)
    have h4 : 0 < 4 * η := by positivity
    nlinarith
  set β := (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
      (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)
  have hβ0 : 0 ≤ β := by
    have := norm_nonneg ((W : ℂ)⁻¹ * (passiveResolvent b E X).trace - matchedA E)
    have h0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have h1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    positivity
  have hβ : C' * β ≤ κ₀ / (2 * W) := by
    have hb' : β ≤ (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (A * d) := by
      have : jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W ≤ A * d := by
        have e : A * d = d + d + d / (4 * η) := by simp only [A]; field_simp; ring
        rw [e]; linarith
      have hWi : 0 ≤ (W : ℝ)⁻¹ := by positivity
      simp only [β]
      gcongr
    calc C' * β ≤ C' * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (A * d)) := mul_le_mul_of_nonneg_left hb' hC'
      _ = (C' / W) * (W : ℝ)⁻¹ + (C' * A * d) * (W : ℝ)⁻¹ := by ring
      _ ≤ (κ₀ / 4) * (W : ℝ)⁻¹ + (κ₀ / 4) * (W : ℝ)⁻¹ := by gcongr
      _ = κ₀ / (2 * W) := by field_simp; ring
  have hCβ : C * β ≤ C' * β := mul_le_mul_of_nonneg_right (le_abs_self C) hβ0
  have hfinal : (main).re - ‖((∫ ν, ‖M ν i j‖ ^ 2 ∂freshLaw W b : ℝ) : ℂ) - main‖ ≤
      ∫ ν, ‖M ν i j‖ ^ 2 ∂freshLaw W b := by
    have := Complex.abs_re_le_norm (((∫ ν, ‖M ν i j‖ ^ 2 ∂freshLaw W b : ℝ) : ℂ) - main)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith [le_abs_self ((∫ ν, ‖M ν i j‖ ^ 2 ∂freshLaw W b) - (main).re),
      neg_abs_le ((∫ ν, ‖M ν i j‖ ^ 2 ∂freshLaw W b) - (main).re)]
  have hcov' : ‖((∫ ν, ‖M ν i j‖ ^ 2 ∂freshLaw W b : ℝ) : ℂ) - main‖ ≤ C * β := hcov
  have e2 : κ₀ / 2 / W = κ₀ / W - κ₀ / (2 * W) := by field_simp; ring
  rw [e2]
  change κ₀ / W - κ₀ / (2 * W) ≤ ∫ ν, ‖M ν i j‖ ^ 2 ∂freshLaw W b
  linarith

end BlockBand.Endpoints
