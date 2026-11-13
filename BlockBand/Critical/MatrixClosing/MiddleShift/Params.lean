module

public import BlockBand.Critical.MatrixClosing.MiddleShift.Forms
public import BlockBand.Critical.MatrixClosing.MiddleShift.Identity
public import BlockBand.Critical.Collar.Density.EnergyStability
public import BlockBand.Critical.Collar.Kernel.Reduction
public import BlockBand.Critical.BoundaryMean.Phases

/-!
# The middle-only shifted collar mean: the reference change `(e, X) ↦ (e+s, X - s)`

* `sum_norm_sq_inv_mulVec_le`: `‖Z⁻¹q‖ ≤ η⁻¹‖q‖` when `Z - Z* = 2i(η + Y)`; `sum_norm_sq_add_le`;
  `re_trace_mul_mul_conjTranspose_le`: `Re Tr(MSM*) ≤ K Re Tr S` (`S ⪰ 0`, `‖Mv‖² ≤ K‖v‖²`).
* `shiftDefect b e s = z_b(e+s) + s - z_b(e)` (`Z = Z' - Δ`), `boundaryZ_sub_eq`, `hZZ_shift`.
* `matchedDistance_shift_le`: `d_{e+s}(X - s) ≤ d_e(X) + ‖Δ‖/(η'η) + ‖a(e+s) - a(e)‖`.
* `conductance_oldScattering_eq` (`g = 4η Re Tr(Z⁻¹YZ⁻*)`), `conductance_shift_le`:
  `g_{e+s}(X - s) ≤ (η'/η)(2 + 2‖Δ‖²/η'²) g_e(X)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

section Vec

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖Z⁻¹q‖² ≤ η⁻²‖q‖²` when `Z - Z* = 2i(ηI + Y)`, `Y ⪰ 0`. -/
theorem sum_norm_sq_inv_mulVec_le {Z Y : Matrix ι ι ℂ} {η : ℝ} (hη : 0 < η)
    (hY : Y.PosSemidef) (hZ : IsUnit Z.det)
    (hZZ : Z - Zᴴ = (2 * Complex.I) • ((η : ℂ) • (1 : Matrix ι ι ℂ) + Y)) (q : ι → ℂ) :
    ∑ i, ‖(Z⁻¹ *ᵥ q) i‖ ^ 2 ≤ (η ^ 2)⁻¹ * ∑ i, ‖q i‖ ^ 2 := by
  have hv : Z *ᵥ (Z⁻¹ *ᵥ q) = q := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hZ, one_mulVec]
  generalize Z⁻¹ *ᵥ q = v at hv ⊢
  have hconj : star v ⬝ᵥ (Zᴴ *ᵥ v) = star (star v ⬝ᵥ (Z *ᵥ v)) := by
    rw [dotProduct_mulVec, ← star_mulVec, star_dotProduct]
  have hdiff : star v ⬝ᵥ (Z *ᵥ v) - star (star v ⬝ᵥ (Z *ᵥ v)) =
      (2 * Complex.I) * (((η : ℂ) * (star v ⬝ᵥ v)) + star v ⬝ᵥ (Y *ᵥ v)) := by
    rw [← hconj, ← dotProduct_sub, ← sub_mulVec, hZZ, smul_mulVec, add_mulVec, smul_mulVec,
      one_mulVec, dotProduct_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hq : ‖star v ⬝ᵥ (Z *ᵥ v)‖ = ‖star v ⬝ᵥ q‖ := by rw [hv]
  generalize star v ⬝ᵥ (Z *ᵥ v) = a at hconj hdiff hq
  have hvv : (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
    have := quadForm_one v
    unfold quadForm at this
    rwa [one_mulVec] at this
  have hvvim : (star v ⬝ᵥ v).im = 0 := by
    simp only [dotProduct, Pi.star_apply, Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  have hYv : 0 ≤ quadForm Y v := WeightedDensity.quadForm_nonneg_of_posSemidef hY v
  have him : a.im = η * ∑ i, ‖v i‖ ^ 2 + quadForm Y v := by
    have h := congrArg Complex.im hdiff
    rw [Complex.star_def, Complex.sub_conj] at h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.add_re, Complex.mul_re, hvvim] at h
    unfold quadForm
    rw [← hvv]
    linarith
  have hnv : 0 ≤ ∑ i, ‖v i‖ ^ 2 := by positivity
  have hcs : ‖a‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) * ∑ i, ‖q i‖ ^ 2 := by
    have h1 : ‖a‖ ≤ ∑ i, ‖v i‖ * ‖q i‖ := by
      rw [hq]
      unfold dotProduct
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖v i‖) (fun i => ‖q i‖)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hlow : η * ∑ i, ‖v i‖ ^ 2 ≤ ‖a‖ := by
    have := Complex.abs_im_le_norm a
    rw [him] at this
    linarith [le_abs_self (η * ∑ i, ‖v i‖ ^ 2 + quadForm Y v)]
  have hsq : (η * ∑ i, ‖v i‖ ^ 2) ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) * ∑ i, ‖q i‖ ^ 2 :=
    (pow_le_pow_left₀ (by positivity) hlow 2).trans hcs
  rcases hnv.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith

omit [DecidableEq ι] in
theorem sum_norm_sq_add_le (u w : ι → ℂ) :
    ∑ i, ‖(u + w) i‖ ^ 2 ≤ 2 * ∑ i, ‖u i‖ ^ 2 + 2 * ∑ i, ‖w i‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := norm_add_le (u i) (w i)
  simp only [Pi.add_apply]
  have h2 : ‖u i + w i‖ ^ 2 ≤ (‖u i‖ + ‖w i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) this 2
  nlinarith [sq_nonneg (‖u i‖ - ‖w i‖)]

omit [DecidableEq ι] in
/-- `Re Tr(MSM*) ≤ K Re Tr S` for `S ⪰ 0` when `‖Mv‖² ≤ K‖v‖²` for every `v`. -/
theorem re_trace_mul_mul_conjTranspose_le {M S : Matrix ι ι ℂ} (hS : S.PosSemidef) {K : ℝ}
    (hM : ∀ v : ι → ℂ, ∑ i, ‖(M *ᵥ v) i‖ ^ 2 ≤ K * ∑ i, ‖v i‖ ^ 2) :
    (M * S * Mᴴ).trace.re ≤ K * S.trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hS
  have hvv : ∀ u : ι → ℂ, (vecMulVec u (star u)).trace.re = ∑ i, ‖u i‖ ^ 2 := by
    intro u
    simp only [trace, diag_apply, vecMulVec_apply, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
    norm_cast
  have hMvv : ∀ u : ι → ℂ, M * vecMulVec u (star u) * Mᴴ = vecMulVec (M *ᵥ u) (star (M *ᵥ u)) := by
    intro u
    rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]
  simp only [Matrix.mul_sum, Matrix.sum_mul, trace_sum, Complex.re_sum, hMvv, hvv]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => hM (v k)

end Vec

variable {W : ℕ}

/-- `Z - Z* = 2i(Im z + Y)` for `Z = z - X`, `Y = -Im X`. -/
theorem smul_one_sub_sub_conjTranspose (z : ℂ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (z • 1 - X) - (z • 1 - X)ᴴ = (2 * Complex.I) • ((z.im : ℂ) • (1 : Matrix (Fin 2 × Fin W) _ ℂ) +
      -imPart X) := by
  have hX := Collar.Kernel.rePart_sub_I_smul_neg_imPart X
  have hz : z - star z = (2 * Complex.I) * (z.im : ℂ) := by
    rw [Complex.star_def, Complex.sub_conj]; push_cast; ring
  simp only [conjTranspose_sub, conjTranspose_smul, conjTranspose_one]
  have hXh : X - Xᴴ = (2 * Complex.I) • imPart X := by
    simp only [imPart, smul_smul]
    rw [mul_inv_cancel₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero), one_smul]
  calc z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X - (star z • 1 - Xᴴ) =
      (z - star z) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - (X - Xᴴ) := by
        rw [sub_smul]; abel
    _ = _ := by rw [hz, hXh, smul_add, smul_neg, smul_smul, sub_eq_add_neg]

/-- The shift defect `Δ = z_b(e+s) + s - z_b(e)` (`Z = Z' - Δ`). -/
def shiftDefect (b e s : ℝ) : ℂ := boundaryZ b (e + s) + s - boundaryZ b e

theorem boundaryZ_sub_eq (b e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X =
      (boundaryZ b (e + s) • 1 - (X - (s : ℂ) • 1)) - shiftDefect b e s • 1 := by
  simp only [shiftDefect, add_smul, sub_smul]
  abel

theorem hZZ_shift (b e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (boundaryZ b (e + s) • 1 - (X - (s : ℂ) • 1)) - (boundaryZ b (e + s) • 1 - (X - (s : ℂ) • 1))ᴴ =
      (2 * Complex.I) • (((boundaryZ b (e + s)).im : ℂ) • (1 : Matrix (Fin 2 × Fin W) _ ℂ) +
        -imPart X) := by
  have : boundaryZ b (e + s) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - (X - (s : ℂ) • 1) =
      (boundaryZ b (e + s) + s) • 1 - X := by rw [add_smul]; abel
  rw [this, smul_one_sub_sub_conjTranspose]
  simp

/-- `|((z'-X')⁻¹(z-X)⁻¹)_{aa}| ≤ (η'η)⁻¹` for passive `X`. -/
theorem norm_inv_mul_inv_apply_le_passive {b e s : ℝ} (hη : 0 < (boundaryZ b e).im)
    (hη' : 0 < (boundaryZ b (e + s)).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-imPart X).PosSemidef) (a : Fin 2 × Fin W) :
    ‖((boundaryZ b (e + s) • 1 - (X - (s : ℂ) • 1))⁻¹ * (boundaryZ b e • 1 - X)⁻¹) a a‖ ≤
      ((boundaryZ b (e + s)).im * (boundaryZ b e).im)⁻¹ := by
  set Z := boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
  set Z' := boundaryZ b (e + s) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - (X - (s : ℂ) • 1)
  have hY' : (-imPart (X - (s : ℂ) • 1)).PosSemidef := by rwa [imPart_sub_smul_one]
  have hZu : IsUnit Z.det := Collar.Kernel.isUnit_det_boundaryZ_sub b e hη hY
  have hZ'u : IsUnit Z'.det := Collar.Kernel.isUnit_det_boundaryZ_sub b (e + s) hη' hY'
  have hZZ := smul_one_sub_sub_conjTranspose (boundaryZ b e) X
  have h1 := sum_norm_sq_inv_conjTranspose_mulVec_le hη' hY hZ'u (hZZ_shift b e s X)
    (Pi.single a 1)
  have h2 := sum_norm_sq_inv_mulVec_le hη hY hZu hZZ (Pi.single a 1)
  have hone : ∑ i, ‖(Pi.single a (1 : ℂ) : Fin 2 × Fin W → ℂ) i‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
    simp
  have e1 : ((Z'⁻¹)ᴴ *ᵥ Pi.single a 1) = fun k => star (Z'⁻¹ a k) := by
    ext k; simp [mulVec, dotProduct, Pi.single_apply, conjTranspose_apply]
  have e2 : (Z⁻¹ *ᵥ Pi.single a 1) = fun k => Z⁻¹ k a := by
    ext k; simp [mulVec, dotProduct, Pi.single_apply]
  rw [hone, mul_one, e1] at h1
  rw [hone, mul_one, e2] at h2
  simp only [norm_star] at h1
  rw [mul_apply]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖Z'⁻¹ a k‖) (fun k => ‖Z⁻¹ k a‖)
  have hle : ‖∑ k, Z'⁻¹ a k * Z⁻¹ k a‖ ≤ ∑ k, ‖Z'⁻¹ a k‖ * ‖Z⁻¹ k a‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp))
  have hsq : (∑ k, ‖Z'⁻¹ a k‖ * ‖Z⁻¹ k a‖) ^ 2 ≤
      (((boundaryZ b (e + s)).im * (boundaryZ b e).im)⁻¹) ^ 2 := by
    refine hcs.trans ?_
    rw [mul_inv, mul_pow, inv_pow, inv_pow]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  exact hle.trans ((pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq)

/-- **Scalar distance after the reference change** `(e, X) ↦ (e+s, X - s)`, passive `X`. -/
theorem matchedDistance_shift_le (hW : 0 < W) {b e s : ℝ} (hη : 0 < (boundaryZ b e).im)
    (hη' : 0 < (boundaryZ b (e + s)).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-imPart X).PosSemidef) :
    matchedDistance b (e + s) (X - (s : ℂ) • 1) ≤ matchedDistance b e X +
      ‖shiftDefect b e s‖ * ((boundaryZ b (e + s)).im * (boundaryZ b e).im)⁻¹ +
        ‖matchedA (e + s) - matchedA e‖ := by
  set Z := boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
  set Z' := boundaryZ b (e + s) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - (X - (s : ℂ) • 1)
  have hY' : (-imPart (X - (s : ℂ) • 1)).PosSemidef := by rwa [imPart_sub_smul_one]
  have hZu : IsUnit Z.det := Collar.Kernel.isUnit_det_boundaryZ_sub b e hη hY
  have hZ'u : IsUnit Z'.det := Collar.Kernel.isUnit_det_boundaryZ_sub b (e + s) hη' hY'
  have hdiff : Z'⁻¹ - Z⁻¹ = (-shiftDefect b e s) • (Z'⁻¹ * Z⁻¹) := by
    have hZ : Z = Z' - shiftDefect b e s • 1 := boundaryZ_sub_eq b e s X
    calc Z'⁻¹ - Z⁻¹ = Z'⁻¹ * (Z - Z') * Z⁻¹ := by
          rw [Matrix.mul_sub, Matrix.sub_mul, nonsing_inv_mul _ hZ'u, Matrix.one_mul,
            Matrix.mul_assoc, mul_nonsing_inv _ hZu, Matrix.mul_one]
      _ = _ := by
          rw [hZ, sub_sub_cancel_left, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one,
            Matrix.neg_mul, Matrix.smul_mul, neg_smul]
  have hbt : ∀ j : Fin 2, ‖blockTrace (Z'⁻¹) j - blockTrace (Z⁻¹) j‖ ≤
      ‖shiftDefect b e s‖ * ((boundaryZ b (e + s)).im * (boundaryZ b e).im)⁻¹ := by
    intro j
    rw [← BoundaryMean.blockTrace_sub, hdiff]
    refine Collar.Density.norm_blockTrace_le hW (fun a => ?_) j
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_left (norm_inv_mul_inv_apply_le_passive hη hη' hY a)
      (norm_nonneg _)
  have hj : ∀ j : Fin 2, ‖blockTrace (Z'⁻¹) j - matchedA (e + s)‖ ≤
      ‖blockTrace (Z⁻¹) j - matchedA e‖ +
        ‖shiftDefect b e s‖ * ((boundaryZ b (e + s)).im * (boundaryZ b e).im)⁻¹ +
          ‖matchedA (e + s) - matchedA e‖ := by
    intro j
    calc ‖blockTrace (Z'⁻¹) j - matchedA (e + s)‖ =
        ‖(blockTrace (Z⁻¹) j - matchedA e) + (blockTrace (Z'⁻¹) j - blockTrace (Z⁻¹) j) -
          (matchedA (e + s) - matchedA e)‖ := by ring_nf
      _ ≤ _ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact (norm_add_le _ _).trans (by gcongr; exact hbt j)
  have hd0 := hj 0
  have hd1 := hj 1
  unfold matchedDistance
  refine max_le (hd0.trans ?_) (hd1.trans ?_) <;> gcongr
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- `g = 4η Re Tr(Z⁻¹YZ⁻*)`, `Z = z - X`, passive `X`. -/
theorem conductance_oldScattering_eq (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosSemidef) :
    conductance (oldScattering b e X) = 4 * (boundaryZ b e).im *
      ((boundaryZ b e • 1 - X)⁻¹ * (-imPart X) * ((boundaryZ b e • 1 - X)⁻¹)ᴴ).trace.re := by
  have hZu := Collar.Kernel.isUnit_det_boundaryZ_sub b e hη hY
  have h := Collar.Kernel.one_sub_scattering_mul_conjTranspose hZu
    (smul_one_sub_sub_conjTranspose (boundaryZ b e) X)
  have h' : oldScattering b e X * (oldScattering b e X)ᴴ =
      1 - ((4 * (boundaryZ b e).im : ℝ) : ℂ) • ((boundaryZ b e • 1 - X)⁻¹ * (-imPart X) *
        ((boundaryZ b e • 1 - X)⁻¹)ᴴ) := h
  rw [conductance]
  have htr : (1 - (oldScattering b e X)ᴴ * oldScattering b e X).trace =
      (1 - oldScattering b e X * (oldScattering b e X)ᴴ).trace := by
    rw [trace_sub, trace_sub, trace_mul_comm]
  rw [htr, h', sub_sub_cancel, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- **Conductance after the reference change**, passive `X`:
`g(e+s, X-s) ≤ (η'/η)(2 + 2‖Δ‖²/η'²) g(e, X)`. -/
theorem conductance_shift_le {b e s : ℝ} (hη : 0 < (boundaryZ b e).im)
    (hη' : 0 < (boundaryZ b (e + s)).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-imPart X).PosSemidef) :
    conductance (oldScattering b (e + s) (X - (s : ℂ) • 1)) ≤
      (boundaryZ b (e + s)).im / (boundaryZ b e).im *
        (2 + 2 * ‖shiftDefect b e s‖ ^ 2 / (boundaryZ b (e + s)).im ^ 2) *
          conductance (oldScattering b e X) := by
  set η := (boundaryZ b e).im
  set η' := (boundaryZ b (e + s)).im
  set Δ := shiftDefect b e s
  set Z := boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
  set Z' := boundaryZ b (e + s) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - (X - (s : ℂ) • 1)
  have hY' : (-imPart (X - (s : ℂ) • 1)).PosSemidef := by rwa [imPart_sub_smul_one]
  have hZu : IsUnit Z.det := Collar.Kernel.isUnit_det_boundaryZ_sub b e hη hY
  have hZ'u : IsUnit Z'.det := Collar.Kernel.isUnit_det_boundaryZ_sub b (e + s) hη' hY'
  rw [conductance_oldScattering_eq b e hη hY, conductance_oldScattering_eq b (e + s) hη' hY',
    imPart_sub_smul_one]
  set M := 1 - Δ • Z'⁻¹
  have hZ'Z : Z'⁻¹ = M * Z⁻¹ := by
    have hZ : Z = Z' - Δ • 1 := boundaryZ_sub_eq b e s X
    have h1 : Z'⁻¹ * Z = M := by
      rw [hZ, Matrix.mul_sub, nonsing_inv_mul _ hZ'u, Matrix.mul_smul, Matrix.mul_one]
    calc Z'⁻¹ = Z'⁻¹ * Z * Z⁻¹ := by
          rw [Matrix.mul_assoc, mul_nonsing_inv _ hZu, Matrix.mul_one]
      _ = M * Z⁻¹ := by rw [h1]
  have hS : (Z⁻¹ * (-imPart X) * (Z⁻¹)ᴴ).PosSemidef := hY.mul_mul_conjTranspose_same _
  have hK : ∀ v : Fin 2 × Fin W → ℂ, ∑ i, ‖(M *ᵥ v) i‖ ^ 2 ≤
      (2 + 2 * ‖Δ‖ ^ 2 / η' ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
    intro v
    have hMv : M *ᵥ v = v + (-Δ) • (Z'⁻¹ *ᵥ v) := by
      show (1 - Δ • Z'⁻¹) *ᵥ v = _
      rw [sub_mulVec, one_mulVec, smul_mulVec, neg_smul, sub_eq_add_neg]
    have h1 := sum_norm_sq_add_le v ((-Δ) • (Z'⁻¹ *ᵥ v))
    have h2 := sum_norm_sq_inv_mulVec_le hη' hY hZ'u (hZZ_shift b e s X) v
    have h3 : ∑ i, ‖((-Δ) • (Z'⁻¹ *ᵥ v)) i‖ ^ 2 = ‖Δ‖ ^ 2 * ∑ i, ‖(Z'⁻¹ *ᵥ v) i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_neg, mul_pow]
    rw [hMv]
    have hη'2 : 0 < η' ^ 2 := by positivity
    calc _ ≤ 2 * ∑ i, ‖v i‖ ^ 2 + 2 * (‖Δ‖ ^ 2 * ∑ i, ‖(Z'⁻¹ *ᵥ v) i‖ ^ 2) := by rw [← h3]; exact h1
      _ ≤ 2 * ∑ i, ‖v i‖ ^ 2 + 2 * (‖Δ‖ ^ 2 * ((η' ^ 2)⁻¹ * ∑ i, ‖v i‖ ^ 2)) := by gcongr
      _ = _ := by field_simp
  have htr := re_trace_mul_mul_conjTranspose_le hS hK
  have hrw : Z'⁻¹ * (-imPart X) * (Z'⁻¹)ᴴ = M * (Z⁻¹ * (-imPart X) * (Z⁻¹)ᴴ) * Mᴴ := by
    rw [hZ'Z, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [hrw]
  have hTr : 0 ≤ (Z⁻¹ * (-imPart X) * (Z⁻¹)ᴴ).trace.re := by
    have := hS.trace_nonneg
    exact (Complex.nonneg_iff.1 this).1
  calc 4 * η' * (M * (Z⁻¹ * (-imPart X) * (Z⁻¹)ᴴ) * Mᴴ).trace.re ≤
      4 * η' * ((2 + 2 * ‖Δ‖ ^ 2 / η' ^ 2) * (Z⁻¹ * (-imPart X) * (Z⁻¹)ᴴ).trace.re) := by
        gcongr
    _ = η' / η * (2 + 2 * ‖Δ‖ ^ 2 / η' ^ 2) *
        (4 * η * (Z⁻¹ * (-imPart X) * (Z⁻¹)ᴴ).trace.re) := by
        field_simp

end BlockBand.Critical.MatrixClosing
