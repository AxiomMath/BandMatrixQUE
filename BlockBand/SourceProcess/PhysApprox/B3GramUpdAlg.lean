module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormStep
public import BlockBand.SourceProcess.PhysApprox.B3GramStepClosed
public import BlockBand.SourceProcess.ComplexSourceLaw.Algebra
public import BlockBand.SourceProcess.CompleteSourceGap.LayerIds

/-!
# The closed Gram step at one sample (deterministic algebra)

For one sample and one phase `z` with the almost-sure invertibilities, at a step `l → l+1`,
`l ≥ 1`. Notation: `𝒰 = boundaryToInterior`, `C = physClosingMapAt`, `ι = nearSel`,
`Gcl = gclAt`, `K = z_∂ − X_cl`, `𝒢 = 𝒢₁₁(X_cl, F_l)`,
`U' = 𝒰Cιᴴ`, `V' = ι𝕊(1 + Z)𝒰ᴴ`.

* `gcl_succ_blocks`: the grown closed interior inverse, newest block first, is
  `[[𝒢, 𝒢KV'], [U'K𝒢, Gcl + U'ΔV']]` with `Δ = K𝒢K − K`, and the old rows of the grown closed
  near column `𝒰'C'ιᴴ` are `−z_∂⁻¹U'K𝒢B_{l+1}` (the proof of ClosedForm's `closedK_step`,
  continued by `gcl_mul_near` at length `l + 1`);
* `closed_interior_gram`: **the closed interior Ward identity** `𝒰CCᴴ𝒰ᴴ = c(Gcl − Gclᴴ)`,
  `c = −(2iη)⁻¹` (`gramC`), from `G − Gᴴ = (z̄_∂ − z_∂)𝒰𝒰ᴴ` and `CCᴴ = 1 + Z + Zᴴ`;
* `freshL_eq_neg`: `L = −z_∂⁻¹K𝒢₁₁B`;
* **`closedGram_step_vec`**: for interior vectors `g` (length `l`) and `g'` (length `l + 1`,
  zero on the newest block, `g` on the old blocks), with `x = 𝒰ᴴg`, `x' = 𝒰'ᴴg'`:
  `(C'ᴴx'_k)ᴴ(C'ᴴx'_l) − (Cᴴx_k)ᴴ(Cᴴx_l) = c u_k*Δv_l + (c u_l*Δv_k)^*` and
  `(ιC'ᴴx'_k)ᴴ(ιC'ᴴx'_l) − u_k*u_l = u_k*(U − 1)u_l`, with `u = ιCᴴx`, `v = ι𝕊(1 + Z)x`,
  `Δ = Δ(X_cl, F_l)`, `U = U(X_cl, F_l)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.PhysApprox.ClosedForm
open scoped ComplexOrder ComplexConjugate

variable {W : ℕ}

namespace GramUpd

/-- `U' = 𝒰Cιᴴ` at length `n`. -/
def nearU (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) (z : ℂ) : Matrix (Fin n × Fin W) (Fin W) ℂ :=
  boundaryToInterior b E W n ω * (physClosingMapAt b E s h W n ω z * (nearSel W)ᴴ)

/-- `V' = ι𝕊(1 + Z)𝒰ᴴ` at length `n`. -/
def nearV (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) (z : ℂ) : Matrix (Fin W) (Fin n × Fin W) ℂ :=
  nearSel W * (scatteringMatrix b E W n ω *
    ((1 + physClosingZAt b E s h W n ω z) * (boundaryToInterior b E W n ω)ᴴ))

/-- `K = z_∂ − X_cl` at length `n`. -/
def closedK (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) (z : ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - closedNearX b E s h W n ω z

/-- `𝒢 = 𝒢₁₁(X_cl, F_n)`. -/
def closedG (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) (z : ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  g11 E (boundaryZ b E) (closedNearX b E s h W n ω z) (freshSample W n ω)

/-!
## The grown closed interior inverse
-/

/-- **The grown closed interior inverse and the old rows of the grown closed near column**
(ClosedForm's `closedK_step`, continued). -/
theorem gcl_succ_blocks (b E s h : ℝ) {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W) (z : ℂ)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W l ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (l + 1) ω) - (E : ℂ) • 1))
    (hB : IsUnit (ω.2 (l + 1)))
    (hU : IsUnit (1 - z • closingN (scatteringMatrix b E W l ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (hU' : IsUnit (1 - z • closingN (scatteringMatrix b E W (l + 1) ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (hY : IsUnit (1 - (z * (star (boundaryZ b E) / boundaryZ b E)) •
      farEmbed (closingPairing b E h W (closeLen s W) ω)).det)
    (hR : IsUnit (closedNearR b E s h W l ω z).det)
    (hX : (passiveY (closedNearX b E s h W l ω z)).PosSemidef) :
    (gclAt b E s h W (l + 1) ω z).submatrix (headEquiv l W) (headEquiv l W) =
        fromBlocks (closedG b E s h W l ω z)
          (closedG b E s h W l ω z * closedK b E s h W l ω z * nearV b E s h W l ω z)
          (nearU b E s h W l ω z * (closedK b E s h W l ω z * closedG b E s h W l ω z))
          (gclAt b E s h W l ω z + nearU b E s h W l ω z *
            (closedK b E s h W l ω z * closedG b E s h W l ω z * closedK b E s h W l ω z -
              closedK b E s h W l ω z) * nearV b E s h W l ω z) ∧
      (nearU b E s h W (l + 1) ω z).submatrix (headEquiv l W) id =
        fromRows (-((boundaryZ b E)⁻¹ • (closedG b E s h W l ω z * ω.2 (l + 1))))
          (-((boundaryZ b E)⁻¹ • (nearU b E s h W l ω z *
            (closedK b E s h W l ω z * closedG b E s h W l ω z) * ω.2 (l + 1)))) := by
  set ζ := boundaryZ b E with hζdef
  have hζ : ζ ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) ω) with hPi
  set A := farEmbed (omittedProj b E h W (closeLen s W) ω) with hAdef
  set Yc := closedFarY b E s h W ω z with hYc
  set ns := nearSel W with hns
  have hnsPi : ns * Pi = 0 := nearSel_mul_farEmbed _
  have hPins : Pi * nsᴴ = 0 := farEmbed_mul_nearSel_conj _
  have hnsA : ns * A = 0 := nearSel_mul_farEmbed _
  have hAns : A * nsᴴ = 0 := farEmbed_mul_nearSel_conj _
  have hnsY : ns * Yc = 0 := by
    have hY0 : ns * (1 - (z * (star ζ / ζ)) • Pi)⁻¹ = ns := by
      have h1 := mul_nonsing_inv _ hY
      calc ns * (1 - (z * (star ζ / ζ)) • Pi)⁻¹
          = ns * (1 - (z * (star ζ / ζ)) • Pi) * (1 - (z * (star ζ / ζ)) • Pi)⁻¹ := by
            rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hnsPi, smul_zero, sub_zero]
        _ = ns := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    rw [hYc, closedFarY, Matrix.mul_smul, ← Matrix.mul_assoc, ← hPi, hY0, hnsPi, smul_zero]
  have hYn : Yc * nsᴴ = 0 := by
    rw [hYc, closedFarY, Matrix.smul_mul, Matrix.mul_assoc, ← hPi, hPins, Matrix.mul_zero,
      smul_zero]
  set S := scatteringMatrix b E W l ω
  set U := boundaryToInterior b E W l ω
  set C := pathPortCoupling (pathAt W l ω) with hCdef
  set nc := nearCol W l ω
  set f := farCoupling W l ω
  set HO := pathMatrix (pathAt W l ω) - (E : ℂ) • 1
  obtain ⟨hG, hCG, hPU, hCU⟩ := old_facts_at b E l ω hA hη hF
  have hGP := mul_eq_one_comm.mp hG
  set Gcl := gclAt b E s h W l ω z with hGcl
  have hCsplit : C = nc * ns + f := coupling_split l ω
  have hfn : f * nsᴴ = 0 := by
    have := congrArg conjTranspose (nearSel_mul_farCoupling (W := W) l ω)
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
  have hnsf : ns * fᴴ = 0 := nearSel_mul_farCoupling l ω
  have hnn : ns * nsᴴ = 1 := nearSel_mul_conjTranspose
  have hCns : C * nsᴴ = nc := by
    rw [hCsplit, Matrix.add_mul, Matrix.mul_assoc, hnn, Matrix.mul_one, hfn, add_zero]
  have k1 : nc * ns * (nc * ns)ᴴ = nc * ncᴴ := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ns, hnn, Matrix.one_mul]
  have k2 : nc * ns * fᴴ = 0 := by rw [Matrix.mul_assoc, hnsf, Matrix.mul_zero]
  have k3 : f * (nc * ns)ᴴ = 0 := by
    rw [conjTranspose_mul, ← Matrix.mul_assoc, hfn, Matrix.zero_mul]
  have hCC : C * Cᴴ = nc * ncᴴ + f * fᴴ := by
    rw [hCsplit, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, k1, k2, k3]
    abel
  have k4 : nc * ns * Yc = 0 := by rw [Matrix.mul_assoc, hnsY, Matrix.mul_zero]
  have k5 : Yc * (nc * ns)ᴴ = 0 := by
    rw [conjTranspose_mul, ← Matrix.mul_assoc, hYn, Matrix.zero_mul]
  have hCY : C * Yc * Cᴴ = f * Yc * fᴴ := by
    rw [hCsplit, conjTranspose_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, k4, Matrix.mul_assoc f Yc, k5]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_assoc]
  set PO := HO - ζ⁻¹ • (f * fᴴ) - f * Yc * fᴴ with hPOdef
  have hPO : (PO - ζ⁻¹ • (nc * ncᴴ)) * Gcl = 1 := by
    have hcp := closedPencil_at b E s h l ω z hA hη hF hU hY
    rw [← hCdef, hCC, hCY, ← hζdef] at hcp
    rw [← hcp]
    congr 1
    simp only [PO, HO, smul_add]
    abel
  set Ccl := closingMap S A Pi z
  set U' := U * (Ccl * nsᴴ) with hU'def
  set V' := ns * (S * ((1 + closingZ S A Pi z) * Uᴴ)) with hV'def
  set R := closedNearR b E s h W l ω z with hRdef
  have hGn : Gcl * nc = -(ζ • U') := by
    rw [← hCns]
    exact gcl_mul_near hGP hPU hζ hCG hCU rfl hPins hAns
  have hnG : ncᴴ * Gcl = -(ζ • V') := by
    rw [← hCns, conjTranspose_mul, conjTranspose_conjTranspose]
    exact near_mul_gcl hCG hCU rfl hnsPi hU
  have hRc : ζ⁻¹ • (1 + ζ⁻¹ • (ncᴴ * (Gcl * nc))) = R := by
    rw [← hCns, conjTranspose_mul, conjTranspose_conjTranspose]
    exact near_gcl_near hGP hPU hζ hCG hCU rfl hPins hAns hnsPi hnsA hnn hU
  obtain ⟨F1, F2, F3, F4⟩ := closed_old_facts hζ hPO hGn hnG hRc
  set X := closedNearX b E s h W l ω z with hXdef
  have hRK : R * (ζ • 1 - X) = 1 := by
    rw [hXdef, closedNearX, ← hζdef, ← hRdef, sub_sub_cancel]
    exact mul_nonsing_inv _ hR
  set 𝒢 := g11 E ζ X (freshSample W l ω) with h𝒢
  have hf := RawTag.fresh_eq hη hX (ω := freshSample W l ω) (hA l) hB
  set A'' := ω.1 l - (E : ℂ) • 1 - ζ⁻¹ • (ω.2 (l + 1) * (ω.2 (l + 1))ᴴ)
  have hF5 : A'' * 𝒢 = 1 + X * 𝒢 := by
    have : A'' = (ω.1 l - (E : ℂ) • 1 - X - ζ⁻¹ • (ω.2 (l + 1) * (ω.2 (l + 1))ᴴ)) + X := by
      simp only [A'']; abel
    rw [this, Matrix.add_mul]
    exact congrArg (· + X * 𝒢) hf
  have hRinv := RawTag.grown_interior_mul ζ PO nc Gcl U' V' X R A'' 𝒢 F1 F2 F3 F4 hF5 hRK hζ
  have hP' := closedPencil_at b E s h (l + 1) ω z hA hη hF' hU' hY
  have hsub := closedPencil_succ_submatrix b E hl ω Yc hnsY hYn
  have hG'e := congrArg (fun M => M.submatrix (headEquiv l W) (headEquiv l W)) hP'
  rw [← submatrix_mul_equiv _ _ (headEquiv l W) (headEquiv l W) (headEquiv l W), hsub,
    submatrix_one_equiv] at hG'e
  have hGcl' : (gclAt b E s h W (l + 1) ω z).submatrix (headEquiv l W) (headEquiv l W) =
      fromBlocks 𝒢 (𝒢 * (ζ • 1 - X) * V') (U' * ((ζ • 1 - X) * 𝒢))
        (Gcl + U' * ((ζ • 1 - X) * 𝒢 * (ζ • 1 - X) - (ζ • 1 - X)) * V') := by
    rw [← Matrix.inv_eq_right_inv hG'e, Matrix.inv_eq_right_inv hRinv]
  refine ⟨hGcl', ?_⟩
  -- the grown closed near column
  obtain ⟨hG1, hCG1, hPU1, hCU1⟩ := old_facts_at b E (l + 1) ω hA hη hF'
  have hGP1 := mul_eq_one_comm.mp hG1
  have hgn : gclAt b E s h W (l + 1) ω z * (pathPortCoupling (pathAt W (l + 1) ω) * nsᴴ) =
      -(ζ • nearU b E s h W (l + 1) ω z) :=
    gcl_mul_near hGP1 hPU1 hζ hCG1 hCU1 rfl hPins hAns
  have hU1 : nearU b E s h W (l + 1) ω z =
      -(ζ⁻¹ • (gclAt b E s h W (l + 1) ω z * (pathPortCoupling (pathAt W (l + 1) ω) * nsᴴ))) := by
    rw [hgn, smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ hζ, one_smul]
  have hcol : (pathPortCoupling (pathAt W (l + 1) ω) * nsᴴ).submatrix (headEquiv l W) id =
      fromRows (ω.2 (l + 1)) 0 := by
    have e1 : (pathPortCoupling (pathAt W (l + 1) ω) * nsᴴ).submatrix (headEquiv l W) id =
        (pathPortCoupling (pathAt W (l + 1) ω)).submatrix (headEquiv l W) id * nsᴴ := by
      ext i j; simp [Matrix.mul_apply, Matrix.submatrix_apply]
    rw [e1, coupling_succ_submatrix hl, fromRows_mul, Matrix.mul_assoc, ← hns, hnn,
      Matrix.mul_one, hfn]
  have e2 : (-(ζ⁻¹ • (gclAt b E s h W (l + 1) ω z *
      (pathPortCoupling (pathAt W (l + 1) ω) * nsᴴ)))).submatrix (headEquiv l W) id =
      -(ζ⁻¹ • ((gclAt b E s h W (l + 1) ω z).submatrix (headEquiv l W) (headEquiv l W) *
        (pathPortCoupling (pathAt W (l + 1) ω) * nsᴴ).submatrix (headEquiv l W) id)) := by
    rw [submatrix_mul_equiv]; rfl
  rw [hU1, e2, hGcl', hcol, fromBlocks_mul_fromRows]
  simp only [Matrix.mul_zero, add_zero]
  ext (i | i) j <;> rfl

/-!
## The closed interior Ward identity
-/

theorem gramC_mul_c (b E : ℝ) (hη : 0 < etaZ b E) :
    gramC b E * (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) = -1 := by
  have h0 : (2 * Complex.I * (etaZ b E : ℂ)) ≠ 0 := by
    have : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    simp [Complex.I_ne_zero, this]
  rw [gramC]
  push_cast
  field_simp

theorem star_gramC (b E : ℝ) : star (gramC b E) = -gramC b E := by
  have e : (2 : ℂ) * -Complex.I * (etaZ b E : ℂ) = -(2 * Complex.I * (etaZ b E : ℂ)) := by ring
  rw [gramC, star_neg, star_inv₀, star_mul', star_mul', Complex.star_def]
  simp only [map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  rw [e, inv_neg]

/-- **The closed interior Ward identity** `𝒰CCᴴ𝒰ᴴ = c(Gcl − Gclᴴ)` at every length. -/
theorem closed_interior_gram (b E s h : ℝ) (hh : h ^ 2 < 1) (n : ℕ) (ω : GrowthPath W) {z : ℂ}
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < etaZ b E)
    (hS : scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1) (hz : z * star z = 1)
    (hU : IsUnit (1 - z • closingN (scatteringMatrix b E W n ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det) :
    boundaryToInterior b E W n ω * (physClosingMapAt b E s h W n ω z *
        (physClosingMapAt b E s h W n ω z)ᴴ) * (boundaryToInterior b E W n ω)ᴴ =
      gramC b E • (gclAt b E s h W n ω z - (gclAt b E s h W n ω z)ᴴ) := by
  set S := scatteringMatrix b E W n ω
  set A := farEmbed (omittedProj b E h W (closeLen s W) ω)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) ω)
  have hA2 : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have hC := closingMap_mul_conj hA2 hAH hPi hS hz hU
  set U := boundaryToInterior b E W n ω
  set G := (fullInverse b E W n ω).toBlocks₁₁
  set Z := closingZ S A Pi z
  set c0 : ℂ := ((2 * etaZ b E : ℝ) : ℂ) * Complex.I with hc0
  have hWard := ComplexSourceLaw.interior_sub_conjTranspose b E n ω hA
  have hconj : conj (boundaryZ b E) - boundaryZ b E = -c0 := by
    rw [hc0, c_eq_sub_star, Complex.star_def]; ring
  have hc0s : star c0 = -c0 := by
    rw [hc0, star_mul', Complex.star_def]
    simp only [Complex.conj_I, Complex.conj_ofReal]
    ring
  have hgcl : gclAt b E s h W n ω z = G - c0 • (U * Z * Uᴴ) := by
    simp only [gclAt, G, U, Z, closingZ, c0, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      Matrix.mul_assoc]
    rfl
  have hZH : (U * Z * Uᴴ)ᴴ = U * Zᴴ * Uᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hW' : G - Gᴴ = (-c0) • (U * Uᴴ) := by rw [← hconj]; exact hWard
  have key : gclAt b E s h W n ω z - (gclAt b E s h W n ω z)ᴴ =
      (-c0) • (U * Uᴴ) - c0 • (U * Z * Uᴴ) - c0 • (U * Zᴴ * Uᴴ) := by
    rw [hgcl, conjTranspose_sub, conjTranspose_smul, hZH, hc0s, ← hW']
    simp only [neg_smul, sub_neg_eq_add]
    abel
  have hcc : gramC b E * c0 = -1 := gramC_mul_c b E hη
  have hC' : physClosingMapAt b E s h W n ω z * (physClosingMapAt b E s h W n ω z)ᴴ =
      1 + Z + Zᴴ := hC
  rw [hC', key]
  simp only [smul_sub, smul_smul, mul_neg, hcc, neg_neg, one_smul, neg_one_smul,
    sub_neg_eq_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]

/-!
## The fresh transmission `L`
-/

/-- `L = K𝒢₁₂ = −z_∂⁻¹K𝒢₁₁B` for a passive input and a good layer. -/
theorem freshL_eq_neg {b E : ℝ} (hη : 0 < (boundaryZ b E).im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    freshL b E X ω = -((boundaryZ b E)⁻¹ • ((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
      g11 E (boundaryZ b E) X ω * ω.2 0 0)) := by
  have hζ : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  have hM : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) ω) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (layer_schur E hη hY hA hB).1
  obtain ⟨-, -, -, -, -, hJ, -, -⟩ := CompleteSourceGap.layer_identities E (boundaryZ b E) X ω hM
  have h12 : g12 E (boundaryZ b E) X ω = -((boundaryZ b E)⁻¹ • (g11 E (boundaryZ b E) X ω *
      ω.2 0 0)) := by
    rw [Matrix.mul_smul, Matrix.mul_one, add_eq_zero_iff_eq_neg'] at hJ
    calc g12 E (boundaryZ b E) X ω =
        (boundaryZ b E)⁻¹ • (boundaryZ b E • g12 E (boundaryZ b E) X ω) := by
          rw [smul_smul, inv_mul_cancel₀ hζ, one_smul]
      _ = _ := by rw [hJ, smul_neg]
  rw [FullSource.freshL_eq_lAt, lAt, h12, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc]

/-!
## Reindexing
-/

theorem conj_mulVec_reindex {α β γ : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (Φ : Matrix β γ ℂ) (g : β → ℂ) : Φᴴ *ᵥ g = (Φ.submatrix e id)ᴴ *ᵥ (g ∘ e) := by
  funext c
  simp only [mulVec, dotProduct, conjTranspose_apply, submatrix_apply, Function.comp_apply,
    id]
  exact (e.sum_comp (fun b => star (Φ b c) * g b)).symm

theorem fromRows_conj_mulVec_elim {m₁ m₂ γ : Type*} [Fintype m₁] [Fintype m₂]
    (P : Matrix m₁ γ ℂ) (Q : Matrix m₂ γ ℂ) (g : m₂ → ℂ) :
    (fromRows P Q)ᴴ *ᵥ Sum.elim (0 : m₁ → ℂ) g = Qᴴ *ᵥ g := by
  funext c
  simp [mulVec, dotProduct, Fintype.sum_sum_type, conjTranspose_apply]

theorem dot_gram {α β : Type*} [Fintype α] [Fintype β] (T : Matrix α β ℂ) (g g' : α → ℂ) :
    star (Tᴴ *ᵥ g) ⬝ᵥ (Tᴴ *ᵥ g') = star g ⬝ᵥ ((T * Tᴴ) *ᵥ g') := by
  rw [← mulVec_mulVec, dotProduct_mulVec (star g), star_mulVec, conjTranspose_conjTranspose]

theorem bilinear_reindex_old {l : ℕ} (G : Matrix (Fin (l + 1) × Fin W) (Fin (l + 1) × Fin W) ℂ)
    {P : Matrix (Fin W) (Fin W) ℂ} {Q : Matrix (Fin W) (Fin l × Fin W) ℂ}
    {R : Matrix (Fin l × Fin W) (Fin W) ℂ} {T : Matrix (Fin l × Fin W) (Fin l × Fin W) ℂ}
    (hG : G.submatrix (headEquiv l W) (headEquiv l W) = fromBlocks P Q R T)
    {g g₂ : Fin l × Fin W → ℂ} {g' g₂' : Fin (l + 1) × Fin W → ℂ}
    (hg : g' ∘ headEquiv l W = Sum.elim (0 : Fin W → ℂ) g)
    (hg₂ : g₂' ∘ headEquiv l W = Sum.elim (0 : Fin W → ℂ) g₂) :
    bilinear g' G g₂' = bilinear g T g₂ := by
  unfold bilinear
  rw [RawTag.dot_reindex (headEquiv l W), hg, hg₂, hG, dot_elim_zero]

/-!
## The closed Gram step at one sample
-/

theorem nearU_conj_mulVec (b E s h : ℝ) (n : ℕ) (ω : GrowthPath W) (z : ℂ)
    (g : Fin n × Fin W → ℂ) :
    (nearU b E s h W n ω z)ᴴ *ᵥ g = nearSel W *ᵥ ((physClosingMapAt b E s h W n ω z)ᴴ *ᵥ
      ((boundaryToInterior b E W n ω)ᴴ *ᵥ g)) := by
  simp only [nearU, conjTranspose_mul, conjTranspose_conjTranspose, mulVec_mulVec,
    Matrix.mul_assoc]

theorem nearV_mulVec (b E s h : ℝ) (n : ℕ) (ω : GrowthPath W) (z : ℂ)
    (g : Fin n × Fin W → ℂ) :
    nearV b E s h W n ω z *ᵥ g = nearSel W *ᵥ (scatteringMatrix b E W n ω *ᵥ
      ((1 + physClosingZAt b E s h W n ω z) *ᵥ ((boundaryToInterior b E W n ω)ᴴ *ᵥ g))) := by
  simp only [nearV, mulVec_mulVec]

/-- The closed `M` Gram overlap of two interior vectors: `c(g*Gcl g₂ − (g₂*Gcl g)^*)`. -/
theorem closed_overlap_eq (b E s h : ℝ) (hh : h ^ 2 < 1) (n : ℕ) (ω : GrowthPath W) {z : ℂ}
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < etaZ b E)
    (hS : scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1) (hz : z * star z = 1)
    (hU : IsUnit (1 - z • closingN (scatteringMatrix b E W n ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (g g₂ : Fin n × Fin W → ℂ) :
    star ((physClosingMapAt b E s h W n ω z)ᴴ *ᵥ ((boundaryToInterior b E W n ω)ᴴ *ᵥ g)) ⬝ᵥ
        ((physClosingMapAt b E s h W n ω z)ᴴ *ᵥ ((boundaryToInterior b E W n ω)ᴴ *ᵥ g₂)) =
      gramC b E * (bilinear g (gclAt b E s h W n ω z) g₂ -
        star (bilinear g₂ (gclAt b E s h W n ω z) g)) := by
  have e1 : ∀ v, (physClosingMapAt b E s h W n ω z)ᴴ *ᵥ ((boundaryToInterior b E W n ω)ᴴ *ᵥ v) =
      (boundaryToInterior b E W n ω * physClosingMapAt b E s h W n ω z)ᴴ *ᵥ v := fun v => by
    rw [conjTranspose_mul, mulVec_mulVec]
  have e2 : boundaryToInterior b E W n ω * physClosingMapAt b E s h W n ω z *
      (boundaryToInterior b E W n ω * physClosingMapAt b E s h W n ω z)ᴴ =
      boundaryToInterior b E W n ω * (physClosingMapAt b E s h W n ω z *
        (physClosingMapAt b E s h W n ω z)ᴴ) * (boundaryToInterior b E W n ω)ᴴ := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, e1, dot_gram, e2, closed_interior_gram b E s h hh n ω hA hη hS hz hU, smul_mulVec,
    dotProduct_smul, sub_mulVec, dotProduct_sub, smul_eq_mul]
  congr 2
  exact FullSource.bilinear_conjTranspose g g₂ _

/-- **The closed Gram step at one sample** (`M` and `B` overlaps of two old interior vectors). -/
theorem closedGram_step_vec (b E s h : ℝ) (hh : h ^ 2 < 1) {l : ℕ} (hl : 1 ≤ l)
    (ω : GrowthPath W) {z : ℂ} (hz : z * star z = 1)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W l ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (l + 1) ω) - (E : ℂ) • 1))
    (hB : IsUnit (ω.2 (l + 1)))
    (hS : ∀ n, scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1)
    (hU : IsUnit (1 - z • closingN (scatteringMatrix b E W l ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (hU' : IsUnit (1 - z • closingN (scatteringMatrix b E W (l + 1) ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (hY : IsUnit (1 - (z * (star (boundaryZ b E) / boundaryZ b E)) •
      farEmbed (closingPairing b E h W (closeLen s W) ω)).det)
    (hR : IsUnit (closedNearR b E s h W l ω z).det)
    (hX : (passiveY (closedNearX b E s h W l ω z)).PosSemidef)
    {g g₂ : Fin l × Fin W → ℂ} {g' g₂' : Fin (l + 1) × Fin W → ℂ}
    (hg : g' ∘ headEquiv l W = Sum.elim (0 : Fin W → ℂ) g)
    (hg₂ : g₂' ∘ headEquiv l W = Sum.elim (0 : Fin W → ℂ) g₂) :
    star ((physClosingMapAt b E s h W (l + 1) ω z)ᴴ *ᵥ
        ((boundaryToInterior b E W (l + 1) ω)ᴴ *ᵥ g')) ⬝ᵥ
        ((physClosingMapAt b E s h W (l + 1) ω z)ᴴ *ᵥ
          ((boundaryToInterior b E W (l + 1) ω)ᴴ *ᵥ g₂')) -
      star ((physClosingMapAt b E s h W l ω z)ᴴ *ᵥ ((boundaryToInterior b E W l ω)ᴴ *ᵥ g)) ⬝ᵥ
        ((physClosingMapAt b E s h W l ω z)ᴴ *ᵥ ((boundaryToInterior b E W l ω)ᴴ *ᵥ g₂)) =
      gramC b E * bilinear ((nearU b E s h W l ω z)ᴴ *ᵥ g)
          (freshDelta b E (closedNearX b E s h W l ω z) (freshSample W l ω))
          (nearV b E s h W l ω z *ᵥ g₂) +
        star (gramC b E * bilinear ((nearU b E s h W l ω z)ᴴ *ᵥ g₂)
          (freshDelta b E (closedNearX b E s h W l ω z) (freshSample W l ω))
          (nearV b E s h W l ω z *ᵥ g)) ∧
    star (nearSel W *ᵥ ((physClosingMapAt b E s h W (l + 1) ω z)ᴴ *ᵥ
        ((boundaryToInterior b E W (l + 1) ω)ᴴ *ᵥ g'))) ⬝ᵥ
        (nearSel W *ᵥ ((physClosingMapAt b E s h W (l + 1) ω z)ᴴ *ᵥ
          ((boundaryToInterior b E W (l + 1) ω)ᴴ *ᵥ g₂'))) -
      star ((nearU b E s h W l ω z)ᴴ *ᵥ g) ⬝ᵥ ((nearU b E s h W l ω z)ᴴ *ᵥ g₂) =
      bilinear ((nearU b E s h W l ω z)ᴴ *ᵥ g)
        (freshU b E (closedNearX b E s h W l ω z) (freshSample W l ω) - 1)
        ((nearU b E s h W l ω z)ᴴ *ᵥ g₂) := by
  obtain ⟨hGcl', hcol⟩ := gcl_succ_blocks b E s h hl ω z hA hη hF hF' hB hU hU' hY hR hX
  have hη' : 0 < etaZ b E := hη
  set Δ := freshDelta b E (closedNearX b E s h W l ω z) (freshSample W l ω) with hΔ
  have hΔe : closedK b E s h W l ω z * closedG b E s h W l ω z * closedK b E s h W l ω z -
      closedK b E s h W l ω z = Δ := rfl
  rw [hΔe] at hGcl'
  refine ⟨?_, ?_⟩
  · rw [closed_overlap_eq b E s h hh (l + 1) ω hA hη' (hS _) hz hU',
      closed_overlap_eq b E s h hh l ω hA hη' (hS _) hz hU,
      bilinear_reindex_old _ hGcl' hg hg₂, bilinear_reindex_old _ hGcl' hg₂ hg]
    have hb : ∀ v v₂ : Fin l × Fin W → ℂ, bilinear v (gclAt b E s h W l ω z +
        nearU b E s h W l ω z * Δ * nearV b E s h W l ω z) v₂ =
        bilinear v (gclAt b E s h W l ω z) v₂ +
          bilinear ((nearU b E s h W l ω z)ᴴ *ᵥ v) Δ (nearV b E s h W l ω z *ᵥ v₂) := by
      intro v v₂
      unfold bilinear
      rw [add_mulVec, dotProduct_add, RawTag.dot_sandwich]
    rw [hb, hb, star_add, star_mul', star_gramC]
    ring
  · have hL : -((boundaryZ b E)⁻¹ • (nearU b E s h W l ω z *
        (closedK b E s h W l ω z * closedG b E s h W l ω z) * ω.2 (l + 1))) =
        nearU b E s h W l ω z *
          freshL b E (closedNearX b E s h W l ω z) (freshSample W l ω) := by
      rw [freshL_eq_neg hη hX (ω := freshSample W l ω) (hA l) hB]
      simp only [Matrix.mul_neg, Matrix.mul_smul, closedK, closedG, Matrix.mul_assoc]
      rfl
    have hu' : ∀ (v' : Fin (l + 1) × Fin W → ℂ) (v : Fin l × Fin W → ℂ),
        v' ∘ headEquiv l W = Sum.elim (0 : Fin W → ℂ) v →
        nearSel W *ᵥ ((physClosingMapAt b E s h W (l + 1) ω z)ᴴ *ᵥ
          ((boundaryToInterior b E W (l + 1) ω)ᴴ *ᵥ v')) =
        (freshL b E (closedNearX b E s h W l ω z) (freshSample W l ω))ᴴ *ᵥ
          ((nearU b E s h W l ω z)ᴴ *ᵥ v) := by
      intro v' v hv
      rw [← nearU_conj_mulVec, conj_mulVec_reindex (headEquiv l W), hv, hcol,
        fromRows_conj_mulVec_elim, hL, conjTranspose_mul, ← mulVec_mulVec]
    rw [hu' g' g hg, hu' g₂' g₂ hg₂, dot_gram]
    unfold bilinear
    rw [sub_mulVec, one_mulVec, dotProduct_sub]
    rfl

end GramUpd

end BlockBand.SourceProcess.PhysApprox.B3
