module

public import BlockBand.SourceProcess.PhysApprox.B3JetPass
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormStep

/-!
# The closed one-port recursion `ClosedInputRecursion b3ClosedX`

Closing touches only the far boundary, and the far-closed pencil grows at the near end exactly
like the open one (`closedPencil_at`, `closedPencil_succ_submatrix`). The proof
reuses the Schur step of `closedK_step`: the grown closed inverse has the fresh
block `𝒢 = (A_l - E - X_cl,l - z_∂⁻¹BBᴴ)⁻¹` in its newest corner. The closed near corner
(`near_gcl_near`) at length `l + 1` is then `R' = z_∂⁻¹(1 + z_∂⁻¹Bᴴ𝒢B)`, and the Woodbury
identity gives `R'(z_∂ - Bᴴ(A_l - E - X_cl,l)⁻¹B) = 1`, that is,
`X_cl,l+1 = z_∂ - R'⁻¹ = Bᴴ(A_l - E - X_cl,l)⁻¹B = freshSchur E X_cl,l F_l`.

* `closedNearX_succ` (deterministic, with the a.s. invertibilities);
* `ae_isUnit_fresh_closedX`: `A_l - E - X_cl,l` is a.s. invertible (fresh GUE block,
  `fresh_det_null` with `closedLaw_map_past_fresh`);
* **`closedInputRecursion_b3ClosedX`**: `ClosedInputRecursion b3ClosedX`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.PhysApprox.ClosedForm
open BlockBand.Transmission.PathScalar BlockBand.SourceProcess.FullSourceStops
open scoped ComplexOrder

variable {W np : ℕ}

/-- `vᴴGv` after reindexing by an equivalence. -/
theorem conj_mul_reindex {m o : Type*} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    (e : o ≃ m) (v : Matrix m (Fin W) ℂ) (G : Matrix m m ℂ) :
    vᴴ * G * v = (v.submatrix e id)ᴴ * G.submatrix e e * v.submatrix e id := by
  rw [Matrix.conjTranspose_submatrix, submatrix_mul_equiv vᴴ G id e e,
    submatrix_mul_equiv (vᴴ * G) v id e id, submatrix_id_id]

/-- **The closed one-port recursion at one step** (deterministic, with the a.s.
invertibilities): `X_cl,l+1 = freshSchur E X_cl,l F_l`. -/
theorem closedNearX_succ (b E s h : ℝ) {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W) (z : ℂ)
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
    (hX : (passiveY (closedNearX b E s h W l ω z)).PosSemidef)
    (hYi : IsUnit (ω.1 l - (E : ℂ) • 1 - closedNearX b E s h W l ω z).det) :
    closedNearX b E s h W (l + 1) ω z =
      freshSchur E (closedNearX b E s h W l ω z) (freshSample W l ω) := by
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
  set S := scatteringMatrix b E W l ω
  set Ccl := closingMap S A Pi z
  set U' := U * (Ccl * nsᴴ)
  set V' := ns * (S * ((1 + closingZ S A Pi z) * Uᴴ))
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
  -- the closed near corner at length `l + 1`
  set C' := pathPortCoupling (pathAt W (l + 1) ω) with hC'def
  obtain ⟨hG2, hCG2, hPU2, hCU2⟩ := old_facts_at b E (l + 1) ω hA hη hF'
  have hGP2 := mul_eq_one_comm.mp hG2
  set Bn := ω.2 (l + 1) with hBn
  have hRc' : ζ⁻¹ • (1 + ζ⁻¹ • ((C' * nsᴴ)ᴴ * gclAt b E s h W (l + 1) ω z * (C' * nsᴴ))) =
      closedNearR b E s h W (l + 1) ω z := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    exact near_gcl_near hGP2 hPU2 hζ hCG2 hCU2 rfl hPins hAns hnsPi hnsA hnn hU'
  have hv : (C' * nsᴴ).submatrix (headEquiv l W) id = fromRows Bn 0 := by
    have : (C' * nsᴴ).submatrix (headEquiv l W) id = C'.submatrix (headEquiv l W) id * nsᴴ := by
      ext i j; simp [Matrix.mul_apply]
    rw [this, coupling_succ_submatrix hl, fromRows_mul, Matrix.mul_assoc, hnn, Matrix.mul_one,
      hfn]
  have hcore : (C' * nsᴴ)ᴴ * gclAt b E s h W (l + 1) ω z * (C' * nsᴴ) = Bnᴴ * 𝒢 * Bn := by
    rw [conj_mul_reindex (headEquiv l W), hv, hGcl',
      conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
    simp
  rw [hcore] at hRc'
  -- the Woodbury identity
  set Yf := ω.1 l - (E : ℂ) • 1 - X with hYf
  have hYYi : Yf * Yf⁻¹ = 1 := mul_nonsing_inv _ hYi
  have hfl : 𝒢 * (Yf - ζ⁻¹ • (Bn * Bnᴴ)) = 1 := mul_eq_one_comm.mp hf
  have hGBB : 𝒢 * (Bn * Bnᴴ) = ζ • (𝒢 * Yf - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, sub_eq_iff_eq_add] at hfl
    rw [hfl, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hζ, one_smul]
  set K := Bnᴴ * 𝒢 * Bn
  set L := Bnᴴ * Yf⁻¹ * Bn
  have hKL : K * L = ζ • (K - L) := by
    have : K * L = Bnᴴ * ((𝒢 * (Bn * Bnᴴ)) * Yf⁻¹) * Bn := by
      simp only [K, L, Matrix.mul_assoc]
    rw [this, hGBB, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_assoc 𝒢, hYYi, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
  have hR'L : closedNearR b E s h W (l + 1) ω z * (ζ • 1 - L) = 1 := by
    rw [← hRc']
    simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, hKL]
    rw [smul_sub, smul_sub, smul_smul, smul_smul, smul_smul]
    match_scalars <;> field_simp <;> ring
  rw [closedNearX, ← hζdef, Matrix.inv_eq_right_inv hR'L, sub_sub_cancel]
  show L = freshSchur E X ((fun _ => ω.1 l, fun _ _ => ω.2 (l + 1)) :
    LayerSample W .oneBlockOnePort)
  rw [freshSchur_eq]

/-- **The fresh Schur block of the closed input is a.s. invertible**: `A_l` is a fresh GUE block,
independent of `X_cl,l` (a function of the past at `l`, the probes and the phase). -/
theorem ae_isUnit_fresh_closedX {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E s h : ℝ)
    (τ m : Fin np → ℝ) {l : ℕ} (hl : closeLen s W ≤ l) :
    ∀ᵐ y ∂closedLaw b W np,
      IsUnit (y.1.1.1 l - (E : ℂ) • 1 - b3ClosedX b E s h τ m W l y).det := by
  set c : (PastSample W l × ((Fin np → Fin W → ℂ) × ℝ)) × Matrix (Fin W) (Fin W) ℂ →
      Matrix (Fin W) (Fin W) ℂ :=
    fun q => -((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) - b3ClosedX b E s h τ m W l
      (b3Rebuild W l q.1)
  have hc : Measurable c := measurable_matrix_sub measurable_const
    ((measurable_b3ClosedX b E s h τ m l).comp ((measurable_b3Rebuild W l).comp measurable_fst))
  have h0 := BlockBand.SourceProcess.ClosedSum.fresh_det_null hb hW
    ((pastLaw W l b).prod (probePhaseLaw W np)) hc
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W l y, freshSample W l y.1.1) :=
    (measurable_b3Past W l).prodMk
      ((measurable_freshSample W l).comp (measurable_fst.comp measurable_fst))
  have hS := BlockBand.SourceProcess.ClosedSum.measurableSet_fresh_det (W := W) hc
  rw [← closedLaw_map_past_fresh b W np l, Measure.map_apply hT hS] at h0
  rw [ae_iff]
  refine le_antisymm (le_trans (measure_mono fun y hy => ?_) h0.le) (zero_le)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy ⊢
  have hy' : (y.1.1.1 l - (E : ℂ) • 1 - b3ClosedX b E s h τ m W l y).det = 0 := by
    by_contra hne; exact hy (isUnit_iff_ne_zero.2 hne)
  have e : (freshSample W l y.1.1).1 0 + c (b3Past W l y, (freshSample W l y.1.1).2 0 0) =
      y.1.1.1 l - (E : ℂ) • 1 - b3ClosedX b E s h τ m W l y := by
    simp only [c, b3Rebuild_b3Past, b3ClosedX_b3Ext hl le_rfl, freshSample]
    abel
  rw [e]; exact hy'

/-- **`ClosedInputRecursion b3ClosedX`**: the closed input follows the fresh Schur recursion. -/
theorem closedInputRecursion_b3ClosedX : ClosedInputRecursion b3ClosedX := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, hh0, hh1, -⟩ := id hF
  have hh : h ^ 2 < 1 := by nlinarith
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [eventually_ge_atTop (max 1 ⌈s⁻¹⌉₊)] with W hWb j hj _
  have hW1 : 1 ≤ W := le_trans (le_max_left _ _) hWb
  have hj1 : 1 ≤ j := by
    refine le_trans ?_ hj
    rw [closeLen, Nat.one_le_floor_iff]
    have h1 := (Nat.le_ceil s⁻¹).trans
      (by exact_mod_cast le_trans (le_max_right _ _) hWb : (⌈s⁻¹⌉₊ : ℝ) ≤ W)
    rw [inv_le_iff_one_le_mul₀ hs] at h1
    linarith
  filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW1,
    ae_closedPhase_good (W := W) (np := np) b E s h j,
    ae_isUnit_fresh_closedX hb hW1 E s h τ m hj] with y hP hQ hYi
  obtain ⟨hA, hFp, hB, hS⟩ := hP
  obtain ⟨hU, hU', hY, h4⟩ := hQ
  have hR := h4.resolve_left (isUnit_closedR0 b E h s j y.1.1 hA hη (hFp j)).ne_zero
  have hX := passive_closedNearX b E s h hh j y.1.1 y.2 hη (hS j) (isUnit_iff_ne_zero.2 hU)
    (isUnit_iff_ne_zero.2 hR)
  exact closedNearX_succ b E s h hj1 y.1.1 (phase y.2) hA hη (hFp j) (hFp (j + 1)) (hB (j + 1))
    (isUnit_iff_ne_zero.2 hU) (isUnit_iff_ne_zero.2 hU') (isUnit_iff_ne_zero.2 hY)
    (isUnit_iff_ne_zero.2 hR) hX hYi

end BlockBand.SourceProcess.PhysApprox.B3.Jet
