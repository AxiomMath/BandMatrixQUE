module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormStep
public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubTwo

/-!
# The closed `𝒦` at a birth step

Deterministic, for one sample and one phase `z` with the almost-sure invertibilities used by
`closedK_step`, at a step `l → l + 1`, `l ≥ 1`:
* **`gclAt_succ_blocks`**: the grown closed interior inverse, newest block first, is
  `[[𝒢, 𝒢K V′], [U′K𝒢, Gcl + U′(K𝒢K − K)V′]]`, with `X = X_cl = closedNearX`, `K = z_∂ − X`,
  `𝒢 = g11(X, F_l)` (the fresh corner), `U′ = 𝒰 C(z) ιᴴ`, `V′ = ι𝕊(1 + Z)𝒰ᴴ`. The proof is the
  setup of `closedK_step`, which states only the old/old block; it is re-derived here because
  that intermediate step is not stated as a lemma.
* **`closedK_birth_old_new`, `closedK_birth_new_old`, `closedK_birth_new_new`** (given the
  block form `GclSuccBlocks`, the conclusion of `gclAt_succ_blocks`): for a tag
  born at `l` (`⌊Wτ⌋ = l`) and an old tag, with `c = √(m/W)`:
  `𝒦_cl,l+1(k, new) = u_k*(K𝒢)(c g)`, `𝒦_cl,l+1(new, k') = (c g)*(𝒢K)v_{k'}` and
  `𝒦_cl,l+1(new, new) = (c g)*𝒢(c g)`, with the closed near frames `u = closedNearU`,
  `v = closedNearV` at length `l`. No loop resolvent appears.
* `birthG_eq`, `birthK_mul_birthG`: at a passive `X_cl`, `𝒢 = R_cl + R_clΔR_cl`, `K𝒢 = 1 + ΔR_cl`,
  `𝒢K = 1 + R_clΔ` (`R_cl = passiveResolvent X_cl`, `Δ = freshDelta(X_cl, F_l)`).

The probe and fresh-layer averages on `closedLaw`, which give `ComplexBirthCrossK` and
`ComplexBirthKDiag`, are taken in `complexBirthCrossK_holds` and `complexBirthKDiag_of_jet`.
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
open scoped ComplexOrder

variable {W np : ℕ}

namespace BirthKSub

/-- The fresh corner `𝒢 = g11(X_cl, F_l)`. -/
def birthG (b E s h : ℝ) (W l : ℕ) (ω : GrowthPath W) (z : ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  g11 E (boundaryZ b E) (closedNearX b E s h W l ω z) (freshSample W l ω)

/-- `K = z_∂ − X_cl`. -/
def birthK (b E s h : ℝ) (W l : ℕ) (ω : GrowthPath W) (z : ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - closedNearX b E s h W l ω z

/-- `U′ = 𝒰 C(z) ιᴴ`. -/
def birthU (b E s h : ℝ) (W l : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin l × Fin W) (Fin W) ℂ :=
  boundaryToInterior b E W l ω * (closingMap (scatteringMatrix b E W l ω)
    (farEmbed (omittedProj b E h W (closeLen s W) ω))
    (farEmbed (closingPairing b E h W (closeLen s W) ω)) z * (nearSel W)ᴴ)

/-- `V′ = ι𝕊(1 + Z)𝒰ᴴ`. -/
def birthV (b E s h : ℝ) (W l : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin W) (Fin l × Fin W) ℂ :=
  nearSel W * (scatteringMatrix b E W l ω * ((1 + closingZ (scatteringMatrix b E W l ω)
    (farEmbed (omittedProj b E h W (closeLen s W) ω))
    (farEmbed (closingPairing b E h W (closeLen s W) ω)) z) * (boundaryToInterior b E W l ω)ᴴ))

end BirthKSub

open BirthKSub

/-- **The grown closed interior inverse in block form** (newest block first). Re-derived from
the setup of `closedK_step`. -/
theorem gclAt_succ_blocks (b E s h : ℝ) {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W) (z : ℂ)
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
      fromBlocks (birthG b E s h W l ω z)
        (birthG b E s h W l ω z * birthK b E s h W l ω z * birthV b E s h W l ω z)
        (birthU b E s h W l ω z * (birthK b E s h W l ω z * birthG b E s h W l ω z))
        (gclAt b E s h W l ω z + birthU b E s h W l ω z * (birthK b E s h W l ω z *
          birthG b E s h W l ω z * birthK b E s h W l ω z - birthK b E s h W l ω z) *
          birthV b E s h W l ω z) := by
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
  -- the old path at length `l`
  set S := scatteringMatrix b E W l ω
  set U := boundaryToInterior b E W l ω
  set Rr := boundaryResolvent b E W l ω
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
  -- the grown closed pencil
  have hP' := closedPencil_at b E s h (l + 1) ω z hA hη hF' hU' hY
  have hsub := closedPencil_succ_submatrix b E hl ω Yc hnsY hYn
  have hG'e := congrArg (fun M => M.submatrix (headEquiv l W) (headEquiv l W)) hP'
  rw [← submatrix_mul_equiv _ _ (headEquiv l W) (headEquiv l W) (headEquiv l W), hsub,
    submatrix_one_equiv] at hG'e
  have hGcl' : (gclAt b E s h W (l + 1) ω z).submatrix (headEquiv l W) (headEquiv l W) =
      fromBlocks 𝒢 (𝒢 * (ζ • 1 - X) * V') (U' * ((ζ • 1 - X) * 𝒢))
        (Gcl + U' * ((ζ • 1 - X) * 𝒢 * (ζ • 1 - X) - (ζ • 1 - X)) * V') := by
    rw [← Matrix.inv_eq_right_inv hG'e, Matrix.inv_eq_right_inv hRinv]
  exact hGcl'

/-!
## The newborn entries
-/

/-- The newborn column at its birth length, newest block first. -/
theorem probeColumns_comp_new (τ m : Fin np → ℝ) (g : Fin np → Fin W → ℂ) {l : ℕ} {k : Fin np}
    (hk : ⌊(W : ℝ) * τ k⌋₊ = l) :
    (fun x => probeColumns W (l + 1) τ m g x k) ∘ headEquiv l W =
      Sum.elim (((Real.sqrt (m k / W) : ℝ) : ℂ) • g k) (0 : Fin l × Fin W → ℂ) := by
  funext x
  rcases x with x | ⟨i, x⟩
  · simp [probeColumns, headEquiv_inl, hk]
  · simp only [Function.comp_apply, headEquiv_inr, probeColumns, Sum.elim_inr, Pi.zero_apply,
      Fin.val_succ]
    simp only [Nat.add_sub_cancel]
    simp
    intro _ h2
    omega

/-- The grown closed inverse in block form (the conclusion of `gclAt_succ_blocks`). -/
def GclSuccBlocks (b E s h : ℝ) (W l : ℕ) (ω : GrowthPath W) (z : ℂ) : Prop :=
  (gclAt b E s h W (l + 1) ω z).submatrix (headEquiv l W) (headEquiv l W) =
    fromBlocks (birthG b E s h W l ω z)
      (birthG b E s h W l ω z * birthK b E s h W l ω z * birthV b E s h W l ω z)
      (birthU b E s h W l ω z * (birthK b E s h W l ω z * birthG b E s h W l ω z))
      (gclAt b E s h W l ω z + birthU b E s h W l ω z * (birthK b E s h W l ω z *
        birthG b E s h W l ω z * birthK b E s h W l ω z - birthK b E s h W l ω z) *
        birthV b E s h W l ω z)

/-- **Old/new**: `𝒦_cl,l+1(k, new) = u_k*(K𝒢)(c g)`. -/
theorem closedK_birth_old_new (b E s h : ℝ) (τ m : Fin np → ℝ) {l : ℕ}
    (y : ProbedPath W np × ℝ) (hblk : GclSuccBlocks b E s h W l y.1.1 (phase y.2))
    {k k' : Fin np} (hk : ⌊(W : ℝ) * τ k⌋₊ < l) (hk' : ⌊(W : ℝ) * τ k'⌋₊ = l) :
    b3ClosedKAt b E s h τ m W (l + 1) y k k' =
      bilinear (closedNearU b E s h τ m W l k y)
        (birthK b E s h W l y.1.1 (phase y.2) * birthG b E s h W l y.1.1 (phase y.2))
        (((Real.sqrt (m k' / W) : ℝ) : ℂ) • y.1.2 k') := by
  rw [b3ClosedKAt_eq_gcl, entry_eq_dot, RawTag.dot_reindex (headEquiv l W),
    probeColumns_comp_old τ m y.1.2 hk, probeColumns_comp_new τ m y.1.2 hk', hblk,
    RawTag.dot_fromBlocks]
  simp only [star_zero, zero_dotProduct, mulVec_zero, add_zero, zero_add]
  rw [← Matrix.mul_one (birthU b E s h W l y.1.1 (phase y.2) *
    (birthK b E s h W l y.1.1 (phase y.2) * birthG b E s h W l y.1.1 (phase y.2))),
    RawTag.dot_sandwich, one_mulVec, bilinear]
  congr 2
  rw [closedNearU, probeCol_eq]
  simp only [birthU, conjTranspose_mul, conjTranspose_conjTranspose, ← mulVec_mulVec]
  rfl

/-- **New/old**: `𝒦_cl,l+1(new, k') = (c g)*(𝒢K)v_{k'}`. -/
theorem closedK_birth_new_old (b E s h : ℝ) (τ m : Fin np → ℝ) {l : ℕ}
    (y : ProbedPath W np × ℝ) (hblk : GclSuccBlocks b E s h W l y.1.1 (phase y.2))
    {k k' : Fin np} (hk : ⌊(W : ℝ) * τ k⌋₊ = l) (hk' : ⌊(W : ℝ) * τ k'⌋₊ < l) :
    b3ClosedKAt b E s h τ m W (l + 1) y k k' =
      bilinear (((Real.sqrt (m k / W) : ℝ) : ℂ) • y.1.2 k)
        (birthG b E s h W l y.1.1 (phase y.2) * birthK b E s h W l y.1.1 (phase y.2))
        (closedNearV b E s h τ m W l k' y) := by
  rw [b3ClosedKAt_eq_gcl, entry_eq_dot, RawTag.dot_reindex (headEquiv l W),
    probeColumns_comp_new τ m y.1.2 hk, probeColumns_comp_old τ m y.1.2 hk', hblk,
    RawTag.dot_fromBlocks]
  simp only [star_zero, zero_dotProduct, mulVec_zero, add_zero, zero_add]
  rw [bilinear, ← mulVec_mulVec]
  congr 2
  rw [closedNearV, probeCol_eq]
  simp only [birthV, ← mulVec_mulVec]
  rfl

/-- **New/new**: `𝒦_cl,l+1(new, new) = (c g)*𝒢(c g)`. -/
theorem closedK_birth_new_new (b E s h : ℝ) (τ m : Fin np → ℝ) {l : ℕ}
    (y : ProbedPath W np × ℝ) (hblk : GclSuccBlocks b E s h W l y.1.1 (phase y.2))
    {k : Fin np} (hk : ⌊(W : ℝ) * τ k⌋₊ = l) :
    b3ClosedKAt b E s h τ m W (l + 1) y k k =
      bilinear (((Real.sqrt (m k / W) : ℝ) : ℂ) • y.1.2 k) (birthG b E s h W l y.1.1 (phase y.2))
        (((Real.sqrt (m k / W) : ℝ) : ℂ) • y.1.2 k) := by
  rw [b3ClosedKAt_eq_gcl, entry_eq_dot, RawTag.dot_reindex (headEquiv l W),
    probeColumns_comp_new τ m y.1.2 hk, hblk, RawTag.dot_fromBlocks]
  simp only [star_zero, zero_dotProduct, mulVec_zero, add_zero]
  rfl

/-!
## The fresh corner at a passive closed input
-/

/-- `𝒢 = R_cl + R_clΔR_cl` at a passive closed input (`TagBirth.g11_eq_resolvent_add`). -/
theorem birthG_eq {b E : ℝ} (s h : ℝ) (hη : 0 < etaZ b E) {l : ℕ} (ω : GrowthPath W) (z : ℂ)
    (hX : (passiveY (closedNearX b E s h W l ω z)).PosSemidef) :
    birthG b E s h W l ω z = passiveResolvent b E (closedNearX b E s h W l ω z) +
      passiveResolvent b E (closedNearX b E s h W l ω z) *
        freshDelta b E (closedNearX b E s h W l ω z) (freshSample W l ω) *
        passiveResolvent b E (closedNearX b E s h W l ω z) :=
  BlockBand.SourceProcess.TagBirth.g11_eq_resolvent_add hη hX _

/-- `K𝒢 = 1 + ΔR_cl` and `𝒢K = 1 + R_clΔ` at a passive closed input. -/
theorem birthK_mul_birthG {b E : ℝ} (s h : ℝ) (hη : 0 < etaZ b E) {l : ℕ} (ω : GrowthPath W)
    (z : ℂ) (hX : (passiveY (closedNearX b E s h W l ω z)).PosSemidef) :
    birthK b E s h W l ω z * birthG b E s h W l ω z =
        1 + freshDelta b E (closedNearX b E s h W l ω z) (freshSample W l ω) *
          passiveResolvent b E (closedNearX b E s h W l ω z) ∧
      birthG b E s h W l ω z * birthK b E s h W l ω z =
        1 + passiveResolvent b E (closedNearX b E s h W l ω z) *
          freshDelta b E (closedNearX b E s h W l ω z) (freshSample W l ω) := by
  have hK := (isUnit_iff_isUnit_det _).mp (BlockBand.SourceProcess.TagBirth.isUnit_pencil hη hX)
  have hKR : birthK b E s h W l ω z * passiveResolvent b E (closedNearX b E s h W l ω z) = 1 :=
    Matrix.mul_nonsing_inv _ hK
  have hRK : passiveResolvent b E (closedNearX b E s h W l ω z) * birthK b E s h W l ω z = 1 :=
    Matrix.nonsing_inv_mul _ hK
  rw [birthG_eq s h hη ω z hX]
  constructor
  · rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hKR, Matrix.one_mul]
  · rw [Matrix.add_mul, hRK, Matrix.mul_assoc, Matrix.mul_assoc, hRK, Matrix.mul_one]

end BlockBand.SourceProcess.PhysApprox.B3
