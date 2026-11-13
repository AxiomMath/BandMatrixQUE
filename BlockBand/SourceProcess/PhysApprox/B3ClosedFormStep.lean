module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormDefs
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormAlg
public import BlockBand.SourceProcess.RawTag.UpdPins
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# The closed exact update at one step (deterministic)

For one sample and one phase `z` (with the invertibilities that hold almost surely), at a step
`l → l+1`, `l ≥ 1`, for two old tags `k, k'`:
`𝒦_cl,l+1 - 𝒦_cl,l = u_k* Δ(X_cl, F_l) v_k'` (**`closedK_step`**), with `u = closedNearU`,
`v = closedNearV`, `X_cl = closedNearX`.

The proof: the closed `𝒦` is `𝒥*Gcl𝒥` with `Gcl = G - cz U QΠ𝕊 Uᴴ` (`b3ClosedKAt_eq_gcl`), and
`Gcl` inverts the **far-closed interior pencil** `Pn - C Y_cl Cᴴ` at every length
(`closedPencil_at`, `ClosedForm.closed_pencil_mul`); `Y_cl` depends only on the time-`s` data and
the phase. Near-end growth hypotheses `Y_cl` in place (`closedPencil_succ_submatrix`), so the
abstract Schur step `RawTag.grown_interior_mul` applies to the closed pencil with the closed
near column, row and resolvent.
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

/-!
## Notation-free definitions
-/

/-- `Y_cl = κ(1 - tΠ)⁻¹Π`, `t = zζ̄/ζ`, `κ = -cz/ζ²`: the far-closing port self-energy shift. -/
def closedFarY (b E s h : ℝ) (W : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (-((((2 * etaZ b E : ℝ) : ℂ) * Complex.I) * z) / boundaryZ b E ^ 2) •
    ((1 - (z * (star (boundaryZ b E) / boundaryZ b E)) •
      farEmbed (closingPairing b E h W (closeLen s W) ω))⁻¹ *
      farEmbed (closingPairing b E h W (closeLen s W) ω))

/-- The closed interior inverse `Gcl = G - cz U(1 - zN)⁻¹Π𝕊Uᴴ` at length `n`. -/
def gclAt (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  (fullInverse b E W n ω).toBlocks₁₁ - ((((2 * etaZ b E : ℝ) : ℂ) * Complex.I) * z) •
    (boundaryToInterior b E W n ω *
      ((1 - z • closingN (scatteringMatrix b E W n ω)
          (farEmbed (omittedProj b E h W (closeLen s W) ω))
          (farEmbed (closingPairing b E h W (closeLen s W) ω)))⁻¹ *
        (farEmbed (closingPairing b E h W (closeLen s W) ω) *
          (scatteringMatrix b E W n ω * (boundaryToInterior b E W n ω)ᴴ))))

/-!
## Small facts
-/

theorem nearSel_mul_farEmbed (X : Matrix (Fin W) (Fin W) ℂ) : nearSel W * farEmbed X = 0 := by
  ext x y
  simp only [nearSel, farEmbed, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h1 h2 <;> simp_all

theorem farEmbed_mul_nearSel_conj (X : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed X * (nearSel W)ᴴ = 0 := by
  ext x y; simp [nearSel, farEmbed, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem c_eq_sub_star (b E : ℝ) :
    (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) = boundaryZ b E - star (boundaryZ b E) := by
  apply Complex.ext <;> simp [etaZ]
  ring

theorem b3ClosedKAt_eq_gcl (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ) (y : ProbedPath W np × ℝ) :
    b3ClosedKAt b E s h τ m W n y = (probeColumns W n τ m y.1.2)ᴴ *
      gclAt b E s h W n y.1.1 (phase y.2) * probeColumns W n τ m y.1.2 := by
  simp only [b3ClosedKAt, gclAt, complexSourceK, probeFrame, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]

theorem entry_eq_dot {α β : Type*} [Fintype α] (A : Matrix α β ℂ) (M : Matrix α α ℂ) (i j : β) :
    (Aᴴ * M * A) i j = star (fun x => A x i) ⬝ᵥ (M *ᵥ fun x => A x j) := by
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, conjTranspose_apply, dotProduct, mulVec, Pi.star_apply]

theorem probeColumns_comp_old (τ m : Fin np → ℝ) (g : Fin np → Fin W → ℂ) {l : ℕ} {k : Fin np}
    (hk : ⌊(W : ℝ) * τ k⌋₊ < l) :
    (fun x => probeColumns W (l + 1) τ m g x k) ∘ headEquiv l W =
      Sum.elim (0 : Fin W → ℂ) (fun x => probeColumns W l τ m g x k) := by
  funext x
  rcases x with x | ⟨i, x⟩
  · simp only [Function.comp_apply, Sum.elim_inl, Pi.zero_apply]
    simp [probeColumns, headEquiv_inl]
    omega
  · simp only [Function.comp_apply, headEquiv_inr, probeColumns, Sum.elim_inr, Fin.val_succ]
    have : (⌊(W : ℝ) * τ k⌋₊ < l + 1 ∧ i.val + 1 = l + 1 - 1 - ⌊(W : ℝ) * τ k⌋₊) ↔
        (⌊(W : ℝ) * τ k⌋₊ < l ∧ i.val = l - 1 - ⌊(W : ℝ) * τ k⌋₊) := by omega
    simp only [this]

theorem dot_elim_zero {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂] (P : Matrix m₁ m₁ ℂ)
    (Q : Matrix m₁ m₂ ℂ) (R : Matrix m₂ m₁ ℂ) (T : Matrix m₂ m₂ ℂ) (a c : m₂ → ℂ) :
    star (Sum.elim (0 : m₁ → ℂ) a) ⬝ᵥ (fromBlocks P Q R T *ᵥ Sum.elim (0 : m₁ → ℂ) c) =
      star a ⬝ᵥ (T *ᵥ c) := by
  rw [fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type]

theorem probeCol_eq (b E : ℝ) (τ m : Fin np → ℝ) (n : ℕ) (k : Fin np) (x : ProbedPath W np) :
    probeCol b E τ m W n k x =
      (boundaryToInterior b E W n x.1)ᴴ *ᵥ fun a => probeColumns W n τ m x.2 a k := by
  funext a
  simp [probeCol, probeFrame, Matrix.mul_apply, mulVec, dotProduct]

/-!
## The old path and the far-closed pencil
-/

/-- The old-path identities at length `n`. -/
theorem old_facts_at (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (hA : ∀ k, (ω.1 k).IsHermitian)
    (hη : 0 < (boundaryZ b E).im) (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) :
    (pathMatrix (pathAt W n ω) - (E : ℂ) • 1 - (boundaryZ b E)⁻¹ •
        (pathPortCoupling (pathAt W n ω) * (pathPortCoupling (pathAt W n ω))ᴴ)) *
        (fullInverse b E W n ω).toBlocks₁₁ = 1 ∧
      (pathPortCoupling (pathAt W n ω))ᴴ * (fullInverse b E W n ω).toBlocks₁₁ =
        -(boundaryZ b E • (scatteringMatrix b E W n ω * (boundaryToInterior b E W n ω)ᴴ)) ∧
      (pathMatrix (pathAt W n ω) - (E : ℂ) • 1 - (boundaryZ b E)⁻¹ •
        (pathPortCoupling (pathAt W n ω) * (pathPortCoupling (pathAt W n ω))ᴴ)) *
        boundaryToInterior b E W n ω = -((boundaryZ b E)⁻¹ • pathPortCoupling (pathAt W n ω)) ∧
      (pathPortCoupling (pathAt W n ω))ᴴ * boundaryToInterior b E W n ω =
        1 - boundaryZ b E • boundaryResolvent b E W n ω := by
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  have hM := isUnit_fullPathMatrix b E n ω hA hη hF
  refine ⟨RawTag.interior_pencil_mul b E n ω hM hz, ?_, (RawTag.boundary_eqs b E n ω hA hη hF).1,
    ?_⟩
  · obtain ⟨-, h2⟩ := RawTag.interior_eqs b E n ω hM
    rw [add_eq_zero_iff_eq_neg] at h2
    rw [h2, RawTag.fullInverse_21_eq b E n ω hA]
  · obtain ⟨-, h2⟩ := full_solution b E n ω hM
    rw [← h2]; abel

/-- **`Gcl` inverts the far-closed pencil** at length `n`. -/
theorem closedPencil_at (b E s h : ℝ) (n : ℕ) (ω : GrowthPath W) (z : ℂ)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1))
    (hU : IsUnit (1 - z • closingN (scatteringMatrix b E W n ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (hY : IsUnit (1 - (z * (star (boundaryZ b E) / boundaryZ b E)) •
      farEmbed (closingPairing b E h W (closeLen s W) ω)).det) :
    (pathMatrix (pathAt W n ω) - (E : ℂ) • 1 - (boundaryZ b E)⁻¹ •
        (pathPortCoupling (pathAt W n ω) * (pathPortCoupling (pathAt W n ω))ᴴ) -
        pathPortCoupling (pathAt W n ω) * closedFarY b E s h W ω z *
          (pathPortCoupling (pathAt W n ω))ᴴ) * gclAt b E s h W n ω z = 1 := by
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  obtain ⟨hG, hCG, hPU, hCU⟩ := old_facts_at b E n ω hA hη hF
  have hAPi : farEmbed (omittedProj b E h W (closeLen s W) ω) *
      farEmbed (closingPairing b E h W (closeLen s W) ω) =
        farEmbed (closingPairing b E h W (closeLen s W) ω) := by
    rw [farEmbed_mul, omittedProj_mul_closingPairing]
  exact closed_pencil_mul hG hCG hPU hCU rfl (c_eq_sub_star b E) hAPi (mul_nonsing_inv _ hU)
    (nonsing_inv_mul _ hY) (by field_simp; ring) (by field_simp)

/-- **Near-end growth keeps the far closing**: the grown far-closed pencil, newest block
first. -/
theorem closedPencil_succ_submatrix (b E : ℝ) {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W)
    (Yc : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hnsY : nearSel W * Yc = 0)
    (hYn : Yc * (nearSel W)ᴴ = 0) :
    (pathMatrix (pathAt W (l + 1) ω) - (E : ℂ) • 1 - (boundaryZ b E)⁻¹ •
        (pathPortCoupling (pathAt W (l + 1) ω) * (pathPortCoupling (pathAt W (l + 1) ω))ᴴ) -
        pathPortCoupling (pathAt W (l + 1) ω) * Yc *
          (pathPortCoupling (pathAt W (l + 1) ω))ᴴ).submatrix (headEquiv l W) (headEquiv l W) =
      fromBlocks (ω.1 l - (E : ℂ) • 1 - (boundaryZ b E)⁻¹ • (ω.2 (l + 1) * (ω.2 (l + 1))ᴴ))
        (nearCol W l ω)ᴴ (nearCol W l ω)
        (pathMatrix (pathAt W l ω) - (E : ℂ) • 1 -
          (boundaryZ b E)⁻¹ • (farCoupling W l ω * (farCoupling W l ω)ᴴ) -
          farCoupling W l ω * Yc * (farCoupling W l ω)ᴴ) := by
  set z := boundaryZ b E
  set C' := pathPortCoupling (pathAt W (l + 1) ω)
  have e1 : ∀ (P Q : Matrix (Fin (l + 1) × Fin W) (Fin (l + 1) × Fin W) ℂ),
      (P - Q).submatrix (headEquiv l W) (headEquiv l W) =
        P.submatrix (headEquiv l W) (headEquiv l W) -
          Q.submatrix (headEquiv l W) (headEquiv l W) := fun _ _ => rfl
  have e2 : ∀ (P Q : Matrix (Fin (l + 1) × Fin W) (Fin (l + 1) × Fin W) ℂ),
      (P - z⁻¹ • Q).submatrix (headEquiv l W) (headEquiv l W) =
        P.submatrix (headEquiv l W) (headEquiv l W) -
          z⁻¹ • Q.submatrix (headEquiv l W) (headEquiv l W) := fun _ _ => rfl
  have hY : (C' * Yc * C'ᴴ).submatrix (headEquiv l W) (headEquiv l W) =
      fromBlocks 0 0 0 (farCoupling W l ω * Yc * (farCoupling W l ω)ᴴ) := by
    have e3 : (C' * Yc * C'ᴴ).submatrix (headEquiv l W) (headEquiv l W) =
        C'.submatrix (headEquiv l W) id * Yc * (C'.submatrix (headEquiv l W) id)ᴴ := by
      ext i j
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
    rw [e3, coupling_succ_submatrix hl, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromRows_mul, fromRows_mul_fromCols]
    have h0 : ω.2 (l + 1) * nearSel W * Yc = 0 := by rw [Matrix.mul_assoc, hnsY, Matrix.mul_zero]
    have h1 : farCoupling W l ω * Yc * (ω.2 (l + 1) * nearSel W)ᴴ = 0 := by
      rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ Yc, hYn, Matrix.mul_zero,
        Matrix.zero_mul]
    rw [h0, h1, Matrix.zero_mul, Matrix.zero_mul]
  rw [e1, e2, pathMatrix_succ_submatrix, RawTag.coupling_sq_succ hl, hY]
  ext (x | x) (y | y) <;> simp [fromBlocks]

/-!
## The closed Schur step
-/

/-- The closed old-path facts of `RawTag.grown_interior_mul`, from the closed pencil and its
near column, row and corner. -/
theorem closed_old_facts {O : Type*} [Fintype O] [DecidableEq O] {PO G : Matrix O O ℂ}
    {nc U' : Matrix O (Fin W) ℂ} {V' : Matrix (Fin W) O ℂ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ζ : ℂ} (hζ : ζ ≠ 0) (hP : (PO - ζ⁻¹ • (nc * ncᴴ)) * G = 1) (hGn : G * nc = -(ζ • U'))
    (hnG : ncᴴ * G = -(ζ • V')) (hR : ζ⁻¹ • (1 + ζ⁻¹ • (ncᴴ * (G * nc))) = R) :
    PO * G = 1 + ζ⁻¹ • (nc * (ncᴴ * G)) ∧ ncᴴ * G = -(ζ • V') ∧ PO * U' = -(nc * R) ∧
      ncᴴ * U' = 1 - ζ • R := by
  have F1 : PO * G = 1 + ζ⁻¹ • (nc * (ncᴴ * G)) := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc] at hP
    exact sub_eq_iff_eq_add.mp hP
  have hU' : U' = -(ζ⁻¹ • (G * nc)) := by
    rw [hGn, smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ hζ, one_smul]
  refine ⟨F1, hnG, ?_, ?_⟩
  · rw [hU', ← hR, Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, F1]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one,
      Matrix.mul_smul, Matrix.mul_assoc]
  · rw [hU', ← hR, Matrix.mul_neg, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hζ, one_smul]
    abel

/-- **The closed exact update at one step** (on the far-closed path): for one
sample and phase with the a.s. invertibilities, a passive closed input, `l ≥ 1` and two old tags,
`𝒦_cl,l+1 - 𝒦_cl,l = u_k*Δ(X_cl, F_l)v_k'`. -/
theorem closedK_step (b E s h : ℝ) (τ m : Fin np → ℝ) {l : ℕ} (hl : 1 ≤ l)
    (y : ProbedPath W np × ℝ) (hA : ∀ k, (y.1.1.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W l y.1.1) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (l + 1) y.1.1) - (E : ℂ) • 1))
    (hB : IsUnit (y.1.1.2 (l + 1)))
    (hU : IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W l y.1.1)
      (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det)
    (hU' : IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W (l + 1) y.1.1)
      (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det)
    (hY : IsUnit (1 - (phase y.2 * (star (boundaryZ b E) / boundaryZ b E)) •
      farEmbed (closingPairing b E h W (closeLen s W) y.1.1)).det)
    (hR : IsUnit (closedNearR b E s h W l y.1.1 (phase y.2)).det)
    (hX : (passiveY (closedNearX b E s h W l y.1.1 (phase y.2))).PosSemidef)
    {k k' : Fin np} (hk : ⌊(W : ℝ) * τ k⌋₊ < l) (hk' : ⌊(W : ℝ) * τ k'⌋₊ < l) :
    b3ClosedKAt b E s h τ m W (l + 1) y k k' - b3ClosedKAt b E s h τ m W l y k k' =
      bilinear (closedNearU b E s h τ m W l k y)
        (freshDelta b E (b3ClosedX b E s h τ m W l y) (freshSample W l y.1.1))
        (closedNearV b E s h τ m W l k' y) := by
  set ω := y.1.1 with hω
  set z := phase y.2 with hzdef
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
  -- the entries
  rw [b3ClosedKAt_eq_gcl, b3ClosedKAt_eq_gcl, entry_eq_dot, entry_eq_dot,
    RawTag.dot_reindex (headEquiv l W), probeColumns_comp_old τ m y.1.2 hk,
    probeColumns_comp_old τ m y.1.2 hk', ← hω, ← hzdef, hGcl', dot_elim_zero, add_mulVec,
    dotProduct_add, add_sub_cancel_left, RawTag.dot_sandwich]
  unfold bilinear
  congr 1
  · congr 1
    rw [closedNearU, probeCol_eq]
    simp only [U', conjTranspose_mul, conjTranspose_conjTranspose, ← mulVec_mulVec]
    rfl
  · congr 1
    rw [closedNearV, probeCol_eq]
    simp only [V', ← mulVec_mulVec]
    rfl

end BlockBand.SourceProcess.PhysApprox.B3

