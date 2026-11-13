module

public import BlockBand.SourceProcess.PhysApprox.B3JetDisc
public import BlockBand.SourceProcess.PhysApprox.B3JetRecur
public import BlockBand.SourceProcess.ClosedFeas.Trace

/-!
# The closing shift at the closing time, factorized (deterministic)

At the closing time `n = n_s` the closing data are built from the same scattering matrix `𝕊`:
`A = farEmbed(1_{T≤h²}(T))`, `Π = farEmbed(g(T)S_ffᴴ)`, `T = 1 - S_ffᴴS_ff`. In the eigenbasis
`U` of `T` (eigenvalues `t_k`), `N = Π𝕊A` acts on `F U` (`F = farInj`) as `diag(φ_k)`,
`φ = g(t)(1-t)1_{t≤h²}`, so `(1 - zN)⁻¹FU = FU diag(1 - zφ)⁻¹`, and

`R_cl - R_o = P diag(z g_k/(1 - zφ_k)) Q`,  `P = ι*ℝFU`, `Q = Uᴴ S_ffᴴ (Fᴴ𝕊ιᴴ)`.

Unitarity gives `‖P e_k‖ = (2η)⁻¹√t_k` and `‖Qᴴe_k‖ ≤ √t_k`, hence the cavity kernel.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedFeas
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedReduce
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## The eigenbasis of a Hermitian matrix
-/

section Eigen

variable {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.IsHermitian)

/-- The eigenvector matrix `U`. -/
abbrev eigU : Matrix (Fin W) (Fin W) ℂ := (hT.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)

theorem eigU_conj_mul : (eigU hT)ᴴ * eigU hT = 1 := Unitary.coe_star_mul_self _

theorem eigU_mul_conj : eigU hT * (eigU hT)ᴴ = 1 := Unitary.coe_mul_star_self _

theorem cfc_mul_eigU (f : ℝ → ℝ) :
    cfc f T * eigU hT = eigU hT * diagonal (RCLike.ofReal ∘ f ∘ hT.eigenvalues) := by
  rw [hT.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc,
    show star (eigU hT) = (eigU hT)ᴴ from rfl, eigU_conj_mul, Matrix.mul_one]

theorem mul_eigU : T * eigU hT = eigU hT * diagonal (RCLike.ofReal ∘ hT.eigenvalues) := by
  have h : T * eigU hT = _ * eigU hT := congrArg (fun M => M * eigU hT) hT.spectral_theorem
  rw [h, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc,
    show star (eigU hT) = (eigU hT)ᴴ from rfl, eigU_conj_mul, Matrix.mul_one]

theorem cfc_eq_eigU (f : ℝ → ℝ) :
    cfc f T = eigU hT * diagonal (RCLike.ofReal ∘ f ∘ hT.eigenvalues) * (eigU hT)ᴴ := by
  rw [← cfc_mul_eigU, Matrix.mul_assoc, eigU_mul_conj, Matrix.mul_one]

/-- Column `k` of `U`. -/
abbrev eigVec (k : Fin W) : Fin W → ℂ := fun i => eigU hT i k

theorem star_eigVec_dot (k : Fin W) : star (eigVec hT k) ⬝ᵥ eigVec hT k = 1 := by
  have := congrFun (congrFun (eigU_conj_mul hT) k) k
  simpa [Matrix.mul_apply, dotProduct, conjTranspose_apply] using this

theorem mulVec_eigVec (k : Fin W) :
    T *ᵥ eigVec hT k = (hT.eigenvalues k : ℂ) • eigVec hT k := by
  funext i
  have := congrFun (congrFun (mul_eigU hT) i) k
  rw [Matrix.mul_diagonal, Matrix.mul_apply] at this
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [this, mul_comm]
  rfl

end Eigen

/-!
## Vector norms
-/

theorem vecNorm_le_of_sq {n m : Type*} [Fintype n] [Fintype m] {a : n → ℂ} {c : m → ℂ}
    (h : vecNorm a ^ 2 ≤ vecNorm c ^ 2) : vecNorm a ≤ vecNorm c :=
  (pow_le_pow_iff_left₀ (vecNorm_nonneg a) (vecNorm_nonneg c) (by norm_num)).1 h

theorem vecNorm_sq_eq_re {n : Type*} [Fintype n] (x : n → ℂ) :
    vecNorm x ^ 2 = (star x ⬝ᵥ x).re := by
  rw [star_self_eq, Complex.ofReal_re]

theorem nearSel_mulVec (x : Fin 2 × Fin W → ℂ) : nearSel W *ᵥ x = fun a => x (0, a) := by
  funext a
  simp [nearSel, mulVec, dotProduct]

theorem nearSel_conj_mulVec (v : Fin W → ℂ) :
    (nearSel W)ᴴ *ᵥ v = fun c => if c.1 = 0 then v c.2 else 0 := by
  funext ⟨i, a⟩
  simp only [mulVec, dotProduct, conjTranspose_apply, nearSel]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Prod.ext_iff, Ne.symm hb]) (by simp)]
  by_cases hi : i = 0 <;> simp [hi, Prod.ext_iff]

theorem vecNorm_nearSel_mulVec_le (x : Fin 2 × Fin W → ℂ) :
    vecNorm (nearSel W *ᵥ x) ≤ vecNorm x := by
  rw [nearSel_mulVec]
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have : 0 ≤ ∑ a : Fin W, ‖x (1, a)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  linarith

theorem vecNorm_nearSel_conj_mulVec (v : Fin W → ℂ) :
    vecNorm ((nearSel W)ᴴ *ᵥ v) = vecNorm v := by
  rw [nearSel_conj_mulVec]
  unfold vecNorm
  congr 1
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

theorem vecNorm_unitary_mulVec {n : Type*} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ}
    (hS : Sᴴ * S = 1) (x : n → ℂ) : vecNorm (S *ᵥ x) = vecNorm x := by
  have h : star (S *ᵥ x) ⬝ᵥ (S *ᵥ x) = star x ⬝ᵥ x := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hS, vecMul_one]
  have h2 : vecNorm (S *ᵥ x) ^ 2 = vecNorm x ^ 2 := by
    rw [vecNorm_sq_eq_re, vecNorm_sq_eq_re, h]
  exact (pow_left_inj₀ (vecNorm_nonneg _) (vecNorm_nonneg _) (by norm_num)).1 h2

/-!
## Small identities
-/

theorem nearSel_mul_farInj : nearSel W * farInj W = 0 := by
  ext a b
  simp only [nearSel, farInj, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs with h1 h2 <;> simp_all

theorem nearSel_conj_mul_nearSel' : (nearSel W)ᴴ * nearSel W = nearPortProj W := by
  ext x y
  simp only [nearSel, nearPortProj, Matrix.mul_apply, conjTranspose_apply, diagonal_apply]
  rw [Finset.sum_eq_single x.2 (fun a _ ha => by
    by_cases h1 : x = (0, a) <;> simp_all [Prod.ext_iff]) (by simp)]
  rcases x with ⟨i, a⟩; rcases y with ⟨j, c⟩
  fin_cases i <;> fin_cases j <;> by_cases hac : a = c <;> simp [Prod.ext_iff, hac, eq_comm]

theorem vecNorm_col_sq {m : Type*} [Fintype m] (M : Matrix m (Fin W) ℂ) (k : Fin W) :
    vecNorm (fun j => M j k) ^ 2 = ((Mᴴ * M) k k).re := by
  rw [vecNorm_sq_eq_re]
  simp [dotProduct, Matrix.mul_apply, conjTranspose_apply]

theorem vecNorm_smul {n : Type*} [Fintype n] (a : ℂ) (v : n → ℂ) :
    vecNorm (a • v) = ‖a‖ * vecNorm v := by
  rw [vecNorm_eq, vecNorm_eq, WithLp.toLp_smul, norm_smul]

theorem vecNorm_neg {n : Type*} [Fintype n] (v : n → ℂ) : vecNorm (-v) = vecNorm v := by
  simp [vecNorm]

/-!
## The scalar factor
-/

/-- The diagonal factor of `N` on the eigenbasis, `φ = g(t)(1-t)1_{t≤h²}`. -/
def nPhi (h t : ℝ) : ℂ := ((pairWeight h t : ℝ) : ℂ) * (1 - (t : ℂ)) * ((omitIndicator h t : ℝ) : ℂ)

theorem nPhi_of_le {h t : ℝ} (hh : h ^ 2 < 1) (ht : t ≤ h ^ 2) :
    nPhi h t = ((Real.sqrt (1 - t) : ℝ) : ℂ) := by
  have h1 : 0 < 1 - t := by linarith
  have hr : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1
  unfold nPhi pairWeight omitIndicator
  simp only [ht, ↓reduceIte]
  push_cast
  have hsq : ((Real.sqrt (1 - t) : ℝ) : ℂ) ^ 2 = 1 - (t : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt h1.le]; push_cast; ring
  have hne : ((Real.sqrt (1 - t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [← hsq]
  field_simp

theorem nPhi_of_lt {h t : ℝ} (ht : h ^ 2 < t) : nPhi h t = 0 := by
  unfold nPhi pairWeight omitIndicator
  simp [not_le.2 ht]

theorem one_sub_mul_nPhi_ne {h t : ℝ} (hh : h ^ 2 < 1) {z : ℂ} (hz : ‖z‖ = 1)
    (hz1 : z ≠ 1) : 1 - z * nPhi h t ≠ 0 := by
  rcases le_or_gt t (h ^ 2) with ht | ht
  · rw [nPhi_of_le hh ht]
    intro h0
    have e : z * ((Real.sqrt (1 - t) : ℝ) : ℂ) = 1 := by linear_combination -h0
    have hn := congrArg norm e
    rw [norm_mul, hz, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), norm_one] at hn
    have hr : ((Real.sqrt (1 - t) : ℝ) : ℂ) = 1 := by rw [hn]; simp
    rw [hr, mul_one] at e
    exact hz1 e
  · rw [nPhi_of_lt ht]; simp

/-- **The scalar bound**: `|z (1 - zφ)⁻¹ g| t ≤ κ(t, z)`. -/
theorem norm_coef_mul_le {h t : ℝ} (hh : h ^ 2 < 1) (ht0 : 0 ≤ t) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z * ((1 - z * nPhi h t)⁻¹ * ((pairWeight h t : ℝ) : ℂ))‖ * t ≤ shiftKernel h t z := by
  unfold shiftKernel
  rcases le_or_gt t (h ^ 2) with ht | ht
  · simp only [ht, ↓reduceIte]
    rw [nPhi_of_le hh ht, max_eq_left ht0]
    have h1 : 0 < 1 - t := by linarith
    have hr : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1
    unfold pairWeight
    simp only [ht, ↓reduceIte]
    rw [norm_mul, hz, one_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hr)]
    apply le_of_eq
    field_simp
  · unfold pairWeight
    simp [not_le.2 ht]

/-!
## The factorization at the closing time
-/

/-- **The closing shift at the closing time, factorized**: `R_cl - R_o = P diag(d) Q` with
`|d_k| ‖Qᴴe_k‖ ‖Pe_k‖ ≤ (2η)⁻¹ κ(t_k, z)`. -/
theorem closedShift_factor (b E s h : ℝ) (hh : h ^ 2 < 1) (ω : GrowthPath W) {z : ℂ}
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W (closeLen s W) ω) - (E : ℂ) • 1))
    (hS : scatteringMatrix b E W (closeLen s W) ω *
      (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hU : IsUnit (1 - z • closingN (scatteringMatrix b E W (closeLen s W) ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (hR : IsUnit (closedNearR b E s h W (closeLen s W) ω z).det) :
    ∃ (P Q : Matrix (Fin W) (Fin W) ℂ) (d : Fin W → ℂ),
      passiveResolvent b E (closedNearX b E s h W (closeLen s W) ω z) -
          passiveResolvent b E (pathX b E W (closeLen s W) ω) = P * diagonal d * Q ∧
      ∀ k, ‖d k‖ * vecNorm (fun i => star (Q k i)) * vecNorm (fun j => P j k) ≤
        (2 * etaZ b E)⁻¹ * shiftKernel h (farEig b E W (closeLen s W) ω k) z := by
  set n := closeLen s W with hn
  set S := scatteringMatrix b E W n ω with hSdef
  have hS' : Sᴴ * S = 1 := mul_eq_one_comm.mp hS
  set hT := isHermitian_farTransmission b E W n ω
  set T := farTransmission b E W n ω with hTdef
  set t := hT.eigenvalues with htdef
  set U := eigU hT with hUdef
  set F := farInj W
  set ns := nearSel W
  set Rr := boundaryResolvent b E W n ω with hRr
  set gC := cfc (pairWeight h) T with hgC
  set A := farEmbed (omittedProj b E h W n ω) with hAdef
  set Pi := farEmbed (closingPairing b E h W n ω) with hPidef
  have hz0 : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  -- `N` on the eigenbasis
  set Dt := diagonal (RCLike.ofReal ∘ t : Fin W → ℂ) with hDt
  set Dg := diagonal (RCLike.ofReal ∘ pairWeight h ∘ t : Fin W → ℂ) with hDg
  set Di := diagonal (RCLike.ofReal ∘ omitIndicator h ∘ t : Fin W → ℂ) with hDi
  set φ : Fin W → ℂ := fun k => nPhi h (t k) with hφ
  have hAFU : A * (F * U) = F * U * Di := by
    rw [← Matrix.mul_assoc, hAdef, farEmbed_mul_farInj, Matrix.mul_assoc]
    rw [show omittedProj b E h W n ω = cfc (omitIndicator h) T from rfl, cfc_mul_eigU,
      ← Matrix.mul_assoc]
  have hPSF : Pi * S * F = F * (gC * (1 - T)) := pi_mul_far (S := S) gC
  have h1T : (1 - T) * U = U * (1 - Dt) := by
    rw [Matrix.sub_mul, Matrix.one_mul, mul_eigU, Matrix.mul_sub, Matrix.mul_one]
  have hdiag : Dg * (1 - Dt) * Di = diagonal φ := by
    rw [← diagonal_one, hDt, hDg, hDi, diagonal_sub, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    rfl
  have hN : closingN S A Pi * (F * U) = F * U * diagonal φ := by
    calc closingN S A Pi * (F * U) = Pi * S * (A * (F * U)) := by
          simp only [closingN, Matrix.mul_assoc]
      _ = Pi * S * F * (U * Di) := by rw [hAFU]; simp only [Matrix.mul_assoc]
      _ = F * (gC * ((1 - T) * U)) * Di := by rw [hPSF]; simp only [Matrix.mul_assoc]
      _ = F * ((gC * U) * (1 - Dt)) * Di := by rw [h1T]; simp only [Matrix.mul_assoc]
      _ = F * U * (Dg * (1 - Dt) * Di) := by
          rw [hgC, cfc_mul_eigU]; simp only [Matrix.mul_assoc]; rfl
      _ = F * U * diagonal φ := by rw [hdiag]
  -- the eigenvalues are nonnegative
  set M := ns * S * F * U with hMdef
  have hMM : Mᴴ * M = Dt := by
    have e : Mᴴ * M = Uᴴ * ((F)ᴴ * (Sᴴ * ((ns)ᴴ * ns) * S) * F) * U := by
      simp only [hMdef, conjTranspose_mul, Matrix.mul_assoc]
    rw [e, nearSel_conj_mul_nearSel', far_outProj hS', show fT S = T from rfl, Matrix.mul_assoc,
      mul_eigU,
      ← Matrix.mul_assoc, eigU_conj_mul, Matrix.one_mul]
  have hMk : ∀ k, vecNorm (fun j => M j k) ^ 2 = t k := by
    intro k
    rw [vecNorm_col_sq, hMM, hDt, diagonal_apply_eq]
    simp
  have ht0 : ∀ k, 0 ≤ t k := fun k => by rw [← hMk k]; positivity
  -- the inverse of `1 - zN` on the eigenbasis
  have hφ0 : ∀ k, 1 - z * φ k ≠ 0 := fun k => one_sub_mul_nPhi_ne hh hz hz1
  set ψ : Fin W → ℂ := fun k => (1 - z * φ k)⁻¹ with hψ
  have hInv : (1 - z • closingN S A Pi)⁻¹ * (F * U) = F * U * diagonal ψ := by
    have e : (1 - z • closingN S A Pi) * (F * U) =
        F * U * diagonal (fun k => 1 - z * φ k) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hN,
        show diagonal (fun k => 1 - z * φ k) = 1 - z • diagonal φ by
          rw [← diagonal_one, ← diagonal_smul, diagonal_sub]; rfl,
        Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
    have hdd : diagonal (fun k => 1 - z * φ k) * diagonal ψ = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext k; exact mul_inv_cancel₀ (hφ0 k)
    have hinvL := nonsing_inv_mul _ hU
    calc (1 - z • closingN S A Pi)⁻¹ * (F * U)
        = (1 - z • closingN S A Pi)⁻¹ * (F * U *
            (diagonal (fun k => 1 - z * φ k) * diagonal ψ)) := by rw [hdd, Matrix.mul_one]
      _ = ((1 - z • closingN S A Pi)⁻¹ * ((1 - z • closingN S A Pi) * (F * U))) *
            diagonal ψ := by rw [e]; simp only [Matrix.mul_assoc]
      _ = F * U * diagonal ψ := by rw [← Matrix.mul_assoc _ (1 - z • _), hinvL, Matrix.one_mul]
  -- `Π𝕊ιᴴ`
  set Q := Uᴴ * (portBlock S 1 1)ᴴ * ((F)ᴴ * S * (ns)ᴴ) with hQdef
  have hPiS : Pi * S * (ns)ᴴ = F * U * Dg * Q := by
    rw [hPidef, show closingPairing b E h W n ω = gC * (portBlock S 1 1)ᴴ from rfl,
      farEmbed_eq_farInj, hgC, cfc_eq_eigU hT]
    simp only [hQdef, Matrix.mul_assoc]; rfl
  -- the closed corner
  have hcorner : closedNearR b E s h W n ω z - ns * Rr * (ns)ᴴ =
      z • (ns * Rr * ((1 - z • closingN S A Pi)⁻¹ * (Pi * S * (ns)ᴴ))) := by
    rw [closedNearR_eq_corner]
    have e1 : ns * Rr * (1 - A) * (ns)ᴴ = ns * Rr * (ns)ᴴ := by
      rw [Matrix.mul_assoc _ (1 - A), Matrix.sub_mul, Matrix.one_mul, hAdef,
        farEmbed_mul_nearSel_conj, sub_zero]
    have e2 : closingT S A Pi * (ns)ᴴ = Pi * S * (ns)ᴴ := by
      rw [closingT, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hAdef,
        farEmbed_mul_nearSel_conj, sub_zero]
    rw [e1, e2, add_sub_cancel_left]
    simp only [Matrix.mul_assoc]; rfl
  -- the resolvents
  have hRcl : passiveResolvent b E (closedNearX b E s h W n ω z) = closedNearR b E s h W n ω z := by
    unfold passiveResolvent closedNearX
    rw [sub_sub_cancel, Matrix.nonsing_inv_nonsing_inv _ hR]
  have hRo : passiveResolvent b E (pathX b E W n ω) = ns * Rr * (ns)ᴴ := by
    have h2 := (RawTag.boundary_eqs b E n ω hA hη hF).2
    obtain ⟨-, -, -, hCU⟩ := old_facts_at b E n ω hA hη hF
    rw [Matrix.mul_assoc, hCU, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      nearSel_mul_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, sub_right_inj] at h2
    have h3 : nearSel W * (boundaryResolvent b E W n ω * (nearSel W)ᴴ) =
        passiveResolvent b E (pathX b E W n ω) := by
      have := congrArg ((boundaryZ b E)⁻¹ • ·) h2
      simpa only [smul_smul, inv_mul_cancel₀ hz0, one_smul] using this
    rw [← h3, Matrix.mul_assoc]
  -- the factorization
  set d : Fin W → ℂ := fun k => z * (ψ k * ((pairWeight h (t k) : ℝ) : ℂ)) with hd
  set P := ns * Rr * F * U with hPdef
  refine ⟨P, Q, d, ?_, ?_⟩
  · rw [hRcl, hRo, hcorner, hPiS]
    have e : (1 - z • closingN S A Pi)⁻¹ * (F * U * Dg * Q) =
        F * U * (diagonal ψ * Dg) * Q := by
      rw [show F * U * Dg * Q = (F * U) * (Dg * Q) by simp only [Matrix.mul_assoc],
        ← Matrix.mul_assoc, hInv]
      simp only [Matrix.mul_assoc]
    rw [e, hDg, diagonal_mul_diagonal]
    rw [show diagonal d = z • diagonal (fun k => ψ k * (RCLike.ofReal ∘ pairWeight h ∘ t) k) by
      rw [← diagonal_smul]; rfl]
    simp only [hPdef, Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  · intro k
    have hη2 : 0 < etaZ b E := hη
    -- `P = -(c⁻¹) M`
    set c : ℂ := ((2 * etaZ b E : ℝ) : ℂ) * Complex.I with hc
    have hc0 : c ≠ 0 := by
      rw [hc]; refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast (by positivity : (2 * etaZ b E) ≠ 0)
    have hRrS : Rr = c⁻¹ • (1 - S) := by
      rw [hSdef, scatteringMatrix, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hnsF : ns * F = 0 := nearSel_mul_farInj
    have hPM : P = (-c⁻¹) • M := by
      calc P = ns * (c⁻¹ • (1 - S)) * F * U := by rw [hPdef, hRrS]
        _ = c⁻¹ • (ns * F * U - ns * S * F * U) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
              Matrix.mul_one]
        _ = (-c⁻¹) • M := by rw [hnsF, Matrix.zero_mul, zero_sub, smul_neg, neg_smul]
    have hPk : vecNorm (fun j => P j k) = (2 * etaZ b E)⁻¹ * vecNorm (fun j => M j k) := by
      rw [show (fun j => P j k) = (-c⁻¹) • (fun j => M j k) by funext j; rw [hPM]; rfl,
        vecNorm_smul, norm_neg, norm_inv, hc, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    -- `Qᴴ = -(ι𝕊ᴴιᴴ) M`
    set B := ns * Sᴴ * (ns)ᴴ with hB
    have hQM : Qᴴ = -(B * M) := by
      have e1 : Qᴴ = ns * Sᴴ * (F * (F)ᴴ) * S * F * U := by
        rw [hQdef, ← farInj_conj_mul_farInj S]
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]; rfl
      have e3 : F * (F)ᴴ = 1 - (ns)ᴴ * ns := by
        rw [nearSel_conj_mul_nearSel', one_sub_nearPortProj]
      have e4 : ns * Sᴴ * S = ns := by rw [Matrix.mul_assoc, hS', Matrix.mul_one]
      rw [e1, e3]
      calc ns * Sᴴ * (1 - (ns)ᴴ * ns) * S * F * U =
          ns * Sᴴ * S * F * U - ns * Sᴴ * (ns)ᴴ * (ns * S * F * U) := by
            simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
        _ = -(B * M) := by rw [e4, hnsF, Matrix.zero_mul, zero_sub]
    have hBn : ‖B‖ ≤ 1 := by
      refine opNorm_le_of_vec _ zero_le_one fun x => ?_
      rw [one_mul, hB, ← mulVec_mulVec, ← mulVec_mulVec]
      refine (vecNorm_nearSel_mulVec_le _).trans ?_
      rw [vecNorm_unitary_mulVec (by rw [conjTranspose_conjTranspose]; exact hS),
        vecNorm_nearSel_conj_mulVec]
    have hQk : vecNorm (fun i => star (Q k i)) ≤ vecNorm (fun j => M j k) := by
      have e : (fun i => star (Q k i)) = -(B *ᵥ fun j => M j k) := by
        funext i
        have := congrFun (congrFun hQM i) k
        rw [conjTranspose_apply] at this
        rw [this]
        simp [Matrix.mul_apply, mulVec, dotProduct]
      rw [e, vecNorm_neg]
      refine (vecNorm_mulVec_le B _).trans ?_
      have := vecNorm_nonneg (fun j => M j k)
      nlinarith
    have hdk := norm_coef_mul_le (t := t k) hh (ht0 k) hz
    have hv0 := vecNorm_nonneg (fun j => M j k)
    rw [hPk]
    calc ‖d k‖ * vecNorm (fun i => star (Q k i)) * ((2 * etaZ b E)⁻¹ * vecNorm (fun j => M j k))
        ≤ ‖d k‖ * vecNorm (fun j => M j k) * ((2 * etaZ b E)⁻¹ * vecNorm (fun j => M j k)) := by
          gcongr
      _ = (2 * etaZ b E)⁻¹ * (‖d k‖ * t k) := by rw [← hMk k]; ring
      _ ≤ (2 * etaZ b E)⁻¹ * shiftKernel h (farEig b E W n ω k) z :=
          mul_le_mul_of_nonneg_left hdk (by positivity)

end BlockBand.SourceProcess.PhysApprox.B3.Jet
