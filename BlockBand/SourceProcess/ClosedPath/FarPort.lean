module

public import BlockBand.SourceProcess.Closing.PhysHardy
public import BlockBand.SourceProcess.ClosedLimit.Frame

/-!
# Far-port algebra for the closed path at time `s`

* `cfc_mulVec_of_eigen`: `T v = t v ⇒ g(T) v = g(t) v` for Hermitian `T` and any `g : ℝ → ℝ`.
* `farInj`: the far-port embedding `ℂ^W → ℂ^{2W}` (Lean port `1` = far);
  `nearPortProj_mul_farInj`, `farInj_conj_mul_self`, `one_sub_nearPortProj`,
  `farEmbed_mul_farInj`, `farEmbed_mul_nearPortProj`.
* `farInj_conj_outProj_farInj`: the far compression of `P' = 𝕊ᴴP𝕊` is `S_nfᴴS_nf`; with
  `𝕊ᴴ𝕊 = 1` it equals `farTransmission = 1 - S_ffᴴS_ff` (`farTransmission_eq_of_unitary`).
* `omittedProj_mul_closingPairing`: `A_-Π = Π`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedPath

open Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedLimit
open BlockBand.Internal.Contracts.TransmissionPath

/-- **Functional calculus on an eigenvector**: `T v = t v ⇒ g(T) v = g(t) v`. -/
theorem cfc_mulVec_of_eigen {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℂ}
    (hT : T.IsHermitian) (g : ℝ → ℝ) {v : n → ℂ} {t : ℝ} (hv : T *ᵥ v = (t : ℂ) • v) :
    cfc g T *ᵥ v = (g t : ℂ) • v := by
  set U : Matrix n n ℂ := (hT.eigenvectorUnitary : Matrix n n ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set w := star U *ᵥ v
  have hspec : star U * T = diagonal (RCLike.ofReal ∘ hT.eigenvalues) * star U := by
    conv_lhs => rw [hT.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hw : ∀ i, (hT.eigenvalues i : ℂ) * w i = (t : ℂ) * w i := by
    intro i
    have := congrFun (congrArg (fun M => M *ᵥ v) hspec) i
    simp only [← mulVec_mulVec, hv, mulVec_smul, mulVec_diagonal, Function.comp_apply,
      Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hgw : diagonal (RCLike.ofReal ∘ g ∘ hT.eigenvalues) *ᵥ w = (g t : ℂ) • w := by
    funext i
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Function.comp_apply]
    by_cases h0 : w i = 0
    · simp [h0]
    · have : (hT.eigenvalues i : ℂ) = t := mul_right_cancel₀ h0 (hw i)
      rw [show hT.eigenvalues i = t by exact_mod_cast this]
      rfl
  rw [hT.cfc_eq g, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec]
  change U *ᵥ (diagonal (RCLike.ofReal ∘ g ∘ hT.eigenvalues) *ᵥ w) = _
  rw [hgw, mulVec_smul, mulVec_mulVec, hUU', one_mulVec]

variable {W : ℕ}

/-- The far-port embedding `ℂ^W → ℂ^{2W}`. -/
def farInj (W : ℕ) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  Matrix.of fun x a => if x = (1, a) then 1 else 0

theorem nearPortProj_mul_farInj : nearPortProj W * farInj W = 0 := by
  ext x a
  rw [nearPortProj, diagonal_mul]
  by_cases hx : x.1 = 0
  · simp [farInj, hx, Prod.ext_iff]
  · simp [hx]

theorem farInj_conj_mul_self : (farInj W)ᴴ * farInj W = 1 := by
  ext a b
  simp only [mul_apply, conjTranspose_apply, farInj, of_apply, one_apply]
  rw [Finset.sum_eq_single (1, a) (fun x _ hx => by simp [hx]) (by simp)]
  by_cases hab : a = b <;> simp [hab, Prod.ext_iff]

theorem one_sub_nearPortProj : 1 - nearPortProj W = farInj W * (farInj W)ᴴ := by
  ext x y
  simp only [Matrix.sub_apply, nearPortProj, mul_apply, conjTranspose_apply, farInj, of_apply,
    one_apply, diagonal_apply]
  rw [Finset.sum_eq_single y.2 (fun a _ ha => by
    by_cases h1 : x = (1, a) <;> by_cases h2 : y = (1, a) <;> simp_all [Prod.ext_iff]) (by simp)]
  rcases x with ⟨i, a⟩; rcases y with ⟨j, c⟩
  fin_cases i <;> fin_cases j <;> simp [Prod.ext_iff]

theorem farEmbed_mul_farInj (X : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed X * farInj W = farInj W * X := by
  ext x a
  simp only [farEmbed, farInj, mul_apply, of_apply]
  rw [Finset.sum_eq_single (1, a) (fun y _ hy => by simp [hy]) (by simp)]
  rcases x with ⟨i, c⟩
  rw [Finset.sum_eq_single c (fun d _ hd => by simp [Prod.ext_iff, Ne.symm hd]) (by simp)]
  fin_cases i <;> simp

theorem farEmbed_mul_nearPortProj (X : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed X * nearPortProj W = 0 := by
  ext x y
  rw [nearPortProj, mul_diagonal]
  by_cases hy : y.1 = 0
  · simp [farEmbed, hy]
  · simp [hy]

/-- The far compression of `P' = 𝕊ᴴP𝕊` is `S_nfᴴ S_nf`. -/
theorem farInj_conj_outProj_farInj (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (farInj W)ᴴ * (Sᴴ * nearPortProj W * S) * farInj W =
      (portBlock S 0 1)ᴴ * portBlock S 0 1 := by
  ext a b
  have e : ∀ M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      ((farInj W)ᴴ * M * farInj W) a b = M (1, a) (1, b) := by
    intro M
    simp only [mul_apply, conjTranspose_apply, farInj, of_apply]
    rw [Finset.sum_eq_single (1, b) (fun y _ hy => by simp [hy]) (by simp)]
    rw [Finset.sum_eq_single (1, a) (fun y _ hy => by simp [hy]) (by simp)]
    simp
  rw [e]
  simp only [mul_apply, conjTranspose_apply, nearPortProj, diagonal_apply, portBlock, of_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

/-- With `𝕊ᴴ𝕊 = 1`, `T_far = 1 - S_ffᴴS_ff = S_nfᴴS_nf`. -/
theorem farTransmission_eq_of_unitary {b E : ℝ} {n : ℕ} {ω : GrowthPath W}
    (hS : (scatteringMatrix b E W n ω)ᴴ * scatteringMatrix b E W n ω = 1) :
    farTransmission b E W n ω = (portBlock (scatteringMatrix b E W n ω) 0 1)ᴴ *
      portBlock (scatteringMatrix b E W n ω) 0 1 := by
  set S := scatteringMatrix b E W n ω
  ext a c
  have h := congrFun (congrFun hS (1, a)) (1, c)
  simp only [mul_apply, conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    one_apply, Prod.mk.injEq, true_and] at h
  simp only [farTransmission, farReflection, Matrix.sub_apply, mul_apply, conjTranspose_apply,
    portBlock, of_apply, one_apply]
  rw [← h]; ring

/-- `A_-Π = Π`. -/
theorem omittedProj_mul_closingPairing (b E h : ℝ) (n : ℕ) (ω : GrowthPath W) :
    omittedProj b E h W n ω * closingPairing b E h W n ω = closingPairing b E h W n ω := by
  unfold omittedProj closingPairing
  rw [← Matrix.mul_assoc, ← cfc_mul _ _ _ (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
  congr 2
  funext t
  unfold omitIndicator pairWeight
  split_ifs <;> simp

end BlockBand.SourceProcess.ClosedPath
