module

public import BlockBand.Palm.ReferenceFlowBackwardGauss
public import BlockBand.Palm.ReferenceFlowGenerator
public import BlockBand.Palm.ReferenceFlowRoot

/-!
# Backward equation of the reference flow: the composite test function and its Itô drift

Hypothesis: the Gaussian input `MultivariateGaussianIBP` (explicit, only in
`drift_eq_refGenerator`).

For a bounded-`C²` test `f`, a state `z` and a matrix `n` put
`Ftil f z n = E f(nᴴ z + (1 - nᴴ n)^{1/2} G)` (`G ~ matCircularLaw`), i.e.
`Ftil f z = gaussMean f ∘ g₀ z` with `g₀ z n = (nᴴ z, sqrtOneSub (nᴴ n))`. On the open set
`opNorm (nᴴ n) < 1` it is `C²` (`contDiffAt_Ftil`), with the first and second derivatives
computed from the chain rule (`fderiv_Ftil_apply`, `fderiv_fderiv_Ftil_apply_of`).

**Drift identity** (`drift_eq_refGenerator`). For the rotation coefficients `D = rotationDrift ρ κ`
and `σ_α = rotationNoise ρ α` (symmetric nonnegative `ρ`, nonnegative `κ`),
`DFtil(n)[D n] + ½ Σ_α D²Ftil(n)[σ_α n, σ_α n] = refGenerator ρ κ h_n z` with
`h_n(z') = E f(nᴴ z' + S G)`, `S = (1 - nᴴ n)^{1/2}`. Proof: `σ_α` is skew-Hermitian, so the
direction `σ_α n` leaves `nᴴ n` fixed to first order; the remaining `G`-terms combine into
`Df(Y)[B G]` with `B = DS(nᴴn)[nᴴ(2D + Σ_α σ_αᴴ σ_α) n] = DS(nᴴn)[-nᴴ diag(κ) n]`
(`two_drift_add_sum_noise`), and `fderiv_sqrtOneSub_anticomm` gives
`SB + BS = nᴴ diag(κ) n`; then `itoDrift_eq_refGenerator`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow.Backward

open MeasureTheory Set Filter Matrix BlockBand.Palm.ReferenceFlow
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionFlow (rotX rotY rotationNoise rotationDrift)

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

local instance (priority := high) frobUnifC {n : Type*} [Fintype n] :
    UniformSpace (Matrix n n ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℂ)).toUniformSpace

local instance (priority := high) frobTopC {n : Type*} [Fintype n] :
    TopologicalSpace (Matrix n n ℂ) :=
  (frobUnifC (n := n)).toTopologicalSpace

variable {N p : ℕ}

/-! ## The Gram map `n ↦ nᴴ n` -/

/-- `(X, Y) ↦ Xᴴ Y` as a real-bilinear map. -/
def bwConjMulLin : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ]
    Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.mk₂ ℝ (fun X Y => Xᴴ * Y)
    (fun X X' Y => by simp [conjTranspose_add, Matrix.add_mul])
    (fun c X Y => by simp [conjTranspose_smul])
    (fun X Y Y' => by simp [Matrix.mul_add])
    (fun c X Y => by simp)

/-- `(X, Y) ↦ Xᴴ Y` as a continuous real-bilinear map. -/
def bwConjMul : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ →L[ℝ]
    Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      bwConjMulLin)

@[simp] theorem bwConjMul_apply (X Y : Matrix (Fin N) (Fin N) ℂ) : bwConjMul X Y = Xᴴ * Y :=
  rfl

/-- The Gram map `n ↦ nᴴ n`. -/
def gram (n : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := nᴴ * n

theorem gram_isHermitian (n : Matrix (Fin N) (Fin N) ℂ) : (gram n).IsHermitian := by
  simp [gram, Matrix.IsHermitian, conjTranspose_mul]

theorem hasFDerivAt_gram (n : Matrix (Fin N) (Fin N) ℂ) :
    HasFDerivAt gram (bwConjMul n + bwConjMul.flip n) n := by
  have h := bwConjMul.hasFDerivAt_of_bilinear (hasFDerivAt_id n) (hasFDerivAt_id n)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp

theorem fderiv_gram : fderiv ℝ (gram (N := N)) = ⇑(bwConjMul + bwConjMul.flip :
    Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ) :=
  funext fun n => (hasFDerivAt_gram n).fderiv

theorem fderiv_gram_apply (n v : Matrix (Fin N) (Fin N) ℂ) :
    fderiv ℝ gram n v = nᴴ * v + vᴴ * n := by
  rw [(hasFDerivAt_gram n).fderiv]
  simp

theorem fderiv_fderiv_gram_apply (n v w : Matrix (Fin N) (Fin N) ℂ) :
    fderiv ℝ (fderiv ℝ gram) n v w = vᴴ * w + wᴴ * v := by
  rw [fderiv_gram, ContinuousLinearMap.fderiv]
  simp

theorem contDiff_gram : ContDiff ℝ ⊤ (gram (N := N)) :=
  (bwConjMul.isBoundedBilinearMap.contDiff).comp (contDiff_id.prodMk contDiff_id)

theorem isOpen_gram_lt : IsOpen {n : Matrix (Fin N) (Fin N) ℂ | opNorm (gram n) < 1} :=
  isOpen_opNorm_lt_one_frobenius.preimage contDiff_gram.continuous

/-! ## The composite `Ftil f z = gaussMean f ∘ g₀ z` -/

/-- `n ↦ nᴴ z` as a real-linear map. -/
def adjZ (z : RefState N p) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] RefState N p :=
  LinearMap.toContinuousLinearMap
    { toFun := fun n => lmul nᴴ z
      map_add' := fun n n' => by rw [conjTranspose_add, lmul_add_mat]
      map_smul' := fun t n => by
        rw [conjTranspose_smul, star_trivial]
        exact (lmulRightLin z).map_smul t nᴴ }

@[simp] theorem adjZ_apply (z : RefState N p) (n : Matrix (Fin N) (Fin N) ℂ) :
    adjZ z n = lmul nᴴ z := rfl

/-- `g₀ z n = (nᴴ z, (1 - nᴴ n)^{1/2})`. -/
def g₀ (z : RefState N p) (n : Matrix (Fin N) (Fin N) ℂ) :
    RefState N p × Matrix (Fin N) (Fin N) ℂ :=
  (adjZ z n, sqrtOneSub (gram n))

/-- `Ftil f z n = E f(nᴴ z + (1 - nᴴ n)^{1/2} G)`. -/
def Ftil (f : RefState N p → ℝ) (z : RefState N p) (n : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  gaussMean f (g₀ z n)

theorem Ftil_eq (f : RefState N p → ℝ) (z : RefState N p) (n : Matrix (Fin N) (Fin N) ℂ) :
    Ftil f z n = ∫ G, f (lmul nᴴ z + lmul (sqrtOneSub (nᴴ * n)) G) ∂matCircularLaw N p := rfl

theorem contDiffAt_sqrtOneSub_gram {n : Matrix (Fin N) (Fin N) ℂ} (hn : opNorm (gram n) < 1) :
    ContDiffAt ℝ 2 (fun m => sqrtOneSub (gram m)) n := by
  have hS : ContDiffAt ℝ 2 sqrtOneSub (gram n) :=
    (contDiffOn_sqrtOneSub.contDiffAt (isOpen_opNorm_lt_one_frobenius.mem_nhds hn)).of_le
      le_top
  exact hS.comp n (contDiff_gram.contDiffAt.of_le le_top)

theorem contDiffAt_g₀ (z : RefState N p) {n : Matrix (Fin N) (Fin N) ℂ}
    (hn : opNorm (gram n) < 1) : ContDiffAt ℝ 2 (g₀ z) n :=
  (adjZ z).contDiff.contDiffAt.prodMk (contDiffAt_sqrtOneSub_gram hn)

theorem fderiv_g₀_apply (z : RefState N p) {n : Matrix (Fin N) (Fin N) ℂ}
    (hn : opNorm (gram n) < 1) (v : Matrix (Fin N) (Fin N) ℂ) :
    fderiv ℝ (g₀ z) n v =
      (lmul vᴴ z, fderiv ℝ sqrtOneSub (gram n) (nᴴ * v + vᴴ * n)) := by
  have hS : DifferentiableAt ℝ (fun m => sqrtOneSub (gram m)) n :=
    (contDiffAt_sqrtOneSub_gram hn).differentiableAt (by norm_num)
  have hS' : DifferentiableAt ℝ sqrtOneSub (gram n) :=
    (contDiffOn_sqrtOneSub.contDiffAt (isOpen_opNorm_lt_one_frobenius.mem_nhds hn)).differentiableAt
      (by simp)
  have h := DifferentiableAt.fderiv_prodMk (adjZ z).differentiableAt hS
  rw [show g₀ z = fun m => (adjZ z m, sqrtOneSub (gram m)) from rfl, h,
    ContinuousLinearMap.prod_apply, (adjZ z).fderiv]
  have hc := fderiv_comp_apply' (J := sqrtOneSub) (P := gram) hS'
    (contDiff_gram.contDiffAt.differentiableAt (by simp)) v
  simp only [Function.comp_def] at hc
  rw [hc, fderiv_gram_apply]
  rfl

theorem fderiv_fderiv_g₀_fst (z : RefState N p) {n : Matrix (Fin N) (Fin N) ℂ}
    (hn : opNorm (gram n) < 1) (v w : Matrix (Fin N) (Fin N) ℂ) :
    (fderiv ℝ (fderiv ℝ (g₀ z)) n v w).1 = 0 := by
  have h := fderiv_fderiv_clm_comp_apply (ContinuousLinearMap.fst ℝ (RefState N p)
    (Matrix (Fin N) (Fin N) ℂ)) (contDiffAt_g₀ z hn) v w
  rw [show (fun y => ContinuousLinearMap.fst ℝ (RefState N p) (Matrix (Fin N) (Fin N) ℂ)
      (g₀ z y)) = ⇑(adjZ z) from rfl, fderiv_fderiv_clm] at h
  simpa using h.symm

theorem fderiv_fderiv_g₀_snd (z : RefState N p) {n : Matrix (Fin N) (Fin N) ℂ}
    (hn : opNorm (gram n) < 1) (v w : Matrix (Fin N) (Fin N) ℂ) :
    (fderiv ℝ (fderiv ℝ (g₀ z)) n v w).2 =
      fderiv ℝ (fderiv ℝ sqrtOneSub) (gram n) (nᴴ * v + vᴴ * n) (nᴴ * w + wᴴ * n) +
        fderiv ℝ sqrtOneSub (gram n) (vᴴ * w + wᴴ * v) := by
  have h := fderiv_fderiv_clm_comp_apply (ContinuousLinearMap.snd ℝ (RefState N p)
    (Matrix (Fin N) (Fin N) ℂ)) (contDiffAt_g₀ z hn) v w
  have hS : ContDiffAt ℝ 2 sqrtOneSub (gram n) :=
    (contDiffOn_sqrtOneSub.contDiffAt (isOpen_opNorm_lt_one_frobenius.mem_nhds hn)).of_le
      le_top
  have h2 := fderiv_fderiv_comp_apply hS (contDiff_gram.contDiffAt.of_le le_top) v w
  rw [show (fun y => ContinuousLinearMap.snd ℝ (RefState N p) (Matrix (Fin N) (Fin N) ℂ)
      (g₀ z y)) = sqrtOneSub ∘ gram from rfl, h2, fderiv_gram_apply, fderiv_gram_apply,
    fderiv_fderiv_gram_apply] at h
  simpa using h.symm

theorem contDiffAt_Ftil {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (z : RefState N p) {n : Matrix (Fin N) (Fin N) ℂ} (hn : opNorm (gram n) < 1) :
    ContDiffAt ℝ 2 (Ftil f z) n :=
  (gaussMean_derivs hf).1.contDiffAt.comp n (contDiffAt_g₀ z hn)

/-- `DFtil(n)[v] = E Df(Y)[vᴴ z + DS(nᴴn)[nᴴ v + vᴴ n] G]`. -/
theorem fderiv_Ftil_apply {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (z : RefState N p) {n : Matrix (Fin N) (Fin N) ℂ} (hn : opNorm (gram n) < 1)
    (v : Matrix (Fin N) (Fin N) ℂ) :
    fderiv ℝ (Ftil f z) n v =
      ∫ G, fderiv ℝ f (lmul nᴴ z + lmul (sqrtOneSub (gram n)) G)
        (lmul vᴴ z + lmul (fderiv ℝ sqrtOneSub (gram n) (nᴴ * v + vᴴ * n)) G)
        ∂matCircularLaw N p := by
  have hd := fderiv_comp_apply' (J := gaussMean f) (P := g₀ z)
    ((gaussMean_derivs hf).1.differentiable (by norm_num) _)
    ((contDiffAt_g₀ z hn).differentiableAt (by norm_num)) v
  rw [show Ftil f z = gaussMean f ∘ g₀ z from rfl, hd, (gaussMean_derivs hf).2.1,
    fderiv_g₀_apply z hn]
  rfl

/-- `D²Ftil(n)[v,v]` in a direction with `nᴴ v + vᴴ n = 0`. -/
theorem fderiv_fderiv_Ftil_apply_of {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (z : RefState N p) {n : Matrix (Fin N) (Fin N) ℂ} (hn : opNorm (gram n) < 1)
    {v : Matrix (Fin N) (Fin N) ℂ} (hv : nᴴ * v + vᴴ * n = 0) :
    fderiv ℝ (fderiv ℝ (Ftil f z)) n v v =
      ∫ G, fderiv ℝ (fderiv ℝ f) (lmul nᴴ z + lmul (sqrtOneSub (gram n)) G)
        (lmul vᴴ z) (lmul vᴴ z) ∂matCircularLaw N p +
      ∫ G, fderiv ℝ f (lmul nᴴ z + lmul (sqrtOneSub (gram n)) G)
        (lmul (fderiv ℝ sqrtOneSub (gram n) (vᴴ * v + vᴴ * v)) G) ∂matCircularLaw N p := by
  have h2 := fderiv_fderiv_comp_apply (J := gaussMean f) (P := g₀ z)
    (gaussMean_derivs hf).1.contDiffAt (contDiffAt_g₀ z hn) v v
  have hP2 : fderiv ℝ (fderiv ℝ (g₀ z)) n v v =
      (0, fderiv ℝ sqrtOneSub (gram n) (vᴴ * v + vᴴ * v)) := by
    refine Prod.ext (fderiv_fderiv_g₀_fst z hn v v) ?_
    rw [fderiv_fderiv_g₀_snd z hn v v, hv]
    simp
  rw [show Ftil f z = gaussMean f ∘ g₀ z from rfl, h2, (gaussMean_derivs hf).2.2,
    (gaussMean_derivs hf).2.1, fderiv_g₀_apply z hn, hP2, hv]
  simp only [map_zero, lmul_zero_mat, add_zero, zero_add]
  rfl

/-! ## The rotation algebra -/

theorem bwRotX_conjTranspose (i j : Fin N) : (rotX i j)ᴴ = -rotX i j := by
  simp [rotX, conjTranspose_sub, conjTranspose_single]

theorem bwRotY_conjTranspose (i j : Fin N) : (rotY i j)ᴴ = -rotY i j := by
  simp [rotY, conjTranspose_add, conjTranspose_single, add_comm, single_neg]

theorem bwRotationNoise_conjTranspose (ρ : Fin N → Fin N → ℝ) (α : RotIdx N) :
    (rotationNoise ρ α)ᴴ = -rotationNoise ρ α := by
  unfold rotationNoise
  split_ifs <;> simp [conjTranspose_smul, bwRotX_conjTranspose, bwRotY_conjTranspose]

theorem rotationDrift_conjTranspose (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) :
    (rotationDrift ρ κ)ᴴ = rotationDrift ρ κ := by
  unfold rotationDrift
  rw [diagonal_conjTranspose]
  congr 1
  funext k
  simp [Complex.conj_ofReal]

theorem sum_noise_conj_mul (ρ : Fin N → Fin N → ℝ) (hρs : ∀ k l, ρ k l = ρ l k)
    (hρ0 : ∀ k l, 0 ≤ ρ k l) :
    ∑ α : RotIdx N, (rotationNoise ρ α)ᴴ * rotationNoise ρ α =
      diagonal fun k => (((∑ m ∈ Finset.univ.erase k, ρ k m : ℝ)) : ℂ) := by
  have hpair : ∀ i j : Fin N, ∑ q : Fin 2, (rotationNoise ρ ((i, j), q))ᴴ *
      rotationNoise ρ ((i, j), q) =
      if i < j then ((ρ i j : ℝ) : ℂ) • (single i i (1 : ℂ) + single j j 1) else 0 := by
    intro i j
    rw [Fin.sum_univ_two]
    simp only [bwRotationNoise_conjTranspose, neg_mul]
    unfold rotationNoise
    by_cases hij : i < j
    · simp only [hij, ite_true, show ((1 : Fin 2) = 0) = False from by decide, ite_false,
        Fin.isValue]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        smul_smul, ← neg_add, ← smul_add, rotX_mul_self_add_rotY_mul_self, smul_smul,
        ← neg_smul]
      congr 1
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg (hρ0 i j) zero_le_two)]
      push_cast
      ring
    · simp [hij]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [hpair]
  ext k l
  rw [Matrix.sum_apply]
  simp_rw [Matrix.sum_apply]
  rw [diagonal_apply]
  have hent : ∀ i j : Fin N, (if i < j then ((ρ i j : ℝ) : ℂ) •
      (single i i (1 : ℂ) + single j j 1) else (0 : Matrix (Fin N) (Fin N) ℂ)) k l =
      if k = l then (if i < j then ((ρ i j : ℝ) : ℂ) * ((if i = k then 1 else 0) +
        (if j = k then 1 else 0)) else 0) else 0 := by
    intro i j
    rcases eq_or_ne k l with rfl | hkl
    · by_cases hij : i < j <;> simp [hij, single_apply]
    · simp only [hkl, ite_false]
      by_cases hij : i < j
      · simp only [hij, ite_true, Matrix.smul_apply, Matrix.add_apply, single_apply, smul_eq_mul]
        have h1 : ¬(i = k ∧ i = l) := fun h => hkl (h.1.symm.trans h.2)
        have h2 : ¬(j = k ∧ j = l) := fun h => hkl (h.1.symm.trans h.2)
        simp [h1, h2]
      · simp [hij]
  simp_rw [hent]
  by_cases hkl : k = l
  · subst hkl
    simp only [ite_true]
    have hreal : ∑ i : Fin N, ∑ j : Fin N, (if i < j then ρ i j * ((if i = k then 1 else 0) +
        (if j = k then 1 else 0)) else 0 : ℝ) = ∑ m ∈ Finset.univ.erase k, ρ k m := by
      rw [sum_lt_pair ρ hρs (fun i => if i = k then 1 else 0),
        Finset.sum_eq_single k (fun m _ hm => by simp [hm]) (by simp)]
      simp
    rw [← hreal]
    simp only [Complex.ofReal_sum, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_zero]
  · simp [hkl]

/-- `2D + Σ_α σ_αᴴ σ_α = -diag(κ)`. -/
theorem two_drift_add_sum_noise (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ)
    (hρs : ∀ k l, ρ k l = ρ l k) (hρ0 : ∀ k l, 0 ≤ ρ k l) :
    rotationDrift ρ κ + rotationDrift ρ κ +
        ∑ α : RotIdx N, (rotationNoise ρ α)ᴴ * rotationNoise ρ α =
      -diagonal fun k => (κ k : ℂ) := by
  rw [sum_noise_conj_mul ρ hρs hρ0]
  unfold rotationDrift
  rw [diagonal_add, diagonal_add, diagonal_neg]
  congr 1
  funext k
  push_cast
  ring

/-! ## The drift identity -/

theorem integrable_fderiv_add_lmul {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (m : RefState N p) (S B : Matrix (Fin N) (Fin N) ℂ) (u : RefState N p) :
    Integrable (fun G => fderiv ℝ f (m + lmul S G) (u + lmul B G)) (matCircularLaw N p) :=
  ((integrable_fderiv_const hf m S u).add (integrable_fderiv_lmul hf m S B)).congr
    (Eventually.of_forall fun G => by simp only [Pi.add_apply, map_add])

/-- The pointwise algebra behind `drift_eq_refGenerator`. -/
theorem drift_pointwise (L : RefState N p →L[ℝ] ℝ)
    (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ)
    (DS : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (G z : RefState N p)
    (n : Matrix (Fin N) (Fin N) ℂ) (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ)
    (hρs : ∀ k l, ρ k l = ρ l k) (hρ0 : ∀ k l, 0 ≤ ρ k l) :
    L (lmul (rotationDrift ρ κ * n)ᴴ z + lmul (DS (nᴴ * (rotationDrift ρ κ * n) +
        (rotationDrift ρ κ * n)ᴴ * n)) G) +
      (1 / 2 : ℝ) * ∑ α : RotIdx N, (Q (lmul (rotationNoise ρ α * n)ᴴ z)
          (lmul (rotationNoise ρ α * n)ᴴ z) +
        L (lmul (DS ((rotationNoise ρ α * n)ᴴ * (rotationNoise ρ α * n) +
          (rotationNoise ρ α * n)ᴴ * (rotationNoise ρ α * n))) G)) =
    L (lmul (nᴴ * rotationDrift ρ κ) z) +
      (1 / 2 : ℝ) * ∑ α : RotIdx N, Q (lmul (nᴴ * rotationNoise ρ α) z)
        (lmul (nᴴ * rotationNoise ρ α) z) +
      L (lmul (DS (-(nᴴ * diagonal (fun k => (κ k : ℂ)) * n))) G) := by
  set D := rotationDrift ρ κ with hD
  set σ := rotationNoise ρ with hσ
  set T : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ := L.comp ((lmulRightCLM N p G).comp DS) with hT
  have hlin : ∀ X : Matrix (Fin N) (Fin N) ℂ, L (lmul (DS X) G) = T X := fun X => rfl
  have hDn : (D * n)ᴴ = nᴴ * D := by
    rw [conjTranspose_mul, hD, rotationDrift_conjTranspose]
  have hσn : ∀ α, lmul (σ α * n)ᴴ z = -lmul (nᴴ * σ α) z := fun α => by
    rw [conjTranspose_mul, hσ, bwRotationNoise_conjTranspose, Matrix.mul_neg]
    funext i β
    simp [lmul, Finset.sum_neg_distrib]
  have hmat : nᴴ * (D * n) + (D * n)ᴴ * n + (1 / 2 : ℝ) • ∑ α : RotIdx N,
      ((σ α * n)ᴴ * (σ α * n) + (σ α * n)ᴴ * (σ α * n)) =
      -(nᴴ * diagonal (fun k => (κ k : ℂ)) * n) := by
    have h2 := two_drift_add_sum_noise ρ κ hρs hρ0
    have e : ∀ α, (σ α * n)ᴴ * (σ α * n) + (σ α * n)ᴴ * (σ α * n) =
        (2 : ℝ) • (nᴴ * ((σ α)ᴴ * σ α) * n) := fun α => by
      rw [two_smul, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    simp_rw [e, ← Finset.smul_sum, smul_smul]
    rw [hDn, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul, ← Finset.sum_mul,
      ← Finset.mul_sum, ← Matrix.neg_mul, ← Matrix.mul_neg, ← h2]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rfl
  rw [map_add]
  simp only [hlin]
  rw [← hmat, map_add T, map_add T, map_smul, map_sum]
  simp only [hσn, map_neg, _root_.neg_apply, neg_neg, hDn, smul_eq_mul, Finset.sum_add_distrib,
    mul_add, map_add]
  ring

/-- **Drift identity.** For `opNorm (nᴴ n) < 1`:
`DFtil(n)[D n] + ½ Σ_α D²Ftil(n)[σ_α n, σ_α n] = refGenerator ρ κ h_n z`. -/
theorem drift_eq_refGenerator (hIBP : MultivariateGaussianIBP) {C : ℝ}
    {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f) (z : RefState N p)
    {n : Matrix (Fin N) (Fin N) ℂ} (hn : opNorm (gram n) < 1) (ρ : Fin N → Fin N → ℝ)
    (κ : Fin N → ℝ) (hρs : ∀ k l, ρ k l = ρ l k) (hρ0 : ∀ k l, 0 ≤ ρ k l)
    (hκ0 : ∀ k, 0 ≤ κ k) :
    fderiv ℝ (Ftil f z) n (rotationDrift ρ κ * n) +
        (1 / 2 : ℝ) * ∑ α : RotIdx N, fderiv ℝ (fderiv ℝ (Ftil f z)) n
          (rotationNoise ρ α * n) (rotationNoise ρ α * n) =
      refGenerator (fun _ => ρ) (fun _ => κ) 0
        (fun z' => ∫ G, f (lmul nᴴ z' + lmul (sqrtOneSub (nᴴ * n)) G) ∂matCircularLaw N p)
        z := by
  set A := gram n with hA
  set S := sqrtOneSub A with hSdef
  set D := rotationDrift ρ κ with hD
  set σ := rotationNoise ρ with hσ
  set DS := fderiv ℝ sqrtOneSub A with hDS
  set B := DS (-(nᴴ * diagonal (fun k => (κ k : ℂ)) * n)) with hB
  have hAh : A.IsHermitian := gram_isHermitian n
  have hS : S.IsHermitian := sqrtOneSub_isHermitian hn hAh
  have hKh : (-(nᴴ * diagonal (fun k => (κ k : ℂ)) * n)).IsHermitian := by
    refine IsHermitian.neg ?_
    have hd : (star fun k => (κ k : ℂ)) = fun k => (κ k : ℂ) := funext fun k => by simp
    simp [Matrix.IsHermitian, conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, hd]
  have hBh : B.IsHermitian := fderiv_sqrtOneSub_isHermitian hn hAh hKh
  have hSB : S * B + B * S = nᴴ * diagonal (fun k => (κ k : ℂ)) * n := by
    have h := fderiv_sqrtOneSub_anticomm hn (-(nᴴ * diagonal (fun k => (κ k : ℂ)) * n))
    rw [neg_neg] at h
    rw [add_comm]
    exact h
  change _ = refGenerator (fun _ => ρ) (fun _ => κ) 0
    (fun z' => ∫ G, f (lmul nᴴ z' + lmul S G) ∂matCircularLaw N p) z
  rw [← itoDrift_eq_refGenerator hIBP hf n S B ρ κ hρs hρ0 hκ0 hS hBh hSB z]
  -- the skew directions
  have hskew : ∀ α, nᴴ * (σ α * n) + (σ α * n)ᴴ * n = 0 := fun α => by
    rw [conjTranspose_mul, bwRotationNoise_conjTranspose, Matrix.mul_assoc, Matrix.neg_mul,
      Matrix.mul_neg, ← Matrix.mul_assoc, add_neg_cancel]
  rw [fderiv_Ftil_apply hf z hn]
  simp_rw [fderiv_fderiv_Ftil_apply_of hf z hn (hskew _)]
  simp only [← hA, ← hSdef, ← hDS, ← hD, ← hσ]
  have hI1 := integrable_fderiv_add_lmul hf (lmul nᴴ z) S (DS (nᴴ * (D * n) + (D * n)ᴴ * n))
    (lmul (D * n)ᴴ z)
  have hI23 : ∀ α, Integrable (fun G => fderiv ℝ (fderiv ℝ f) (lmul nᴴ z + lmul S G)
      (lmul (σ α * n)ᴴ z) (lmul (σ α * n)ᴴ z) + fderiv ℝ f (lmul nᴴ z + lmul S G)
      (lmul (DS ((σ α * n)ᴴ * (σ α * n) + (σ α * n)ᴴ * (σ α * n))) G))
      (matCircularLaw N p) := fun α =>
    (integrable_D2_lmul hf _ S _ _).add (integrable_fderiv_lmul hf _ S _)
  have hsum : ∑ α : RotIdx N, (∫ G, fderiv ℝ (fderiv ℝ f) (lmul nᴴ z + lmul S G)
        (lmul (σ α * n)ᴴ z) (lmul (σ α * n)ᴴ z) ∂matCircularLaw N p +
      ∫ G, fderiv ℝ f (lmul nᴴ z + lmul S G)
        (lmul (DS ((σ α * n)ᴴ * (σ α * n) + (σ α * n)ᴴ * (σ α * n))) G) ∂matCircularLaw N p) =
      ∫ G, ∑ α : RotIdx N, (fderiv ℝ (fderiv ℝ f) (lmul nᴴ z + lmul S G)
        (lmul (σ α * n)ᴴ z) (lmul (σ α * n)ᴴ z) + fderiv ℝ f (lmul nᴴ z + lmul S G)
        (lmul (DS ((σ α * n)ᴴ * (σ α * n) + (σ α * n)ᴴ * (σ α * n))) G))
        ∂matCircularLaw N p := by
    rw [integral_finsetSum _ fun α _ => hI23 α]
    exact Finset.sum_congr rfl fun α _ =>
      (integral_add (integrable_D2_lmul hf _ S _ _) (integrable_fderiv_lmul hf _ S _)).symm
  rw [hsum, ← integral_const_mul, ← integral_add hI1 ((integrable_finsetSum _ fun α _ =>
    hI23 α).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun G => ?_)
  exact drift_pointwise (fderiv ℝ f (lmul nᴴ z + lmul S G))
    (fderiv ℝ (fderiv ℝ f) (lmul nᴴ z + lmul S G)) DS G z n ρ κ hρs hρ0

end BlockBand.Palm.ReferenceFlow.Backward
