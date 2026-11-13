module

public import BlockBand.Palm.ReferenceFlowHeat
public import BlockBand.Palm.ReferenceFlowParamInt

/-!
# The pointwise generator identity of the reference flow

For `h(z) = E f(nᴴ z + (1 - nᴴ n)^{1/2} G)`, the Itô drift of the reference flow applied to `h`
equals the reference generator `refGenerator` (`itoDrift_eq_refGenerator`).

Proof: `h` is `C²` with `Dh(z)[w] = E Df(Y)[nᴴ w]`, `D²h(z)[w,w'] = E D²f(Y)[nᴴ w, nᴴ w']`
(`integral_affine_contDiff`); the rotation part is the algebra `X² + Y² = -2(E_ii + E_jj)` and
`σ_α = √(ρ_ij/2) X`; the Ornstein–Uhlenbeck part is the Stein identity
(`integral_fderiv_lmul`) followed by the contraction identity (`gaussPair_of_anticomm`) with
`W = nᴴ diag(√κ)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionFlow (rotX rotY rotationNoise rotationDrift)

variable {N p : ℕ}

/-!
## `lmul` as a function of the matrix
-/

theorem lmul_mul (P Q : Matrix (Fin N) (Fin N) ℂ) (z : RefState N p) :
    lmul (P * Q) z = lmul P (lmul Q z) := by
  funext i α
  simp only [lmul, mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lmul_add_mat (P Q : Matrix (Fin N) (Fin N) ℂ) (z : RefState N p) :
    lmul (P + Q) z = lmul P z + lmul Q z := by
  funext i α
  simp only [lmul, Matrix.add_apply, add_mul, Finset.sum_add_distrib, Pi.add_apply]

theorem lmul_smul_mat (c : ℂ) (P : Matrix (Fin N) (Fin N) ℂ) (z : RefState N p) :
    lmul (c • P) z = c • lmul P z := by
  funext i α
  simp only [lmul, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

theorem lmul_ofReal_smul_mat (t : ℝ) (P : Matrix (Fin N) (Fin N) ℂ) (z : RefState N p) :
    lmul ((t : ℂ) • P) z = t • lmul P z := by
  rw [lmul_smul_mat]
  funext i α
  simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]

theorem lmul_zero_mat (z : RefState N p) : lmul (0 : Matrix (Fin N) (Fin N) ℂ) z = 0 := by
  funext i α
  simp [lmul]

theorem lmul_cmul (P : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (z : RefState N p) :
    lmul P (c • z) = c • lmul P z := by
  funext i α
  simp only [lmul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem lmul_single_self (i : Fin N) (z : RefState N p) :
    lmul (Matrix.single i i (1 : ℂ)) z = rowProj i z := by
  funext k β
  by_cases h : k = i
  · subst h
    simp [lmul, rowProj, Matrix.single_apply]
  · simp [lmul, rowProj, h, Ne.symm h]

theorem lmul_diagonal (d : Fin N → ℂ) (z : RefState N p) :
    lmul (Matrix.diagonal d) z = fun k β => d k * z k β := by
  funext k β
  simp [lmul, Matrix.diagonal_apply]

/-!
## The rotation algebra
-/

theorem rotX_mul_self_add_rotY_mul_self (i j : Fin N) :
    rotX i j * rotX i j + rotY i j * rotY i j =
      ((-2 : ℝ) : ℂ) • (Matrix.single i i (1 : ℂ) + Matrix.single j j 1) := by
  simp only [rotX, rotY, sub_mul, mul_sub, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    single_mul_single_same, smul_smul, smul_add, mul_one]
  simp only [Complex.I_mul_I]
  push_cast
  module

theorem vfSq_lmul_sum (i j : Fin N) (z : RefState N p) :
    lmul (rotX i j) (lmul (rotX i j) z) + lmul (rotY i j) (lmul (rotY i j) z) =
      (-2 : ℝ) • (rowProj i z + rowProj j z) := by
  rw [← lmul_mul, ← lmul_mul, ← lmul_add_mat, rotX_mul_self_add_rotY_mul_self,
    lmul_ofReal_smul_mat, lmul_add_mat, lmul_single_self, lmul_single_self]

theorem lmul_rotationDrift (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (z : RefState N p) :
    lmul (rotationDrift ρ κ) z =
      ∑ k, (-(1 / 2 : ℝ) * ((∑ m ∈ Finset.univ.erase k, ρ k m) + κ k)) • rowProj k z := by
  unfold rotationDrift
  rw [lmul_diagonal]
  funext i α
  simp only [Finset.sum_apply, Pi.smul_apply, rowProj, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  simp [Complex.real_smul]

/-!
## Finite-sum combinatorics
-/

theorem sum_lt_pair (ρ : Fin N → Fin N → ℝ) (hρs : ∀ k l, ρ k l = ρ l k) (a : Fin N → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N, (if i < j then ρ i j * (a i + a j) else 0) =
      ∑ k, (∑ m ∈ Finset.univ.erase k, ρ k m) * a k := by
  have h1 : ∀ i j : Fin N, (if i < j then ρ i j * (a i + a j) else 0) =
      (if i < j then ρ i j * a i else 0) + (if i < j then ρ i j * a j else 0) := by
    intro i j; split_ifs <;> ring
  simp_rw [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then ρ i j * a j else 0)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.filter_ne', Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases lt_trichotomy k m with h | h | h
  · simp [h, not_lt_of_gt h, ne_of_gt h]
  · subst h; simp
  · simp [h, not_lt_of_gt h, ne_of_lt h, hρs m k]

/-!
## The algebraic generator identity
-/

theorem bilin_smul_smul (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ) (t : ℝ)
    (u : RefState N p) : Q (t • u) (t • u) = t * t * Q u u := by
  simp only [map_smul, _root_.smul_apply, smul_eq_mul]
  ring

theorem sum_rotationNoise (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ)
    (ρ : Fin N → Fin N → ℝ) (hρ0 : ∀ k l, 0 ≤ ρ k l) (z : RefState N p) :
    ∑ α : RotIdx N, Q (lmul (rotationNoise ρ α) z) (lmul (rotationNoise ρ α) z) =
      ∑ i : Fin N, ∑ j : Fin N, (if i < j then ρ i j / 2 *
        (Q (lmul (rotX i j) z) (lmul (rotX i j) z) + Q (lmul (rotY i j) z) (lmul (rotY i j) z))
        else 0) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two]
  unfold rotationNoise
  by_cases hij : i < j
  · simp only [hij, ite_true, lmul_ofReal_smul_mat, bilin_smul_smul]
    simp only [show ((1 : Fin 2) = 0) = False from by decide, ite_false]
    rw [Real.mul_self_sqrt (div_nonneg (hρ0 i j) zero_le_two)]
    ring
  · simp [hij, lmul_zero_mat]

/-- **Algebraic form of the generator identity**, for any linear `L` and bilinear `Q`. -/
theorem generator_algebra (L : RefState N p →L[ℝ] ℝ)
    (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ)
    (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (hρs : ∀ k l, ρ k l = ρ l k)
    (hρ0 : ∀ k l, 0 ≤ ρ k l) (z : RefState N p) (T : Fin N → ℝ) :
    L (lmul (rotationDrift ρ κ) z) +
        (1 / 2 : ℝ) * ∑ α : RotIdx N, Q (lmul (rotationNoise ρ α) z) (lmul (rotationNoise ρ α) z) +
        (1 / 4 : ℝ) * ∑ i : Fin N, κ i * T i =
      (1 / 4 : ℝ) * ∑ i : Fin N, ∑ j : Fin N,
          (if i < j then ρ i j * ((Q (lmul (rotX i j) z) (lmul (rotX i j) z) +
              L (lmul (rotX i j) (lmul (rotX i j) z))) +
            (Q (lmul (rotY i j) z) (lmul (rotY i j) z) +
              L (lmul (rotY i j) (lmul (rotY i j) z)))) else 0) +
        ∑ i : Fin N, κ i * (-(1 / 2 : ℝ) * L (rowProj i z) + (1 / 4 : ℝ) * T i) := by
  have hpair : ∀ i j : Fin N, (if i < j then ρ i j * ((Q (lmul (rotX i j) z) (lmul (rotX i j) z) +
        L (lmul (rotX i j) (lmul (rotX i j) z))) +
      (Q (lmul (rotY i j) z) (lmul (rotY i j) z) +
        L (lmul (rotY i j) (lmul (rotY i j) z)))) else 0) =
      2 * (if i < j then ρ i j / 2 * (Q (lmul (rotX i j) z) (lmul (rotX i j) z) +
        Q (lmul (rotY i j) z) (lmul (rotY i j) z)) else 0) +
      (-2) * (if i < j then ρ i j * (L (rowProj i z) + L (rowProj j z)) else 0) := by
    intro i j
    by_cases hij : i < j
    · have h := congrArg L (vfSq_lmul_sum i j z)
      rw [map_add, map_smul, map_add, smul_eq_mul] at h
      simp only [hij, ite_true]
      linear_combination ρ i j * h
    · simp [hij]
  have e1 : ∑ k, (-(1 / 2 : ℝ) * ((∑ m ∈ Finset.univ.erase k, ρ k m) + κ k)) * L (rowProj k z) =
      -(1 / 2 : ℝ) * ∑ k, (∑ m ∈ Finset.univ.erase k, ρ k m) * L (rowProj k z) +
        -(1 / 2 : ℝ) * ∑ k, κ k * L (rowProj k z) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ i, κ i * (-(1 / 2 : ℝ) * L (rowProj i z) + (1 / 4 : ℝ) * T i) =
      -(1 / 2 : ℝ) * ∑ k, κ k * L (rowProj k z) + (1 / 4 : ℝ) * ∑ i, κ i * T i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hpair, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_rotationNoise Q ρ hρ0 z, sum_lt_pair ρ hρs (fun k => L (rowProj k z)),
    lmul_rotationDrift, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [e1, e2]
  ring

/-!
## The Ornstein–Uhlenbeck part
-/

theorem lmul_diagonal_unitEntry (c : Fin N → ℝ) (j : Fin N) (α : Fin p) :
    lmul (Matrix.diagonal fun k => ((c k : ℝ) : ℂ)) (unitEntry j α : RefState N p) =
      c j • (unitEntry j α : RefState N p) := by
  rw [lmul_diagonal]
  funext k β
  by_cases h : k = j ∧ β = α
  · obtain ⟨rfl, rfl⟩ := h
    simp [unitEntry, Complex.real_smul]
  · simp [unitEntry, h]

theorem integrable_D2_add {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (m : RefState N p) (S : Matrix (Fin N) (Fin N) ℂ) (u v u' v' : RefState N p) :
    Integrable (fun G => D2 f (m + lmul S G) u v + D2 f (m + lmul S G) u' v')
      (matCircularLaw N p) :=
  (integrable_D2_lmul hf m S u v).add (integrable_D2_lmul hf m S u' v')

/-- `gaussPair Q W W` for `W = nᴴ diag(√κ)`. -/
theorem gaussPair_sqrtDiag (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ)
    (n : Matrix (Fin N) (Fin N) ℂ) (κ : Fin N → ℝ) (hκ0 : ∀ k, 0 ≤ κ k) :
    gaussPair Q (nᴴ * Matrix.diagonal fun k => ((Real.sqrt (κ k) : ℝ) : ℂ))
        (nᴴ * Matrix.diagonal fun k => ((Real.sqrt (κ k) : ℝ) : ℂ)) =
      ∑ i : Fin N, κ i * ∑ α : Fin p,
        (Q (lmul nᴴ (unitEntry i α)) (lmul nᴴ (unitEntry i α)) +
          Q (lmul nᴴ (Complex.I • unitEntry i α)) (lmul nᴴ (Complex.I • unitEntry i α))) := by
  unfold gaussPair
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [lmul_mul, lmul_diagonal_unitEntry, lmul_smul_real, smul_comm Complex.I, lmul_cmul,
    bilin_smul_smul, bilin_smul_smul, Real.mul_self_sqrt (hκ0 i)]
  ring

theorem sqrtDiag_mul_conjTranspose (n : Matrix (Fin N) (Fin N) ℂ) (κ : Fin N → ℝ)
    (hκ0 : ∀ k, 0 ≤ κ k) :
    nᴴ * Matrix.diagonal (fun k => (κ k : ℂ)) * n =
      (nᴴ * Matrix.diagonal fun k => ((Real.sqrt (κ k) : ℝ) : ℂ)) *
        (nᴴ * Matrix.diagonal fun k => ((Real.sqrt (κ k) : ℝ) : ℂ))ᴴ := by
  have hD : (Matrix.diagonal fun k => ((Real.sqrt (κ k) : ℝ) : ℂ)) *
      (Matrix.diagonal fun k => ((Real.sqrt (κ k) : ℝ) : ℂ))ᴴ =
      Matrix.diagonal (fun k => (κ k : ℂ)) := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext k
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hκ0 k)]
  rw [← hD, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- **Ornstein–Uhlenbeck part.** Stein identity plus contraction: for Hermitian `S, B` with
`SB + BS = nᴴ diag(κ) n`, `E Df(m + SG)[BG] = ¼ Σ_i κ_i Σ_α E (D²f(m+SG)[nᴴ e_{iα}, nᴴ e_{iα}] +
D²f(m+SG)[nᴴ i e_{iα}, nᴴ i e_{iα}])`. -/
theorem integral_ou_part (hIBP : MultivariateGaussianIBP) {C : ℝ} {f : RefState N p → ℝ}
    (hf : IsC2BoundedBy C f) (m : RefState N p) (n S B : Matrix (Fin N) (Fin N) ℂ)
    (κ : Fin N → ℝ) (hκ0 : ∀ k, 0 ≤ κ k) (hS : S.IsHermitian) (hB : B.IsHermitian)
    (hSB : S * B + B * S = nᴴ * Matrix.diagonal (fun k => (κ k : ℂ)) * n) :
    ∫ G, fderiv ℝ f (m + lmul S G) (lmul B G) ∂matCircularLaw N p =
      (1 / 4 : ℝ) * ∑ i : Fin N, κ i * ∑ α : Fin p,
        (∫ G, D2 f (m + lmul S G) (lmul nᴴ (unitEntry i α)) (lmul nᴴ (unitEntry i α))
            ∂matCircularLaw N p +
          ∫ G, D2 f (m + lmul S G) (lmul nᴴ (Complex.I • unitEntry i α))
            (lmul nᴴ (Complex.I • unitEntry i α)) ∂matCircularLaw N p) := by
  have hW := sqrtDiag_mul_conjTranspose n κ hκ0
  have hpt : ∀ G : RefState N p,
      gaussPair (fderiv ℝ (fderiv ℝ f) (m + lmul S G)) B S =
        (1 / 2 : ℝ) * ∑ i : Fin N, κ i * ∑ α : Fin p,
          (D2 f (m + lmul S G) (lmul nᴴ (unitEntry i α)) (lmul nᴴ (unitEntry i α)) +
            D2 f (m + lmul S G) (lmul nᴴ (Complex.I • unitEntry i α))
              (lmul nᴴ (Complex.I • unitEntry i α))) := by
    intro G
    rw [gaussPair_of_anticomm _ (fun u v => D2_symm hf.contDiff _ u v) hS hB (hSB.trans hW),
      gaussPair_sqrtDiag _ n κ hκ0]
    rfl
  have hsum : ∫ G, gaussPair (fderiv ℝ (fderiv ℝ f) (m + lmul S G)) B S ∂matCircularLaw N p =
      ∑ j : Fin N, ∑ α : Fin p, ∫ G,
        (D2 f (m + lmul S G) (lmul B (unitEntry j α)) (lmul S (unitEntry j α)) +
         D2 f (m + lmul S G) (Complex.I • lmul B (unitEntry j α))
          (Complex.I • lmul S (unitEntry j α))) ∂matCircularLaw N p := by
    unfold gaussPair
    change ∫ G, ∑ j : Fin N, ∑ α : Fin p,
        (D2 f (m + lmul S G) (lmul B (unitEntry j α)) (lmul S (unitEntry j α)) +
         D2 f (m + lmul S G) (Complex.I • lmul B (unitEntry j α))
          (Complex.I • lmul S (unitEntry j α))) ∂matCircularLaw N p = _
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun α _ =>
      integrable_D2_add hf m S _ _ _ _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun α _ => integrable_D2_add hf m S _ _ _ _]
  rw [integral_fderiv_lmul hIBP hf m S B, ← hsum, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_const_mul, integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun α _ =>
      integrable_D2_add hf m S _ _ _ _).const_mul _,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun α _ => integrable_D2_add hf m S _ _ _ _]
  simp only [integral_add (integrable_D2_lmul hf m S _ _) (integrable_D2_lmul hf m S _ _)]
  ring

/-!
## Derivatives of the Gaussian average
-/

/-- `h(z) = E f(Kz + SG)` is `C²` with `Dh(z)[u] = E Df(Kz+SG)[Ku]` and
`D²h(z)[u,v] = E D²f(Kz+SG)[Ku, Kv]`. -/
theorem gaussAvg_derivs {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (K S : Matrix (Fin N) (Fin N) ℂ) :
    ContDiff ℝ 2 (fun z => ∫ G, f (lmul K z + lmul S G) ∂matCircularLaw N p) ∧
      (∀ z u, fderiv ℝ (fun z => ∫ G, f (lmul K z + lmul S G) ∂matCircularLaw N p) z u =
        ∫ G, fderiv ℝ f (lmul K z + lmul S G) (lmul K u) ∂matCircularLaw N p) ∧
      (∀ z u v, D2 (fun z => ∫ G, f (lmul K z + lmul S G) ∂matCircularLaw N p) z u v =
        ∫ G, D2 f (lmul K z + lmul S G) (lmul K u) (lmul K v) ∂matCircularLaw N p) :=
  integral_affine_contDiff (P := matCircularLaw N p) (A := fun _ => lmulL K)
    (b := fun G => lmul S G) aestronglyMeasurable_const
    (continuous_lmul S).aestronglyMeasurable (M := ‖(lmulL K : RefState N p →L[ℝ] RefState N p)‖)
    (ae_of_all _ fun _ => le_rfl) hf.contDiff hf.bound hf.deriv_bound (norm_fderiv_fderiv_le hf)

theorem integrable_fderiv_const {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (m : RefState N p) (S : Matrix (Fin N) (Fin N) ℂ) (w : RefState N p) :
    Integrable (fun G => fderiv ℝ f (m + lmul S G) w) (matCircularLaw N p) :=
  integrable_matCircularLaw_of_bound
    (((contDiff_fderiv_of_C2 hf.contDiff).continuous.comp
      (continuous_const.add (continuous_lmul S))).clm_apply continuous_const)
    (fun _ => abs_fderiv_apply_le hf _ w)

/-!
## The generator identity
-/

/-- **Pointwise generator identity of the reference flow.** For `Y = nᴴ z + S G`,
`G ~ matCircularLaw`, and `h(z') = E f(nᴴ z' + S G)`:
`E [Df(Y)[nᴴ D z] + ½ Σ_α D²f(Y)[nᴴ σ_α z, nᴴ σ_α z] + Df(Y)[B G]] = refGenerator ρ κ h z`,
`D = rotationDrift ρ κ`, `σ_α = rotationNoise ρ α`. -/
theorem itoDrift_eq_refGenerator (hIBP : MultivariateGaussianIBP) {C : ℝ}
    {f : RefState N p → ℝ}
    (hf : IsC2BoundedBy C f) (n S B : Matrix (Fin N) (Fin N) ℂ) (ρ : Fin N → Fin N → ℝ)
    (κ : Fin N → ℝ)
    (hρs : ∀ k l, ρ k l = ρ l k) (hρ0 : ∀ k l, 0 ≤ ρ k l) (hκ0 : ∀ k, 0 ≤ κ k)
    (hS : S.IsHermitian) (hB : B.IsHermitian)
    (hSB : S * B + B * S = nᴴ * Matrix.diagonal (fun k => (κ k : ℂ)) * n) (z : RefState N p) :
    ∫ G, (fderiv ℝ f (lmul nᴴ z + lmul S G) (lmul (nᴴ * rotationDrift ρ κ) z) +
        (1 / 2 : ℝ) * ∑ α : RotIdx N, D2 f (lmul nᴴ z + lmul S G)
          (lmul (nᴴ * rotationNoise ρ α) z) (lmul (nᴴ * rotationNoise ρ α) z) +
        fderiv ℝ f (lmul nᴴ z + lmul S G) (lmul B G)) ∂matCircularLaw N p =
      refGenerator (fun _ => ρ) (fun _ => κ) 0
        (fun z' => ∫ G, f (lmul nᴴ z' + lmul S G) ∂matCircularLaw N p) z := by
  obtain ⟨-, hD1, hD2⟩ := gaussAvg_derivs hf nᴴ S
  have hI1 := integrable_fderiv_const hf (lmul nᴴ z) S (lmul (nᴴ * rotationDrift ρ κ) z)
  have hI2 : Integrable (fun G => (1 / 2 : ℝ) * ∑ α : RotIdx N, D2 f (lmul nᴴ z + lmul S G)
      (lmul (nᴴ * rotationNoise ρ α) z) (lmul (nᴴ * rotationNoise ρ α) z))
      (matCircularLaw N p) :=
    (integrable_finsetSum _ fun α _ => integrable_D2_lmul hf _ S _ _).const_mul _
  have hI12 : Integrable (fun G =>
      fderiv ℝ f (lmul nᴴ z + lmul S G) (lmul (nᴴ * rotationDrift ρ κ) z) +
        (1 / 2 : ℝ) * ∑ α : RotIdx N, D2 f (lmul nᴴ z + lmul S G)
          (lmul (nᴴ * rotationNoise ρ α) z) (lmul (nᴴ * rotationNoise ρ α) z))
      (matCircularLaw N p) := hI1.add hI2
  rw [integral_add hI12 (integrable_fderiv_lmul hf (lmul nᴴ z) S B),
    integral_add hI1 hI2, integral_const_mul,
    integral_finsetSum _ fun α _ => integrable_D2_lmul hf _ S _ _,
    integral_ou_part hIBP hf (lmul nᴴ z) n S B κ hκ0 hS hB hSB]
  simp only [lmul_mul]
  rw [← hD1 z (lmul (rotationDrift ρ κ) z)]
  simp only [← hD2 z]
  unfold refGenerator vfSq D2
  exact generator_algebra _ _ ρ κ hρs hρ0 z _

end BlockBand.Palm.ReferenceFlow
