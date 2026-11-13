module

public import BlockBand.Critical.EntireLaw.GaussianPhase
public import BlockBand.Critical.EntireLaw.PhasePassage
public import BlockBand.Critical.EntireLaw.ConeBound
public import BlockBand.Critical.EntireLaw.Measurability

/-!
# The entire law: the finite-width Gaussian moment identity

Proof. For Hermitian `H` with `det(H - E) ≠ 0` (almost sure under the physical law,
`isPhysical.1`, `ae_baseDeterminant_ne_zero`): the probe is `ζ = D g` with
`D = diag(√(W⁻² Σ_a y_a Q_a(j/n)))` (`ringProbeVector_eq_mulVec`); `D_W(iy) = det(1 + i DRD)`
(Sylvester, `finiteEntireDeterminant_conePoint_eq`, the computation of
`one_le_norm_finiteEntireDeterminant_conePoint`); the Gaussian integral
`E exp{-iσ g^*(DRD)g} = Π_k (1 + iσλ_k)⁻¹` (`GaussianPhase`) is `D_W(iy)⁻¹`, resp. its conjugate.
Fubini (the phase is bounded by one a.s.) and the product structure of the probes conclude.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.CriticalEntire
open scoped ComplexConjugate

variable {p : Parameters}

/-- The diagonal square-root weight `diag(√(W⁻² Σ_a y_a Q_a(j/n)))`. -/
def coneRootDiag (p : Parameters) {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (y : Fin m → ℝ) :
    p.SiteMatrix :=
  Matrix.diagonal fun x => ((Real.sqrt (coneWeight p Q y x) : ℝ) : ℂ)

theorem coneRootDiag_conjTranspose {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (y : Fin m → ℝ) :
    (coneRootDiag p Q y)ᴴ = coneRootDiag p Q y := by
  unfold coneRootDiag
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  simp

/-- `D_W(iy) = det(1 + i D R D)`, `D = coneRootDiag`, `R = (H - E)⁻¹` (Sylvester). -/
theorem finiteEntireDeterminant_conePoint_eq (E : ℝ) {m : ℕ} {Q : Fin m → C(Torus, ℝ)}
    (hQ : ∀ a t, 0 ≤ Q a t) {H : p.SiteMatrix}
    (hA : (H - (E : ℂ) • (1 : p.SiteMatrix)).det ≠ 0) {y : Fin m → ℝ} (hy : ∀ a, 0 ≤ y a) :
    finiteEntireDeterminant p E Q H (conePoint y) =
      (1 + Complex.I • (coneRootDiag p Q y * (H - (E : ℂ) • (1 : p.SiteMatrix))⁻¹ *
        coneRootDiag p Q y)).det := by
  set A := H - (E : ℂ) • (1 : p.SiteMatrix) with hAdef
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  set D : p.SiteMatrix := coneRootDiag p Q y
  have hDD : D * Dᴴ = Matrix.diagonal (fun x => ((coneWeight p Q y x : ℝ) : ℂ)) := by
    simp only [D, coneRootDiag]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (coneWeight_nonneg hQ hy x)]
  have hpen : BlockBand.Critical.finiteCharacteristicPencil A (fun a => p.profileSourceMatrix (Q a))
      (BlockBand.Critical.widthSourceScale p.W) (conePoint y) =
      A * (1 + (Complex.I • (A⁻¹ * D)) * Dᴴ) := by
    unfold BlockBand.Critical.finiteCharacteristicPencil
    rw [cone_source_eq, ← hDD, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAu, Matrix.one_mul]
  have hval : finiteEntireDeterminant p E Q H (conePoint y) =
      (1 + Complex.I • (Dᴴ * A⁻¹ * D)).det := by
    simp only [finiteEntireDeterminant, EntireFunction.coe_ofDifferentiable,
      BlockBand.Critical.finiteCharacteristicDeterminant]
    rw [hpen, Matrix.det_mul, Matrix.det_one_add_mul_comm, mul_comm A.det, mul_assoc,
      mul_inv_cancel₀ hA, mul_one, Matrix.mul_smul, Matrix.mul_assoc]
  rw [hval, coneRootDiag_conjTranspose]

/-- The probe with profile `Σ_a y_a Q_a` is `D g`. -/
theorem ringProbeVector_eq_mulVec {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (y : Fin m → ℝ)
    (g : p.Site → ℂ) :
    ringProbeVector p (∑ a, y a • Q a) g = coneRootDiag p Q y *ᵥ g := by
  funext x
  rw [ringProbeVector_apply, coneRootDiag, Matrix.mulVec_diagonal]
  congr 2
  unfold coneWeight
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr (Nat.cast_nonneg _))]
  congr 2
  simp [ContinuousMap.coe_sum, smul_eq_mul]

/-- `(Dg)^* R (Dg) = g^* (D^* R D) g`. -/
theorem star_mulVec_dotProduct_mulVec {ι : Type*} [Fintype ι] (D R : Matrix ι ι ℂ) (g : ι → ℂ) :
    star (D *ᵥ g) ⬝ᵥ (R *ᵥ (D *ᵥ g)) = star g ⬝ᵥ ((Dᴴ * R * D) *ᵥ g) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- **One probe, fixed `H`**: `E_g exp{-iσ ζ^*Rζ} = D_W(iy)⁻¹` (`σ = 1`), resp.
`conj(D_W(iy)⁻¹)` (`σ = -1`), for Hermitian `H` with `det(H - E) ≠ 0`, the probe
`ζ = W⁻¹(Σ_a y_a Q_a)^{1/2} g` and `y ≥ 0`. -/
theorem integral_ringProbe_phase (E : ℝ) {m : ℕ} {Q : Fin m → C(Torus, ℝ)}
    (hQ : ∀ a t, 0 ≤ Q a t) {H : p.SiteMatrix} (hH : H.IsHermitian)
    (hA : (H - (E : ℂ) • (1 : p.SiteMatrix)).det ≠ 0) {y : Fin m → ℝ} (hy : ∀ a, 0 ≤ y a)
    (σ : ℤˣ) :
    ∫ g, Complex.exp (-(Complex.I * (((σ : ℤ) : ℂ) *
        (star (ringProbeVector p (∑ a, y a • Q a) g) ⬝ᵥ
          ((H - (E : ℂ) • 1)⁻¹ *ᵥ ringProbeVector p (∑ a, y a • Q a) g)))))
        ∂circularVectorLaw p.Site =
      mixedInverseFactor σ (finiteEntireDeterminant p E Q H (conePoint y)) := by
  set D := coneRootDiag p Q y
  set R := (H - (E : ℂ) • (1 : p.SiteMatrix))⁻¹
  have hK : (D * R * D).IsHermitian := by
    have h := Matrix.isHermitian_mul_mul_conjTranspose D (isHermitian_resolvent hH E)
    rwa [coneRootDiag_conjTranspose] at h
  have hint := integral_circularVectorLaw_hermitian_phase hK ((σ : ℤ) : ℝ)
  have hdet := det_one_add_smul_of_isHermitian hK Complex.I
  rw [finiteEntireDeterminant_conePoint_eq E hQ hA hy, hdet]
  have hlhs : ∀ g : p.Site → ℂ, Complex.exp (-(Complex.I * (((σ : ℤ) : ℂ) *
        (star (ringProbeVector p (∑ a, y a • Q a) g) ⬝ᵥ (R *ᵥ ringProbeVector p (∑ a, y a • Q a) g))))) =
      Complex.exp (-(Complex.I * (((σ : ℤ) : ℝ) : ℂ)) * (star g ⬝ᵥ ((D * R * D) *ᵥ g))) := by
    intro g
    rw [ringProbeVector_eq_mulVec, star_mulVec_dotProduct_mulVec, coneRootDiag_conjTranspose]
    push_cast
    ring_nf
    rfl
  simp_rw [hlhs]
  rw [hint]
  rcases Int.units_eq_one_or σ with h | h
  · subst h
    simp [mixedInverseFactor, Finset.prod_inv_distrib]
  · subst h
    have hne : ¬((-1 : ℤˣ) = 1) := by decide
    simp only [mixedInverseFactor, hne, ite_false]
    rw [Finset.prod_inv_distrib, map_inv₀, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [Complex.conj_ofReal]

/-- The closed phase of the ring source matrix is the product of the one-probe phases. -/
theorem closedSourcePhase_ringSourceMatrix (E : ℝ) {J : ℕ} (σ : Fin J → ℤˣ)
    (Q : Fin J → C(Torus, ℝ)) (H : p.SiteMatrix) (g : Fin J → p.Site → ℂ) :
    closedSourcePhase σ (ringSourceMatrix p E Q H g) =
      ∏ j, Complex.exp (-(Complex.I * (((σ j : ℤ) : ℂ) *
        (star (ringProbeVector p (Q j) (g j)) ⬝ᵥ
          ((H - (E : ℂ) • 1)⁻¹ *ᵥ ringProbeVector p (Q j) (g j)))))) := by
  unfold closedSourcePhase ringSourceMatrix
  rw [← Complex.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- **`FiniteGaussianMomentIdentity`**: the finite-width mixed inverse moments of `D_W` are the
expected closed phases of the ring source matrix. -/
theorem finiteGaussianMomentIdentity : FiniteGaussianMomentIdentity := by
  intro p R E k q hq J y σ hy
  have hQ := fullProfile_nonneg hq
  have hD := BlockBand.Critical.JointRecovery.measurable_finiteEntireDeterminant (p := p) E
    (fullProfile q)
  have hfac : ∀ s : ℤˣ, Measurable (mixedInverseFactor s) := fun s => by
    unfold mixedInverseFactor
    split_ifs
    · exact measurable_inv
    · exact Complex.continuous_conj.measurable.comp measurable_inv
  -- left side: push the law of `D_W` back to `H`
  have hL : mixedInverseMoment (finiteEntireLaw R E (fullProfile q)) y σ =
      ∫ H, ∏ j, mixedInverseFactor (σ j)
        (finiteEntireDeterminant p E (fullProfile q) H (conePoint (y j))) ∂(R.model.law : Measure p.SiteMatrix) := by
    unfold mixedInverseMoment finiteEntireLaw
    rw [ProbabilityMeasure.toMeasure_map, integral_map hD.aemeasurable]
    exact (Finset.measurable_prod _ fun j _ =>
      (hfac (σ j)).comp (EntireFunction.measurable_eval_const _)).aestronglyMeasurable
  rw [hL]
  -- right side: Fubini, then the one-probe identity
  set ν : Measure (Fin J → p.Site → ℂ) := Measure.pi fun _ : Fin J => circularVectorLaw p.Site
  have hmeas : Measurable fun x : p.SiteMatrix × (Fin J → p.Site → ℂ) =>
      closedSourcePhase σ (ringSourceMatrix p E (probeProfile q y) x.1 x.2) :=
    (measurable_closedSourcePhase σ).comp (measurable_ringSourceMatrix E _)
  have hherm : ∀ᵐ x ∂(fullRingProbeLaw R.model J), x.1.IsHermitian :=
    (Measure.quasiMeasurePreserving_fst).ae R.model.isPhysical.1
  have hint : Integrable (fun x : p.SiteMatrix × (Fin J → p.Site → ℂ) =>
      closedSourcePhase σ (ringSourceMatrix p E (probeProfile q y) x.1 x.2))
      (fullRingProbeLaw R.model J) := by
    have : IsFiniteMeasure (fullRingProbeLaw R.model J) := by
      unfold fullRingProbeLaw; infer_instance
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards [hherm] with x hx
    exact norm_closedSourcePhase_le σ fun j => ringSourceMatrix_diag_im hx E _ _ j
  unfold fullRingProbeLaw
  rw [integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [R.model.isPhysical.1, R.model.ae_baseDeterminant_ne_zero E] with H hH hA
  simp_rw [closedSourcePhase_ringSourceMatrix]
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun (j : Fin J) (g : p.Site → ℂ) =>
    Complex.exp (-(Complex.I * (((σ j : ℤ) : ℂ) *
        (star (ringProbeVector p (probeProfile q y j) g) ⬝ᵥ
          ((H - (E : ℂ) • 1)⁻¹ *ᵥ ringProbeVector p (probeProfile q y j) g))))))]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact (integral_ringProbe_phase E hQ hH hA (hy j) (σ j)).symm

end BlockBand.Critical.EntireLaw
