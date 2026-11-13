module

public import BlockBand.SourceProcess.PhysApprox.B3StepFresh
public import BlockBand.SourceProcess.FullSource.WardIdentity
public import BlockBand.Transmission.PathScalar.Dissipative
public import BlockBand.Transmission.PathScalar.MeanEqPort
public import BlockBand.Transmission.Bridge.NullDet
public import BlockBand.Transmission.PassiveCovariance.Fluctuation
public import BlockBand.Transmission.PassiveCovariance.MainTerm

/-!
# One fresh layer, `L⁴` bounds of `u*Δv` and of `u*(U − 1)u'`

* `oneLeak_eq`: the one-port leak `Tr(1 − SS*)`, `S = 1 − 2iηR`, `R = (z − X)⁻¹`, is
  `4η Re Tr(RYR*)`, `Y = −Im X` (`1 − SS* = 4ηRYR*`).
* **`eLpNorm_bilinear_freshDelta_le`** (from the contract hypotheses): `‖u*Δv‖_{L^p} ≤
  C(δ₀ + W^{-1/2})‖u‖‖v‖` (`RawTag.delta_fresh_bounds`).
* **`eLpNorm_bilinear_freshUSub_le`** (from the contract hypotheses): `‖u*(U − 1)u'‖_{L⁴} ≤
  C(δ₀ + W^{-1/2})(‖u‖‖u'‖ + (‖u‖² + ‖u'‖²)·Tr(1 − SS*))`. The linear part is two `Δ` forms
  (`p = 4`); the quadratic part `Σ_e (u*Δq_e)(u'*Δq_e)^*` is bounded by Minkowski with the `L⁸`
  bound and `Σ_e‖q_e‖² = Tr(1 − SS*)/(4η²)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.GramStepU

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## The one-port leak
-/

/-- The one-port scattering matrix `S = 1 − 2iηR`, `R = (z − X)⁻¹`. -/
def oneS (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  1 - ((2 * etaZ b E : ℝ) * Complex.I) • passiveResolvent b E X

/-- **The one-port leak** `Re Tr(1 − SS*)` (the transmission of the input into its far end). -/
def oneLeak (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ((1 - oneS b E X * (oneS b E X)ᴴ).trace).re

theorem isUnit_pencil {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) :
    IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) := by
  apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
  rw [matrixImaginaryPart_nearPencil]
  exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)

/-- `1 − SS* = 4ηRYR*`. -/
theorem one_sub_oneS_mul {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) :
    1 - oneS b E X * (oneS b E X)ᴴ =
      ((4 * etaZ b E : ℝ) : ℂ) • (passiveResolvent b E X * passiveY X *
        (passiveResolvent b E X)ᴴ) := by
  set z := boundaryZ b E
  set K := z • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set R := passiveResolvent b E X
  set Y := passiveY X
  set c : ℂ := ((2 * etaZ b E : ℝ) : ℂ) * Complex.I with hc
  have hKd := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_pencil hη hY)
  have hRK : R * K = 1 := Matrix.nonsing_inv_mul _ hKd
  have hp : K - Kᴴ = (2 * Complex.I) • (((etaZ b E : ℝ) : ℂ) • 1 + Y) := pencil_sub_conj z X
  have hK' : Kᴴ - K = -((2 * Complex.I) • (((etaZ b E : ℝ) : ℂ) • 1 + Y)) := by
    rw [← hp]; abel
  have h1 : R - Rᴴ = -((2 * Complex.I) • (((etaZ b E : ℝ) : ℂ) • (R * Rᴴ) + R * Y * Rᴴ)) := by
    rw [inv_sub_conj R K hRK, hK']
    simp only [Matrix.mul_neg, Matrix.neg_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one]
  have hs : star c = -c := by simp [hc, Complex.conj_ofReal]
  have e1 : 1 - oneS b E X * (oneS b E X)ᴴ = c • (R - Rᴴ) + (c * c) • (R * Rᴴ) := by
    simp only [oneS, conjTranspose_sub, conjTranspose_one, conjTranspose_smul]
    rw [show ((2 * etaZ b E : ℝ) * Complex.I) = c from rfl, hs]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
      mul_smul_comm, neg_smul, Matrix.mul_neg]
    module
  have hc1 : c * (2 * Complex.I) = -((4 * etaZ b E : ℝ) : ℂ) := by
    rw [hc]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hc2 : c * c = -((((2 * etaZ b E : ℝ) : ℂ)) ^ 2) := by
    rw [hc]; ring_nf; rw [Complex.I_sq]; ring
  rw [e1, h1, smul_neg, smul_smul, hc1, hc2]
  push_cast
  module

/-- `Tr(1 − SS*) = 4η Re Tr(RYR*)`. -/
theorem oneLeak_eq {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) :
    oneLeak b E X = 4 * etaZ b E * ((passiveResolvent b E X * passiveY X *
      (passiveResolvent b E X)ᴴ).trace).re := by
  rw [oneLeak, one_sub_oneS_mul hη hY, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-!
## The exact one-layer identity for `U − 1`
-/

open scoped MatrixOrder in
/-- A positive semidefinite matrix is `B*B`. -/
theorem exists_eq_conjTranspose_mul {A : Matrix (Fin W) (Fin W) ℂ} (h : A.PosSemidef) :
    ∃ B : Matrix (Fin W) (Fin W) ℂ, A = Bᴴ * B := by
  obtain ⟨a, ha⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  exact ⟨a, by rw [ha, star_eq_conjTranspose]⟩

/-- A factor `Q` of the far absorption: `RYR* = ηQQ*`. -/
theorem exists_absorption_factor {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) :
    ∃ Q : Matrix (Fin W) (Fin W) ℂ, passiveResolvent b E X * passiveY X *
      (passiveResolvent b E X)ᴴ = ((etaZ b E : ℝ) : ℂ) • (Q * Qᴴ) := by
  obtain ⟨B, hB⟩ := exists_eq_conjTranspose_mul hY
  set R := passiveResolvent b E X
  set t : ℝ := (Real.sqrt (etaZ b E))⁻¹
  refine ⟨(t : ℂ) • (R * Bᴴ), ?_⟩
  have ht : ((etaZ b E : ℝ) : ℂ) * ((t : ℂ) * (t : ℂ)) = 1 := by
    have : etaZ b E * (t * t) = 1 := by
      simp only [t]
      rw [← mul_inv, Real.mul_self_sqrt hη.le, mul_inv_cancel₀ hη.ne']
    exact_mod_cast this
  rw [hB, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_smul_comm,
    smul_smul, ht, one_smul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- **`U − 1 = Δf + f*Δ* − (ΔQ)(ΔQ)*`** for passive `X`, `A` Hermitian, `B` invertible, and any
`Q` with `RYR* = ηQQ*` (the near block of the full-source Ward identity at a one-port input). -/
theorem freshU_sub_one_eq {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) (Q : Matrix (Fin W) (Fin W) ℂ)
    (hQ : passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ =
      ((etaZ b E : ℝ) : ℂ) • (Q * Qᴴ)) :
    freshU b E X ω - 1 =
      freshDelta b E X ω * (passiveResolvent b E X - (2 * Complex.I * (etaZ b E : ℂ))⁻¹ • 1) +
        (passiveResolvent b E X - (2 * Complex.I * (etaZ b E : ℂ))⁻¹ • 1)ᴴ *
          (freshDelta b E X ω)ᴴ -
        freshDelta b E X ω * Q * (freshDelta b E X ω * Q)ᴴ := by
  set z := boundaryZ b E
  have hz : 0 < z.im := hη
  have hKd := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_pencil hη hY)
  have h := ward_algebra (g11 E z X ω) (g12 E z X ω) (z • 1 - X) (passiveY X)
    (passiveResolvent b E X) Q hη.ne' (im_g11 E hz hY hA hB) (pencil_sub_conj z X)
    (Matrix.mul_nonsing_inv _ hKd) hQ
  rw [freshU, freshL_eq_lAt, freshDelta_eq]
  rw [← h]
  simp only [lAt]
  abel

/-!
## Bilinear forms
-/

theorem bilinear_mul_vec (u : Fin W → ℂ) (M N : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    bilinear u (M * N) v = bilinear u M (N *ᵥ v) := by
  simp only [bilinear, mulVec_mulVec]

/-- Column `e` of a matrix. -/
def col (Q : Matrix (Fin W) (Fin W) ℂ) (e : Fin W) : Fin W → ℂ := fun x => Q x e

theorem vecMul_mul_col (u : Fin W → ℂ) (D Q : Matrix (Fin W) (Fin W) ℂ) (e : Fin W) :
    (star u ᵥ* (D * Q)) e = bilinear u D (col Q e) := by
  simp only [bilinear, vecMul, dotProduct, mulVec, col, Matrix.mul_apply, Finset.mul_sum]

theorem conjTranspose_mulVec_apply (v : Fin W → ℂ) (N : Matrix (Fin W) (Fin W) ℂ) (e : Fin W) :
    (Nᴴ *ᵥ v) e = star ((star v ᵥ* N) e) := by
  simp only [vecMul, dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, star_sum,
    star_mul', star_star]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem bilinear_mul_conjTranspose (u v : Fin W → ℂ) (N : Matrix (Fin W) (Fin W) ℂ) :
    bilinear u (N * Nᴴ) v = ∑ e, (star u ᵥ* N) e * star ((star v ᵥ* N) e) := by
  rw [bilinear, ← mulVec_mulVec, dotProduct_mulVec, dotProduct]
  exact Finset.sum_congr rfl fun e _ => by rw [conjTranspose_mulVec_apply]

/-- **The bilinear form of `U − 1`** as two `Δ` forms and a sum of products of `Δ` forms. -/
theorem bilinear_freshU_sub_one {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) (Q : Matrix (Fin W) (Fin W) ℂ)
    (hQ : passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ =
      ((etaZ b E : ℝ) : ℂ) • (Q * Qᴴ)) (u v : Fin W → ℂ) :
    bilinear u (freshU b E X ω - 1) v =
      bilinear u (freshDelta b E X ω)
          ((passiveResolvent b E X - (2 * Complex.I * (etaZ b E : ℂ))⁻¹ • 1) *ᵥ v) +
        star (bilinear v (freshDelta b E X ω)
          ((passiveResolvent b E X - (2 * Complex.I * (etaZ b E : ℂ))⁻¹ • 1) *ᵥ u)) -
        ∑ e, bilinear u (freshDelta b E X ω) (col Q e) *
          star (bilinear v (freshDelta b E X ω) (col Q e)) := by
  rw [freshU_sub_one_eq hη hY hA hB Q hQ, bilinear_sub, bilinear_add, bilinear_mul_vec,
    ← conjTranspose_mul, bilinear_conjTranspose, bilinear_mul_vec, bilinear_mul_conjTranspose]
  simp only [vecMul_mul_col]

/-!
## `L^p` bounds of `Δ` forms
-/

/-- **`‖u*Δv‖_{L^p} ≤ C(δ₀ + W^{-1/2})‖u‖‖v‖`** for passive `X` (`RawTag.delta_fresh_bounds`:
mean `C_m(δ₀ + W⁻¹)`, fluctuation `C_f(W^{-1/2} + δ₀)`). -/
theorem eLpNorm_bilinear_freshDelta_le (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) {p : ℝ} (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ a c : Fin W → ℂ,
        eLpNorm (fun F => bilinear a (freshDelta b E X F) c) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C * (jetDistance0 b E X + (Real.sqrt W)⁻¹) * vecNorm a * vecNorm c) := by
  obtain ⟨hκ, hEκ⟩ := StepFresh.bulk_of_lt hE1 hE2
  obtain ⟨Cm, Cf, W₁, hCm, hCf, hD⟩ := RawTag.delta_fresh_bounds hGA hLp b hb0 hb _ hκ p hp
  refine ⟨Cm + Cf, max W₁ 1, by positivity, fun W hW X hX a c => ?_⟩
  have hW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hsqW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hinv : (W : ℝ)⁻¹ ≤ (Real.sqrt W)⁻¹ := by
    refine inv_anti₀ hsqW ?_
    rw [Real.sqrt_le_left hW0.le]; nlinarith
  obtain ⟨-, hm, hfl⟩ := hD W hW₁ E hEκ X hX
  set M := matrixExpect (freshLaw W b) (freshDelta b E X)
  have hsplit : (fun F => bilinear a (freshDelta b E X F) c) =
      (fun _ => bilinear a M c) + fun F => bilinear a (freshDelta b E X F - M) c := by
    funext F; simp only [Pi.add_apply, RawTag.bilinear_sub_mid]; ring
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hδ : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have ha := vecNorm_nonneg a
  have hc := vecNorm_nonneg c
  have hmn : ‖bilinear a M c‖ ≤
      Cm * (jetDistance0 b E X + (Real.sqrt W)⁻¹) * vecNorm a * vecNorm c := by
    refine (norm_bilinear_le a M c).trans ?_
    have hm' : ‖M‖ ≤ Cm * (jetDistance0 b E X + (Real.sqrt W)⁻¹) :=
      hm.trans (mul_le_mul_of_nonneg_left (by linarith) hCm)
    calc vecNorm a * ‖M‖ * vecNorm c ≤
          vecNorm a * (Cm * (jetDistance0 b E X + (Real.sqrt W)⁻¹)) * vecNorm c := by gcongr
      _ = _ := by ring
  rw [hsplit]
  refine (eLpNorm_add_le hp1).trans ?_
  rw [eLpNorm_const' _ hp0 ENNReal.ofReal_ne_top, measure_univ, ENNReal.one_rpow, mul_one]
  calc ‖bilinear a M c‖ₑ +
        eLpNorm (fun F => bilinear a (freshDelta b E X F - M) c) (ENNReal.ofReal p) (freshLaw W b)
      ≤ ENNReal.ofReal (Cm * (jetDistance0 b E X + (Real.sqrt W)⁻¹) * vecNorm a * vecNorm c) +
          ENNReal.ofReal (Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E X) * vecNorm a * vecNorm c) :=
        add_le_add (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hmn) (hfl a c)
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- `‖|α|²‖_{L⁴} ≤ s²` from `‖α‖_{L⁸} ≤ s`. -/
theorem eLpNorm_sq_le {F : Type*} [MeasurableSpace F] {μ : Measure F} {α : F → ℂ}
    (hα : AEStronglyMeasurable α μ) {s : ℝ} (hs : 0 ≤ s)
    (h : eLpNorm α (ENNReal.ofReal 8) μ ≤ ENNReal.ofReal s) :
    eLpNorm (fun F => ‖α F‖ ^ 2) 4 μ ≤ ENNReal.ofReal (s ^ 2) := by
  rw [show (fun F => ‖α F‖ ^ 2) = fun F => ‖α F‖ ^ (2 : ℝ) from
    funext fun F => (Real.rpow_two _).symm, eLpNorm_norm_rpow α hα two_pos]
  rw [show (4 : ℝ≥0∞) * ENNReal.ofReal 2 = ENNReal.ofReal 8 by
    rw [ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]; norm_num]
  calc eLpNorm α (ENNReal.ofReal 8) μ ^ (2 : ℝ) ≤ ENNReal.ofReal s ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (s ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hs (by norm_num), Real.rpow_two]

/-- `Σ_e ‖Qe_e‖² = Re Tr(QQ*)`. -/
theorem sum_vecNorm_col_sq (Q : Matrix (Fin W) (Fin W) ℂ) :
    ∑ e, vecNorm (col Q e) ^ 2 = ((Q * Qᴴ).trace).re := by
  have h := Four.reTrace_conjTranspose_mul Qᴴ
  rw [conjTranspose_conjTranspose] at h
  rw [h, Four.frameSq]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [vecNorm_sq_eq]
  simp [col, conjTranspose_apply]

theorem norm_wardF_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    ‖passiveResolvent b E X - (2 * Complex.I * (etaZ b E : ℂ))⁻¹ • 1‖ ≤
      (etaZ b E)⁻¹ + (2 * etaZ b E)⁻¹ := by
  have hη : 0 < etaZ b E := etaZ_pos b E (by linarith) hE1 hE2
  refine (norm_sub_le _ _).trans (add_le_add (norm_passiveResolvent_le hb0 hb hE1 hE2 hX) ?_)
  rw [norm_smul]
  have hn : ‖(2 * Complex.I * (etaZ b E : ℂ))⁻¹‖ = (2 * etaZ b E)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hη]
    norm_num
  rw [hn]
  exact mul_le_of_le_one_right (by positivity) norm_one_matrix_le

/-- **`‖u*(U − 1)v‖_{L⁴} ≤ C(δ₀ + W^{-1/2})(‖u‖‖v‖ + (‖u‖² + ‖v‖²)Tr(1 − SS*))`** for passive
`X`, uniformly in `W ≥ W₀` and `X`. -/
theorem eLpNorm_bilinear_freshUSub_le (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun F => bilinear u (freshU b E X F - 1) v) 4 (freshLaw W b) ≤
          ENNReal.ofReal (C * (jetDistance0 b E X + (Real.sqrt W)⁻¹) *
            (vecNorm u * vecNorm v + (vecNorm u ^ 2 + vecNorm v ^ 2) * oneLeak b E X)) := by
  have hη : 0 < etaZ b E := etaZ_pos b E (by linarith) hE1 hE2
  obtain ⟨C4, W4, hC4, h4⟩ :=
    eLpNorm_bilinear_freshDelta_le hGA hLp hb0 hb hE1 hE2 (p := 4) (by norm_num)
  obtain ⟨C8, W8, hC8, h8⟩ :=
    eLpNorm_bilinear_freshDelta_le hGA hLp hb0 hb hE1 hE2 (p := 8) (by norm_num)
  set η := etaZ b E with hηdef
  set Fn := η⁻¹ + (2 * η)⁻¹ with hFn
  have hFn0 : 0 ≤ Fn := by positivity
  set C := 2 * C4 * Fn + C8 ^ 2 * (η⁻¹ + 2) / (8 * η ^ 2) with hCdef
  refine ⟨C, max (max W4 W8) 1, by positivity, fun W hW X hX u v => ?_⟩
  have hW4 : W4 ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW8 : W8 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW1n : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  set μ := freshLaw W b
  set δ := jetDistance0 b E X
  set w := (Real.sqrt W)⁻¹
  set D := δ + w with hDdef
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hw0 : 0 ≤ w := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hw1 : w ≤ 1 := by
    refine inv_le_one_of_one_le₀ ?_
    rw [Real.le_sqrt (by norm_num) hW0.le]; simpa using hW1
  have hD0 : 0 ≤ D := add_nonneg hδ0 hw0
  have hDle : D ≤ η⁻¹ + 2 := by
    have := Transmission.PathScalar.jetDistance0_le_bound hb0 hb hE1 hE2 hX
    simp only [hDdef]; linarith
  obtain ⟨Q, hQ⟩ := exists_absorption_factor hη hX
  set f := passiveResolvent b E X - (2 * Complex.I * (etaZ b E : ℂ))⁻¹ • 1
  have hf : ‖f‖ ≤ Fn := norm_wardF_le hb0 hb hE1 hE2 hX
  have hu0 := vecNorm_nonneg u
  have hv0 := vecNorm_nonneg v
  have hfu : vecNorm (f *ᵥ u) ≤ Fn * vecNorm u :=
    (vecNorm_mulVec_le f u).trans (mul_le_mul_of_nonneg_right hf hu0)
  have hfv : vecNorm (f *ᵥ v) ≤ Fn * vecNorm v :=
    (vecNorm_mulVec_le f v).trans (mul_le_mul_of_nonneg_right hf hv0)
  -- the leak in terms of `Q`
  have hleak : oneLeak b E X = 4 * η ^ 2 * ∑ e, vecNorm (col Q e) ^ 2 := by
    rw [oneLeak_eq hη hX, hQ, trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      sum_vecNorm_col_sq]
    ring
  have hq0 : 0 ≤ ∑ e, vecNorm (col Q e) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hleak0 : 0 ≤ oneLeak b E X := by rw [hleak]; positivity
  -- measurability
  have hΔm : Measurable (freshDelta b E X) :=
    FullSource.measurable_freshDelta_comp b E measurable_const measurable_id
  have hbil : ∀ a c : Fin W → ℂ, Measurable fun F => bilinear a (freshDelta b E X F) c :=
    fun a c => RawTag.measurable_bilinear_jt measurable_const hΔm measurable_const
  have hUm : Measurable fun F => bilinear u (freshU b E X F - 1) v :=
    RawTag.measurable_bilinear_jt measurable_const
      (FullSourceStops.measurable_matrix_sub (measurable_freshU b E X) measurable_const)
      measurable_const
  -- the pointwise bound
  set g : LayerSample W .oneBlockOnePort → ℝ := fun F =>
    ‖bilinear u (freshDelta b E X F) (f *ᵥ v)‖ + ‖bilinear v (freshDelta b E X F) (f *ᵥ u)‖ +
      ∑ e, (1 / 2 : ℝ) * (‖bilinear u (freshDelta b E X F) (col Q e)‖ ^ 2 +
        ‖bilinear v (freshDelta b E X F) (col Q e)‖ ^ 2)
  have hgood : ∀ᵐ F ∂μ, (F.1 0).IsHermitian ∧ IsUnit (F.2 0 0) :=
    (Transmission.PathScalar.ae_layer_herm b).and
      ((Transmission.Bridge.ae_isUnit_layerLaw_bond hb0 hW1n _).mono fun F h => h 0 0)
  have hpt : ∀ᵐ F ∂μ, ‖bilinear u (freshU b E X F - 1) v‖ ≤ g F := by
    filter_upwards [hgood] with F hF
    rw [bilinear_freshU_sub_one hη hX hF.1 hF.2 Q hQ u v]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add le_rfl (norm_star _).le)) ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun e _ => ?_)))
    rw [norm_mul, norm_star]
    nlinarith [sq_nonneg (‖bilinear u (freshDelta b E X F) (col Q e)‖ -
      ‖bilinear v (freshDelta b E X F) (col Q e)‖)]
  have hg : g = (fun F => ‖bilinear u (freshDelta b E X F) (f *ᵥ v)‖) +
      (fun F => ‖bilinear v (freshDelta b E X F) (f *ᵥ u)‖) +
      ∑ e, (1 / 2 : ℝ) • ((fun F => ‖bilinear u (freshDelta b E X F) (col Q e)‖ ^ 2) +
        fun F => ‖bilinear v (freshDelta b E X F) (col Q e)‖ ^ 2) := by
    funext F
    simp only [g, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h4' : ∀ a c : Fin W → ℂ, eLpNorm (fun F => ‖bilinear a (freshDelta b E X F) c‖) 4 μ ≤
      ENNReal.ofReal (C4 * D * vecNorm a * vecNorm c) := fun a c => by
    rw [eLpNorm_norm _ (hbil a c).aestronglyMeasurable]
    have := h4 W hW4 X hX a c
    rwa [ENNReal.ofReal_ofNat] at this
  have h8' : ∀ a c : Fin W → ℂ, eLpNorm (fun F => ‖bilinear a (freshDelta b E X F) c‖ ^ 2) 4 μ ≤
      ENNReal.ofReal ((C8 * D * vecNorm a * vecNorm c) ^ 2) := fun a c =>
    eLpNorm_sq_le (hbil a c).aestronglyMeasurable
      (by have := vecNorm_nonneg a; have := vecNorm_nonneg c; positivity) (h8 W hW8 X hX a c)
  have hsum : ∀ e, eLpNorm ((1 / 2 : ℝ) •
      ((fun F => ‖bilinear u (freshDelta b E X F) (col Q e)‖ ^ 2) +
        fun F => ‖bilinear v (freshDelta b E X F) (col Q e)‖ ^ 2)) 4 μ ≤
      ENNReal.ofReal ((1 / 2) * ((C8 * D * vecNorm u * vecNorm (col Q e)) ^ 2 +
        (C8 * D * vecNorm v * vecNorm (col Q e)) ^ 2)) := fun e => by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    gcongr
    exact (eLpNorm_add_le (by norm_num)).trans (add_le_add (h8' _ _) (h8' _ _))
  calc eLpNorm (fun F => bilinear u (freshU b E X F - 1) v) 4 μ ≤ eLpNorm g 4 μ :=
        eLpNorm_mono_ae_real hUm.aestronglyMeasurable hpt
    _ ≤ ENNReal.ofReal (C4 * D * vecNorm u * vecNorm (f *ᵥ v)) +
          ENNReal.ofReal (C4 * D * vecNorm v * vecNorm (f *ᵥ u)) +
          ∑ e, ENNReal.ofReal ((1 / 2) * ((C8 * D * vecNorm u * vecNorm (col Q e)) ^ 2 +
            (C8 * D * vecNorm v * vecNorm (col Q e)) ^ 2)) := by
        rw [hg]
        refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ((eLpNorm_add_le
          (by norm_num)).trans (add_le_add (h4' _ _) (h4' _ _))) ?_)
        exact (eLpNorm_sum_le (by norm_num)).trans (Finset.sum_le_sum fun e _ => hsum e)
    _ = ENNReal.ofReal (C4 * D * vecNorm u * vecNorm (f *ᵥ v) +
          C4 * D * vecNorm v * vecNorm (f *ᵥ u) +
          ∑ e, (1 / 2) * ((C8 * D * vecNorm u * vecNorm (col Q e)) ^ 2 +
            (C8 * D * vecNorm v * vecNorm (col Q e)) ^ 2)) := by
        have := vecNorm_nonneg (f *ᵥ u); have := vecNorm_nonneg (f *ᵥ v)
        rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun e _ => by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        set Xl := (vecNorm u ^ 2 + vecNorm v ^ 2) * oneLeak b E X with hXl
        have hsq : ∑ e, (1 / 2 : ℝ) * ((C8 * D * vecNorm u * vecNorm (col Q e)) ^ 2 +
            (C8 * D * vecNorm v * vecNorm (col Q e)) ^ 2) =
            D ^ 2 * (C8 ^ 2 * Xl / (8 * η ^ 2)) := by
          have e1 : ∑ e, (1 / 2 : ℝ) * ((C8 * D * vecNorm u * vecNorm (col Q e)) ^ 2 +
              (C8 * D * vecNorm v * vecNorm (col Q e)) ^ 2) =
              C8 ^ 2 * D ^ 2 * (vecNorm u ^ 2 + vecNorm v ^ 2) / 2 *
                ∑ e, vecNorm (col Q e) ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun e _ => by ring
          rw [e1, hXl, hleak]
          field_simp
          ring
        rw [hsq]
        have h1 : C4 * D * vecNorm u * vecNorm (f *ᵥ v) ≤ C4 * D * vecNorm u * (Fn * vecNorm v) :=
          by gcongr
        have h2 : C4 * D * vecNorm v * vecNorm (f *ᵥ u) ≤ C4 * D * vecNorm v * (Fn * vecNorm u) :=
          by gcongr
        have hL : 0 ≤ Xl := by positivity
        have hDD : D ^ 2 ≤ (η⁻¹ + 2) * D := by
          rw [sq]; exact mul_le_mul_of_nonneg_right hDle hD0
        have hX0 : 0 ≤ C8 ^ 2 * Xl / (8 * η ^ 2) := by positivity
        have h3 : D ^ 2 * (C8 ^ 2 * Xl / (8 * η ^ 2)) ≤
            C8 ^ 2 * (η⁻¹ + 2) / (8 * η ^ 2) * D * Xl := by
          calc D ^ 2 * (C8 ^ 2 * Xl / (8 * η ^ 2)) ≤
                ((η⁻¹ + 2) * D) * (C8 ^ 2 * Xl / (8 * η ^ 2)) :=
                mul_le_mul_of_nonneg_right hDD hX0
            _ = _ := by ring
        have hK : 0 ≤ C8 ^ 2 * (η⁻¹ + 2) / (8 * η ^ 2) := by positivity
        have hrest : 0 ≤ 2 * C4 * Fn * D * Xl +
            C8 ^ 2 * (η⁻¹ + 2) / (8 * η ^ 2) * D * (vecNorm u * vecNorm v) := by positivity
        have e2 : C * D * (vecNorm u * vecNorm v + Xl) =
            C4 * D * vecNorm u * (Fn * vecNorm v) + C4 * D * vecNorm v * (Fn * vecNorm u) +
              C8 ^ 2 * (η⁻¹ + 2) / (8 * η ^ 2) * D * Xl +
              (2 * C4 * Fn * D * Xl +
                C8 ^ 2 * (η⁻¹ + 2) / (8 * η ^ 2) * D * (vecNorm u * vecNorm v)) := by
          simp only [hCdef]; ring
        rw [e2]
        linarith

end BlockBand.SourceProcess.PhysApprox.B3.GramStepU
