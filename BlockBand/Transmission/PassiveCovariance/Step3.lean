module

public import BlockBand.Transmission.PassiveCovariance.Step5
public import BlockBand.Transmission.SchurDerivative

/-!
# The scalar words `⟨R²R*⟩` and `⟨R²R*²⟩` of the passive covariance

Near a stationary jet, the normalized traces `⟨R²R*⟩` and `⟨R²R*²⟩` of the passive resolvent are
explicit scalars `B_*`, `C_*` up to `O(δ₀ + δ₁ + q/W)`.


* `norm_trace_mul_posSemidef_le`: `|Tr(MP)| ≤ ‖M‖ Re Tr P` for `P ⪰ 0`
  (via `P = X*X`, `CFC.exists_sqrt_…`);
* `deriv_normTrace_resolvent`: `∂_z⟨(z-X)⁻¹⟩ = -⟨R²⟩`, hence `|⟨R²⟩ + s| = δ₁`;
* `normTrace_R2Rstar_sub_le`: `|⟨R²R*⟩ - c₀(d_*+s)| ≤ K_B(δ₀+δ₁+q/W)`;
* `normTrace_R2Rstar2_sub_le`: `|⟨R²R*²⟩ - (s+s̄+2d_*)/(4η²)| ≤ K_C(δ₀+δ₁+q/W)`,
  where `K_B = 2/η² + 1/η` and `K_C = K_B/η + 1/η³`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

section Trace

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_conjTranspose_mul_self {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    ∃ X : Matrix n n ℂ, P = Xᴴ * X := by
  obtain ⟨X, hX, -, h⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hP.isHermitian
      (QuasispectrumRestricts.nnreal_of_nonneg hP.nonneg)
  refine ⟨X, ?_⟩
  have hXh : Xᴴ = X := hX
  rw [hXh, h]

omit [DecidableEq n] in
theorem diag_mul_mul_conjTranspose (X M : Matrix n n ℂ) (i : n) :
    (X * M * Xᴴ) i i = star (star (fun k => X i k)) ⬝ᵥ (M *ᵥ star (fun k => X i k)) := by
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- `|Tr(MP)| ≤ ‖M‖ Re Tr P` for `P ⪰ 0`. -/
theorem norm_trace_mul_posSemidef_le {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (M : Matrix n n ℂ) : ‖(M * P).trace‖ ≤ ‖M‖ * P.trace.re := by
  obtain ⟨X, rfl⟩ := exists_conjTranspose_mul_self hP
  have htr : (M * (Xᴴ * X)).trace = (X * M * Xᴴ).trace := by
    rw [← mul_assoc, trace_mul_comm, ← mul_assoc]
  rw [htr, trace_mul_comm Xᴴ X]
  have hre : (X * Xᴴ).trace.re = ∑ i, vecNorm (star fun k => X i k) ^ 2 := by
    simp only [trace, diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vecNorm, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [hre, trace, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [diag_apply, diag_mul_mul_conjTranspose]
  refine (norm_star_dotProduct_le _ _).trans ?_
  have := vecNorm_mulVec_le M (star fun k => X i k)
  have := vecNorm_nonneg (star fun k => X i k)
  nlinarith

end Trace

variable {W : ℕ} {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)

include hb0 hb h1 h2 hY

/-- `∂_z⟨(z - X)⁻¹⟩ = -⟨R²⟩` at `z = z_∂` (the derivative in `jetDistance1`). -/
theorem deriv_normTrace_resolvent :
    deriv (fun w : ℂ => (W : ℂ)⁻¹ * ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace)
        (boundaryZ b E) =
      -((W : ℂ)⁻¹ * (passiveResolvent b E X * passiveResolvent b E X).trace) := by
  have hK := (passive_inverse_constructed _ _ (etaZ_pos b E (by linarith) h1 h2) hY
    (matrixImaginaryPart_nearPencil b E X)).1
  have hK' : IsUnit (-X + boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ)) := by
    rwa [neg_add_eq_sub]
  have hd := affineInverse_hasDerivAt (-X) 1 (boundaryZ b E) hK'
  have ht := ((Matrix.traceLinearMap (Fin W) ℂ ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    _ hd).const_mul (W : ℂ)⁻¹
  have hfun2 : (fun w : ℂ => (W : ℂ)⁻¹ * ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace) =
      fun y => (W : ℂ)⁻¹ * ((Matrix.traceLinearMap (Fin W) ℂ ℂ).toContinuousLinearMap ∘
        fun t : ℂ => (-X + t • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹) y := by
    funext y; simp [neg_add_eq_sub]
  rw [hfun2, ht.deriv]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.traceLinearMap_apply,
    neg_add_eq_sub, Matrix.mul_one, trace_neg, mul_neg]
  rfl

/-- `|⟨R²⟩ + s| = δ₁`. -/
theorem normTrace_R2_add_s (s : ℂ) :
    ‖(W : ℂ)⁻¹ * (passiveResolvent b E X * passiveResolvent b E X).trace + s‖ =
      jetDistance1 b E s X := by
  rw [jetDistance1, deriv_normTrace_resolvent hb0 hb h1 h2 hY, ← norm_neg]
  congr 1; ring

/-- The constant `K_B = 2/η² + 1/η`. -/
def constB (b E : ℝ) : ℝ := 2 / etaZ b E ^ 2 + 1 / etaZ b E

/-- **`⟨R²R*⟩ = c₀(d_* + s) + O(δ₀ + δ₁ + q/W)`** (the scalar `B_*`). -/
theorem normTrace_R2Rstar_sub_le (hW : W ≠ 0) (s : ℂ) :
    ‖(W : ℂ)⁻¹ * (passiveResolvent b E X * passiveResolvent b E X *
        (passiveResolvent b E X)ᴴ).trace - jetB b E s‖ ≤
      constB b E * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) := by
  have hηpos := etaZ_pos b E (by linarith) h1 h2
  have hη : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hηpos.ne'
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hWr : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW
  have hRR := resolvent_mul_adj hb0 hb h1 h2 hY
  have hQtr0 := trace_tildeQ hb0 hb h1 h2 hY
  have b1 := normTrace_RRstar_sub_dStar_le hb0 hb h1 h2 hY hW
  have b2 := normTrace_R2_add_s hb0 hb h1 h2 hY s
  have hR := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have hQt : (passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ).PosSemidef :=
    hY.mul_mul_conjTranspose_same _
  set R := passiveResolvent b E X
  set Qt := R * passiveY X * Rᴴ
  have hQtr : Qt.trace.re = passiveMass b E X := by rw [hQtr0]; rfl
  have hexp : R * R * Rᴴ = cZero b E • (R * Rᴴ) - cZero b E • (R * R) -
      (etaZ b E : ℂ)⁻¹ • (R * Qt) := by
    conv_lhs => rw [mul_assoc, hRR]
    simp only [mul_sub, mul_smul_comm, Qt, mul_assoc, smul_sub]
  set e1 := (W : ℂ)⁻¹ * (R * Rᴴ).trace - dStar b
  set e2 := (W : ℂ)⁻¹ * (R * R).trace + s
  set e3 := (W : ℂ)⁻¹ * (R * Qt).trace
  have key : (W : ℂ)⁻¹ * (R * R * Rᴴ).trace - jetB b E s =
      cZero b E * e1 - cZero b E * e2 - (etaZ b E : ℂ)⁻¹ * e3 := by
    rw [hexp, trace_sub, trace_sub, trace_smul, trace_smul, trace_smul, jetB]
    simp only [smul_eq_mul, e1, e2, e3]
    ring
  have b3 : ‖e3‖ ≤ (etaZ b E)⁻¹ * (passiveMass b E X / W) := by
    simp only [e3, norm_mul, norm_inv, Complex.norm_natCast]
    have h := norm_trace_mul_posSemidef_le hQt R
    rw [hQtr] at h
    have hq := passiveMass_nonneg b E hY
    calc (W : ℝ)⁻¹ * ‖(R * Qt).trace‖ ≤ (W : ℝ)⁻¹ * ((etaZ b E)⁻¹ * passiveMass b E X) :=
          mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right hR hq)) (by positivity)
      _ = _ := by ring
  have hc := norm_cZero b E hηpos
  have hq := passiveMass_nonneg b E hY
  have hd0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hd1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  have hqW : 0 ≤ passiveMass b E X / W := by positivity
  have n1 : ‖cZero b E * e1‖ ≤ 1 / etaZ b E ^ 2 *
      (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) := by
    rw [norm_mul, hc]
    have t := mul_le_mul_of_nonneg_left b1 (by positivity : (0 : ℝ) ≤ (2 * etaZ b E)⁻¹)
    have : (2 * etaZ b E)⁻¹ * ((jetDistance0 b E X + passiveMass b E X / W) / etaZ b E) =
        1 / (2 * etaZ b E ^ 2) * (jetDistance0 b E X + passiveMass b E X / W) := by
      field_simp
    have h2' : 1 / (2 * etaZ b E ^ 2) ≤ 1 / etaZ b E ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    have h3' := mul_le_mul h2' (by linarith : jetDistance0 b E X + passiveMass b E X / W ≤
      jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) (by positivity)
      (by positivity)
    linarith
  have n2 : ‖cZero b E * e2‖ ≤ 1 / etaZ b E *
      (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) := by
    rw [norm_mul, hc, b2]
    have : (2 * etaZ b E)⁻¹ ≤ 1 / etaZ b E := by
      rw [one_div]; apply inv_anti₀ hηpos; linarith
    exact mul_le_mul this (by linarith) hd1 (by positivity)
  have n3 : ‖(etaZ b E : ℂ)⁻¹ * e3‖ ≤ 1 / etaZ b E ^ 2 *
      (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
    have t := mul_le_mul_of_nonneg_left b3 (by positivity : (0 : ℝ) ≤ (etaZ b E)⁻¹)
    have : (etaZ b E)⁻¹ * ((etaZ b E)⁻¹ * (passiveMass b E X / W)) =
        1 / etaZ b E ^ 2 * (passiveMass b E X / W) := by field_simp
    have h3' := mul_le_mul_of_nonneg_left (by linarith : passiveMass b E X / W ≤
      jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)
      (by positivity : (0 : ℝ) ≤ 1 / etaZ b E ^ 2)
    linarith
  rw [key, constB]
  have := norm_sub_le (cZero b E * e1 - cZero b E * e2) ((etaZ b E : ℂ)⁻¹ * e3)
  have := norm_sub_le (cZero b E * e1) (cZero b E * e2)
  have e : (2 / etaZ b E ^ 2 + 1 / etaZ b E) *
      (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) =
      1 / etaZ b E ^ 2 * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) +
      1 / etaZ b E * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) +
      1 / etaZ b E ^ 2 * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) := by
    ring
  linarith

/-- The constant `K_C = K_B/η + 1/η³`. -/
def constC (b E : ℝ) : ℝ := constB b E / etaZ b E + 1 / etaZ b E ^ 3

omit hY in
theorem constB_nonneg : 0 ≤ constB b E := by
  have := etaZ_pos b E (by linarith) h1 h2; rw [constB]; positivity

/-- **`⟨R²R*²⟩ = (s+s̄+2d_*)/(4η²) + O(δ₀ + δ₁ + q/W)`** (the scalar `C_*`). -/
theorem normTrace_R2Rstar2_sub_le (hW : W ≠ 0) (s : ℂ) :
    ‖(W : ℂ)⁻¹ * (passiveResolvent b E X * passiveResolvent b E X *
        (passiveResolvent b E X)ᴴ * (passiveResolvent b E X)ᴴ).trace - jetC b E s‖ ≤
      constC b E * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) := by
  have hηpos := etaZ_pos b E (by linarith) h1 h2
  have hη : etaZ b E ≠ 0 := hηpos.ne'
  have hRR := resolvent_mul_adj hb0 hb h1 h2 hY
  have hQtr0 := trace_tildeQ hb0 hb h1 h2 hY
  have hB := normTrace_R2Rstar_sub_le hb0 hb h1 h2 hY hW s
  have hR := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have hKB := constB_nonneg (b := b) (E := E) hb0 hb h1 h2
  have hQt : (passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ).PosSemidef :=
    hY.mul_mul_conjTranspose_same _
  have hg : (4 * (etaZ b E : ℂ) ^ 2)⁻¹ = -cZero b E ^ 2 := by
    rw [cZero_sq b E hη]; push_cast; ring
  set R := passiveResolvent b E X
  set Qt := R * passiveY X * Rᴴ
  have hQtr : Qt.trace.re = passiveMass b E X := by rw [hQtr0]; rfl
  have hexp : R * R * Rᴴ * Rᴴ = cZero b E • (R * Rᴴ * Rᴴ) - cZero b E • (R * R * Rᴴ) -
      (etaZ b E : ℂ)⁻¹ • (R * Qt * Rᴴ) := by
    conv_lhs => rw [mul_assoc R R, hRR]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, Qt, mul_assoc, smul_sub]
  have hconj : (R * Rᴴ * Rᴴ).trace = conj (R * R * Rᴴ).trace := by
    rw [← Complex.star_def, ← trace_conjTranspose]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
  set β := (W : ℂ)⁻¹ * (R * R * Rᴴ).trace
  set e := β - jetB b E s
  set e3 := (W : ℂ)⁻¹ * (R * Qt * Rᴴ).trace
  have key : (W : ℂ)⁻¹ * (R * R * Rᴴ * Rᴴ).trace - jetC b E s =
      cZero b E * (conj e - e) - (etaZ b E : ℂ)⁻¹ * e3 := by
    rw [hexp, trace_sub, trace_sub, trace_smul, trace_smul, trace_smul, hconj, jetC,
      div_eq_mul_inv _ (4 * (etaZ b E : ℂ) ^ 2), hg]
    simp only [smul_eq_mul, e, e3, β, jetB, map_sub, map_mul, map_inv₀, Complex.conj_natCast,
      conj_cZero, map_add, Complex.conj_ofReal]
    ring
  have b3 : ‖e3‖ ≤ (etaZ b E)⁻¹ ^ 2 * (passiveMass b E X / W) := by
    have htr : (R * Qt * Rᴴ).trace = (Rᴴ * R * Qt).trace := by
      rw [trace_mul_comm, ← mul_assoc]
    simp only [e3, norm_mul, norm_inv, Complex.norm_natCast, htr]
    have h := norm_trace_mul_posSemidef_le hQt (Rᴴ * R)
    rw [hQtr, Matrix.l2_opNorm_conjTranspose_mul_self] at h
    have hq := passiveMass_nonneg b E hY
    have hR2 : ‖R‖ * ‖R‖ ≤ (etaZ b E)⁻¹ ^ 2 := by
      rw [pow_two]; exact mul_le_mul hR hR (norm_nonneg _) (by positivity)
    calc (W : ℝ)⁻¹ * ‖(Rᴴ * R * Qt).trace‖ ≤
          (W : ℝ)⁻¹ * ((etaZ b E)⁻¹ ^ 2 * passiveMass b E X) :=
          mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right hR2 hq)) (by positivity)
      _ = _ := by ring
  set δ := jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W
  have hq := passiveMass_nonneg b E hY
  have hqW : 0 ≤ passiveMass b E X / W := by positivity
  have hd0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hd1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  have n1 : ‖cZero b E * (conj e - e)‖ ≤ constB b E / etaZ b E * δ := by
    rw [norm_mul, norm_cZero b E hηpos]
    have : ‖conj e - e‖ ≤ 2 * (constB b E * δ) := by
      have := norm_sub_le (conj e) e
      rw [Complex.norm_conj] at this
      linarith
    have t := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (2 * etaZ b E)⁻¹)
    have : (2 * etaZ b E)⁻¹ * (2 * (constB b E * δ)) = constB b E / etaZ b E * δ := by
      field_simp
    linarith
  have n2 : ‖(etaZ b E : ℂ)⁻¹ * e3‖ ≤ 1 / etaZ b E ^ 3 * δ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
    have t := mul_le_mul_of_nonneg_left b3 (by positivity : (0 : ℝ) ≤ (etaZ b E)⁻¹)
    have : (etaZ b E)⁻¹ * ((etaZ b E)⁻¹ ^ 2 * (passiveMass b E X / W)) =
        1 / etaZ b E ^ 3 * (passiveMass b E X / W) := by field_simp
    have h3' := mul_le_mul_of_nonneg_left (by linarith : passiveMass b E X / W ≤ δ)
      (by positivity : (0 : ℝ) ≤ 1 / etaZ b E ^ 3)
    linarith
  rw [key, constC, add_mul]
  linarith [norm_sub_le (cZero b E * (conj e - e)) ((etaZ b E : ℂ)⁻¹ * e3)]

end BlockBand.Transmission.PassiveCovariance
