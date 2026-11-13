module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWickGenWords
public import BlockBand.Endpoints.Response.TaggedConvexOrderWickGenTaylor
public import BlockBand.Endpoints.Response.TaggedConvexOrderWickMoment
public import BlockBand.Endpoints.Response.TaggedConvexOrderStoppedSummed

/-!
# The generator identity `TcxWickGenerator` and the fixed-energy tagged convex order

`tcx_wickGenerator : TcxWickGenerator` holds at every path (`wg_wickGenerator_path`; the `∀ᵐ` of
`TcxWickGenerator` follows by `ae_of_all`): with `Q = Q_{l;k}`, `R = Q^{1/2}`,
`P = nearProjection W`, `P' = 𝕊*P𝕊`, `v = Rh`, `X = h*Qh`, `κ = D₀/2`, `D₀ = transportD0 b e`,
`polyValue_l(wordGenerator Φ_m) = κ m(m-1) E_h[X^{m-2}(v*Pv)(v*P'v)]` (`= tcw_H`).

The proof writes the generator as a contracted second-order coefficient, evaluates the Wick
side, and computes the probe sum `Σ_x Y_x² = 4G`. The file ends with the fixed-energy tag
comparison core from the moment, birth, stop, word and GUE count contracts
(`tcoTagComparisonCoreFixed_of_contracts`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionUniform
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

section Path

variable (b e : ℝ) (W l k : ℕ) (ω : GrowthPath W)

/-- The index `x = (α, β, c)` of a contraction direction. -/
abbrev wg_Idx (W : ℕ) : Type := (Fin 2 × Fin W) × (Fin 2 × Fin W) × Fin 2

/-- `u_α`: column `α` of `P`. -/
def wg_u (α : Fin 2 × Fin W) : Fin 2 × Fin W → ℂ := fun i => nearProjection W i α

/-- `w_β`: column `β` of `𝕊*P`. -/
def wg_w (β : Fin 2 × Fin W) : Fin 2 × Fin W → ℂ :=
  fun i => ((scatteringMatrix b e W l ω)ᴴ * nearProjection W) i β

theorem wg_hu : ∑ a, vecMulVec (wg_u W a) (star (wg_u W a)) = nearProjection W :=
  (wg_sum_vecMulVec_col _).trans (wg_proj_mul_conjTranspose W)

theorem wg_hw : ∑ a, vecMulVec (wg_w b e W l ω a) (star (wg_w b e W l ω a)) =
    tcw_conjProj b e W l ω :=
  (wg_sum_vecMulVec_col _).trans (wg_conjProj_eq b e W l ω)

/-- `U_{αβ} = u_α w_β*`. -/
def wg_U (x : wg_Idx W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  vecMulVec (wg_u W x.1) (star (wg_w b e W l ω x.2.1))

theorem wg_U_conjTranspose (x : wg_Idx W) :
    (wg_U b e W l ω x)ᴴ = vecMulVec (wg_w b e W l ω x.2.1) (star (wg_u W x.1)) := by
  unfold wg_U
  rw [conjTranspose_vecMulVec, star_star]

/-- The Hermitian direction `K_x`. -/
def wg_K (x : wg_Idx W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  wg_dir (wg_U b e W l ω x) (wg_U b e W l ω x)ᴴ x.2.2

/-- `H_x = R K_x R`, `R = Q^{1/2}`. -/
def wg_H (x : wg_Idx W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  tcw_sqrtQ b e W l k ω * wg_K b e W l ω x * tcw_sqrtQ b e W l k ω

theorem wg_isHermitian_H (x : wg_Idx W) : (wg_H b e W l k ω x).IsHermitian := by
  have hK : (wg_K b e W l ω x)ᴴ = wg_K b e W l ω x := wg_isHermitian_dir _ _
  unfold wg_H Matrix.IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, tcw_sqrtQ_conjTranspose, hK, Matrix.mul_assoc]

/-- `F_x(w)(s)`: `Tr(Q + sH_x)^{|w|}` shifted so that `F_x(w)(0) = wordValue w`. -/
def wg_F (x : wg_Idx W) (w : TraceWord 1 0) : Polynomial ℂ :=
  Polynomial.C (wordValue b e (tcw_tagFamily k) tcw_noInterval W l ω w) +
    (wg_pertTrace (tco_tagQ b e W l k ω) (wg_H b e W l k ω x) w.length -
      Polynomial.C ((tco_tagQ b e W l k ω ^ w.length).trace))

theorem wg_base_F (x : wg_Idx W) :
    wg_base (wg_F b e W l k ω x) = wordValue b e (tcw_tagFamily k) tcw_noInterval W l ω := by
  funext w
  unfold wg_base wg_F
  rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_zero, Polynomial.coeff_C_zero,
    wg_pertTrace_coeff_zero, sub_self, add_zero]

theorem wg_F_tagWord (x : wg_Idx W) (r : ℕ) :
    wg_F b e W l k ω x (tcx_tagWord r) =
      wg_pertTrace (tco_tagQ b e W l k ω) (wg_H b e W l k ω x) r := by
  unfold wg_F
  rw [tcx_wordValue_tagWord, wg_tagWord_eq, List.length_replicate]
  ring

theorem wg_F_coeff_one (x : wg_Idx W) (r : ℕ) :
    (wg_F b e W l k ω x (tcx_tagWord r)).coeff 1 =
      (r : ℂ) * (tco_tagQ b e W l k ω ^ r * wg_K b e W l ω x).trace := by
  rw [wg_F_tagWord, wg_pertTrace_coeff_one, wg_H, wg_trace_A_sandwich (tcw_sqrtQ_mul_self b e W l k ω)]

theorem wg_F_coeff_two (x : wg_Idx W) (r : ℕ) :
    (wg_F b e W l k ω x (tcx_tagWord r)).coeff 2 = ∑ i ∈ range r, ∑ j ∈ Ioo i r,
      (tco_tagQ b e W l k ω ^ (r - (j - i)) * wg_K b e W l ω x * tco_tagQ b e W l k ω ^ (j - i) *
        wg_K b e W l ω x).trace := by
  rw [wg_F_tagWord, wg_pertTrace_coeff_two, wg_H, wg_trace_B_sandwich (tcw_sqrtQ_mul_self b e W l k ω)]

/-!
## The contraction sums over `x`
-/

theorem wg_sum_Idx {M : Type*} [AddCommMonoid M] (f : wg_Idx W → M) :
    ∑ x, f x = ∑ a, ∑ c, ∑ d, f (a, c, d) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]

theorem wg_sum_K_mul_mul (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ x, (A * wg_K b e W l ω x * B * wg_K b e W l ω x).trace =
      2 * ((A * nearProjection W).trace * (B * tcw_conjProj b e W l ω).trace +
        (A * tcw_conjProj b e W l ω).trace * (B * nearProjection W).trace) := by
  rw [wg_sum_Idx]
  simp only [wg_K, wg_U, conjTranspose_vecMulVec, star_star, wg_sum_dir_trace_mul_mul]
  rw [← wg_sum_trace_mul_mul A B _ _ (wg_u W) (wg_w b e W l ω) (wg_hu W) (wg_hw b e W l ω),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

theorem wg_sum_K_trace_mul_trace (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ x, (A * wg_K b e W l ω x).trace * (B * wg_K b e W l ω x).trace =
      2 * ((A * nearProjection W * B * tcw_conjProj b e W l ω).trace +
        (A * tcw_conjProj b e W l ω * B * nearProjection W).trace) := by
  rw [wg_sum_Idx]
  simp only [wg_K, wg_U, conjTranspose_vecMulVec, star_star, wg_sum_dir_trace_mul_trace]
  rw [← wg_sum_trace_mul_trace A B _ _ (wg_u W) (wg_w b e W l ω) (wg_hu W) (wg_hw b e W l ω),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-- `wordDrift` is the contracted `s²`-coefficient: `drift(w_r) = (κ/2) Σ_x [s²]F_x(w_r)`. -/
theorem wg_polyValue_wordDrift_eq (D0 : ℝ) (r : ℕ) :
    polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω (wordDrift D0 (tcx_tagWord r)) =
      ((D0 / 2 : ℝ) : ℂ) / 2 * ∑ x, (wg_F b e W l k ω x (tcx_tagWord r)).coeff 2 := by
  rw [wg_polyValue_wordDrift]
  simp only [wg_F_coeff_two]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wg_sum_K_mul_mul]
  unfold wg_T
  ring

/-- `wordCov` is the contracted product of `s`-coefficients:
`cov(w_r, w_s) = (κ/2) Σ_x [s]F_x(w_r) [s]F_x(w_s)`. -/
theorem wg_polyValue_wordCov_eq (D0 : ℝ) (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω
        (wordCov D0 (tcx_tagWord r) (tcx_tagWord s)) =
      ((D0 / 2 : ℝ) : ℂ) / 2 * ∑ x, ((wg_F b e W l k ω x (tcx_tagWord r)).coeff 1 *
        (wg_F b e W l k ω x (tcx_tagWord s)).coeff 1) := by
  rw [wg_polyValue_wordCov _ _ _ _ _ _ _ _ _ hr hs]
  simp only [wg_F_coeff_one]
  have h := wg_sum_K_trace_mul_trace b e W l ω (tco_tagQ b e W l k ω ^ r) (tco_tagQ b e W l k ω ^ s)
  have e1 : ∑ x, (r : ℂ) * (tco_tagQ b e W l k ω ^ r * wg_K b e W l ω x).trace *
      ((s : ℂ) * (tco_tagQ b e W l k ω ^ s * wg_K b e W l ω x).trace) =
      (r : ℂ) * (s : ℂ) * ∑ x, (tco_tagQ b e W l k ω ^ r * wg_K b e W l ω x).trace *
        (tco_tagQ b e W l k ω ^ s * wg_K b e W l ω x).trace := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by ring
  rw [e1, h]
  unfold wg_Cr
  ring

end Path

/-!
## The generator as a contracted second-order coefficient
-/

theorem wg_polyValue_wordGenerator (b e : ℝ) (W l k m : ℕ) (t : ℝ) (ω : GrowthPath W) :
    polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω
        (wordGenerator b e tcw_noInterval t (tcx_wickPoly m)) =
      ((transportD0 b e / 2 : ℝ) : ℂ) / 2 * ∑ x, (MvPolynomial.aeval
        (wg_restrict (wg_F b e W l k ω x) (tcx_wickPoly m).vars) (tcx_wickPoly m)).coeff 2 := by
  have hD : ∀ w ∈ (tcx_wickPoly m).vars,
      MvPolynomial.eval (wordValue b e (tcw_tagFamily k) tcw_noInterval W l ω)
        (wordDrift (transportD0 b e) w) + wordInjection b tcw_noInterval t w =
      ((transportD0 b e / 2 : ℝ) : ℂ) / 2 * ∑ x, (wg_F b e W l k ω x w).coeff 2 := by
    intro w hw
    obtain ⟨r, -, rfl⟩ := wg_mem_vars_wickPoly m w hw
    rw [wg_wordInjection_eq_zero, add_zero]
    exact wg_polyValue_wordDrift_eq b e W l k ω _ r
  have hC : ∀ w ∈ (tcx_wickPoly m).vars, ∀ v ∈ (tcx_wickPoly m).vars,
      MvPolynomial.eval (wordValue b e (tcw_tagFamily k) tcw_noInterval W l ω)
        (wordCov (transportD0 b e) w v) = ((transportD0 b e / 2 : ℝ) : ℂ) / 2 *
          ∑ x, ((wg_F b e W l k ω x w).coeff 1 * (wg_F b e W l k ω x v).coeff 1) := by
    intro w hw v hv
    obtain ⟨r, hr, rfl⟩ := wg_mem_vars_wickPoly m w hw
    obtain ⟨s, hs, rfl⟩ := wg_mem_vars_wickPoly m v hv
    exact wg_polyValue_wordCov_eq b e W l k ω _ r s hr hs
  have hT : ∀ x, (MvPolynomial.aeval (wg_restrict (wg_F b e W l k ω x) (tcx_wickPoly m).vars)
      (tcx_wickPoly m)).coeff 2 =
      ∑ w ∈ (tcx_wickPoly m).vars, MvPolynomial.eval
          (wordValue b e (tcw_tagFamily k) tcw_noInterval W l ω)
          (MvPolynomial.pderiv w (tcx_wickPoly m)) * (wg_F b e W l k ω x w).coeff 2 +
        1 / 2 * ∑ w ∈ (tcx_wickPoly m).vars, ∑ v ∈ (tcx_wickPoly m).vars,
          MvPolynomial.eval (wordValue b e (tcw_tagFamily k) tcw_noInterval W l ω)
            (MvPolynomial.pderiv v (MvPolynomial.pderiv w (tcx_wickPoly m))) *
            ((wg_F b e W l k ω x w).coeff 1 * (wg_F b e W l k ω x v).coeff 1) := by
    intro x
    rw [wg_taylor2, wg_base_F]
  unfold wordGenerator polyValue
  simp only [map_add, map_sum, map_mul, MvPolynomial.eval_C]
  rw [Finset.sum_congr rfl fun w hw => by rw [hD w hw],
    Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun v hv => by rw [hC w hw v hv]]
  simp only [hT, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => by ring
  · conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun x _ => by ring

/-!
## The Wick side
-/

theorem wg_aeval_restrict_wickPoly (b e : ℝ) (W l k m : ℕ) (ω : GrowthPath W) (x : wg_Idx W) :
    MvPolynomial.aeval (wg_restrict (wg_F b e W l k ω x) (tcx_wickPoly m).vars) (tcx_wickPoly m) =
      ∑ π : Equiv.Perm (Fin m), (π.partition.parts.map fun r =>
        wg_pertTrace (tco_tagQ b e W l k ω) (wg_H b e W l k ω x) r).prod := by
  have hcongr : MvPolynomial.aeval (wg_restrict (wg_F b e W l k ω x) (tcx_wickPoly m).vars)
      (tcx_wickPoly m) = MvPolynomial.aeval (wg_F b e W l k ω x) (tcx_wickPoly m) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def]
    refine MvPolynomial.eval₂_congr _ _ _ fun {i c} hi hc => ?_
    have hv : i ∈ (tcx_wickPoly m).vars :=
      (MvPolynomial.mem_vars_iff_mem_support i).2 ⟨c, MvPolynomial.mem_support_iff.2 hc, hi⟩
    simp [wg_restrict, hv]
  rw [hcongr]
  unfold tcx_wickPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  simp only [Function.comp_apply, MvPolynomial.aeval_X, wg_F_tagWord]

theorem wg_coeff_two_x (b e : ℝ) (W l k m : ℕ) (ω : GrowthPath W) (x : wg_Idx W) :
    (MvPolynomial.aeval (wg_restrict (wg_F b e W l k ω x) (tcx_wickPoly m).vars)
        (tcx_wickPoly m)).coeff 2 =
      (((m.choose 2 : ℝ) * ∫ h, quadForm (tco_tagQ b e W l k ω) h ^ (m - 2) *
        quadForm (wg_H b e W l k ω x) h ^ 2 ∂circularVectorLaw (Fin 2 × Fin W) : ℝ) : ℂ) := by
  rw [wg_aeval_restrict_wickPoly]
  exact wg_coeff_two_wick m (tco_posSemidef_tagQ b e W l k ω).1 (wg_isHermitian_H b e W l k ω x)

/-!
## The probe sum `Σ_x Y_x² = 4G`
-/

theorem wg_quadForm_H (b e : ℝ) (W l k : ℕ) (ω : GrowthPath W) (x : wg_Idx W)
    (h : Fin 2 × Fin W → ℂ) :
    quadForm (wg_H b e W l k ω x) h =
      (star (tcw_v b e W l k (ω, h)) ⬝ᵥ (wg_K b e W l ω x *ᵥ tcw_v b e W l k (ω, h))).re := by
  unfold quadForm wg_H tcw_v
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, tcw_sqrtQ_conjTranspose]

theorem wg_sum_sq_Y (b e : ℝ) (W l k : ℕ) (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ) :
    ∑ x, quadForm (wg_H b e W l k ω x) h ^ 2 = 4 * tcw_G b e W l k (ω, h) := by
  simp only [wg_quadForm_H]
  set v := tcw_v b e W l k (ω, h)
  have hstar : ∀ β, Complex.normSq (star (wg_w b e W l ω β) ⬝ᵥ v) =
      Complex.normSq (star v ⬝ᵥ wg_w b e W l ω β) := by
    intro β
    rw [Matrix.star_dotProduct, Complex.star_def, Complex.normSq_conj]
  have hP := congrArg Complex.re (wg_sum_normSq_dotProduct _ (wg_u W) (wg_hu W) v)
  have hP' := congrArg Complex.re
    (wg_sum_normSq_dotProduct _ (wg_w b e W l ω) (wg_hw b e W l ω) v)
  rw [Complex.ofReal_re] at hP hP'
  rw [wg_sum_Idx]
  simp only [wg_K, wg_U, wg_sum_re_sq_dir, wg_dotProduct_vecMulVec, map_mul, hstar]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hP, hP']
  rfl

/-!
## The generator identity
-/

/-- The generator identity at every path:
`Re polyValue_l(𝒜Φ_m) = (D₀/2) m(m-1) E_h[X^{m-2}(v*Pv)(v*P'v)]`. -/
theorem wg_wickGenerator_path (m : ℕ) (b e : ℝ) (W l k : ℕ) (t : ℝ) (ω : GrowthPath W) :
    (polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω
      (wordGenerator b e tcw_noInterval t (tcx_wickPoly m))).re = tcw_H b e W l k m ω := by
  set Q := tco_tagQ b e W l k ω
  set I := ∫ h, quadForm Q h ^ (m - 2) * tcw_G b e W l k (ω, h) ∂circularVectorLaw (Fin 2 × Fin W)
  have hsum : ∑ x : wg_Idx W, ∫ h, quadForm Q h ^ (m - 2) * quadForm (wg_H b e W l k ω x) h ^ 2
      ∂circularVectorLaw (Fin 2 × Fin W) = 4 * I := by
    rw [← integral_finsetSum _ fun x _ => wg_integrable_quadForm_pow_mul_pow _ _ _ _,
      ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only
    rw [← Finset.mul_sum, wg_sum_sq_Y]
    ring
  have hH : tcw_H b e W l k m ω = transportD0 b e / 2 * ((m : ℝ) * ((m : ℝ) - 1)) * I := by
    unfold tcw_H
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only
    rw [tcw_X_eq, tco_tagClock_eq_quadForm]
    ring
  rw [wg_polyValue_wordGenerator]
  simp only [wg_coeff_two_x]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum, hsum, hH,
    show ((transportD0 b e / 2 : ℝ) : ℂ) / 2 = (((transportD0 b e / 2) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re, Nat.cast_choose_two]
  ring

/-- **The generator identity** `TcxWickGenerator`; it holds at every path. -/
theorem tcx_wickGenerator : TcxWickGenerator := by
  intro m b _ _ e _ _ W _ l k t
  exact ae_of_all _ fun ω => wg_wickGenerator_path m b e W l k t ω

/-!
## The fixed-energy tagged convex order from the contracts
-/

/-- `TcoTagComparisonCoreFixed` from the contracts alone (the identities `TcxWickMoment`,
`TcxWickGenerator` are proved). -/
theorem tcoTagComparisonCoreFixed_of_contracts (hMom : FullSourceMomentsContract)
    (hBirth : TagBirthValueContract) (hStops : FullSourceStopsContract)
    (hCount : ConditionalBlockGUECount) (hCW : ContractingWordsContract) :
    TcoTagComparisonCoreFixed :=
  tcoTagComparisonCoreFixed_of_wick hMom hBirth hStops hCount hCW tcx_wickMoment tcx_wickGenerator

/-- **The tagged convex order theorem at fixed energy** (`taggedConvexOrder_fixed`) from the
contracts alone.
-/
theorem taggedConvexOrder_fixed_of_contracts (hMomU : FullSourceMomentsEnergyUniformContract)
    (hMom : FullSourceMomentsContract) (hBirth : TagBirthValueContract)
    (hStops : FullSourceStopsContract) (hCount : ConditionalBlockGUECount)
    (hCW : ContractingWordsContract) : TaggedConvexOrderFixedStatement :=
  taggedConvexOrder_fixed_of_wick hMomU hMom hBirth hStops hCount hCW tcx_wickMoment
    tcx_wickGenerator

end BlockBand.Endpoints
