module

public import BlockBand.Critical.RelativeVectors.TestedHess

/-!
# The cross-Hessian error of a tested backward function

* `bilRot_eq`: for a real bilinear `D` on the tested array space `(ℂ^r)^k`,
  `D(ia, ib) - D(a, b) = -Re Σ_{e,e'} γ_{ee'} a_e b_{e'}` with
  `γ_{ee'} = (D(1_e,1_{e'}) - D(i_e,i_{e'})) - i(D(1_e,i_{e'}) + D(i_e,1_{e'}))` (`gam`), and
  `|γ_{ee'}| ≤ 4‖D‖` (`norm_gam_le`).
* `crossError_backward_eq`: for the tested backward function `g`,
  `crossError(D²g)(z) = -¼ ∫ Re Σ_{m,q,m',q'} γ_{(m,q),(m',q')}(ω) Σ_i Σ_j Θ^{m m'}_{ij}(ω) z_{iq'} z_{jq} dP`,
  `Θ^{mm'}_{ij} = 1_{i≠j, |i-j| ≥ ℓ} c_ij M_{ι m, i} M_{ι m', j}` (`crossTheta`), a sum of the form
  `Σ Θ_ij z_i^a z_j^b` whose phase average is bounded by `phase_pairing_frame_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N r k : ℕ}

/-!
## Complex coordinates of a real bilinear form on the tested arrays
-/

/-- Real basis `1_{(m,q)}`, `i_{(m,q)}` of `(ℂ^r)^k`. -/
abbrev cR (m : Fin k) (q : Fin r) : Fin k → Fin r → ℂ := Pi.single m (Pi.single q 1)
abbrev cI (m : Fin k) (q : Fin r) : Fin k → Fin r → ℂ := Pi.single m (Pi.single q Complex.I)

theorem arr_decomp (a : Fin k → Fin r → ℂ) :
    a = ∑ m, ∑ q, ((a m q).re • cR m q + (a m q).im • cI m q) := by
  funext m' q'
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single m', Finset.sum_eq_single q']
  · simp only [Pi.single_eq_same]
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    exact (Complex.re_add_im (a m' q')).symm
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [hb]
  · simp

theorem bil_expand2 (D : (Fin k → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) →L[ℝ] ℝ)
    (a b : Fin k → Fin r → ℂ) :
    D a b = ∑ m', ∑ q', ∑ m, ∑ q,
      ((a m q).re * (b m' q').re * D (cR m q) (cR m' q') +
        (a m q).re * (b m' q').im * D (cR m q) (cI m' q') +
        (a m q).im * (b m' q').re * D (cI m q) (cR m' q') +
        (a m q).im * (b m' q').im * D (cI m q) (cI m' q')) := by
  conv_lhs => rw [arr_decomp a, arr_decomp b]
  simp only [map_sum, map_add, map_smul, _root_.sum_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun q' _ =>
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- `γ_{ee'} = (D(1_e,1_{e'}) - D(i_e,i_{e'})) - i(D(1_e,i_{e'}) + D(i_e,1_{e'}))`. -/
def gam (D : (Fin k → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) →L[ℝ] ℝ) (m : Fin k) (q : Fin r)
    (m' : Fin k) (q' : Fin r) : ℂ :=
  ((D (cR m q) (cR m' q') - D (cI m q) (cI m' q') : ℝ) : ℂ) -
    Complex.I * ((D (cR m q) (cI m' q') + D (cI m q) (cR m' q') : ℝ) : ℂ)

/-- `D(ia, ib) - D(a, b) = -Re Σ_{e,e'} γ_{ee'} a_e b_{e'}`. -/
theorem bilRot_eq (D : (Fin k → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) →L[ℝ] ℝ)
    (a b : Fin k → Fin r → ℂ) :
    D (Complex.I • a) (Complex.I • b) - D a b =
      -(∑ m', ∑ q', ∑ m, ∑ q, gam D m q m' q' * (a m q * b m' q')).re := by
  rw [bil_expand2 D (Complex.I • a) (Complex.I • b), bil_expand2 D a b]
  simp only [Complex.re_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun q' _ =>
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, gam, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem norm_gam_le {D : (Fin k → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) →L[ℝ] ℝ} {K : ℝ}
    (hD : ‖D‖ ≤ K) (m : Fin k) (q : Fin r) (m' : Fin k) (q' : Fin r) :
    ‖gam D m q m' q'‖ ≤ 4 * K := by
  have hb : ∀ u w : Fin k → Fin r → ℂ, ‖u‖ = 1 → ‖w‖ = 1 → |D u w| ≤ K := by
    intro u w hu hw
    rw [← Real.norm_eq_abs]
    refine ((D u).le_opNorm w).trans ?_
    rw [hw, mul_one]
    exact (D.le_opNorm u).trans (by rw [hu, mul_one]; exact hD)
  have n1 : ∀ m q, ‖cR (k := k) (r := r) m q‖ = 1 := by
    intro m q; rw [Pi.norm_single, Pi.norm_single]; simp
  have n2 : ∀ m q, ‖cI (k := k) (r := r) m q‖ = 1 := by
    intro m q; rw [Pi.norm_single, Pi.norm_single]; simp
  unfold gam
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have h1 := hb _ _ (n1 m q) (n1 m' q')
  have h2 := hb _ _ (n2 m q) (n2 m' q')
  have h3 := hb _ _ (n1 m q) (n2 m' q')
  have h4 := hb _ _ (n2 m q) (n1 m' q')
  have := abs_sub (D (cR m q) (cR m' q')) (D (cI m q) (cI m' q'))
  have := abs_add_le (D (cR m q) (cI m' q')) (D (cI m q) (cR m' q'))
  linarith

/-!
## The cross term of a tested backward function
-/

/-- `W_ij = Σ_{e,e'} γ_{ee'} (T_i z_j)_e (T_j z_i)_{e'}`, `(T_i v)_m = M_{ι m, i} v`. -/
def crossW (ι : Fin k → Fin N) (D : (Fin k → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) →L[ℝ] ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → Fin r → ℂ) (i j : Fin N) : ℂ :=
  ∑ m', ∑ q', ∑ m, ∑ q, gam D m q m' q' * ((A (ι m) i * z j q) * (A (ι m') j * z i q'))

/-- `Θ^{m m'}_{ij} = 1_{i ≠ j, |i-j| ≥ ℓ} c_ij A_{ι m, i} A_{ι m', j}`. -/
def crossTheta (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (m m' : Fin k) (i j : Fin N) : ℂ :=
  if i ≠ j ∧ ℓ ≤ labelDist i j then (dysonCoupling N lam i j : ℂ) * A (ι m) i * A (ι m') j
  else 0

theorem crossTheta_diag (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) (m m' : Fin k) (i : Fin N) :
    crossTheta ι lam ℓ A m m' i i = 0 := by simp [crossTheta]

theorem smul_I_comm (t : Fin k → ℂ) (v : Fin r → ℂ) :
    (fun m => t m • Complex.I • v : Fin k → Fin r → ℂ) = Complex.I • fun m => t m • v := by
  funext m q; simp [smul_eq_mul]; ring

theorem ite_sum_zero {α : Type*} (p : Prop) [Decidable p] (s : Finset α) (f : α → ℂ) :
    (if p then ∑ x ∈ s, f x else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem sum3_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (G : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, G a b c = ∑ c, ∑ a, ∑ b, G a b c := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem sum6_comm {α β γ δ ε η : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] [Fintype η] (F : α → β → γ → δ → ε → η → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ h, F a b c d e h =
      ∑ c, ∑ d, ∑ e, ∑ h, ∑ a, ∑ b, F a b c d e h := by
  rw [sum3_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum3_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sum3_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum3_comm]

section Backward

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M : Ω → Matrix (Fin N) (Fin N) ℂ} {Ξ : Ω → Fin N → Fin r → ℂ}
  {φ : (Fin k → Fin r → ℂ) → ℝ}

theorem integrable_crossW_re (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (z : Fin N → Fin r → ℂ) (i j : Fin N) :
    Integrable (fun ω => (crossW ι (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω)))
      (M ω) z i j).re) P := by
  have h2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hS.c2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hπ := (testProj ι : (Fin N → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ)).continuous
  have hD : Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul p.1 z + p.2)) :=
    h2.comp (hπ.comp (((continuous_arrayMul_apply z).comp continuous_fst).add continuous_snd))
  have hgam : ∀ m q m' q', Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      gam (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul p.1 z + p.2))) m q m' q' := by
    intro m q m' q'
    unfold gam
    have ev : ∀ u w : Fin k → Fin r → ℂ, Continuous fun p : Matrix (Fin N) (Fin N) ℂ ×
        (Fin N → Fin r → ℂ) => fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul p.1 z + p.2)) u w :=
      fun u w => (hD.clm_apply continuous_const).clm_apply continuous_const
    exact (Complex.continuous_ofReal.comp ((ev _ _).sub (ev _ _))).sub
      (continuous_const.mul (Complex.continuous_ofReal.comp ((ev _ _).add (ev _ _))))
  have hc : Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      (crossW ι (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul p.1 z + p.2))) p.1 z i j).re := by
    unfold crossW
    refine Complex.continuous_re.comp ?_
    refine continuous_finsetSum _ fun m' _ => continuous_finsetSum _ fun q' _ =>
      continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun q _ => ?_
    refine (hgam m q m' q').mul ?_
    exact (((continuous_fst.matrix_elem (ι m) i).mul continuous_const).mul
      ((continuous_fst.matrix_elem (ι m') j).mul continuous_const))
  refine Integrable.of_bound (μ := P) (hc.measurable.comp (hS.measM.prodMk hS.measXi)).aestronglyMeasurable
    (∑ _m' : Fin k, ∑ _q' : Fin r, ∑ _m : Fin k, ∑ _q : Fin r, 4 * K₂ * (‖z‖ * ‖z‖))
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs]
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold crossW
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m' _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q' _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul]
  refine mul_le_mul (norm_gam_le (hS.bound2 _) m q m' q') ?_ (norm_nonneg _) (by
    linarith [hS.nonneg2])
  rw [norm_mul, norm_mul, norm_mul]
  have e1 := hS.entry ω (ι m) i
  have e2 := hS.entry ω (ι m') j
  have z1 : ‖z j q‖ ≤ ‖z‖ := (norm_le_pi_norm (z j) q).trans (norm_le_pi_norm z j)
  have z2 : ‖z i q'‖ ≤ ‖z‖ := (norm_le_pi_norm (z i) q').trans (norm_le_pi_norm z i)
  calc ‖M ω (ι m) i‖ * ‖z j q‖ * (‖M ω (ι m') j‖ * ‖z i q'‖)
      ≤ (1 * ‖z‖) * (1 * ‖z‖) := by gcongr
    _ = ‖z‖ * ‖z‖ := by ring

/-- `crossTerm(D²g)(z)_{ij} = -∫ Re(W_ij + W_ji) dP`. -/
theorem crossTerm_backward_eq (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (z : Fin N → Fin r → ℂ) (i j : Fin N) :
    crossTerm (fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)) z)
        z i j =
      -∫ ω, ((crossW ι (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) (M ω) z i j).re +
        (crossW ι (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) (M ω) z j i).re)
        ∂P := by
  unfold crossTerm
  simp only [hess_tested ι hS]
  set Hs : (Fin N → Fin r → ℂ) → (Fin N → Fin r → ℂ) → Ω → ℝ := fun u w ω =>
    fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω)) (testProj ι (arrayMul (M ω) u))
      (testProj ι (arrayMul (M ω) w)) with hHs
  have hI : ∀ u w, Integrable (Hs u w) P := fun u w => integrable_hess_tested ι hS z u w
  have hAB : Integrable (fun ω => Hs (single i (Complex.I • z j)) (single j (Complex.I • z i)) ω +
      Hs (single j (Complex.I • z i)) (single i (Complex.I • z j)) ω) P := (hI _ _).add (hI _ _)
  have hABC : Integrable (fun ω => Hs (single i (Complex.I • z j)) (single j (Complex.I • z i)) ω +
      Hs (single j (Complex.I • z i)) (single i (Complex.I • z j)) ω -
      Hs (single i (z j)) (single j (z i)) ω) P := hAB.sub (hI _ _)
  calc ∫ ω, Hs (single i (Complex.I • z j)) (single j (Complex.I • z i)) ω ∂P +
        ∫ ω, Hs (single j (Complex.I • z i)) (single i (Complex.I • z j)) ω ∂P -
        ∫ ω, Hs (single i (z j)) (single j (z i)) ω ∂P -
        ∫ ω, Hs (single j (z i)) (single i (z j)) ω ∂P
      = ∫ ω, (Hs (single i (Complex.I • z j)) (single j (Complex.I • z i)) ω +
        Hs (single j (Complex.I • z i)) (single i (Complex.I • z j)) ω -
        Hs (single i (z j)) (single j (z i)) ω - Hs (single j (z i)) (single i (z j)) ω) ∂P := by
        rw [integral_sub hABC (hI _ _), integral_sub hAB (hI _ _), integral_add (hI _ _) (hI _ _)]
    _ = ∫ ω, -((crossW ι (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) (M ω) z i j).re +
        (crossW ι (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) (M ω) z j i).re)
        ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only [hHs, testProj_arrayMul_single, smul_I_comm]
        set D := fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))
        have h1 := bilRot_eq D (fun m => M ω (ι m) i • z j) (fun m => M ω (ι m) j • z i)
        have h2 := bilRot_eq D (fun m => M ω (ι m) j • z i) (fun m => M ω (ι m) i • z j)
        simp only [crossW]
        beta_reduce at h1 h2
        simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
        linarith
    _ = _ := integral_neg _

/-- **The cross error of a tested backward function.** See the module docstring. -/
theorem crossError_backward_eq (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (lam : Fin N → ℝ) (ℓ : ℕ) (z : Fin N → Fin r → ℂ) :
    crossError N r lam ℓ
        (fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)) z) z =
      -(1 / 4 : ℝ) * ∫ ω, (∑ m', ∑ q', ∑ m, ∑ q,
        gam (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) m q m' q' *
          ∑ i, ∑ j, crossTheta ι lam ℓ (M ω) m m' i j * (z i q' * z j q)).re ∂P := by
  unfold crossError
  simp only [crossTerm_backward_eq ι hS]
  set Wr : Ω → Fin N → Fin N → ℝ := fun ω i j =>
    (crossW ι (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) (M ω) z i j).re
    with hWr
  have hint : ∀ i j, Integrable (fun ω => Wr ω i j) P := fun i j => integrable_crossW_re ι hS z i j
  -- pairs to ordered pairs
  have hP : ∀ i j : Fin N, ℓ ≤ labelDist i j → ℓ ≤ labelDist j i :=
    fun i j h => by rwa [labelDist_symm]
  have hpair := sum_pairs_symm (fun i j => ℓ ≤ labelDist i j) hP
    (fun i j => dysonCoupling N lam i j * ∫ ω, Wr ω i j ∂P)
  have e1 : ∀ i, ∑ j ∈ univ.filter (fun j => i < j ∧ ℓ ≤ labelDist i j),
      dysonCoupling N lam i j * -∫ ω, (Wr ω i j + Wr ω j i) ∂P =
      -∑ j ∈ univ.filter (fun j => i < j ∧ ℓ ≤ labelDist i j),
        (dysonCoupling N lam i j * ∫ ω, Wr ω i j ∂P +
          dysonCoupling N lam j i * ∫ ω, Wr ω j i ∂P) := by
    intro i
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add (hint i j) (hint j i), dysonCoupling_symm lam j i]
    ring
  simp only [hWr] at e1
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_neg_distrib, hpair]
  -- integral outside
  have e2 : ∑ i, ∑ j ∈ univ.filter (fun j => i ≠ j ∧ ℓ ≤ labelDist i j),
      dysonCoupling N lam i j * ∫ ω, Wr ω i j ∂P =
      ∫ ω, ∑ i, ∑ j ∈ univ.filter (fun j => i ≠ j ∧ ℓ ≤ labelDist i j),
        dysonCoupling N lam i j * Wr ω i j ∂P := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  simp only [hWr] at e2
  rw [e2]
  have e3 : ∀ ω, ∑ i, ∑ j ∈ univ.filter (fun j => i ≠ j ∧ ℓ ≤ labelDist i j),
      dysonCoupling N lam i j * Wr ω i j =
      (∑ m', ∑ q', ∑ m, ∑ q,
        gam (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) m q m' q' *
          ∑ i, ∑ j, crossTheta ι lam ℓ (M ω) m m' i j * (z i q' * z j q)).re := by
    intro ω
    simp only [hWr]
    have hre : ∑ i, ∑ j ∈ univ.filter (fun j => i ≠ j ∧ ℓ ≤ labelDist i j),
        dysonCoupling N lam i j *
          (crossW ι (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) (M ω) z i j).re =
        (∑ i, ∑ j ∈ univ.filter (fun j => i ≠ j ∧ ℓ ≤ labelDist i j),
          (dysonCoupling N lam i j : ℂ) *
            crossW ι (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) (M ω) z i j).re := by
      simp only [Complex.re_sum, Complex.re_ofReal_mul]
    rw [hre]
    congr 1
    set D := fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))
    simp only [crossW, crossTheta, Finset.sum_filter, Finset.mul_sum, ite_sum_zero]
    rw [sum6_comm]
    refine Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun q' _ =>
      Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  simp only [hWr] at e3
  simp only [e3]
  ring

end Backward

end BlockBand.Critical.RelativeVectors
