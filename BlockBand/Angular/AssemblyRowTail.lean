module

public import BlockBand.Angular.Assembly
public import BlockBand.QUE.Invariance.CyclicLaw

/-!
# The pair-row norm tail

**`pairRowNormTail_holds : Assembly.PairRowNormTailStatement`**, with no hypothesis:
`P♯_{α,S}{‖H_SS‖ + ‖H_RS‖ > W/2} ≤ 49152 T / W` for `n ≤ TW` (operator norms).

Proof (second Frobenius moment of the `2W` pair columns, `k = 2`).
* `F(H) = Σ_{x} Σ_{y ∈ S} |H_xy|²` dominates `‖H_SS‖² + ‖H_RS‖²` (operator norm `≤` Frobenius,
  `l2_opNorm_le_frob`), so the event lies in `{F² ≥ W⁴/256}`.
* Entry moments from the exact law (`GaussianRingModel.law_eq_gaussianMatrixLaw`: product of
  centred real Gaussian coordinates): `E|H_xy|⁴ ≤ 96 σ_xy²`, `σ_xy = entryVariance x y`
  (`lintegral_entry_four_le`; the Gaussian fourth moment from the moment generating function,
  `t⁴ ≤ 24 v²(e^{t/√v} + e^{-t/√v})`). No independence is used: Cauchy–Schwarz on each product
  gives `E F² ≤ (Σ √96 σ_xy)² ≤ 96 (2W)²`, since column variance sums are `≤ c + 2b = 1`
  (`sum_entryVariance_le_one`).
* Markov: `P(F² ≥ W⁴/256) ≤ 98304/W²`; the pair density is `(n/2)(m_i + m_{i+1}) ≤ n/2` almost
  surely (block masses sum to one), and `n/2 · 98304/W² ≤ 49152 T/W`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Assembly

open MeasureTheory ProbabilityTheory BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.QUE.Fourier
open BlockBand.Angular.FiberAngular
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

namespace RowTail

/-!
## Operator norm and Frobenius norm
-/

/-- `‖A‖ ≤ (Σ |A_rc|²)^{1/2}` for the Euclidean operator norm. -/
theorem l2_opNorm_le_frob {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ‖A‖ ≤ Real.sqrt (∑ r, ∑ c, ‖A r c‖ ^ 2) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r _ => ?_
  calc ‖(A *ᵥ WithLp.ofLp x) r‖ ^ 2 ≤ (∑ c, ‖A r c‖ * ‖WithLp.ofLp x c‖) ^ 2 := by
        gcongr
        unfold Matrix.mulVec dotProduct
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-!
## Gaussian fourth moments
-/

theorem lintegral_exp_mul_gaussianReal (v : ℝ≥0) (c : ℝ) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (c * t)) ∂gaussianReal 0 v =
      ENNReal.ofReal (Real.exp ((v : ℝ) * c ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal c)
    (ae_of_all _ fun t => (Real.exp_pos _).le)]
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) c
  simp only [mgf, id] at this
  rw [this]
  congr 2
  ring

theorem pow_four_le_exp (y : ℝ) : y ^ 4 ≤ 24 * (Real.exp y + Real.exp (-y)) := by
  have h1 := Real.pow_div_factorial_le_exp |y| (abs_nonneg y) 4
  have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf, pow_abs] at h1
  have h4 : |y ^ 4| = y ^ 4 := abs_of_nonneg (by positivity)
  rw [h4] at h1
  have hpos := Real.exp_pos y
  have hneg := Real.exp_pos (-y)
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy] at h1; nlinarith
  · rw [abs_of_nonpos hy] at h1; nlinarith

theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
  have hm : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (1 / 2 : ℝ)
  nlinarith

/-- Fourth moment of a centred real Gaussian: `E t⁴ ≤ 96 v²` (exactly `3v²`). -/
theorem lintegral_pow_four_gaussianReal_le (v : ℝ≥0) :
    ∫⁻ t, ENNReal.ofReal (t ^ 4) ∂gaussianReal 0 v ≤ ENNReal.ofReal (96 * (v : ℝ) ^ 2) := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    rw [gaussianReal_zero_var, lintegral_dirac' _ (by fun_prop)]
    simp
  have hv' : 0 < (v : ℝ) := by positivity
  set l := (Real.sqrt v)⁻¹
  have hs := Real.sqrt_pos.mpr hv'
  have hl2 : (v : ℝ) * l ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt hv'.le, mul_inv_cancel₀ hv'.ne']
  have hpt : ∀ t : ℝ, ENNReal.ofReal (t ^ 4) ≤
      ENNReal.ofReal (24 * (v : ℝ) ^ 2) * ENNReal.ofReal (Real.exp (l * t)) +
        ENNReal.ofReal (24 * (v : ℝ) ^ 2) * ENNReal.ofReal (Real.exp ((-l) * t)) := by
    intro t
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := pow_four_le_exp (l * t)
    have ht : t ^ 4 = (v : ℝ) ^ 2 * (l * t) ^ 4 := by
      have : ((v : ℝ) * l ^ 2) ^ 2 = 1 := by rw [hl2]; norm_num
      calc t ^ 4 = ((v : ℝ) * l ^ 2) ^ 2 * t ^ 4 := by rw [this, one_mul]
        _ = _ := by ring
    rw [ht, neg_mul]
    have hv2 : 0 ≤ (v : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h hv2]
  calc ∫⁻ t, ENNReal.ofReal (t ^ 4) ∂gaussianReal 0 v
      ≤ ∫⁻ t, (ENNReal.ofReal (24 * (v : ℝ) ^ 2) * ENNReal.ofReal (Real.exp (l * t)) +
        ENNReal.ofReal (24 * (v : ℝ) ^ 2) * ENNReal.ofReal (Real.exp ((-l) * t)))
          ∂gaussianReal 0 v := lintegral_mono hpt
    _ = ENNReal.ofReal (24 * (v : ℝ) ^ 2) * ENNReal.ofReal (Real.exp (1 / 2)) +
        ENNReal.ofReal (24 * (v : ℝ) ^ 2) * ENNReal.ofReal (Real.exp (1 / 2)) := by
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
        lintegral_const_mul _ (by fun_prop), lintegral_exp_mul_gaussianReal,
        lintegral_exp_mul_gaussianReal, neg_sq, hl2]
    _ ≤ ENNReal.ofReal (96 * (v : ℝ) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := exp_half_le_two
      have hv2 : 0 ≤ (v : ℝ) ^ 2 := by positivity
      nlinarith

theorem lintegral_coord_four_le (p : Parameters) (j : p.GaussianCoordinate) :
    ∫⁻ z, ENNReal.ofReal (z j ^ 4) ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) ≤
      ENNReal.ofReal (96 * (p.gaussianCoordinateVariance j : ℝ) ^ 2) := by
  have hmp := measurePreserving_eval (fun i : p.GaussianCoordinate =>
    gaussianReal 0 (p.gaussianCoordinateVariance i)) j
  have h := hmp.lintegral_comp (f := fun t : ℝ => ENNReal.ofReal (t ^ 4)) (by fun_prop)
  change ∫⁻ z, ENNReal.ofReal (z j ^ 4)
    ∂Measure.pi (fun i => gaussianReal 0 (p.gaussianCoordinateVariance i)) ≤ _
  exact h.le.trans (lintegral_pow_four_gaussianReal_le _)

theorem norm_four_add_mul_I_le (a b : ℝ) :
    ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ^ 4 ≤ 2 * a ^ 4 + 2 * b ^ 4 := by
  have h : ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, mul_comm, Complex.normSq_add_mul_I]
  have : ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ^ 4 = (a ^ 2 + b ^ 2) ^ 2 := by
    rw [← h]; ring
  rw [this]; nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

theorem norm_four_sub_mul_I_le (a b : ℝ) :
    ‖(a : ℂ) - Complex.I * (b : ℂ)‖ ^ 4 ≤ 2 * a ^ 4 + 2 * b ^ 4 := by
  have e : (a : ℂ) - Complex.I * (b : ℂ) = (a : ℂ) + Complex.I * ((-b : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  have := norm_four_add_mul_I_le a (-b)
  have h4 : (-b) ^ 4 = b ^ 4 := by ring
  rw [h4] at this
  exact this

theorem lintegral_pair_coord_four_le (p : Parameters) (ja jb : p.GaussianCoordinate) {σ : ℝ}
    (ha : (p.gaussianCoordinateVariance ja : ℝ) = σ / 2)
    (hb : (p.gaussianCoordinateVariance jb : ℝ) = σ / 2) (g : (p.GaussianCoordinate → ℝ) → ℝ)
    (hg : ∀ z, g z ≤ 2 * z ja ^ 4 + 2 * z jb ^ 4) :
    ∫⁻ z, ENNReal.ofReal (g z)
      ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) ≤
      ENNReal.ofReal (96 * σ ^ 2) := by
  have h1 := lintegral_coord_four_le p ja
  have h2 := lintegral_coord_four_le p jb
  rw [ha] at h1; rw [hb] at h2
  calc ∫⁻ z, ENNReal.ofReal (g z) ∂(p.gaussianCoordinatesLaw : Measure _)
      ≤ ∫⁻ z, (ENNReal.ofReal 2 * ENNReal.ofReal (z ja ^ 4) +
          ENNReal.ofReal 2 * ENNReal.ofReal (z jb ^ 4))
          ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) := by
        refine lintegral_mono fun z => ?_
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hg z)
    _ = ENNReal.ofReal 2 * ∫⁻ z, ENNReal.ofReal (z ja ^ 4)
          ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) +
        ENNReal.ofReal 2 * ∫⁻ z, ENNReal.ofReal (z jb ^ 4)
          ∂(p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
          lintegral_const_mul _ (by fun_prop)]
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (96 * (σ / 2) ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal (96 * (σ / 2) ^ 2) := by gcongr
    _ = ENNReal.ofReal (96 * σ ^ 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1; ring

/-- **Fourth moment of an entry of the physical ring law:** `E|H_xy|⁴ ≤ 96 σ_xy²`,
`σ_xy = E|H_xy|²` (`entryVariance`). -/
theorem lintegral_entry_four_le {p : Parameters} (model : p.GaussianRingModel) (x y : p.Site) :
    ∫⁻ H, ENNReal.ofReal (‖H x y‖ ^ 4) ∂(model.law : Measure p.SiteMatrix) ≤
      ENNReal.ofReal (96 * p.entryVariance x y ^ 2) := by
  rw [model.law_eq_gaussianMatrixLaw]
  change ∫⁻ H, ENNReal.ofReal (‖H x y‖ ^ 4) ∂Measure.map p.gaussianReconstruction
    (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) ≤ _
  rw [lintegral_map (by fun_prop) p.measurable_gaussianReconstruction]
  by_cases hxy : x = y
  · subst hxy
    have e : ∀ z : p.GaussianCoordinate → ℝ,
        ‖p.gaussianReconstruction z x x‖ ^ 4 = z (.inl x) ^ 4 := by
      intro z
      simp only [Parameters.gaussianReconstruction, ite_true, Complex.norm_real, Real.norm_eq_abs]
      exact Even.pow_abs ⟨2, rfl⟩ _
    simp_rw [e]
    exact lintegral_coord_four_le p (.inl x)
  by_cases hlt : p.siteIndex x < p.siteIndex y
  · refine lintegral_pair_coord_four_le p (.inr (x, y, false)) (.inr (x, y, true))
      (by simp [Parameters.gaussianCoordinateVariance, hlt]; rfl)
      (by simp [Parameters.gaussianCoordinateVariance, hlt]; rfl) _ fun z => ?_
    simp only [Parameters.gaussianReconstruction, hxy, hlt, ite_false, ite_true]
    exact norm_four_add_mul_I_le _ _
  · have hne : p.siteIndex x ≠ p.siteIndex y := fun h => hxy (p.siteIndex_injective h)
    have hgt : p.siteIndex y < p.siteIndex x := by omega
    have hsy := p.entryVariance_symm x y
    refine lintegral_pair_coord_four_le p (.inr (y, x, false)) (.inr (y, x, true))
      (by simp [Parameters.gaussianCoordinateVariance, hgt, hsy]; rfl)
      (by simp [Parameters.gaussianCoordinateVariance, hgt, hsy]; rfl) _ fun z => ?_
    simp only [Parameters.gaussianReconstruction, hxy, hlt, ite_false]
    exact norm_four_sub_mul_I_le _ _

/-- Column variance sums are at most one (`c + 2b = 1`). -/
theorem sum_entryVariance_le_one (p : Parameters) (y : p.Site) :
    ∑ x, p.entryVariance x y ≤ 1 := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  set g : ZMod p.n → ℝ := fun k =>
    p.c / p.W * (if k = y.1 then 1 else 0) + p.b / p.W * (if k = y.1 - 1 then 1 else 0) +
      p.b / p.W * (if k = y.1 + 1 then 1 else 0) with hg
  have hpt : ∀ x : p.Site, p.entryVariance x y ≤ g x.1 := by
    intro x
    have hc := p.c_pos
    have hb := p.b_pos
    have h1 : 0 ≤ p.c / p.W := by positivity
    have h2 : 0 ≤ p.b / p.W := by positivity
    simp only [Parameters.entryVariance, hg]
    by_cases e1 : y.1 = x.1
    · rw [ite_eq_left e1, ite_eq_left e1.symm]
      split_ifs <;> linarith
    · rw [ite_eq_right e1]
      by_cases e2 : y.1 = x.1 + 1
      · have h3 : x.1 = y.1 - 1 := by rw [e2]; ring
        rw [ite_eq_left (Or.inl e2), ite_eq_left h3]
        split_ifs <;> linarith
      · by_cases e3 : y.1 = x.1 - 1
        · have h3 : x.1 = y.1 + 1 := by rw [e3]; ring
          rw [ite_eq_left (Or.inr e3), ite_eq_left h3]
          split_ifs <;> linarith
        · rw [ite_eq_right (by tauto)]
          split_ifs <;> linarith
  calc ∑ x, p.entryVariance x y ≤ ∑ x : p.Site, g x.1 := Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ k : ZMod p.n, ∑ _a : Fin p.W, g k := Fintype.sum_prod_type _
    _ = (p.W : ℝ) * (p.c / p.W + p.b / p.W + p.b / p.W) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        congr 1
        simp only [hg, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true, mul_one]
    _ = 1 := by
        field_simp
        unfold Parameters.c; ring

/-!
## The pair-column Frobenius mass
-/

section Column

variable {p : Parameters} {i : ZMod p.n}

/-- `F(H) = Σ_x Σ_{y ∈ S} |H_xy|²`, the squared Frobenius norm of the `2W` pair columns. -/
def pairColumnSq (i : ZMod p.n) (H : p.SiteMatrix) : ℝ :=
  ∑ k : p.Site × PairSite p i, ‖H k.1 k.2.1‖ ^ 2

theorem pairColumnSq_nonneg (H : p.SiteMatrix) : 0 ≤ pairColumnSq i H :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- `‖H_SS‖ + ‖H_RS‖ ≤ 2 F(H)^{1/2}`. -/
theorem pairRow_norm_le (H : p.SiteMatrix) :
    ‖pairBlock p i H‖ + ‖couplingBlock p i H‖ ≤ 2 * Real.sqrt (pairColumnSq i H) := by
  have h1 := l2_opNorm_le_frob (pairBlock p i H)
  have h2 := l2_opNorm_le_frob (couplingBlock p i H)
  set g : p.Site → ℝ := fun x => ∑ c : PairSite p i, ‖H x c.1‖ ^ 2 with hg
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x : p.Site => x.1 = i ∨ x.1 = i + 1) g
  have hF : pairColumnSq i H = ∑ x, g x := Fintype.sum_prod_type _
  have hP : (∑ r, ∑ c, ‖pairBlock p i H r c‖ ^ 2) = ∑ x : PairSite p i, g x.1 := rfl
  have hC : (∑ r, ∑ c, ‖couplingBlock p i H r c‖ ^ 2) = ∑ x : ExteriorSite p i, g x.1 := rfl
  have hgn : ∀ x, 0 ≤ g x := fun x => Finset.sum_nonneg fun _ _ => by positivity
  have hPn : 0 ≤ ∑ x : PairSite p i, g x.1 := Finset.sum_nonneg fun _ _ => hgn _
  have hCn : 0 ≤ ∑ x : ExteriorSite p i, g x.1 := Finset.sum_nonneg fun _ _ => hgn _
  rw [hP] at h1
  rw [hC] at h2
  have h1' : Real.sqrt (∑ x : PairSite p i, g x.1) ≤ Real.sqrt (pairColumnSq i H) :=
    Real.sqrt_le_sqrt (by rw [hF, ← hsplit]; linarith)
  have h2' : Real.sqrt (∑ x : ExteriorSite p i, g x.1) ≤ Real.sqrt (pairColumnSq i H) :=
    Real.sqrt_le_sqrt (by rw [hF, ← hsplit]; linarith)
  linarith

theorem measurable_entry_sq (x y : p.Site) :
    Measurable fun H : p.SiteMatrix => ENNReal.ofReal (‖H x y‖ ^ 2) :=
  (((measurable_pi_apply y).comp (measurable_pi_apply x)).norm.pow_const 2).ennreal_ofReal

theorem measurable_pairColumnSq : Measurable fun H : p.SiteMatrix => pairColumnSq i H :=
  Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k.2.1).comp (measurable_pi_apply k.1)).norm.pow_const 2

/-- **Second moment of the pair-column mass:** `E F² ≤ 96 (2W)²`. -/
theorem lintegral_pairColumnSq_sq_le (model : p.GaussianRingModel) :
    ∫⁻ H, ENNReal.ofReal (pairColumnSq i H ^ 2) ∂(model.law : Measure p.SiteMatrix) ≤
      ENNReal.ofReal (96 * (2 * p.W) ^ 2) := by
  set μ := (model.law : Measure p.SiteMatrix)
  set K := p.Site × PairSite p i
  set f : K → p.SiteMatrix → ℝ≥0∞ := fun k H => ENNReal.ofReal (‖H k.1 k.2.1‖ ^ 2) with hf
  set σ : K → ℝ := fun k => Real.sqrt 96 * p.entryVariance k.1 k.2.1 with hσ
  have hσn : ∀ k, 0 ≤ σ k := fun k => mul_nonneg (Real.sqrt_nonneg _) (p.entryVariance_nonneg _ _)
  have hfm : ∀ k, Measurable (f k) := fun k => measurable_entry_sq _ _
  have hexp : ∀ H : p.SiteMatrix, ENNReal.ofReal (pairColumnSq i H ^ 2) =
      ∑ k, ∑ l, f k H * f l H := by
    intro H
    unfold pairColumnSq
    rw [sq, Finset.sum_mul_sum, ENNReal.ofReal_sum_of_nonneg
      (fun k _ => Finset.sum_nonneg fun l _ => by positivity)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have hmom : ∀ k, (∫⁻ H, f k H ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (σ k) := by
    intro k
    have e : (∫⁻ H, f k H ^ (2 : ℝ) ∂μ) = ∫⁻ H, ENNReal.ofReal (‖H k.1 k.2.1‖ ^ 4) ∂μ := by
      refine lintegral_congr fun H => ?_
      rw [hf]
      simp only
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]
    rw [e]
    have h := lintegral_entry_four_le model k.1 k.2.1
    calc (∫⁻ H, ENNReal.ofReal (‖H k.1 k.2.1‖ ^ 4) ∂μ) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (96 * p.entryVariance k.1 k.2.1 ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h (by norm_num)
      _ = ENNReal.ofReal (σ k) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
            Real.sqrt_mul (by norm_num), Real.sqrt_sq (p.entryVariance_nonneg _ _)]
  have hpair : ∀ k l, (∫⁻ H, f k H * f l H ∂μ) ≤ ENNReal.ofReal (σ k) * ENNReal.ofReal (σ l) := by
    intro k l
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      (hfm k).aemeasurable (hfm l).aemeasurable
    exact hH.trans (mul_le_mul' (hmom k) (hmom l))
  have hsum : ∑ k, σ k ≤ Real.sqrt 96 * (2 * p.W) := by
    have e : ∑ k, σ k = Real.sqrt 96 * ∑ c : PairSite p i, ∑ x : p.Site, p.entryVariance x c.1 := by
      rw [hσ]
      simp only
      rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    rw [e]
    have hc : ∑ c : PairSite p i, ∑ x : p.Site, p.entryVariance x c.1 ≤ 2 * p.W := by
      calc _ ≤ ∑ _c : PairSite p i, (1 : ℝ) :=
            Finset.sum_le_sum fun c _ => sum_entryVariance_le_one p c.1
        _ = 2 * p.W := by
            rw [Finset.sum_const, Finset.card_univ, card_pairSite, nsmul_eq_mul, mul_one]
            push_cast; ring
    exact mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)
  calc ∫⁻ H, ENNReal.ofReal (pairColumnSq i H ^ 2) ∂μ
      = ∑ k, ∑ l, ∫⁻ H, f k H * f l H ∂μ := by
        simp_rw [hexp]
        rw [lintegral_finsetSum Finset.univ (f := fun k H => ∑ l, f k H * f l H) fun k _ =>
          Finset.measurable_sum _ fun l _ => (hfm k).mul (hfm l)]
        exact Finset.sum_congr rfl fun k _ =>
          lintegral_finsetSum Finset.univ (f := fun l H => f k H * f l H) fun l _ =>
            (hfm k).mul (hfm l)
    _ ≤ ∑ k, ∑ l, ENNReal.ofReal (σ k) * ENNReal.ofReal (σ l) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hpair k l
    _ = ENNReal.ofReal ((∑ k, σ k) ^ 2) := by
        rw [sq, Finset.sum_mul_sum, ENNReal.ofReal_sum_of_nonneg
          (fun k _ => Finset.sum_nonneg fun l _ => mul_nonneg (hσn k) (hσn l))]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (hσn k) (hσn l))]
        exact Finset.sum_congr rfl fun l _ => (ENNReal.ofReal_mul (hσn k)).symm
    _ ≤ ENNReal.ofReal (96 * (2 * p.W) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 : 0 ≤ ∑ k, σ k := Finset.sum_nonneg fun k _ => hσn k
        have h96 : Real.sqrt 96 ^ 2 = 96 := Real.sq_sqrt (by norm_num)
        calc (∑ k, σ k) ^ 2 ≤ (Real.sqrt 96 * (2 * p.W)) ^ 2 := pow_le_pow_left₀ h0 hsum 2
          _ = _ := by rw [mul_pow, h96]

end Column

/-!
## Markov and the pair density
-/

section Tail

variable {p : Parameters} {i : ZMod p.n}

/-- **Markov:** `P(F² ≥ W⁴/256) ≤ 98304/W²` under the physical law. -/
theorem law_pairColumnSq_tail_le (model : p.GaussianRingModel) :
    (model.law : Measure p.SiteMatrix)
        {H | ENNReal.ofReal ((p.W : ℝ) ^ 4 / 256) ≤ ENNReal.ofReal (pairColumnSq i H ^ 2)} ≤
      ENNReal.ofReal (98304 / (p.W : ℝ) ^ 2) := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hpos : (0 : ℝ) < (p.W : ℝ) ^ 4 / 256 := by positivity
  have hm : Measurable fun H : p.SiteMatrix => ENNReal.ofReal (pairColumnSq i H ^ 2) :=
    (measurable_pairColumnSq.pow_const 2).ennreal_ofReal
  refine (meas_ge_le_lintegral_div hm.aemeasurable (ENNReal.ofReal_pos.mpr hpos).ne'
    ENNReal.ofReal_ne_top).trans ?_
  refine (ENNReal.div_le_div_right (lintegral_pairColumnSq_sq_le model) _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos hpos]
  congr 1
  field_simp
  ring

/-- The pair law has density at most `n/2` with respect to the physical law. -/
theorem physicalPairMeasure_le (model : p.GaussianRingModel) (α : Fin p.N) (s : Set p.SiteMatrix) :
    physicalPairMeasure p model α i s ≤
      ENNReal.ofReal ((p.n : ℝ) / 2) * (model.law : Measure p.SiteMatrix) s := by
  rw [physicalPairMeasure, withDensity_apply', ← setLIntegral_const]
  refine lintegral_mono_ae (ae_restrict_of_ae ?_)
  filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  show (p.n : ℝ) / 2 * (physicalOrderedBlockMass p H α i +
      physicalOrderedBlockMass p H α (i + 1)) ≤ (p.n : ℝ) / 2
  have h := Finset.add_le_sum (f := fun k => physicalOrderedBlockMass p H α k)
    (fun k _ => physicalOrderedBlockMass_nonneg p H α k) (Finset.mem_univ i)
    (Finset.mem_univ (i + 1)) (self_ne_add_one p i)
  rw [hH α] at h
  have hn : (0 : ℝ) ≤ (p.n : ℝ) / 2 := by positivity
  nlinarith

end Tail

end RowTail

open RowTail

/-- **Pair-row norm tail** (`Assembly.PairRowNormTailStatement`), with `C = 49152 T` and
no hypothesis: `P♯_{α,S}{‖H_SS‖ + ‖H_RS‖ > W/2} ≤ C/W` for `n ≤ TW`. -/
theorem pairRowNormTail_holds : PairRowNormTailStatement := by
  intro b T
  refine ⟨49152 * T, fun p _ hnT model α i => ?_⟩
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hsub : {H : p.SiteMatrix | (p.W : ℝ) / 2 < ‖pairBlock p i H‖ + ‖couplingBlock p i H‖} ⊆
      {H | ENNReal.ofReal ((p.W : ℝ) ^ 4 / 256) ≤ ENNReal.ofReal (pairColumnSq i H ^ 2)} := by
    intro H hH
    simp only [Set.mem_ofPred_eq] at hH ⊢
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := pairRow_norm_le (i := i) H
    have h2 : (p.W : ℝ) / 4 < Real.sqrt (pairColumnSq i H) := by linarith
    have h3 : ((p.W : ℝ) / 4) ^ 2 < pairColumnSq i H :=
      (Real.lt_sqrt (by positivity)).mp h2
    have h4 : (((p.W : ℝ) / 4) ^ 2) ^ 2 < pairColumnSq i H ^ 2 :=
      pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
    have e : (p.W : ℝ) ^ 4 / 256 = (((p.W : ℝ) / 4) ^ 2) ^ 2 := by ring
    rw [e]; exact h4.le
  have hn : (0 : ℝ) ≤ (p.n : ℝ) / 2 := by positivity
  calc physicalPairMeasure p model α i
        {H | (p.W : ℝ) / 2 < ‖pairBlock p i H‖ + ‖couplingBlock p i H‖}
      ≤ ENNReal.ofReal ((p.n : ℝ) / 2) * (model.law : Measure p.SiteMatrix)
        {H | (p.W : ℝ) / 2 < ‖pairBlock p i H‖ + ‖couplingBlock p i H‖} :=
        physicalPairMeasure_le model α _
    _ ≤ ENNReal.ofReal ((p.n : ℝ) / 2) * ENNReal.ofReal (98304 / (p.W : ℝ) ^ 2) :=
        mul_le_mul' le_rfl ((measure_mono hsub).trans (law_pairColumnSq_tail_le model))
    _ = ENNReal.ofReal ((p.n : ℝ) / 2 * (98304 / (p.W : ℝ) ^ 2)) :=
        (ENNReal.ofReal_mul hn).symm
    _ ≤ ENNReal.ofReal (49152 * T / p.W) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : (p.n : ℝ) / 2 * (98304 / (p.W : ℝ) ^ 2) = 49152 * (p.n : ℝ) / p.W / p.W := by
          field_simp; ring
        rw [e, div_le_div_iff_of_pos_right hW]
        rw [div_le_iff₀ hW]
        nlinarith

end BlockBand.Angular.Assembly
