module

public import BlockBand.Center.PhysicalCenter

/-!
# Existence of the exact simultaneous splitting (`PcSplittingExists`)

Construction (every `p`, every `model`), `s = splitS p = min(c, b)`, `t = s/(2W)`:
`Ω = ℝ^{coordinates} × ∏_g PairMatrix_g`, `P = (⊗ N(0, σ_V)) ⊗ (⊗_g GUE_{2W}(t))`, where the
residual profile is `σ_V(x, y) = E|H_xy|² - Σ_g t 1{x, y ∈ S_g}` (`cspResProfile`); it is `≥ 0`
because each diagonal block lies in two pairs (`(c - s)/W ≥ 0`) and each bond in one
(`(b - s/2)/W ≥ 0`) (`csp_resProfile_nonneg`). `V` is the Hermitian reconstruction of the
coordinates, `G_g` the Hermitian part of the `g`-th pair coordinate (equal to it almost surely),
`ξ_g = (2W)⁻¹ Re Tr G_g`, `H = V + Σ_g embed(G_g)`.

* `csp_charFun_res`, `csp_charFun_embed`: characteristic functions of `V` and of `embed(G_g)`
  against the physical coordinate pairing (`exp(-Q_σ/2)` with the profile forms `cspVarForm`);
* `csp_map_eq`: `P.map H = model.law` (variances add: `σ_V + Σ_g σ_g = E|H_xy|²`; then the
  uniqueness `physicalGaussianRingLaw_unique`);
* **`pcSplittingExists_holds : PcSplittingExists`**: all four clauses of
  `SimultaneousSplitting.IsExact`.

Measure: the product law `P` above. No hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.Model.Construction
open scoped ENNReal NNReal ComplexConjugate

variable {p : Parameters}

/-!
## 1. Centered Gaussian Hermitian matrices with a variance profile
-/

/-- The covariance form of a centered Gaussian Hermitian matrix with independent entries of
variance profile `σ` (diagonal variance `σ_xx`, real and imaginary parts of the strict upper
entries of variance `σ_xy/2`), against the physical coordinate pairing. For `σ = E|H_xy|²` it is
`coordinateVariance` (`csp_varForm_entryVariance`). -/
def cspVarForm (σ : p.Site → p.Site → ℝ) (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) : ℝ :=
  (∑ x, σ x x * d x ^ 2) +
    ∑ x, ∑ y with p.siteIndex x < p.siteIndex y, (σ x y / 2) * (u x y ^ 2 + v x y ^ 2)

theorem csp_varForm_entryVariance (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    cspVarForm p.entryVariance d u v = p.coordinateVariance d u v := rfl

theorem csp_varForm_add (σ τ : p.Site → p.Site → ℝ) (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    cspVarForm (fun x y => σ x y + τ x y) d u v = cspVarForm σ d u v + cspVarForm τ d u v := by
  unfold cspVarForm
  simp only [add_mul, add_div, Finset.sum_add_distrib]
  ring

theorem csp_varForm_zero (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    cspVarForm (fun _ _ => (0 : ℝ)) d u v = 0 := by
  simp [cspVarForm]

theorem csp_varForm_sum {ι : Type*} (s : Finset ι) (σ : ι → p.Site → p.Site → ℝ)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    cspVarForm (fun x y => ∑ i ∈ s, σ i x y) d u v = ∑ i ∈ s, cspVarForm (σ i) d u v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using csp_varForm_zero d u v
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [csp_varForm_add (σ a) (fun x y => ∑ i ∈ s, σ i x y), ih]

/-- Variances of the independent real coordinates for the profile `σ`. -/
def cspCoordVar (σ : p.Site → p.Site → ℝ) : p.GaussianCoordinate → ℝ≥0
  | .inl x => Real.toNNReal (σ x x)
  | .inr (x, y, _) => if p.siteIndex x < p.siteIndex y then Real.toNNReal (σ x y / 2) else 0

theorem csp_coordVar_sum (σ : p.Site → p.Site → ℝ) (hσ : ∀ x y, 0 ≤ σ x y) (d : p.Site → ℝ)
    (u v : p.Site → p.Site → ℝ) :
    (∑ i, (cspCoordVar σ i : ℝ) * (p.gaussianCoordinateCoefficient d u v i) ^ 2) =
      cspVarForm σ d u v := by
  classical
  simp only [cspVarForm, Parameters.gaussianCoordinate_sum,
    Parameters.gaussianCoordinateCoefficient, cspCoordVar]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Real.coe_toNNReal _ (hσ x x)]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : p.siteIndex x < p.siteIndex y
    · simp only [h, ite_true, Bool.false_eq_true, ite_false]
      rw [Real.coe_toNNReal _ (div_nonneg (hσ x y) (by norm_num))]
      ring
    · simp [h]

/-- The product law of the real coordinates for the profile `σ`. -/
def cspCoordLaw (σ : p.Site → p.Site → ℝ) : Measure (p.GaussianCoordinate → ℝ) :=
  Measure.pi fun i => gaussianReal 0 (cspCoordVar σ i)

instance csp_isProb_coordLaw (σ : p.Site → p.Site → ℝ) : IsProbabilityMeasure (cspCoordLaw σ) := by
  unfold cspCoordLaw
  infer_instance

/-- **Characteristic function of the profile Gaussian** `V = recon(z)`, `z ~ cspCoordLaw σ`. -/
theorem csp_charFun_res (σ : p.Site → p.Site → ℝ) (hσ : ∀ x y, 0 ≤ σ x y) (d : p.Site → ℝ)
    (u v : p.Site → p.Site → ℝ) :
    ∫ z, Complex.exp (Complex.I * (p.coordinatePairing d u v (p.gaussianReconstruction z) : ℂ))
        ∂cspCoordLaw σ =
      Complex.exp (-(cspVarForm σ d u v : ℂ) / 2) := by
  simp_rw [p.gaussianReconstruction_coordinatePairing d u v]
  exact (Parameters.gaussianProduct_characteristic (cspCoordVar σ)
    (p.gaussianCoordinateCoefficient d u v)).trans
    (congrArg (fun t : ℝ => Complex.exp (-(t : ℂ) / 2)) (csp_coordVar_sum σ hσ d u v))

/-!
## 2. The embedded pair Gaussian
-/

/-- Variance profile of `embed(G_g)`, `G_g ~ GUE_{2W}(t)`: `t` on `S_g × S_g`, zero elsewhere. -/
def cspPairProfile (g : ZMod p.n) (t : ℝ) (x y : p.Site) : ℝ :=
  if (x.1 = g ∨ x.1 = g + 1) ∧ (y.1 = g ∨ y.1 = g + 1) then t else 0

/-- A sum over sites of a function vanishing off the pair `S_g` is a sum over `S_g`. -/
theorem csp_sum_pair (g : ZMod p.n) (f : p.Site → ℝ) (hf : ∀ x : p.Site, ¬ (x.1 = g ∨ x.1 = g + 1) →
    f x = 0) : ∑ x, f x = ∑ x : PairSite p g, f x.1 := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : p.Site => x.1 = g ∨ x.1 = g + 1) f]
  have h0 : ∑ x : {x : p.Site // ¬ (x.1 = g ∨ x.1 = g + 1)}, f x.1 = 0 :=
    Finset.sum_eq_zero fun x _ => hf x.1 x.2
  rw [h0, add_zero]

/-- Test coefficients of the pairing restricted to the pair. -/
def cspAlpha (g : ZMod p.n) (d : p.Site → ℝ) (u : p.Site → p.Site → ℝ) (x y : PairSite p g) : ℝ :=
  (if x = y then d x.1 else 0) + if p.siteIndex x.1 < p.siteIndex y.1 then u x.1 y.1 else 0

/-- Test coefficients of the imaginary parts on the pair. -/
def cspBeta (g : ZMod p.n) (v : p.Site → p.Site → ℝ) (x y : PairSite p g) : ℝ :=
  if p.siteIndex x.1 < p.siteIndex y.1 then v x.1 y.1 else 0

theorem csp_embedPair_apply (g : ZMod p.n) (G : PairMatrix p g) (x y : PairSite p g) :
    embedPair p g G x.1 y.1 = G x y := by
  simp [embedPair, x.2, y.2]

theorem csp_embedPair_apply_left (g : ZMod p.n) (G : PairMatrix p g) (x y : p.Site)
    (hx : ¬ (x.1 = g ∨ x.1 = g + 1)) : embedPair p g G x y = 0 := by
  simp [embedPair, hx]

theorem csp_embedPair_apply_right (g : ZMod p.n) (G : PairMatrix p g) (x y : p.Site)
    (hy : ¬ (y.1 = g ∨ y.1 = g + 1)) : embedPair p g G x y = 0 := by
  unfold embedPair
  split_ifs <;> rfl

theorem csp_pairing_embed (g : ZMod p.n) (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
    (G : PairMatrix p g) :
    p.coordinatePairing d u v (embedPair p g G) =
      BlockBand.Layers.rslTest (cspAlpha g d u) (cspBeta g v) G := by
  classical
  unfold Parameters.coordinatePairing BlockBand.Layers.rslTest
  simp only [Finset.sum_filter]
  rw [csp_sum_pair g (fun x => d x * (embedPair p g G x x).re)
      (fun x hx => by simp [csp_embedPair_apply_left g G x x hx]),
    csp_sum_pair g (fun x => ∑ y, if p.siteIndex x < p.siteIndex y then
      u x y * (embedPair p g G x y).re + v x y * (embedPair p g G x y).im else 0)
      (fun x hx => Finset.sum_eq_zero fun y _ => by simp [csp_embedPair_apply_left g G x y hx])]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [csp_sum_pair g (fun y => if p.siteIndex x.1 < p.siteIndex y then
      u x.1 y * (embedPair p g G x.1 y).re + v x.1 y * (embedPair p g G x.1 y).im else 0)
      (fun y hy => by simp [csp_embedPair_apply_right g G x.1 y hy])]
  simp only [csp_embedPair_apply, cspAlpha, cspBeta, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

theorem csp_Q_point (g : ZMod p.n) (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
    (x y : PairSite p g) :
    ((cspAlpha g d u x y + cspAlpha g d u y x) ^ 2 + (cspBeta g v x y - cspBeta g v y x) ^ 2) / 4 =
      (if x = y then d x.1 ^ 2 else 0) +
        ((if p.siteIndex x.1 < p.siteIndex y.1 then (u x.1 y.1 ^ 2 + v x.1 y.1 ^ 2) / 4 else 0) +
          if p.siteIndex y.1 < p.siteIndex x.1 then (u y.1 x.1 ^ 2 + v y.1 x.1 ^ 2) / 4 else 0) := by
  unfold cspAlpha cspBeta
  by_cases hxy : x = y
  · subst hxy
    simp only [ite_true, lt_irrefl, ite_false, add_zero, sub_self]
    ring
  · have hne : p.siteIndex x.1 ≠ p.siteIndex y.1 := fun h =>
      hxy (Subtype.ext (p.siteIndex_injective h))
    rcases lt_or_gt_of_ne hne with h | h
    · simp [hxy, Ne.symm hxy, h, not_lt.2 h.le]
    · simp [hxy, Ne.symm hxy, h, not_lt.2 h.le]

theorem csp_Q_embed (g : ZMod p.n) (t : ℝ) (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    t * BlockBand.Layers.rslQ (cspAlpha g d u) (cspBeta g v) =
      cspVarForm (cspPairProfile g t) d u v := by
  classical
  unfold BlockBand.Layers.rslQ cspVarForm
  simp only [csp_Q_point, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hswap : ∑ x : PairSite p g, ∑ y : PairSite p g,
      (if p.siteIndex y.1 < p.siteIndex x.1 then (u y.1 x.1 ^ 2 + v y.1 x.1 ^ 2) / 4 else 0) =
      ∑ x : PairSite p g, ∑ y : PairSite p g,
        (if p.siteIndex x.1 < p.siteIndex y.1 then (u x.1 y.1 ^ 2 + v x.1 y.1 ^ 2) / 4 else 0) :=
    Finset.sum_comm
  rw [hswap]
  simp only [Finset.sum_filter]
  rw [csp_sum_pair g (fun x => cspPairProfile g t x x * d x ^ 2)
      (fun x hx => by simp [cspPairProfile, hx]),
    csp_sum_pair g (fun x => ∑ y, if p.siteIndex x < p.siteIndex y then
      cspPairProfile g t x y / 2 * (u x y ^ 2 + v x y ^ 2) else 0)
      (fun x hx => Finset.sum_eq_zero fun y _ => by simp [cspPairProfile, hx])]
  have hin : ∀ x : PairSite p g, ∑ y, (if p.siteIndex x.1 < p.siteIndex y then
      cspPairProfile g t x.1 y / 2 * (u x.1 y ^ 2 + v x.1 y ^ 2) else 0) =
      ∑ y : PairSite p g, (if p.siteIndex x.1 < p.siteIndex y.1 then
        t / 2 * (u x.1 y.1 ^ 2 + v x.1 y.1 ^ 2) else 0) := by
    intro x
    rw [csp_sum_pair g _ (fun y hy => by simp [cspPairProfile, hy])]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [cspPairProfile, x.2, y.2]
  simp only [hin]
  have hd : ∀ x : PairSite p g, cspPairProfile g t x.1 x.1 = t := fun x => by
    simp [cspPairProfile, x.2]
  simp only [hd]
  rw [mul_add, Finset.mul_sum]
  congr 1
  rw [← two_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

/-- **Characteristic function of `embed(G)`, `G ~ GUE_{2W}(t)`**, against the physical pairing. -/
theorem csp_charFun_embed (g : ZMod p.n) (t : ℝ≥0) (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    ∫ G, Complex.exp (Complex.I * (p.coordinatePairing d u v (embedPair p g G) : ℂ))
        ∂gueMeasure (PairSite p g) t =
      Complex.exp (-(cspVarForm (cspPairProfile g (t : ℝ)) d u v : ℂ) / 2) := by
  simp_rw [csp_pairing_embed g d u v]
  rw [BlockBand.Layers.rsl_charFun_gue, csp_Q_embed]

/-!
## 3. The residual profile is nonnegative
-/

variable (p) in
/-- The pair entry variance `t = s/(2W)`, `s = splitS p`. -/
def cspT : ℝ := (pairTime p (splitS p) : ℝ)

theorem csp_T_eq : cspT p = splitS p / (2 * (p.W : ℝ)) := by
  unfold cspT pairTime
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  exact Real.coe_toNNReal _ (div_nonneg ctr_splitS_pos.le (by positivity))

variable (p) in
/-- The residual variance profile `σ_V(x, y) = E|H_xy|² - Σ_g t 1{x, y ∈ S_g}`. -/
def cspResProfile (x y : p.Site) : ℝ :=
  p.entryVariance x y - ∑ g, cspPairProfile g (cspT p) x y

theorem csp_sum_profile_eq (x y : p.Site) :
    ∑ g, cspPairProfile g (cspT p) x y =
      ((Finset.univ.filter fun g : ZMod p.n =>
        (x.1 = g ∨ x.1 = g + 1) ∧ (y.1 = g ∨ y.1 = g + 1)).card : ℝ) * cspT p := by
  classical
  unfold cspPairProfile
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem csp_adj_pair {k g : ZMod p.n} (h : (k = g ∨ k = g + 1) ∧ (k + 1 = g ∨ k + 1 = g + 1)) :
    g = k := by
  rcases h with ⟨h1 | h1, h2⟩
  · exact h1.symm
  · exfalso
    rcases h2 with h2 | h2
    · apply BlockBand.Layers.rng_add_two_ne p g
      rw [← h1, h2]
    · apply BlockBand.Layers.rng_add_one_ne p g
      rw [← h1]
      exact add_right_cancel h2

theorem csp_T_nonneg : 0 ≤ cspT p := by
  rw [csp_T_eq]
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  exact div_nonneg ctr_splitS_pos.le (by positivity)

/-- **Covariance positivity**: every diagonal block lies in two pairs and every
bond in one, so `Σ_g t 1{x, y ∈ S_g} ≤ E|H_xy|²` since `2t = s/W ≤ c/W`, `t = s/(2W) ≤ b/W`. -/
theorem csp_resProfile_nonneg (x y : p.Site) : 0 ≤ cspResProfile p x y := by
  classical
  unfold cspResProfile
  rw [sub_nonneg, csp_sum_profile_eq]
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hT := csp_T_nonneg (p := p)
  have hsc : splitS p ≤ p.c := min_le_left _ _
  have hsb : splitS p ≤ p.b := min_le_right _ _
  set P : ZMod p.n → Prop := fun g => (x.1 = g ∨ x.1 = g + 1) ∧ (y.1 = g ∨ y.1 = g + 1) with hP
  unfold Parameters.entryVariance
  by_cases h1 : y.1 = x.1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
    have hsub : Finset.univ.filter P ⊆ {x.1, x.1 - 1} := by
      intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP] at hg
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hg.1 with h | h
      · exact Or.inl h.symm
      · right; rw [h]; ring
    have hcard : ((Finset.univ.filter P).card : ℝ) ≤ 2 := by
      have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      simp only [Finset.card_singleton] at this
      exact_mod_cast this
    calc ((Finset.univ.filter P).card : ℝ) * cspT p ≤ 2 * cspT p :=
          mul_le_mul_of_nonneg_right hcard hT
      _ = splitS p / p.W := by rw [csp_T_eq]; field_simp
      _ ≤ p.c / p.W := div_le_div_of_nonneg_right hsc hW.le
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
  by_cases h2 : y.1 = x.1 + 1 ∨ y.1 = x.1 - 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
    have hsub : Finset.univ.filter P ⊆ {if y.1 = x.1 + 1 then x.1 else y.1} := by
      intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP] at hg
      simp only [Finset.mem_singleton]
      by_cases h3 : y.1 = x.1 + 1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]
        rw [h3] at hg
        exact csp_adj_pair hg
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h3)]
        have hx : x.1 = y.1 + 1 := by
          rcases h2 with h | h
          · exact absurd h h3
          · rw [h]; ring
        rw [hx] at hg
        exact csp_adj_pair ⟨hg.2, hg.1⟩
    have hcard : ((Finset.univ.filter P).card : ℝ) ≤ 1 := by
      have := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at this
      exact_mod_cast this
    calc ((Finset.univ.filter P).card : ℝ) * cspT p ≤ 1 * cspT p :=
          mul_le_mul_of_nonneg_right hcard hT
      _ = splitS p / (2 * p.W) := by rw [csp_T_eq, one_mul]
      _ ≤ p.b / p.W := by
        rw [div_le_div_iff₀ (by positivity) hW]
        nlinarith [ctr_splitS_pos (p := p), p.b_pos]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
    have hempty : Finset.univ.filter P = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun g _ hg => ?_
      rcases hg with ⟨hx | hx, hy | hy⟩
      · exact h1 (hy.trans hx.symm)
      · exact h2 (Or.inl (by rw [hy, hx]))
      · exact h2 (Or.inr (by rw [hy, hx]; ring))
      · exact h1 (hy.trans hx.symm)
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]

/-!
## 4. The product space and the assembled matrix
-/

/-- Hermitian part `(M + Mᴴ)/2`; it is the identity on Hermitian matrices, hence almost surely
under `GUE`, and makes `ξ_g` real at every sample point. -/
def cspHerm {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := (2⁻¹ : ℂ) • (M + Mᴴ)

theorem csp_herm_isHermitian {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : (cspHerm M).IsHermitian := by
  unfold cspHerm
  change ((2⁻¹ : ℂ) • (M + Mᴴ))ᴴ = _
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
    add_comm]
  congr 1
  simp

theorem csp_herm_of_isHermitian {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    cspHerm M = M := by
  unfold cspHerm
  rw [hM.eq]
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem csp_continuous_herm {ι : Type*} [Fintype ι] : Continuous (cspHerm (ι := ι)) := by
  have h : Continuous (fun M : Matrix ι ι ℂ => Mᴴ) := continuous_id.matrix_conjTranspose
  unfold cspHerm
  exact (continuous_id.add h).const_smul (2⁻¹ : ℂ)

theorem csp_measurable_herm {ι : Type*} [Fintype ι] : Measurable (cspHerm (ι := ι)) :=
  csp_continuous_herm.measurable

theorem csp_map_herm_gue {ι : Type} [Fintype ι] (t : ℝ≥0) :
    (gueMeasure ι t).map cspHerm = gueMeasure ι t := by
  have hae : cspHerm =ᵐ[gueMeasure ι t] id := by
    filter_upwards [ctr_ae_gue_isHermitian t] with M hM
    exact csp_herm_of_isHermitian hM
  rw [Measure.map_congr hae, Measure.map_id]

variable (p) in
/-- The sample space: real coordinates of `V` and one pair matrix per edge. -/
abbrev CspOmega := (p.GaussianCoordinate → ℝ) × (∀ g : ZMod p.n, PairMatrix p g)

variable (p) in
/-- Independent pair Gaussians `GUE_{2W}(s/(2W))`, one per edge. -/
def cspPairLaw : Measure (∀ g : ZMod p.n, PairMatrix p g) :=
  Measure.pi fun g => gueMeasure (PairSite p g) (pairTime p (splitS p))

instance csp_isProb_pairLaw : IsProbabilityMeasure (cspPairLaw p) := by
  unfold cspPairLaw
  infer_instance

variable (p) in
/-- The product law of `(V, (G_g)_g)`. -/
def cspP : Measure (CspOmega p) := (cspCoordLaw (cspResProfile p)).prod (cspPairLaw p)

instance csp_isProb_P : IsProbabilityMeasure (cspP p) := by
  unfold cspP
  infer_instance

/-- `G_g`: the Hermitian part of the `g`-th pair coordinate. -/
def cspG (g : ZMod p.n) (ω : CspOmega p) : PairMatrix p g := cspHerm (ω.2 g)

/-- `ξ_g = (2W)⁻¹ Re Tr G_g` (the trace is real). -/
def cspXi (g : ZMod p.n) (ω : CspOmega p) : ℝ :=
  (((Fintype.card (PairSite p g) : ℂ))⁻¹ * (cspG g ω).trace).re

/-- `H = V + Σ_g embed(G_g)`. -/
def cspH (ω : CspOmega p) : p.SiteMatrix :=
  p.gaussianReconstruction ω.1 + ∑ g, embedPair p g (cspG g ω)

theorem csp_measurable_G (g : ZMod p.n) : Measurable (cspG (p := p) g) :=
  csp_measurable_herm.comp ((measurable_pi_apply g).comp measurable_snd)

theorem csp_measurable_Xi (g : ZMod p.n) : Measurable (cspXi (p := p) g) := by
  have hc : Continuous (fun M : PairMatrix p g =>
      (((Fintype.card (PairSite p g) : ℂ))⁻¹ * M.trace).re) :=
    Complex.continuous_re.comp (continuous_const.mul continuous_id.matrix_trace)
  exact hc.measurable.comp (csp_measurable_G g)

theorem csp_measurable_H : Measurable (cspH (p := p)) := by
  have h1 : Measurable (fun ω : CspOmega p => p.gaussianReconstruction ω.1) :=
    p.measurable_gaussianReconstruction.comp measurable_fst
  have h2 := pc_measurable_sum_embed (ι := CspOmega p) Finset.univ (fun ω h => cspG h ω)
    (fun h => csp_measurable_G h)
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  simp only [cspH, Matrix.add_apply]
  exact (BlockBand.Layers.pg_entry h1 x y).add (BlockBand.Layers.pg_entry h2 x y)

theorem csp_H_isHermitian (ω : CspOmega p) : (cspH ω).IsHermitian := by
  unfold cspH
  refine (p.gaussianReconstruction_isHermitian ω.1).add ?_
  change (∑ g, embedPair p g (cspG g ω))ᴴ = _
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [ctr_embedPair_conjTranspose]
  congr 1
  exact (csp_herm_isHermitian (ω.2 g)).eq

theorem csp_H_sub (ω : CspOmega p) :
    cspH ω - ∑ g, embedPair p g (cspG g ω) = p.gaussianReconstruction ω.1 := by
  unfold cspH
  rw [add_sub_cancel_right]

/-!
## 5. The law of `H`
-/

theorem csp_pairing_add (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) (A B : p.SiteMatrix) :
    p.coordinatePairing d u v (A + B) = p.coordinatePairing d u v A + p.coordinatePairing d u v B := by
  unfold Parameters.coordinatePairing
  simp only [Matrix.add_apply, Complex.add_re, Complex.add_im, mul_add, Finset.sum_add_distrib]
  ring

theorem csp_pairing_zero (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    p.coordinatePairing d u v 0 = 0 := by
  simp [Parameters.coordinatePairing]

theorem csp_pairing_sum {ι : Type*} (s : Finset ι) (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
    (A : ι → p.SiteMatrix) :
    p.coordinatePairing d u v (∑ i ∈ s, A i) = ∑ i ∈ s, p.coordinatePairing d u v (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using csp_pairing_zero d u v
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, csp_pairing_add, ih]

theorem csp_continuous_pairing (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    Continuous (p.coordinatePairing d u v) := by
  unfold Parameters.coordinatePairing
  fun_prop

/-- **Characteristic function of `H = V + Σ_g embed(G_g)`** = that of the model. -/
theorem csp_charFun_H (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    ∫ ω, Complex.exp (Complex.I * (p.coordinatePairing d u v (cspH ω) : ℂ)) ∂cspP p =
      Complex.exp (-(p.coordinateVariance d u v : ℂ) / 2) := by
  have hpt : ∀ ω : CspOmega p, Complex.exp (Complex.I * (p.coordinatePairing d u v (cspH ω) : ℂ)) =
      Complex.exp (Complex.I * (p.coordinatePairing d u v (p.gaussianReconstruction ω.1) : ℂ)) *
        ∏ g, Complex.exp (Complex.I *
          (p.coordinatePairing d u v (embedPair p g (cspHerm (ω.2 g))) : ℂ)) := by
    intro ω
    rw [cspH, csp_pairing_add, csp_pairing_sum, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    push_cast
    rw [mul_add, Finset.mul_sum]
    rfl
  simp_rw [hpt]
  unfold cspP cspPairLaw
  rw [integral_prod_mul (f := fun z : p.GaussianCoordinate → ℝ =>
      Complex.exp (Complex.I * (p.coordinatePairing d u v (p.gaussianReconstruction z) : ℂ)))
    (g := fun x : (∀ g : ZMod p.n, PairMatrix p g) => ∏ g, Complex.exp (Complex.I *
          (p.coordinatePairing d u v (embedPair p g (cspHerm (x g))) : ℂ))),
    integral_fintype_prod_eq_prod (fun g (M : PairMatrix p g) => Complex.exp (Complex.I *
          (p.coordinatePairing d u v (embedPair p g (cspHerm M)) : ℂ)))]
  have hfac : ∀ g : ZMod p.n, ∫ M, Complex.exp (Complex.I *
      (p.coordinatePairing d u v (embedPair p g (cspHerm M)) : ℂ))
        ∂gueMeasure (PairSite p g) (pairTime p (splitS p)) =
      Complex.exp (-(cspVarForm (cspPairProfile g (cspT p)) d u v : ℂ) / 2) := by
    intro g
    rw [show cspT p = ((pairTime p (splitS p) : ℝ≥0) : ℝ) from rfl,
      ← csp_charFun_embed g (pairTime p (splitS p)) d u v]
    refine integral_congr_ae ?_
    filter_upwards [ctr_ae_gue_isHermitian (ι := PairSite p g) (pairTime p (splitS p))] with M hM
    rw [csp_herm_of_isHermitian hM]
  simp only [hfac]
  rw [csp_charFun_res (cspResProfile p) csp_resProfile_nonneg, ← Complex.exp_sum,
    ← Complex.exp_add]
  congr 1
  have hsum : p.coordinateVariance d u v = cspVarForm (cspResProfile p) d u v +
      ∑ g, cspVarForm (cspPairProfile g (cspT p)) d u v := by
    rw [← csp_varForm_sum, ← csp_varForm_add, ← csp_varForm_entryVariance]
    congr 1
    funext x y
    unfold cspResProfile
    ring
  rw [hsum]
  push_cast
  simp only [neg_div, add_div, Finset.sum_div, Finset.sum_neg_distrib, neg_add]

theorem csp_isProb_map : IsProbabilityMeasure ((cspP p).map cspH) :=
  (Measure.isProbabilityMeasure_map_iff csp_measurable_H.aemeasurable).mpr inferInstance

variable (p) in
/-- The assembled law as a physical model. -/
def cspModel : p.GaussianRingModel where
  law := ⟨(cspP p).map cspH, csp_isProb_map⟩
  isPhysical := by
    refine ⟨?_, fun d u v => ?_⟩
    · change ∀ᵐ H ∂(cspP p).map cspH, H.IsHermitian
      rw [ae_map_iff csp_measurable_H.aemeasurable ctr_measurableSet_hermitian]
      exact Filter.Eventually.of_forall csp_H_isHermitian
    · change ∫ H, _ ∂(cspP p).map cspH = _
      have hm : Measurable (fun H : p.SiteMatrix =>
          Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))) := by
        have := (csp_continuous_pairing (p := p) d u v)
        exact (by fun_prop : Continuous (fun H : p.SiteMatrix =>
          Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ)))).measurable
      rw [integral_map csp_measurable_H.aemeasurable hm.aestronglyMeasurable]
      exact csp_charFun_H d u v

/-- **Law identification** `P.map H = model.law`. -/
theorem csp_map_eq (model : p.GaussianRingModel) :
    (cspP p).map cspH = (model.law : Measure p.SiteMatrix) := by
  have h := Parameters.physicalGaussianRingLaw_unique (cspModel p) model
  exact congrArg (fun m : ProbabilityMeasure p.SiteMatrix => (m : Measure p.SiteMatrix)) h

/-!
## 6. The exact simultaneous splitting
-/

theorem csp_trace_im {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    M.trace.im = 0 := by
  unfold Matrix.trace
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  exact Complex.conj_eq_iff_im.mp (hM.apply x x)

/-- `G = G⁰ + ξ I` with the real `ξ = d⁻¹ Re Tr G`, for Hermitian `G`. -/
theorem csp_decomp {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    tracelessPart M + ((((((Fintype.card ι : ℂ))⁻¹ * M.trace).re : ℝ) : ℂ)) • (1 : Matrix ι ι ℂ) =
      M := by
  have hz : (((((Fintype.card ι : ℂ))⁻¹ * M.trace).re : ℝ) : ℂ) =
      ((Fintype.card ι : ℂ))⁻¹ * M.trace := by
    apply Complex.ext
    · simp
    · rw [Complex.ofReal_im, Complex.mul_im, csp_trace_im hM]
      simp
  rw [hz]
  unfold tracelessPart
  exact sub_add_cancel _ _

theorem csp_continuous_traceless {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (tracelessPart (ι := ι)) := by
  unfold tracelessPart
  exact continuous_id.sub ((continuous_const.mul continuous_id.matrix_trace).smul continuous_const)

/-- The extension `(Ω, P, H)` of the simultaneous splitting. -/
def cspExtension (model : p.GaussianRingModel) : PairExtension p model where
  Ω := CspOmega p
  P := cspP p
  Hm := cspH
  measurable_Hm := csp_measurable_H
  map_eq := csp_map_eq model

/-- The simultaneous splitting `H = V + Σ_g (G_g⁰ + ξ_g I_{S_g})`. -/
def cspSplitting (model : p.GaussianRingModel) : SimultaneousSplitting p model where
  X := cspExtension model
  G := fun g => cspG g
  ξ := fun g => cspXi g
  measurable_G := fun g => csp_measurable_G g
  measurable_ξ := fun g => csp_measurable_Xi g

/-- All four law clauses of the simultaneous splitting hold for `cspSplitting`. -/
theorem csp_isExact (model : p.GaussianRingModel) : (cspSplitting model).IsExact := by
  have hsnd : (cspP p).map Prod.snd = cspPairLaw p :=
    (measurePreserving_snd (μ := cspCoordLaw (cspResProfile p)) (ν := cspPairLaw p)).map_eq
  have hev : ∀ g : ZMod p.n, (cspPairLaw p).map (fun x => x g) =
      gueMeasure (PairSite p g) (pairTime p (splitS p)) := fun g =>
    (measurePreserving_eval (fun g => gueMeasure (PairSite p g) (pairTime p (splitS p))) g).map_eq
  refine ⟨fun g => ?_, fun g ω => ?_, ?_, ?_⟩
  · refine ⟨(csp_measurable_G g).aemeasurable, ?_⟩
    change (cspP p).map (cspHerm ∘ (fun x => x g) ∘ Prod.snd) = _
    rw [← Measure.map_map csp_measurable_herm ((measurable_pi_apply g).comp measurable_snd),
      ← Measure.map_map (measurable_pi_apply g) measurable_snd, hsnd, hev g, csp_map_herm_gue]
  · exact csp_decomp (csp_herm_isHermitian _)
  · set F : ∀ g : ZMod p.n, PairMatrix p g → PairMatrix p g × ℝ := fun g M =>
      (tracelessPart (cspHerm M), (((Fintype.card (PairSite p g) : ℂ))⁻¹ * (cspHerm M).trace).re)
      with hFdef
    have hF : ∀ g, Measurable (F g) := by
      intro g
      have h1 : Continuous (fun M : PairMatrix p g => tracelessPart (cspHerm M)) :=
        csp_continuous_traceless.comp csp_continuous_herm
      have h2 : Continuous (fun M : PairMatrix p g =>
          (((Fintype.card (PairSite p g) : ℂ))⁻¹ * (cspHerm M).trace).re) :=
        Complex.continuous_re.comp (continuous_const.mul csp_continuous_herm.matrix_trace)
      exact (h1.prodMk h2).measurable
    change iIndepFun (fun g ω => F g ((ω : CspOmega p).2 g)) (cspP p)
    refine (iIndepFun_iff_map_fun_eq_pi_map (f := fun g (ω : CspOmega p) => F g (ω.2 g))
      (fun g => ((hF g).comp ((measurable_pi_apply g).comp measurable_snd)).aemeasurable)).mpr ?_
    have hL : (cspP p).map (fun ω : CspOmega p => fun g => F g (ω.2 g)) =
        Measure.pi (fun g => (gueMeasure (PairSite p g) (pairTime p (splitS p))).map (F g)) := by
      change (cspP p).map ((fun x g => F g (x g)) ∘ Prod.snd) = _
      have hm : Measurable (fun x : (∀ g : ZMod p.n, PairMatrix p g) => fun g => F g (x g)) :=
        measurable_pi_iff.mpr fun g => (hF g).comp (measurable_pi_apply g)
      rw [← Measure.map_map hm measurable_snd, hsnd]
      exact Measure.pi_map_pi (fun g => (hF g).aemeasurable)
    rw [hL]
    congr 1
    funext g
    change _ = (cspP p).map (F g ∘ (fun x => x g) ∘ Prod.snd)
    rw [← Measure.map_map (hF g) ((measurable_pi_apply g).comp measurable_snd),
      ← Measure.map_map (measurable_pi_apply g) measurable_snd, hsnd, hev g]
  · have h1 : (fun ω : CspOmega p => cspH ω - ∑ g, embedPair p g (cspG g ω)) =
        fun ω => p.gaussianReconstruction ω.1 := funext csp_H_sub
    change IndepFun (fun ω : CspOmega p => cspH ω - ∑ g, embedPair p g (cspG g ω))
      (fun ω g => cspG g ω) (cspP p)
    rw [h1]
    exact indepFun_prod (μ := cspCoordLaw (cspResProfile p)) (ν := cspPairLaw p)
      (X := p.gaussianReconstruction) (Y := fun x g => cspHerm (x g))
      p.measurable_gaussianReconstruction
      (measurable_pi_iff.mpr fun g => csp_measurable_herm.comp (measurable_pi_apply g))

/-- **`PcSplittingExists`** (the simultaneous splitting): for every parameter
set and model there is an exact simultaneous splitting. -/
theorem pcSplittingExists_holds : PcSplittingExists :=
  fun _ model => ⟨cspSplitting model, csp_isExact model⟩

end BlockBand.Center
