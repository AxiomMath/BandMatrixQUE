module

public import BlockBand.Endpoints.Poisson.SequentialCollars
public import BlockBand.Model.Construction.GaussianCharacteristic

/-!
# Sequential collar removal: the coordinate prior is the physical law

The ring matrix assembled from independent Gaussian block and bond coordinates has the law of
the physical ring model.

* `coordinatePairing_ringMatrix`, `coordinateVariance_split`: for `n ≥ 4` the pairing and
  variance split over blocks and bonds (`upper_sum_regroup`).
* `ringCoordLaw_charFun` + `ringMatrix_isHermitian` give `coordinatePriorIsPhysical`.
* `ringCoordsOf` (left inverse of `ringMatrix`), `hasLaw_ringCoordsOf`: under `model.law`,
  `ringCoordsOf H` has law `ringCoordLaw` and `H = ringMatrix (ringCoordsOf H)` a.s.
* `sequentialCollars_locked`: the distributional clauses of items (i) and (iii) of the
  sequential-collars lemma transported to `model.law`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample)
open BlockBand.Internal.Contracts.Layers (ginibreMeasure pathLaw)
open scoped NNReal

section CharFun

/-- Splitting a double sum over `Fin W` into the diagonal and the strict upper triangle. -/
theorem sum_sum_eq_diag_add_upper {W : ℕ} (f : Fin W → Fin W → ℝ) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ a, ∑ b, if a < b then f a b + f b a else 0 := by
  have h1 : ∀ a, ∑ b, f a b = f a a + ∑ b, ((if a < b then f a b else 0) +
      (if b < a then f a b else 0)) := by
    intro a
    have hpt : ∀ b, f a b = (if a = b then f a b else 0) +
        ((if a < b then f a b else 0) + (if b < a then f a b else 0)) := by
      intro b
      rcases lt_trichotomy a b with h | h | h
      · simp [h, ne_of_lt h, not_lt.mpr h.le]
      · subst h; simp
      · simp [h, (ne_of_lt h).symm, not_lt.mpr h.le]
    rw [Finset.sum_congr rfl fun b _ => hpt b, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  simp_rw [h1, Finset.sum_add_distrib]
  congr 1
  have hswap : ∑ a, ∑ b, (if b < a then f a b else 0) =
      ∑ a, ∑ b, (if a < b then f b a else 0) := Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

open BlockBand.SourceProcess (circularBrownianCoordinates commonCircularIncrementLaw)

/-- Measurability of the circular coordinate map. -/
theorem measurable_circ {ι : Type*} :
    Measurable (circularBrownianCoordinates (ι := ι)) :=
  measurable_pi_iff.mpr fun u => by
    unfold circularBrownianCoordinates
    exact ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).add
      ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).mul measurable_const)).div_const _

/-- Measurability of the GUE sample map. -/
theorem measurable_gueSample {ι : Type*} (t : ℝ≥0) : Measurable (gueSample (ι := ι) t) :=
  Measurable.of_eval_matrix _ fun a b => by
    simp only [gueSample, Matrix.of_apply]
    exact measurable_const.mul ((measurable_pi_apply _).add
      (continuous_star.measurable.comp (measurable_pi_apply _)))

/-- Real part of a GUE sample entry in the real coordinates. -/
theorem gueSample_circ_re {W : ℕ} (t : ℝ≥0) (r : (Fin W × Fin W) × Fin 2 → ℝ) (a b : Fin W) :
    (gueSample t (circularBrownianCoordinates r) a b).re =
      Real.sqrt t / 2 * (r ((a, b), 0) + r ((b, a), 0)) := by
  have h2 : Real.sqrt ((t : ℝ) / 2) = Real.sqrt t / Real.sqrt 2 := Real.sqrt_div' _ (by norm_num)
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [gueSample, circularBrownianCoordinates, Matrix.of_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.conj_re,
    Complex.conj_im, Complex.div_re, Complex.div_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.normSq_ofReal, zero_mul, mul_zero, sub_zero, add_zero, mul_one, zero_add]
  rw [h2]
  field_simp
  rw [show Real.sqrt 2 ^ 3 = Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt 2) by ring, hs]
  ring

/-- Imaginary part of a GUE sample entry in the real coordinates. -/
theorem gueSample_circ_im {W : ℕ} (t : ℝ≥0) (r : (Fin W × Fin W) × Fin 2 → ℝ) (a b : Fin W) :
    (gueSample t (circularBrownianCoordinates r) a b).im =
      Real.sqrt t / 2 * (r ((a, b), 1) - r ((b, a), 1)) := by
  have h2 : Real.sqrt ((t : ℝ) / 2) = Real.sqrt t / Real.sqrt 2 := Real.sqrt_div' _ (by norm_num)
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [gueSample, circularBrownianCoordinates, Matrix.of_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.conj_re,
    Complex.conj_im, Complex.div_re, Complex.div_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.normSq_ofReal, zero_mul, mul_zero, sub_zero, add_zero, mul_one, zero_add]
  rw [h2]
  field_simp
  rw [show Real.sqrt 2 ^ 3 = Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt 2) by ring, hs]
  ring

/-- The real linear form of a GUE block entering `coordinatePairing`. -/
def gueForm {W : ℕ} (d : Fin W → ℝ) (u v : Fin W → Fin W → ℝ) (A : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ∑ a, d a * (A a a).re + ∑ a, ∑ b, if a < b then u a b * (A a b).re + v a b * (A a b).im else 0

/-- Matrix entries are continuous. -/
theorem continuous_entry {ι : Type*} (a b : ι) :
    Continuous fun A : Matrix ι ι ℂ => A a b :=
  (continuous_apply b).comp (continuous_apply a)

/-- `gueForm` is continuous. -/
theorem continuous_gueForm {W : ℕ} (d : Fin W → ℝ) (u v : Fin W → Fin W → ℝ) :
    Continuous (gueForm d u v) := by
  unfold gueForm
  refine (continuous_finsetSum _ fun a _ => continuous_const.mul
    (Complex.continuous_re.comp (continuous_entry a a))).add
    (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_)
  split_ifs
  · exact (continuous_const.mul (Complex.continuous_re.comp (continuous_entry a b))).add
      (continuous_const.mul (Complex.continuous_im.comp (continuous_entry a b)))
  · exact continuous_const

/-- Its variance. -/
def gueFormVar {W : ℕ} (t : ℝ) (d : Fin W → ℝ) (u v : Fin W → Fin W → ℝ) : ℝ :=
  ∑ a, t * d a ^ 2 + ∑ a, ∑ b, if a < b then t / 2 * (u a b ^ 2 + v a b ^ 2) else 0

/-- Characteristic function of the GUE block `GUE_W(t)` (`gueMeasure`) at a real linear form of its real coordinates
(diagonal, upper real and imaginary parts). -/
theorem gue_charFun {W : ℕ} (t : ℝ≥0) (d : Fin W → ℝ) (u v : Fin W → Fin W → ℝ) :
    ∫ A, Complex.exp (Complex.I * (gueForm d u v A : ℂ)) ∂(gueMeasure (Fin W) t) =
      Complex.exp (-((gueFormVar t d u v : ℝ) : ℂ) / 2) := by
  set st := Real.sqrt t / 2 with hst
  have hst2 : st ^ 2 = (t : ℝ) / 4 := by
    rw [hst, div_pow, Real.sq_sqrt (NNReal.coe_nonneg t)]; norm_num
  let coef : (Fin W × Fin W) × Fin 2 → ℝ := fun j =>
    if j.2 = 0 then (if j.1.1 = j.1.2 then 2 * st * d j.1.1 else if j.1.1 < j.1.2 then
        st * u j.1.1 j.1.2 else st * u j.1.2 j.1.1)
    else (if j.1.1 = j.1.2 then 0 else if j.1.1 < j.1.2 then st * v j.1.1 j.1.2
        else -(st * v j.1.2 j.1.1))
  have hform : ∀ r : (Fin W × Fin W) × Fin 2 → ℝ,
      gueForm d u v (gueSample t (circularBrownianCoordinates r)) = ∑ j, coef j * r j := by
    intro r
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type (f := fun (x : Fin W × Fin W) => _), Fin.sum_univ_two]
    rw [sum_sum_eq_diag_add_upper]
    unfold gueForm
    simp only [gueSample_circ_re, gueSample_circ_im]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp [coef]; ring
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : a < b
      · have hba : ¬ b < a := not_lt.mpr hab.le
        have hne : a ≠ b := ne_of_lt hab
        simp only [hab, ite_true, coef, hne, hne.symm, hba, ite_false]
        simp
        ring
      · simp [hab]
  have hvar : (∑ j, ((fun _ => (1 : ℝ≥0)) j : ℝ) * coef j ^ 2) = gueFormVar t d u v := by
    simp only [NNReal.coe_one, one_mul]
    rw [Fintype.sum_prod_type]
    simp_rw [Fin.sum_univ_two]
    rw [show (∑ x : Fin W × Fin W, (coef (x, 0) ^ 2 + coef (x, 1) ^ 2)) =
      ∑ a, ∑ b, (coef ((a, b), 0) ^ 2 + coef ((a, b), 1) ^ 2) from Fintype.sum_prod_type _]
    rw [sum_sum_eq_diag_add_upper]
    unfold gueFormVar
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [coef, ite_true, one_ne_zero, ite_false]
      simp
      nlinarith [hst2]
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : a < b
      · have hba : ¬ b < a := not_lt.mpr hab.le
        have hne : a ≠ b := ne_of_lt hab
        simp only [hab, ite_true, coef, hne, hne.symm, hba, ite_false]
        simp
        nlinarith [hst2]
      · simp [hab]
  unfold gueMeasure commonCircularIncrementLaw
  rw [Measure.map_map (measurable_gueSample t) measurable_circ,
    integral_map ((measurable_gueSample t).comp measurable_circ).aemeasurable
      (f := fun A => Complex.exp (Complex.I * (gueForm d u v A : ℂ)))
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_gueForm d u v)))).aestronglyMeasurable]
  simp only [Function.comp_apply, hform]
  have := BlockBand.Parameters.gaussianProduct_characteristic (fun _ => (1 : ℝ≥0)) coef
  rw [hvar] at this
  exact this

/-- The real linear form of a bond entering `coordinatePairing`. -/
def ginForm {W : ℕ} (α β : Fin W → Fin W → ℝ) (B : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ∑ a, ∑ b, (α a b * (B a b).re + β a b * (B a b).im)

/-- Its variance. -/
def ginFormVar {W : ℕ} (t : ℝ) (α β : Fin W → Fin W → ℝ) : ℝ :=
  ∑ a, ∑ b, t / 2 * (α a b ^ 2 + β a b ^ 2)

/-- `ginForm` is continuous. -/
theorem continuous_ginForm {W : ℕ} (α β : Fin W → Fin W → ℝ) : Continuous (ginForm α β) := by
  unfold ginForm
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (continuous_const.mul (Complex.continuous_re.comp (continuous_entry a b))).add
      (continuous_const.mul (Complex.continuous_im.comp (continuous_entry a b)))

/-- Characteristic function of the Ginibre bond `Gin(t)` (`ginibreMeasure`). -/
theorem gin_charFun {W : ℕ} (t : ℝ≥0) (α β : Fin W → Fin W → ℝ) :
    ∫ B, Complex.exp (Complex.I * (ginForm α β B : ℂ)) ∂(ginibreMeasure (Fin W) (Fin W) t) =
      Complex.exp (-((ginFormVar t α β : ℝ) : ℂ) / 2) := by
  set G : (Fin W × Fin W × Fin 2 → ℝ) → Matrix (Fin W) (Fin W) ℂ :=
    fun r => Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I
  have hG : Measurable G := Measurable.of_eval_matrix _ fun x y => by
    simp only [G, Matrix.of_apply]
    exact (Complex.measurable_ofReal.comp (measurable_pi_apply _)).add
      ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).mul measurable_const)
  let coef : Fin W × Fin W × Fin 2 → ℝ := fun j => if j.2.2 = 0 then α j.1 j.2.1 else β j.1 j.2.1
  have hform : ∀ r, ginForm α β (G r) = ∑ j, coef j * r j := by
    intro r
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [G, coef, Fin.sum_univ_two]
  have hvar : (∑ j, ((fun _ => t / 2) j : ℝ) * coef j ^ 2) = ginFormVar t α β := by
    unfold ginFormVar
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [coef, Fin.sum_univ_two]
    ring
  unfold ginibreMeasure
  rw [integral_map hG.aemeasurable (f := fun B => Complex.exp (Complex.I * (ginForm α β B : ℂ)))
    (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ginForm α β)))).aestronglyMeasurable]
  simp only [hform]
  have := BlockBand.Parameters.gaussianProduct_characteristic (fun _ => t / 2) coef
  rw [hvar] at this
  exact this

end CharFun

section Ring

variable (p : Parameters)

/-- Row-major order on sites. -/
theorem siteIndex_lt_iff (x y : p.Site) :
    p.siteIndex x < p.siteIndex y ↔ x.1.val < y.1.val ∨ (x.1 = y.1 ∧ x.2 < y.2) := by
  unfold Parameters.siteIndex
  have hx := x.2.isLt
  have hy := y.2.isLt
  rcases lt_trichotomy x.1.val y.1.val with h | h | h
  · have : (x.1.val + 1) * p.W ≤ y.1.val * p.W := Nat.mul_le_mul_right _ h
    rw [add_mul, one_mul] at this
    constructor
    · intro _; exact Or.inl h
    · intro _; omega
  · have h' : x.1 = y.1 := ZMod.val_injective _ h
    rw [h]
    constructor
    · intro hl; exact Or.inr ⟨h', Fin.lt_def.mpr (by omega)⟩
    · rintro (hl | ⟨-, hl⟩)
      · omega
      · have := Fin.lt_def.mp hl; omega
  · have : (y.1.val + 1) * p.W ≤ x.1.val * p.W := Nat.mul_le_mul_right _ h
    rw [add_mul, one_mul] at this
    constructor
    · intro _; omega
    · rintro (hl | ⟨he, -⟩)
      · omega
      · rw [he] at h; omega

/-- `1 ≠ 0` in `ZMod n`, `n ≥ 4`. -/
theorem zmod_one_ne_zero : (1 : ZMod p.n) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 1 p.n).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd one_pos this; have := p.n_ge_four; omega

/-- `2 ≠ 0` in `ZMod n`, `n ≥ 4`. -/
theorem zmod_two_ne_zero : (2 : ZMod p.n) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 2 p.n).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd two_pos this; have := p.n_ge_four; omega

/-- `q + 1 ≠ q`. -/
theorem succ_ne_self (q : ZMod p.n) : q + 1 ≠ q := fun h =>
  zmod_one_ne_zero p (by linear_combination h)

/-- `q + 2 ≠ q` (`n ≥ 4`). -/
theorem succ_succ_ne_self (q : ZMod p.n) : q + 1 + 1 ≠ q := fun h =>
  zmod_two_ne_zero p (by linear_combination h)

/-- `val q ≠ val (q+1)`. -/
theorem val_succ_ne (q : ZMod p.n) : q.val ≠ (q + 1).val := fun h =>
  succ_ne_self p q (ZMod.val_injective _ h).symm

/-- Regrouping the strict upper sum over sites into same-block pairs and the pairs of each bond
`q → q+1` (`n ≥ 4`). -/
theorem upper_sum_regroup (T : p.Site → p.Site → ℝ)
    (hT : ∀ x y : p.Site, x.1 ≠ y.1 → y.1 ≠ x.1 + 1 → x.1 ≠ y.1 + 1 → T x y = 0) :
    (∑ x, ∑ y with p.siteIndex x < p.siteIndex y, T x y) =
      (∑ q : ZMod p.n, ∑ a : Fin p.W, ∑ b : Fin p.W, if a < b then T (q, a) (q, b) else 0) +
      ∑ q : ZMod p.n, ∑ a : Fin p.W, ∑ b : Fin p.W,
        if q.val < (q + 1).val then T (q, a) (q + 1, b) else T (q + 1, b) (q, a) := by
  simp_rw [Finset.sum_filter]
  have hpt : ∀ x y : p.Site, (if p.siteIndex x < p.siteIndex y then T x y else 0) =
      (if x.1 = y.1 ∧ x.2 < y.2 then T x y else 0) +
      (if y.1 = x.1 + 1 ∧ x.1.val < y.1.val then T x y else 0) +
      (if x.1 = y.1 + 1 ∧ x.1.val < y.1.val then T x y else 0) := by
    intro x y
    simp only [siteIndex_lt_iff]
    by_cases h1 : x.1 = y.1
    · simp [h1, zmod_one_ne_zero p]
    · by_cases h2 : y.1 = x.1 + 1
      · have h4 : ¬ x.1 = x.1 + 1 + 1 := fun h => succ_succ_ne_self p x.1 h.symm
        simp [h2, h4, zmod_one_ne_zero p]
      · by_cases h3 : x.1 = y.1 + 1
        · have h4 : ¬ y.1 = y.1 + 1 + 1 := fun h => succ_succ_ne_self p y.1 h.symm
          simp [h3, h4, zmod_one_ne_zero p]
        · simp [h1, h2, h3, hT x y h1 h2 h3]
  simp_rw [hpt, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 1
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [ite_and]
    rw [Finset.sum_eq_single q]
    · simp
    · intro q' _ hq; simp [Ne.symm hq]
    · simp
  · have hB : ∀ q : ZMod p.n, ∀ a : Fin p.W,
        (∑ y : p.Site, if y.1 = q + 1 ∧ q.val < y.1.val then T (q, a) y else 0) =
          ∑ b : Fin p.W, if q.val < (q + 1).val then T (q, a) (q + 1, b) else 0 := by
      intro q a
      rw [Fintype.sum_prod_type]
      simp only [ite_and]
      rw [Finset.sum_eq_single (q + 1)]
      · split_ifs <;> simp_all
      · intro q' _ hq; simp [hq]
      · simp
    have hC : (∑ x : p.Site, ∑ y : p.Site,
        if x.1 = y.1 + 1 ∧ x.1.val < y.1.val then T x y else 0) =
        ∑ q : ZMod p.n, ∑ a : Fin p.W, ∑ b : Fin p.W,
          if (q + 1).val < q.val then T (q + 1, b) (q, a) else 0 := by
      rw [Finset.sum_comm, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
      rw [Fintype.sum_prod_type]
      simp only [ite_and]
      rw [Finset.sum_eq_single (q + 1)]
      · split_ifs <;> simp_all
      · intro q' _ hq; simp [hq]
      · simp
    rw [hC, Fintype.sum_prod_type]
    simp_rw [hB]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hv := val_succ_ne p q
    by_cases hlt : q.val < (q + 1).val
    · have : ¬ (q + 1).val < q.val := not_lt.mpr hlt.le
      simp [hlt, this]
    · have : (q + 1).val < q.val := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hv)
      simp [hlt, this]

/-!
### Entries of `ringMatrix` and of the variance profile
-/

variable {p}

/-- Diagonal blocks of `ringMatrix`. -/
theorem ringMatrix_same (ω : RingCoords p.n p.W) (q : ZMod p.n) (a b : Fin p.W) :
    ringMatrix ω (q, a) (q, b) = ω.1 q a b := by simp [ringMatrix]

/-- Forward bonds of `ringMatrix`. -/
theorem ringMatrix_succ (ω : RingCoords p.n p.W) (q : ZMod p.n) (a b : Fin p.W) :
    ringMatrix ω (q, a) (q + 1, b) = ω.2 q a b := by
  have h := (succ_ne_self p q).symm
  simp [ringMatrix, h]

/-- Reverse bonds of `ringMatrix`. -/
theorem ringMatrix_pred (ω : RingCoords p.n p.W) (q : ZMod p.n) (a b : Fin p.W) :
    ringMatrix ω (q + 1, b) (q, a) = star (ω.2 q a b) := by
  have h := succ_ne_self p q
  have h2 : ¬ q = q + 1 + 1 := fun e => succ_succ_ne_self p q e.symm
  simp [ringMatrix, h, h2]

/-- Entries outside the band vanish. -/
theorem ringMatrix_far (ω : RingCoords p.n p.W) {x y : p.Site} (h1 : x.1 ≠ y.1)
    (h2 : y.1 ≠ x.1 + 1) (h3 : x.1 ≠ y.1 + 1) : ringMatrix ω x y = 0 := by
  simp [ringMatrix, h1, h2, h3]

/-- Variance profile on diagonal blocks. -/
theorem entryVariance_same (q : ZMod p.n) (a b : Fin p.W) :
    p.entryVariance (q, a) (q, b) = p.c / p.W := by simp [Parameters.entryVariance]

/-- Variance profile on forward bonds. -/
theorem entryVariance_succ (q : ZMod p.n) (a b : Fin p.W) :
    p.entryVariance (q, a) (q + 1, b) = p.b / p.W := by
  have h := succ_ne_self p q
  simp [Parameters.entryVariance, h]

/-- Variance profile on reverse bonds. -/
theorem entryVariance_pred (q : ZMod p.n) (a b : Fin p.W) :
    p.entryVariance (q + 1, b) (q, a) = p.b / p.W := by
  have h := (succ_ne_self p q).symm
  simp [Parameters.entryVariance, h]

/-- Variance profile outside the band. -/
theorem entryVariance_far {x y : p.Site} (h1 : x.1 ≠ y.1)
    (h2 : y.1 ≠ x.1 + 1) (h3 : x.1 ≠ y.1 + 1) : p.entryVariance x y = 0 := by
  have h1' : ¬ y.1 = x.1 := fun e => h1 e.symm
  have h3' : ¬ y.1 = x.1 - 1 := fun e => h3 (by rw [e]; ring)
  simp [Parameters.entryVariance, h1', h2, h3']

variable (p)

/-- Coefficients of the bond `q` in `coordinatePairing`. -/
def bondU (u : p.Site → p.Site → ℝ) (q : ZMod p.n) (a b : Fin p.W) : ℝ :=
  if q.val < (q + 1).val then u (q, a) (q + 1, b) else u (q + 1, b) (q, a)

/-- Coefficients of the bond `q` in `coordinatePairing` (imaginary parts). -/
def bondV (v : p.Site → p.Site → ℝ) (q : ZMod p.n) (a b : Fin p.W) : ℝ :=
  if q.val < (q + 1).val then v (q, a) (q + 1, b) else -v (q + 1, b) (q, a)

/-- `coordinatePairing` of the assembled ring splits over blocks and bonds. -/
theorem coordinatePairing_ringMatrix (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
    (ω : RingCoords p.n p.W) :
    p.coordinatePairing d u v (ringMatrix ω) =
      (∑ q, gueForm (fun a => d (q, a)) (fun a b => u (q, a) (q, b)) (fun a b => v (q, a) (q, b))
        (ω.1 q)) + ∑ q, ginForm (bondU p u q) (bondV p v q) (ω.2 q) := by
  unfold Parameters.coordinatePairing
  rw [upper_sum_regroup p (fun x y => u x y * (ringMatrix ω x y).re + v x y * (ringMatrix ω x y).im)
    (fun x y h1 h2 h3 => by simp [ringMatrix_far ω h1 h2 h3])]
  unfold gueForm ginForm
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, add_assoc]
  congr 1
  · simp [ringMatrix_same]
  · congr 1
    · simp [ringMatrix_same]
    · refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      by_cases h : q.val < (q + 1).val
      · simp [h, bondU, bondV, ringMatrix_succ]
      · simp [h, bondU, bondV, ringMatrix_pred]

/-- `coordinateVariance` splits over blocks and bonds. -/
theorem coordinateVariance_split (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    p.coordinateVariance d u v =
      (∑ q, gueFormVar (p.c / p.W) (fun a => d (q, a)) (fun a b => u (q, a) (q, b))
        (fun a b => v (q, a) (q, b))) +
        ∑ q, ginFormVar (p.b / p.W) (bondU p u q) (bondV p v q) := by
  unfold Parameters.coordinateVariance
  rw [upper_sum_regroup p (fun x y => p.entryVariance x y / 2 * (u x y ^ 2 + v x y ^ 2))
    (fun x y h1 h2 h3 => by simp [entryVariance_far h1 h2 h3])]
  unfold gueFormVar ginFormVar
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, add_assoc]
  congr 1
  · simp [entryVariance_same]
  · congr 1
    · simp [entryVariance_same]
    · refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      by_cases h : q.val < (q + 1).val
      · simp [h, bondU, bondV, entryVariance_succ]
      · simp [h, bondU, bondV, entryVariance_pred]

end Ring

section Physical

variable (p : Parameters)

/-- `ringMatrix` is measurable. -/
theorem measurable_ringMatrix {n W : ℕ} : Measurable (ringMatrix (n := n) (W := W)) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  unfold ringMatrix
  split_ifs
  · exact (Matrix.measurable_apply).comp ((measurable_pi_apply _).comp measurable_fst)
  · exact (Matrix.measurable_apply).comp ((measurable_pi_apply _).comp measurable_snd)
  · exact continuous_star.measurable.comp
      ((Matrix.measurable_apply).comp ((measurable_pi_apply _).comp measurable_snd))
  · exact measurable_const

/-- The pairing is continuous. -/
theorem continuous_coordinatePairing (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    Continuous (p.coordinatePairing d u v) := by
  unfold Parameters.coordinatePairing
  exact (continuous_finsetSum _ fun x _ => continuous_const.mul
    (Complex.continuous_re.comp (continuous_entry x x))).add
    (continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ =>
      (continuous_const.mul (Complex.continuous_re.comp (continuous_entry x y))).add
        (continuous_const.mul (Complex.continuous_im.comp (continuous_entry x y))))

/-- The joint characteristic function of `ringMatrix` under the coordinate prior is that of the
physical model (`IsPhysicalGaussianRingLaw`, second clause). -/
theorem ringCoordLaw_charFun (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    ∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))
        ∂((ringCoordLaw p.n p.W p.b).map ringMatrix) =
      Complex.exp (-(p.coordinateVariance d u v : ℂ) / 2) := by
  rw [integral_map measurable_ringMatrix.aemeasurable
    (f := fun H => Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ)))
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_coordinatePairing p d u v)))).aestronglyMeasurable]
  simp_rw [coordinatePairing_ringMatrix]
  set F : ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ → ℂ := fun q A => Complex.exp (Complex.I *
    (gueForm (fun a => d (q, a)) (fun a b => u (q, a) (q, b)) (fun a b => v (q, a) (q, b)) A : ℂ))
  set G : ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ → ℂ := fun q B => Complex.exp (Complex.I *
    (ginForm (bondU p u q) (bondV p v q) B : ℂ))
  have hsplit : ∀ ω : RingCoords p.n p.W,
      Complex.exp (Complex.I * (((∑ q, gueForm (fun a => d (q, a)) (fun a b => u (q, a) (q, b))
        (fun a b => v (q, a) (q, b)) (ω.1 q)) +
        ∑ q, ginForm (bondU p u q) (bondV p v q) (ω.2 q) : ℝ) : ℂ)) =
      (∏ q, F q (ω.1 q)) * ∏ q, G q (ω.2 q) := by
    intro ω
    simp only [F, G, Complex.ofReal_add, Complex.ofReal_sum, mul_add, Finset.mul_sum,
      Complex.exp_add, Complex.exp_sum]
  simp_rw [hsplit]
  unfold ringCoordLaw
  rw [integral_prod_mul (fun A : ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ => ∏ q, F q (A q))
    (fun B : ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ => ∏ q, G q (B q)),
    integral_fintype_prod_eq_prod F, integral_fintype_prod_eq_prod G]
  simp only [F, G, gue_charFun, gin_charFun]
  rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add, coordinateVariance_split]
  have hc : ((Real.toNNReal ((1 - 2 * p.b) / p.W) : ℝ≥0) : ℝ) = p.c / p.W := by
    show ((Real.toNNReal (p.c / p.W) : ℝ≥0) : ℝ) = p.c / p.W
    exact Real.coe_toNNReal _ (div_pos p.c_pos (Nat.cast_pos.mpr p.W_pos)).le
  have hb : ((Real.toNNReal (p.b / p.W) : ℝ≥0) : ℝ) = p.b / p.W := by
    exact Real.coe_toNNReal _ (div_pos p.b_pos (Nat.cast_pos.mpr p.W_pos)).le
  rw [hc, hb]
  congr 1
  simp only [Complex.ofReal_add, Complex.ofReal_sum, neg_add, add_div, Finset.sum_div,
    Finset.sum_neg_distrib, neg_div]

/-- Hermitian matrices form a measurable set. -/
theorem measurableSet_isHermitian' {ι : Type*} [Fintype ι] :
    MeasurableSet {A : Matrix ι ι ℂ | A.IsHermitian} := by
  have : {A : Matrix ι ι ℂ | A.IsHermitian} = ⋂ a, ⋂ b, {A | star (A b a) = A a b} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h a b => h.apply a b, fun h => Matrix.IsHermitian.ext h⟩
  rw [this]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    measurableSet_eq_fun (continuous_star.measurable.comp Matrix.measurable_apply)
      Matrix.measurable_apply

/-- `ringMatrix ω` is Hermitian when all its diagonal blocks are. -/
theorem ringMatrix_isHermitian (ω : RingCoords p.n p.W) (hA : ∀ q, (ω.1 q).IsHermitian) :
    (ringMatrix ω).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨q, a⟩ ⟨q', b⟩
  by_cases h1 : q = q'
  · subst h1; rw [ringMatrix_same, ringMatrix_same]; exact (hA q).apply a b
  · by_cases h2 : q' = q + 1
    · subst h2; rw [ringMatrix_succ, ringMatrix_pred, star_star]
    · by_cases h3 : q = q' + 1
      · subst h3; rw [ringMatrix_succ, ringMatrix_pred]
      · rw [ringMatrix_far ω (x := (q, a)) (y := (q', b)) h1 h2 h3,
          ringMatrix_far ω (x := (q', b)) (y := (q, a)) (Ne.symm h1) h3 h2, star_zero]

/-- **`CoordinatePriorIsPhysical` holds**: the coordinate prior is the physical law. -/
theorem coordinatePriorIsPhysical : CoordinatePriorIsPhysical := by
  intro p
  refine ⟨⟨(ringCoordLaw p.n p.W p.b).map ringMatrix, inferInstance⟩, rfl, ?_, ?_⟩
  · change ∀ᵐ H ∂((ringCoordLaw p.n p.W p.b).map ringMatrix), H.IsHermitian
    rw [ae_map_iff measurable_ringMatrix.aemeasurable measurableSet_isHermitian']
    filter_upwards [ringCoordLaw_ae_isHermitian (n := p.n) (W := p.W) p.b] with ω hA
    exact ringMatrix_isHermitian p ω hA
  · intro d u v
    exact ringCoordLaw_charFun p d u v

/-!
### Transport to the law of every realization
-/

/-- Read the Gaussian coordinates (diagonal blocks, forward bonds) back from a ring matrix. -/
def ringCoordsOf {n W : ℕ} (H : Matrix (RingSite n W) (RingSite n W) ℂ) : RingCoords n W :=
  (fun q => Matrix.of fun a b => H (q, a) (q, b), fun q => Matrix.of fun a b => H (q, a) (q + 1, b))

/-- `ringCoordsOf` is measurable. -/
theorem measurable_ringCoordsOf {n W : ℕ} : Measurable (ringCoordsOf (n := n) (W := W)) :=
  Measurable.prodMk (Measurable.of_eval fun _ => Measurable.of_eval_matrix _ fun _ _ =>
      Matrix.measurable_apply)
    (Measurable.of_eval fun _ => Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply)

/-- `ringMatrix` is injective (`n ≥ 4`): `ringCoordsOf` is a left inverse. -/
theorem ringCoordsOf_ringMatrix (ω : RingCoords p.n p.W) : ringCoordsOf (ringMatrix ω) = ω := by
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_) <;> ext a b
  · exact ringMatrix_same ω q a b
  · exact ringMatrix_succ ω q a b

/-- Under the law of any realization, the coordinates read from `H` have the law
`ringCoordLaw`, and `H` is almost surely the ring assembled from them. -/
theorem hasLaw_ringCoordsOf (model : p.GaussianRingModel) :
    HasLaw ringCoordsOf (ringCoordLaw p.n p.W p.b) (model.law : Measure p.SiteMatrix) ∧
      ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ringMatrix (ringCoordsOf H) = H := by
  have hm := ringCoordLaw_map_eq_model coordinatePriorIsPhysical p model
  refine ⟨⟨measurable_ringCoordsOf.aemeasurable, ?_⟩, ?_⟩
  · rw [← hm, Measure.map_map measurable_ringCoordsOf measurable_ringMatrix]
    have : ringCoordsOf ∘ ringMatrix = (id : RingCoords p.n p.W → RingCoords p.n p.W) :=
      funext (ringCoordsOf_ringMatrix p)
    rw [this, Measure.map_id]
  · have hset : MeasurableSet {H : p.SiteMatrix | ringMatrix (ringCoordsOf H) = H} := by
      have : {H : p.SiteMatrix | ringMatrix (ringCoordsOf H) = H} =
          ⋂ x, ⋂ y, {H | ringMatrix (ringCoordsOf H) x y = H x y} := by
        ext H; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
        exact ⟨fun h x y => by rw [h], fun h => Matrix.ext h⟩
      rw [this]
      exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
        measurableSet_eq_fun ((Matrix.measurable_apply).comp
          (measurable_ringMatrix.comp measurable_ringCoordsOf)) Matrix.measurable_apply
    rw [← hm, ae_map_iff measurable_ringMatrix.aemeasurable hset]
    exact Filter.Eventually.of_forall fun ω => by rw [ringCoordsOf_ringMatrix]

/-- Transport of independence along a measurable map with the right law. -/
theorem indepFun_comp_of_hasLaw {Ω Ω' β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] [MeasurableSpace γ] {P : Measure Ω} {μ : Measure Ω'} [IsFiniteMeasure P]
    {X : Ω → Ω'} (hXm : Measurable X) (hX : HasLaw X μ P) {f : Ω' → β} {g : Ω' → γ}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun f g μ) :
    IndepFun (f ∘ X) (g ∘ X) P := by
  have : IsFiniteMeasure μ := by rw [← hX.map_eq]; infer_instance
  rw [indepFun_iff_map_prod_eq_prod_map_map (hf.comp hXm).aemeasurable
    (hg.comp hXm).aemeasurable]
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable] at h
  rw [← Measure.map_map hf hXm, ← Measure.map_map hg hXm, hX.map_eq,
    show (fun ω => ((f ∘ X) ω, (g ∘ X) ω)) = (fun ω' => (f ω', g ω')) ∘ X from rfl,
    ← Measure.map_map (hf.prodMk hg) hXm, hX.map_eq, h]

/-- `freshCollar` is measurable. -/
theorem measurable_freshCollar {m n W : ℕ} (L : Fin m → ℕ) (s : ZMod n) (k : Fin m) :
    Measurable (freshCollar (W := W) L s k) :=
  Measurable.prodMk (Measurable.of_eval fun _ => (measurable_pi_apply _).comp measurable_fst)
    (Measurable.of_eval fun _ => (measurable_pi_apply _).comp measurable_snd)

/-- `oldCoords` is measurable. -/
theorem measurable_oldCoords {m n W : ℕ} [NeZero n] (L : Fin m → ℕ) (s : ZMod n) (k : Fin m) :
    Measurable (oldCoords (W := W) L s k) :=
  Measurable.of_eval fun i => measurable_ringCoord i.1

/-- `(M_κ, C_o)` is measurable. -/
theorem measurable_oldNetwork {m n W : ℕ} [NeZero n] (L : Fin m → ℕ) (s : ZMod n) (π : Pairing)
    (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) :
    Measurable (fun ω : RingCoords n W =>
      (oldInterior L s π S k e z buf κ ω, oldCoupling L s π S k e z buf κ ω)) := by
  have hf := measurable_stageFull (W := W) (L := L) (s := s) π S e z buf κ
  exact Measurable.prodMk (Measurable.of_eval_matrix _ fun _ _ => hf.eval_matrix)
    (Measurable.of_eval_matrix _ fun _ _ => hf.eval_matrix)

/-- **Items (i) and (iii) under the physical law.** For every admissible `p`, every realization
`model : p.GaussianRingModel` (law `model.law` on `p.SiteMatrix`, the original prior of the model) and every
collar layout of its `p.n` blocks, with `ω := ringCoordsOf H`: `ω` has law `ringCoordLaw`, `H = ringMatrix ω`
almost surely, and, for either pairing and every stage, the fresh collar has law `GUE³⊗Gin²` and is independent of
all old coordinates and of the old network; both incident old components have the law `pathLaw` and are
independent of the fresh collar; the factorization holds almost surely on the event that `M_κ⁻¹`, `(G-e)⁻¹` exist
(its unconditional form is `stageMatrix_factorization_ae_locked`); the deterministic clauses (component structure,
matched ports, final models) are those of `sequentialCollars`. -/
theorem sequentialCollars_locked {m : ℕ} {L : Fin m → ℕ} (s : ZMod p.n)
    (model : p.GaussianRingModel) (hL : IsCollarLayout p.n L) (buf : ℕ) (e : ℝ) (z : ℂ)
    (hz : 0 < z.im) :
    HasLaw ringCoordsOf (ringCoordLaw p.n p.W p.b) (model.law : Measure p.SiteMatrix) ∧
    (∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ringMatrix (ringCoordsOf H) = H) ∧
    ∀ (π : Pairing) (S : Finset (Fin m)) (k : Fin m), k ∉ S →
      HasLaw (freshCollar L s k ∘ ringCoordsOf) (collarLaw p.W p.b)
        (model.law : Measure p.SiteMatrix) ∧
      IndepFun (freshCollar L s k ∘ ringCoordsOf) (oldCoords L s k ∘ ringCoordsOf)
        (model.law : Measure p.SiteMatrix) ∧
      (∀ κ : ℝ, IndepFun (freshCollar L s k ∘ ringCoordsOf)
        ((fun ω : RingCoords p.n p.W =>
          (oldInterior L s π S k e z buf κ ω, oldCoupling L s π S k e z buf κ ω)) ∘ ringCoordsOf)
        (model.law : Measure p.SiteMatrix)) ∧
      (∃ (pR : ZMod p.n) (rR : ℕ) (pL : ZMod p.n) (rL : ℕ),
        IsActualGaussianPath (W := p.W) L s π S k e z buf p.b pR rR ∧
        IsActualGaussianPath (W := p.W) L s π S k e z buf p.b pL rL ∧
        HasLaw (runSample pR rR ∘ ringCoordsOf) (pathLaw p.W rR p.b)
          (model.law : Measure p.SiteMatrix) ∧
        HasLaw (runSample pL rL ∘ ringCoordsOf) (pathLaw p.W rL p.b)
          (model.law : Measure p.SiteMatrix) ∧
        IndepFun (freshCollar L s k ∘ ringCoordsOf) (runSample pR rR ∘ ringCoordsOf)
          (model.law : Measure p.SiteMatrix) ∧
        IndepFun (freshCollar L s k ∘ ringCoordsOf) (runSample pL rL ∘ ringCoordsOf)
          (model.law : Measure p.SiteMatrix)) ∧
      (∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ κ : ℝ, 0 ≤ κ →
        IsUnit (oldInterior L s π S k e z buf κ (ringCoordsOf H)).det →
        IsUnit (collarMidBlock e (freshCollar L s k (ringCoordsOf H))).det →
        (stageMatrix L s π S e z buf κ (ringCoordsOf H)).det /
            (stageMatrix L s π (insert k S) e z buf κ (ringCoordsOf H)).det =
          collarPrefactor e z (freshCollar L s k (ringCoordsOf H)) *
            (1 - collarU z.im (collarKc e z.re (freshCollar L s k (ringCoordsOf H))) *
              oldResponse z (oldSchur (oldInterior L s π S k e z buf κ (ringCoordsOf H))
                (oldCoupling L s π S k e z buf κ (ringCoordsOf H))
                (oldCoupling L s π S k e z buf κ (ringCoordsOf H))ᴴ)).det) := by
  obtain ⟨hX, hrec⟩ := hasLaw_ringCoordsOf p model
  have hXm := measurable_ringCoordsOf (n := p.n) (W := p.W)
  have main := (sequentialCollars (W := p.W) (s := s) hL p.b buf e z hz).1
  refine ⟨hX, hrec, fun π S k hk => ?_⟩
  obtain ⟨⟨hfresh, hind, hindN⟩, ⟨pR, rR, pL, rL, hR, hLp, -⟩, -, hfac⟩ := main π S k hk
  refine ⟨hfresh.comp hX, indepFun_comp_of_hasLaw hXm hX (measurable_freshCollar L s k)
      (measurable_oldCoords L s k) hind,
    fun κ => indepFun_comp_of_hasLaw hXm hX (measurable_freshCollar L s k)
      (measurable_oldNetwork L s π S k e z buf κ) (hindN κ),
    ⟨pR, rR, pL, rL, hR, hLp, hR.2.2.2.1.comp hX, hLp.2.2.2.1.comp hX,
      indepFun_comp_of_hasLaw hXm hX (measurable_freshCollar L s k) (measurable_runSample _ _)
        hR.2.2.2.2.1,
      indepFun_comp_of_hasLaw hXm hX (measurable_freshCollar L s k) (measurable_runSample _ _)
        hLp.2.2.2.2.1⟩, ?_⟩
  rw [← hX.map_eq] at hfac
  exact ae_of_ae_map hX.aemeasurable hfac

end Physical

end BlockBand.Endpoints
