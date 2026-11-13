module

public import BlockBand.Layers.PathTraces
public import BlockBand.Model.Construction.GaussianCompatibility

/-!
# The physical ring as independent Gaussian blocks and bonds; the one-block decomposition

Step 5 of the proof of the matched-traces theorem: "For the ring with one block removed, we grow
the middle `n−3` physical blocks with separate ports, as above. The two remaining end blocks,
together with their bonds to the removed block, form one last layer in which both ends meet at a
common port."

Law: the exact physical law `model.law` (`IsPhysicalGaussianRingLaw`, characteristic function
definition; raw `H`, row variance one), every admissible `p` (`n ≥ 4`), every block
`k : ZMod n`, every real `E`.

* `rngLaw p`: independent diagonal blocks `A_j ~ GUE_W(c/W)` and bonds `B_j ~ Gin(b/W)`,
  `j : ZMod n`; `rngAssemble` puts `A_j` at `(j, j)`, `B_j` at `(j, j+1)` and `B_jᴴ` at
  `(j+1, j)`.
* `rng_law_eq_map` (law identification): `model.law = (rngLaw p).map rngAssemble`. Proof: the
  pushforward is a.s. Hermitian and has the characteristic function of the model (exact GUE and
  Ginibre characteristic functions `rng_charFun_gue`, `rng_charFun_ginibre`; band splitting of
  the pairing and of the variance, `rng_sum_band`), so it is the law of a second
  `GaussianRingModel` and the uniqueness `physicalGaussianRingLaw_unique` applies.
* `rng_mp_split` (rearrangement): relative to the removed block `k`, the map `rngSplit k`
  (layer blocks `A_{k+1}, A_{k-1}`, layer bonds `B_kᴴ, B_{k-1}`; path blocks `A_{k+2+i}`,
  path bonds `B_{k+2+i}`, path port bonds `B_{k+1}ᴴ, B_{k-2}`) carries `rngLaw p` to
  `layerLaw W b .common ⊗ pathLaw W (n-3) b` (the removed diagonal block is a dropped marginal).
* `rng_oneBlockComplement` (deterministic Schur composition): for invertible `H_path - E` and
  `A - E - X`, the one-block complement `Σ = C*(H_R - E)⁻¹C` of `rngAssemble ω` at block `k` is
  the common-port layer Schur matrix `B*(A - E - X)⁻¹B` with `X = pathSchur E π`, reindexed.
* `rng_eLpNorm_commonPort` (final transfer): for every `q`, the `L^q(model.law)` norm of
  `‖W⁻¹Tr(z₀ - Σ)⁻¹ - a‖` equals the `L^q(layerLaw .common ⊗ pathLaw (n-3))` norm of
  `‖W⁻¹Tr(𝒢_port) - a‖`, `𝒢` the common-port layer resolvent at `X = pathSchur E π`.

No hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample)
open scoped ENNReal NNReal ComplexConjugate

/-!
## 1. Characteristic functions of `GUE_W(t)` and `Gin_W(t)`
-/

section CharFun

variable {W : ℕ}

/-- Splitting a double sum along an injective key into diagonal and ordered off-diagonal parts. -/
theorem rng_sum_split_key {ι : Type*} [Fintype ι] [DecidableEq ι] (κ : ι → ℕ)
    (hκ : Function.Injective κ) (F : ι → ι → ℝ) :
    ∑ a, ∑ b, F a b = ∑ a, F a a + ∑ a, ∑ b, if κ a < κ b then F a b + F b a else 0 := by
  have hpt : ∀ a b, F a b = (if a = b then F a b else 0) + (if κ a < κ b then F a b else 0) +
      (if κ b < κ a then F a b else 0) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp
    · have hne : κ a ≠ κ b := fun h => hab (hκ h)
      rcases lt_or_gt_of_ne hne with h | h
      · simp [hab, h, not_lt.2 h.le]
      · simp [hab, h, not_lt.2 h.le]
  calc ∑ a, ∑ b, F a b
      = ∑ a, ∑ b, ((if a = b then F a b else 0) + (if κ a < κ b then F a b else 0) +
          (if κ b < κ a then F a b else 0)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hpt a b
    _ = ∑ a, F a a + (∑ a, ∑ b, (if κ a < κ b then F a b else 0) +
          ∑ a, ∑ b, (if κ b < κ a then F a b else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring
    _ = ∑ a, F a a + (∑ a, ∑ b, (if κ a < κ b then F a b else 0) +
          ∑ a, ∑ b, (if κ a < κ b then F b a else 0)) := by
        congr 2
        exact Finset.sum_comm
    _ = ∑ a, F a a + ∑ a, ∑ b, if κ a < κ b then F a b + F b a else 0 := by
        rw [← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> ring

/-- The real linear test of a `W × W` Hermitian block in the physical pairing: diagonal real
parts and the key-ordered upper real and imaginary parts. -/
def rngGueTest (κ : Fin W → ℕ) (D : Fin W → ℝ) (U V : Fin W → Fin W → ℝ)
    (A : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ∑ a, D a * (A a a).re +
    ∑ a, ∑ b, if κ a < κ b then U a b * (A a b).re + V a b * (A a b).im else 0

/-- Its variance under `GUE_W(t)`. -/
def rngGueVar (κ : Fin W → ℕ) (t : ℝ) (D : Fin W → ℝ) (U V : Fin W → Fin W → ℝ) : ℝ :=
  t * ∑ a, D a ^ 2 + ∑ a, ∑ b, if κ a < κ b then t / 2 * (U a b ^ 2 + V a b ^ 2) else 0

/-- The scale `√(t/2)/√2` of `gueOfCoords`. -/
def rngGueScale (t : ℝ≥0) : ℝ := Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2

theorem rng_gueOfCoords_re (t : ℝ≥0) (r : GaussCoord W → ℝ) (a b : Fin W) :
    (gueOfCoords W t r a b).re = rngGueScale t * (r ((a, b), 0) + r ((b, a), 0)) :=
  gueOfCoords_re W t r a b

theorem rng_gueOfCoords_im (t : ℝ≥0) (r : GaussCoord W → ℝ) (a b : Fin W) :
    (gueOfCoords W t r a b).im = rngGueScale t * (r ((a, b), 1) - r ((b, a), 1)) :=
  gueOfCoords_im W t r a b

/-- Coefficients of `rngGueTest ∘ gueOfCoords t` on the real circular coordinates. -/
def rngGueCoef (κ : Fin W → ℕ) (t : ℝ≥0) (D : Fin W → ℝ) (U V : Fin W → Fin W → ℝ)
    (k : GaussCoord W) : ℝ :=
  if k.2 = 0 then
    (if k.1.1 = k.1.2 then 2 * (rngGueScale t) * D k.1.1
      else if κ k.1.1 < κ k.1.2 then rngGueScale t * U k.1.1 k.1.2
      else rngGueScale t * U k.1.2 k.1.1)
  else
    (if k.1.1 = k.1.2 then 0
      else if κ k.1.1 < κ k.1.2 then rngGueScale t * V k.1.1 k.1.2
      else -(rngGueScale t * V k.1.2 k.1.1))

theorem rng_sum_gaussCoord (f : GaussCoord W → ℝ) :
    ∑ k, f k = ∑ a, ∑ b, (f ((a, b), 0) + f ((a, b), 1)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

theorem rng_gueScale_sq (t : ℝ≥0) :
    (rngGueScale t) ^ 2 = (t : ℝ) / 4 := by
  rw [rngGueScale, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
  ring

theorem rng_gueTest_coords (κ : Fin W → ℕ) (hκ : Function.Injective κ) (t : ℝ≥0)
    (D : Fin W → ℝ) (U V : Fin W → Fin W → ℝ) (r : GaussCoord W → ℝ) :
    rngGueTest κ D U V (gueOfCoords W t r) = ∑ k, rngGueCoef κ t D U V k * r k := by
  rw [rng_sum_gaussCoord, rng_sum_split_key κ hκ]
  unfold rngGueTest
  simp only [rng_gueOfCoords_re, rng_gueOfCoords_im]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [rngGueCoef]
    ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : κ a < κ b
    · have hab : a ≠ b := fun e => by subst e; exact lt_irrefl _ h
      have hba : b ≠ a := Ne.symm hab
      have h' : ¬ κ b < κ a := not_lt.2 h.le
      simp [rngGueCoef, h, h', hab, hba]
      ring
    · simp [h]

theorem rng_gueCoef_sq (κ : Fin W → ℕ) (hκ : Function.Injective κ) (t : ℝ≥0)
    (D : Fin W → ℝ) (U V : Fin W → Fin W → ℝ) :
    ∑ k, ((1 : ℝ≥0) : ℝ) * rngGueCoef κ t D U V k ^ 2 = rngGueVar κ t D U V := by
  rw [rng_sum_gaussCoord, rng_sum_split_key κ hκ]
  unfold rngGueVar
  have hs := rng_gueScale_sq t
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [rngGueCoef]
    simp
    nlinarith [hs]
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : κ a < κ b
    · have hab : a ≠ b := fun e => by subst e; exact lt_irrefl _ h
      have hba : b ≠ a := Ne.symm hab
      have h' : ¬ κ b < κ a := not_lt.2 h.le
      simp [rngGueCoef, h, h', hab, hba]
      nlinarith [hs]
    · simp [h]

theorem rng_measurable_gueTest (κ : Fin W → ℕ) (D : Fin W → ℝ) (U V : Fin W → Fin W → ℝ) :
    Measurable (rngGueTest κ D U V) := by
  unfold rngGueTest
  refine (Finset.measurable_sum _ fun a _ => ?_).add
    (Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  · exact measurable_const.mul (Complex.measurable_re.comp
      ((measurable_pi_apply a).comp (measurable_pi_apply a)))
  · split_ifs
    · exact (measurable_const.mul (Complex.measurable_re.comp
        ((measurable_pi_apply b).comp (measurable_pi_apply a)))).add
        (measurable_const.mul (Complex.measurable_im.comp
          ((measurable_pi_apply b).comp (measurable_pi_apply a))))
    · exact measurable_const

/-- **Characteristic function of `GUE_W(t)`** against the physical block test. -/
theorem rng_charFun_gue (κ : Fin W → ℕ) (hκ : Function.Injective κ) (t : ℝ≥0)
    (D : Fin W → ℝ) (U V : Fin W → Fin W → ℝ) :
    ∫ A, Complex.exp (Complex.I * (rngGueTest κ D U V A : ℂ)) ∂gueMeasure (Fin W) t =
      Complex.exp (-(rngGueVar κ t D U V : ℂ) / 2) := by
  have hm : Measurable (fun A => Complex.exp (Complex.I * (rngGueTest κ D U V A : ℂ))) := by
    have := rng_measurable_gueTest κ D U V
    fun_prop
  rw [gueMeasure_eq_map, integral_map (measurable_gueOfCoords W t).aemeasurable
    hm.aestronglyMeasurable]
  simp only [rng_gueTest_coords κ hκ]
  have h := BlockBand.Parameters.gaussianProduct_characteristic (fun _ : GaussCoord W => (1 : ℝ≥0))
    (rngGueCoef κ t D U V)
  rw [rng_gueCoef_sq κ hκ] at h
  exact h

/-- The real linear test of a bond block: `Σ (S Re B + T Im B)`. -/
def rngGinTest (S T : Fin W → Fin W → ℝ) (B : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ∑ a, ∑ b, (S a b * (B a b).re + T a b * (B a b).im)

theorem rng_measurable_ginTest (S T : Fin W → Fin W → ℝ) : Measurable (rngGinTest S T) := by
  unfold rngGinTest
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact (measurable_const.mul (Complex.measurable_re.comp
      ((measurable_pi_apply b).comp (measurable_pi_apply a)))).add
    (measurable_const.mul (Complex.measurable_im.comp
      ((measurable_pi_apply b).comp (measurable_pi_apply a))))

/-- **Characteristic function of `Gin_W(t)`** (`E|B_ab|² = t`, real and imaginary parts of
variance `t/2`). -/
theorem rng_charFun_ginibre (t : ℝ≥0) (S T : Fin W → Fin W → ℝ) :
    ∫ B, Complex.exp (Complex.I * (rngGinTest S T B : ℂ)) ∂ginibreMeasure (Fin W) (Fin W) t =
      Complex.exp (-(((t : ℝ) / 2 * ∑ a, ∑ b, (S a b ^ 2 + T a b ^ 2) : ℝ) : ℂ) / 2) := by
  have hm : Measurable (fun B => Complex.exp (Complex.I * (rngGinTest S T B : ℂ))) := by
    have := rng_measurable_ginTest S T
    fun_prop
  rw [ginibreMeasure_eq_map, integral_map measurable_ginibreAssemble.aemeasurable
    hm.aestronglyMeasurable]
  let coef : Fin W × Fin W × Fin 2 → ℝ := fun k => if k.2.2 = 0 then S k.1 k.2.1 else T k.1 k.2.1
  have hlin : ∀ r : Fin W × Fin W × Fin 2 → ℝ,
      rngGinTest S T (ginibreAssemble r) = ∑ k, coef k * r k := by
    intro r
    rw [Fintype.sum_prod_type]
    unfold rngGinTest
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [ginibreAssemble, coef, Fin.sum_univ_two]
  simp only [hlin]
  have h := BlockBand.Parameters.gaussianProduct_characteristic
    (fun _ : Fin W × Fin W × Fin 2 => t / 2) coef
  unfold whiteNoise
  rw [h]
  have hv : (∑ k : Fin W × Fin W × Fin 2, (((t / 2 : ℝ≥0) : ℝ)) * coef k ^ 2) =
      (t : ℝ) / 2 * ∑ a, ∑ b, (S a b ^ 2 + T a b ^ 2) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [coef, Fin.sum_univ_two]
    ring
  rw [hv]

end CharFun

/-!
## 2. The ring sample and the law identification
-/

section Ring

variable (p : Parameters)

/-- `(m : ZMod n) ≠ 0` for `0 < m < n`. -/
theorem rng_natCast_ne_zero {m : ℕ} (h0 : 0 < m) (hm : m < p.n) : ((m : ℕ) : ZMod p.n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

theorem rng_add_one_ne (j : ZMod p.n) : j + 1 ≠ j := by
  intro h
  have h1 : ((1 : ℕ) : ZMod p.n) = 0 := by
    have := congrArg (fun x => x - j) h
    simpa using this
  exact rng_natCast_ne_zero p one_pos (by have := p.n_ge_four; omega) h1

theorem rng_add_two_ne (j : ZMod p.n) : j + 1 + 1 ≠ j := by
  intro h
  have h1 : ((2 : ℕ) : ZMod p.n) = 0 := by
    have := congrArg (fun x => x - j) h
    push_cast
    linear_combination this
  exact rng_natCast_ne_zero p two_pos (by have := p.n_ge_four; omega) h1

/-- Independent diagonal blocks and bonds of the ring, indexed by `ZMod n`
(bond `j` joins blocks `j` and `j + 1`). -/
abbrev RngSample := (ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ) ×
  (ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ)

/-- Law of the ring sample: independent `GUE_W(c/W)` blocks and `Gin(b/W)` bonds. -/
def rngLaw : Measure (RngSample p) :=
  (Measure.pi fun _ : ZMod p.n => gueMeasure (Fin p.W) (Real.toNNReal ((1 - 2 * p.b) / p.W))).prod
    (Measure.pi fun _ : ZMod p.n => ginibreMeasure (Fin p.W) (Fin p.W) (Real.toNNReal (p.b / p.W)))

instance rng_isProbabilityMeasure_rngLaw : IsProbabilityMeasure (rngLaw p) := by
  have := fun t => isProbabilityMeasure_gueMeasure p.W t
  unfold rngLaw
  infer_instance

/-- The ring matrix: `A_j` at `(j, j)`, `B_j` at `(j, j+1)`, `B_jᴴ` at `(j+1, j)`. -/
def rngAssemble (ω : RngSample p) : p.SiteMatrix := fun x y =>
  if x.1 = y.1 then ω.1 x.1 x.2 y.2
  else if y.1 = x.1 + 1 then ω.2 x.1 x.2 y.2
  else if x.1 = y.1 + 1 then star (ω.2 y.1 y.2 x.2)
  else 0

variable {p}

theorem rngAssemble_same (ω : RngSample p) (j : ZMod p.n) (a b : Fin p.W) :
    rngAssemble p ω (j, a) (j, b) = ω.1 j a b := by
  simp [rngAssemble]

theorem rngAssemble_succ (ω : RngSample p) (j : ZMod p.n) (a b : Fin p.W) :
    rngAssemble p ω (j, a) (j + 1, b) = ω.2 j a b := by
  have h1 : j ≠ j + 1 := (rng_add_one_ne p j).symm
  simp [rngAssemble, h1]

theorem rngAssemble_pred (ω : RngSample p) (j : ZMod p.n) (a b : Fin p.W) :
    rngAssemble p ω (j + 1, b) (j, a) = star (ω.2 j a b) := by
  have h1 : j + 1 ≠ j := rng_add_one_ne p j
  have h2 : j ≠ j + 1 + 1 := (rng_add_two_ne p j).symm
  simp [rngAssemble, h1, h2]

theorem rngAssemble_far (ω : RngSample p) (x y : p.Site) (h1 : x.1 ≠ y.1) (h2 : y.1 ≠ x.1 + 1)
    (h3 : x.1 ≠ y.1 + 1) : rngAssemble p ω x y = 0 := by
  simp [rngAssemble, h1, h2, h3]

theorem rngAssemble_isHermitian (ω : RngSample p) (hA : ∀ j, (ω.1 j).IsHermitian) :
    (rngAssemble p ω).IsHermitian := by
  ext x y
  obtain ⟨j, a⟩ := x
  obtain ⟨j', b⟩ := y
  simp only [conjTranspose_apply]
  by_cases h1 : j = j'
  · subst h1
    rw [rngAssemble_same, rngAssemble_same]
    exact (hA j).apply a b
  by_cases h2 : j' = j + 1
  · subst h2
    rw [rngAssemble_succ, rngAssemble_pred, star_star]
  by_cases h3 : j = j' + 1
  · subst h3
    rw [rngAssemble_succ, rngAssemble_pred]
  rw [rngAssemble_far ω (j', b) (j, a) (Ne.symm h1) (fun h => h3 h) (fun h => h2 h),
    rngAssemble_far ω (j, a) (j', b) h1 h2 h3, star_zero]

theorem rng_measurable_assemble : Measurable (rngAssemble p) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  unfold rngAssemble
  split_ifs
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp measurable_fst))
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp measurable_snd))
  · exact continuous_star.measurable.comp ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp measurable_snd)))
  · exact measurable_const

/-- **Band splitting** of a double sum over sites, for a kernel supported on equal or
adjacent blocks. -/
theorem rng_sum_band (F : p.Site → p.Site → ℝ)
    (hF : ∀ x y : p.Site, x.1 ≠ y.1 → y.1 ≠ x.1 + 1 → x.1 ≠ y.1 + 1 → F x y = 0) :
    ∑ x, ∑ y, F x y = ∑ j, ∑ a, ∑ b, F (j, a) (j, b) +
      ∑ j, ∑ a, ∑ b, (F (j, a) (j + 1, b) + F (j + 1, b) (j, a)) := by
  set G : ZMod p.n → ZMod p.n → ℝ := fun j j' => ∑ a, ∑ b, F (j, a) (j', b) with hGdef
  have h1 : ∑ x, ∑ y, F x y = ∑ j, ∑ j', G j j' := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hG : ∀ j j', j ≠ j' → j' ≠ j + 1 → j ≠ j' + 1 → G j j' = 0 := by
    intro j j' h1 h2 h3
    exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => hF _ _ h1 h2 h3
  have h2 : ∀ j, ∑ j', G j j' = G j j + G j (j + 1) + G j (j - 1) := by
    intro j
    have hsub : ∑ j' ∈ ({j, j + 1, j - 1} : Finset (ZMod p.n)), G j j' = ∑ j', G j j' := by
      refine Finset.sum_subset (Finset.subset_univ _) fun j' _ hj' => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
      refine hG j j' (Ne.symm hj'.1) hj'.2.1 fun h => hj'.2.2 ?_
      rw [h]; ring
    rw [← hsub]
    have hn1 : j ≠ j + 1 := (rng_add_one_ne p j).symm
    have hn2 : j ≠ j - 1 := fun h =>
      rng_add_one_ne p (j - 1) (by rw [sub_add_cancel]; exact h)
    have hn3 : j + 1 ≠ j - 1 := fun h =>
      rng_add_two_ne p (j - 1) (by rw [sub_add_cancel]; exact h)
    rw [Finset.sum_insert (by simp [hn1, hn2]), Finset.sum_insert (by simp [hn3]),
      Finset.sum_singleton]
    ring
  have h3 : ∑ j, G (j + 1) j = ∑ j, G j (j - 1) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ fun j => by simp
  rw [h1]
  simp_rw [h2]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← h3, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hGdef, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

/-- Coefficient of `Re B_j` in the bond test: `u` at the key-ordered position. -/
def rngS (u : p.Site → p.Site → ℝ) (j : ZMod p.n) (a b : Fin p.W) : ℝ :=
  if p.siteIndex (j, a) < p.siteIndex (j + 1, b) then u (j, a) (j + 1, b) else u (j + 1, b) (j, a)

/-- Coefficient of `Im B_j` in the bond test (sign flip on the conjugated entry). -/
def rngT (v : p.Site → p.Site → ℝ) (j : ZMod p.n) (a b : Fin p.W) : ℝ :=
  if p.siteIndex (j, a) < p.siteIndex (j + 1, b) then v (j, a) (j + 1, b) else -v (j + 1, b) (j, a)

theorem rng_siteIndex_injective_block (j : ZMod p.n) :
    Function.Injective fun a : Fin p.W => p.siteIndex (j, a) := fun a b h => by
  have := p.siteIndex_injective h
  simpa using this

theorem rng_siteIndex_lt_or (x y : p.Site) (h : x ≠ y) :
    p.siteIndex x < p.siteIndex y ∨ p.siteIndex y < p.siteIndex x := by
  have : p.siteIndex x ≠ p.siteIndex y := fun e => h (p.siteIndex_injective e)
  omega

theorem rng_ne_succ_site (j : ZMod p.n) (a b : Fin p.W) : ((j, a) : p.Site) ≠ (j + 1, b) := by
  intro h
  exact rng_add_one_ne p j (congrArg Prod.fst h).symm

/-- **Variance splitting**: the physical covariance form is the sum of the block GUE variances
and the bond Ginibre variances. -/
theorem rng_coordinateVariance (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    p.coordinateVariance d u v =
      ∑ j, rngGueVar (fun a => p.siteIndex (j, a)) (p.c / p.W) (fun a => d (j, a))
          (fun a b => u (j, a) (j, b)) (fun a b => v (j, a) (j, b)) +
        ∑ j, p.b / p.W / 2 * ∑ a, ∑ b, (rngS u j a b ^ 2 + rngT v j a b ^ 2) := by
  unfold Parameters.coordinateVariance
  simp only [Finset.sum_filter]
  rw [rng_sum_band (F := fun x y => if p.siteIndex x < p.siteIndex y then
      p.entryVariance x y / 2 * (u x y ^ 2 + v x y ^ 2) else 0)]
  swap
  · intro x y h1 h2 h3
    have : p.entryVariance x y = 0 := by
      unfold Parameters.entryVariance
      have h4 : y.1 ≠ x.1 - 1 := fun h => h3 (by rw [h]; ring)
      simp [Ne.symm h1, h2, h4]
    simp [this]
  have hd : ∑ x : p.Site, p.entryVariance x x * d x ^ 2 =
      ∑ j : ZMod p.n, p.c / p.W * ∑ a, d (j, a) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Parameters.entryVariance]
  rw [hd]
  unfold rngGueVar
  rw [Finset.sum_add_distrib, add_assoc]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    simp [Parameters.entryVariance]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hv1 : p.entryVariance (j, a) (j + 1, b) = p.b / p.W := by
      unfold Parameters.entryVariance
      simp [rng_add_one_ne p j]
    have hv2 : p.entryVariance (j + 1, b) (j, a) = p.b / p.W := by
      unfold Parameters.entryVariance
      simp [(rng_add_one_ne p j).symm]
    rw [hv1, hv2]
    unfold rngS rngT
    rcases rng_siteIndex_lt_or (j, a) (j + 1, b) (rng_ne_succ_site j a b) with h | h
    · simp [h, not_lt.2 h.le]
    · simp [h, not_lt.2 h.le]

theorem rng_coordinatePairing_assemble (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
    (ω : RngSample p) :
    p.coordinatePairing d u v (rngAssemble p ω) =
      ∑ j, rngGueTest (fun a => p.siteIndex (j, a)) (fun a => d (j, a))
          (fun a b => u (j, a) (j, b)) (fun a b => v (j, a) (j, b)) (ω.1 j) +
        ∑ j, rngGinTest (rngS u j) (rngT v j) (ω.2 j) := by
  unfold Parameters.coordinatePairing
  simp only [Finset.sum_filter]
  rw [rng_sum_band (F := fun x y => if p.siteIndex x < p.siteIndex y then
      u x y * (rngAssemble p ω x y).re + v x y * (rngAssemble p ω x y).im else 0)]
  swap
  · intro x y h1 h2 h3
    simp [rngAssemble_far ω x y h1 h2 h3]
  have hd : ∑ x : p.Site, d x * (rngAssemble p ω x x).re =
      ∑ j : ZMod p.n, ∑ a, d (j, a) * (ω.1 j a a).re := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    rw [rngAssemble_same]
  rw [hd]
  unfold rngGueTest
  rw [Finset.sum_add_distrib, add_assoc]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    simp only [rngAssemble_same]
  · refine Finset.sum_congr rfl fun j _ => ?_
    unfold rngGinTest
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [rngAssemble_succ, rngAssemble_pred]
    unfold rngS rngT
    rcases rng_siteIndex_lt_or (j, a) (j + 1, b) (rng_ne_succ_site j a b) with h | h
    · simp [h, not_lt.2 h.le]
    · simp [h, not_lt.2 h.le]

theorem rng_measurable_coordinatePairing (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    Measurable (p.coordinatePairing d u v) := by
  unfold Parameters.coordinatePairing
  refine (Finset.measurable_sum _ fun x _ => ?_).add
    (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_)
  · exact measurable_const.mul (Complex.measurable_re.comp
      ((measurable_pi_apply x).comp (measurable_pi_apply x)))
  · exact (measurable_const.mul (Complex.measurable_re.comp
        ((measurable_pi_apply y).comp (measurable_pi_apply x)))).add
      (measurable_const.mul (Complex.measurable_im.comp
        ((measurable_pi_apply y).comp (measurable_pi_apply x))))

theorem rng_exp_sum_split {α β : Type*} (s : Finset α) (t : Finset β) (f : α → ℝ) (g : β → ℝ) :
    Complex.exp (Complex.I * (((∑ j ∈ s, f j) + ∑ j ∈ t, g j : ℝ) : ℂ)) =
      (∏ j ∈ s, Complex.exp (Complex.I * (f j : ℂ))) *
        ∏ j ∈ t, Complex.exp (Complex.I * (g j : ℂ)) := by
  rw [Complex.ofReal_add, mul_add, Complex.exp_add, Complex.ofReal_sum, Complex.ofReal_sum,
    Finset.mul_sum, Finset.mul_sum, Complex.exp_sum, Complex.exp_sum]

/-- **Characteristic function of the assembled ring** = that of the model. -/
theorem rng_charFun (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    ∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))
        ∂(rngLaw p).map (rngAssemble p) =
      Complex.exp (-(p.coordinateVariance d u v : ℂ) / 2) := by
  have hm : Measurable (fun H : p.SiteMatrix =>
      Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))) := by
    have := rng_measurable_coordinatePairing (p := p) d u v
    fun_prop
  rw [integral_map rng_measurable_assemble.aemeasurable hm.aestronglyMeasurable]
  simp only [rng_coordinatePairing_assemble, rng_exp_sum_split]
  have := fun t => isProbabilityMeasure_gueMeasure p.W t
  unfold rngLaw
  rw [integral_prod_mul (f := fun A : ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ =>
      ∏ j, Complex.exp (Complex.I * (rngGueTest (fun a => p.siteIndex (j, a)) (fun a => d (j, a))
        (fun a b => u (j, a) (j, b)) (fun a b => v (j, a) (j, b)) (A j) : ℂ)))
    (g := fun B : ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ =>
      ∏ j, Complex.exp (Complex.I * (rngGinTest (rngS u j) (rngT v j) (B j) : ℂ))),
    integral_fintype_prod_eq_prod (fun j (A : Matrix (Fin p.W) (Fin p.W) ℂ) =>
      Complex.exp (Complex.I * (rngGueTest (fun a => p.siteIndex (j, a)) (fun a => d (j, a))
        (fun a b => u (j, a) (j, b)) (fun a b => v (j, a) (j, b)) A : ℂ))),
    integral_fintype_prod_eq_prod (fun j (B : Matrix (Fin p.W) (Fin p.W) ℂ) =>
      Complex.exp (Complex.I * (rngGinTest (rngS u j) (rngT v j) B : ℂ)))]
  simp only [rng_charFun_gue _ (rng_siteIndex_injective_block _), rng_charFun_ginibre]
  have hc : ((Real.toNNReal ((1 - 2 * p.b) / p.W) : ℝ)) = p.c / p.W := by
    rw [Real.coe_toNNReal _ (div_nonneg (by linarith [p.b_lt_half]) (Nat.cast_nonneg _))]
    rfl
  have hb : ((Real.toNNReal (p.b / p.W) : ℝ)) = p.b / p.W :=
    Real.coe_toNNReal _ (div_nonneg p.b_pos.le (Nat.cast_nonneg _))
  rw [hc, hb, ← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add, rng_coordinateVariance]
  congr 1
  push_cast
  simp only [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div]
  ring

theorem rng_ae_isHermitian_gue (t : ℝ≥0) :
    ∀ᵐ A ∂gueMeasure (Fin p.W) t, A.IsHermitian := by
  have hS : MeasurableSet {A : Matrix (Fin p.W) (Fin p.W) ℂ | A.IsHermitian} :=
    (isClosed_eq (by fun_prop : Continuous (fun A : Matrix (Fin p.W) (Fin p.W) ℂ => Aᴴ))
      continuous_id).measurableSet
  rw [gueMeasure_eq_map, ae_map_iff (measurable_gueOfCoords p.W t).aemeasurable hS]
  refine Filter.Eventually.of_forall fun r => ?_
  ext a b
  exact gueOfCoords_star p.W t r a b

theorem rng_ae_blocks_isHermitian : ∀ᵐ ω ∂rngLaw p, ∀ j, (ω.1 j).IsHermitian := by
  have := fun t => isProbabilityMeasure_gueMeasure p.W t
  refine Filter.eventually_all.mpr fun j => ?_
  have h := ((measurePreserving_eval (fun _ : ZMod p.n =>
      gueMeasure (Fin p.W) (Real.toNNReal ((1 - 2 * p.b) / p.W))) j).comp
    (measurePreserving_fst (μ := Measure.pi fun _ : ZMod p.n =>
      gueMeasure (Fin p.W) (Real.toNNReal ((1 - 2 * p.b) / p.W)))
      (ν := Measure.pi fun _ : ZMod p.n =>
        ginibreMeasure (Fin p.W) (Fin p.W) (Real.toNNReal (p.b / p.W)))))
  exact h.quasiMeasurePreserving.ae (rng_ae_isHermitian_gue _)

variable (p) in
/-- The assembled ring law as a probability measure. -/
def rngRingLaw : ProbabilityMeasure p.SiteMatrix :=
  ⟨(rngLaw p).map (rngAssemble p), inferInstance⟩

variable (p) in
/-- The assembled ring realizes the exact physical law. -/
def rngModel : p.GaussianRingModel where
  law := rngRingLaw p
  isPhysical := by
    refine ⟨?_, fun d u v => rng_charFun d u v⟩
    change ∀ᵐ H ∂(rngLaw p).map (rngAssemble p), H.IsHermitian
    have hS : MeasurableSet {H : p.SiteMatrix | H.IsHermitian} :=
      (isClosed_eq (by fun_prop : Continuous (fun H : p.SiteMatrix => Hᴴ))
        continuous_id).measurableSet
    rw [ae_map_iff rng_measurable_assemble.aemeasurable hS]
    filter_upwards [rng_ae_blocks_isHermitian] with ω hω
    exact rngAssemble_isHermitian ω hω

/-- **Law identification**: every realization of the exact physical law is the image of the
independent block/bond law under `rngAssemble`. -/
theorem rng_law_eq_map (model : p.GaussianRingModel) :
    (model.law : Measure p.SiteMatrix) = (rngLaw p).map (rngAssemble p) := by
  rw [BlockBand.Parameters.physicalGaussianRingLaw_unique model (rngModel p)]
  rfl

end Ring

/-!
## 3. Offsets relative to the removed block and the split of the ring sample
-/

section Split

variable {p : Parameters}

/-- The block at offset `o` from `k`: `k + o`. -/
def rngBlk (k : ZMod p.n) (o : ℕ) : ZMod p.n := k + (o : ZMod p.n)

theorem rngBlk_zero (k : ZMod p.n) : rngBlk k 0 = k := by simp [rngBlk]

theorem rngBlk_succ (k : ZMod p.n) (o : ℕ) : rngBlk k o + 1 = rngBlk k (o + 1) := by
  simp only [rngBlk]; push_cast; ring

theorem rngBlk_eq_iff (k : ZMod p.n) {o₁ o₂ : ℕ} (h₁ : o₁ < p.n) (h₂ : o₂ < p.n) :
    rngBlk k o₁ = rngBlk k o₂ ↔ o₁ = o₂ := by
  constructor
  · intro h
    have h' : ((o₁ : ℕ) : ZMod p.n) = (o₂ : ℕ) := by simpa [rngBlk] using h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at h'
    exact h'
  · rintro rfl; rfl

theorem rngBlk_succ_eq_iff (k : ZMod p.n) {o₁ o₂ : ℕ} (h₁ : o₁ < p.n) (h₂ : o₂ < p.n) :
    rngBlk k o₂ = rngBlk k o₁ + 1 ↔ (o₂ = o₁ + 1 ∨ (o₁ + 1 = p.n ∧ o₂ = 0)) := by
  rw [rngBlk_succ]
  constructor
  · intro h
    have h' : ((o₂ : ℕ) : ZMod p.n) = ((o₁ + 1 : ℕ) : ZMod p.n) := by simpa [rngBlk] using h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h₂] at h'
    by_cases hc : o₁ + 1 = p.n
    · rw [hc, Nat.mod_self] at h'; exact Or.inr ⟨hc, h'⟩
    · rw [Nat.mod_eq_of_lt (by omega)] at h'; exact Or.inl h'
  · rintro (h | ⟨h1, h2⟩)
    · rw [h]
    · rw [h1, h2]
      simp [rngBlk]

/-- **Ring entries at offsets** `o₁, o₂ < n` from `k`. -/
theorem rngAssemble_off (ω : RngSample p) (k : ZMod p.n) {o₁ o₂ : ℕ} (h₁ : o₁ < p.n)
    (h₂ : o₂ < p.n) (a b : Fin p.W) :
    rngAssemble p ω (rngBlk k o₁, a) (rngBlk k o₂, b) =
      if o₁ = o₂ then ω.1 (rngBlk k o₁) a b
      else if o₂ = o₁ + 1 ∨ (o₁ + 1 = p.n ∧ o₂ = 0) then ω.2 (rngBlk k o₁) a b
      else if o₁ = o₂ + 1 ∨ (o₂ + 1 = p.n ∧ o₁ = 0) then star (ω.2 (rngBlk k o₂) b a)
      else 0 := by
  unfold rngAssemble
  simp only [rngBlk_eq_iff k h₁ h₂, rngBlk_succ_eq_iff k h₁ h₂, rngBlk_succ_eq_iff k h₂ h₁]

theorem rngAssemble_star_of_ne (ω : RngSample p) (x y : p.Site) (h : x.1 ≠ y.1) :
    star (rngAssemble p ω x y) = rngAssemble p ω y x := by
  obtain ⟨j, a⟩ := x
  obtain ⟨j', b⟩ := y
  simp only at h
  by_cases h2 : j' = j + 1
  · subst h2
    rw [rngAssemble_succ, rngAssemble_pred]
  by_cases h3 : j = j' + 1
  · subst h3
    rw [rngAssemble_succ, rngAssemble_pred, star_star]
  rw [rngAssemble_far ω (j, a) (j', b) h h2 h3,
    rngAssemble_far ω (j', b) (j, a) (Ne.symm h) (fun e => h3 e) (fun e => h2 e), star_zero]

variable (p) in
/-- Offsets of the two end blocks of the last layer: `k + 1` (layer block `0`) and `k - 1`
(layer block `1`). -/
def rngLayerOff (a : Fin 2) : ℕ := if a = 0 then 1 else p.n - 1

variable (p) in
/-- Offsets of all blocks other than `k`: the layer blocks, then path block `i` at `i + 2`. -/
def rngOff : Fin 2 ⊕ Fin (p.n - 3) → ℕ
  | .inl a => rngLayerOff p a
  | .inr i => i.val + 2

theorem rngOff_lt (u : Fin 2 ⊕ Fin (p.n - 3)) : rngOff p u < p.n := by
  have := p.n_ge_four
  rcases u with a | i
  · simp only [rngOff, rngLayerOff]; split_ifs <;> omega
  · simp only [rngOff]; omega

theorem rngOff_pos (u : Fin 2 ⊕ Fin (p.n - 3)) : 0 < rngOff p u := by
  have := p.n_ge_four
  rcases u with a | i
  · simp only [rngOff, rngLayerOff]; split_ifs <;> omega
  · simp only [rngOff]; omega

theorem rngOff_injective : Function.Injective (rngOff p) := by
  have := p.n_ge_four
  rintro (a | i) (a' | i') h <;> simp only [rngOff, rngLayerOff] at h
  · congr 1
    by_cases ha : a = 0 <;> by_cases ha' : a' = 0
    · rw [ha, ha']
    · rw [ite_eq_left ha, ite_eq_right ha'] at h; omega
    · rw [ite_eq_right ha, ite_eq_left ha'] at h; omega
    · have h1 : a.val ≠ 0 := fun e => ha (Fin.ext e)
      have h2 : a'.val ≠ 0 := fun e => ha' (Fin.ext e)
      exact Fin.ext (by have := a.isLt; have := a'.isLt; omega)
  · exfalso; have := i'.isLt; split_ifs at h <;> omega
  · exfalso; have := i.isLt; split_ifs at h <;> omega
  · congr 1; exact Fin.ext (by omega)

/-- The non-removed blocks as blocks `≠ k`. -/
def rngBlkNe (k : ZMod p.n) (u : Fin 2 ⊕ Fin (p.n - 3)) : {j : ZMod p.n // j ≠ k} :=
  ⟨rngBlk k (rngOff p u), fun h => by
    have h' : rngBlk k (rngOff p u) = rngBlk k 0 := by rw [h, rngBlk_zero]
    rw [rngBlk_eq_iff k (rngOff_lt u) (by have := p.n_ge_four; omega)] at h'
    exact (rngOff_pos u).ne' h'⟩

theorem rngBlkNe_bijective (k : ZMod p.n) : Function.Bijective (rngBlkNe k) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro u v h
    have h' : rngBlk k (rngOff p u) = rngBlk k (rngOff p v) := congrArg Subtype.val h
    rw [rngBlk_eq_iff k (rngOff_lt u) (rngOff_lt v)] at h'
    exact rngOff_injective h'
  · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_subtype,
      Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card]
    have := p.n_ge_four
    omega

/-- The sites off block `k`: layer sites `(a, i) ↦ (k + rngLayerOff a, i)`, path sites
`(j, i) ↦ (k + j + 2, i)`. -/
def rngSiteEquiv (k : ZMod p.n) :
    (Fin 2 × Fin p.W) ⊕ (Fin (p.n - 3) × Fin p.W) ≃ OffBlockSite p k :=
  (Equiv.sumProdDistrib _ _ _).symm.trans
    (((Equiv.ofBijective _ (rngBlkNe_bijective k)).prodCongr (Equiv.refl _)).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun j : ZMod p.n => j ≠ k)).symm)

theorem rngSiteEquiv_inl (k : ZMod p.n) (a : Fin 2) (i : Fin p.W) :
    (rngSiteEquiv k (.inl (a, i))).1 = (rngBlk k (rngLayerOff p a), i) := rfl

theorem rngSiteEquiv_inr (k : ZMod p.n) (j : Fin (p.n - 3)) (i : Fin p.W) :
    (rngSiteEquiv k (.inr (j, i))).1 = (rngBlk k (j.val + 2), i) := rfl

/-- The sites of block `k` as the port of the common-port layer. -/
def rngPortEquiv (k : ZMod p.n) : Fin 1 × Fin p.W ≃ BlockSite p k where
  toFun x := ⟨(k, x.2), rfl⟩
  invFun y := (0, y.1.2)
  left_inv x := by
    obtain ⟨j, a⟩ := x
    simp only [Prod.mk.injEq, and_true]
    exact (Fin.fin_one_eq_zero j).symm
  right_inv y := by
    obtain ⟨⟨j, a⟩, hy⟩ := y
    simp only at hy
    subst hy
    rfl

theorem rngPortEquiv_val (k : ZMod p.n) (x : Fin 1 × Fin p.W) :
    (rngPortEquiv k x).1 = (rngBlk k 0, x.2) := by
  rw [rngBlk_zero]; rfl

/-- **The split of the ring sample** relative to the removed block `k`: the common-port layer
(blocks `A_{k+1}, A_{k-1}`, bonds `B_kᴴ, B_{k-1}` to the port `k`) and the path of the `n - 3`
middle blocks `A_{k+2+i}` (bonds `B_{k+2+i}`, port bonds `B_{k+1}ᴴ`, `B_{k-2}`). -/
def rngSplit (k : ZMod p.n) (ω : RngSample p) :
    LayerSample p.W .common × PathSample p.W (p.n - 3) :=
  ((fun a => ω.1 (rngBlk k (rngLayerOff p a)),
      fun a _ => if a = 0 then (ω.2 (rngBlk k 0))ᴴ else ω.2 (rngBlk k (p.n - 1))),
    (fun i => ω.1 (rngBlk k (i.val + 2)), fun i => ω.2 (rngBlk k (i.val + 2)),
      fun j => if j = 0 then (ω.2 (rngBlk k 1))ᴴ else ω.2 (rngBlk k (p.n - 2))))

end Split

/-!
## 4. The split is measure preserving
-/

section SplitLaw

variable {p : Parameters}

theorem rng_ofBijective_reindex {ι : Type*} [Fintype ι] {β : Type*} [MeasurableSpace β]
    (μ : Measure β) [IsProbabilityMeasure μ] {g : ι → ZMod p.n} (hg : Function.Bijective g) :
    MeasurePreserving (fun (f : ZMod p.n → β) (i : ι) => f (g i))
      (Measure.pi fun _ : ZMod p.n => μ) (Measure.pi fun _ : ι => μ) := by
  have h := pg_mp_reindex μ (Equiv.ofBijective g hg).symm
  simpa using h

theorem rng_mp_sum_split {ι ι' : Type*} [Fintype ι] [Fintype ι'] {β : Type*}
    [MeasurableSpace β] (μ : Measure β) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun (f : ι ⊕ ι' → β) => (fun i => f (.inl i), fun i => f (.inr i)))
      (Measure.pi fun _ : ι ⊕ ι' => μ)
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι' => μ)) :=
  measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι' => μ)

/-- Offsets of the blocks in the order `k`, layer blocks, path blocks. -/
def rngBlkIdx (k : ZMod p.n) : Fin 1 ⊕ (Fin 2 ⊕ Fin (p.n - 3)) → ZMod p.n
  | .inl _ => rngBlk k 0
  | .inr u => rngBlk k (rngOff p u)

theorem rngBlkIdx_bijective (k : ZMod p.n) : Function.Bijective (rngBlkIdx k) := by
  have h4 := p.n_ge_four
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · rintro (x | u) (y | v) h <;> simp only [rngBlkIdx] at h
    · rw [Fin.fin_one_eq_zero x, Fin.fin_one_eq_zero y]
    · rw [rngBlk_eq_iff k (by omega) (rngOff_lt v)] at h
      exact absurd h.symm (rngOff_pos v).ne'
    · rw [rngBlk_eq_iff k (rngOff_lt u) (by omega)] at h
      exact absurd h (rngOff_pos u).ne'
    · rw [rngBlk_eq_iff k (rngOff_lt u) (rngOff_lt v)] at h
      rw [rngOff_injective h]
  · simp only [Fintype.card_sum, Fintype.card_fin, ZMod.card]
    omega

/-- Offsets of the bonds: layer bonds `k, k-1`; internal path bonds `k+2+i`; path port bonds
`k+1, k-2`. -/
def rngBondOff : Fin 2 ⊕ (Fin (p.n - 3 - 1) ⊕ Fin 2) → ℕ
  | .inl a => if a = 0 then 0 else p.n - 1
  | .inr (.inl i) => i.val + 2
  | .inr (.inr j) => if j = 0 then 1 else p.n - 2

theorem rngBondOff_lt (u : Fin 2 ⊕ (Fin (p.n - 3 - 1) ⊕ Fin 2)) : rngBondOff u < p.n := by
  have := p.n_ge_four
  rcases u with a | i | j
  · simp only [rngBondOff]; split_ifs <;> omega
  · simp only [rngBondOff]; omega
  · simp only [rngBondOff]; split_ifs <;> omega

theorem rng_fin2_eq {a a' : Fin 2} (ha : a ≠ 0) (ha' : a' ≠ 0) : a = a' := by
  have h1 : a.val ≠ 0 := fun e => ha (Fin.ext e)
  have h2 : a'.val ≠ 0 := fun e => ha' (Fin.ext e)
  exact Fin.ext (by have := a.isLt; have := a'.isLt; omega)

theorem rngBondOff_injective : Function.Injective (rngBondOff (p := p)) := by
  have := p.n_ge_four
  rintro (a | i | j) (a' | i' | j') h <;> simp only [rngBondOff] at h
  · congr 1
    by_cases ha : a = 0 <;> by_cases ha' : a' = 0
    · rw [ha, ha']
    · rw [ite_eq_left ha, ite_eq_right ha'] at h; omega
    · rw [ite_eq_right ha, ite_eq_left ha'] at h; omega
    · exact rng_fin2_eq ha ha'
  · exfalso; have := i'.isLt; split_ifs at h; omega
  · exfalso; split_ifs at h <;> omega
  · exfalso; have := i.isLt; split_ifs at h; omega
  · congr 2; exact Fin.ext (by omega)
  · exfalso; have := i.isLt; split_ifs at h <;> omega
  · exfalso; split_ifs at h <;> omega
  · exfalso; have := i'.isLt; split_ifs at h <;> omega
  · congr 2
    by_cases ha : j = 0 <;> by_cases ha' : j' = 0
    · rw [ha, ha']
    · rw [ite_eq_left ha, ite_eq_right ha'] at h; omega
    · rw [ite_eq_right ha, ite_eq_left ha'] at h; omega
    · exact rng_fin2_eq ha ha'

theorem rngBondIdx_bijective (k : ZMod p.n) :
    Function.Bijective (fun u : Fin 2 ⊕ (Fin (p.n - 3 - 1) ⊕ Fin 2) => rngBlk k (rngBondOff u)) := by
  have h4 := p.n_ge_four
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro u v h
    rw [rngBlk_eq_iff k (rngBondOff_lt u) (rngBondOff_lt v)] at h
    exact rngBondOff_injective h
  · simp only [Fintype.card_sum, Fintype.card_fin, ZMod.card]
    omega

/-- The rearrangement `((a,b),(c,d)) ↦ ((a,c),(b,d))` is measure preserving. -/
theorem rng_mp_rearrange {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ)
    (μd : Measure δ) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun x : (α × β) × (γ × δ) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := pg_mp_rearrange μa μb μc μd
  have h2 := (MeasurePreserving.id (μa.prod μc)).prod
    (Measure.measurePreserving_swap (μ := μd) (ν := μb))
  exact h2.comp h1

theorem rng_mp_conj_or_id (t : ℝ≥0) (c : Bool) :
    MeasurePreserving (fun B : Matrix (Fin p.W) (Fin p.W) ℂ => if c then Bᴴ else B)
      (ginibreMeasure (Fin p.W) (Fin p.W) t) (ginibreMeasure (Fin p.W) (Fin p.W) t) := by
  cases c
  · exact MeasurePreserving.id _
  · exact pg_mp_conjTranspose_ginibre t

/-- **The split of the ring sample is measure preserving**:
`rngLaw p ∘ (rngSplit k)⁻¹ = layerLaw W b .common ⊗ pathLaw W (n-3) b`. -/
theorem rng_mp_split (k : ZMod p.n) :
    MeasurePreserving (rngSplit k) (rngLaw p)
      ((layerLaw p.W p.b .common).prod (pathLaw p.W (p.n - 3) p.b)) := by
  have := fun t => isProbabilityMeasure_gueMeasure p.W t
  set μA := gueMeasure (Fin p.W) (Real.toNNReal ((1 - 2 * p.b) / p.W)) with hμA
  set μB := ginibreMeasure (Fin p.W) (Fin p.W) (Real.toNNReal (p.b / p.W)) with hμB
  -- blocks
  have hA1 := rng_ofBijective_reindex μA (rngBlkIdx_bijective k)
  have hA2 := rng_mp_sum_split (ι := Fin 1) (ι' := Fin 2 ⊕ Fin (p.n - 3)) μA
  have hA3 := measurePreserving_snd (μ := Measure.pi fun _ : Fin 1 => μA)
    (ν := Measure.pi fun _ : Fin 2 ⊕ Fin (p.n - 3) => μA)
  have hA4 := rng_mp_sum_split (ι := Fin 2) (ι' := Fin (p.n - 3)) μA
  have hA := hA4.comp (hA3.comp (hA2.comp hA1))
  -- bonds
  have hB1 := rng_ofBijective_reindex μB (rngBondIdx_bijective k)
  have hB2 := rng_mp_sum_split (ι := Fin 2) (ι' := Fin (p.n - 3 - 1) ⊕ Fin 2) μB
  have hB3 := (MeasurePreserving.id (Measure.pi fun _ : Fin 2 => μB)).prod
    (rng_mp_sum_split (ι := Fin (p.n - 3 - 1)) (ι' := Fin 2) μB)
  have hL : MeasurePreserving
      (fun (f : Fin 2 → Matrix (Fin p.W) (Fin p.W) ℂ) (a : Fin 2) (_ : Fin 1) =>
        if decide (a = 0) then (f a)ᴴ else f a)
      (Measure.pi fun _ : Fin 2 => μB) (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 1 => μB) := by
    refine measurePreserving_pi (fun _ : Fin 2 => μB) (fun _ : Fin 2 => Measure.pi fun _ : Fin 1 => μB)
      (f := fun (a : Fin 2) (B : Matrix (Fin p.W) (Fin p.W) ℂ) (_ : Fin 1) =>
        if decide (a = 0) then Bᴴ else B) fun a => ?_
    have h1 := (measurePreserving_funUnique μB (Fin 1)).symm
    exact h1.comp (rng_mp_conj_or_id _ (decide (a = 0)))
  have hP : MeasurePreserving
      (fun (f : Fin 2 → Matrix (Fin p.W) (Fin p.W) ℂ) (j : Fin 2) =>
        if decide (j = 0) then (f j)ᴴ else f j)
      (Measure.pi fun _ : Fin 2 => μB) (Measure.pi fun _ : Fin 2 => μB) :=
    measurePreserving_pi _ _ fun j => rng_mp_conj_or_id _ (decide (j = 0))
  have hB4 := hL.prod ((MeasurePreserving.id (Measure.pi fun _ : Fin (p.n - 3 - 1) => μB)).prod hP)
  have hB := hB4.comp (hB3.comp (hB2.comp hB1))
  have hR := rng_mp_rearrange (Measure.pi fun _ : Fin 2 => μA)
    (Measure.pi fun _ : Fin (p.n - 3) => μA)
    (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 1 => μB)
    ((Measure.pi fun _ : Fin (p.n - 3 - 1) => μB).prod (Measure.pi fun _ : Fin 2 => μB))
  have hall := hR.comp (hA.prod hB)
  unfold rngLaw layerLaw pathLaw
  convert hall using 1
  funext ω
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext a; rfl
  · funext a x
    by_cases ha : a = 0
    · subst ha; simp [rngSplit, rngBondOff]
    · simp [rngSplit, rngBondOff, ha]
  · funext i; rfl
  · funext i; rfl
  · funext j
    by_cases hj : j = 0
    · subst hj; simp [rngSplit, rngBondOff]
    · simp [rngSplit, rngBondOff, hj]

end SplitLaw

/-!
## 5. Deterministic Schur composition of the one-block complement
-/

section Schur

variable {p : Parameters}

theorem rng_fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h
  · exact Or.inl h
  · exact Or.inr h

@[simp] theorem rngLayerOff_zero : rngLayerOff p 0 = 1 := rfl

@[simp] theorem rngLayerOff_one : rngLayerOff p 1 = p.n - 1 := rfl

/-- The path block `H_R` of `oneBlockComplement`. -/
def rngHR (k : ZMod p.n) (H : p.SiteMatrix) : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ :=
  fun x y => H x.1 y.1

/-- The coupling `C = H_{R,k}` of `oneBlockComplement`. -/
def rngC (k : ZMod p.n) (H : p.SiteMatrix) : Matrix (OffBlockSite p k) (BlockSite p k) ℂ :=
  fun x y => H x.1 y.1

theorem rng_oneBlockComplement_eq (k : ZMod p.n) (H : p.SiteMatrix) (E : ℝ) :
    oneBlockComplement p k H E = (rngC k H)ᴴ * (rngHR k H - (E : ℂ) • 1)⁻¹ * rngC k H := rfl

/-- Path-to-layer entries: the port coupling of the middle path. -/
theorem rng_entry_path_layer (ω : RngSample p) (k : ZMod p.n) (j : Fin (p.n - 3))
    (a : Fin 2) (i i' : Fin p.W) :
    rngAssemble p ω (rngBlk k (j.val + 2), i) (rngBlk k (rngLayerOff p a), i') =
      pathPortCoupling (rngSplit k ω).2 (j, i) (a, i') := by
  have h4 := p.n_ge_four
  have hj := j.isLt
  rcases rng_fin2_cases a with rfl | rfl
  · rw [rngLayerOff_zero, rngAssemble_off ω k (by omega) (by omega)]
    simp only [pathPortCoupling, rngSplit, true_and, Fin.isValue]
    by_cases h0 : j.val = 0
    · simp [h0, conjTranspose_apply]
    · simp [h0]
  · rw [rngLayerOff_one, rngAssemble_off ω k (by omega) (by omega)]
    simp only [pathPortCoupling, rngSplit, Fin.isValue]
    by_cases h0 : j.val + 1 = p.n - 3
    · have h2 : j.val + 2 = p.n - 2 := by omega
      have h3 : p.n - 1 = j.val + 2 + 1 := by omega
      simp [h0, h3]
      rw [h2]
    · simp [h0]
      split_ifs <;> first | rfl | (exfalso; omega)

theorem rngBlk_layer_ne_path (k : ZMod p.n) (a : Fin 2) (j : Fin (p.n - 3)) :
    rngBlk k (rngLayerOff p a) ≠ rngBlk k (j.val + 2) := by
  have h4 := p.n_ge_four
  have hj := j.isLt
  have hlt : rngLayerOff p a < p.n := rngOff_lt (.inl a)
  rw [Ne, rngBlk_eq_iff k hlt (by omega)]
  rcases rng_fin2_cases a with rfl | rfl
  · simp only [rngLayerOff_zero]; omega
  · simp only [rngLayerOff_one]; omega

/-- Layer-to-layer entries: the block-diagonal `diag(A_{k+1}, A_{k-1})`. -/
theorem rng_entry_layer_layer (ω : RngSample p) (k : ZMod p.n) (a a' : Fin 2) (i i' : Fin p.W) :
    rngAssemble p ω (rngBlk k (rngLayerOff p a), i) (rngBlk k (rngLayerOff p a'), i') =
      Internal.Contracts.Layers.blockDiag (rngSplit k ω).1.1 (a, i) (a', i') := by
  have h4 := p.n_ge_four
  rw [rngAssemble_off ω k (o₁ := rngLayerOff p a) (o₂ := rngLayerOff p a')
    (rngOff_lt (.inl a)) (rngOff_lt (.inl a'))]
  simp only [Internal.Contracts.Layers.blockDiag, rngSplit]
  rcases rng_fin2_cases a with rfl | rfl <;> rcases rng_fin2_cases a' with rfl | rfl <;>
    simp <;> split_ifs <;> first | rfl | (exfalso; omega)

/-- Path-to-path entries: the path matrix of the middle blocks. -/
theorem rng_entry_path_path (ω : RngSample p) (k : ZMod p.n) (j j' : Fin (p.n - 3))
    (i i' : Fin p.W) :
    rngAssemble p ω (rngBlk k (j.val + 2), i) (rngBlk k (j'.val + 2), i') =
      pathMatrix (rngSplit k ω).2 (j, i) (j', i') := by
  have h4 := p.n_ge_four
  have hj := j.isLt
  have hj' := j'.isLt
  rw [rngAssemble_off ω k (by omega) (by omega)]
  simp only [pathMatrix, rngSplit, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Layer-to-path entries (the conjugate of `rng_entry_path_layer`). -/
theorem rng_entry_layer_path (ω : RngSample p) (k : ZMod p.n) (a : Fin 2) (j : Fin (p.n - 3))
    (i i' : Fin p.W) :
    rngAssemble p ω (rngBlk k (rngLayerOff p a), i) (rngBlk k (j.val + 2), i') =
      (pathPortCoupling (rngSplit k ω).2)ᴴ (a, i) (j, i') := by
  rw [conjTranspose_apply, ← rng_entry_path_layer,
    rngAssemble_star_of_ne ω _ _ (Ne.symm (rngBlk_layer_ne_path k a j))]

/-- Layer-to-port entries: the common-port bond matrix `(B_kᴴ; B_{k-1})`. -/
theorem rng_entry_layer_port (ω : RngSample p) (k : ZMod p.n) (a : Fin 2) (x : Fin 1 × Fin p.W)
    (i : Fin p.W) :
    rngAssemble p ω (rngBlk k (rngLayerOff p a), i) (rngBlk k 0, x.2) =
      bondMatrix .common (rngSplit k ω).1.2 (a, i) x := by
  have h4 := p.n_ge_four
  rw [rngAssemble_off ω k (o₁ := rngLayerOff p a) (o₂ := 0) (rngOff_lt (.inl a)) (by omega)]
  simp only [bondMatrix, LayerShape.incident, rngSplit, ite_true]
  rcases rng_fin2_cases a with rfl | rfl
  · simp [conjTranspose_apply]
    intro h; omega
  · simp only [rngLayerOff_one]
    have h1 : ¬ (p.n - 1 = 0) := by omega
    have h3 : p.n - 1 + 1 = p.n := by omega
    simp [h1, h3]

/-- Path-to-port entries vanish. -/
theorem rng_entry_path_port (ω : RngSample p) (k : ZMod p.n) (j : Fin (p.n - 3))
    (x : Fin 1 × Fin p.W) (i : Fin p.W) :
    rngAssemble p ω (rngBlk k (j.val + 2), i) (rngBlk k 0, x.2) = 0 := by
  have h4 := p.n_ge_four
  have hj := j.isLt
  rw [rngAssemble_off ω k (by omega) (by omega)]
  have e1 : ¬ (j.val + 2 = 0) := by omega
  have e2 : ¬ ((0 : ℕ) = j.val + 2 + 1 ∨ (j.val + 2 + 1 = p.n ∧ (0 : ℕ) = 0)) := by omega
  have e3 : ¬ (j.val + 2 = 0 + 1 ∨ (0 + 1 = p.n ∧ j.val + 2 = 0)) := by omega
  rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right e3]

/-- `H_R - E` in the layer ⊕ path decomposition. -/
theorem rng_HR_submatrix (ω : RngSample p) (k : ZMod p.n) (E : ℝ) :
    (rngHR k (rngAssemble p ω) - (E : ℂ) • 1).submatrix (rngSiteEquiv k) (rngSiteEquiv k) =
      Matrix.fromBlocks (Internal.Contracts.Layers.blockDiag (rngSplit k ω).1.1 - (E : ℂ) • 1)
        (pathPortCoupling (rngSplit k ω).2)ᴴ (pathPortCoupling (rngSplit k ω).2)
        (pathMatrix (rngSplit k ω).2 - (E : ℂ) • 1) := by
  rw [show (rngHR k (rngAssemble p ω) - (E : ℂ) • 1).submatrix (rngSiteEquiv k) (rngSiteEquiv k) =
      (rngHR k (rngAssemble p ω)).submatrix (rngSiteEquiv k) (rngSiteEquiv k) -
        (E : ℂ) • (1 : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ).submatrix
          (rngSiteEquiv k) (rngSiteEquiv k) from rfl, submatrix_one_equiv]
  ext (⟨a, i⟩ | ⟨j, i⟩) (⟨a', i'⟩ | ⟨j', i'⟩)
  · simp only [Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, rngHR, rngSiteEquiv_inl,
      fromBlocks_apply₁₁]
    rw [rng_entry_layer_layer]
    simp [one_apply]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, rngHR, rngSiteEquiv_inl,
      rngSiteEquiv_inr, fromBlocks_apply₁₂]
    rw [rng_entry_layer_path]
    simp [one_apply]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, rngHR, rngSiteEquiv_inl,
      rngSiteEquiv_inr, fromBlocks_apply₂₁]
    rw [rng_entry_path_layer]
    simp [one_apply]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, rngHR, rngSiteEquiv_inr,
      fromBlocks_apply₂₂]
    rw [rng_entry_path_path]
    simp [one_apply]

/-- The coupling `C` in the layer ⊕ path decomposition. -/
theorem rng_C_submatrix (ω : RngSample p) (k : ZMod p.n) :
    (rngC k (rngAssemble p ω)).submatrix (rngSiteEquiv k) (rngPortEquiv k) =
      Matrix.fromRows (bondMatrix .common (rngSplit k ω).1.2)
        (0 : Matrix (Fin (p.n - 3) × Fin p.W) (Fin 1 × Fin p.W) ℂ) := by
  ext (⟨a, i⟩ | ⟨j, i⟩) x
  · simp only [submatrix_apply, rngC, rngSiteEquiv_inl, rngPortEquiv_val, fromRows_apply_inl]
    exact rng_entry_layer_port ω k a x i
  · simp only [submatrix_apply, rngC, rngSiteEquiv_inr, rngPortEquiv_val, fromRows_apply_inr,
      Matrix.zero_apply]
    exact rng_entry_path_port ω k j x i

/-- **Deterministic Schur composition** (Step 5): if `H_path - E` and `A - E - X` are
invertible, the one-block complement of the assembled ring at block `k`, reindexed by the port
equivalence, is the common-port layer Schur matrix `B*(A - E - X)⁻¹B` with
`X = pathSchur E π`, `(ℓ, π) = rngSplit k ω`. -/
theorem rng_oneBlockComplement (ω : RngSample p) (k : ZMod p.n) (E : ℝ)
    (hH : IsUnit (pathMatrix (rngSplit k ω).2 - (E : ℂ) • 1).det)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag (rngSplit k ω).1.1 - (E : ℂ) • 1 -
      pathSchur E (rngSplit k ω).2).det) :
    (oneBlockComplement p k (rngAssemble p ω) E).submatrix (rngPortEquiv k) (rngPortEquiv k) =
      layerSchur .common E (pathSchur E (rngSplit k ω).2) (rngSplit k ω).1 := by
  rw [rng_oneBlockComplement_eq, ← submatrix_mul_equiv _ _ _ (rngSiteEquiv k) _,
    ← submatrix_mul_equiv _ _ _ (rngSiteEquiv k) _, ← conjTranspose_submatrix,
    ← inv_submatrix_equiv, rng_HR_submatrix, rng_C_submatrix]
  set ω' := rngSplit k ω
  let _ := invertibleOfIsUnitDet _ hH
  have hS' : IsUnit (Internal.Contracts.Layers.blockDiag ω'.1.1 - (E : ℂ) • 1 -
      (pathPortCoupling ω'.2)ᴴ * ⅟(pathMatrix ω'.2 - (E : ℂ) • 1) * pathPortCoupling ω'.2).det := by
    rw [invOf_eq_nonsing_inv]; exact hS
  let _ := invertibleOfIsUnitDet _ hS'
  let _ := fromBlocks₂₂Invertible (Internal.Contracts.Layers.blockDiag ω'.1.1 - (E : ℂ) • 1)
    (pathPortCoupling ω'.2)ᴴ (pathPortCoupling ω'.2) (pathMatrix ω'.2 - (E : ℂ) • 1)
  rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq, pg_fromRows_sandwich, invOf_eq_nonsing_inv,
    invOf_eq_nonsing_inv]
  rfl

/-- **The normalized trace of `(z - Σ)⁻¹`** is the port trace of the common-port layer
resolvent (under the same invertibility hypotheses). -/
theorem rng_oneBlockTrace_eq (ω : RngSample p) (k : ZMod p.n) (E : ℝ) (z : ℂ)
    (hH : IsUnit (pathMatrix (rngSplit k ω).2 - (E : ℂ) • 1).det)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag (rngSplit k ω).1.1 - (E : ℂ) • 1 -
      pathSchur E (rngSplit k ω).2).det) :
    oneBlockTrace p k ((z • 1 - oneBlockComplement p k (rngAssemble p ω) E)⁻¹) =
      portBlockTrace (layerResolvent .common E z (pathSchur E (rngSplit k ω).2)
        (rngSplit k ω).1) 0 := by
  set Sg := oneBlockComplement p k (rngAssemble p ω) E
  have hsub : ((z • 1 - Sg)⁻¹).submatrix (rngPortEquiv k) (rngPortEquiv k) =
      (layerResolvent .common E z (pathSchur E (rngSplit k ω).2) (rngSplit k ω).1).toBlocks₂₂ := by
    rw [← inv_submatrix_equiv, show (z • 1 - Sg).submatrix (rngPortEquiv k) (rngPortEquiv k) =
        z • (1 : Matrix (BlockSite p k) (BlockSite p k) ℂ).submatrix (rngPortEquiv k)
          (rngPortEquiv k) - Sg.submatrix (rngPortEquiv k) (rngPortEquiv k) from rfl,
      submatrix_one_equiv, rng_oneBlockComplement ω k E hH hS, layerResolvent, layerMatrix,
      pg_toBlocks22_inv _ _ _ _ hS]
    rfl
  unfold oneBlockTrace portBlockTrace
  congr 1
  rw [Matrix.trace, ← Fintype.sum_equiv (rngPortEquiv k) (fun x =>
    ((z • 1 - Sg)⁻¹).submatrix (rngPortEquiv k) (rngPortEquiv k) x x) _ (fun x => rfl), hsub,
    Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

end Schur

/-!
## 6. Transfer of the `L^q` norm
-/

section Transfer

open scoped Matrix.Norms.L2Operator

variable {p : Parameters}

/-- The `.common` instance (the shape-generic one is not found through `Fin σ.blocks`). -/
instance rng_isProbabilityMeasure_layerLaw_common (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (layerLaw W b .common) :=
  pg_isProbabilityMeasure_layerLaw W b .common

/-- The common-port observable `‖W⁻¹Tr 𝒢_port - a‖` at `X = pathSchur E π`, `z = z₀`. -/
def rngPortObs (b E : ℝ) {W r : ℕ} (x : LayerSample W .common × PathSample W r) : ℝ :=
  ‖portBlockTrace (layerResolvent .common E (commonZ b E) (pathSchur E x.2) x.1) 0 - matchedA E‖

theorem rng_layerMatrix_eq_sub {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) :
    layerMatrix σ E z X ω = layerMatrix σ E z 0 ω - Matrix.fromBlocks X 0 0 0 := by
  unfold layerMatrix
  ext (i | i) (j | j) <;> simp

/-- Joint measurability of the layer resolvent in `(ℓ, X)`. -/
theorem rng_measurable_layerResolvent {Ω : Type*} [MeasurableSpace Ω] {W : ℕ} (σ : LayerShape)
    (E : ℝ) (z : ℂ) {Xf : Ω → Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    {ℓf : Ω → LayerSample W σ} (hX : Measurable Xf) (hℓ : Measurable ℓf) :
    Measurable (fun t => layerResolvent σ E z (Xf t) (ℓf t)) := by
  unfold layerResolvent
  simp_rw [rng_layerMatrix_eq_sub σ E z (Xf _)]
  refine measurable_matrix_inv.comp ((measurable_layerMatrix σ E z 0).comp hℓ |>.sub ?_)
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  rcases x with x | x <;> rcases y with y | y
  · simp only [fromBlocks_apply₁₁]; exact pg_entry hX x y
  · simp only [fromBlocks_apply₁₂]; exact measurable_const
  · simp only [fromBlocks_apply₂₁]; exact measurable_const
  · simp only [fromBlocks_apply₂₂]; exact measurable_const

theorem rng_measurable_portObs (b E : ℝ) (W r : ℕ) :
    Measurable (rngPortObs (W := W) (r := r) b E) := by
  have hG := rng_measurable_layerResolvent (Ω := LayerSample W .common × PathSample W r)
    .common E (commonZ b E) ((measurable_pathSchur W r E).comp measurable_snd) measurable_fst
  unfold rngPortObs portBlockTrace
  exact ((measurable_const.mul (Finset.measurable_sum _ fun a _ => pg_entry hG _ _)).sub
    measurable_const).norm

theorem rng_measurable_oneBlockObs (k : ZMod p.n) (E : ℝ) (z : ℂ) :
    Measurable (fun H : p.SiteMatrix =>
      ‖oneBlockTrace p k ((z • 1 - oneBlockComplement p k H E)⁻¹) - matchedA E‖) := by
  have hHR : Measurable (fun H : p.SiteMatrix => rngHR k H) :=
    measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
      (measurable_pi_apply y.1).comp (measurable_pi_apply x.1)
  have hC : Measurable (fun H : p.SiteMatrix => rngC k H) :=
    measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
      (measurable_pi_apply y.1).comp (measurable_pi_apply x.1)
  have hS : Measurable (fun H : p.SiteMatrix => oneBlockComplement p k H E) := by
    simp_rw [rng_oneBlockComplement_eq]
    exact srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose hC)
      (measurable_matrix_inv.comp (hHR.sub measurable_const))) hC
  have hR : Measurable (fun H : p.SiteMatrix => (z • 1 - oneBlockComplement p k H E)⁻¹) :=
    measurable_matrix_inv.comp (measurable_const.sub hS)
  unfold oneBlockTrace Matrix.trace
  exact ((measurable_const.mul (Finset.measurable_sum _ fun a _ => pg_entry hR _ _)).sub
    measurable_const).norm

/-- Both invertibility hypotheses of `rng_oneBlockTrace_eq` hold a.s. under
`layerLaw ⊗ pathLaw`. -/
theorem rng_ae_invertible {W r : ℕ} {b : ℝ} (hb : b < 1 / 2) (E : ℝ) :
    ∀ᵐ x ∂(layerLaw W b .common).prod (pathLaw W r b),
      IsUnit (pathMatrix x.2 - (E : ℂ) • 1).det ∧
        IsUnit (Internal.Contracts.Layers.blockDiag x.1.1 - (E : ℂ) • 1 - pathSchur E x.2).det := by
  have h1 : ∀ᵐ x ∂(layerLaw W b .common).prod (pathLaw W r b),
      IsUnit (pathMatrix x.2 - (E : ℂ) • 1).det :=
    (Measure.quasiMeasurePreserving_snd).ae (ae_isUnit_det_pathMatrix W r hb E)
  have hm : Measurable (fun x : LayerSample W .common × PathSample W r =>
      (Internal.Contracts.Layers.blockDiag x.1.1 - (E : ℂ) • 1 - pathSchur E x.2).det) := by
    have hD : Measurable (fun x : LayerSample W .common × PathSample W r =>
        Internal.Contracts.Layers.blockDiag x.1.1) :=
      (srec_continuous_blockDiag 2 W).measurable.comp (measurable_fst.comp measurable_fst)
    exact (continuous_id.matrix_det).measurable.comp
      ((hD.sub measurable_const).sub ((measurable_pathSchur W r E).comp measurable_snd))
  have hset : MeasurableSet {x : LayerSample W .common × PathSample W r |
      IsUnit (Internal.Contracts.Layers.blockDiag x.1.1 - (E : ℂ) • 1 - pathSchur E x.2).det} := by
    simp_rw [isUnit_iff_ne_zero]
    exact hm (measurableSet_singleton 0).compl
  have h2 : ∀ᵐ x ∂(layerLaw W b .common).prod (pathLaw W r b),
      IsUnit (Internal.Contracts.Layers.blockDiag x.1.1 - (E : ℂ) • 1 - pathSchur E x.2).det := by
    rw [Measure.ae_prod_iff_ae_ae hset, Measure.ae_ae_comm hset]
    exact Filter.Eventually.of_forall fun π => srec_ae_isUnit_top hb .common E (pathSchur E π)
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

/-- **Transfer** (Step 5, exact law identity): the `L^q(model.law)` norm of
`‖W⁻¹Tr(z₀ - Σ)⁻¹ - a‖` for the one-block complement at block `k` equals the
`L^q(layerLaw .common ⊗ pathLaw (n-3))` norm of the common-port observable `rngPortObs`. -/
theorem rng_eLpNorm_commonPort (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ)
    (q : ℝ≥0∞) :
    eLpNorm (fun H => ‖oneBlockTrace p k ((commonZ p.b E • 1 - oneBlockComplement p k H E)⁻¹) -
        matchedA E‖) q (model.law : Measure p.SiteMatrix) =
      eLpNorm (rngPortObs p.b E) q
        ((layerLaw p.W p.b .common).prod (pathLaw p.W (p.n - 3) p.b)) := by
  rw [rng_law_eq_map model, eLpNorm_map_measure
    (rng_measurable_oneBlockObs k E (commonZ p.b E)).aestronglyMeasurable
    rng_measurable_assemble.aemeasurable,
    ← eLpNorm_comp_measurePreserving (rng_measurable_portObs p.b E p.W (p.n - 3)).aestronglyMeasurable
      (rng_mp_split k)]
  refine eLpNorm_congr_ae ?_
  filter_upwards [(rng_mp_split k).quasiMeasurePreserving.ae (rng_ae_invertible p.b_lt_half E)]
    with ω hω
  simp only [Function.comp_apply, rngPortObs]
  rw [rng_oneBlockTrace_eq ω k E _ hω.1 hω.2]

end Transfer

end BlockBand.Layers
