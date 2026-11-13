module

public import BlockBand.Counting.ComplexGaussianWick
public import BlockBand.DeterminantScore.Statements
public import BlockBand.DeterminantScore.RowRealTrace

/-!
# Gaussian row moments for the signed row spread

* `coarea_circularVectorLaw_eq`: the standard circular law `CoareaPalm.circularVectorLaw ι`
  (a pushforward of the real product law on `ι × Fin 2`) is the pushforward of
  `Counting.circularVectorLaw ι` (product over `ι` of the planar standard law) under
  `Counting.circularVector`; this lets the Wick identities of `Counting.ComplexGaussianWick`
  act on the row law of `rowLaw`.
* `rowLaw_eq_map`: `rowLaw k t` is the image of `N(0,t) ⊗ Counting.circularVectorLaw (Fin k)`
  under `(x, z) ↦ (x, √t · g(z))`.
* `wick_one`, `wick_two`: for Hermitian `A, B` the real quadratic forms `Re(g*Ag)` are integrable
  with `E Re(g*Ag) = Tr A` and `E Re(g*Ag) Re(g*Bg) = Tr A Tr B + Tr AB` (real parts).
* `HasInt`: the pair "integrable with integral `c`", closed under sums, scalar multiples and
  products over a product measure, used to integrate the row polynomial term by term.

All statements hold for every finite index type and every variance; no limit occurs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SignedRowSpread

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

/-!
## The two presentations of the standard circular law
-/

theorem continuous_circularVector (ι : Type*) :
    Continuous (BlockBand.Counting.circularVector (ι := ι)) := by
  apply continuous_pi
  intro a
  change Continuous fun z : ι → ℝ × ℝ =>
    ((z a).1 : ℂ) + Complex.I * ((z a).2 : ℂ)
  fun_prop

/-- `CoareaPalm.circularVectorLaw ι = (Counting.circularVectorLaw ι).map circularVector`. -/
theorem coarea_circularVectorLaw_eq (ι : Type*) [Fintype ι] :
    BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw ι =
      (BlockBand.Counting.circularVectorLaw ι).map BlockBand.Counting.circularVector := by
  classical
  set μ : Measure ℝ := gaussianReal 0 (1 / 2 : ℝ≥0) with hμ
  have hcurry : (Measure.pi fun _ : ι × Fin 2 => μ).map (MeasurableEquiv.curry ι (Fin 2) ℝ) =
      Measure.pi fun _ : ι => Measure.pi fun _ : Fin 2 => μ := by
    have h := Measure.infinitePi_map_curry (fun (_ : ι) (_ : Fin 2) => μ)
    simpa only [Measure.infinitePi_eq_pi] using h
  have hpair : MeasurePreserving
      (fun (c : ι → Fin 2 → ℝ) a => MeasurableEquiv.finTwoArrow (c a))
      (Measure.pi fun _ : ι => Measure.pi fun _ : Fin 2 => μ)
      (Measure.pi fun _ : ι => μ.prod μ) :=
    measurePreserving_pi _ _ (fun _ => measurePreserving_finTwoArrow μ)
  have he : (Measure.pi fun _ : ι × Fin 2 => μ).map
      (fun r a => (r (a, 0), r (a, 1))) = BlockBand.Counting.circularVectorLaw ι := by
    have hfun : (fun (r : ι × Fin 2 → ℝ) a => (r (a, 0), r (a, 1))) =
        (fun (c : ι → Fin 2 → ℝ) a => MeasurableEquiv.finTwoArrow (c a)) ∘
          (MeasurableEquiv.curry ι (Fin 2) ℝ) := by
      funext r a
      rfl
    rw [hfun, ← Measure.map_map hpair.measurable (MeasurableEquiv.measurable _), hcurry,
      hpair.map_eq]
    rfl
  have hm : Measurable (fun (r : ι × Fin 2 → ℝ) (a : ι) => (r (a, 0), r (a, 1))) := by
    fun_prop
  rw [← he, Measure.map_map (continuous_circularVector ι).measurable hm]
  change (Measure.pi fun _ : ι × Fin 2 => μ).map _ = _
  congr 1
  funext r a
  simp only [Function.comp_apply, BlockBand.Counting.circularVector,
    BlockBand.Counting.circularGaussianCoordinate]
  ring

/-- The row law as an image of `N(0,t) ⊗ Counting.circularVectorLaw (Fin k)`. -/
theorem rowLaw_eq_map (k : ℕ) (t : ℝ≥0) :
    rowLaw k t = ((gaussianReal 0 t).prod (BlockBand.Counting.circularVectorLaw (Fin k))).map
      (Prod.map id fun z => (Real.sqrt (t : ℝ) : ℂ) • BlockBand.Counting.circularVector z) := by
  have hs : Measurable fun g : Fin k → ℂ => (Real.sqrt (t : ℝ) : ℂ) • g :=
    (continuous_const_smul _).measurable
  unfold rowLaw
  rw [coarea_circularVectorLaw_eq, Measure.map_map hs (continuous_circularVector _).measurable]
  conv_lhs => rw [← Measure.map_id (μ := gaussianReal 0 t)]
  rw [Measure.map_prod_map _ _ measurable_id (hs.comp (continuous_circularVector _).measurable)]
  rfl

/-!
## Quadratic forms
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dotProduct_mulVec_eq_complexQuadraticForm (A : Matrix ι ι ℂ) (g : ι → ℂ) :
    star g ⬝ᵥ (A *ᵥ g) = BlockBand.Counting.complexQuadraticForm A g := by
  simp only [dotProduct, mulVec, BlockBand.Counting.complexQuadraticForm, Finset.mul_sum,
    Pi.star_apply, Complex.star_def]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quad_smul_ofReal (A : Matrix ι ι ℂ) (c : ℝ) (g : ι → ℂ) :
    star ((c : ℂ) • g) ⬝ᵥ (A *ᵥ ((c : ℂ) • g)) = ((c ^ 2 : ℝ) : ℂ) * (star g ⬝ᵥ (A *ᵥ g)) := by
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  push_cast
  ring

/-- Real part of a scaled quadratic form: `Re((√t g)*A(√t g)) = t Re(g*Ag)`. -/
theorem quad_re_sqrt_smul (A : Matrix ι ι ℂ) (t : ℝ) (ht : 0 ≤ t) (g : ι → ℂ) :
    (star ((Real.sqrt t : ℂ) • g) ⬝ᵥ (A *ᵥ ((Real.sqrt t : ℂ) • g))).re =
      t * (star g ⬝ᵥ (A *ᵥ g)).re := by
  rw [quad_smul_ofReal, Real.sq_sqrt ht, Complex.re_ofReal_mul]

theorem quad_im_eq_zero (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (g : ι → ℂ) :
    (star g ⬝ᵥ (A *ᵥ g)).im = 0 := by
  rw [Row.hermitian_quadratic_eq_ofReal A hA g]
  simp

theorem trace_im_eq_zero (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : A.trace.im = 0 := by
  rw [Row.hermitian_trace_eq_ofReal A hA]
  simp

/-!
## Real Wick identities on the circular law
-/

/-- `E Re(g*Ag) = Re Tr A`, with integrability. -/
theorem wick_one (A : Matrix ι ι ℂ) :
    Integrable (fun z => (star (BlockBand.Counting.circularVector z) ⬝ᵥ
        (A *ᵥ BlockBand.Counting.circularVector z)).re) (BlockBand.Counting.circularVectorLaw ι) ∧
      (∫ z, (star (BlockBand.Counting.circularVector z) ⬝ᵥ
        (A *ᵥ BlockBand.Counting.circularVector z)).re
        ∂BlockBand.Counting.circularVectorLaw ι) = A.trace.re := by
  simp_rw [dotProduct_mulVec_eq_complexQuadraticForm]
  have hi := BlockBand.Counting.integrable_actualComplexQuadratic A
  refine ⟨hi.re, ?_⟩
  have h := integral_re hi
  simp only [RCLike.re_to_complex] at h
  rw [h, BlockBand.Counting.integral_actualComplexQuadratic_eq_trace]

/-- For Hermitian `A, B`: `E Re(g*Ag) Re(g*Bg) = Re Tr A Re Tr B + Re Tr AB`. -/
theorem wick_two (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Integrable (fun z => (star (BlockBand.Counting.circularVector z) ⬝ᵥ
        (A *ᵥ BlockBand.Counting.circularVector z)).re *
        (star (BlockBand.Counting.circularVector z) ⬝ᵥ
        (B *ᵥ BlockBand.Counting.circularVector z)).re)
        (BlockBand.Counting.circularVectorLaw ι) ∧
      (∫ z, (star (BlockBand.Counting.circularVector z) ⬝ᵥ
        (A *ᵥ BlockBand.Counting.circularVector z)).re *
        (star (BlockBand.Counting.circularVector z) ⬝ᵥ
        (B *ᵥ BlockBand.Counting.circularVector z)).re
        ∂BlockBand.Counting.circularVectorLaw ι) =
        A.trace.re * B.trace.re + (A * B).trace.re := by
  have hpt : ∀ z : ι → ℝ × ℝ,
      (star (BlockBand.Counting.circularVector z) ⬝ᵥ
        (A *ᵥ BlockBand.Counting.circularVector z)).re *
        (star (BlockBand.Counting.circularVector z) ⬝ᵥ
        (B *ᵥ BlockBand.Counting.circularVector z)).re =
      (BlockBand.Counting.complexQuadraticForm A (BlockBand.Counting.circularVector z) *
        BlockBand.Counting.complexQuadraticForm B (BlockBand.Counting.circularVector z)).re := by
    intro z
    rw [← dotProduct_mulVec_eq_complexQuadraticForm, ← dotProduct_mulVec_eq_complexQuadraticForm,
      Complex.mul_re, quad_im_eq_zero A hA, quad_im_eq_zero B hB]
    ring
  simp_rw [hpt]
  have hi := BlockBand.Counting.integrable_actualComplexQuadratic_mul A B
  refine ⟨hi.re, ?_⟩
  have h := integral_re hi
  simp only [RCLike.re_to_complex] at h
  rw [h, BlockBand.Counting.integral_actualComplexQuadratic_mul_eq_trace, Complex.add_re,
    Complex.mul_re, trace_im_eq_zero A hA]
  ring

/-!
## Term-by-term integration
-/

/-- `F` is integrable with integral `c`. -/
def HasInt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → ℝ) (c : ℝ) : Prop :=
  Integrable F P ∧ ∫ ω, F ω ∂P = c

section HasInt

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem HasInt.add {F G : Ω → ℝ} {c d : ℝ} (hF : HasInt P F c) (hG : HasInt P G d) :
    HasInt P (fun ω => F ω + G ω) (c + d) :=
  ⟨hF.1.add hG.1, by rw [integral_add hF.1 hG.1, hF.2, hG.2]⟩

theorem HasInt.sub {F G : Ω → ℝ} {c d : ℝ} (hF : HasInt P F c) (hG : HasInt P G d) :
    HasInt P (fun ω => F ω - G ω) (c - d) :=
  ⟨hF.1.sub hG.1, by rw [integral_sub hF.1 hG.1, hF.2, hG.2]⟩

theorem HasInt.const_mul {F : Ω → ℝ} {c : ℝ} (hF : HasInt P F c) (r : ℝ) :
    HasInt P (fun ω => r * F ω) (r * c) :=
  ⟨hF.1.const_mul r, by rw [integral_const_mul, hF.2]⟩

theorem HasInt.congr {F G : Ω → ℝ} {c d : ℝ} (hF : HasInt P F c) (hFG : ∀ ω, F ω = G ω)
    (hcd : c = d) : HasInt P G d := by
  have : F = G := funext hFG
  subst this hcd
  exact hF

theorem hasInt_const [IsProbabilityMeasure P] (c : ℝ) : HasInt P (fun _ => c) c :=
  ⟨integrable_const c, by simp⟩

theorem HasInt.prod {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [SFinite P] [SFinite Q]
    {f : Ω → ℝ} {h : Ω' → ℝ} {a b : ℝ} (hf : HasInt P f a) (hh : HasInt Q h b) :
    HasInt (P.prod Q) (fun z => f z.1 * h z.2) (a * b) :=
  ⟨hf.1.mul_prod hh.1, by rw [integral_prod_mul, hf.2, hh.2]⟩

end HasInt

/-!
## Moments of the diagonal coordinate
-/

theorem hasInt_gauss_shift (v : ℝ≥0) (m : ℝ) :
    HasInt (gaussianReal 0 v) (fun x => m + x) m := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl
  refine ⟨(integrable_const m).add hid, ?_⟩
  rw [integral_add (integrable_const m) hid, integral_const, integral_id_gaussianReal]
  simp

theorem hasInt_gauss_shift_sq (v : ℝ≥0) (m : ℝ) :
    HasInt (gaussianReal 0 v) (fun x => (m + x) ^ 2) (m ^ 2 + v) := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := v) (2 : ℝ≥0)).integrable_norm_pow
      (p := 2) (by norm_num)
    simpa [Real.norm_eq_abs, sq_abs] using h
  have h1 : HasInt (gaussianReal 0 v) (fun x => x) 0 :=
    ⟨hid, by rw [integral_id_gaussianReal]⟩
  have h2 : HasInt (gaussianReal 0 v) (fun x => x ^ 2) v :=
    ⟨hsq, BlockBand.Counting.integral_sq_gaussianReal v⟩
  exact ((hasInt_const (m ^ 2)).add ((h1.const_mul (2 * m)).add h2)).congr
    (fun x => by ring) (by ring)

end BlockBand.DeterminantScore.SignedRowSpread
