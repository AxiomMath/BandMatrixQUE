module

public import BlockBand.Coarea.Native.BlockBand.Basic.Indices
public import BlockBand.Coarea.Native.BlockBand.Spectral.Ordered
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic

/-!
# The Gaussian block-band ring law

This file fixes the model and normalization of the Gaussian block-band ring.  It
separates the deterministic variance profile from the probability law.  The law is
an explicit structure, not an axiom: a construction must provide its fields, and
theorems may be stated conditionally on it.

For an off-diagonal circular entry of total variance `s`, the real and imaginary
parts each have variance `s/2`.  A diagonal entry is real with variance `c/W`.
Upper-triangular entries are jointly independent, and the sampled matrix is
Hermitian by its codomain.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace GaussianRing

/-- Block-level variance weight
`c 1_{l=k} + b 1_{l=k+1} + b 1_{l=k-1}`.  The additive presentation
makes row normalization independent of any case split. -/
def blockWeight (p : Params) (k l : ZMod p.n) : ℝ :=
  (if l = k then p.c else 0) +
    (if l = k + 1 then p.b else 0) +
    (if l = k - 1 then p.b else 0)

/-- Total complex entry variance on the site space. -/
def varianceProfile (p : Params) (x y : Site p.n p.W) : ℝ :=
  blockWeight p x.1 y.1 / (p.W : ℝ)

/-- The profile is symmetric, matching Hermitian covariance. -/
theorem blockWeight_comm (p : Params) (k l : ZMod p.n) :
    blockWeight p k l = blockWeight p l k := by
  simp only [blockWeight]
  have hplus : l = k + 1 ↔ k = l - 1 := by constructor <;> intro h <;> subst h <;> ring
  have hminus : l = k - 1 ↔ k = l + 1 := by constructor <;> intro h <;> subst h <;> ring
  by_cases h : l = k
  · subst l; simp
  · have hk : k ≠ l := Ne.symm h
    simp only [h, hk, ite_false]
    rw [if_congr hplus rfl rfl, if_congr hminus rfl rfl]
    ring

/-- Entry variances are symmetric. -/
theorem varianceProfile_comm (p : Params) (x y : Site p.n p.W) :
    varianceProfile p x y = varianceProfile p y x := by
  rw [varianceProfile, varianceProfile, blockWeight_comm]

/-- Each block row has total block weight one. -/
theorem sum_blockWeight (p : Params) (k : ZMod p.n) :
    let _ := p.nNeZero
    ∑ l : ZMod p.n, blockWeight p k l = 1 := by
  let _ := p.nNeZero
  dsimp only
  simp only [blockWeight, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  linarith [p.c_add_two_b]

/-- Every matrix row has total variance exactly one. -/
theorem sum_varianceProfile (p : Params) (x : Site p.n p.W) :
    let _ := p.nNeZero
    ∑ y : Site p.n p.W, varianceProfile p x y = 1 := by
  let _ := p.nNeZero
  dsimp only
  rw [Fintype.sum_prod_type]
  simp only [varianceProfile]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hW : (p.W : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt p.W_pos
  rw [← sum_blockWeight p x.1]
  apply Finset.sum_congr rfl
  intro l hl
  field_simp

/-- Canonical row-major ordering on sites, used only to select the independent
upper-triangular coordinates. -/
def siteLE (p : Params) (x y : Site p.n p.W) : Prop :=
  (p.siteIndexEquiv x).val ≤ (p.siteIndexEquiv y).val

instance (p : Params) (x y : Site p.n p.W) : Decidable (siteLE p x y) :=
  by unfold siteLE; infer_instance

/-- Upper-triangular site pairs in the fixed row-major ordering. -/
def UpperPair (p : Params) :=
  {q : Site p.n p.W × Site p.n p.W // siteLE p q.1 q.2}

/-- Every entry variance is nonnegative. -/
theorem varianceProfile_nonneg (p : Params) (x y : Site p.n p.W) :
    0 ≤ varianceProfile p x y := by
  have hc : 0 ≤ p.c := p.c_pos.le
  have hb : 0 ≤ p.b := p.b_pos.le
  have hW : 0 ≤ (p.W : ℝ) := by positivity
  unfold varianceProfile blockWeight
  split_ifs <;> positivity

/-- The total variance as a nonnegative parameter for `gaussianReal`. -/
def varianceNNReal (p : Params) (x y : Site p.n p.W) : NNReal :=
  ⟨varianceProfile p x y, varianceProfile_nonneg p x y⟩

/-- The probability law `P_{n,W,b}` of the Gaussian ring, as an explicit structure.
It records the upper-triangular independence, the real diagonal convention,
and the two half-variance components of every strictly upper entry. -/
structure Law (p : Params) where
  Ω : Type*
  mΩ : MeasurableSpace Ω
  P : Measure Ω
  probability : IsProbabilityMeasure P
  H : Ω → Matrix (Site p.n p.W) (Site p.n p.W) ℂ
  H_hermitian : ∀ ω, (H ω).IsHermitian
  measurable_entry : ∀ x y, Measurable (fun ω => H ω x y)
  upper_independent :
    @iIndepFun Ω (UpperPair p) mΩ
      (fun _ => ℂ) (fun _ => Complex.measurableSpace)
      (fun q ω => H ω q.1.1 q.1.2) P
  diagonal_im_zero : ∀ x,
    ∀ᵐ ω ∂P, (H ω x x).im = 0
  diagonal_re_law : ∀ x,
    HasLaw (fun ω => (H ω x x).re)
      (gaussianReal 0 (varianceNNReal p x x)) P
  offdiag_components_independent : ∀ x y, siteLE p x y → x ≠ y →
    IndepFun (fun ω => (H ω x y).re) (fun ω => (H ω x y).im) P
  offdiag_re_law : ∀ x y, siteLE p x y → x ≠ y →
    HasLaw (fun ω => (H ω x y).re)
      (gaussianReal 0 (⟨varianceProfile p x y / 2, by
        exact div_nonneg (varianceProfile_nonneg p x y) (by norm_num)⟩)) P
  offdiag_im_law : ∀ x y, siteLE p x y → x ≠ y →
    HasLaw (fun ω => (H ω x y).im)
      (gaussianReal 0 (⟨varianceProfile p x y / 2, by
        exact div_nonneg (varianceProfile_nonneg p x y) (by norm_num)⟩)) P

attribute [instance] Law.mΩ Law.probability

/-- Every sample of the model law is Hermitian. -/
theorem Law.isHermitian {p : Params} (M : Law p) (ω : M.Ω) :
    (M.H ω).IsHermitian :=
  M.H_hermitian ω

end GaussianRing

end CoareaNative.BlockBand
