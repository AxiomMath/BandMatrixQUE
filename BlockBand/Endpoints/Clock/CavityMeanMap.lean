module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The deterministic cavity map of one block

We prove existence, uniqueness and a-priori bounds for the solution of the one-block cavity
equations, the deterministic part of the cavity-mean lemma. Steps 2–5 below follow the steps of the
paper's proof.

## Conventions

* The old path enters through a finite family of real numbers `x i` (the eigenvalues of the
  Hermitian Schur complement term `X`) with probability weights `p i` (`p i = 1/W` for
  `f(ζ) = W⁻¹ Tr (ζ - X)⁻¹`). The Stieltjes transform
  is `f(ζ) = Σ p_i (ζ - x_i)⁻¹`, so `Im f(ζ) = -Im ζ · Σ p_i |ζ - x_i|⁻²`: `f` maps the upper
  half-plane into the lower half-plane (`im_cavityStieltjes`).
* The cavity equations are `v = f(-e - c v - b u)`, `u = (z' - b v)⁻¹`, with
  `Im z' ≥ η₀ > 0`, `|z'| ≤ M`. A solution "with negative imaginary parts" has `Im v < 0` and
  `Im u < 0`; then the argument `ζ = -e - c v - b u` has `Im ζ = c(-Im v) + b(-Im u) > 0`.
  In the application `c = 1 - 2b`; here `b, c > 0` are arbitrary.
* `A = ⟨|D - c v - b u|⁻²⟩ = Σ p_i |ζ - x_i|⁻²` is `cavitySq p x ζ`, where `D = -e - X`.

## Results

* Step 2 (`cavity_imaginary_identities`, `cavity_gap_identity`):
  `y = A(cy + bw)`, `w = |u|²(Im z' + b y)`, and `1 - A(c + b²|u|²) = b Im z' |u|² / (cy + bw)`
  with `y = -Im v`, `w = -Im u`.
* Step 3 (`cavity_apriori_bounds`, `cavity_gap_lower_bound`): `|v|² ≤ A ≤ c⁻¹`,
  `(M + b/√c)⁻¹ ≤ |u| ≤ η₀⁻¹`, and `A(c + b²|u|²) ≤ 1 - δ` with
  `δ = cavityGapConst b c η₀ M = b η₀ (M + b/√c)⁻² / (√c + b/η₀)`, independent of `X`.
* Step 4 (`cavity_solution_unique`, `cavity_fixed_exists`, `cavity_existsUnique`): uniqueness
  by the two Cauchy–Schwarz inequalities of the paper's proof; existence by a contraction argument for the
  reduced map `Φ(v) = f(-e - c v - b (z' - b v)⁻¹)` in the hyperbolic quantity
  `|v - v'|² / (Im v Im v')`, on an `X`-dependent compact invariant set (this replaces the paper's
  dimension-repetition argument; only existence uses `X`-dependent constants).
* Step 5, deterministic part: `cavity_stability`.
* Matrix form `f(ζ) = W⁻¹ Tr (ζ - X)⁻¹`: `cavityMatrix_existsUnique`.

Uniformity: the constants of Steps 3–4 depend only on `(b, c, η₀, M)`, never on `x`, `p`, the
dimension or `e` (the internal constants of the existence proof depend on `max |x_i|`; the
conclusion does not).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Complex

variable {ι : Type*} [Fintype ι]

/-!
## Definitions
-/

/-- Probability weights on a finite index set. -/
def IsCavityWeights (p : ι → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The Stieltjes transform `f(ζ) = Σ_i p_i (ζ - x_i)⁻¹` of the finite law `Σ p_i δ_{x_i}`
(sign convention of the cavity-mean lemma: `f(ζ) = W⁻¹ Tr (ζ - X)⁻¹`). -/
def cavityStieltjes (p x : ι → ℝ) (ζ : ℂ) : ℂ := ∑ i, (p i : ℂ) * (ζ - x i)⁻¹

/-- `A = Σ_i p_i |ζ - x_i|⁻²` (the paper's `⟨|D - c v - b u|⁻²⟩` at `ζ = -e - c v - b u`). -/
def cavitySq (p x : ι → ℝ) (ζ : ℂ) : ℝ := ∑ i, p i * ‖(ζ - x i)⁻¹‖ ^ 2

/-- The port value `u(v) = (z' - b v)⁻¹`. -/
def cavityPort (b : ℝ) (z' v : ℂ) : ℂ := (z' - b * v)⁻¹

/-- The argument `ζ(v) = -e - c v - b u(v)` of the Stieltjes transform. -/
def cavityArg (b c e : ℝ) (z' v : ℂ) : ℂ := -e - c * v - b * cavityPort b z' v

/-- The reduced cavity map `Φ(v) = f(-e - c v - b (z' - b v)⁻¹)`; `v` solves
the cavity equations together with `u = (z' - b v)⁻¹` iff `Φ(v) = v`. -/
def cavityMap (p x : ι → ℝ) (b c e : ℝ) (z' v : ℂ) : ℂ :=
  cavityStieltjes p x (cavityArg b c e z' v)

/-- `(v, u)` solves the cavity equations, `v = f(-e - c v - b u)`, `u = (z' - b v)⁻¹`, with
negative imaginary parts. -/
def IsCavitySolution (p x : ι → ℝ) (b c e : ℝ) (z' v u : ℂ) : Prop :=
  v = cavityStieltjes p x (-e - c * v - b * u) ∧ u = (z' - b * v)⁻¹ ∧ v.im < 0 ∧ u.im < 0

/-- The gap constant of Step 3: `δ = b η (M + b/√c)⁻² / (√c + b/η)`. -/
def cavityGapConst (b c η M : ℝ) : ℝ := b * η / ((M + b / Real.sqrt c) ^ 2 * (Real.sqrt c + b / η))

namespace CavityMean

/-!
## Elementary complex facts
-/

theorem weighted_cs (p a b : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (∑ i, p i * a i * b i) ^ 2 ≤ (∑ i, p i * a i ^ 2) * (∑ i, p i * b i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (p i) * a i)
    (fun i => Real.sqrt (p i) * b i)
  have hs : ∀ i, Real.sqrt (p i) ^ 2 = p i := fun i => Real.sq_sqrt (hp i)
  calc (∑ i, p i * a i * b i) ^ 2
        = (∑ i, (Real.sqrt (p i) * a i) * (Real.sqrt (p i) * b i)) ^ 2 := by
          congr 1; refine Finset.sum_congr rfl fun i _ => ?_
          rw [show Real.sqrt (p i) * a i * (Real.sqrt (p i) * b i) =
            (Real.sqrt (p i) * Real.sqrt (p i)) * (a i * b i) by ring, Real.mul_self_sqrt (hp i)]
          ring
    _ ≤ _ := h
    _ = _ := by
          congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> rw [mul_pow, hs]

theorem ne_zero_of_im_pos {w : ℂ} (h : 0 < w.im) : w ≠ 0 := by
  rintro rfl; simp at h

theorem sub_ofReal_ne_zero {ζ : ℂ} (h : 0 < ζ.im) (t : ℝ) : ζ - t ≠ 0 :=
  ne_zero_of_im_pos (by simpa using h)

theorem inv_im_eq (w : ℂ) : (w⁻¹).im = -w.im * ‖w⁻¹‖ ^ 2 := by
  rw [Complex.inv_im, norm_inv, inv_pow, Complex.sq_norm]
  ring

theorem norm_inv_le_of_im {w : ℂ} {η : ℝ} (hη : 0 < η) (h : η ≤ w.im) : ‖w⁻¹‖ ≤ 1 / η := by
  rw [norm_inv, one_div]
  exact inv_anti₀ hη (h.trans (Complex.im_le_norm w))

theorem norm_inv_sub_le {ζ : ℂ} (h : 0 < ζ.im) (t : ℝ) : ‖(ζ - t)⁻¹‖ ≤ 1 / ζ.im :=
  norm_inv_le_of_im h (by simp)

/-!
## The finite Stieltjes transform
-/

variable (p x : ι → ℝ)

theorem im_cavityStieltjes (ζ : ℂ) :
    (cavityStieltjes p x ζ).im = -ζ.im * cavitySq p x ζ := by
  unfold cavityStieltjes cavitySq
  rw [Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.im_ofReal_mul, inv_im_eq]
  simp
  ring

variable {p}

theorem cavitySq_nonneg (hp : IsCavityWeights p) (ζ : ℂ) : 0 ≤ cavitySq p x ζ :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (sq_nonneg _)

theorem norm_cavityStieltjes_le_sum (hp : IsCavityWeights p) (ζ : ℂ) :
    ‖cavityStieltjes p x ζ‖ ≤ ∑ i, p i * ‖(ζ - x i)⁻¹‖ := by
  unfold cavityStieltjes
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp.1 i)]

theorem norm_sq_cavityStieltjes_le (hp : IsCavityWeights p) (ζ : ℂ) :
    ‖cavityStieltjes p x ζ‖ ^ 2 ≤ cavitySq p x ζ := by
  have h1 := norm_cavityStieltjes_le_sum x hp ζ
  have h2 := weighted_cs p (fun _ => 1) (fun i => ‖(ζ - x i)⁻¹‖) hp.1
  simp only [mul_one, one_pow, hp.2, one_mul] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem cavitySq_le (hp : IsCavityWeights p) {ζ : ℂ} (h : 0 < ζ.im) :
    cavitySq p x ζ ≤ 1 / ζ.im ^ 2 := by
  unfold cavitySq
  calc ∑ i, p i * ‖(ζ - x i)⁻¹‖ ^ 2 ≤ ∑ i, p i * (1 / ζ.im) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (norm_inv_sub_le h _) 2) (hp.1 i)
    _ = 1 / ζ.im ^ 2 := by rw [← Finset.sum_mul, hp.2]; ring

theorem norm_cavityStieltjes_le (hp : IsCavityWeights p) {ζ : ℂ} (h : 0 < ζ.im) :
    ‖cavityStieltjes p x ζ‖ ≤ 1 / ζ.im := by
  refine (norm_cavityStieltjes_le_sum x hp ζ).trans ?_
  calc ∑ i, p i * ‖(ζ - x i)⁻¹‖ ≤ ∑ i, p i * (1 / ζ.im) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (norm_inv_sub_le h _) (hp.1 i)
    _ = 1 / ζ.im := by rw [← Finset.sum_mul, hp.2, one_mul]

theorem exists_weight_pos (hp : IsCavityWeights p) : ∃ i, 0 < p i := by
  by_contra hc
  simp only [not_exists, not_lt] at hc
  have : ∑ i, p i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
  linarith [hp.2]

theorem cavitySq_ge (hp : IsCavityWeights p) {L : ℝ} (hL : ∀ i, |x i| ≤ L)
    {ζ : ℂ} (h : 0 < ζ.im) : 1 / (‖ζ‖ + L) ^ 2 ≤ cavitySq p x ζ := by
  obtain ⟨i₀, -⟩ := exists_weight_pos hp
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL i₀)
  have hpos : 0 < ‖ζ‖ + L := by
    have : 0 < ‖ζ‖ := norm_pos_iff.mpr (ne_zero_of_im_pos h)
    linarith
  unfold cavitySq
  calc 1 / (‖ζ‖ + L) ^ 2 = ∑ i, p i * (1 / (‖ζ‖ + L)) ^ 2 := by
        rw [← Finset.sum_mul, hp.2, one_mul, div_pow, one_pow]
    _ ≤ ∑ i, p i * ‖(ζ - x i)⁻¹‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hp.1 i)
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        rw [norm_inv, one_div]
        refine inv_anti₀ (norm_pos_iff.mpr (sub_ofReal_ne_zero h _)) ?_
        calc ‖ζ - x i‖ ≤ ‖ζ‖ + ‖(x i : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖ζ‖ + L := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith [hL i]

theorem cavitySq_pos (hp : IsCavityWeights p) {ζ : ℂ} (h : 0 < ζ.im) :
    0 < cavitySq p x ζ := by
  have hL : ∀ i, |x i| ≤ ∑ j, |x j| := fun i =>
    Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  refine lt_of_lt_of_le ?_ (cavitySq_ge x hp hL h)
  have : 0 < ‖ζ‖ := norm_pos_iff.mpr (ne_zero_of_im_pos h)
  have : 0 ≤ ∑ j, |x j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  positivity

/-- The resolvent identity `f(ζ) - f(ζ') = K(ζ,ζ') (ζ' - ζ)` with `|K|² ≤ A(ζ) A(ζ')`
(the first Cauchy–Schwarz inequality of Step 4). -/
theorem cavityStieltjes_sub (hp : IsCavityWeights p) {ζ ζ' : ℂ} (h : 0 < ζ.im)
    (h' : 0 < ζ'.im) : ∃ K : ℂ,
      cavityStieltjes p x ζ - cavityStieltjes p x ζ' = K * (ζ' - ζ) ∧
      ‖K‖ ^ 2 ≤ cavitySq p x ζ * cavitySq p x ζ' := by
  refine ⟨∑ i, (p i : ℂ) * ((ζ - x i)⁻¹ * (ζ' - x i)⁻¹), ?_, ?_⟩
  · unfold cavityStieltjes
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := sub_ofReal_ne_zero h (x i)
    have h2 := sub_ofReal_ne_zero h' (x i)
    field_simp
    ring
  · have h1 : ‖∑ i, (p i : ℂ) * ((ζ - x i)⁻¹ * (ζ' - x i)⁻¹)‖ ≤
        ∑ i, p i * ‖(ζ - x i)⁻¹‖ * ‖(ζ' - x i)⁻¹‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp.1 i), mul_assoc]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (weighted_cs p _ _ hp.1)

/-- Lipschitz bound `|f(ζ) - f(ζ')| ≤ |ζ - ζ'| / (Im ζ Im ζ')`. -/
theorem norm_cavityStieltjes_sub_le (hp : IsCavityWeights p) {ζ ζ' : ℂ} (h : 0 < ζ.im)
    (h' : 0 < ζ'.im) :
    ‖cavityStieltjes p x ζ - cavityStieltjes p x ζ'‖ ≤ ‖ζ - ζ'‖ / (ζ.im * ζ'.im) := by
  obtain ⟨K, hK, hK2⟩ := cavityStieltjes_sub x hp h h'
  have hA := cavitySq_le x hp h
  have hA' := cavitySq_le x hp h'
  have hK' : ‖K‖ ≤ 1 / (ζ.im * ζ'.im) := by
    have : ‖K‖ ^ 2 ≤ (1 / (ζ.im * ζ'.im)) ^ 2 := by
      calc ‖K‖ ^ 2 ≤ cavitySq p x ζ * cavitySq p x ζ' := hK2
        _ ≤ 1 / ζ.im ^ 2 * (1 / ζ'.im ^ 2) :=
          mul_le_mul hA hA' (cavitySq_nonneg x hp _) (by positivity)
        _ = (1 / (ζ.im * ζ'.im)) ^ 2 := by field_simp
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
  rw [hK, norm_mul, norm_sub_rev ζ' ζ, div_eq_mul_inv, mul_comm, ← one_div]
  exact mul_le_mul_of_nonneg_left hK' (norm_nonneg _)

/-!
## The cavity map at a point of the closed lower half-plane
-/

section Map

variable {b c e η : ℝ} {z' : ℂ}

theorem im_sub_mul (z' v : ℂ) (b : ℝ) : (z' - (b : ℂ) * v).im = z'.im - b * v.im := by simp

theorem port_facts (hb : 0 ≤ b) (hη : 0 < η) (hz : η ≤ z'.im) {v : ℂ} (hv : v.im ≤ 0) :
    η ≤ (z' - b * v).im ∧
    (cavityPort b z' v).im = -(z' - b * v).im * ‖cavityPort b z' v‖ ^ 2 ∧
    ‖cavityPort b z' v‖ ≤ 1 / η ∧ cavityPort b z' v ≠ 0 := by
  have h1 : η ≤ (z' - b * v).im := by rw [im_sub_mul]; nlinarith
  exact ⟨h1, inv_im_eq _, norm_inv_le_of_im hη h1,
    inv_ne_zero (ne_zero_of_im_pos (hη.trans_le h1))⟩

theorem port_mul (z' v : ℂ) (b : ℝ) (h : z' - b * v ≠ 0) :
    cavityPort b z' v * (z' - b * v) = 1 := inv_mul_cancel₀ h

theorem im_cavityArg (b c e : ℝ) (z' v : ℂ) :
    (cavityArg b c e z' v).im = c * (-v.im) + b * (-(cavityPort b z' v).im) := by
  unfold cavityArg; simp; ring

theorem im_cavityArg_eq (hb : 0 ≤ b) (hη : 0 < η) (hz : η ≤ z'.im) {v : ℂ} (hv : v.im ≤ 0) :
    (cavityArg b c e z' v).im =
      (c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2) * (-v.im) + b * ‖cavityPort b z' v‖ ^ 2 * z'.im := by
  obtain ⟨-, h2, -, -⟩ := port_facts hb hη hz hv
  rw [im_cavityArg, h2, im_sub_mul]; ring

theorem cavityArg_im_ge (hb : 0 ≤ b) (hc : 0 ≤ c) (hη : 0 < η) (hz : η ≤ z'.im) {v : ℂ}
    (hv : v.im ≤ 0) : b * ‖cavityPort b z' v‖ ^ 2 * η ≤ (cavityArg b c e z' v).im := by
  rw [im_cavityArg_eq hb hη hz hv]
  have : 0 ≤ (c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2) * (-v.im) :=
    mul_nonneg (by positivity) (by linarith)
  have : b * ‖cavityPort b z' v‖ ^ 2 * η ≤ b * ‖cavityPort b z' v‖ ^ 2 * z'.im :=
    mul_le_mul_of_nonneg_left hz (by positivity)
  linarith

theorem cavityArg_im_pos (hb : 0 < b) (hc : 0 ≤ c) (hη : 0 < η) (hz : η ≤ z'.im) {v : ℂ}
    (hv : v.im ≤ 0) : 0 < (cavityArg b c e z' v).im := by
  obtain ⟨-, -, -, hu⟩ := port_facts hb.le hη hz hv
  have : 0 < b * ‖cavityPort b z' v‖ ^ 2 * η := by
    have := norm_pos_iff.mpr hu; positivity
  exact this.trans_le (cavityArg_im_ge hb.le hc hη hz hv)

variable (p x : ι → ℝ)
variable {p}

/-- `-Im Φ(v) = Im ζ(v) · A(ζ(v))`. -/
theorem neg_im_cavityMap (v : ℂ) :
    -(cavityMap p x b c e z' v).im =
      (cavityArg b c e z' v).im * cavitySq p x (cavityArg b c e z' v) := by
  unfold cavityMap; rw [im_cavityStieltjes]; ring

/-- The two Cauchy–Schwarz inequalities of Step 4, for the reduced map:
`|Φ(v) - Φ(v')|² ≤ G(v) G(v') |v - v'|²` with `G(v) = A(ζ(v)) (c + b²|u(v)|²)`. -/
theorem cavityMap_sub_sq_le (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 ≤ c) (hη : 0 < η)
    (hz : η ≤ z'.im) {v v' : ℂ} (hv : v.im ≤ 0) (hv' : v'.im ≤ 0) :
    ‖cavityMap p x b c e z' v - cavityMap p x b c e z' v'‖ ^ 2 ≤
      (cavitySq p x (cavityArg b c e z' v) * (c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2)) *
      (cavitySq p x (cavityArg b c e z' v') * (c + b ^ 2 * ‖cavityPort b z' v'‖ ^ 2)) *
        ‖v - v'‖ ^ 2 := by
  set u := cavityPort b z' v
  set u' := cavityPort b z' v'
  obtain ⟨h1, -, -, -⟩ := port_facts hb.le hη hz hv
  obtain ⟨h1', -, -, -⟩ := port_facts hb.le hη hz hv'
  have hu := port_mul z' v b (ne_zero_of_im_pos (hη.trans_le h1))
  have hu' := port_mul z' v' b (ne_zero_of_im_pos (hη.trans_le h1'))
  obtain ⟨K, hK, hK2⟩ := cavityStieltjes_sub x hp (cavityArg_im_pos (e := e) hb hc hη hz hv)
    (cavityArg_im_pos (e := e) hb hc hη hz hv')
  have hdiff : cavityArg b c e z' v' - cavityArg b c e z' v = (c + b ^ 2 * u * u') * (v - v') := by
    unfold cavityArg
    change -(e : ℂ) - c * v' - b * u' - (-e - c * v - b * u) = _
    linear_combination (b * u') * hu - (b * u) * hu'
  have hnorm : ‖(c : ℂ) + b ^ 2 * u * u'‖ ^ 2 ≤
      (c + b ^ 2 * ‖u‖ ^ 2) * (c + b ^ 2 * ‖u'‖ ^ 2) := by
    have h1 : ‖(c : ℂ) + b ^ 2 * u * u'‖ ≤ c + b ^ 2 * (‖u‖ * ‖u'‖) := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [Complex.norm_real, Real.norm_of_nonneg hc, norm_mul, norm_mul, norm_pow,
        Complex.norm_real, Real.norm_of_nonneg hb.le]
      ring
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
    nlinarith [sq_nonneg (‖u‖ - ‖u'‖), mul_nonneg hc (sq_nonneg b),
      mul_nonneg (mul_nonneg hc (sq_nonneg b)) (sq_nonneg (‖u‖ - ‖u'‖))]
  unfold cavityMap
  rw [hK, hdiff, norm_mul, norm_mul, mul_pow, mul_pow]
  have hA := cavitySq_nonneg x hp (cavityArg b c e z' v)
  have hA' := cavitySq_nonneg x hp (cavityArg b c e z' v')
  calc ‖K‖ ^ 2 * (‖(c : ℂ) + b ^ 2 * u * u'‖ ^ 2 * ‖v - v'‖ ^ 2)
      ≤ (cavitySq p x (cavityArg b c e z' v) * cavitySq p x (cavityArg b c e z' v')) *
          ((c + b ^ 2 * ‖u‖ ^ 2) * (c + b ^ 2 * ‖u'‖ ^ 2) * ‖v - v'‖ ^ 2) :=
        mul_le_mul hK2 (mul_le_mul_of_nonneg_right hnorm (sq_nonneg _))
          (by positivity) (by positivity)
    _ = _ := by ring

end Map

end CavityMean

open CavityMean

/-!
## Steps 2–4 for exact solutions
-/

section Solutions

variable {p x : ι → ℝ} {b c e η M : ℝ} {z' v u : ℂ}

/-- A solution is a fixed point of the reduced map, with `u = u(v)`. -/
theorem IsCavitySolution.fixed (h : IsCavitySolution p x b c e z' v u) :
    u = cavityPort b z' v ∧ cavityMap p x b c e z' v = v := by
  obtain ⟨h1, h2, -, -⟩ := h
  refine ⟨h2, ?_⟩
  unfold cavityMap cavityArg cavityPort
  rw [← h2, ← h1]

/-- Conversely a fixed point `v` with `Im v < 0` gives a solution `(v, u(v))`. -/
theorem isCavitySolution_of_fixed (hb : 0 ≤ b) (hz : 0 < z'.im) (hv : v.im < 0)
    (hfix : cavityMap p x b c e z' v = v) :
    IsCavitySolution p x b c e z' v (cavityPort b z' v) := by
  obtain ⟨h1, h2, -, hu⟩ := port_facts hb hz le_rfl hv.le
  refine ⟨hfix.symm, rfl, hv, ?_⟩
  rw [h2]
  have := norm_pos_iff.mpr hu
  have := hz.trans_le h1
  nlinarith [mul_pos this (pow_pos (norm_pos_iff.mpr hu) 2)]

/-- **Step 2** of the cavity-mean lemma: with `y = -Im v`, `w = -Im u` and
`A = cavitySq p x ζ`, `ζ = -e - c v - b u`: `y = A (c y + b w)` and `w = |u|² (Im z' + b y)`. -/
theorem cavity_imaginary_identities (h : IsCavitySolution p x b c e z' v u) :
    -v.im = cavitySq p x (-e - c * v - b * u) * (c * (-v.im) + b * (-u.im)) ∧
      -u.im = ‖u‖ ^ 2 * (z'.im + b * (-v.im)) := by
  obtain ⟨h1, h2, -, -⟩ := h
  constructor
  · conv_lhs => rw [h1]
    rw [im_cavityStieltjes]
    simp; ring
  · rw [h2, inv_im_eq, im_sub_mul]; ring

theorem cavity_den_pos (hb : 0 < b) (hc : 0 < c) (h : IsCavitySolution p x b c e z' v u) :
    0 < c * (-v.im) + b * (-u.im) := by
  obtain ⟨-, -, hv, hu⟩ := h
  nlinarith

/-- **Step 2**, the gap identity:
`1 - A (c + b²|u|²) = b (Im z') |u|² / (c y + b w)`. -/
theorem cavity_gap_identity (hb : 0 < b) (hc : 0 < c) (h : IsCavitySolution p x b c e z' v u) :
    1 - cavitySq p x (-e - c * v - b * u) * (c + b ^ 2 * ‖u‖ ^ 2) =
      b * z'.im * ‖u‖ ^ 2 / (c * (-v.im) + b * (-u.im)) := by
  have hD := cavity_den_pos hb hc h
  obtain ⟨hy, hw⟩ := cavity_imaginary_identities h
  rw [eq_div_iff hD.ne']
  set A := cavitySq p x (-e - c * v - b * u)
  linear_combination (c + b ^ 2 * ‖u‖ ^ 2) * hy + b * hw

/-- **Step 3** a-priori bounds, independent of `x` and `p`:
`|v|² ≤ A ≤ c⁻¹` and `(M + b/√c)⁻¹ ≤ |u| ≤ η⁻¹`. -/
theorem cavity_apriori_bounds (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c) (hη : 0 < η)
    (hz : η ≤ z'.im) (hM : ‖z'‖ ≤ M) (h : IsCavitySolution p x b c e z' v u) :
    ‖v‖ ^ 2 ≤ cavitySq p x (-e - c * v - b * u) ∧ cavitySq p x (-e - c * v - b * u) ≤ 1 / c ∧
      1 / (M + b / Real.sqrt c) ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / η := by
  have hD := cavity_den_pos hb hc h
  obtain ⟨hy, hw⟩ := cavity_imaginary_identities h
  have hsol := h
  obtain ⟨h1, h2, hv, hu⟩ := h
  set A := cavitySq p x (-e - c * v - b * u)
  have hA0 : 0 ≤ A := cavitySq_nonneg x hp _
  have hvA : ‖v‖ ^ 2 ≤ A := by
    conv_lhs => rw [h1]
    exact norm_sq_cavityStieltjes_le x hp _
  have hAc : A ≤ 1 / c := by
    rw [le_div_iff₀ hc]
    have : A * (c * (-v.im)) ≤ -v.im := by
      rw [hy]; exact mul_le_mul_of_nonneg_left (by nlinarith) hA0
    nlinarith
  have hvc : ‖v‖ ≤ 1 / Real.sqrt c := by
    have hsc := Real.sqrt_pos.mpr hc
    rw [← Real.sqrt_sq (norm_nonneg v), one_div, ← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt (by rw [← one_div]; linarith)
  obtain ⟨-, -, hu1, -⟩ := port_facts hb.le hη hz hv.le
  refine ⟨hvA, hAc, ?_, by rw [h2]; exact hu1⟩
  have hden : ‖z' - b * v‖ ≤ M + b / Real.sqrt c := by
    calc ‖z' - b * v‖ ≤ ‖z'‖ + ‖(b : ℂ) * v‖ := norm_sub_le _ _
      _ ≤ M + b * (1 / Real.sqrt c) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
          exact add_le_add hM (mul_le_mul_of_nonneg_left hvc hb.le)
      _ = M + b / Real.sqrt c := by ring
  have hpos : 0 < ‖z' - b * v‖ := by
    have := port_facts hb.le hη hz hv.le
    exact norm_pos_iff.mpr (ne_zero_of_im_pos (hη.trans_le this.1))
  rw [h2, norm_inv, ← one_div]
  exact one_div_le_one_div_of_le hpos hden

theorem cavityGapConst_pos (hb : 0 < b) (hc : 0 < c) (hη : 0 < η) (hM : 0 ≤ M) :
    0 < cavityGapConst b c η M := by
  unfold cavityGapConst
  have := Real.sqrt_pos.mpr hc
  have : 0 < M + b / Real.sqrt c := by positivity
  positivity

/-- **Step 3**, the gap is bounded below, uniformly in `x`, `p`, `e`:
`A (c + b²|u|²) ≤ 1 - δ`, `δ = cavityGapConst b c η M > 0`. -/
theorem cavity_gap_lower_bound (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c) (hη : 0 < η)
    (hz : η ≤ z'.im) (hM : ‖z'‖ ≤ M) (h : IsCavitySolution p x b c e z' v u) :
    cavitySq p x (-e - c * v - b * u) * (c + b ^ 2 * ‖u‖ ^ 2) ≤ 1 - cavityGapConst b c η M := by
  have hgap := cavity_gap_identity hb hc h
  obtain ⟨hvA, hAc, hul, huu⟩ := cavity_apriori_bounds hp hb hc hη hz hM h
  have hD := cavity_den_pos hb hc h
  have hsc := Real.sqrt_pos.mpr hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hMb : 0 < M + b / Real.sqrt c := by positivity
  obtain ⟨h1, h2, hv, hu⟩ := h
  have hvc : ‖v‖ ≤ 1 / Real.sqrt c := by
    rw [← Real.sqrt_sq (norm_nonneg v), one_div, ← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt (by rw [← one_div]; linarith)
  -- numerator and denominator bounds
  have hnum : b * η / (M + b / Real.sqrt c) ^ 2 ≤ b * z'.im * ‖u‖ ^ 2 := by
    have : 1 / (M + b / Real.sqrt c) ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [one_div, ← inv_pow, ← one_div]; exact pow_le_pow_left₀ (one_div_pos.mpr hMb).le hul 2
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hz hb.le) this (by positivity)
      (mul_nonneg hb.le (hη.le.trans hz))
  have hden : c * (-v.im) + b * (-u.im) ≤ Real.sqrt c + b / η := by
    have h1' : -v.im ≤ 1 / Real.sqrt c := by
      have := Complex.abs_im_le_norm v; rw [abs_le] at this; linarith
    have h2' : -u.im ≤ 1 / η := by
      have := Complex.abs_im_le_norm u; rw [abs_le] at this; linarith
    have hcs : c * (1 / Real.sqrt c) = Real.sqrt c := by
      rw [mul_one_div, Real.div_sqrt]
    have e1 := mul_le_mul_of_nonneg_left h1' hc.le
    have e2 := mul_le_mul_of_nonneg_left h2' hb.le
    rw [hcs] at e1; rw [mul_one_div] at e2
    linarith
  have : cavityGapConst b c η M ≤ b * z'.im * ‖u‖ ^ 2 / (c * (-v.im) + b * (-u.im)) := by
    unfold cavityGapConst
    rw [← div_div]
    exact div_le_div₀ (mul_nonneg (mul_nonneg hb.le (hη.le.trans hz)) (sq_nonneg _)) hnum hD hden
  linarith

/-- **Step 4**, uniqueness: two solutions with negative imaginary parts
coincide. The comparison coefficient is bounded by the geometric mean of the two gap quantities,
each `≤ 1 - δ < 1`. -/
theorem cavity_solution_unique (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c)
    (hz : 0 < z'.im) {v' u' : ℂ} (h : IsCavitySolution p x b c e z' v u)
    (h' : IsCavitySolution p x b c e z' v' u') : v = v' ∧ u = u' := by
  obtain ⟨hu, hfix⟩ := h.fixed
  obtain ⟨hu', hfix'⟩ := h'.fixed
  have hg := cavity_gap_lower_bound hp hb hc hz le_rfl le_rfl h
  have hg' := cavity_gap_lower_bound hp hb hc hz le_rfl le_rfl h'
  have hδ := cavityGapConst_pos hb hc hz (norm_nonneg z')
  have hcs := cavityMap_sub_sq_le (e := e) x hp hb hc.le hz le_rfl h.2.2.1.le h'.2.2.1.le
  have harg : cavityArg b c e z' v = -e - c * v - b * u := by rw [hu]; rfl
  have harg' : cavityArg b c e z' v' = -e - c * v' - b * u' := by rw [hu']; rfl
  rw [hfix, hfix', harg, harg', ← hu, ← hu'] at hcs
  set G := cavitySq p x (-e - c * v - b * u) * (c + b ^ 2 * ‖u‖ ^ 2)
  set G' := cavitySq p x (-e - c * v' - b * u') * (c + b ^ 2 * ‖u'‖ ^ 2)
  have hG0 : 0 ≤ G := mul_nonneg (cavitySq_nonneg x hp _) (by positivity)
  have hG0' : 0 ≤ G' := mul_nonneg (cavitySq_nonneg x hp _) (by positivity)
  have hGG : G * G' < 1 := by
    have : G * G' ≤ (1 - cavityGapConst b c z'.im ‖z'‖) * 1 :=
      mul_le_mul hg (by linarith) hG0' (by linarith)
    linarith
  have hvv : v = v' := by
    have h0 : ‖v - v'‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v - v'‖]
    have : ‖v - v'‖ = 0 := by nlinarith [norm_nonneg (v - v')]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  refine ⟨hvv, ?_⟩
  rw [hu, hu', hvv]

end Solutions

/-!
## Step 4, existence
-/

namespace CavityMean

section ExistenceHelpers

variable {b c e η : ℝ} {z' v : ℂ}

theorem port_norm_ge (hb : 0 ≤ b) (hη : 0 < η) (hz : η ≤ z'.im) (hv : v.im ≤ 0) :
    1 / (‖z'‖ + b * ‖v‖) ≤ ‖cavityPort b z' v‖ := by
  obtain ⟨h1, -, -, -⟩ := port_facts hb hη hz hv
  have hpos : 0 < ‖z' - b * v‖ := norm_pos_iff.mpr (ne_zero_of_im_pos (hη.trans_le h1))
  have hden : ‖z' - b * v‖ ≤ ‖z'‖ + b * ‖v‖ := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb]
  unfold cavityPort
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le hpos hden

theorem port_term_ge (hb : 0 < b) (hη : 0 < η) (hz : η ≤ z'.im)
    (hv : v.im ≤ 0) {R : ℝ} (hR : ‖v‖ ≤ R) :
    b * η / (‖z'‖ + b * R) ^ 2 ≤ b * ‖cavityPort b z' v‖ ^ 2 * η := by
  have hz0 : 0 < ‖z'‖ := hη.trans_le (hz.trans (Complex.im_le_norm z'))
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hpos : 0 < ‖z'‖ + b * ‖v‖ := by positivity
  have hu := port_norm_ge hb.le hη hz hv
  have h1 : 1 / (‖z'‖ + b * R) ≤ ‖cavityPort b z' v‖ :=
    (one_div_le_one_div_of_le hpos (by nlinarith)).trans hu
  calc b * η / (‖z'‖ + b * R) ^ 2 = b * (1 / (‖z'‖ + b * R)) ^ 2 * η := by
        rw [div_pow, one_pow]; ring
    _ ≤ b * ‖cavityPort b z' v‖ ^ 2 * η := by gcongr

theorem arg_im_ge_of_norm_le (hb : 0 < b) (hc : 0 ≤ c) (hη : 0 < η) (hz : η ≤ z'.im)
    (hv : v.im ≤ 0) {R : ℝ} (hR : ‖v‖ ≤ R) :
    b * η / (‖z'‖ + b * R) ^ 2 ≤ (cavityArg b c e z' v).im :=
  (port_term_ge hb hη hz hv hR).trans (cavityArg_im_ge hb.le hc hη hz hv)

theorem norm_cavityArg_le (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ‖cavityArg b c e z' v‖ ≤ |e| + c * ‖v‖ + b * ‖cavityPort b z' v‖ := by
  unfold cavityArg
  calc ‖-(e : ℂ) - c * v - b * cavityPort b z' v‖
      ≤ ‖-(e : ℂ) - c * v‖ + ‖(b : ℂ) * cavityPort b z' v‖ := norm_sub_le _ _
    _ ≤ ‖-(e : ℂ)‖ + ‖(c : ℂ) * v‖ + ‖(b : ℂ) * cavityPort b z' v‖ := by
        gcongr; exact norm_sub_le _ _
    _ = _ := by
        rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_of_nonneg hb, Real.norm_of_nonneg hc]

end ExistenceHelpers

end CavityMean

section Existence

variable {p x : ι → ℝ} {b c e : ℝ} {z' : ℂ}

/-- **Step 4**, existence (by a contraction argument): the
reduced map `Φ` has a fixed point with negative imaginary part. Proof: `Φ` maps the closed lower
half-plane into a compact set `S = {Im v ≤ -y₀, |v| ≤ K}` with `S ⊆` the closed lower half-plane;
on `S` it is a strict contraction for the hyperbolic quantity `|v - v'|²/(Im v Im v')`; the
iterates converge. The constants `K, y₀` depend on `max |x_i|` (existence only). -/
theorem cavity_fixed_exists (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c) (hz : 0 < z'.im) :
    ∃ v : ℂ, v.im < 0 ∧ cavityMap p x b c e z' v = v := by
  set η := z'.im with hηdef
  set M := ‖z'‖ with hMdef
  have hη : 0 < η := hz
  have hM : 0 < M := hη.trans_le (Complex.im_le_norm z')
  set L := ∑ i, |x i|
  have hL : ∀ i, |x i| ≤ L := fun i =>
    Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ => abs_nonneg _
  set Φ := cavityMap p x b c e z' with hΦ
  -- a global bound on `Φ` over the closed lower half-plane
  obtain ⟨K, hK1, hE1⟩ : ∃ K : ℝ, 1 ≤ K ∧ ∀ v : ℂ, v.im ≤ 0 → ‖Φ v‖ ≤ K := by
    set V₀ := (1 + |e| + b / η + L) / c
    have hV₀ : 0 < V₀ := by positivity
    refine ⟨max 1 ((M + b * V₀) ^ 2 / (b * η)), le_max_left _ _, fun v hv => ?_⟩
    obtain ⟨-, -, hu1, -⟩ := port_facts hb.le hη le_rfl hv
    by_cases hvV : ‖v‖ ≤ V₀
    · have him := arg_im_ge_of_norm_le (e := e) hb hc.le hη le_rfl hv hvV
      have hpos : 0 < b * η / (M + b * V₀) ^ 2 := by positivity
      refine le_trans ?_ (le_max_right _ _)
      calc ‖Φ v‖ ≤ 1 / (cavityArg b c e z' v).im :=
            norm_cavityStieltjes_le x hp (hpos.trans_le him)
        _ ≤ 1 / (b * η / (M + b * V₀) ^ 2) := one_div_le_one_div_of_le hpos him
        _ = (M + b * V₀) ^ 2 / (b * η) := by rw [one_div_div]
    · rw [not_le] at hvV
      refine le_trans ?_ (le_max_left _ _)
      have hfar : ∀ i, 1 ≤ ‖cavityArg b c e z' v - x i‖ := by
        intro i
        have hcv : (c : ℂ) * v =
            -(cavityArg b c e z' v - x i) - ((e : ℂ) + b * cavityPort b z' v + x i) := by
          unfold cavityArg; ring
        have h1 : c * ‖v‖ ≤ ‖cavityArg b c e z' v - x i‖ + (|e| + b * (1 / η) + L) := by
          have : ‖(c : ℂ) * v‖ = c * ‖v‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
          rw [← this, hcv]
          refine (norm_sub_le _ _).trans (add_le_add (le_of_eq (norm_neg _)) ?_)
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (le_of_eq (by rw [Complex.norm_real, Real.norm_eq_abs])) ?_)) ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
            exact mul_le_mul_of_nonneg_left hu1 hb.le
          · rw [Complex.norm_real, Real.norm_eq_abs]; exact hL i
        have h2 : c * V₀ = 1 + |e| + b / η + L := by
          simp only [V₀]; field_simp
        have h3 : c * V₀ ≤ c * ‖v‖ := mul_le_mul_of_nonneg_left hvV.le hc.le
        rw [mul_one_div] at h1
        linarith
      refine (norm_cavityStieltjes_le_sum x hp _).trans ?_
      calc ∑ i, p i * ‖(cavityArg b c e z' v - x i)⁻¹‖ ≤ ∑ i, p i * 1 := by
            refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hp.1 i)
            rw [norm_inv]; exact inv_le_one_of_one_le₀ (hfar i)
        _ = 1 := by rw [← Finset.sum_mul, hp.2, one_mul]
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  -- constants on the compact set `S`
  set s₁ := b * η / (M + b * K) ^ 2 with hs₁
  have hs₁0 : 0 < s₁ := by positivity
  set Z₁ := |e| + c * K + b * (1 / η)
  have hZ₁ : 0 ≤ Z₁ := by positivity
  set y₀ := s₁ * (1 / (Z₁ + L) ^ 2) with hy₀
  have hy₀0 : 0 < y₀ := by
    have : 0 < Z₁ + L := by
      have : 0 < c * K := by positivity
      positivity
    positivity
  set Pm := c + b ^ 2 * (1 / η) ^ 2
  have hPm : 0 < Pm := by positivity
  set q := Pm * K / (Pm * K + s₁) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  set Lip := Pm / s₁ ^ 2
  -- facts on `S`
  have hSarg : ∀ v : ℂ, v.im ≤ 0 → ‖v‖ ≤ K → s₁ ≤ (cavityArg b c e z' v).im := fun v hv hvK =>
    arg_im_ge_of_norm_le (e := e) hb hc.le hη le_rfl hv hvK
  have hP : ∀ v : ℂ, v.im ≤ 0 → c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2 ≤ Pm := by
    intro v hv
    obtain ⟨-, -, hu1, -⟩ := port_facts hb.le hη le_rfl hv
    have := pow_le_pow_left₀ (norm_nonneg _) hu1 2
    nlinarith [sq_nonneg b]
  have hE2 : ∀ v : ℂ, v.im ≤ 0 → ‖v‖ ≤ K → y₀ ≤ -(Φ v).im := by
    intro v hv hvK
    obtain ⟨-, -, hu1, -⟩ := port_facts hb.le hη le_rfl hv
    have him := hSarg v hv hvK
    have hpos := hs₁0.trans_le him
    rw [hΦ, neg_im_cavityMap]
    have hζ : ‖cavityArg b c e z' v‖ ≤ Z₁ := by
      refine (norm_cavityArg_le hb.le hc.le).trans ?_
      have := mul_le_mul_of_nonneg_left hvK hc.le
      have := mul_le_mul_of_nonneg_left hu1 hb.le
      linarith
    have hA := cavitySq_ge x hp hL hpos
    have hA' : 1 / (Z₁ + L) ^ 2 ≤ cavitySq p x (cavityArg b c e z' v) := by
      refine le_trans ?_ hA
      have : 0 < ‖cavityArg b c e z' v‖ + L := by
        have := norm_pos_iff.mpr (ne_zero_of_im_pos hpos); linarith
      exact one_div_le_one_div_of_le (by positivity) (by gcongr)
    exact mul_le_mul him hA' (by positivity) hpos.le
  -- the gap quantity on `S`
  have hGy : ∀ v : ℂ, v.im ≤ 0 → ‖v‖ ≤ K →
      cavitySq p x (cavityArg b c e z' v) * (c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2) * (-v.im) ≤
        q * (-(Φ v).im) := by
    intro v hv hvK
    have him := hSarg v hv hvK
    have hpos := hs₁0.trans_le him
    set A := cavitySq p x (cavityArg b c e z' v)
    set P := c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2
    have hA0 : 0 ≤ A := cavitySq_nonneg x hp _
    have hP0 : 0 ≤ P := by positivity
    have hPP := hP v hv
    have hy : -v.im ≤ K := by
      have := Complex.abs_im_le_norm v; rw [abs_le] at this; linarith
    have heq := im_cavityArg_eq (c := c) (e := e) hb.le hη le_rfl hv
    have hQ : s₁ ≤ b * ‖cavityPort b z' v‖ ^ 2 * z'.im :=
      port_term_ge hb hη le_rfl hv hvK
    rw [hΦ, neg_im_cavityMap]
    -- `P y ≤ q (P y + Q)`
    have key : P * (-v.im) ≤ q * (cavityArg b c e z' v).im := by
      rw [heq, hq, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 0 ≤ -v.im := by linarith
      nlinarith [mul_le_mul hPP hy this hPm.le, mul_nonneg hP0 this,
        mul_le_mul_of_nonneg_left hQ (mul_nonneg hPm.le hK0.le)]
    calc A * P * (-v.im) = A * (P * (-v.im)) := by ring
      _ ≤ A * (q * (cavityArg b c e z' v).im) := mul_le_mul_of_nonneg_left key hA0
      _ = q * ((cavityArg b c e z' v).im * A) := by ring
  have hG : ∀ v : ℂ, v.im ≤ 0 → ‖v‖ ≤ K →
      cavitySq p x (cavityArg b c e z' v) * (c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2) ≤ Lip := by
    intro v hv hvK
    have him := hSarg v hv hvK
    have hpos := hs₁0.trans_le him
    have hA := cavitySq_le x hp hpos
    have hA' : cavitySq p x (cavityArg b c e z' v) ≤ 1 / s₁ ^ 2 :=
      hA.trans (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hs₁0.le him 2))
    calc _ ≤ 1 / s₁ ^ 2 * Pm := mul_le_mul hA' (hP v hv) (by positivity) (by positivity)
      _ = Lip := by ring
  have hΦnn : ∀ v : ℂ, v.im ≤ 0 → ‖v‖ ≤ K → 0 ≤ -(Φ v).im := fun v hv hvK =>
    hy₀0.le.trans (hE2 v hv hvK)
  -- contraction and Lipschitz bounds on `S`
  have hcontr : ∀ v v' : ℂ, v.im ≤ 0 → ‖v‖ ≤ K → v'.im ≤ 0 → ‖v'‖ ≤ K →
      ‖Φ v - Φ v'‖ ^ 2 * ((-v.im) * (-v'.im)) ≤
        q ^ 2 * ((-(Φ v).im) * (-(Φ v').im)) * ‖v - v'‖ ^ 2 := by
    intro v v' hv hvK hv' hvK'
    have hcs := cavityMap_sub_sq_le (e := e) x hp hb hc.le hη le_rfl hv hv'
    have h1 := hGy v hv hvK
    have h2 := hGy v' hv' hvK'
    have hy : 0 ≤ -v.im := by linarith
    have hy' : 0 ≤ -v'.im := by linarith
    have hG0 : 0 ≤ cavitySq p x (cavityArg b c e z' v) * (c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2) :=
      mul_nonneg (cavitySq_nonneg x hp _) (by positivity)
    have hG0' :
        0 ≤ cavitySq p x (cavityArg b c e z' v') * (c + b ^ 2 * ‖cavityPort b z' v'‖ ^ 2) :=
      mul_nonneg (cavitySq_nonneg x hp _) (by positivity)
    calc ‖Φ v - Φ v'‖ ^ 2 * ((-v.im) * (-v'.im))
        ≤ (cavitySq p x (cavityArg b c e z' v) * (c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2)) *
          (cavitySq p x (cavityArg b c e z' v') * (c + b ^ 2 * ‖cavityPort b z' v'‖ ^ 2)) *
            ‖v - v'‖ ^ 2 * ((-v.im) * (-v'.im)) :=
          mul_le_mul_of_nonneg_right hcs (mul_nonneg hy hy')
      _ = (cavitySq p x (cavityArg b c e z' v) * (c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2) *
            (-v.im)) *
          (cavitySq p x (cavityArg b c e z' v') * (c + b ^ 2 * ‖cavityPort b z' v'‖ ^ 2) *
            (-v'.im)) * ‖v - v'‖ ^ 2 := by ring
      _ ≤ (q * (-(Φ v).im)) * (q * (-(Φ v').im)) * ‖v - v'‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity)
            (mul_nonneg hq0 (hΦnn v hv hvK))) (sq_nonneg _)
      _ = q ^ 2 * ((-(Φ v).im) * (-(Φ v').im)) * ‖v - v'‖ ^ 2 := by ring
  have hlip : ∀ v v' : ℂ, v.im ≤ 0 → ‖v‖ ≤ K → v'.im ≤ 0 → ‖v'‖ ≤ K →
      ‖Φ v - Φ v'‖ ≤ Lip * ‖v - v'‖ := by
    intro v v' hv hvK hv' hvK'
    have hcs := cavityMap_sub_sq_le (e := e) x hp hb hc.le hη le_rfl hv hv'
    have hG0 : 0 ≤ cavitySq p x (cavityArg b c e z' v) * (c + b ^ 2 * ‖cavityPort b z' v‖ ^ 2) :=
      mul_nonneg (cavitySq_nonneg x hp _) (by positivity)
    have hG0' :
        0 ≤ cavitySq p x (cavityArg b c e z' v') * (c + b ^ 2 * ‖cavityPort b z' v'‖ ^ 2) :=
      mul_nonneg (cavitySq_nonneg x hp _) (by positivity)
    have hLip0 : 0 ≤ Lip := by positivity
    have : ‖Φ v - Φ v'‖ ^ 2 ≤ (Lip * ‖v - v'‖) ^ 2 := by
      refine hcs.trans ?_
      rw [mul_pow, sq Lip]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hG v hv hvK) (hG v' hv' hvK') hG0' hLip0) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
  -- the iterates
  set w : ℕ → ℂ := fun n => Φ^[n + 1] 0 with hw
  have hwsucc : ∀ n, w (n + 1) = Φ (w n) := fun n => by
    simp only [hw]; rw [Function.iterate_succ_apply']
  have hwS : ∀ n, (w n).im ≤ -y₀ ∧ ‖w n‖ ≤ K := by
    intro n
    induction n with
    | zero =>
      have h0 : (0 : ℂ).im ≤ 0 := le_refl _
      have hw0 : w 0 = Φ 0 := rfl
      rw [hw0]
      exact ⟨by linarith [hE2 0 h0 (by simp; linarith)], hE1 0 h0⟩
    | succ n ih =>
      rw [hwsucc]
      have hv : (w n).im ≤ 0 := ih.1.trans (by linarith)
      exact ⟨by linarith [hE2 (w n) hv ih.2], hE1 (w n) hv⟩
  have hwim : ∀ n, 0 < -(w n).im := fun n => by linarith [(hwS n).1]
  have hwle : ∀ n, -(w n).im ≤ K := fun n => by
    have := Complex.abs_im_le_norm (w n); rw [abs_le] at this; linarith [(hwS n).2]
  set d : ℕ → ℝ := fun n => ‖w (n + 1) - w n‖ ^ 2 / ((-(w (n + 1)).im) * (-(w n).im)) with hd
  have hd0 : ∀ n, 0 ≤ d n := fun n => by
    have := hwim n; have := hwim (n + 1); positivity
  have hdstep : ∀ n, d (n + 1) ≤ q ^ 2 * d n := by
    intro n
    have hv1 : (w (n + 1)).im ≤ 0 := by linarith [hwim (n + 1)]
    have hv0 : (w n).im ≤ 0 := by linarith [hwim n]
    have hc' := hcontr (w (n + 1)) (w n) hv1 (hwS (n + 1)).2 hv0 (hwS n).2
    rw [← hwsucc, ← hwsucc] at hc'
    simp only [hd]
    rw [mul_div_assoc', div_le_div_iff₀ (mul_pos (hwim _) (hwim _)) (mul_pos (hwim _) (hwim _))]
    linarith [hc']
  have hdgeom : ∀ n, d n ≤ q ^ (2 * n) * d 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc d (n + 1) ≤ q ^ 2 * d n := hdstep n
        _ ≤ q ^ 2 * (q ^ (2 * n) * d 0) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = q ^ (2 * (n + 1)) * d 0 := by ring
  have hstepb : ∀ n, ‖w n - w (n + 1)‖ ≤ K * Real.sqrt (d 0) * q ^ n := by
    intro n
    rw [norm_sub_rev]
    have hsq : ‖w (n + 1) - w n‖ ^ 2 ≤ (K * Real.sqrt (d 0) * q ^ n) ^ 2 := by
      have heq : ‖w (n + 1) - w n‖ ^ 2 = d n * ((-(w (n + 1)).im) * (-(w n).im)) := by
        simp only [hd]
        rw [div_mul_cancel₀ _ (mul_pos (hwim _) (hwim _)).ne']
      rw [heq, mul_pow, mul_pow, Real.sq_sqrt (hd0 0)]
      have hyy : (-(w (n + 1)).im) * (-(w n).im) ≤ K ^ 2 := by
        rw [sq]; exact mul_le_mul (hwle _) (hwle _) (hwim _).le hK0.le
      calc d n * ((-(w (n + 1)).im) * (-(w n).im)) ≤ (q ^ (2 * n) * d 0) * K ^ 2 :=
            mul_le_mul (hdgeom n) hyy (mul_pos (hwim _) (hwim _)).le
              (mul_nonneg (pow_nonneg hq0 _) (hd0 0))
        _ = K ^ 2 * d 0 * (q ^ n) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hcauchy : CauchySeq w :=
    cauchySeq_of_le_geometric q (K * Real.sqrt (d 0)) hq1 (fun n => by
      rw [dist_eq_norm]; exact hstepb n)
  obtain ⟨vs, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hSclosed : IsClosed {v : ℂ | v.im ≤ -y₀ ∧ ‖v‖ ≤ K} :=
    (isClosed_le Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_norm continuous_const)
  have hvsS : vs.im ≤ -y₀ ∧ ‖vs‖ ≤ K :=
    hSclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hwS)
  have hvs0 : vs.im ≤ 0 := hvsS.1.trans (by linarith)
  refine ⟨vs, by linarith [hvsS.1], ?_⟩
  have h1 : Filter.Tendsto (fun n => w (n + 1)) Filter.atTop (nhds vs) :=
    hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have h2 : Filter.Tendsto (fun n => w (n + 1)) Filter.atTop (nhds (Φ vs)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hz0 : Filter.Tendsto (fun n => Lip * ‖w n - vs‖) Filter.atTop (nhds 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.mp hlim).const_mul Lip
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hz0
    rw [hwsucc]
    exact hlip (w n) vs (by linarith [hwim n]) (hwS n).2 hvs0 hvsS.2
  exact tendsto_nhds_unique h2 h1

/-- **Step 4**: existence and uniqueness of the solution of the cavity equations with negative
imaginary parts, for every finite law and every `Im z' > 0` (`b, c > 0`). -/
theorem cavity_existsUnique (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c) (hz : 0 < z'.im) :
    ∃ vu : ℂ × ℂ, IsCavitySolution p x b c e z' vu.1 vu.2 ∧
      ∀ v u : ℂ, IsCavitySolution p x b c e z' v u → v = vu.1 ∧ u = vu.2 := by
  obtain ⟨v, hv, hfix⟩ := cavity_fixed_exists (x := x) (e := e) hp hb hc hz
  have hsol := isCavitySolution_of_fixed hb.le hz hv hfix
  exact ⟨(v, cavityPort b z' v), hsol, fun v' u' h' => cavity_solution_unique hp hb hc hz h' hsol⟩

end Existence

end BlockBand.Endpoints.Clock
