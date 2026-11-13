module

public import BlockBand.SourceProcess.WienerRecovery.BrownianCanonicalDyadicStepClosure

/-!
# Fixed-time convergence of canonical Brownian dyadic interpolants

For each fixed time on a positive compact horizon, this module chooses the containing
dyadic edge.  Gaussian increment tails and first Borel–Cantelli show that the raw
coordinate at the edge's left endpoint approaches the raw coordinate at the fixed
time almost surely.  The already-proved uniform dyadic edge modulus and the exact
affine formula then imply almost-sure convergence of the fixed canonical polygonal
interpolants.  This closes the last field of the canonical interpolation facts without
assuming a continuous modification.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped ENNReal NNReal Topology BigOperators
open Filter MeasureTheory ProbabilityTheory

namespace BrownianCanonicalDyadicEvalClosure

open BrownianKolmogorovChentsovClosure
open BrownianDyadicChainingClosure
open BrownianDyadicGaussianEnvelope
open BrownianDyadicInterpolationCorrection
open BrownianDyadicCompactExtension
open BrownianCanonicalDyadicInterpolant
open BrownianCanonicalDyadicAffineClosure
open BrownianCanonicalDyadicStepClosure
open ScalarWienerMeasureConstruction

/-- The selected level-`n` dyadic edge containing a fixed compact-horizon time. -/
def dyadicEdgeAt (T : NNReal) (hT : 0 < T) (n : ℕ)
    (t : Set.Icc (0 : NNReal) T) : Fin (2 ^ n) :=
  Classical.choose (exists_dyadicEdge_mem T hT n t)

private theorem dyadicEdgeAt_left_le (T : NNReal) (hT : 0 < T) (n : ℕ)
    (t : Set.Icc (0 : NNReal) T) :
    dyadicLeft T n (dyadicEdgeAt T hT n t) ≤ t.1 :=
  (Classical.choose_spec (exists_dyadicEdge_mem T hT n t)).1

private theorem dyadicEdgeAt_le_right (T : NNReal) (hT : 0 < T) (n : ℕ)
    (t : Set.Icc (0 : NNReal) T) :
    t.1 ≤ dyadicRight T n (dyadicEdgeAt T hT n t) :=
  (Classical.choose_spec (exists_dyadicEdge_mem T hT n t)).2

private theorem nndist_dyadicEdgeAt_left_le
    (T : NNReal) (hT : 0 < T) (n : ℕ)
    (t : Set.Icc (0 : NNReal) T) :
    (nndist (dyadicLeft T n (dyadicEdgeAt T hT n t)).1 t.1.1 : ℝ) ≤
      (T : ℝ) / (2 : ℝ) ^ n := by
  let k := dyadicEdgeAt T hT n t
  let a : ℝ := (dyadicLeft T n k).1
  let x : ℝ := t.1
  let b : ℝ := (dyadicRight T n k).1
  have hl : dyadicLeft T n k ≤ t.1 := dyadicEdgeAt_left_le T hT n t
  have hr : t.1 ≤ dyadicRight T n k := dyadicEdgeAt_le_right T hT n t
  calc
    (nndist (dyadicLeft T n k).1 t.1.1 : ℝ) ≤
        (nndist (dyadicLeft T n k).1 (dyadicRight T n k).1 : ℝ) := by
      rw [coe_nndist, coe_nndist]
      change dist a x ≤ dist a b
      have hlr : a ≤ x := by
        exact_mod_cast hl
      have hrr : x ≤ b := by
        exact_mod_cast hr
      exact Real.dist_left_le_of_mem_uIcc (by
        rw [Set.uIcc_of_le (hlr.trans hrr)]
        exact ⟨hlr, hrr⟩)
    _ = (T : ℝ) / (2 : ℝ) ^ n :=
      nndist_dyadicLeft_dyadicRight T n k

private theorem fixedTimeGaussianExponent_le
    (T : NNReal) (hT : 0 < T) (n : ℕ)
    (t : Set.Icc (0 : NNReal) T)
    (hne : dyadicLeft T n (dyadicEdgeAt T hT n t) ≠ t.1) :
    -(compactDyadicModulus T n) ^ 2 /
        (2 * (nndist (dyadicLeft T n (dyadicEdgeAt T hT n t)).1 t.1.1 : ℝ)) ≤
      -(n + 1 : ℕ) := by
  let k := dyadicEdgeAt T hT n t
  have hdpos : 0 < (nndist (dyadicLeft T n k).1 t.1.1 : ℝ) := by
    rw [coe_nndist]
    exact dist_pos.mpr (by
      intro hv
      apply hne
      apply NNReal.eq
      simpa [k] using hv)
  have hlenpos : 0 < (nndist (dyadicLeft T n k).1
      (dyadicRight T n k).1 : ℝ) := by
    rw [nndist_dyadicLeft_dyadicRight]
    positivity
  have he := dyadicGaussianExponent_le T hT n k
  rw [div_le_iff₀ (mul_pos (by norm_num) hlenpos)] at he
  rw [div_le_iff₀ (mul_pos (by norm_num) hdpos)]
  exact he.trans (by
    have hd := nndist_dyadicEdgeAt_left_le T hT n t
    rw [← nndist_dyadicLeft_dyadicRight T n k] at hd
    have hn : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
    nlinarith)

/-- The fixed-time left-endpoint error has a geometric probability envelope.  The
fixed binders are `hcont,T,hT,t,n`; no simultaneous-in-time assertion is made. -/
theorem measure_fixedTime_leftError_le
    (hcont : BrownianCylinderContinuityAtEmpty)
    (T : NNReal) (hT : 0 < T) (t : Set.Icc (0 : NNReal) T) (n : ℕ) :
    brownianRawMeasure hcont
        {ω | compactDyadicModulus T n ≤
          |rawCoordinateProcess (dyadicLeft T n (dyadicEdgeAt T hT n t)) ω -
            rawCoordinateProcess t.1 ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(n + 1 : ℕ))) := by
  let _ := isProbabilityMeasure_brownianRawMeasure hcont
  by_cases heq : dyadicLeft T n (dyadicEdgeAt T hT n t) = t.1
  · have hmod : 0 < compactDyadicModulus T n := by
      unfold compactDyadicModulus
      positivity
    simp [heq, not_le_of_gt hmod]
  · have hr := measureReal_abs_rawCoordinateIncrement_ge_le hcont
      (dyadicLeft T n (dyadicEdgeAt T hT n t)) t.1
      (compactDyadicModulus_nonneg T n)
    calc
      brownianRawMeasure hcont {ω | compactDyadicModulus T n ≤
          |rawCoordinateProcess (dyadicLeft T n (dyadicEdgeAt T hT n t)) ω -
            rawCoordinateProcess t.1 ω|} =
          ENNReal.ofReal ((brownianRawMeasure hcont).real
            {ω | compactDyadicModulus T n ≤
              |rawCoordinateProcess (dyadicLeft T n (dyadicEdgeAt T hT n t)) ω -
                rawCoordinateProcess t.1 ω|}) := by
            symm
            exact ofReal_measureReal
      _ ≤ ENNReal.ofReal (2 * Real.exp
          (-(compactDyadicModulus T n) ^ 2 /
            (2 * (nndist
              (dyadicLeft T n (dyadicEdgeAt T hT n t)).1 t.1.1 : ℝ)))) :=
        ENNReal.ofReal_le_ofReal hr
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(n + 1 : ℕ))) := by
        gcongr
        exact fixedTimeGaussianExponent_le T hT n t heq

private def fixedTimeGaussianRatio : ENNReal :=
  ENNReal.ofReal (Real.exp (-1))

private def fixedTimeGaussianConstant : ENNReal :=
  ENNReal.ofReal (2 * Real.exp (-1))

private theorem fixedTimeGaussianRatio_lt_one :
    fixedTimeGaussianRatio < 1 := by
  exact ENNReal.ofReal_lt_one.2 (by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num))

private theorem measure_fixedTime_leftError_geometric_le
    (hcont : BrownianCylinderContinuityAtEmpty)
    (T : NNReal) (hT : 0 < T) (t : Set.Icc (0 : NNReal) T) (n : ℕ) :
    brownianRawMeasure hcont
        {ω | compactDyadicModulus T n ≤
          |rawCoordinateProcess (dyadicLeft T n (dyadicEdgeAt T hT n t)) ω -
            rawCoordinateProcess t.1 ω|} ≤
      fixedTimeGaussianConstant * fixedTimeGaussianRatio ^ n := by
  refine (measure_fixedTime_leftError_le hcont T hT t n).trans_eq ?_
  have hexp : Real.exp (-(n + 1 : ℕ)) =
      Real.exp (-1) * Real.exp (-1) ^ n := by
    rw [← pow_succ', ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  unfold fixedTimeGaussianConstant fixedTimeGaussianRatio
  rw [show 2 * (Real.exp (-1) * Real.exp (-1) ^ n) =
      (2 * Real.exp (-1)) * Real.exp (-1) ^ n by ring]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.exp (-1))]
  rw [ENNReal.ofReal_pow (Real.exp_pos (-1)).le]

/-- For a fixed compact-horizon time, almost every raw sample eventually differs
from the selected dyadic left endpoint by less than the prescribed modulus. -/
theorem ae_eventually_fixedTime_leftError_lt
    (hcont : BrownianCylinderContinuityAtEmpty)
    (T : NNReal) (hT : 0 < T) (t : Set.Icc (0 : NNReal) T) :
    ∀ᵐ ω ∂brownianRawMeasure hcont, ∀ᶠ n in atTop,
      |rawCoordinateProcess (dyadicLeft T n (dyadicEdgeAt T hT n t)) ω -
          rawCoordinateProcess t.1 ω| < compactDyadicModulus T n := by
  filter_upwards
    [ae_eventually_notMem_of_geometric_bound
      (μ := brownianRawMeasure hcont)
      (fun n => {ω | compactDyadicModulus T n ≤
        |rawCoordinateProcess (dyadicLeft T n (dyadicEdgeAt T hT n t)) ω -
          rawCoordinateProcess t.1 ω|})
      (C := fixedTimeGaussianConstant) (q := fixedTimeGaussianRatio)
      (by exact ENNReal.ofReal_ne_top)
      fixedTimeGaussianRatio_lt_one
      (measure_fixedTime_leftError_geometric_le hcont T hT t)] with ω hω
  filter_upwards [hω] with n hn
  simpa only [Set.mem_ofPred_eq, not_le] using hn

private theorem abs_canonicalRawDyadicInterpolant_sub_le
    (T : NNReal) (hT : 0 < T) (ω : BrownianRawPath) (n : ℕ)
    (t : Set.Icc (0 : NNReal) T) :
    |canonicalRawDyadicInterpolant T ω n t - rawCoordinateProcess t.1 ω| ≤
      |rawCoordinateProcess (dyadicLeft T n (dyadicEdgeAt T hT n t)) ω -
        rawCoordinateProcess t.1 ω| +
      |rawCoordinateProcess (dyadicRight T n (dyadicEdgeAt T hT n t)) ω -
        rawCoordinateProcess (dyadicLeft T n (dyadicEdgeAt T hT n t)) ω| := by
  let k := dyadicEdgeAt T hT n t
  let a : ℝ := (dyadicLeft T n k).1
  let b : ℝ := (dyadicRight T n k).1
  let x : ℝ := t.1
  let A := rawCoordinateProcess (dyadicLeft T n k) ω
  let B := rawCoordinateProcess (dyadicRight T n k) ω
  let Y := rawCoordinateProcess t.1 ω
  have hax : a ≤ x := by
    exact_mod_cast dyadicEdgeAt_left_le T hT n t
  have hxb : x ≤ b := by
    exact_mod_cast dyadicEdgeAt_le_right T hT n t
  have hab : a < b := by
    simp only [a, b, dyadicLeft, dyadicRight]
    have hp : (0 : NNReal) < (2 ^ n : ℕ) := by positivity
    exact_mod_cast (div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left (by exact_mod_cast Nat.lt_succ_self k.1) hT) hp)
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hβ0 : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hab.le)
  have hβ1 : (x - a) / (b - a) ≤ 1 := by
    rw [div_le_one (sub_pos.mpr hab)]
    linarith
  have hinterp :
      canonicalRawDyadicInterpolant T ω n t - Y =
        ((x - a) / (b - a)) * (B - A) + (A - Y) := by
    rw [canonicalRawDyadicInterpolant_apply_eq_affine T hT ω n k t
      (dyadicEdgeAt_left_le T hT n t) (dyadicEdgeAt_le_right T hT n t)]
    change ((b - x) / (b - a) * A + (x - a) / (b - a) * B) - Y =
      (x - a) / (b - a) * (B - A) + (A - Y)
    field_simp
    ring
  rw [hinterp]
  calc
    |(x - a) / (b - a) * (B - A) + (A - Y)| ≤
        |(x - a) / (b - a) * (B - A)| + |A - Y| := abs_add_le _ _
    _ = |(x - a) / (b - a)| * |B - A| + |A - Y| := by rw [abs_mul]
    _ ≤ |B - A| + |A - Y| := by
      have habs : |(x - a) / (b - a)| ≤ 1 := by
        rw [abs_of_nonneg hβ0]
        exact hβ1
      exact add_le_add
        (by simpa using mul_le_mul_of_nonneg_right habs (abs_nonneg (B - A)))
        le_rfl
    _ = |A - Y| + |B - A| := add_comm _ _

/-- At every fixed time on a positive compact horizon, the canonical raw dyadic
interpolants converge almost surely to the original raw coordinate.  The null set
may depend on the fixed time; no simultaneous-in-time assertion is made. -/
theorem ae_tendsto_canonicalRawDyadicInterpolant_eval
    (hcont : BrownianCylinderContinuityAtEmpty)
    (T : NNReal) (hT : 0 < T) (t : Set.Icc (0 : NNReal) T) :
    ∀ᵐ ω ∂brownianRawMeasure hcont,
      Tendsto (fun n => canonicalRawDyadicInterpolant T ω n t) atTop
        (𝓝 (rawCoordinateProcess t.1 ω)) := by
  filter_upwards
    [ae_eventually_fixedTime_leftError_lt hcont T hT t,
      ae_eventually_rawCoordinate_dyadic_modulus hcont T hT] with ω hleft hedge
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := (eventually_atTop.1 hleft)
  obtain ⟨N₂, hN₂⟩ := (eventually_atTop.1 hedge)
  obtain ⟨N₃, hN₃⟩ :=
    (Metric.tendsto_atTop.1
      (summable_compactDyadicModulus T).tendsto_atTop_zero)
      (ε / 2) (by linarith)
  refine ⟨max (max N₁ N₂) N₃, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans
    ((le_max_left (max N₁ N₂) N₃).trans hn)
  have hn₂ : N₂ ≤ n := (le_max_right N₁ N₂).trans
    ((le_max_left (max N₁ N₂) N₃).trans hn)
  have hn₃ : N₃ ≤ n := (le_max_right (max N₁ N₂) N₃).trans hn
  have hleftn := hN₁ n hn₁
  have hedgen := hN₂ n hn₂ (dyadicEdgeAt T hT n t)
  have hmod : compactDyadicModulus T n < ε / 2 := by
    have := hN₃ n hn₃
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (compactDyadicModulus_nonneg T n)] using this
  rw [Real.dist_eq]
  refine lt_of_le_of_lt
    (abs_canonicalRawDyadicInterpolant_sub_le T hT ω n t) ?_
  have hedge' :
      |rawCoordinateProcess
          (dyadicRight T n (dyadicEdgeAt T hT n t)) ω -
        rawCoordinateProcess
          (dyadicLeft T n (dyadicEdgeAt T hT n t)) ω| <
        compactDyadicModulus T n := by
    simpa only [abs_sub_comm] using hedgen
  linarith

/-- On a positive compact horizon, all residual facts for the fixed canonical
nodal-hat approximants are unconditional consequences of the raw Brownian
finite-dimensional law. -/
theorem brownianCanonicalDyadicInterpolationFacts
    (hcont : BrownianCylinderContinuityAtEmpty)
    (T : NNReal) (hT : 0 < T) :
    BrownianCanonicalDyadicInterpolationFacts hcont T where
  isRawDyadicPiecewiseLinear :=
    isRawDyadicPiecewiseLinear_canonicalRawDyadicInterpolant T hT
  unique_isRawDyadicPiecewiseLinear :=
    eq_canonicalRawDyadicInterpolant_of_isRawDyadicPiecewiseLinear T hT
  badStep_subset :=
    canonicalRawDyadicInterpolant_badStep_subset T hT
  eval_tendsto :=
    ae_tendsto_canonicalRawDyadicInterpolant_eval hcont T hT

/-- **Unconditional compact-horizon Brownian modification closure.**  For every
positive horizon, the explicit canonical dyadic interpolants converge in compact
path space almost surely to a measurable continuous path whose value at each fixed
time agrees almost surely with the raw Brownian coordinate.  The quantifier order
is `hcont,T,hT`, then the path and fixed-time conclusions; this theorem does not
yet glue the compact horizons into a single path on all of `ℝ≥0`. -/
theorem exists_measurable_compactPath_modification
    (hcont : BrownianCylinderContinuityAtEmpty)
    (T : NNReal) (hT : 0 < T) :
    ∃ F : BrownianRawPath → CompactPath T,
      Measurable F ∧
      (∀ᵐ ω ∂brownianRawMeasure hcont,
        Tendsto (canonicalRawDyadicInterpolant T ω) atTop (𝓝 (F ω))) ∧
      ∀ t : Set.Icc (0 : NNReal) T,
        (fun ω => F ω t) =ᵐ[brownianRawMeasure hcont]
          rawCoordinateProcess t.1 :=
  exists_measurable_compactPath_modification_of_canonical_facts
    hcont T hT (brownianCanonicalDyadicInterpolationFacts hcont T hT)

end BrownianCanonicalDyadicEvalClosure
end BlockBand.SourceProcess.WienerRecovery.CEH
