module

public import BlockBand.Critical.RelativeVectors.GenDiffBound

/-!
# The generator difference at one time, in row-tail form

For labels `j ∉ J` the sums of squared Hilbert–Schmidt norms of `T_j` are bounded by a fixed
multiple of the row tail of the propagator, and inside `J` the floor vanishes.

`genDiff_rowTail_le`: the bound `generatorDiff_backward_le` with
* `X_i = X_J` on the window `J` and `X_i = X_ext` off it,
* the cross bound `crossBoundFun_le` (`|c_ij| ≤ c̄` for `|i-j| ≥ ℓ`, rows of norm `≤ 1`),
* the floor `β̂_i = β_i` on `J` and `|β̂_i - β_i| ≤ b_f` everywhere,
* the square roots removed by `√x ≤ (x/ε + ε)/2` (any `ε > 0`; this replaces the Jensen and
  Cauchy–Schwarz steps `∫√τ ≤ (∫τ)^{1/2}` and needs no measurability of square roots),

collected in the form `|𝒜g - 𝓛_ref g| ≤ Q₀ + Q₁ R`, where `R = Σ_m ∫ rowTail(M) J (ι m) dP` is
the tested row tail of the propagator (the quantity of the finite-speed bound).
`sum_tau_off_eq`: `Σ_{i ∉ J} ∫ τ_i = R`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.CoarseRelative

variable {N r k : ℕ}

/-- `√x ≤ (x/ε + ε)/2` for `x ≥ 0`, `ε > 0`. -/
theorem sqrt_le_amgm {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) : Real.sqrt x ≤ (x / ε + ε) / 2 := by
  have hs := Real.sq_sqrt hx
  have h0 := Real.sqrt_nonneg x
  rw [div_add' _ _ _ hε.ne', div_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt x - ε)]

/-- `∫ √f ≤ (∫ f/ε + ε)/2` on a probability space. -/
theorem integral_sqrt_le_amgm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Integrable f P) (hf0 : ∀ ω, 0 ≤ f ω)
    (hs : Integrable (fun ω => Real.sqrt (f ω)) P) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, Real.sqrt (f ω) ∂P ≤ ((∫ ω, f ω ∂P) / ε + ε) / 2 := by
  have hg : Integrable (fun ω => (f ω / ε + ε) / 2) P :=
    ((hf.div_const ε).add (integrable_const ε)).div_const 2
  refine (integral_mono hs hg fun ω => sqrt_le_amgm (hf0 ω) hε).trans (le_of_eq ?_)
  have e : ∫ ω, (f ω / ε + ε) / 2 ∂P = (∫ ω, f ω / ε + ε ∂P) / 2 := integral_div _ _
  rw [e, integral_add (hf.div_const ε) (integrable_const ε), integral_div, integral_const]
  simp

/-- Tested row tail of a propagator: `R = Σ_m ∫ rowTail(M) J (ι m) dP`. -/
def testedTail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ι : Fin k → Fin N)
    (M : Ω → Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) : ℝ :=
  ∑ m, ∫ ω, rowTail (M ω) J (ι m) ∂P

section Backward

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M : Ω → Matrix (Fin N) (Fin N) ℂ} {Ξ : Ω → Fin N → Fin r → ℂ}
  {φ : (Fin k → Fin r → ℂ) → ℝ}

theorem integrable_rowTail {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (J : Finset (Fin N)) (a : Fin N) :
    Integrable (fun ω => rowTail (M ω) J a) P := by
  have hc : Continuous fun A : Matrix (Fin N) (Fin N) ℂ => rowTail A J a := by
    unfold rowTail
    refine continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · exact continuous_const
    · exact (continuous_id.matrix_elem a j).norm.pow 2
  refine Integrable.of_bound (μ := P) (hc.measurable.comp hS.measM).aestronglyMeasurable
    (N : ℝ) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (rowTail_nonneg _ _ _)]
  unfold rowTail
  calc ∑ j, (if j ∈ J then 0 else ‖M ω a j‖ ^ 2) ≤ ∑ _j : Fin N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs
        · exact zero_le_one
        · have := hS.entry ω a j
          have h0 := norm_nonneg (M ω a j)
          nlinarith
    _ = N := by simp

omit [IsProbabilityMeasure P] in
theorem testedTail_nonneg (ι : Fin k → Fin N) (M : Ω → Matrix (Fin N) (Fin N) ℂ)
    (J : Finset (Fin N)) : 0 ≤ testedTail P ι M J :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => rowTail_nonneg _ _ _

/-- `Σ_{i ∉ J} ∫ τ_i = Σ_m ∫ rowTail(M) J (ι m)`. -/
theorem sum_tau_off_eq (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (J : Finset (Fin N)) :
    ∑ i, (if i ∈ J then 0 else ∫ ω, tau (fun m => M ω (ι m) i) ∂P) = testedTail P ι M J := by
  unfold testedTail
  have h1 : ∀ i, (if i ∈ J then 0 else ∫ ω, tau (fun m => M ω (ι m) i) ∂P) =
      ∫ ω, (if i ∈ J then 0 else tau (fun m => M ω (ι m) i)) ∂P := by
    intro i; split_ifs <;> simp
  simp_rw [h1]
  rw [← integral_finsetSum _ fun i _ => ?_, ← integral_finsetSum _ fun m _ =>
    integrable_rowTail hS J (ι m)]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [rowTail, tau]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · by_cases hi : i ∈ J
    · simp [hi]
    · simpa [hi] using integrable_tau ι hS i

theorem sum_tau_le_card (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂)
    (hrow : ∀ ω a, ∑ b, ‖M ω a b‖ ^ 2 ≤ 1) :
    ∑ i, ∫ ω, tau (fun m => M ω (ι m) i) ∂P ≤ k := by
  rw [← integral_finsetSum _ fun i _ => integrable_tau ι hS i]
  calc ∫ ω, ∑ i, tau (fun m => M ω (ι m) i) ∂P ≤ ∫ _ω, (k : ℝ) ∂P :=
        integral_mono (integrable_finsetSum _ fun i _ => integrable_tau ι hS i)
          (integrable_const _) fun ω => sum_tau_le ι (hrow ω)
    _ = k := by simp

/-- **The generator difference in row-tail form.** See the module docstring. -/
theorem genDiff_rowTail_le (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂)
    (hg : ContDiff ℝ 2 (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P))
    (hinv : ∀ u : Fin N → ℂ, (∀ i, ‖u i‖ = 1) → ∀ z,
      (∫ ω, φ (testProj ι (arrayMul (M ω) (phaseCLM u z) + Ξ ω)) ∂P) =
        ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)
    (hrow : ∀ ω a, ∑ b, ‖M ω a b‖ ^ 2 ≤ 1)
    (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ωf : FlowSample N) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (σ : ℝ) (z : Fin N → Fin r → ℂ) (J : Finset (Fin N)) {B Z : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (hzJ : ∀ i ∈ J, ∀ q, ‖z i q‖ ^ 2 ≤ B) (hz : ∀ i q, ‖z i q‖ ≤ Z)
    {cbar XJ Xext bf ε : ℝ} (hc0 : 0 ≤ cbar)
    (hc : ∀ i j, ℓ ≤ labelDist i j → |dysonCoupling N (flowEigenvalue F a ωf σ) i j| ≤ cbar)
    (hXJ0 : 0 ≤ XJ)
    (hXJ : ∀ i ∈ J, ∀ p : Fin r → ℂ, |∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N (flowEigenvalue F a ωf σ) i j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| ≤
        XJ * nsq p)
    (hXext : ∀ i ∉ J, ∀ p : Fin r → ℂ, |∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N (flowEigenvalue F a ωf σ) i j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| ≤
        Xext * nsq p)
    (hbf0 : 0 ≤ bf)
    (hfl : ∀ i ∈ J, refDamping F a b₀ ωf ℓ σ i = longCoupling F a ωf ℓ σ i)
    (hbf : ∀ i, |refDamping F a b₀ ωf ℓ σ i - longCoupling F a ωf ℓ σ i| ≤ bf)
    (hε : 0 < ε) :
    |complexAngularGenerator N r (flowEigenvalue F a ωf σ)
        (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P) z -
      referenceArrayGenerator F a b₀ ωf ℓ σ
        (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P) z| ≤
      (K₂ * (2 * (r : ℝ) ^ 2 * k * XJ + ((k : ℝ) * r) ^ 2 * (B * (Real.sqrt 2 * cbar))) +
          K₂ * (Z * Z * (cbar * N)) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * ε +
          bf * (1 / 2 * K₁ * Z) * ((N : ℝ) * ε / 2)) +
        (K₂ * (2 * (r : ℝ) ^ 2 * Xext) + bf * (1 / 2 * r * K₂) +
          K₂ * (Z * Z * (cbar * N)) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 / ε +
          bf * (1 / 2 * K₁ * Z) / (2 * ε)) * testedTail P ι M J := by
  classical
  set R := testedTail P ι M J with hRdef
  have hR0 : 0 ≤ R := testedTail_nonneg ι M J
  set X : Fin N → ℝ := fun i => if i ∈ J then XJ else Xext with hXdef
  have hX : ∀ i (p : Fin r → ℂ), |∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N (flowEigenvalue F a ωf σ) i j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| ≤
        X i * nsq p := by
    intro i p
    by_cases hi : i ∈ J
    · simpa [hXdef, hi] using hXJ i hi p
    · simpa [hXdef, hi] using hXext i hi p
  have hmain := generatorDiff_backward_le ι hS hg hinv F a b₀ ωf hℓ σ z J hB hZ hzJ hz X hX
  refine hmain.trans ?_
  set τ : Fin N → ℝ := fun i => ∫ ω, tau (fun m => M ω (ι m) i) ∂P with hτ
  have hτ0 : ∀ i, 0 ≤ τ i := fun i => integral_nonneg fun ω => tau_nonneg _
  have hK₁ := hS.nonneg1
  have hK₂ := hS.nonneg2
  -- diagonal
  have hdiag : ∑ i, X i * τ i ≤ XJ * k + Xext * R := by
    have hs : ∑ i, X i * τ i = XJ * ∑ i, (if i ∈ J then τ i else 0) +
        Xext * ∑ i, (if i ∈ J then 0 else τ i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i ∈ J <;> simp [hXdef, hi]
    rw [hs, sum_tau_off_eq ι hS J]
    have h1 : ∑ i, (if i ∈ J then τ i else 0) ≤ k := by
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_tau_le_card ι hS hrow)
      split_ifs
      · exact le_rfl
      · exact hτ0 i
    have := mul_le_mul_of_nonneg_left h1 hXJ0
    linarith
  -- cross
  have hrowT : ∀ m, ∫ ω, Real.sqrt (rowTail (M ω) J (ι m)) ∂P ≤ (R / ε + ε) / 2 := by
    intro m
    have hc : Continuous fun A : Matrix (Fin N) (Fin N) ℂ => Real.sqrt (rowTail A J (ι m)) := by
      unfold rowTail
      refine (continuous_finsetSum _ fun j _ => ?_).sqrt
      split_ifs
      · exact continuous_const
      · exact (continuous_id.matrix_elem (ι m) j).norm.pow 2
    have hint : Integrable (fun ω => Real.sqrt (rowTail (M ω) J (ι m))) P := by
      refine Integrable.of_bound (μ := P) (hc.measurable.comp hS.measM).aestronglyMeasurable
        1 (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      refine Real.sqrt_le_one.mpr ?_
      refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hrow ω (ι m))
      split_ifs
      · positivity
      · exact le_rfl
    refine (integral_sqrt_le_amgm (integrable_rowTail hS J (ι m))
      (fun ω => rowTail_nonneg _ _ _) hint hε).trans ?_
    have hTm : ∫ ω, rowTail (M ω) J (ι m) ∂P ≤ R := by
      rw [hRdef, testedTail]
      exact Finset.single_le_sum (f := fun m => ∫ ω, rowTail (M ω) J (ι m) ∂P)
        (fun _ _ => integral_nonneg fun _ => rowTail_nonneg _ _ _) (Finset.mem_univ m)
    have : (∫ ω, rowTail (M ω) J (ι m) ∂P) / ε ≤ R / ε := div_le_div_of_nonneg_right hTm hε.le
    linarith
  have hcross : ∀ m m' : Fin k, ∫ ω, crossBoundFun ι (flowEigenvalue F a ωf σ) ℓ J B Z (M ω)
      m m' ∂P ≤ B * (Real.sqrt 2 * cbar) + Z * Z * (cbar * N) * (R / ε + ε) := by
    intro m m'
    have hbd := fun ω => crossBoundFun_le ι (flowEigenvalue F a ωf σ) ℓ J (Z := Z) hB (M ω)
      (hrow ω) hc0 hc m m'
    have hc1 := continuous_crossBoundFun ι (flowEigenvalue F a ωf σ) ℓ J B Z m m'
    have hsq : ∀ (a' : Fin N) (A : Matrix (Fin N) (Fin N) ℂ), Continuous
        (fun A : Matrix (Fin N) (Fin N) ℂ => Real.sqrt (rowTail A J a')) := by
      intro a' _
      unfold rowTail
      refine (continuous_finsetSum _ fun j _ => ?_).sqrt
      split_ifs
      · exact continuous_const
      · exact (continuous_id.matrix_elem a' j).norm.pow 2
    have hintS : ∀ a', Integrable (fun ω => Real.sqrt (rowTail (M ω) J a')) P := by
      intro a'
      refine Integrable.of_bound (μ := P)
        (((hsq a' 1).measurable.comp hS.measM).aestronglyMeasurable) 1
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      refine Real.sqrt_le_one.mpr ?_
      refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hrow ω a')
      split_ifs
      · positivity
      · exact le_rfl
    have hintR : Integrable (fun ω => B * (Real.sqrt 2 * cbar) + Z * Z * (cbar * N *
        (Real.sqrt (rowTail (M ω) J (ι m)) + Real.sqrt (rowTail (M ω) J (ι m'))))) P :=
      (integrable_const _).add ((((hintS (ι m)).add (hintS (ι m'))).const_mul _).const_mul _)
    have hintL : Integrable (fun ω => crossBoundFun ι (flowEigenvalue F a ωf σ) ℓ J B Z (M ω)
        m m') P := by
      refine hintR.mono' (hc1.measurable.comp hS.measM).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have h0 : 0 ≤ crossBoundFun ι (flowEigenvalue F a ωf σ) ℓ J B Z (M ω) m m' := by
        unfold crossBoundFun
        have : 0 ≤ Z * Z := mul_self_nonneg Z
        refine add_nonneg (mul_nonneg hB (Real.sqrt_nonneg _)) (mul_nonneg this ?_)
        refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
        split_ifs <;> positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hbd ω
    refine (integral_mono hintL hintR hbd).trans ?_
    have e1 : ∫ ω, B * (Real.sqrt 2 * cbar) + Z * Z * (cbar * N *
        (Real.sqrt (rowTail (M ω) J (ι m)) + Real.sqrt (rowTail (M ω) J (ι m')))) ∂P =
        B * (Real.sqrt 2 * cbar) + Z * Z * (cbar * N *
          (∫ ω, Real.sqrt (rowTail (M ω) J (ι m)) ∂P +
            ∫ ω, Real.sqrt (rowTail (M ω) J (ι m')) ∂P)) := by
      have i2 : Integrable (fun ω => Z * Z * (cbar * N *
          (Real.sqrt (rowTail (M ω) J (ι m)) + Real.sqrt (rowTail (M ω) J (ι m'))))) P :=
        (((hintS (ι m)).add (hintS (ι m'))).const_mul _).const_mul _
      rw [integral_add (integrable_const _) i2, integral_const]
      rw [integral_const_mul, integral_const_mul, integral_add (hintS (ι m)) (hintS (ι m'))]
      simp
    rw [e1]
    have h1 := hrowT m
    have h2 := hrowT m'
    have hZZ : 0 ≤ Z * Z := mul_self_nonneg Z
    have hcN : 0 ≤ cbar * N := by positivity
    have : Z * Z * (cbar * N * (∫ ω, Real.sqrt (rowTail (M ω) J (ι m)) ∂P +
        ∫ ω, Real.sqrt (rowTail (M ω) J (ι m')) ∂P)) ≤
        Z * Z * (cbar * N * ((R / ε + ε) / 2 + (R / ε + ε) / 2)) := by gcongr
    nlinarith
  have hcrossSum : ∑ m', ∑ _q' : Fin r, ∑ m, ∑ _q : Fin r,
      ∫ ω, crossBoundFun ι (flowEigenvalue F a ωf σ) ℓ J B Z (M ω) m m' ∂P ≤
      ((k : ℝ) * r) ^ 2 * (B * (Real.sqrt 2 * cbar) + Z * Z * (cbar * N) * (R / ε + ε)) := by
    calc _ ≤ ∑ _m' : Fin k, ∑ _q' : Fin r, ∑ _m : Fin k, ∑ _q : Fin r,
          (B * (Real.sqrt 2 * cbar) + Z * Z * (cbar * N) * (R / ε + ε)) :=
          Finset.sum_le_sum fun m' _ => Finset.sum_le_sum fun _ _ =>
            Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun _ _ => hcross m m'
      _ = _ := by simp; ring
  -- floor
  have hfloor : ∑ i, |refDamping F a b₀ ωf ℓ σ i - longCoupling F a ωf ℓ σ i| *
      (1 / 2 * K₁ * ‖z i‖ * ∫ ω, Real.sqrt (tau (fun m => M ω (ι m) i)) ∂P +
        1 / 2 * r * K₂ * τ i) ≤
      bf * (1 / 2 * K₁ * Z) * ((R / ε + N * ε) / 2) + bf * (1 / 2 * r * K₂) * R := by
    have hzi : ∀ i, ‖z i‖ ≤ Z := fun i => (pi_norm_le_iff_of_nonneg hZ).mpr fun q => hz i q
    have hsqrt : ∀ i, ∫ ω, Real.sqrt (tau (fun m => M ω (ι m) i)) ∂P ≤ (τ i / ε + ε) / 2 := by
      intro i
      exact integral_sqrt_le_amgm (integrable_tau ι hS i) (fun ω => tau_nonneg _)
        (integrable_sqrt_tau ι hS i) hε
    have hpt : ∀ i, |refDamping F a b₀ ωf ℓ σ i - longCoupling F a ωf ℓ σ i| *
        (1 / 2 * K₁ * ‖z i‖ * ∫ ω, Real.sqrt (tau (fun m => M ω (ι m) i)) ∂P +
          1 / 2 * r * K₂ * τ i) ≤
        if i ∈ J then 0 else bf * (1 / 2 * K₁ * Z * ((τ i / ε + ε) / 2) + 1 / 2 * r * K₂ * τ i) := by
      intro i
      by_cases hi : i ∈ J
      · simp [hi, hfl i hi]
      · simp only [hi, ite_false]
        refine mul_le_mul (hbf i) ?_ (by
          have := integral_nonneg (μ := P) (f := fun ω => Real.sqrt (tau (fun m => M ω (ι m) i))) fun ω => Real.sqrt_nonneg _
          have := hτ0 i
          have := norm_nonneg (z i)
          positivity) hbf0
        have hs0 := integral_nonneg (μ := P) (f := fun ω => Real.sqrt (tau (fun m => M ω (ι m) i))) fun ω => Real.sqrt_nonneg _
        have h1 : 1 / 2 * K₁ * ‖z i‖ * ∫ ω, Real.sqrt (tau (fun m => M ω (ι m) i)) ∂P ≤
            1 / 2 * K₁ * Z * ((τ i / ε + ε) / 2) := by
          have := norm_nonneg (z i)
          gcongr
          · exact hzi i
          · exact hsqrt i
        linarith
    refine (Finset.sum_le_sum fun i _ => hpt i).trans ?_
    have hoff := sum_tau_off_eq ι hS J
    have hcard : ∑ i : Fin N, (if i ∈ J then (0 : ℝ) else ε) ≤ N * ε := by
      calc _ ≤ ∑ _i : Fin N, ε := Finset.sum_le_sum fun i _ => by split_ifs <;> linarith
        _ = N * ε := by simp
    have hsplit : ∀ i, (if i ∈ J then (0 : ℝ) else
        bf * (1 / 2 * K₁ * Z * ((τ i / ε + ε) / 2) + 1 / 2 * r * K₂ * τ i)) =
        bf * (1 / 2 * K₁ * Z) / 2 / ε * (if i ∈ J then 0 else τ i) +
          bf * (1 / 2 * K₁ * Z) / 2 * (if i ∈ J then 0 else ε) +
          bf * (1 / 2 * r * K₂) * (if i ∈ J then 0 else τ i) := by
      intro i
      split_ifs
      · ring
      · field_simp
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [hτ] at hoff ⊢
    rw [hoff]
    have hc' : 0 ≤ bf * (1 / 2 * K₁ * Z) / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hcard hc'
    have e : bf * (1 / 2 * K₁ * Z) * ((R / ε + N * ε) / 2) =
        bf * (1 / 2 * K₁ * Z) / 2 / ε * R + bf * (1 / 2 * K₁ * Z) / 2 * (N * ε) := by
      field_simp
    rw [e]
    linarith
  have hZZ : 0 ≤ Z * Z := mul_self_nonneg Z
  have hdiag' := mul_le_mul_of_nonneg_left hdiag (by positivity : (0 : ℝ) ≤ 2 * r ^ 2 * K₂)
  have hcross' := mul_le_mul_of_nonneg_left hcrossSum hK₂
  calc _ ≤ 2 * (r : ℝ) ^ 2 * K₂ * (XJ * k + Xext * R) +
        K₂ * (((k : ℝ) * r) ^ 2 * (B * (Real.sqrt 2 * cbar) + Z * Z * (cbar * N) * (R / ε + ε))) +
        (bf * (1 / 2 * K₁ * Z) * ((R / ε + N * ε) / 2) + bf * (1 / 2 * r * K₂) * R) := by
        simp only [hτ] at hdiag' hfloor
        gcongr
    _ = _ := by field_simp; ring

end Backward

end BlockBand.Critical.RelativeVectors
