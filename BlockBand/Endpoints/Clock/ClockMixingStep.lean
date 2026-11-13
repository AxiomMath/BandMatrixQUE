module

public import BlockBand.Endpoints.Clock.ClockMixingMeasure

/-!
# The clock-mixing lemma: the conditional one-layer bounds

We consider a deterministic past (an old Hermitian `X` and a positive semidefinite clock `Q`) and
one fresh layer of law `freshLaw W b`, with `T₊ = L f₊ L*` and its mean `ET₊`.

* `eLpNorm_sqrt_wsum_le`: the `L^{p/2}`-Minkowski step for square functions,
  `‖(Σ_k w_k |c_k|²)^{1/2}‖_p ≤ (Σ_k w_k ‖c_k‖_p²)^{1/2}` for `p ≥ 2`, `w ≥ 0`;
* `condTrace_le`: if every centered bilinear entry `u*(T₊ - ET₊)v` has `L^p` norm
  `≤ c‖u‖‖v‖`, then `‖Tr(Q(T₊ - θf))‖_p ≤ (‖ET₊ - θf‖ + c) Tr Q`
  (the trace version of the Minkowski step);
* `condHS_le`: under the same hypothesis at an order `r ≥ max(p,2)`,
  `‖‖Q^{1/2}(T₊ - θf)Q^{1/2}‖_HS‖_p ≤ (‖ET₊ - θf‖ + c) Tr Q`, "independent of the number of
  nonzero eigenvalues of `Q`";
* `condSq_le`: `‖g²‖_p ≤ C²` from `‖g‖_{2p} ≤ C`;
* `X_isHermitian`, `Y_posSemidef`, `Q_posSemidef`, `ae_blocks_isHermitian`: the Hermitian and
  positivity structure of the chain.

No contract is used here: the centered-entry bound and the mean are hypotheses of the lemmas,
supplied in `clockMixing_of` by `PassiveSourceMixingContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexConjugate Matrix Matrix.Norms.L2Operator ComplexOrder

namespace ClockMixingProb

open ClockMixingAlg

section Cond

variable {S : Type*} [MeasurableSpace S] {ν : Measure S} [IsProbabilityMeasure ν]

theorem eLpNorm_const_prob {F : Type*} [NormedAddCommGroup F] (c : F) {p : ℝ≥0∞}
    (hp : p ≠ 0) : eLpNorm (fun _ : S => c) p ν = ‖c‖ₑ := by
  rw [eLpNorm_const c hp (IsProbabilityMeasure.ne_zero ν), measure_univ, ENNReal.one_rpow,
    mul_one]

omit [IsProbabilityMeasure ν] in
theorem eLpNorm_real_mul_le {f : S → ℝ} (c : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => c * f x) p ν = ENNReal.ofReal |c| * eLpNorm f p ν := by
  have h := eLpNorm_const_smul c f p ν
  rw [Real.enorm_eq_ofReal_abs] at h
  exact h

omit [IsProbabilityMeasure ν] in
/-- **`L^{p/2}`-Minkowski for square functions**: for `r ≥ 2`, `w ≥ 0`,
`‖(Σ_k w_k |c_k|²)^{1/2}‖_r ≤ (Σ_k w_k B_k²)^{1/2}` whenever `‖c_k‖_r ≤ B_k`. -/
theorem eLpNorm_sqrt_wsum_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k)
    (c : ι → S → ℂ) (hc : ∀ k, Measurable (c k)) {r : ℝ} (hr : 2 ≤ r) (B : ι → ℝ)
    (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k, eLpNorm (c k) (ENNReal.ofReal r) ν ≤ ENNReal.ofReal (B k)) :
    eLpNorm (fun y => Real.sqrt (∑ k, w k * ‖c k y‖ ^ 2)) (ENNReal.ofReal r) ν ≤
      ENNReal.ofReal (Real.sqrt (∑ k, w k * B k ^ 2)) := by
  set F : S → ℝ := fun y => ∑ k, w k * ‖c k y‖ ^ 2 with hF
  have hFm : Measurable F :=
    Finset.measurable_sum _ fun k _ => measurable_const.mul ((hc k).norm.pow_const 2)
  have hF0 : ∀ y, 0 ≤ F y := fun y =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (sq_nonneg _)
  have hsm : AEStronglyMeasurable (fun y => Real.sqrt (F y)) ν :=
    (Real.continuous_sqrt.measurable.comp hFm).aestronglyMeasurable
  have hr2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (r / 2) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  -- `‖√F‖_r^2 = ‖F‖_{r/2}`
  have hsq := eLpNorm_norm_rpow (p := ENNReal.ofReal (r / 2)) (μ := ν)
    (fun y => Real.sqrt (F y)) hsm (q := 2) two_pos
  have hrr : ENNReal.ofReal (r / 2) * ENNReal.ofReal 2 = ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_mul (by linarith)]; congr 1; ring
  rw [hrr] at hsq
  have hFeq : (fun y => ‖Real.sqrt (F y)‖ ^ (2 : ℝ)) = F := by
    funext y
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.rpow_two, Real.sq_sqrt (hF0 y)]
  rw [hFeq] at hsq
  -- `‖F‖_{r/2} ≤ Σ_k w_k ‖c_k‖_r^2`
  have hsum : eLpNorm F (ENNReal.ofReal (r / 2)) ν ≤ ENNReal.ofReal (∑ k, w k * B k ^ 2) := by
    have hFs : F = ∑ k, fun y => w k * ‖c k y‖ ^ 2 := by
      funext y; simp [hF, Finset.sum_apply]
    rw [hFs]
    refine (eLpNorm_sum_le hr2).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg (hw k) (sq_nonneg _)]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [eLpNorm_real_mul_le, abs_of_nonneg (hw k), ENNReal.ofReal_mul (hw k)]
    gcongr
    have hk := eLpNorm_norm_rpow (p := ENNReal.ofReal (r / 2)) (μ := ν) (c k)
      (hc k).aestronglyMeasurable (q := 2) two_pos
    rw [hrr] at hk
    have hfun : (fun y => ‖c k y‖ ^ (2 : ℝ)) = fun y => ‖c k y‖ ^ 2 := by
      funext y; rw [Real.rpow_two]
    rw [hfun] at hk
    rw [hk]
    calc eLpNorm (c k) (ENNReal.ofReal r) ν ^ (2 : ℝ) ≤ (ENNReal.ofReal (B k)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (hB k) zero_le_two
      _ = ENNReal.ofReal (B k ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (hB0 k) zero_le_two, Real.rpow_two]
  rw [hsq] at hsum
  show eLpNorm (fun y => Real.sqrt (F y)) (ENNReal.ofReal r) ν ≤ _
  have hS0 : 0 ≤ ∑ k, w k * B k ^ 2 := Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (sq_nonneg _)
  have h2 := ENNReal.rpow_le_rpow hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hS0 (by norm_num), ← Real.sqrt_eq_rpow] at h2
  exact h2

variable {W : ℕ}

/-- **Conditional trace bound**. -/
theorem condTrace_le {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (f : Matrix (Fin W) (Fin W) ℂ) (θ : ℂ) {T : S → Matrix (Fin W) (Fin W) ℂ}
    {p : ℝ} (hp : 1 ≤ p) {c : ℝ} (hc : 0 ≤ c)
    (hfl : ∀ u v : Fin W → ℂ, eLpNorm (fun ξ => bilinear u (T ξ - matrixExpect ν T) v)
      (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (c * vecNorm u * vecNorm v)) :
    eLpNorm (fun ξ => (Q * (T ξ - θ • f)).trace) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal ((‖matrixExpect ν T - θ • f‖ + c) * Q.trace.re) := by
  set R := matrixExpect ν T - θ • f
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hdec : (fun ξ => (Q * (T ξ - θ • f)).trace) =
      (fun _ => (Q * R).trace) + ∑ i, fun ξ =>
        (hQ.1.eigenvalues i : ℂ) * bilinear (fun a => eU hQ.1 a i) (T ξ - matrixExpect ν T)
          (fun a => eU hQ.1 a i) := by
    funext ξ
    have : T ξ - θ • f = R + (T ξ - matrixExpect ν T) := by simp only [R]; abel
    rw [Pi.add_apply, Finset.sum_apply, this, Matrix.mul_add, trace_add, trace_mul_eq_sum hQ.1
      (T ξ - matrixExpect ν T)]
    simp only [rot_apply]
  rw [hdec]
  refine (eLpNorm_add_le (ε := ℂ) hp1).trans ?_
  rw [eLpNorm_const_prob _ hp0]
  refine (add_le_add le_rfl (eLpNorm_sum_le (ε' := ℂ) hp1)).trans ?_
  have h1 : ‖(Q * R).trace‖ₑ ≤ ENNReal.ofReal (‖R‖ * Q.trace.re) := by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (norm_trace_mul_le hQ R)
  have h2 : ∑ i, eLpNorm (fun ξ => (hQ.1.eigenvalues i : ℂ) * bilinear (fun a => eU hQ.1 a i)
      (T ξ - matrixExpect ν T) (fun a => eU hQ.1 a i)) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (c * Q.trace.re) := by
    rw [trace_re_eq_sum hQ.1, Finset.mul_sum,
      ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg hc (hQ.eigenvalues_nonneg i)]
    refine Finset.sum_le_sum fun i _ => ?_
    have hs := eLpNorm_const_smul (hQ.1.eigenvalues i : ℂ) (fun ξ => bilinear
      (fun a => eU hQ.1 a i) (T ξ - matrixExpect ν T) (fun a => eU hQ.1 a i)) (ENNReal.ofReal p) ν
    simp only [Pi.smul_def, smul_eq_mul] at hs
    rw [hs]
    have hb := hfl (fun a => eU hQ.1 a i) (fun a => eU hQ.1 a i)
    rw [vecNorm_eU_col, mul_one, mul_one] at hb
    rw [show c * hQ.1.eigenvalues i = hQ.1.eigenvalues i * c by ring,
      ENNReal.ofReal_mul (hQ.eigenvalues_nonneg i), ← ofReal_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hQ.eigenvalues_nonneg i)]
    gcongr
  calc ‖(Q * R).trace‖ₑ + ∑ i, eLpNorm (fun ξ => (hQ.1.eigenvalues i : ℂ) *
        bilinear (fun a => eU hQ.1 a i) (T ξ - matrixExpect ν T) (fun a => eU hQ.1 a i))
          (ENNReal.ofReal p) ν
      ≤ ENNReal.ofReal (‖R‖ * Q.trace.re) + ENNReal.ofReal (c * Q.trace.re) := add_le_add h1 h2
    _ = ENNReal.ofReal ((‖R‖ + c) * Q.trace.re) := by
      rw [← ENNReal.ofReal_add (mul_nonneg (norm_nonneg _) (trace_re_nonneg hQ))
        (mul_nonneg hc (trace_re_nonneg hQ))]
      congr 1; ring

/-- **Conditional Hilbert–Schmidt bound**: Minkowski in `L^{r/2}` over the
eigenbasis of `Q`, at an order `r ≥ max(p, 2)`. -/
theorem condHS_le {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (f : Matrix (Fin W) (Fin W) ℂ) (θ : ℂ) {T : S → Matrix (Fin W) (Fin W) ℂ}
    (hT : Measurable T) {p r : ℝ} (hp : 1 ≤ p) (hpr : p ≤ r) (hr : 2 ≤ r) {c : ℝ} (hc : 0 ≤ c)
    (hfl : ∀ u v : Fin W → ℂ, eLpNorm (fun ξ => bilinear u (T ξ - matrixExpect ν T) v)
      (ENNReal.ofReal r) ν ≤ ENNReal.ofReal (c * vecNorm u * vecNorm v)) :
    eLpNorm (fun ξ => hsSandwich Q (T ξ - θ • f)) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal ((‖matrixExpect ν T - θ • f‖ + c) * Q.trace.re) := by
  set R := matrixExpect ν T - θ • f
  set ev := hQ.1.eigenvalues
  have hev : ∀ i, 0 ≤ ev i := hQ.eigenvalues_nonneg
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  let cc : Fin W × Fin W → S → ℂ := fun ik ξ =>
    bilinear (fun a => eU hQ.1 a ik.1) (T ξ - matrixExpect ν T) (fun a => eU hQ.1 a ik.2)
  let w : Fin W × Fin W → ℝ := fun ik => ev ik.1 * ev ik.2
  have hw : ∀ ik, 0 ≤ w ik := fun ik => mul_nonneg (hev _) (hev _)
  have hcm : ∀ ik, Measurable (cc ik) := by
    intro ik
    have hb : Continuous (fun M : Matrix (Fin W) (Fin W) ℂ =>
        bilinear (fun a => eU hQ.1 a ik.1) M (fun a => eU hQ.1 a ik.2)) := by
      unfold bilinear
      exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact hb.measurable.comp (hT.sub measurable_const)
  have hpt : ∀ ξ, hsSandwich Q (T ξ - θ • f) ≤
      ‖R‖ * Q.trace.re + Real.sqrt (∑ ik, w ik * ‖cc ik ξ‖ ^ 2) := by
    intro ξ
    have : T ξ - θ • f = R + (T ξ - matrixExpect ν T) := by simp only [R]; abel
    rw [this]
    refine (hsSandwich_add_le hQ _ _).trans (add_le_add (hsSandwich_le hQ R) (le_of_eq ?_))
    rw [hsSandwich_eq_sqrt hQ.1]
    congr 1
    unfold sandwichSum
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [w, cc, rot_apply, ev]
  have hmeasL : AEStronglyMeasurable (fun ξ => hsSandwich Q (T ξ - θ • f)) ν :=
    (meas_hsSandwich measurable_const (hT.sub measurable_const)).aestronglyMeasurable
  have hB : ∀ ik, eLpNorm (cc ik) (ENNReal.ofReal r) ν ≤ ENNReal.ofReal c := by
    intro ik
    have h := hfl (fun a => eU hQ.1 a ik.1) (fun a => eU hQ.1 a ik.2)
    rwa [vecNorm_eU_col, vecNorm_eU_col, mul_one, mul_one] at h
  have hsq := eLpNorm_sqrt_wsum_le (ν := ν) w hw cc hcm hr (fun _ => c) (fun _ => hc) hB
  have hval : Real.sqrt (∑ ik, w ik * c ^ 2) = c * Q.trace.re := by
    rw [trace_re_eq_sum hQ.1]
    have : ∑ ik, w ik * c ^ 2 = (c * ∑ i, ev i) ^ 2 := by
      rw [mul_pow, sq (∑ i, ev i), Finset.sum_mul_sum, ← Finset.sum_mul, Fintype.sum_prod_type,
        mul_comm]
    rw [this, Real.sqrt_sq (mul_nonneg hc (Finset.sum_nonneg fun i _ => hev i))]
  rw [hval] at hsq
  calc eLpNorm (fun ξ => hsSandwich Q (T ξ - θ • f)) (ENNReal.ofReal p) ν
      ≤ eLpNorm (fun ξ => ‖R‖ * Q.trace.re + Real.sqrt (∑ ik, w ik * ‖cc ik ξ‖ ^ 2))
          (ENNReal.ofReal p) ν :=
        eLpNorm_mono_real hmeasL fun ξ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hsSandwich_nonneg _ _)]; exact hpt ξ
    _ ≤ eLpNorm (fun _ : S => ‖R‖ * Q.trace.re) (ENNReal.ofReal p) ν +
          eLpNorm (fun ξ => Real.sqrt (∑ ik, w ik * ‖cc ik ξ‖ ^ 2)) (ENNReal.ofReal p) ν :=
        eLpNorm_add_le (ε := ℝ) (f := fun _ : S => ‖R‖ * Q.trace.re)
          (g := fun ξ => Real.sqrt (∑ ik, w ik * ‖cc ik ξ‖ ^ 2)) hp1
    _ ≤ ENNReal.ofReal (‖R‖ * Q.trace.re) + ENNReal.ofReal (c * Q.trace.re) := by
        rw [eLpNorm_const_prob _ hp0, Real.enorm_eq_ofReal_abs,
          abs_of_nonneg (mul_nonneg (norm_nonneg _) (trace_re_nonneg hQ))]
        gcongr
        exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpr)).trans hsq
    _ = ENNReal.ofReal ((‖R‖ + c) * Q.trace.re) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (norm_nonneg _) (trace_re_nonneg hQ))
          (mul_nonneg hc (trace_re_nonneg hQ))]
        congr 1; ring

omit [IsProbabilityMeasure ν] in
/-- `‖g²‖_p ≤ C²` from `‖g‖_{2p} ≤ C` (the fresh norm bound, squared). -/
theorem condSq_le {g : S → ℝ} {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hg : eLpNorm g (ENNReal.ofReal (2 * p)) ν ≤ ENNReal.ofReal C) :
    eLpNorm (fun ξ => g ξ ^ 2) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (C ^ 2) := by
  have hm := aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hg)
  have h := eLpNorm_norm_rpow (p := ENNReal.ofReal p) (μ := ν) g hm (q := 2) two_pos
  have hfun : (fun ξ => ‖g ξ‖ ^ (2 : ℝ)) = fun ξ => g ξ ^ 2 := by
    funext ξ; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hfun, ← ENNReal.ofReal_mul hp.le, mul_comm p 2] at h
  rw [h]
  calc eLpNorm g (ENNReal.ofReal (2 * p)) ν ^ (2 : ℝ) ≤ (ENNReal.ofReal C) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hg zero_le_two
    _ = ENNReal.ofReal (C ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hC zero_le_two, Real.rpow_two]

end Cond

/-!
## The chain is almost surely Hermitian, the clock is positive
-/

section Chain

variable {W : ℕ}

/-- The fresh layer law is a probability measure (`Layers.meq_isProbabilityMeasure_layerLaw`). -/
instance freshLaw_isProbabilityMeasure (W : ℕ) (b : ℝ) : IsProbabilityMeasure (freshLaw W b) :=
  BlockBand.Layers.meq_isProbabilityMeasure_layerLaw W b _

instance oneEndedLaw_isProbabilityMeasure (W : ℕ) (b : ℝ) (j : ℕ) :
    IsProbabilityMeasure (oneEndedLaw W b j) := by
  unfold oneEndedLaw; infer_instance

theorem weight_nonneg : (0 : ℂ) ≤ (((W : ℝ) ^ 2)⁻¹ : ℂ) := by
  rw [show (((W : ℝ) ^ 2)⁻¹ : ℂ) = ((((W : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  exact Complex.zero_le_real.mpr (by positivity)

theorem X_isHermitian (E : ℝ) {D : Matrix (Fin W) (Fin W) ℂ} (hD : D.IsHermitian) (j : ℕ)
    (ω : Fin j → OneEndedLayer W) (hω : ∀ k a, ((ω k).1 a).IsHermitian) :
    (oneEndedX E D j ω).IsHermitian := by
  induction j with
  | zero => exact hD
  | succ j ih =>
    exact freshSchur_isHermitian E (ih (Fin.init ω) fun k a => hω _ a) _ (hω (Fin.last j))

theorem Y_posSemidef (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (D : Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) (ω : Fin j → OneEndedLayer W) : (oneEndedY b E q D j ω).PosSemidef := by
  induction j with
  | zero => exact PosSemidef.zero
  | succ j ih =>
    refine PosSemidef.add ?_ ((ih (Fin.init ω)).conjTranspose_mul_mul_same _)
    exact (freshC_posSemidef b E _ _).smul (Complex.zero_le_real.mpr (hq _))

theorem Q_posSemidef (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (D : Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) (ω : Fin j → OneEndedLayer W) : (oneEndedQ b E q D j ω).PosSemidef :=
  (Y_posSemidef b E hq D j ω).smul weight_nonneg

theorem ae_blocks_isHermitian (b : ℝ) (j : ℕ) :
    ∀ᵐ ω ∂oneEndedLaw W b j, ∀ k a, ((ω k).1 a).IsHermitian := by
  rw [ae_all_iff]
  intro k
  have h := BlockBand.Layers.lct_ae_blocks_isHermitian W b .oneBlockOnePort
  exact (measurePreserving_eval (fun _ : Fin j => freshLaw W b) k).quasiMeasurePreserving.ae h

/-- The clock recursion in `Q` form: `Q_{j+1} = L*Q_jL + (q((j+1)/W)/W²) C_{j+1}`. -/
theorem Q_succ (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (ω : Fin (j + 1) → OneEndedLayer W) :
    oneEndedQ b E q D (j + 1) ω =
      (freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)))ᴴ *
          oneEndedQ b E q D j (Fin.init ω) *
          freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) +
        (((q (((j + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ)) : ℂ) •
          freshC b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) := by
  have hY : oneEndedY b E q D (j + 1) ω =
      ((q (((j + 1 : ℕ) : ℝ) / W) : ℝ) : ℂ) •
          freshC b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) +
        (freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)))ᴴ *
          oneEndedY b E q D j (Fin.init ω) *
          freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) := rfl
  simp only [oneEndedQ]
  rw [hY, smul_add, smul_smul, add_comm]
  congr 1
  · rw [Matrix.mul_smul, Matrix.smul_mul]
  · congr 1; push_cast; ring

end Chain

end ClockMixingProb

end BlockBand.Endpoints.Clock
