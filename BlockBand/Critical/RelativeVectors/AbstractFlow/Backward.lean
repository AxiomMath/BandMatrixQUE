module

public import BlockBand.Critical.RelativeVectors.AbstractFlow.BackwardDeriv

/-!
# Regularity of the backward function of an abstract reference flow

`rfBackwardRegular_holds`: `RFBackwardRegularStatement N r` holds for all `N, r`.

**Proof.** By Fubini, `g_s(z) = ∫ f(K_s z + L_s G) d(P ⊗ matCircularLaw)` (`refBackward_eq_prod`).
For `s ∈ [a, c]` the matrix `K_s` is a.s. an `ℓ²`-contraction, so its entries have modulus
`≤ 1` and `‖lmulL K_s‖ ≤ N` (sup norm); an `IsArrayC2Bounded C` test has sup-norm bounds
`C (1 + N r + (N r)²)` on `f, Df, D²f`. The affine-average lemmas (`integral_affine_contDiff`)
and their operator form (`integral_affine_fderiv_clm`) give `C²` and
`Dg_s(z)[u] = E Df(x)[K_s u]`, `D²g_s(z)[u, v] = E D²f(x)[K_s u, K_s v]`; the Euclidean
bounds with constant `C` follow from the columnwise contraction
`arrayNormSq (K_s u) ≤ arrayNormSq u`. Joint continuity in `(s, z)` on `[a, c] × ℂ^{N×r}` is
dominated convergence (`continuousOn_of_dominated`) for the integrands `f(x)`,
`Df(x) ∘ K_s` and `affD2 f K_s x`, which are a.s. continuous on `[a, c] × ℂ^{N×r}` and
bounded by constants (the bound uses the a.s. contraction for all `s ∈ [a, c]` at once).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.AbstractFlow

open MeasureTheory Set Filter Matrix
open BlockBand.Palm.ReferenceFlow
open BlockBand.Internal.Contracts.CoareaPalm

attribute [local instance] matrix_secondCountable matrix_pseudoMetrizable

variable {N r : ℕ}

/-- Points `(K, L, G, z)` of the integrands. -/
abbrev BwQ (N r : ℕ) :=
  Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ × RefState N r × RefState N r

/-- The affine argument `K z + L G`. -/
def bwArg (q : BwQ N r) : RefState N r := lmulL q.1 q.2.2.2 + lmul q.2.1 q.2.2.1

/-- Value integrand `f(K z + L G)`. -/
def bwF0 (f : RefState N r → ℝ) (q : BwQ N r) : ℝ := f (bwArg q)

/-- First-derivative integrand `Df(K z + L G) ∘ K`. -/
def bwF1 (f : RefState N r → ℝ) (q : BwQ N r) : RefState N r →L[ℝ] ℝ :=
  (fderiv ℝ f (bwArg q)).comp (lmulL q.1)

/-- Second-derivative integrand `(u, v) ↦ D²f(K z + L G)[K u, K v]`. -/
def bwF2 (f : RefState N r → ℝ) (q : BwQ N r) : RefState N r →L[ℝ] RefState N r →L[ℝ] ℝ :=
  affD2 f (lmulL q.1) (bwArg q)

theorem continuous_bwArg : Continuous (bwArg (N := N) (r := r)) := by
  have h1 : Continuous fun q : BwQ N r => lmul q.1 q.2.2.2 :=
    continuous_lmul_joint.comp (by fun_prop : Continuous fun q : BwQ N r => (q.1, q.2.2.2))
  have h2 : Continuous fun q : BwQ N r => lmul q.2.1 q.2.2.1 :=
    continuous_lmul_joint.comp (by fun_prop : Continuous fun q : BwQ N r => (q.2.1, q.2.2.1))
  exact h1.add h2

theorem continuous_bwF0 {f : RefState N r → ℝ} (hf : Continuous f) : Continuous (bwF0 f) :=
  hf.comp continuous_bwArg

theorem continuous_bwF1 {f : RefState N r → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (bwF1 f) :=
  ((hf.continuous_fderiv (by norm_num)).comp continuous_bwArg).clm_comp
    (continuous_lmulL.comp continuous_fst)

theorem continuous_bwF2 {f : RefState N r → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (bwF2 f) := by
  have hf2c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hK : Continuous fun q : BwQ N r => (lmulL q.1 : RefState N r →L[ℝ] RefState N r) :=
    continuous_lmulL.comp continuous_fst
  have hpre : Continuous fun q : BwQ N r =>
      (ContinuousLinearMap.compL ℝ (RefState N r) (RefState N r) ℝ).flip (lmulL q.1) :=
    ((ContinuousLinearMap.compL ℝ (RefState N r) (RefState N r) ℝ).flip).continuous.comp hK
  exact hpre.clm_comp ((hf2c.comp continuous_bwArg).clm_comp hK)

section Main

variable {Ωd : Type} {K L : ℝ → Ωd → Matrix (Fin N) (Fin N) ℂ}

/-- The point `(K_s(y), L_s(y), G, z)` at `ω = (y, G)`. -/
def bwPt (K L : ℝ → Ωd → Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : RefState N r)
    (ω : Ωd × RefState N r) : BwQ N r :=
  (K s ω.1, L s ω.1, ω.2, z)

theorem measurable_bwPt [MeasurableSpace Ωd] {s : ℝ} (hK : Measurable (K s))
    (hL : Measurable (L s)) (z : RefState N r) : Measurable (bwPt K L s z) :=
  (hK.comp measurable_fst).prodMk ((hL.comp measurable_fst).prodMk
    (measurable_snd.prodMk measurable_const))

theorem continuousOn_bwPt {a c : ℝ} {y : Ωd} (hKc : ContinuousOn (fun s => K s y) (Icc a c))
    (hLc : ContinuousOn (fun s => L s y) (Icc a c)) (G : RefState N r) :
    ContinuousOn (fun p : ℝ × RefState N r => bwPt K L p.1 p.2 (y, G)) (Icc a c ×ˢ univ) := by
  have hm : MapsTo (fun p : ℝ × RefState N r => p.1) (Icc a c ×ˢ univ) (Icc a c) :=
    fun p hp => hp.1
  exact (hKc.comp continuousOn_fst hm).prodMk ((hLc.comp continuousOn_fst hm).prodMk
    (continuousOn_const.prodMk continuousOn_snd))

theorem bwF0_bwPt (f : RefState N r → ℝ) (s : ℝ) (z : RefState N r) (ω : Ωd × RefState N r) :
    bwF0 f (bwPt K L s z ω) = f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) := rfl

variable [MeasurableSpace Ωd] {P : Measure Ωd} [IsProbabilityMeasure P]

/-- **Fubini form of the backward function.** -/
theorem refBackward_eq_prod {s : ℝ} (hK : Measurable (K s)) (hL : Measurable (L s)) {C : ℝ}
    {f : RefState N r → ℝ} (hfc : Continuous f) (hfb : ∀ z, |f z| ≤ C) :
    RelativeDuhamel.RF.refBackward P K L f s = fun z =>
      ∫ ω, f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) ∂(P.prod (matCircularLaw N r)) := by
  funext z
  have hm : Measurable fun ω : Ωd × RefState N r =>
      f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) :=
    ((continuous_bwF0 hfc).measurable.comp (measurable_bwPt hK hL z) :)
  have hi : Integrable (fun ω : Ωd × RefState N r =>
      f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2)) (P.prod (matCircularLaw N r)) :=
    Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hfb _)
  rw [RelativeDuhamel.RF.refBackward, integral_prod _ hi]
  rfl

set_option maxHeartbeats 1000000 in

/-- **Regularity of the backward function for a fixed flow.** -/
theorem refBackward_regular {a c : ℝ} (hK : ∀ s, Measurable (K s))
    (hL : ∀ s, Measurable (L s))
    (hcont : ∀ᵐ y ∂P, ContinuousOn (fun s => K s y) (Icc a c) ∧
      ContinuousOn (fun s => L s y) (Icc a c))
    (hcontr : ∀ᵐ y ∂P, ∀ s ∈ Icc a c, ∀ v : Fin N → ℂ, l2Norm (K s y *ᵥ v) ≤ l2Norm v)
    {C : ℝ} {f : (Fin N → Fin r → ℂ) → ℝ} (hf : IsArrayC2Bounded C f) :
    (∀ s ∈ Icc a c, IsArrayC2Bounded C (RelativeDuhamel.RF.refBackward P K L f s)) ∧
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => RelativeDuhamel.RF.refBackward P K L f p.1 p.2)
        (Icc a c ×ˢ univ) ∧
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
          fderiv ℝ (RelativeDuhamel.RF.refBackward P K L f p.1) p.2) (Icc a c ×ˢ univ) ∧
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
          fderiv ℝ (fderiv ℝ (RelativeDuhamel.RF.refBackward P K L f p.1)) p.2) (Icc a c ×ˢ univ) := by
  set μ : Measure (Ωd × RefState N r) := P.prod (matCircularLaw N r) with hμ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf.bound 0)
  have t1 : 0 ≤ C * (N * r) := mul_nonneg hC (by positivity)
  have t2 : 0 ≤ C * (N * r) * (N * r) := mul_nonneg t1 (by positivity)
  set B : ℝ := C + C * (N * r) + C * (N * r) * (N * r) with hB
  have hB0 : 0 ≤ B := by linarith
  have h0 : ∀ z, |f z| ≤ B := fun z => (hf.bound z).trans (by linarith)
  have h1 : ∀ z, ‖fderiv ℝ f z‖ ≤ B := fun z =>
    (norm_fderiv_le_of_array hf z).trans (by linarith)
  have h2 : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B := fun z =>
    (norm_fderiv_fderiv_le_of_array hf z).trans (by linarith)
  have hcontrμ : ∀ᵐ ω ∂μ, ∀ s ∈ Icc a c, ∀ v : Fin N → ℂ,
      l2Norm (K s ω.1 *ᵥ v) ≤ l2Norm v :=
    Measure.quasiMeasurePreserving_fst.ae hcontr
  have hcontμ : ∀ᵐ ω ∂μ, ContinuousOn (fun s => K s ω.1) (Icc a c) ∧
      ContinuousOn (fun s => L s ω.1) (Icc a c) :=
    Measure.quasiMeasurePreserving_fst.ae hcont
  have hAMall : ∀ᵐ ω ∂μ, ∀ s ∈ Icc a c,
      ‖(lmulL (K s ω.1) : RefState N r →L[ℝ] RefState N r)‖ ≤ N := by
    filter_upwards [hcontrμ] with ω hω s hs
    exact norm_lmulL_le (norm_entry_le_one (hω s hs))
  have hA : ∀ s, AEStronglyMeasurable (fun ω : Ωd × RefState N r =>
      (lmulL (K s ω.1) : RefState N r →L[ℝ] RefState N r)) μ := fun s =>
    continuous_lmulL.comp_aestronglyMeasurable ((hK s).comp measurable_fst).aestronglyMeasurable
  have hb : ∀ s, AEStronglyMeasurable (fun ω : Ωd × RefState N r => lmul (L s ω.1) ω.2) μ :=
    fun s => continuous_lmul_joint.comp_aestronglyMeasurable
      (((hL s).comp measurable_fst).prodMk measurable_snd).aestronglyMeasurable
  have hAM : ∀ s ∈ Icc a c, ∀ᵐ ω ∂μ,
      ‖(lmulL (K s ω.1) : RefState N r →L[ℝ] RefState N r)‖ ≤ N := fun s hs => by
    filter_upwards [hAMall] with ω hω using hω s hs
  have heq : ∀ s, RelativeDuhamel.RF.refBackward P K L f s = fun z =>
      ∫ ω, f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) ∂μ := fun s =>
    refBackward_eq_prod (hK s) (hL s) hf.contDiff.continuous hf.bound
  have hpm : ∀ s z, AEStronglyMeasurable (bwPt K L s z) μ := fun s z =>
    (measurable_bwPt (hK s) (hL s) z).aestronglyMeasurable
  refine ⟨fun s hs => ?_, ?_, ?_, ?_⟩
  · -- (1) the Euclidean bounded-`C²` property with the same constant
    obtain ⟨hcd, hd1, hd2⟩ :=
      integral_affine_contDiff (hA s) (hb s) (hAM s hs) hf.contDiff h0 h1 h2
    have hKs : ∀ᵐ ω ∂μ, ∀ v : RefState N r, arrayNormSq (lmulL (K s ω.1) v) ≤ arrayNormSq v := by
      filter_upwards [hcontrμ] with ω hω v using arrayNormSq_lmul_le (hω s hs) v
    rw [heq s]
    refine ⟨hcd, fun z => ?_, fun z v => ?_, fun z v w => ?_⟩
    · have := norm_integral_le_of_norm_le_const (μ := μ) (C := C)
        (f := fun ω => f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2))
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hf.bound _)
      simpa [Real.norm_eq_abs] using this
    · rw [hd1 z v]
      have := norm_integral_le_of_norm_le_const (μ := μ) (C := C * Real.sqrt (arrayNormSq v))
        (f := fun ω => fderiv ℝ f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2)
          (lmulL (K s ω.1) v)) (by
          filter_upwards [hKs] with ω hω
          rw [Real.norm_eq_abs]
          exact (hf.deriv_bound _ _).trans
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hω v)) hC))
      simpa [Real.norm_eq_abs] using this
    · rw [hd2 z v w]
      have := norm_integral_le_of_norm_le_const (μ := μ)
        (C := C * Real.sqrt (arrayNormSq v) * Real.sqrt (arrayNormSq w))
        (f := fun ω => fderiv ℝ (fderiv ℝ f) (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2)
          (lmulL (K s ω.1) v) (lmulL (K s ω.1) w)) (by
          filter_upwards [hKs] with ω hω
          rw [Real.norm_eq_abs]
          refine (hf.hessian_bound _ _ _).trans ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hω v)) hC)
            (Real.sqrt_le_sqrt (hω w)) (Real.sqrt_nonneg _)
            (mul_nonneg hC (Real.sqrt_nonneg _)))
      simpa [Real.norm_eq_abs] using this
  · -- (2) joint continuity of `g`
    have he : (fun p : ℝ × RefState N r => RelativeDuhamel.RF.refBackward P K L f p.1 p.2) =
        fun p => ∫ ω, bwF0 f (bwPt K L p.1 p.2 ω) ∂μ :=
      funext fun p => congrFun (heq p.1) p.2
    rw [he]
    refine continuousOn_of_dominated (bound := fun _ => C) (fun p _ => ?_)
      (fun p _ => Eventually.of_forall fun ω => ?_) (integrable_const C) ?_
    · exact ((continuous_bwF0 hf.contDiff.continuous).comp_aestronglyMeasurable (hpm p.1 p.2) :)
    · simpa [Real.norm_eq_abs, bwF0] using hf.bound _
    · filter_upwards [hcontμ] with ω hω
      exact ((continuous_bwF0 hf.contDiff.continuous).comp_continuousOn
        (continuousOn_bwPt hω.1 hω.2 ω.2) :)
  · -- (3) joint continuity of `Dg`
    refine ContinuousOn.congr (f := fun p : ℝ × RefState N r =>
      ∫ ω, bwF1 f (bwPt K L p.1 p.2 ω) ∂μ) ?_ ?_
    · refine continuousOn_of_dominated (bound := fun _ => B * N) (fun p _ => ?_)
        (fun p hp => ?_) (integrable_const _) ?_
      · exact ((continuous_bwF1 hf.contDiff).comp_aestronglyMeasurable (hpm p.1 p.2) :)
      · filter_upwards [hAMall] with ω hω
        exact (norm_fderiv_comp_affine_le h1 _ _ _).trans
          (mul_le_mul_of_nonneg_left (hω p.1 hp.1) hB0)
      · filter_upwards [hcontμ] with ω hω
        exact ((continuous_bwF1 hf.contDiff).comp_continuousOn
          (continuousOn_bwPt hω.1 hω.2 ω.2) :)
    · intro p hp
      have hst := integral_affine_fderiv_clm (hA p.1) (hb p.1) (hAM p.1 hp.1) hf.contDiff h0 h1 h2
      show fderiv ℝ (RelativeDuhamel.RF.refBackward P K L f p.1) p.2 = _
      rw [heq p.1, hst.1 p.2]
      rfl
  · -- (4) joint continuity of `D²g`
    refine ContinuousOn.congr (f := fun p : ℝ × RefState N r =>
      ∫ ω, bwF2 f (bwPt K L p.1 p.2 ω) ∂μ) ?_ ?_
    · refine continuousOn_of_dominated (bound := fun _ => N * (B * N)) (fun p _ => ?_)
        (fun p hp => ?_) (integrable_const _) ?_
      · exact ((continuous_bwF2 hf.contDiff).comp_aestronglyMeasurable (hpm p.1 p.2) :)
      · filter_upwards [hAMall] with ω hω
        exact (norm_affD2_le h2 _ _).trans (mul_le_mul (hω p.1 hp.1)
          (mul_le_mul_of_nonneg_left (hω p.1 hp.1) hB0) (mul_nonneg hB0 (norm_nonneg _))
          (Nat.cast_nonneg N))
      · filter_upwards [hcontμ] with ω hω
        exact ((continuous_bwF2 hf.contDiff).comp_continuousOn
          (continuousOn_bwPt hω.1 hω.2 ω.2) :)
    · intro p hp
      have hst := integral_affine_fderiv_clm (hA p.1) (hb p.1) (hAM p.1 hp.1) hf.contDiff h0 h1 h2
      show fderiv ℝ (fderiv ℝ (RelativeDuhamel.RF.refBackward P K L f p.1)) p.2 = _
      rw [heq p.1, hst.2 p.2]
      rfl

end Main

/-- **Regularity of the backward function** (`RFBackwardRegularStatement`), for all `N, r`. -/
theorem rfBackwardRegular_holds : ∀ N r, RelativeDuhamel.RF.RFBackwardRegularStatement N r := by
  intro N r Ωd _ P _ K L a c _ hK hL hcont hcontr C f hf
  exact refBackward_regular hK hL hcont hcontr hf

end BlockBand.Critical.RelativeVectors.AbstractFlow
