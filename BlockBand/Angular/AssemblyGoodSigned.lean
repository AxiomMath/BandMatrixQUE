module

public import BlockBand.Angular.FiberAngular

/-!
# Signed transfer tools for the physical angular estimate

The transfer identity `FiberAngular.lintegral_extendedPairMeasure_eq_angular` is unsigned and
its observables are functions of the eigenline `ψψ*`; the angular comparison is signed and its
test is a function of a vector. This file provides the measure-theoretic tools connecting them.

* `liftP`: a function `g(x, u)` invariant under `u ↦ cu`, `c ≠ 0`, as a measurable function of
  the projector (`Σ_j P_jj g(x, P e_j)`): `liftP_eigenProjector` (unit `u`),
  `liftP_lineProjector` (`L ≠ 0`), `measurable_liftP`.
* `ofReal_abs_sub_le_nested`: if `a ≤ b + c` and `b ≤ a + c` almost everywhere on the outer
  variable (and everywhere on the inner one), with `a`, `b` measurable and of finite nested
  integral, then `|∫∫a - ∫∫b| ≤ ∫∫c` (no measurability of `c` is needed).
* `le_add_of_ofReal_abs_sub_le`: the pointwise form of the same inequality.
* `toReal_sub_eq_integral`: `∫ wh = (∫⁻ w h⁺) - (∫⁻ w h⁻)` for integrable `w ≥ 0` and bounded
  measurable `h`, with both lintegrals finite.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.AssemblyGood

open MeasureTheory BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.FiberAngular
open scoped ENNReal ComplexConjugate

/-!
## Lifting a line-invariant function to the projector
-/

section Lift

variable {X : Type*} {ι : Type} [Fintype ι]

/-- `g` is invariant under `u ↦ cu` for every `c ≠ 0`. -/
def IsLineInvariant (g : X → (ι → ℂ) → ℝ) : Prop :=
  ∀ (x : X) (u : ι → ℂ) (c : ℂ), c ≠ 0 → g x (c • u) = g x u

/-- `Σ_j Re P_jj · g(x, P e_j)`: for `P = uu*` the `j`-th column is `conj(u_j) u`. -/
def liftP (g : X → (ι → ℂ) → ℝ) (x : X) (P : ι → ι → ℂ) : ℝ :=
  ∑ j, (P j j).re * g x (fun k => P k j)

theorem sum_norm_sq_of_l2Norm {u : ι → ℂ} (hu : l2Norm u = 1) : (∑ k, ‖u k‖ ^ 2) = 1 := by
  have h0 : 0 ≤ ∑ k, ‖u k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  have h := hu
  unfold l2Norm at h
  nlinarith [Real.sq_sqrt h0]

theorem liftP_eigenProjector {g : X → (ι → ℂ) → ℝ} (hg : IsLineInvariant g) (x : X)
    {u : ι → ℂ} (hu : l2Norm u = 1) : liftP g x (eigenProjector u) = g x u := by
  unfold liftP eigenProjector
  have hterm : ∀ j, (u j * conj (u j)).re * g x (fun k => u k * conj (u j)) =
      ‖u j‖ ^ 2 * g x u := by
    intro j
    have hre : (u j * conj (u j)).re = ‖u j‖ ^ 2 := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hre]
    by_cases hj : u j = 0
    · simp [hj]
    · have hcol : (fun k => u k * conj (u j)) = conj (u j) • u := by
        funext k; rw [Pi.smul_apply, smul_eq_mul, mul_comm]
      rw [hcol, hg x u _ ((map_ne_zero _).2 hj)]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_mul, sum_norm_sq_of_l2Norm hu,
    one_mul]

theorem l2Norm_pos_of_ne_zero {L : ι → ℂ} (hL : L ≠ 0) : 0 < l2Norm L := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hL
  unfold l2Norm
  apply Real.sqrt_pos.2
  exact lt_of_lt_of_le (by positivity : 0 < ‖L k‖ ^ 2)
    (Finset.single_le_sum (f := fun j => ‖L j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ k))

theorem l2Norm_normalize {L : ι → ℂ} (hL : L ≠ 0) : l2Norm (FiberAngular.normalize L) = 1 := by
  unfold FiberAngular.normalize
  rw [l2Norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (l2Norm_pos_of_ne_zero hL), inv_mul_cancel₀ (l2Norm_pos_of_ne_zero hL).ne']

theorem lineProjector_eq_eigenProjector_normalize (L : ι → ℂ) :
    lineProjector L = eigenProjector (FiberAngular.normalize L) := by
  funext x y
  unfold lineProjector eigenProjector FiberAngular.normalize
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, Complex.conj_ofReal]
  ring

theorem lineProjector_eq_eigenProjector {u : ι → ℂ} (hu : l2Norm u = 1) :
    lineProjector u = eigenProjector u := by
  funext x y
  unfold lineProjector eigenProjector
  rw [hu]; simp

theorem liftP_lineProjector {g : X → (ι → ℂ) → ℝ} (hg : IsLineInvariant g) (x : X)
    {L : ι → ℂ} (hL : L ≠ 0) : liftP g x (lineProjector L) = g x L := by
  rw [lineProjector_eq_eigenProjector_normalize, liftP_eigenProjector hg x (l2Norm_normalize hL)]
  unfold FiberAngular.normalize
  exact hg x L _ (by
    have := (l2Norm_pos_of_ne_zero hL).ne'
    exact_mod_cast inv_ne_zero this)

theorem measurable_liftP [MeasurableSpace X] {g : X → (ι → ℂ) → ℝ}
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : X × (ι → ι → ℂ) => liftP g z.1 z.2) := by
  unfold liftP
  refine Finset.measurable_sum _ fun j _ => ?_
  have h1 : Measurable fun z : X × (ι → ι → ℂ) => (z.2 j j).re :=
    Complex.measurable_re.comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply j).comp measurable_snd))
  have h2 : Measurable fun z : X × (ι → ι → ℂ) => (fun k => z.2 k j) :=
    measurable_pi_iff.2 fun k => (measurable_pi_apply j).comp
      ((measurable_pi_apply k).comp measurable_snd)
  exact h1.mul (hg.comp (measurable_fst.prodMk h2))

end Lift

/-!
## Signed nested integrals
-/

section Nested

theorem le_add_of_ofReal_abs_sub_le {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞)
    (h : ENNReal.ofReal |a.toReal - b.toReal| ≤ c) : a ≤ b + c := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ ≤ ENNReal.ofReal (b.toReal + |a.toReal - b.toReal|) :=
        ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (a.toReal - b.toReal)])
    _ ≤ ENNReal.ofReal b.toReal + ENNReal.ofReal |a.toReal - b.toReal| := ENNReal.ofReal_add_le
    _ ≤ b + c := by rw [ENNReal.ofReal_toReal hb]; gcongr

theorem ofReal_abs_sub_le_of_le {A B C : ℝ≥0∞} (hA : A ≠ ∞) (hB : B ≠ ∞) (hAB : A ≤ B + C)
    (hBA : B ≤ A + C) : ENNReal.ofReal |A.toReal - B.toReal| ≤ C := by
  by_cases hC : C = ∞
  · rw [hC]; exact le_top
  have h1 : A.toReal ≤ B.toReal + C.toReal := by
    rw [← ENNReal.toReal_add hB hC]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hB, hC⟩) hAB
  have h2 : B.toReal ≤ A.toReal + C.toReal := by
    rw [← ENNReal.toReal_add hA hC]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hA, hC⟩) hBA
  rw [← ENNReal.ofReal_toReal hC]
  exact ENNReal.ofReal_le_ofReal (abs_le.2 ⟨by linarith, by linarith⟩)

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

theorem lintegral_nested_le_add [SFinite ν] {a b c : α → β → ℝ≥0∞}
    (hb : Measurable (Function.uncurry b)) (hab : ∀ᵐ x ∂μ, ∀ y, a x y ≤ b x y + c x y) :
    (∫⁻ x, ∫⁻ y, a x y ∂ν ∂μ) ≤ (∫⁻ x, ∫⁻ y, b x y ∂ν ∂μ) + ∫⁻ x, ∫⁻ y, c x y ∂ν ∂μ := by
  have hbx : ∀ x, Measurable (b x) := fun x => hb.comp (measurable_const.prodMk measurable_id)
  have hbo : Measurable fun x => ∫⁻ y, b x y ∂ν := hb.lintegral_prod_right'
  calc (∫⁻ x, ∫⁻ y, a x y ∂ν ∂μ) ≤ ∫⁻ x, ∫⁻ y, (b x y + c x y) ∂ν ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hab] with x hx
        exact lintegral_mono fun y => hx y
    _ = ∫⁻ x, ((∫⁻ y, b x y ∂ν) + ∫⁻ y, c x y ∂ν) ∂μ :=
        lintegral_congr fun x => lintegral_add_left (hbx x) _
    _ = _ := lintegral_add_left hbo _

/-- **Signed nested comparison**: `|∫∫a - ∫∫b| ≤ ∫∫c` from the two one-sided pointwise
inequalities (outer variable almost everywhere). -/
theorem ofReal_abs_sub_le_nested [SFinite ν] {a b c : α → β → ℝ≥0∞}
    (ha : Measurable (Function.uncurry a)) (hb : Measurable (Function.uncurry b))
    (hfa : (∫⁻ x, ∫⁻ y, a x y ∂ν ∂μ) ≠ ∞) (hfb : (∫⁻ x, ∫⁻ y, b x y ∂ν ∂μ) ≠ ∞)
    (hab : ∀ᵐ x ∂μ, ∀ y, a x y ≤ b x y + c x y) (hba : ∀ᵐ x ∂μ, ∀ y, b x y ≤ a x y + c x y) :
    ENNReal.ofReal |(∫⁻ x, ∫⁻ y, a x y ∂ν ∂μ).toReal - (∫⁻ x, ∫⁻ y, b x y ∂ν ∂μ).toReal| ≤
      ∫⁻ x, ∫⁻ y, c x y ∂ν ∂μ :=
  ofReal_abs_sub_le_of_le hfa hfb (lintegral_nested_le_add hb hab) (lintegral_nested_le_add ha hba)

end Nested

/-!
## Positive and negative parts against a density
-/

section Parts

variable {V : Type*} [MeasurableSpace V] {ν : Measure V}

/-- For an integrable density `w ≥ 0` and a bounded measurable `h`,
`∫ w h = (∫⁻ w h⁺) - (∫⁻ w h⁻)`, both lintegrals finite. -/
theorem toReal_sub_eq_integral {w h : V → ℝ} (hw0 : ∀ v, 0 ≤ w v) (hwi : Integrable w ν)
    (hh : Measurable h) {B : ℝ} (hB : ∀ v, |h v| ≤ B) :
    (∫⁻ v, ENNReal.ofReal (w v) * ENNReal.ofReal (h v) ∂ν) ≠ ∞ ∧
      (∫⁻ v, ENNReal.ofReal (w v) * ENNReal.ofReal (-h v) ∂ν) ≠ ∞ ∧
      (∫⁻ v, ENNReal.ofReal (w v) * ENNReal.ofReal (h v) ∂ν).toReal -
          (∫⁻ v, ENNReal.ofReal (w v) * ENNReal.ofReal (-h v) ∂ν).toReal =
        ∫ v, w v * h v ∂ν := by
  have hi : Integrable (fun v => w v * h v) ν := by
    have := hwi.bdd_mul (c := B) hh.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hB v)
    simpa [mul_comm] using this
  have e1 : ∀ v, ENNReal.ofReal (w v) * ENNReal.ofReal (h v) = ENNReal.ofReal (w v * h v) :=
    fun v => (ENNReal.ofReal_mul (hw0 v)).symm
  have e2 : ∀ v, ENNReal.ofReal (w v) * ENNReal.ofReal (-h v) =
      ENNReal.ofReal (-(w v * h v)) := fun v => by
    rw [← ENNReal.ofReal_mul (hw0 v), mul_neg]
  simp_rw [e1, e2]
  refine ⟨?_, ?_, (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi).symm⟩
  · exact hi.lintegral_lt_top.ne
  · exact hi.neg.lintegral_lt_top.ne

end Parts

end BlockBand.Angular.AssemblyGood
