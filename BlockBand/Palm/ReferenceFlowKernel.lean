module

public import BlockBand.Palm.ReferenceFlowSpec
public import BlockBand.Palm.RelativeLocalizationBridgeFlow

/-!
# The reference kernel and its mass propagator

For deterministic coefficients `r, κ` on `[a,c]`, let `𝓝` be a rotation flow (`IsRotationFlow`)
started at `a` with the time-reflected coefficients `r(a+c-x)`, `κ(a+c-x)`. The reference kernel
is `K_s = (𝓝_{c-s})ᴴ` (`refKernel`). The only hypothesis is `LinearRotationFlowContract N`.

* `exists_reflectedFlow`: the reflected flow exists.
* `refKernel_terminal`: `K_c = I`.
* `measurable_refKernel`, `continuousOn_refKernel`: measurability and a.s. continuity in `s`.
* `refKernel_mass`: `E_aux |(K_s)_{kj}|²` is a backward propagator of `massGenerator r κ`
  (`massGenerator r κ` is symmetric for symmetric `r`).
* `backwardPropagator_unique`: uniqueness of the backward propagator.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Set Matrix BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow LinearRotationFlowContract
  massGenerator)
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic
open BlockBand.Palm.RelativeLocalization (le_exp_mul_of_deriv_le)
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {N : ℕ} {S : Type} [MeasurableSpace S]

/-- Time-reflected rates `r(a+c-x)`. -/
def reflectRate (a c : ℝ) (r : ℝ → Fin N → Fin N → ℝ) : ℝ → Fin N → Fin N → ℝ :=
  fun x => r (a + c - x)

/-- Time-reflected damping `κ(a+c-x)`. -/
def reflectDamp (a c : ℝ) (κ : ℝ → Fin N → ℝ) : ℝ → Fin N → ℝ :=
  fun x => κ (a + c - x)

/-- The reference kernel `K_s = (𝓝_{c-s})ᴴ`. -/
def refKernel (c : ℝ) (𝓝 : ℝ≥0 → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ) (y : DriverSample S (RotIdx N)) : Matrix (Fin N) (Fin N) ℂ :=
  (𝓝 (c - s).toNNReal y)ᴴ

theorem mapsTo_reflect {a c : ℝ} : MapsTo (fun x : ℝ => a + c - x) (Icc a c) (Icc a c) :=
  fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem continuousOn_reflect {X : Type*} [TopologicalSpace X] {a c : ℝ} {f : ℝ → X}
    (hf : ContinuousOn f (Icc a c)) : ContinuousOn (fun x => f (a + c - x)) (Icc a c) :=
  hf.comp (continuous_const.sub continuous_id).continuousOn mapsTo_reflect

/-- The reflected rotation flow exists. -/
theorem exists_reflectedFlow (hRF : LinearRotationFlowContract N) (μ : Measure S)
    [IsProbabilityMeasure μ] {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c : ℝ}
    (hac : a ≤ c) (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l) (hκ0 : ∀ x k, 0 ≤ κ x k) :
    ∃ 𝓝, IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝 :=
  (hRF S μ (reflectRate a c r) (reflectDamp a c κ) a c hac (continuousOn_reflect hr)
    (continuousOn_reflect hκ) (fun _ k l => hrs _ k l) (fun _ k l => hr0 _ k l)
    (fun _ k => hκ0 _ k)).1 a ⟨le_rfl, hac⟩

variable {μ : Measure S} [IsProbabilityMeasure μ] {r : ℝ → Fin N → Fin N → ℝ}
  {κ : ℝ → Fin N → ℝ} {a c : ℝ}
  {𝓝 : ℝ≥0 → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}

theorem refKernel_terminal (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝)
    (y : DriverSample S (RotIdx N)) : refKernel c 𝓝 c y = 1 := by
  simp [refKernel, h𝓝.2 y]

theorem measurable_flow_entry
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝) (t : ℝ≥0)
    (i j : Fin N) : Measurable fun y => 𝓝 t y i j := by
  have h := (h𝓝.1.adapted t).mono ((driverAugmented (κ := RotIdx N) μ).le t)
  have hc : @Continuous (Matrix (Fin N) (Fin N) ℂ) ℂ
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ (fun A => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  exact (hc.comp_stronglyMeasurable h).measurable

theorem measurable_refKernel
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝) (s : ℝ) :
    Measurable (refKernel c 𝓝 s) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have h := Complex.continuous_conj.measurable.comp (measurable_flow_entry h𝓝 (c - s).toNNReal j i)
  simpa [refKernel, Matrix.conjTranspose_apply, Function.comp_def] using h

theorem continuousOn_refKernel
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ContinuousOn (fun s => refKernel c 𝓝 s y) (Icc a c) := by
  filter_upwards [h𝓝.1.continuous] with y hy
  have hc : Continuous fun s : ℝ => 𝓝 (c - s).toNNReal y :=
    hy.comp (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
  exact (continuous_id.matrix_conjTranspose.comp hc).continuousOn

/-!
## The mass identity
-/

theorem massGenerator_symm (hrs : ∀ x k l, r x k l = r x l k) (x : ℝ) (k l : Fin N) :
    massGenerator r κ x k l = massGenerator r κ x l k := by
  by_cases h : k = l
  · subst h; rfl
  · simp [massGenerator, h, Ne.symm h, hrs x k l]

theorem massGenerator_reflect (x : ℝ) :
    massGenerator (reflectRate a c r) (reflectDamp a c κ) x =
      massGenerator r κ (a + c - x) :=
  rfl

/-- **Mass identity.** `P(s)_{kj} = E_aux |(K_s)_{kj}|²` is a backward propagator of
`massGenerator r κ` on `[a,c]`. -/
theorem refKernel_mass (hRF : LinearRotationFlowContract N) (hac : a ≤ c)
    (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l) (hκ0 : ∀ x k, 0 ≤ κ x k)
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝) :
    BackwardPropagator (massGenerator r κ) a c
      (fun s k j => ∫ y, ‖refKernel c 𝓝 s y k j‖ ^ 2 ∂driverLaw (κ := RotIdx N) μ) := by
  have H := hRF S μ (reflectRate a c r) (reflectDamp a c κ) a c hac (continuousOn_reflect hr)
    (continuousOn_reflect hκ) (fun _ k l => hrs _ k l) (fun _ k l => hr0 _ k l)
    (fun _ k => hκ0 _ k)
  -- forward column solutions `Q x j k = E_aux |𝓝_{x-a}(j,k)|²`
  set Q : ℝ → Fin N → Fin N → ℝ := fun x j k =>
    ∫ y, ‖𝓝 (x - a).toNNReal y j k‖ ^ 2 ∂driverLaw (κ := RotIdx N) μ with hQ
  have hcol : ∀ k : Fin N, BlockBand.Internal.Contracts.TransmissionFlow.ForwardMassSolution
      (massGenerator (reflectRate a c r) (reflectDamp a c κ)) a c
      (fun j => if j = k then 1 else 0) (fun x j => Q x j k) := by
    intro k
    have h := H.2.2.1 a ⟨le_rfl, hac⟩ 𝓝 h𝓝 (fun j => if j = k then 1 else 0)
    have he : (fun x j => Q x j k) = fun x j => ∫ y, ∑ i, ‖𝓝 (x - a).toNNReal y j i‖ ^ 2 *
        (if i = k then 1 else 0) ∂driverLaw (κ := RotIdx N) μ := by
      funext x j
      simp only [hQ]
      congr 1
      funext y
      simp
    rw [he]
    exact h
  -- `P s k j = Q (a + c - s) j k`
  have hP : (fun s k j => ∫ y, ‖refKernel c 𝓝 s y k j‖ ^ 2 ∂driverLaw (κ := RotIdx N) μ) =
      fun s k j => Q (a + c - s) j k := by
    funext s k j
    simp only [hQ, refKernel, Matrix.conjTranspose_apply, norm_star]
    congr 3
    ring_nf
  rw [hP]
  refine ⟨?_, ?_, ?_⟩
  · funext k j
    have h0 := congrFun (hcol k).1 j
    simp only [add_sub_cancel_right] at h0 ⊢
    rw [h0]
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [hkj, Ne.symm hkj]
  · refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun j => ?_
    have hc := continuousOn_pi.1 (hcol k).2.1 j
    exact hc.comp (continuous_const.sub continuous_id).continuousOn mapsTo_reflect
  · intro s hs
    have hx : a + c - s ∈ Ioo a c := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rw [hasDerivAt_pi]
    intro k
    rw [hasDerivAt_pi]
    intro j
    have hd := (hasDerivAt_pi.1 ((hcol k).2.2 (a + c - s) hx)) j
    have hrefl : HasDerivAt (fun x : ℝ => a + c - x) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (a + c)
    refine (hd.comp s hrefl).congr_deriv ?_
    rw [massGenerator_reflect, sub_sub_cancel, mul_neg_one, neg_inj]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [massGenerator_symm hrs]
    ring

/-!
## Uniqueness of the backward propagator
-/

theorem sum_mul_sum_le {N : ℕ} (d : Fin N → ℝ) (L : Fin N → Fin N → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ m l, |L m l| ≤ M) :
    ∑ l, d l * ∑ m, d m * L m l ≤ M * N * ∑ l, d l ^ 2 := by
  have h1 : ∀ l m, d l * (d m * L m l) ≤ M * ((d l ^ 2 + d m ^ 2) / 2) := by
    intro l m
    have hb : d l * (d m * L m l) ≤ |d l| * |d m| * M := by
      calc d l * (d m * L m l) ≤ |d l * (d m * L m l)| := le_abs_self _
        _ = |d l| * |d m| * |L m l| := by rw [abs_mul, abs_mul]; ring
        _ ≤ |d l| * |d m| * M := mul_le_mul_of_nonneg_left (hM m l) (by positivity)
    have hq : |d l| * |d m| ≤ (d l ^ 2 + d m ^ 2) / 2 := by
      nlinarith [sq_nonneg (|d l| - |d m|), sq_abs (d l), sq_abs (d m)]
    nlinarith [mul_le_mul_of_nonneg_right hq hM0]
  calc ∑ l, d l * ∑ m, d m * L m l = ∑ l, ∑ m, d l * (d m * L m l) := by
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ l, ∑ m, M * ((d l ^ 2 + d m ^ 2) / 2) :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ => h1 l m
    _ = M * N * ∑ l, d l ^ 2 := by
        have e1 : ∀ l, ∑ m, M * ((d l ^ 2 + d m ^ 2) / 2) =
            N * (M / 2 * d l ^ 2) + M / 2 * ∑ m, d m ^ 2 := by
          intro l
          rw [show (fun m => M * ((d l ^ 2 + d m ^ 2) / 2)) =
              fun m => M / 2 * d l ^ 2 + M / 2 * d m ^ 2 from funext fun m => by ring,
            Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
        rw [Finset.sum_congr rfl fun l _ => e1 l, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-- **Uniqueness** of `BackwardPropagator` for a generator continuous on `[a,c]`. -/
theorem backwardPropagator_unique {L : ℝ → Fin N → Fin N → ℝ} (hL : ContinuousOn L (Icc a c))
    {P Q : ℝ → Fin N → Fin N → ℝ} (hP : BackwardPropagator L a c P)
    (hQ : BackwardPropagator L a c Q) : ∀ x ∈ Icc a c, P x = Q x := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := a) (b := c)).exists_bound_of_continuousOn hL
  set M := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ x ∈ Icc a c, ∀ m l, |L x m l| ≤ M := fun x hx m l =>
    ((norm_le_pi_norm (L x m) l).trans ((norm_le_pi_norm (L x) m).trans (hM₀ x hx))).trans
      (le_max_left _ _)
  set D : ℝ → Fin N → Fin N → ℝ := fun x k l => P x k l - Q x k l with hD
  set e : ℝ → ℝ := fun x => ∑ k, ∑ l, D x k l ^ 2 with he
  have hDc : ContinuousOn D (Icc a c) := hP.2.1.sub hQ.2.1
  have hec : ContinuousOn e (Icc a c) := by
    refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun l _ => ?_
    exact ((continuousOn_pi.1 (continuousOn_pi.1 hDc k) l)).pow 2
  have hDd : ∀ x ∈ Ioo a c, ∀ k l, HasDerivAt (fun x => D x k l)
      (-∑ m, D x k m * L x m l) x := by
    intro x hx k l
    have hp := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hP.2.2 x hx) k) l
    have hq := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hQ.2.2 x hx) k) l
    convert hp.sub hq using 1
    simp only [hD, sub_mul, Finset.sum_sub_distrib]
    ring
  have hed : ∀ x ∈ Ioo a c, HasDerivAt e
      (∑ k, ∑ l, 2 * D x k l * (-∑ m, D x k m * L x m l)) x := by
    intro x hx
    refine HasDerivAt.fun_sum fun k _ => HasDerivAt.fun_sum fun l _ => ?_
    convert (hDd x hx k l).pow 2 using 1
    simp
  -- reflected energy
  set e' : ℝ → ℝ := fun t => e (a + c - t)
  have he'c : ContinuousOn e' (Icc a c) :=
    hec.comp (continuous_const.sub continuous_id).continuousOn mapsTo_reflect
  have hrefl : ∀ t, HasDerivAt (fun x : ℝ => a + c - x) (-1) t := fun t => by
    simpa using (hasDerivAt_id t).const_sub (a + c)
  have he'd : ∀ t ∈ Ioo a c, HasDerivAt e'
      ((∑ k, ∑ l, 2 * D (a + c - t) k l * (-∑ m, D (a + c - t) k m * L (a + c - t) m l)) * (-1))
      t := fun t ht =>
    (hed (a + c - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).comp t (hrefl t)
  have hle : ∀ t ∈ Ioo a c,
      (∑ k, ∑ l, 2 * D (a + c - t) k l * (-∑ m, D (a + c - t) k m * L (a + c - t) m l)) * (-1)
        ≤ (2 * M * N) * e' t := by
    intro t ht
    have hx : a + c - t ∈ Icc a c := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hk : ∀ k, ∑ l, D (a + c - t) k l * ∑ m, D (a + c - t) k m * L (a + c - t) m l ≤
        M * N * ∑ l, D (a + c - t) k l ^ 2 :=
      fun k => sum_mul_sum_le _ _ hM0 (hM _ hx)
    have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hk k
    simp only [e', he]
    rw [← Finset.mul_sum] at hsum
    have : (∑ k, ∑ l, 2 * D (a + c - t) k l * (-∑ m, D (a + c - t) k m * L (a + c - t) m l)) *
        (-1) = 2 * ∑ k, ∑ l, D (a + c - t) k l * ∑ m, D (a + c - t) k m * L (a + c - t) m l := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this]
    nlinarith
  have hbound := le_exp_mul_of_deriv_le he'c he'd hle
  have he'a : e' a = 0 := by
    simp only [e', he, hD, add_sub_cancel_left, hP.1, hQ.1, sub_self]
    simp
  intro x hx
  have hx' : a + c - x ∈ Icc a c := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h0 := hbound (a + c - x) hx'
  rw [he'a, mul_zero] at h0
  have hex : e x = 0 := by
    have : e' (a + c - x) = e x := by simp [e']
    have hnn : 0 ≤ e x := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _
    linarith
  funext k l
  have hkl : D x k l ^ 2 = 0 := by
    have hnn := Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Finset.sum_nonneg fun l _ =>
      sq_nonneg (D x k l)) |>.1 hex k (Finset.mem_univ k)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg (D x k l))).1 hnn l
      (Finset.mem_univ l)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hkl
  simp only [hD] at this
  linarith

end BlockBand.Palm.ReferenceFlow
