module

public import BlockBand.Palm.RelativeLocalizationDrift
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Relative localization, Step 2 (deterministic part): the linear mass equation

* `nonneg_of_supersolution` : barrier/maximum principle (every component of a
  supersolution with nonnegative initial value stays nonnegative);
* `forwardMass_nonneg`, `forwardMass_le_const`, `forwardMass_unique` : solutions with
  data in `[0, c]` stay in `[0, c]`; solutions are unique;
* `backward_forward_pairing` : for a backward propagator `P` on `[a,c]` and a forward
  solution `v` on `[s,c]`, `Σ_j P(s)_{kj} v(s)_j = v_k(c)` (this identifies the integrand of
  `reference_finite_speed` with a forward mass);
* `shortGen_isSubGenerator`, `referenceGenerator_isSubGenerator` and the domination
  `(R v)_k ≤ (S v)_k` for `v ≥ 0` (the killing is nonpositive);
* `le_exp_mul_of_deriv_le` : scalar Gronwall `f' ≤ K f ⇒ f(x) ≤ e^{K(x-s)} f(s)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Set Filter Topology Finset BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- Sub-generator on `(s,u)`: nonnegative off-diagonal entries, nonpositive row sums. -/
def IsSubGenerator (L : ℝ → Fin N → Fin N → ℝ) (s u : ℝ) : Prop :=
  ∀ x ∈ Ioo s u, (∀ k l, k ≠ l → 0 ≤ L x k l) ∧ ∀ k, ∑ l, L x k l ≤ 0

/-- At a minimizing negative component, a sub-generator applied to `w` is nonnegative. -/
theorem sum_mul_nonneg_of_isMin {L : Fin N → Fin N → ℝ} (hoff : ∀ k l, k ≠ l → 0 ≤ L k l)
    (hrow : ∀ k, ∑ l, L k l ≤ 0) {w : Fin N → ℝ} {i : Fin N} (hmin : ∀ j, w i ≤ w j)
    (hneg : w i ≤ 0) : 0 ≤ ∑ l, L i l * w l := by
  have : ∑ l, L i l * w l = ∑ l, L i l * (w l - w i) + (∑ l, L i l) * w i := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [this]
  refine add_nonneg (Finset.sum_nonneg fun l _ => ?_) (mul_nonneg_of_nonpos_of_nonpos (hrow i) hneg)
  by_cases hl : i = l
  · subst hl; simp
  · exact mul_nonneg (hoff i l hl) (sub_nonneg.mpr (hmin l))

/-- From `HasDerivAt f f' t`, `f' > 0`: there are points left of `t` (inside `(s,t)`) where
`f < f t`. -/
theorem exists_lt_left_of_deriv_pos {f : ℝ → ℝ} {f' s t : ℝ} (hst : s < t)
    (hf : HasDerivAt f f' t) (hpos : 0 < f') : ∃ x ∈ Ioo s t, f x < f t := by
  have h := (hasDerivWithinAt_iff_tendsto_slope.mp (hf.hasDerivWithinAt (s := Iio t)))
  have hset : Iio t \ {t} = Iio t := by
    ext x; simp only [Set.mem_sdiff, Set.mem_Iio, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact fun h e => (lt_irrefl t) (e ▸ h)
  rw [hset] at h
  have h1 : ∀ᶠ x in 𝓝[<] t, 0 < slope f t x := h.eventually (lt_mem_nhds hpos)
  have h2 : ∀ᶠ x in 𝓝[<] t, x ∈ Ioo s t := Ioo_mem_nhdsLT hst
  have h3 : ∀ᶠ x in 𝓝[<] t, x < t := self_mem_nhdsWithin
  obtain ⟨x, hx1, hx2, hx3⟩ := (h1.and (h2.and h3)).exists
  refine ⟨x, hx2, ?_⟩
  rw [slope_def_field] at hx1
  have : x - t < 0 := by linarith
  have := (div_pos_iff.mp hx1).resolve_left (fun h => absurd h.2 (not_lt.mpr this.le))
  linarith [this.1]

/-- **Barrier lemma.** A supersolution `w' ≥ L w` of the mass equation of a sub-generator
with `w(s) ≥ 0` stays nonnegative on `[s,u]`. No regularity of `L` in time is used. -/
theorem nonneg_of_supersolution {L : ℝ → Fin N → Fin N → ℝ} {s u : ℝ}
    (hL : IsSubGenerator L s u) {w : ℝ → Fin N → ℝ} {w' : ℝ → Fin N → ℝ}
    (hcont : ContinuousOn w (Icc s u)) (hder : ∀ x ∈ Ioo s u, HasDerivAt w (w' x) x)
    (hsup : ∀ x ∈ Ioo s u, ∀ k, ∑ l, L x k l * w x l ≤ w' x k) (h0 : ∀ k, 0 ≤ w s k) :
    ∀ x ∈ Icc s u, ∀ k, 0 ≤ w x k := by
  -- perturbed claim
  have key : ∀ ε > 0, ∀ x ∈ Icc s u, ∀ k, 0 ≤ w x k + ε * (1 + (x - s)) := by
    intro ε hε
    set p : ℝ → Fin N → ℝ := fun x k => w x k + ε * (1 + (x - s)) with hp
    have hpcont : ∀ k, ContinuousOn (fun x => p x k) (Icc s u) := by
      intro k
      have := (continuousOn_pi.mp hcont) k
      exact this.add (continuousOn_const.mul (continuousOn_const.add
        (continuousOn_id.sub continuousOn_const)))
    by_contra hcon
    push Not at hcon
    obtain ⟨x₁, hx₁, k₁, hk₁⟩ := hcon
    set T : Set ℝ := {x ∈ Icc s x₁ | ∃ k, p x k ≤ 0} with hT
    have hTne : T.Nonempty := ⟨x₁, ⟨⟨hx₁.1, le_rfl⟩, k₁, hk₁.le⟩⟩
    have hTsub : T ⊆ Icc s u := fun x hx => ⟨hx.1.1, hx.1.2.trans hx₁.2⟩
    have hTclosed : IsClosed T := by
      have : T = ⋃ k, (Icc s x₁ ∩ (fun x => p x k) ⁻¹' Iic 0) := by
        ext x; simp only [hT, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_Iic]
        constructor
        · rintro ⟨h1, k, h2⟩; exact ⟨k, h1, h2⟩
        · rintro ⟨k, h1, h2⟩; exact ⟨h1, k, h2⟩
      rw [this]
      refine isClosed_iUnion_of_finite fun k => ?_
      exact ((hpcont k).mono (Icc_subset_Icc le_rfl hx₁.2)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_Iic
    have hTbdd : BddBelow T := ⟨s, fun x hx => hx.1.1⟩
    set t := sInf T with ht
    have htT : t ∈ T := hTclosed.csInf_mem hTne hTbdd
    have hts : s < t := by
      rcases htT.1.1.lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨k, hk⟩ := htT.2
        rw [← h] at hk
        have := h0 k
        simp only [hp, sub_self, add_zero, mul_one] at hk
        linarith
    -- before `t` all components are positive
    have hbefore : ∀ x ∈ Ico s t, ∀ k, 0 < p x k := by
      intro x hx k
      by_contra hneg
      push Not at hneg
      have hxT : x ∈ T := ⟨⟨hx.1, hx.2.le.trans htT.1.2⟩, k, hneg⟩
      exact absurd (csInf_le hTbdd hxT) (not_le.mpr hx.2)
    -- at `t` all components are `≥ 0`
    have hat : ∀ k, 0 ≤ p t k := by
      intro k
      have hc : ContinuousWithinAt (fun x => p x k) (Ico s t) t :=
        ((hpcont k) t (hTsub htT)).mono (fun x hx => ⟨hx.1, hx.2.le.trans (hTsub htT).2⟩)
      have := right_nhdsWithin_Ico_neBot hts
      exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun x hx => (hbefore x hx k).le)
    obtain ⟨i, hi⟩ := htT.2
    have hi0 : p t i = 0 := le_antisymm hi (hat i)
    have htx₁ : t < x₁ := by
      rcases htT.1.2.lt_or_eq with h | h
      · exact h
      · exfalso; have := hat k₁; rw [h] at this; linarith
    have htu : t ∈ Ioo s u := ⟨hts, htx₁.trans_le hx₁.2⟩
    -- derivative of `p · i` at `t` is `≥ ε`
    have hmin : ∀ j, w t i ≤ w t j := by
      intro j; have := hat j; simp only [hp] at this hi0; linarith
    have hneg : w t i ≤ 0 := by
      simp only [hp] at hi0
      have : 0 < ε * (1 + (t - s)) := mul_pos hε (by linarith)
      linarith
    have hLw := sum_mul_nonneg_of_isMin (hL t htu).1 (hL t htu).2 hmin hneg
    have hw'i : 0 ≤ w' t i := hLw.trans (hsup t htu i)
    have hdi : HasDerivAt (fun x => p x i) (w' t i + ε * 1) t := by
      have := (hasDerivAt_pi.mp (hder t htu)) i
      exact this.add ((((hasDerivAt_id' t).sub_const s).const_add 1).const_mul ε)
    obtain ⟨x, hx, hxlt⟩ := exists_lt_left_of_deriv_pos hts hdi (by linarith)
    have := hbefore x ⟨hx.1.le, hx.2⟩ i
    rw [hi0] at hxlt
    linarith
  intro x hx k
  by_contra hneg
  push Not at hneg
  have hpos : 0 < 1 + (x - s) := by linarith [hx.1]
  set ε := -w x k / (2 * (1 + (x - s)))
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have := key ε hε x hx k
  have : ε * (1 + (x - s)) = -w x k / 2 := by
    simp only [ε]; field_simp
  linarith

/-- Solutions of the forward mass equation with nonnegative data are nonnegative. -/
theorem forwardMass_nonneg {L : ℝ → Fin N → Fin N → ℝ} {s u : ℝ} (hL : IsSubGenerator L s u)
    {v₀ : Fin N → ℝ} {v : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L s u v₀ v)
    (h0 : ∀ k, 0 ≤ v₀ k) : ∀ x ∈ Icc s u, ∀ k, 0 ≤ v x k := by
  obtain ⟨hs, hc, hd⟩ := hv
  exact nonneg_of_supersolution hL hc hd (fun x _ k => le_rfl) (by rw [hs]; exact h0)

/-- Solutions with data `≤ c` (`c ≥ 0`) stay `≤ c`. -/
theorem forwardMass_le_const {L : ℝ → Fin N → Fin N → ℝ} {s u : ℝ} (hL : IsSubGenerator L s u)
    {v₀ : Fin N → ℝ} {v : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L s u v₀ v) {c : ℝ}
    (hc0 : 0 ≤ c) (h0 : ∀ k, v₀ k ≤ c) : ∀ x ∈ Icc s u, ∀ k, v x k ≤ c := by
  obtain ⟨hs, hcont, hd⟩ := hv
  have := nonneg_of_supersolution (w := fun x k => c - v x k)
    (w' := fun x k => -∑ l, L x k l * v x l) hL
    (continuousOn_const.sub hcont)
    (fun x hx => (hasDerivAt_const x (fun _ => c)).sub (hd x hx) |>.congr_deriv
      (by funext k; simp))
    (fun x hx k => by
      have hrow := (hL x hx).2 k
      have : ∑ l, L x k l * (c - v x l) = c * ∑ l, L x k l - ∑ l, L x k l * v x l := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [this]
      nlinarith)
    (fun k => by simp only [hs]; linarith [h0 k])
  intro x hx k
  have := this x hx k
  linarith

/-- Uniqueness of solutions of the forward mass equation. -/
theorem forwardMass_unique {L : ℝ → Fin N → Fin N → ℝ} {s u : ℝ} (hL : IsSubGenerator L s u)
    {v₀ : Fin N → ℝ} {v w : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L s u v₀ v)
    (hw : ForwardMassSolution L s u v₀ w) : ∀ x ∈ Icc s u, v x = w x := by
  obtain ⟨hvs, hvc, hvd⟩ := hv
  obtain ⟨hws, hwc, hwd⟩ := hw
  have hsol : ∀ (a b : ℝ → Fin N → ℝ), a s = v₀ → ContinuousOn a (Icc s u) →
      (∀ x ∈ Ioo s u, HasDerivAt a (fun k => ∑ l, L x k l * a x l) x) →
      b s = v₀ → ContinuousOn b (Icc s u) →
      (∀ x ∈ Ioo s u, HasDerivAt b (fun k => ∑ l, L x k l * b x l) x) →
      ∀ x ∈ Icc s u, ∀ k, 0 ≤ a x k - b x k := by
    intro a b has hac had hbs hbc hbd
    refine nonneg_of_supersolution (w := fun x k => a x k - b x k)
      (w' := fun x k => ∑ l, L x k l * (a x l - b x l)) hL (hac.sub hbc)
      (fun x hx => ((had x hx).sub (hbd x hx)).congr_deriv ?_) (fun _ _ _ => le_rfl) ?_
    · funext k; simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    · intro k; simp [has, hbs]
  intro x hx
  funext k
  have h1 := hsol v w hvs hvc hvd hws hwc hwd x hx k
  have h2 := hsol w v hws hwc hwd hvs hvc hvd x hx k
  linarith

/-!
### Pairing of backward propagators with forward solutions
-/

/-- **Backward–forward pairing.** If `P` is a backward propagator of `L` on `[a,c]` and `v`
a forward solution of `L` on `[s,c]` with `a ≤ s ≤ c`, then `Σ_j P(s)_{kj} v_j(s) = v_k(c)`.
With `v(s) = 1_{J^c}` this is `Σ_{j∉J} E_aux|(𝓜_{s,c})_{kj}|² = v_k(c)`. -/
theorem backward_forward_pairing {L : ℝ → Fin N → Fin N → ℝ} {a c s : ℝ}
    {P : ℝ → Fin N → Fin N → ℝ} (hP : BackwardPropagator L a c P) (has : a ≤ s) (hsc : s ≤ c)
    {v₀ : Fin N → ℝ} {v : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L s c v₀ v) (k : Fin N) :
    ∑ j, P s k j * v₀ j = v c k := by
  obtain ⟨hPc, hPcont, hPd⟩ := hP
  obtain ⟨hvs, hvcont, hvd⟩ := hv
  rcases hsc.lt_or_eq with hlt | heq
  · set f : ℝ → ℝ := fun x => ∑ j, P x k j * v x j
    have hfc : ContinuousOn f (Icc s c) := by
      refine continuousOn_finsetSum _ fun j _ => ?_
      have h1 : ContinuousOn (fun x => P x k j) (Icc s c) :=
        (continuousOn_pi.mp (continuousOn_pi.mp (hPcont.mono (Icc_subset_Icc has le_rfl)) k)) j
      have h2 : ContinuousOn (fun x => v x j) (Icc s c) := continuousOn_pi.mp hvcont j
      exact h1.mul h2
    have hfd : ∀ x ∈ Ioo s c, HasDerivAt f 0 x := by
      intro x hx
      have hxa : x ∈ Ioo a c := ⟨has.trans_lt hx.1, hx.2⟩
      have hP1 := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hPd x hxa) k)
      have hv1 := hasDerivAt_pi.mp (hvd x hx)
      have := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hP1 j).mul (hv1 j)
      refine this.congr_deriv ?_
      simp only [neg_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
      ring
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hlt hfc hfd
    have hfeq : f c = f s := by
      have hne : c - s ≠ 0 := sub_ne_zero.mpr hlt.ne'
      field_simp at hslope
      linarith
    simp only [f, hPc, hvs] at hfeq
    rw [← hfeq]
    simp [ite_mul, Finset.sum_ite_eq]
  · subst heq
    rw [hPc, ← hvs]
    simp [ite_mul, Finset.sum_ite_eq]

/-!
### The short and reference generators are sub-generators
-/

theorem shortGen_rowSum (lam : Fin N → ℝ) (ℓ : ℕ) (k : Fin N) :
    ∑ l, shortGen N lam ℓ k l = 0 := by
  have := shortGen_apply lam ℓ (fun _ => (1 : ℝ)) k
  simp only [mul_one, sub_self, mul_zero, ite_self, Finset.sum_const_zero] at this
  exact this

theorem shortGen_isSubGenerator (lam : ℝ → Fin N → ℝ) (ℓ : ℕ) (s u : ℝ) :
    IsSubGenerator (fun x => shortGen N (lam x) ℓ) s u := fun _ _ =>
  ⟨fun _ _ h => shortGen_offdiag_nonneg _ ℓ h, fun k => (shortGen_rowSum _ ℓ k).le⟩

theorem shortGenerator_isSubGenerator (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) (s u : ℝ) : IsSubGenerator (shortGenerator F a ω ℓ) s u :=
  shortGen_isSubGenerator (fun x => flowEigenvalue F a ω x) ℓ s u

theorem referenceGenerator_apply (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) (v : Fin N → ℝ) (k : Fin N) :
    ∑ l, referenceGenerator F a b₀ ω ℓ σ k l * v l =
      ∑ l, shortGenerator F a ω ℓ σ k l * v l -
        max (longCoupling F a ω ℓ σ k) (b₀ * N / ℓ) * v k := by
  simp only [referenceGenerator, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem killing_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) (k : Fin N) : 0 ≤ max (longCoupling F a ω ℓ σ k) (b₀ * N / ℓ) :=
  le_max_of_le_left (by rw [longCoupling_eq_longCoup]; exact longCoup_nonneg _ ℓ k)

/-- Domination by the short generator on nonnegative vectors (killing `≤ 0`). -/
theorem referenceGenerator_le_short (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ) {v : Fin N → ℝ} (hv : ∀ k, 0 ≤ v k) (k : Fin N) :
    ∑ l, referenceGenerator F a b₀ ω ℓ σ k l * v l ≤ ∑ l, shortGenerator F a ω ℓ σ k l * v l := by
  rw [referenceGenerator_apply]
  have := mul_nonneg (killing_nonneg F a b₀ ω ℓ σ k) (hv k)
  linarith

theorem referenceGenerator_isSubGenerator (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) (s u : ℝ) :
    IsSubGenerator (referenceGenerator F a b₀ ω ℓ) s u := by
  intro x _
  refine ⟨fun k l hkl => ?_, fun k => ?_⟩
  · simp only [referenceGenerator, hkl, ite_false, sub_zero]
    exact (shortGenerator_isSubGenerator F a ω ℓ s u x ‹_›).1 k l hkl
  · have := referenceGenerator_apply F a b₀ ω ℓ x (fun _ => 1) k
    simp only [mul_one] at this
    rw [this, shortGenerator_eq_shortGen, shortGen_rowSum]
    linarith [killing_nonneg F a b₀ ω ℓ x k]

/-!
### Scalar Gronwall
-/

/-- **Gronwall.** If `f` is continuous on `[s,u]` with `f' ≤ K f` on `(s,u)`, then
`f(x) ≤ e^{K(x-s)} f(s)` on `[s,u]`. -/
theorem le_exp_mul_of_deriv_le {f f' : ℝ → ℝ} {s u K : ℝ} (hc : ContinuousOn f (Icc s u))
    (hd : ∀ x ∈ Ioo s u, HasDerivAt f (f' x) x) (hle : ∀ x ∈ Ioo s u, f' x ≤ K * f x) :
    ∀ x ∈ Icc s u, f x ≤ Real.exp (K * (x - s)) * f s := by
  set g : ℝ → ℝ := fun x => Real.exp (-(K * (x - s))) * f x
  have hgc : ContinuousOn g (Icc s u) :=
    (Real.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ => -(K * (x - s)))).continuousOn.mul hc
  have hgd : ∀ x ∈ Ioo s u, HasDerivAt g
      (Real.exp (-(K * (x - s))) * (-K) * f x + Real.exp (-(K * (x - s))) * f' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => -(K * (x - s))) (-K) x := by
      have := (((hasDerivAt_id' x).sub_const s).const_mul K).neg
      exact this.congr_deriv (by ring)
    exact (h1.exp.mul (hd x hx))
  have hanti : AntitoneOn g (Icc s u) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s u) hgc ?_ ?_
    · rw [interior_Icc]; exact fun x hx => (hgd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hgd x hx).deriv]
      have := hle x hx
      have he := Real.exp_pos (-(K * (x - s)))
      nlinarith
  intro x hx
  have h := hanti ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1
  simp only [g, sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul] at h
  have he : Real.exp (K * (x - s)) * Real.exp (-(K * (x - s))) = 1 := by
    rw [← Real.exp_add]; simp
  calc f x = Real.exp (K * (x - s)) * (Real.exp (-(K * (x - s))) * f x) := by
        rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp (K * (x - s)) * f s := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

end BlockBand.Palm.RelativeLocalization
