module
public import BlockBand.Internal.Contracts.TransmissionFlow
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Backward propagators from forward fundamental solutions

`backward_of_forward`: if `Φ(x, ·)` solves the forward equation `∂_u Φ(x, u) = L(u) Φ(x, u)` on
`[x, c]` with `Φ(x, x) = 1`, and `Q` is a backward propagator of `L` on `[a, c]`, then
`x ↦ Φ(x, c)` is also a backward propagator (it equals `Q`). `massGenerator_symm`: the mass
generator is symmetric for symmetric rates.
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open Set Filter BlockBand.Internal.Contracts.TransmissionFlow
open scoped BigOperators Topology

variable {N : ℕ}

/-- **Backward propagator from forward fundamental solutions.** -/
theorem backward_of_forward {L : ℝ → Fin N → Fin N → ℝ} {a c : ℝ} (hac : a ≤ c)
    {Φ : ℝ → ℝ → Fin N → Fin N → ℝ}
    (hΦ0 : ∀ x ∈ Icc a c, Φ x x = fun k l => if k = l then 1 else 0)
    (hΦc : ∀ x ∈ Icc a c, ContinuousOn (Φ x) (Icc x c))
    (hΦd : ∀ x ∈ Icc a c, ∀ u ∈ Ioo x c,
      HasDerivAt (Φ x) (fun k j => ∑ l, L u k l * Φ x u l j) u)
    {Q : ℝ → Fin N → Fin N → ℝ} (hQ : BackwardPropagator L a c Q) :
    BackwardPropagator L a c (fun x => Φ x c) := by
  have key : ∀ x ∈ Icc a c, Φ x c = Q x := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h
      rw [hΦ0 x hx, hQ.1]
    funext k j
    set f : ℝ → ℝ := fun u => ∑ p, Q u k p * Φ x u p j with hfdef
    have hQx : ContinuousOn Q (Icc x c) := hQ.2.1.mono (Icc_subset_Icc hx.1 le_rfl)
    have hcont : ContinuousOn f (Icc x c) := by
      refine continuousOn_finsetSum _ fun p _ => ?_
      exact ((continuous_apply p).comp_continuousOn ((continuous_apply k).comp_continuousOn
        hQx)).mul ((continuous_apply j).comp_continuousOn ((continuous_apply p).comp_continuousOn
          (hΦc x hx)))
    have hd : ∀ u ∈ Ioo x c, HasDerivAt f 0 u := by
      intro u hu
      have hQu := hQ.2.2 u ⟨hx.1.trans_lt hu.1, hu.2⟩
      have hΦu := hΦd x hx u hu
      have h1 : ∀ p, HasDerivAt (fun u => Q u k p) (-∑ m, Q u k m * L u m p) u := fun p =>
        hasDerivAt_pi.1 (hasDerivAt_pi.1 hQu k) p
      have h2 : ∀ p, HasDerivAt (fun u => Φ x u p j) (∑ l, L u p l * Φ x u l j) u := fun p =>
        hasDerivAt_pi.1 (hasDerivAt_pi.1 hΦu p) j
      have h3 := HasDerivAt.fun_sum (u := Finset.univ) fun p _ => (h1 p).mul (h2 p)
      convert h3 using 1
      simp only [neg_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
      rw [Finset.sum_comm (f := fun p m => Q u k m * L u m p * Φ x u p j)]
      have : ∀ m p, Q u k m * L u m p * Φ x u p j = Q u k m * (L u m p * Φ x u p j) :=
        fun m p => by ring
      simp only [this]
      ring
    obtain ⟨ξ, -, hslope⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) h hcont hd
    have hfe : f c = f x := by
      have h0 := (div_eq_zero_iff.1 hslope.symm).resolve_right (sub_ne_zero.2 (ne_of_gt h))
      linarith
    have hfc : f c = Φ x c k j := by
      simp only [hfdef, hQ.1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true]
    have hfx : f x = Q x k j := by
      simp only [hfdef, hΦ0 x hx, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    rw [← hfc, hfe, hfx]
  refine ⟨hΦ0 c ⟨hac, le_rfl⟩, hQ.2.1.congr fun x hx => key x hx, fun x hx => ?_⟩
  have hev : (fun x => Φ x c) =ᶠ[𝓝 x] Q := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact key y (Ioo_subset_Icc_self hy)
  simp only [key x (Ioo_subset_Icc_self hx)]
  exact (hQ.2.2 x hx).congr_of_eventuallyEq hev

/-- The mass generator is symmetric for symmetric rates. -/
theorem massGenerator_symm {r : ℝ → Fin N → Fin N → ℝ} (κ : ℝ → Fin N → ℝ)
    (hs : ∀ x k l, r x k l = r x l k) (x : ℝ) (k l : Fin N) :
    massGenerator r κ x k l = massGenerator r κ x l k := by
  unfold massGenerator
  by_cases h : k = l
  · subst h
    rfl
  · simp only [h, Ne.symm h, ite_false, hs x k l]

end BlockBand.SourceProcess.Stochastic.RotationFlow
