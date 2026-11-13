module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularE12

/-!
# Orthogonality of the angular martingale to all exponential functionals of `W`

For a finite set `J` of times `≥ r`, phases `θ : ℝ≥0 → ℝ^N` and
`Ψ = exp(i ∑_{j∈J} θ_j·(W_j - W_r))`, by induction on `J` (peeling the smallest time):
* `Hyp.F1`: `E[ζ Ψ] = γ E[ζ]` for bounded `𝓕_r`-measurable `ζ` (with `γ` independent of `ζ`);
* `Hyp.F2`: `E[ζ Ψ (Ms_u - Ms_{u∧r})] = 0`.
Consequently (`Hyp.orth_exp`) `E[1_A e^{i∑_j θ_j·W_j} (Ms_u - Ms_0)] = 0` for `A ∈ 𝓕_0`.
This is the conditional martingale property of the stopped angular process given
`𝓕_0 ∨ σ(W)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges

section Generic
variable {N : ℕ} {Ω : Type}

/-- `∑_{j∈J} θ_j·(W_j - W_r)`. -/
def psum (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (J : Finset ℝ≥0) (θ : ℝ≥0 → Fin N → ℝ) (r : ℝ≥0)
    (ω : Ω) : ℝ :=
  ∑ j ∈ J, (Wd (θ j) Y j ω - Wd (θ j) Y r ω)

theorem Wd_sum (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (J : Finset ℝ≥0) (θ : ℝ≥0 → Fin N → ℝ)
    (u : ℝ≥0) (ω : Ω) : ∑ j ∈ J, Wd (θ j) Y u ω = Wd (∑ j ∈ J, θ j) Y u ω := by
  simp only [Wd, Finset.sum_apply, Finset.sum_mul]; rw [Finset.sum_comm]

theorem psum_insert (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) {a : ℝ≥0} {J : Finset ℝ≥0} (ha : a ∉ J)
    (θ : ℝ≥0 → Fin N → ℝ) (r : ℝ≥0) (ω : Ω) :
    psum Y (insert a J) θ r ω = psum Y J θ a ω +
      (Wd (∑ j ∈ insert a J, θ j) Y a ω - Wd (∑ j ∈ insert a J, θ j) Y r ω) := by
  rw [← Wd_sum, ← Wd_sum, ← Finset.sum_sub_distrib]
  simp only [psum, Finset.sum_insert ha]
  have : ∀ j ∈ J, Wd (θ j) Y j ω - Wd (θ j) Y r ω =
      (Wd (θ j) Y j ω - Wd (θ j) Y a ω) + (Wd (θ j) Y a ω - Wd (θ j) Y r ω) := fun _ _ => by ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]; ring

end Generic

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ} {s : ℝ≥0}
  {f : (Fin N → ℝ) → ℝ} {n : ℕ}

theorem norm_cexp_mul_I (x : ℝ) : ‖cexp ((x : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x

theorem Hyp.adapted_Wd (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ) (u : ℝ≥0) :
    StronglyMeasurable[shiftFiltration 𝓖 s u] fun ω => Wd θ (Yst N q G F s) u ω :=
  Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    stronglyMeasurable_const.mul (H.adapted_phase q (Pi.single i 1) u)

theorem Hyp.sm_expInc (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ) {r a : ℝ≥0}
    (hra : r ≤ a) : StronglyMeasurable[shiftFiltration 𝓖 s a] fun ω =>
      cexp (((Wd θ (Yst N q G F s) a ω - Wd θ (Yst N q G F s) r ω : ℝ) : ℂ) * I) := by
  have h1 := H.adapted_Wd q θ a
  have h2 := (H.adapted_Wd q θ r).mono ((shiftFiltration 𝓖 s).mono hra)
  have : Continuous fun x : ℝ => cexp ((x : ℂ) * I) := by fun_prop
  exact this.comp_stronglyMeasurable (h1.sub h2)

theorem Hyp.sm_psum (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (J : Finset ℝ≥0)
    (θ : ℝ≥0 → Fin N → ℝ) (r : ℝ≥0) :
    StronglyMeasurable fun ω => cexp ((psum (Yst N q G F s) J θ r ω : ℂ) * I) := by
  have : Continuous fun x : ℝ => cexp ((x : ℂ) * I) := by fun_prop
  refine this.comp_stronglyMeasurable (Finset.stronglyMeasurable_fun_sum _ fun j _ => ?_)
  exact ((H.adapted_Wd q (θ j) j).mono ((shiftFiltration 𝓖 s).le j)).sub
    ((H.adapted_Wd q (θ j) r).mono ((shiftFiltration 𝓖 s).le r))

theorem integrable_bdd {g : Ω → ℂ} (hg : AEStronglyMeasurable g Q) {C : ℝ}
    (hC : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C) : Integrable g Q := Integrable.of_bound hg C hC

/-- Future exponential functionals of `W` factor out of `𝓕_r`. -/
theorem Hyp.F1 (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (J : Finset ℝ≥0) :
    ∀ r : ℝ≥0, (∀ j ∈ J, r ≤ j) → ∀ θ : ℝ≥0 → Fin N → ℝ, ∃ γ : ℂ, ∀ ζ : Ω → ℂ,
      StronglyMeasurable[shiftFiltration 𝓖 s r] ζ → ∀ C, (∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) →
        ∫ ω, ζ ω * cexp ((psum (Yst N q G F s) J θ r ω : ℂ) * I) ∂Q = γ * ∫ ω, ζ ω ∂Q := by
  induction J using Finset.induction_on_min with
  | empty => exact fun r _ θ => ⟨1, fun ζ _ _ _ => by simp [psum]⟩
  | insert a J hlt ih =>
    intro r hr θ
    have ha : a ∉ J := fun h => lt_irrefl a (hlt a h)
    obtain ⟨γ, hγ⟩ := ih a (fun j hj => (hlt j hj).le) θ
    have hra : r ≤ a := hr a (Finset.mem_insert_self a J)
    set Θ := ∑ j ∈ insert a J, θ j
    refine ⟨γ * ((Real.exp (-(cθ Θ * ((a : ℝ) - r))) : ℝ) : ℂ), fun ζ hζ C hC => ?_⟩
    have hζ' := (hζ.mono ((shiftFiltration 𝓖 s).mono hra)).mul (H.sm_expInc q Θ hra)
    have hC' : ∀ᵐ ω ∂Q, ‖ζ ω * cexp (((Wd Θ (Yst N q G F s) a ω -
        Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I)‖ ≤ C := hC.mono fun ω h => by
      rw [norm_mul, norm_cexp_mul_I, mul_one]; exact h
    have e : ∀ ω, ζ ω * cexp ((psum (Yst N q G F s) (insert a J) θ r ω : ℂ) * I) =
        (ζ ω * cexp (((Wd Θ (Yst N q G F s) a ω - Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I)) *
          cexp ((psum (Yst N q G F s) J θ a ω : ℂ) * I) := fun ω => by
      rw [psum_insert _ ha, Complex.ofReal_add, add_mul, Complex.exp_add]; ring
    simp_rw [e]
    rw [hγ (fun ω => ζ ω * cexp (((Wd Θ (Yst N q G F s) a ω -
        Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I)) hζ' C hC', H.E1 q Θ hra hζ hC]; ring

/-- The stopped angular martingale is orthogonal to future exponentials of `W`. -/
theorem Hyp.F2 (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (J : Finset ℝ≥0) :
    ∀ r : ℝ≥0, (∀ j ∈ J, r ≤ j) → ∀ θ : ℝ≥0 → Fin N → ℝ, ∀ ζ : Ω → ℂ,
      StronglyMeasurable[shiftFiltration 𝓖 s r] ζ → ∀ C, (∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) → ∀ u : ℝ≥0,
        ∫ ω, ζ ω * cexp ((psum (Yst N q G F s) J θ r ω : ℂ) * I) *
          ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) u ω -
            stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) (min u r) ω : ℝ) : ℂ) ∂Q = 0 := by
  set Ms := stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) with hMs
  obtain ⟨-, hMsad, hMsb⟩ := H.ms_props (f := f) q
  -- the two-time increment lemma
  have key : ∀ r a : ℝ≥0, r ≤ a → ∀ Θ : Fin N → ℝ, ∀ ζ : Ω → ℂ,
      StronglyMeasurable[shiftFiltration 𝓖 s r] ζ → ∀ C, (∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) → ∀ u : ℝ≥0,
      ∫ ω, ζ ω * cexp (((Wd Θ (Yst N q G F s) a ω - Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I) *
        ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ) ∂Q = 0 := by
    intro r a hra Θ ζ hζ C hC u
    rcases le_total u r with hur | hru
    · simp [min_eq_left hur, min_eq_left (hur.trans hra)]
    rcases le_total a u with hau | hua
    · rw [min_eq_right hau, min_eq_right hru]; exact H.E2 q Θ hra hζ hC
    · rw [min_eq_left hua, min_eq_right hru]
      have hζ' : StronglyMeasurable[shiftFiltration 𝓖 s u] fun ω => ζ ω *
          cexp (((Wd Θ (Yst N q G F s) u ω - Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I) *
            ((Ms u ω - Ms r ω : ℝ) : ℂ) := by
        refine ((hζ.mono ((shiftFiltration 𝓖 s).mono hru)).mul (H.sm_expInc q Θ hru)).mul ?_
        exact Complex.continuous_ofReal.comp_stronglyMeasurable
          ((hMsad u).sub ((hMsad r).mono ((shiftFiltration 𝓖 s).mono hru)))
      obtain ⟨CM, hCM⟩ := hMsb u
      have hC' : ∀ᵐ ω ∂Q, ‖ζ ω * cexp (((Wd Θ (Yst N q G F s) u ω -
          Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I) * ((Ms u ω - Ms r ω : ℝ) : ℂ)‖ ≤ C * (CM + CM) := by
        filter_upwards [hC, hCM] with ω h1 h2
        rw [norm_mul, norm_mul, norm_cexp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul h1 ((abs_sub _ _).trans (add_le_add (h2 u le_rfl) (h2 r hru)))
          (abs_nonneg _) ((norm_nonneg _).trans h1)
      have e : ∀ ω, ζ ω * cexp (((Wd Θ (Yst N q G F s) a ω - Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I)
          * ((Ms u ω - Ms r ω : ℝ) : ℂ) = (ζ ω * cexp (((Wd Θ (Yst N q G F s) u ω -
            Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I) * ((Ms u ω - Ms r ω : ℝ) : ℂ)) *
          cexp (((Wd Θ (Yst N q G F s) a ω - Wd Θ (Yst N q G F s) u ω : ℝ) : ℂ) * I) := fun ω => by
        rw [show ((Wd Θ (Yst N q G F s) a ω - Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I =
          ((Wd Θ (Yst N q G F s) u ω - Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I +
            ((Wd Θ (Yst N q G F s) a ω - Wd Θ (Yst N q G F s) u ω : ℝ) : ℂ) * I by push_cast; ring,
          Complex.exp_add]; ring
      simp_rw [e]
      rw [H.E1 q Θ hua hζ' hC', H.E2 q Θ hru hζ hC, zero_mul]
  induction J using Finset.induction_on_min with
  | empty =>
    intro r _ θ ζ hζ C hC u
    have := key r (max u r) (le_max_right _ _) 0 ζ hζ C hC u
    simpa [psum, Wd, min_eq_left (le_max_left u r)] using this
  | insert a J hlt ih =>
    intro r hr θ ζ hζ C hC u
    have ha : a ∉ J := fun h => lt_irrefl a (hlt a h)
    have hra : r ≤ a := hr a (Finset.mem_insert_self a J)
    set Θ := ∑ j ∈ insert a J, θ j
    set ζ' : Ω → ℂ := fun ω => ζ ω *
      cexp (((Wd Θ (Yst N q G F s) a ω - Wd Θ (Yst N q G F s) r ω : ℝ) : ℂ) * I)
    have hζ' : StronglyMeasurable[shiftFiltration 𝓖 s a] ζ' :=
      (hζ.mono ((shiftFiltration 𝓖 s).mono hra)).mul (H.sm_expInc q Θ hra)
    have hC' : ∀ᵐ ω ∂Q, ‖ζ' ω‖ ≤ C := hC.mono fun ω h => by
      simp only [ζ']; rw [norm_mul, norm_cexp_mul_I, mul_one]; exact h
    obtain ⟨CM, hCM⟩ := hMsb u
    have hD : StronglyMeasurable[shiftFiltration 𝓖 s a] fun ω =>
        ζ' ω * ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ) :=
      hζ'.mul (Complex.continuous_ofReal.comp_stronglyMeasurable
        (((hMsad _).mono ((shiftFiltration 𝓖 s).mono (min_le_right _ _))).sub
          ((hMsad _).mono ((shiftFiltration 𝓖 s).mono ((min_le_right _ _).trans hra)))))
    have hDb : ∀ᵐ ω ∂Q, ‖ζ' ω * ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ)‖ ≤ C * (CM + CM) := by
      filter_upwards [hC', hCM] with ω h1 h2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1 ((abs_sub _ _).trans (add_le_add (h2 _ (min_le_left _ _))
        (h2 _ (min_le_left _ _)))) (abs_nonneg _) ((norm_nonneg _).trans h1)
    obtain ⟨γ, hγ⟩ := H.F1 q J a (fun j hj => (hlt j hj).le) θ
    have hsm : ∀ v, AEStronglyMeasurable (fun ω => ((Ms v ω : ℝ) : ℂ)) Q := fun v =>
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        ((hMsad v).mono ((shiftFiltration 𝓖 s).le v))).aestronglyMeasurable
    have hPs := (H.sm_psum q J θ a).aestronglyMeasurable (μ := Q)
    have hz' := (hζ'.mono ((shiftFiltration 𝓖 s).le a)).aestronglyMeasurable (μ := Q)
    have i1 : Integrable (fun ω => ζ' ω * cexp ((psum (Yst N q G F s) J θ a ω : ℂ) * I) *
        ((Ms u ω - Ms (min u a) ω : ℝ) : ℂ)) Q := by
      refine integrable_bdd ((hz'.mul hPs).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((hMsad u).mono ((shiftFiltration 𝓖 s).le u)).aestronglyMeasurable.sub
          ((hMsad _).mono ((shiftFiltration 𝓖 s).le _)).aestronglyMeasurable))) (C := C * (CM + CM)) ?_
      filter_upwards [hC', hCM] with ω h1 h2
      rw [norm_mul, norm_mul, norm_cexp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1 ((abs_sub _ _).trans (add_le_add (h2 u le_rfl) (h2 _ (min_le_left _ _))))
        (abs_nonneg _) ((norm_nonneg _).trans h1)
    have i2 : Integrable (fun ω => ζ' ω * cexp ((psum (Yst N q G F s) J θ a ω : ℂ) * I) *
        ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ)) Q := by
      refine integrable_bdd ((hz'.mul hPs).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((hMsad _).mono ((shiftFiltration 𝓖 s).le _)).aestronglyMeasurable.sub
          ((hMsad _).mono ((shiftFiltration 𝓖 s).le _)).aestronglyMeasurable))) (C := C * (CM + CM)) ?_
      filter_upwards [hC', hCM] with ω h1 h2
      rw [norm_mul, norm_mul, norm_cexp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1 ((abs_sub _ _).trans (add_le_add (h2 _ (min_le_left _ _))
        (h2 _ (min_le_left _ _)))) (abs_nonneg _) ((norm_nonneg _).trans h1)
    have e : ∀ ω, ζ ω * cexp ((psum (Yst N q G F s) (insert a J) θ r ω : ℂ) * I) *
        ((Ms u ω - Ms (min u r) ω : ℝ) : ℂ) =
        ζ' ω * cexp ((psum (Yst N q G F s) J θ a ω : ℂ) * I) * ((Ms u ω - Ms (min u a) ω : ℝ) : ℂ) +
        ζ' ω * cexp ((psum (Yst N q G F s) J θ a ω : ℂ) * I) *
          ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ) := fun ω => by
      simp only [ζ']
      rw [psum_insert _ ha, Complex.ofReal_add, add_mul, Complex.exp_add]; push_cast; ring
    simp_rw [e]
    rw [integral_add i1 i2, ih a (fun j hj => (hlt j hj).le) θ ζ' hζ' C hC' u, zero_add]
    have e2 : ∀ ω, ζ' ω * cexp ((psum (Yst N q G F s) J θ a ω : ℂ) * I) *
        ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ) = (ζ' ω *
          ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ)) *
          cexp ((psum (Yst N q G F s) J θ a ω : ℂ) * I) := fun ω => by ring
    simp_rw [e2]
    rw [hγ _ hD _ hDb, key r a hra Θ ζ hζ C hC u, mul_zero]

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
