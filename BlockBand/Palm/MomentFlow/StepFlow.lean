module

public import BlockBand.Palm.MomentFlow.IndProps
public import BlockBand.Palm.MomentFlow.MultiAux

/-!
# Flow lemmas for the induction step: affine combinations, comparison, versions

* `IsMomentFlowSolution.affine`: `αF + βG + γ` solves the moment flow if `F, G` do.
* **`abs_sub_one_le_of_initial`** (comparison): with nonnegative off-diagonal rates, if
  `|g(a) - 1| ≤ K h(a)` on the sector, then `|g(u) - 1| ≤ K h(u)` for all `u ∈ [a, b]`
  (positivity of the flow applied to `Kh ∓ (g - 1)`).
* `card_sector_le_real`: `#sector N r ≤ N^r` (every configuration is the occupation of a label word).
* `momentMonomial_overlap_nonneg`, **`regVersion_nonneg`**: a regular version of the
  conditional moments is a.s. nonnegative on the whole sector and time interval.
* `zeroExt`, **`zeroExt_version`**: the zero extension off the sector of a regular version is
  again a version on the sector and is a.s. continuous in time for **every** configuration, as
  required by `removal_average_uniform`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory Filter BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- Affine combinations of solutions are solutions. -/
theorem IsMomentFlowSolution.affine {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {a b : ℝ}
    {F G : ℝ → Occ N → ℝ} (hF : IsMomentFlowSolution c r a b F)
    (hG : IsMomentFlowSolution c r a b G) (α β γ : ℝ) :
    IsMomentFlowSolution c r a b (fun u ξ => α * F u ξ + β * G u ξ + γ) := by
  intro ξ hξ
  refine ⟨((continuousOn_const.mul (hF ξ hξ).1).add (continuousOn_const.mul (hG ξ hξ).1)).add
    continuousOn_const, fun u hu => ?_⟩
  have h := ((((hF ξ hξ).2 u hu).const_mul α).add (((hG ξ hξ).2 u hu).const_mul β)).add_const γ
  convert h using 1
  show momentGenerator (c u) (fun ζ => α * F u ζ + β * G u ζ + γ) ξ = _
  have e : (fun ζ => α * F u ζ + β * G u ζ + γ) = α • F u + β • G u + fun _ => γ := by
    funext ζ; simp
  rw [e, momentGenerator_add, momentGenerator_add, momentGenerator_smul, momentGenerator_smul,
    momentGenerator_const, add_zero]

/-- **Comparison**: `|g(a) - 1| ≤ K h(a)` on the sector propagates to all `u ∈ [a, b]`. -/
theorem abs_sub_one_le_of_initial {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {a b : ℝ}
    (hc : ∀ u ∈ Ioo a b, ∀ i j, i ≠ j → 0 ≤ c u i j) {g h : ℝ → Occ N → ℝ}
    (hg : IsMomentFlowSolution c r a b g) (hh : IsMomentFlowSolution c r a b h) {K : ℝ}
    (h0 : ∀ ζ ∈ sector N r, |g a ζ - 1| ≤ K * h a ζ) :
    ∀ u ∈ Icc a b, ∀ ζ ∈ sector N r, |g u ζ - 1| ≤ K * h u ζ := by
  intro u hu ζ hζ
  have h1 := (IsMomentFlowSolution.affine hh hg K (-1) 1).ge_of_initial_ge hc (m := 0)
    (fun ξ hξ => by have := abs_le.1 (h0 ξ hξ); linarith) u hu ζ hζ
  have h2 := (IsMomentFlowSolution.affine hh hg K 1 (-1)).ge_of_initial_ge hc (m := 0)
    (fun ξ hξ => by have := abs_le.1 (h0 ξ hξ); linarith) u hu ζ hζ
  rw [abs_le]; constructor <;> linarith

/-- `#sector N r ≤ N^r`. -/
theorem card_sector_le_real (N r : ℕ) : ((sector N r).card : ℝ) ≤ (N : ℝ) ^ r := by
  classical
  have hsub : sector N r ⊆ (univ : Finset (Fin r → Fin N)).image occOf := by
    intro ξ hξ
    obtain ⟨x, hx⟩ := exists_occOf r ξ hξ
    exact Finset.mem_image.2 ⟨x, mem_univ x, hx⟩
  have h := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  exact_mod_cast h

theorem momentMonomial_overlap_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ)
    (σ : ℝ) (ξ : Occ N) (ω : FlowSample N) :
    0 ≤ momentMonomial (fun k => flowOverlap F a q σ k ω) ξ := by
  unfold momentMonomial flowOverlap
  exact Finset.prod_nonneg fun i _ => div_nonneg (pow_nonneg (by positivity) _) (by positivity)

/-- A regular version is a.s. nonnegative on the sector and on `[a, c]`. -/
theorem regVersion_nonneg {F : Matrix (Fin N) (Fin N) ℂ} {a c : ℝ} (hac : a ≤ c)
    {q : Fin N → ℂ} {r : ℕ} {Φ : ℝ → Occ N → FlowSample N → ℝ} (hΦ : RegVersion F a c q r Φ) :
    ∀ᵐ ω ∂flowLaw N a, ∀ u ∈ Icc a c, ∀ ξ ∈ sector N r, 0 ≤ Φ u ξ ω := by
  have h0 : ∀ ξ ∈ sector N r, ∀ᵐ ω ∂flowLaw N a, 0 ≤ Φ a ξ ω := by
    intro ξ hξ
    have hv := hΦ.1 a ⟨le_rfl, hac⟩ ξ hξ
    have hn : 0 ≤ᵐ[flowLaw N a] condMoment F a c q a ξ :=
      condExp_nonneg (Eventually.of_forall fun ω => momentMonomial_overlap_nonneg F a q a ξ ω)
    filter_upwards [hv, hn] with ω h1 h2
    rw [h1]; exact h2
  have h0' := (Filter.eventually_all_finset (sector N r)).2 h0
  filter_upwards [h0', hΦ.2] with ω h1 h2 u hu ξ hξ
  exact h2.ge_of_initial_ge (fun x _ i j _ => flowRate_nonneg F a ω x i j) (m := 0)
    (fun ζ hζ => h1 ζ hζ) u hu ξ hξ

/-- Zero extension off the `r`-sector. -/
def zeroExt (r : ℕ) (Φ : ℝ → Occ N → FlowSample N → ℝ) : ℝ → Occ N → FlowSample N → ℝ :=
  fun σ ζ ω => if ζ ∈ sector N r then Φ σ ζ ω else 0

theorem zeroExt_of_mem {r : ℕ} (Φ : ℝ → Occ N → FlowSample N → ℝ) {ζ : Occ N}
    (hζ : ζ ∈ sector N r) (σ : ℝ) (ω : FlowSample N) : zeroExt r Φ σ ζ ω = Φ σ ζ ω := by
  simp [zeroExt, hζ]

/-- **Zero extension of a regular version.** -/
theorem zeroExt_version {F : Matrix (Fin N) (Fin N) ℂ} {a c : ℝ} {q : Fin N → ℂ} {r : ℕ}
    {Φ : ℝ → Occ N → FlowSample N → ℝ} (hΦ : RegVersion F a c q r Φ) :
    (∀ σ ∈ Icc a c, ∀ ζ ∈ sector N r,
      zeroExt r Φ σ ζ =ᵐ[flowLaw N a] condMoment F a c q σ ζ) ∧
    ∀ᵐ ω ∂flowLaw N a, ∀ ζ : Occ N, ContinuousOn (fun σ => zeroExt r Φ σ ζ ω) (Icc a c) := by
  refine ⟨fun σ hσ ζ hζ => ?_, ?_⟩
  · have e : zeroExt r Φ σ ζ = Φ σ ζ := by funext ω; exact zeroExt_of_mem Φ hζ σ ω
    rw [e]; exact hΦ.1 σ hσ ζ hζ
  · filter_upwards [hΦ.2] with ω hω ζ
    by_cases hζ : ζ ∈ sector N r
    · simpa [zeroExt, hζ] using (hω ζ hζ).1
    · simpa [zeroExt, hζ] using continuousOn_const

end BlockBand.Palm.MomentFlow
