module

public import BlockBand.Transmission.LawDuality.KillPath

/-!
# Integration by parts for a killing factor: the expectation identity

* (orthogonality) `E[K_s (Φ_t − Φ_s − ∫_s^t G)] = 0` for `0 ≤ s ≤ t ≤ r`; this is what the
  martingale property of `Φ − ∫G` gives when `K_s` is bounded and `𝓖_s`-measurable;
* a.s. paths: `Φ, K` continuous on `[0,r]`, `K(b) − K(a) = ∫_a^b K'`, and `Φ, G, K, K'`
  bounded by `C`;
* measurability of `Φ_t`, `K_t`, `∫_s^t G` in `ω`.
Then `E[Φ_r K_r − Φ_0 K_0] = E ∫_0^r (K_u G_u + Φ_u K'_u) du`. With `K = exp(−∫_0^· k)`,
`K' = −kK`, this is `E[Φ_r K_r] − E[Φ_0] = E ∫_0^r K_u (G_u − k_u Φ_u) du`, the dual-side
identity with killing of (step (a)). Proof: telescoping on the grid
`killGrid r n`, orthogonality cell by cell, then dominated convergence with the pathwise limit
`tendsto_riemannKill` and the bound `abs_riemannKill_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set intervalIntegral

variable {Ω : Type*}

/-- The orthogonal remainder of the telescoping: `Σ_j K_j (ΔΦ_j − ∫_{cell} G)`. -/
def killRemainder (Φ G K : ℝ → Ω → ℝ) (r : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), K (killGrid r n j) ω *
    (Φ (killGrid r n (j + 1)) ω - Φ (killGrid r n j) ω -
      ∫ u in killGrid r n j..killGrid r n (j + 1), G u ω)

theorem riemannKill_eq (Φ G K : ℝ → Ω → ℝ) (r : ℝ) (n : ℕ) (ω : Ω) :
    riemannKill (Φ · ω) (G · ω) (K · ω) r n =
      (Φ r ω * K r ω - Φ 0 ω * K 0 ω) - killRemainder Φ G K r n ω := by
  have h := mul_sub_mul_eq_sum (fun j => Φ (killGrid r n j) ω) (fun j => K (killGrid r n j) ω)
    (n + 1)
  simp only [killGrid_zero, killGrid_last] at h
  rw [h, riemannKill, killRemainder, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable [MeasurableSpace Ω]

/-- **Killed integration by parts.** -/
theorem integral_killed_eq {P : Measure Ω} [IsFiniteMeasure P] {Φ G K K' : ℝ → Ω → ℝ} {r C : ℝ} (hr : 0 ≤ r)
    (hΦm : ∀ t, AEStronglyMeasurable (Φ t) P) (hKm : ∀ t, AEStronglyMeasurable (K t) P)
    (hGm : ∀ s t, AEStronglyMeasurable (fun ω => ∫ u in s..t, G u ω) P)
    (hpath : ∀ᵐ ω ∂P, ContinuousOn (Φ · ω) (Icc 0 r) ∧ ContinuousOn (K · ω) (Icc 0 r) ∧
      IntervalIntegrable (G · ω) volume 0 r ∧ IntervalIntegrable (K' · ω) volume 0 r ∧
      (∀ a b, 0 ≤ a → a ≤ b → b ≤ r → K b ω - K a ω = ∫ u in a..b, K' u ω) ∧
      ∀ u, |Φ u ω| ≤ C ∧ |G u ω| ≤ C ∧ |K u ω| ≤ C ∧ |K' u ω| ≤ C)
    (hInc : ∀ s t, 0 ≤ s → s ≤ t → t ≤ r →
      ∫ ω, K s ω * (Φ t ω - Φ s ω - ∫ u in s..t, G u ω) ∂P = 0) :
    ∫ ω, (Φ r ω * K r ω - Φ 0 ω * K 0 ω) ∂P =
      ∫ ω, (∫ u in (0 : ℝ)..r, (K u ω * G u ω + Φ u ω * K' u ω)) ∂P := by
  have hbd : ∀ᵐ ω ∂P, ∀ u, |Φ u ω| ≤ C ∧ |G u ω| ≤ C ∧ |K u ω| ≤ C ∧ |K' u ω| ≤ C :=
    hpath.mono fun ω h => h.2.2.2.2.2
  have hib : ∀ {f : Ω → ℝ} (B : ℝ), AEStronglyMeasurable f P → (∀ᵐ ω ∂P, |f ω| ≤ B) →
      Integrable f P := fun B hm h =>
    Integrable.of_bound hm B (h.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hbdry : Integrable (fun ω => Φ r ω * K r ω - Φ 0 ω * K 0 ω) P := by
    refine hib (C * C + C * C) (((hΦm r).mul (hKm r)).sub ((hΦm 0).mul (hKm 0))) ?_
    filter_upwards [hbd] with ω h
    refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;>
      exact mul_le_mul (h _).1 (h _).2.2.1 (abs_nonneg _) ((abs_nonneg _).trans (h 0).1)
  have hcell : ∀ n j, j < n + 1 → Integrable (fun ω => K (killGrid r n j) ω *
      (Φ (killGrid r n (j + 1)) ω - Φ (killGrid r n j) ω -
        ∫ u in killGrid r n j..killGrid r n (j + 1), G u ω)) P ∧
      ∫ ω, K (killGrid r n j) ω * (Φ (killGrid r n (j + 1)) ω - Φ (killGrid r n j) ω -
        ∫ u in killGrid r n j..killGrid r n (j + 1), G u ω) ∂P = 0 := by
    intro n j hj
    refine ⟨hib (C * (C + C + C * |killGrid r n (j + 1) - killGrid r n j|))
      ((hKm _).mul (((hΦm _).sub (hΦm _)).sub (hGm _ _))) ?_, hInc _ _ (killGrid_mem hr hj.le).1
        (killGrid_le_succ hr n j) (killGrid_mem hr (Nat.succ_le_of_lt hj)).2⟩
    filter_upwards [hbd] with ω h
    have hG := norm_integral_le_of_norm_le_const (a := killGrid r n j) (b := killGrid r n (j + 1))
      (f := fun u => G u ω) (C := C) fun u _ => (h u).2.1
    rw [Real.norm_eq_abs] at hG
    rw [abs_mul]
    refine mul_le_mul (h _).2.2.1 ?_ (abs_nonneg _) ((abs_nonneg _).trans (h 0).1)
    refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
      (add_le_add (h _).1 (h _).1)) hG)
  have hrem : ∀ n, Integrable (killRemainder Φ G K r n) P ∧
      ∫ ω, killRemainder Φ G K r n ω ∂P = 0 := by
    intro n
    have hI : ∀ j ∈ Finset.range (n + 1), Integrable (fun ω => K (killGrid r n j) ω *
        (Φ (killGrid r n (j + 1)) ω - Φ (killGrid r n j) ω -
          ∫ u in killGrid r n j..killGrid r n (j + 1), G u ω)) P :=
      fun j hj => (hcell n j (Finset.mem_range.1 hj)).1
    refine ⟨?_, ?_⟩
    · have := integrable_finsetSum (Finset.range (n + 1)) hI
      convert this using 1
      funext ω; simp [killRemainder]
    · unfold killRemainder
      rw [integral_finsetSum _ hI]
      exact Finset.sum_eq_zero fun j hj => (hcell n j (Finset.mem_range.1 hj)).2
  set F : ℕ → Ω → ℝ := fun n ω => riemannKill (Φ · ω) (G · ω) (K · ω) r n with hF
  have hFeq : ∀ n, F n = fun ω => (Φ r ω * K r ω - Φ 0 ω * K 0 ω) - killRemainder Φ G K r n ω :=
    fun n => funext fun ω => riemannKill_eq Φ G K r n ω
  have hFint : ∀ n, ∫ ω, F n ω ∂P = ∫ ω, (Φ r ω * K r ω - Φ 0 ω * K 0 ω) ∂P := by
    intro n
    rw [hFeq, integral_sub hbdry (hrem n).1, (hrem n).2, sub_zero]
  have hlim := tendsto_integral_of_dominated_convergence (μ := P) (F := F)
    (f := fun ω => ∫ u in (0 : ℝ)..r, (K u ω * G u ω + Φ u ω * K' u ω))
    (fun _ => 4 * C ^ 2 * r)
    (fun n => by rw [hFeq]; exact (hbdry.sub (hrem n).1).aestronglyMeasurable)
    (integrable_const _)
    (fun n => hpath.mono fun ω h => by
      rw [Real.norm_eq_abs]
      exact abs_riemannKill_le hr (fun u => (h.2.2.2.2.2 u).1) (fun u => (h.2.2.2.2.2 u).2.1)
        (fun u => (h.2.2.2.2.2 u).2.2.1) (fun u => (h.2.2.2.2.2 u).2.2.2) h.2.2.2.2.1 n)
    (hpath.mono fun ω h => tendsto_riemannKill hr h.1 h.2.1 (fun u => (h.2.2.2.2.2 u).2.1)
      (fun u => (h.2.2.2.2.2 u).2.2.2) h.2.2.1 h.2.2.2.1 h.2.2.2.2.1)
  simp_rw [hFint] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end BlockBand.Transmission.LawDuality
