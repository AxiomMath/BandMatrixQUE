module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Scheme.Errors
public import Mathlib.MeasureTheory.Order.Lattice
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Taylor scheme: measurability and bounds of the grid quantities

Under `SchemeHyp` (raw filtration `𝓖`, probability `Q`), each grid quantity is
`𝓖_u`-a.e.-strongly measurable for the appropriate grid time `u` (`dφ1, dφ2` at `t_k`;
`incN, incI, incJ` at `t_{k+1}`), and almost surely bounded. Consequently the Riemann sums
over a grid of `[s, t]` are `𝓖_t`-a.e.-strongly measurable, and so are their a.e. limits.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀} {K U : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {Cβ Cα : ℝ}
  {φ : (Fin d → ℝ) → ℝ} {s t : ℝ≥0}

/-- Finite sums keep `AEStronglyMeasurable[m]` (for a measure on a larger σ-algebra). -/
theorem aesm_finset_sum {m : MeasurableSpace Ω} {ι : Type*} (S : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ S, AEStronglyMeasurable[m] (f i) Q) :
    AEStronglyMeasurable[m] (fun ω => ∑ i ∈ S, f i ω) Q := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (aestronglyMeasurable_const (m := m) (μ := Q) (b := (0 : ℝ)))
  | insert a S ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))

theorem measurable_range_sup'_aux {Ω' : Type*} [MeasurableSpace Ω'] (g : ℕ → Ω' → ℝ)
    (hg : ∀ k, Measurable (g k)) (n : ℕ) :
    Measurable (fun ω => (Finset.range (n + 1)).sup' ⟨0, by simp⟩ fun k => g k ω) := by
  convert Finset.measurable_range_sup'' (f := g) (n := n) fun k _ => hg k

/-- Finite maxima of a.e.-strongly measurable real functions. -/
theorem aestronglyMeasurable_range_sup' {m : MeasurableSpace Ω} {f : ℕ → Ω → ℝ}
    (hf : ∀ k, AEStronglyMeasurable[m] (f k) Q) (n : ℕ) :
    AEStronglyMeasurable[m] (fun ω => (Finset.range (n + 1)).sup' ⟨0, by simp⟩
      fun k => f k ω) Q := by
  refine ⟨fun ω => (Finset.range (n + 1)).sup' ⟨0, by simp⟩ fun k => (hf k).mk (f k) ω, ?_, ?_⟩
  · exact (@measurable_range_sup'_aux Ω m (fun k ω => (hf k).mk (f k) ω)
      (fun k => (hf k).stronglyMeasurable_mk.measurable) n).stronglyMeasurable
  · filter_upwards [ae_all_iff.2 fun k => (hf k).ae_eq_mk] with ω hω
    exact Finset.sup'_congr _ rfl fun k _ => hω k

theorem SchemeHyp.aestronglyMeasurable_comp (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) {F : Type*}
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [TopologicalSpace.PseudoMetrizableSpace F] [Zero F] {f : (Fin d → ℝ) → F}
    (hf : ContinuousOn f K) (u : ℝ≥0) :
    AEStronglyMeasurable[𝓖 u] (fun ω => f (Z u ω)) Q :=
  aestronglyMeasurable_comp_of_continuousOn H.compact.isClosed hf (H.meas u)
    (H.mem.mono fun _ h => h u)

theorem continuousOn_dφ1 (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (i : Fin d) :
    ContinuousOn (fun z => fderiv ℝ φ z (ev i)) K :=
  ((hφ.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hKU).clm_apply continuousOn_const

theorem continuousOn_dφ2 (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (i j : Fin d) :
    ContinuousOn (fun z => fderiv ℝ (fderiv ℝ φ) z (ev i) (ev j)) K :=
  ((((hφ.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU
    le_rfl).mono hKU).clm_apply continuousOn_const).clm_apply continuousOn_const

theorem SchemeHyp.aesm_dφ1 (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (hU : IsOpen U) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ 2 φ U) (n : ℕ) (i : Fin d) (k : ℕ) :
    AEStronglyMeasurable[𝓖 (grid s t n k)] (dφ1 φ Z s t n i k) Q :=
  H.aestronglyMeasurable_comp (continuousOn_dφ1 hU hKU hφ i) _

theorem SchemeHyp.aesm_dφ2 (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (hU : IsOpen U) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ 2 φ U) (n : ℕ) (i j : Fin d) (k : ℕ) :
    AEStronglyMeasurable[𝓖 (grid s t n k)] (dφ2 φ Z s t n i j k) Q :=
  H.aestronglyMeasurable_comp (continuousOn_dφ2 hU hKU hφ i j) _

theorem SchemeHyp.aesm_Zi (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (u : ℝ≥0) (i : Fin d) :
    AEStronglyMeasurable[𝓖 u] (fun ω => Z u ω i) Q :=
  (continuous_apply i).comp_aestronglyMeasurable (H.meas u)

theorem SchemeHyp.aesm_incI (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (hst : s ≤ t) (n k : ℕ)
    (i : Fin d) : AEStronglyMeasurable[𝓖 (grid s t n (k + 1))] (incI β s t n i k) Q := by
  have hle := 𝓖.mono (grid_mono hst n (Nat.le_succ k))
  have h0 := 𝓖.mono (zero_le : (0 : ℝ≥0) ≤ grid s t n (k + 1))
  have hm : AEStronglyMeasurable[𝓖 (grid s t n (k + 1))] (fun ω =>
      (Z (grid s t n (k + 1)) ω i - Z 0 ω i - N i (grid s t n (k + 1)) ω) -
      (Z (grid s t n k) ω i - Z 0 ω i - N i (grid s t n k) ω)) Q :=
    (((H.aesm_Zi _ i).sub ((H.aesm_Zi 0 i).mono h0)).sub ((H.mart i).1 _).aestronglyMeasurable).sub
      ((((H.aesm_Zi _ i).sub ((H.aesm_Zi 0 i).mono (𝓖.mono zero_le))).sub
        ((H.mart i).1 _).aestronglyMeasurable).mono hle)
  refine hm.congr ?_
  filter_upwards [H.ae_good s t] with ω hω
  simp only [incI, hω.2.2.2.2.1]
  ring

theorem SchemeHyp.ae_abs_dφ1_le (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) {M₁ : ℝ}
    (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁) (n : ℕ) (i : Fin d) (k : ℕ) :
    ∀ᵐ ω ∂Q, ‖dφ1 φ Z s t n i k ω‖ ≤ M₁ := by
  filter_upwards [H.mem] with ω hω
  rw [Real.norm_eq_abs]; exact (abs_clm_ev_le _ i).trans (hM₁ _ (hω _))

theorem SchemeHyp.ae_abs_dφ2_le (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) {M₂ : ℝ}
    (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) (n : ℕ) (i j : Fin d) (k : ℕ) :
    ∀ᵐ ω ∂Q, ‖dφ2 φ Z s t n i j k ω‖ ≤ M₂ := by
  filter_upwards [H.mem] with ω hω
  rw [Real.norm_eq_abs]; exact (abs_bilin_ev_le _ i j).trans (hM₂ _ (hω _))

/-- Grid times of `[s, t]` lie below `t`. -/
theorem grid_le_last (hst : s ≤ t) (n : ℕ) {k : ℕ} (hk : k ≤ n + 1) : grid s t n k ≤ t := by
  have := grid_mono hst n hk; rwa [grid_last hst] at this

/-- Riemann sums over a grid of `[s, t]` are `𝓖_t`-a.e.-strongly measurable. -/
theorem SchemeHyp.aesm_riemannSum (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (hU : IsOpen U)
    (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (hst : s ≤ t) (n : ℕ) :
    AEStronglyMeasurable[𝓖 t] (riemannSum φ Z β α s t n) Q := by
  unfold riemannSum
  refine aesm_finset_sum _ fun k hk => ?_
  have hk' : k < n + 1 := Finset.mem_range.1 hk
  have l0 := 𝓖.mono (grid_le_last hst n hk'.le)
  have l1 := 𝓖.mono (grid_le_last hst n (Nat.succ_le_of_lt hk'))
  refine AEStronglyMeasurable.add
    (f := fun ω => ∑ i, dφ1 φ Z s t n i k ω * incI β s t n i k ω)
    (g := fun ω => (1 / 2 : ℝ) * ∑ i, ∑ j, dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω) ?_
    (AEStronglyMeasurable.const_mul ?_ _)
  · exact aesm_finset_sum _ fun i _ =>
      ((H.aesm_dφ1 hU hKU hφ n i k).mono l0).mul ((H.aesm_incI hst n k i).mono l1)
  · exact aesm_finset_sum _ fun i _ =>
      aesm_finset_sum _ fun j _ =>
        ((H.aesm_dφ2 hU hKU hφ n i j k).mono l0).mul ((H.aestronglyMeasurable_incJ hst n k i j).mono l1)

/-- The generator integrand is bounded on `K`. -/
theorem abs_schemeGen_le (hβ : ∀ t ω i, |β t ω i| ≤ Cβ) (hα : ∀ t ω i j, |α t ω i j| ≤ Cα)
    {M₁ M₂ : ℝ} (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁)
    (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) {u : ℝ≥0} {ω : Ω} (hZ : Z u ω ∈ K) :
    |schemeGen φ Z β α u ω| ≤ d * (Cβ * M₁) + (1 / 2) * (d * (d * (Cα * M₂))) := by
  unfold schemeGen
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |β u ω i * fderiv ℝ φ (Z u ω) (ev i)| ≤ ∑ _i : Fin d, Cβ * M₁ :=
          Finset.sum_le_sum fun i _ => by
            rw [abs_mul]; exact mul_le_mul (hβ u ω i) ((abs_clm_ev_le _ i).trans (hM₁ _ hZ))
              (abs_nonneg _) ((abs_nonneg _).trans (hβ u ω i))
      _ = d * (Cβ * M₁) := by simp
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (by norm_num)
    calc ∑ i, |∑ j, α u ω i j * fderiv ℝ (fderiv ℝ φ) (Z u ω) (ev i) (ev j)| ≤
          ∑ _i : Fin d, ∑ _j : Fin d, Cα * M₂ :=
          Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => by
              rw [abs_mul]; exact mul_le_mul (hα u ω i j)
                ((abs_bilin_ev_le _ i j).trans (hM₂ _ hZ)) (abs_nonneg _)
                ((abs_nonneg _).trans (hα u ω i j)))
      _ = d * (d * (Cα * M₂)) := by simp

end BlockBand.SourceProcess.Stochastic.Semimartingale
