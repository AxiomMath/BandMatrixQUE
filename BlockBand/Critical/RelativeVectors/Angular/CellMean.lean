module

public import BlockBand.Critical.RelativeVectors.Angular.Interval

/-!
# The grid sums have mean zero

From `ComplexAngularContract`: for every cell `k` of a grid with `K ≥ 1` cells, `Λ` times the cell
term is integrable with mean zero (`integrable_and_integral_cell`), hence so is `Λ · gridSum_K`
(`integrable_and_integral_gridSum`). The fixed-time clause is applied at the start time `s + p_k` to
the random test `cellTest`; its hypotheses (`C²`, phase invariance, ball bounds, measurability for
`𝓖_{s+p_k} ⊔ path(s + p_k)`) are checked here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.TransmissionAngular
open scoped NNReal

variable {N r : ℕ}

theorem abs_ite_le {P : Prop} [Decidable P] {x C : ℝ} (hx : |x| ≤ C) :
    |(if P then x else 0)| ≤ max C 0 := by
  split_ifs
  · exact hx.trans (le_max_left _ _)
  · simp

/-- **One grid cell.** `Λ` times the cell term is integrable with mean zero. -/
theorem integrable_and_integral_cell (hC : ComplexAngularContract)
    {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
    (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian)
    (s : ℝ≥0) (V : Matrix (Fin N) (Fin r) ℂ) {n : ℕ} (hn : 0 < n) {T : ℝ≥0}
    {h ht : Ω → ℝ → (Fin N → Fin r → ℂ) → ℝ}
    (hT : IsSpaceTimeAngularTest (BlockBand.Critical.RelativeVectors.eigenPathSigma F G s)
      (gapStop N (fun t ω => F ω + G t ω) s n) T h ht)
    {u : ℝ≥0} (huT : u ≤ T) {Λ : Ω → ℝ}
    (hΛ : Measurable[BlockBand.Critical.RelativeVectors.eigenPathSigma F G s] Λ)
    (hΛb : ∃ C, ∀ ω, |Λ ω| ≤ C) {K k : ℕ} (hK : K ≠ 0) (hk : k < K) :
    Integrable (fun ω => Λ ω * cellTerm (h ω) (genPath F G V s h ω) (arrPath F G V s ω)
        (stopTime (gapStop N (fun t ω => F ω + G t ω) s n) u ω) u K k) Q ∧
      ∫ ω, Λ ω * cellTerm (h ω) (genPath F G V s h ω) (arrPath F G V s ω)
        (stopTime (gapStop N (fun t ω => F ω + G t ω) s n) u ω) u K k ∂Q = 0 := by
  have hH : ∀ t ω, (F ω + G t ω).IsHermitian := fun t ω => (hFh ω).add (hG.hermitian t ω)
  set σ := gapStop N (fun t ω => F ω + G t ω) s n
  set sk := gridNN u K k
  set p := gridPt u K (k + 1)
  have hp : p ∈ Icc (0 : ℝ) T := ⟨gridPt_nonneg u.2 _, (gridPt_le u.2 hK (by omega)).trans
    (by exact_mod_cast huT)⟩
  
  have hcd : ∀ ω, ContDiff ℝ 2 (cellTest σ Λ h u K k ω) := fun ω =>
    contDiff_const_mul_comp_relabel (hT.contDiff ω p hp) _
  have hph : ∀ ω, IsPhaseInvariant (cellTest σ Λ h u K k ω) := fun ω =>
    isPhaseInvariant_const_mul_comp_relabel (hT.phase ω p) _
  have hle' : BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G s ≤
      (𝓖 (s + sk) ⊔
        BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G (s + sk)) :=
    contractPathSigma_le_shift 𝓖 hF hG.adapted s sk
  have hle : BlockBand.Critical.RelativeVectors.eigenPathSigma F G s ≤ (𝓖 (s + sk) ⊔
      BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G (s + sk)) :=
    (eigenPathSigma_le_contract F G hH s).trans hle'
  have hmeas : ∀ Z, Measurable[(𝓖 (s + sk) ⊔
      BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G (s + sk))]
      fun ω => cellTest σ Λ h u K k ω Z := by
    intro Z
    have hset : MeasurableSet[(𝓖 (s + sk) ⊔
      BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G (s + sk))]
        {ω | (sk : WithTop ℝ≥0) < σ ω} :=
      hle' _ (measurableSet_lt_gapStop F G hG.continuous s n sk)
    have hΛm : Measurable[(𝓖 (s + sk) ⊔
      BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G (s + sk))] Λ :=
      hΛ.mono hle le_rfl
    have hhm : Measurable[(𝓖 (s + sk) ⊔
      BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G (s + sk))]
        fun ω => h ω p (relabelArray Z) :=
      (hT.measurable p (relabelArray Z)).1.mono hle le_rfl
    exact (Measurable.ite hset hΛm measurable_const).mul hhm
  obtain ⟨CΛ, hCΛ⟩ := hΛb
  obtain ⟨Cb, hCb⟩ := hT.bound
  have hbd : ∀ R : ℝ, ∃ C : ℝ, ∀ ω Z, ‖Z‖ ≤ R →
      |cellTest σ Λ h u K k ω Z| ≤ C ∧ ‖fderiv ℝ (cellTest σ Λ h u K k ω) Z‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (cellTest σ Λ h u K k ω)) Z‖ ≤ C := by
    intro _
    refine ⟨max CΛ 0 * max Cb 0, fun ω Z _ => ?_⟩
    have hc := abs_ite_le (P := (sk : WithTop ℝ≥0) < σ ω) (hCΛ ω)
    have hb := hCb ω p hp (relabelArray Z)
    have hg := hT.contDiff ω p hp
    refine ⟨?_, ?_, ?_⟩
    · unfold cellTest
      rw [abs_mul]
      exact mul_le_mul hc (hb.1.trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    · refine (norm_fderiv_const_mul_comp_relabel_le hg _ Z).trans ?_
      exact mul_le_mul hc (hb.2.1.trans (le_max_left _ _))
        (norm_nonneg (fderiv ℝ (h ω p) (relabelArray Z))) (le_max_right _ _)
    · refine (norm_fderiv_fderiv_const_mul_comp_relabel_le hg _ Z).trans ?_
      exact mul_le_mul hc (hb.2.2.trans (le_max_left _ _))
        (norm_nonneg (fderiv ℝ (fderiv ℝ (h ω p)) (relabelArray Z))) (le_max_right _ _)
  have key := hC.angular N r Ω Q 𝓖 G F hG hF hFh (revSelection N)
    (isEigenSelection_revSelection N) (s + sk) (scaledFrame V) n hn (cellTest σ Λ h u K k) hcd
    hph hmeas hbd (((u : ℝ) / K).toNNReal)
  have hpt := contractVariable_eq (r := r) hH s V n (fun ω v hv => hT.contDiff ω v hv) huT Λ hK hk
  refine ⟨key.1.congr (ae_of_all _ fun ω => hpt ω), ?_⟩
  rw [← key.2]
  exact integral_congr_ae (ae_of_all _ fun ω => (hpt ω).symm)

/-- **The grid sums have mean zero.** -/
theorem integrable_and_integral_gridSum (hC : ComplexAngularContract)
    {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
    (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian)
    (s : ℝ≥0) (V : Matrix (Fin N) (Fin r) ℂ) {n : ℕ} (hn : 0 < n) {T : ℝ≥0}
    {h ht : Ω → ℝ → (Fin N → Fin r → ℂ) → ℝ}
    (hT : IsSpaceTimeAngularTest (BlockBand.Critical.RelativeVectors.eigenPathSigma F G s)
      (gapStop N (fun t ω => F ω + G t ω) s n) T h ht)
    {u : ℝ≥0} (huT : u ≤ T) {Λ : Ω → ℝ}
    (hΛ : Measurable[BlockBand.Critical.RelativeVectors.eigenPathSigma F G s] Λ)
    (hΛb : ∃ C, ∀ ω, |Λ ω| ≤ C) {K : ℕ} (hK : K ≠ 0) :
    Integrable (fun ω => Λ ω * gridSum (h ω) (genPath F G V s h ω) (arrPath F G V s ω)
        (stopTime (gapStop N (fun t ω => F ω + G t ω) s n) u ω) u K) Q ∧
      ∫ ω, Λ ω * gridSum (h ω) (genPath F G V s h ω) (arrPath F G V s ω)
        (stopTime (gapStop N (fun t ω => F ω + G t ω) s n) u ω) u K ∂Q = 0 := by
  have hcell := fun k (hk : k < K) =>
    integrable_and_integral_cell hC hG hF hFh s V hn hT huT hΛ hΛb hK hk
  simp_rw [gridSum_eq_sum_cellTerm, Finset.mul_sum]
  refine ⟨integrable_finsetSum _ fun k hk => (hcell k (Finset.mem_range.1 hk)).1, ?_⟩
  rw [integral_finsetSum _ fun k hk => (hcell k (Finset.mem_range.1 hk)).1]
  exact Finset.sum_eq_zero fun k hk => (hcell k (Finset.mem_range.1 hk)).2

end BlockBand.Critical.RelativeVectors.Angular
