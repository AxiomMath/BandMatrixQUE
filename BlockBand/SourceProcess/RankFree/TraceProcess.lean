module

public import BlockBand.SourceProcess.RankFree.ZeroBefore
public import BlockBand.SourceProcess.RankFree.CrossTerm

/-!
# The trace process of a born frame

`traceProc X` is the continuous process
`‖Y♯_t‖² + ∑_k (2 Re Tr(W_kᴴ(Y♯_t - Y♯_{t∧τ_k})) + 1{τ_k > 0} β_k)`, where `Y♯` is the frame without
positive-time births and `W_k = birthMat col_k (posW w)_k`. It equals `‖X_t‖² + ∑_k 1{t < τ_k} β_k`
(a birth adds `β_k` to `‖X‖²`), so it dominates `‖X_t‖²` and starts at `‖ξ‖² + ∑_k 1{τ_k>0} β_k`.

* `locMart_traceProc`: `traceProc X` is a `LocMart` with drift `0`: its drift is
  `2 Re Tr(X_sᴴ b_s) + ∑_a ‖σ_a(s)‖²` off the birth times, which vanishes on the constraint
  (`sdeGenerator_normSq_mul_eq_zero`). This is the trace martingale `Tr M` with births.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {nb : ℕ}

/-- The trace process `‖X_t‖² + ∑_k 1{t < τ_k} β_k`, written through `Y♯`. -/
def traceProc {Ω : Type*} (X : ℝ≥0 → Ω → Matrix ι c ℂ) (τ : Fin nb → Ω → ℝ≥0)
    (col : Fin nb → c) (w : Fin nb → Ω → ι → ℂ) (β : Fin nb → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t x => ‖sharpFrame X τ col w t x‖ ^ 2 + ∑ k, (2 * reInner (birthMat (col k) (posW τ w k x))
      (sharpFrame X τ col w t x - stoppedProcess (sharpFrame X τ col w)
        (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)) t x) + if 0 < τ k x then β k else 0)

omit [DecidableEq ι] in
theorem norm_birthMat_posW_le {Ω : Type*} {τ : Fin nb → Ω → ℝ≥0} {w : Fin nb → Ω → ι → ℂ}
    {β : Fin nb → ℝ} {k : Fin nb} {x : Ω} (hx : ∑ i, ‖w k x i‖ ^ 2 = β k) (j : c) :
    ‖birthMat j (posW τ w k x)‖ ≤ Real.sqrt (β k) := by
  have h0 : 0 ≤ β k := hx ▸ Finset.sum_nonneg fun i _ => sq_nonneg _
  refine Real.le_sqrt_of_sq_le ?_
  rw [norm_sq_birthMat, posW]
  split_ifs
  · exact hx.le
  · simpa using h0

/-- **The trace process with births is a `LocMart` with zero drift.** -/
theorem locMart_traceProc {D0 : ℝ} (hD0 : 0 < D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξ0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x))
    {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → c}
    {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ} {β : Fin nb → ℝ}
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)))
    (hw : ∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k))
    (hDcol : ∀ k j, D (col k) j = 0 ∧ D j (col k) = 0)
    (hξcol : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i, ξ x i (col k) = 0)
    (hwβ : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∑ i, ‖w k x i‖ ^ 2 = β k)
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsBornSDESolution μ D0 Naux P D ξ (frameBirthJump τ col w) X) :
    LocMart (driverLaw (κ := SourceNoise ι) μ) (driverAugmented (κ := SourceNoise ι) μ)
      (traceProc X τ col w β) (fun _ _ => 0) := by
  have hTP := twoProjection_born hD0 hP hD hξ hξ0 hDcol hξcol hX
  have hN := isNative_sharpFrame hτ hw hX
  have hA := hN.locMart_disc (contDiff_normSq (k := 2)) 0
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, zero_add] at hA
  have hB : ∀ k, LocMart (driverLaw (κ := SourceNoise ι) μ) (driverAugmented (κ := SourceNoise ι) μ)
      (fun t x => 2 * reInner (birthMat (col k) (posW τ w k x))
        (sharpFrame X τ col w t x - stoppedProcess (sharpFrame X τ col w)
          (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)) t x))
      (fun s x => 2 * if ((τ k x : ℝ≥0) : WithTop ℝ≥0) < (s : WithTop ℝ≥0) then
        reInner (birthMat (col k) (posW τ w k x)) (sourceDrift D0 Naux P (X s x)) else 0) :=
    fun k => (locMart_reInner_shift hN (hτ k)
      ((birthCLM (col k)).continuous.comp_stronglyMeasurable (stronglyMeasurable_posW τ w hτ hw k))
      ((hwβ k).mono fun x hx => norm_birthMat_posW_le hx (col k))).const_mul 2
  have hC : ∀ k, LocMart (driverLaw (κ := SourceNoise ι) μ) (driverAugmented (κ := SourceNoise ι) μ)
      (fun _ x => if 0 < τ k x then β k else 0) (fun _ _ => 0) := fun k => by
    refine LocMart.const (StronglyMeasurable.ite ?_ stronglyMeasurable_const stronglyMeasurable_const)
    have h := ((hτ k) 0).compl
    convert h using 1
    ext x
    show 0 < τ k x ↔ ¬ ((τ k x : WithTop ℝ≥0) ≤ ((0 : ℝ≥0) : WithTop ℝ≥0))
    rw [WithTop.coe_le_coe, not_le]
  have hsum := hA.add (LocMart.sum Finset.univ fun k _ => (hB k).add (hC k))
  refine hsum.congr_drift ?_
  filter_upwards [hTP] with x hx
  filter_upwards [ae_all_iff.2 fun k => ae_ne_toNNReal (τ k x)] with s hs
  set u := s.toNNReal
  have hind : ∀ k, (((τ k x : ℝ≥0) : WithTop ℝ≥0) < (u : WithTop ℝ≥0)) ↔ τ k x ≤ u := fun k =>
    WithTop.coe_lt_coe.trans ⟨le_of_lt, fun h => lt_of_le_of_ne h fun e => hs k e.symm⟩
  have key := sdeGenerator_normSq_mul_eq_zero hD0.le hP (hx u) (1 : Matrix c c ℂ)
  simp only [Matrix.mul_one] at key
  rw [sdeGenerator_normSq] at key
  rw [sdeGenerator_normSq]
  set b := sourceDrift D0 Naux P (X u x)
  have hre : reInner (X u x) b = reInner (sharpFrame X τ col w u x) b +
      ∑ k, if τ k x ≤ u then reInner (birthMat (col k) (posW τ w k x)) b else 0 := by
    conv_lhs => rw [X_eq_sharpFrame_add X τ col w u x]
    rw [map_add, _root_.add_apply, map_sum, _root_.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  simp only [hind, add_zero]
  rw [reInner_comm (X u x) b] at key
  rw [reInner_comm (sharpFrame X τ col w u x) b]
  have hs2 : ∑ k, 2 * (if τ k x ≤ u then reInner (birthMat (col k) (posW τ w k x)) b else 0) =
      2 * ∑ k, if τ k x ≤ u then reInner (birthMat (col k) (posW τ w k x)) b else 0 := by
    rw [Finset.mul_sum]
  rw [hs2]
  linarith

end BlockBand.SourceProcess.RankFree
