module

public import BlockBand.SourceProcess.PhysApprox.B3FddDefs
public import BlockBand.SourceProcess.PhysApprox.B3FddMod
public import BlockBand.SourceProcess.PhysApprox.B3LimPass
public import BlockBand.SourceProcess.PhysApprox.IdentCap
public import BlockBand.SourceProcess.CapLaw.TightGram
public import BlockBand.SourceProcess.CapLaw.Cond
public import BlockBand.SourceProcess.FullSourceGenerator.LimitFdd

/-!
# The conditioned coordinates and their finite-`W` bounds

* `jumpAll`, `limJ`: the finite-`W` birth jumps at `limLenAll` and their limit (`gramJ`, `kJ`);
  **`eventually_jumpAll_eq`**: at a non-birth time they agree for `W` large.
* `fddCoord`: the births-removed observables `b3ObsAll − jumpAll` at model time `t` (entrance
  coordinates unchanged; `fddCoord_eq`); `fddProc`: enumerated by `Encodable` (the `WordLim`
  format); `measurable_fddCoord`.
* `condL`: the closed law conditioned on the Borel cap event `capM`; `condObsTestAll_eq`
  (`condObsTestAll` is a `condL` expectation), `condL_le` (bounds on the cap event).
* `ae_start_bound`: at model time `0` every coordinate is at most `4K + 1` (start state
  `initialGram`, `𝒦 = 0`, `t_k ∈ [0, 1]`).
* **`fdd_modulus`**: the conditioned modulus of every coordinate on `[0, T']`, every `T'`, from
  `Modul.modulusS` at the horizon `max (max T s) (s + T')` (the hypotheses hold at every horizon above
  `T`: `ComplexSourceLawDomain` only asks `τ_j < T`).
* **`fdd_tight`**: one-time tightness of every coordinate at every `t ≥ 0`, from the start bound
  and the modulus by `CapLaw.chain_bound`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Fdd

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Internal.Contracts.Layers
open scoped NNReal ENNReal

variable {W np K : ℕ}

/-!
## Jumps
-/

/-- The finite-`W` birth jumps of the observables at `limLenAll` (`0` for entrance coordinates). -/
def jumpAll (b E s : ℝ) (τ m : Fin np → ℝ) (W : ℕ) : LIdx K np → ℝ≥0 → ℂ
  | Sum.inl e => fun u => gramEntry e (b3JumpAt b s τ m W (limLenAll s W u))
  | Sum.inr (Sum.inl _) => fun _ => 0
  | Sum.inr (Sum.inr ij) => fun u => b3KJumpAt E s τ m W (limLenAll s W u) ij.1 ij.2

/-- The limit jumps (`gramJ`, `kJ`; `0` for entrance coordinates). -/
def limJ (b E s : ℝ) (τ m : Fin np → ℝ) : LIdx K np → ℝ≥0 → ℂ
  | Sum.inl e => fun u => gramEntry e (gramJ b s τ m u)
  | Sum.inr (Sum.inl _) => fun _ => 0
  | Sum.inr (Sum.inr ij) => fun u => kJ E s τ m u ij.1 ij.2

theorem b3JumpAt_eq_sum (b s : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) :
    b3JumpAt (K := K) b s τ m W n = ∑ i, if ⌊(W : ℝ) * τ i⌋₊ ∈ Finset.Ico (closeLen s W) n then
      (((dStar b * m i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1,
        ((dStar b * m i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1) else 0 := by
  unfold b3JumpAt b3BirthAt
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_ite_eq _ _ _

theorem b3KJumpAt_eq_sum (E s : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) :
    b3KJumpAt E s τ m W n = ∑ i, if ⌊(W : ℝ) * τ i⌋₊ ∈ Finset.Ico (closeLen s W) n then
      (matchedA E * (m i : ℂ)) • Matrix.single i i 1 else 0 := by
  unfold b3KJumpAt b3KBirthAt
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_ite_eq _ _ _

/-- At a non-birth time, eventually the births before `limLenAll` are those with `τ_i - s ≤ u`. -/
theorem eventually_born_iff {s : ℝ} (hs : 0 ≤ s) {τ : Fin np → ℝ} (hsτ : ∀ j, s < τ j)
    {u : ℝ≥0} (hu : ∀ j, s + (u : ℝ) ≠ τ j) :
    ∀ᶠ W : ℕ in atTop, ∀ i, (⌊(W : ℝ) * τ i⌋₊ ∈ Finset.Ico (closeLen s W) (limLenAll s W u) ↔
      τ i - s ≤ u) := by
  refine eventually_all.2 fun i => ?_
  have hlo : ∀ W : ℕ, closeLen s W ≤ ⌊(W : ℝ) * τ i⌋₊ := fun W =>
    Nat.floor_mono (mul_le_mul_of_nonneg_left (hsτ i).le (Nat.cast_nonneg W))
  rcases lt_or_gt_of_ne (hu i) with hgt | hlt
  · refine Eventually.of_forall fun W => ?_
    have h2 : limLenAll s W u ≤ ⌊(W : ℝ) * τ i⌋₊ :=
      Nat.floor_mono (mul_le_mul_of_nonneg_left hgt.le (Nat.cast_nonneg W))
    simp only [Finset.mem_Ico]
    exact ⟨fun h => by omega, fun h => by linarith⟩
  · have hτ0 : 0 ≤ τ i := hs.trans (hsτ i).le
    have hpos : 0 < s + u - τ i := by linarith
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / (s + u - τ i))
    filter_upwards [eventually_ge_atTop N] with W hW
    have hW' : (N : ℝ) ≤ W := by exact_mod_cast hW
    have h1 : 1 ≤ (W : ℝ) * (s + u - τ i) := by
      rw [div_le_iff₀ hpos] at hN; nlinarith
    have h2 : ⌊(W : ℝ) * τ i⌋₊ + 1 ≤ limLenAll s W u := by
      rw [← Nat.floor_add_one (mul_nonneg (Nat.cast_nonneg W) hτ0)]
      exact Nat.floor_mono (by nlinarith)
    simp only [Finset.mem_Ico]
    exact ⟨fun _ => by linarith, fun _ => ⟨hlo W, by omega⟩⟩

/-- **At a non-birth time the finite-`W` jumps are eventually the limit jumps.** -/
theorem eventually_jumpAll_eq {b E s : ℝ} (hs : 0 ≤ s) {τ m : Fin np → ℝ}
    (hsτ : ∀ j, s < τ j) {u : ℝ≥0} (hu : ∀ j, s + (u : ℝ) ≠ τ j) :
    ∀ᶠ W : ℕ in atTop, ∀ l : LIdx K np, jumpAll b E s τ m W l u = limJ b E s τ m l u := by
  filter_upwards [eventually_born_iff hs hsτ hu] with W hW l
  have hG : b3JumpAt (K := K) b s τ m W (limLenAll s W u) = gramJ b s τ m u := by
    rw [b3JumpAt_eq_sum, gramJ, birthJump]
    exact Finset.sum_congr rfl fun i _ => by simp only [hW i]
  have hK : b3KJumpAt E s τ m W (limLenAll s W u) = kJ E s τ m u := by
    rw [b3KJumpAt_eq_sum, kJ, kBirthJump]
    exact Finset.sum_congr rfl fun i _ => by simp only [hW i]
  rcases l with e | k | ij
  · simp only [jumpAll, limJ, hG]
  · rfl
  · simp only [jumpAll, limJ, hK]

/-!
## The coordinates
-/

/-- **The births-removed coordinates** at model time `t` (length `⌊W(s + t)⌋₊`). -/
def fddCoord (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    LIdx K np → ℝ → ProbedPath W np × ℝ → ℂ
  | Sum.inl e => fun t => Modul.zB b E s h τ m W Vs (Sum.inl e) ⌊(W : ℝ) * (s + t)⌋₊
  | Sum.inr (Sum.inl k) => fun _ y => (physTseq b E s W y.1.1 k : ℂ)
  | Sum.inr (Sum.inr ij) => fun t => Modul.zB b E s h τ m W Vs (Sum.inr ij) ⌊(W : ℝ) * (s + t)⌋₊

theorem fddCoord_cToL (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) (t : ℝ) :
    fddCoord b E s h τ m W Vs (cToL c) t = Modul.zB b E s h τ m W Vs c ⌊(W : ℝ) * (s + t)⌋₊ := by
  rcases c with e | ij <;> rfl

/-- The coordinates are the observables minus the jumps. -/
theorem fddCoord_eq (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (l : LIdx K np) (u : ℝ≥0)
    (y : ProbedPath W np × ℝ) :
    fddCoord b E s h τ m W Vs l u y =
      b3ObsAll b E s h τ m W Vs l u y - jumpAll b E s τ m W l u := by
  rcases l with e | k | ij
  · rfl
  · simp only [fddCoord, b3ObsAll, jumpAll, sub_zero]
  · rfl

/-- The coordinates enumerated by `ℕ` (`0` for codes of no label). -/
def fddProc (b E s h : ℝ) (τ m : Fin np → ℝ) (Wn : ℕ → ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (n a : ℕ) (t : ℝ)
    (y : ProbedPath (Wn n) np × ℝ) : ℂ :=
  match Encodable.decode (α := LIdx K np) a with
  | some l => fddCoord b E s h τ m (Wn n) (Vs (Wn n)) l t y
  | none => 0

theorem fddProc_some (b E s h : ℝ) (τ m : Fin np → ℝ) (Wn : ℕ → ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {n a : ℕ}
    {l : LIdx K np} (hd : Encodable.decode (α := LIdx K np) a = some l) (t : ℝ) :
    fddProc b E s h τ m Wn Vs n a t = fddCoord b E s h τ m (Wn n) (Vs (Wn n)) l t := by
  funext y; simp [fddProc, hd]

theorem fddProc_none (b E s h : ℝ) (τ m : Fin np → ℝ) (Wn : ℕ → ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {n a : ℕ}
    (hd : Encodable.decode (α := LIdx K np) a = none) (t : ℝ) :
    fddProc (K := K) b E s h τ m Wn Vs n a t = 0 := by
  funext y; simp [fddProc, hd]

theorem fddProc_encode (b E s h : ℝ) (τ m : Fin np → ℝ) (Wn : ℕ → ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (n : ℕ)
    (l : LIdx K np) :
    fddProc b E s h τ m Wn Vs n (Encodable.encode l) = fddCoord b E s h τ m (Wn n) (Vs (Wn n)) l :=
  funext fun t => fddProc_some b E s h τ m Wn Vs (Encodable.encodek l) t

theorem measurable_fddCoord {b E s h : ℝ} {τ m : Fin np → ℝ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) (l : LIdx K np) {t : ℝ} (ht : 0 ≤ t) :
    Measurable (fddCoord b E s h τ m W Vs l t) := by
  have hj : closeLen s W ≤ ⌊(W : ℝ) * (s + t)⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg W))
  have hc : ∀ c : CIdx K np, Measurable (Modul.zB b E s h τ m W Vs c ⌊(W : ℝ) * (s + t)⌋₊) :=
    fun c => ((Modul.measurable_b3X_past s h τ m hj le_rfl hV c).mono
      (gen_sigma_le W _ np) le_rfl).sub measurable_const
  rcases l with e | k | ij
  · exact hc (Sum.inl e)
  · exact Complex.measurable_ofReal.comp
      ((CapLaw.measurable_physTseq b E s W k).comp (measurable_fst.comp measurable_fst))
  · exact hc (Sum.inr ij)

/-!
## The conditioned law
-/

/-- The Borel cap event on the closed sample. -/
def capM (b E s h : ℝ) (K W np : ℕ) : Set (ProbedPath W np × ℝ) :=
  {y | y.1.1 ∈ ClosedIdent.physCapEventM b E s h K W}

theorem measurableSet_capM (b E s h : ℝ) (K W np : ℕ) : MeasurableSet (capM b E s h K W np) :=
  (measurable_fst.comp measurable_fst) (ClosedIdent.measurableSet_physCapEventM b E s h K W)

/-- The closed law conditioned on the cap event. -/
def condL (b E s h : ℝ) (K W np : ℕ) : Measure (ProbedPath W np × ℝ) :=
  (closedLaw b W np)[|capM b E s h K W np]

theorem capC_ae_eq {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ) :
    {y : ProbedPath W np × ℝ | y.1.1 ∈ physCapEventC b E s h K W} =ᵐ[closedLaw b W np]
      capM b E s h K W np := by
  have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      (closedLaw b W np) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
  exact hq.preimage_ae_eq (ClosedIdent.physCapEvent_ae_eq hb hE1 hE2 s h K)

theorem closedLaw_capM {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ) :
    closedLaw b W np (capM b E s h K W np) = growthPathLaw W b (physCapEventC b E s h K W) := by
  have e := measure_congr (μ := growthPathLaw W b)
    (ClosedIdent.physCapEvent_ae_eq (W := W) hb hE1 hE2 s h K)
  exact (probedPhase_preimage_path b _).trans e.symm

theorem isProbabilityMeasure_condL {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {s h : ℝ}
    (h0 : growthPathLaw W b (physCapEventC b E s h K W) ≠ 0) :
    IsProbabilityMeasure (condL b E s h K W np) := by
  unfold condL
  exact cond_isProbabilityMeasure (by rwa [closedLaw_capM hb hE1 hE2])

/-- **`condObsTestAll` is an expectation under the conditioned law.** -/
theorem condObsTestAll_eq {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ)
    (τ m : Fin np → ℝ) (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    {ι : Type} [Fintype ι] (i : ι → LIdx K np) (u : ι → ℝ≥0)
    (ψ : BoundedContinuousFunction (ι → ℂ) ℝ) :
    condObsTestAll b E s h τ m W Vs i u ψ =
      ∫ y, ψ (fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y) ∂condL b E s h K W np := by
  set f := fun y : ProbedPath W np × ℝ => ψ (fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y)
  have e1 : ∫ y, (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 * f y
      ∂closedLaw b W np = ∫ y in capM b E s h K W np, f y ∂closedLaw b W np := by
    rw [← integral_indicator (measurableSet_capM b E s h K W np)]
    have e2 : (fun y : ProbedPath W np × ℝ =>
        (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 * f y) =
        {y : ProbedPath W np × ℝ | y.1.1 ∈ physCapEventC b E s h K W}.indicator f := by
      funext y
      by_cases hc : y.1.1 ∈ physCapEventC b E s h K W
      · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (show y ∈ {y : ProbedPath W np × ℝ |
          y.1.1 ∈ physCapEventC b E s h K W} from hc), one_mul]
      · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (show y ∉ {y : ProbedPath W np × ℝ |
          y.1.1 ∈ physCapEventC b E s h K W} from hc), zero_mul]
    rw [e2]
    exact integral_congr_ae (indicator_ae_eq_of_ae_eq_set (capC_ae_eq hb hE1 hE2 s h))
  unfold condObsTestAll condL
  simp only [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul]
  rw [e1, ENNReal.toReal_inv, closedLaw_capM hb hE1 hE2,
    div_eq_inv_mul]

/-- **Conditioned bounds from bounds on the cap event.** -/
theorem condL_le {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {s h : ℝ} {c θ : ℝ}
    (hc : 0 < c) (hcap : ENNReal.ofReal c ≤ growthPathLaw W b (physCapEventC b E s h K W))
    {S : Set (ProbedPath W np × ℝ)}
    (hS : closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧ y ∈ S} ≤
      ENNReal.ofReal (c * θ)) :
    condL b E s h K W np S ≤ ENNReal.ofReal θ := by
  rw [condL, cond_apply (measurableSet_capM b E s h K W np)]
  have e : capM b E s h K W np ∩ S =ᵐ[closedLaw b W np]
      {y | y.1.1 ∈ physCapEventC b E s h K W ∧ y ∈ S} :=
    (capC_ae_eq hb hE1 hE2 s h).symm.inter (EventuallyEq.refl _ S)
  rw [measure_congr e, closedLaw_capM hb hE1 hE2]
  exact (mul_le_mul' (ENNReal.inv_le_inv.2 hcap) hS).trans (le_of_eq (CapLaw.ofReal_inv_mul hc))

/-!
## The start bound
-/

/-- **At model time `0` every coordinate is at most `4K + 1`**, almost surely. -/
theorem ae_start_bound {b E s h : ℝ} {τ m : Fin np → ℝ} (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (hτ : ∀ i, s < τ i)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : IsTimeSFrame b E s h K W Vs) :
    ∀ᵐ y ∂closedLaw b W np, ∀ l : LIdx K np, ‖fddCoord b E s h τ m W Vs l 0 y‖ ≤ 4 * K + 1 := by
  have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      (closedLaw b W np) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
  have hK0 : (0 : ℝ) ≤ 4 * K := by positivity
  filter_upwards [StopTail.ae_b3Tr_start_le (m := m) hb hE1 hE2 hW hτ hV,
    hq.ae (FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW)] with y hy hU l
  have hj : ⌊(W : ℝ) * (s + 0)⌋₊ = closeLen s W := by rw [add_zero]
  have hJ : b3JumpAt (K := K) b s τ m W (closeLen s W) = 0 := by
    simp [b3JumpAt]
  have hKJ : b3KJumpAt E s τ m W (closeLen s W) = 0 := by
    simp [b3KJumpAt]
  rcases l with e | k | ij
  · change ‖Modul.zB b E s h τ m W Vs (Sum.inl e) ⌊(W : ℝ) * (s + 0)⌋₊ y‖ ≤ _
    rw [hj, Modul.zB, hJ, hKJ, Modul.cEntry_zero, sub_zero]
    refine ((norm_gramEntry_b3ClosedGramAt_le b E s h τ m W _ Vs y e).trans hy).trans ?_
    linarith
  · change ‖((physTseq b E s W y.1.1 k : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h0 := ClosedSum.physTseq_nonneg (b := b) (E := E) (s := s) (hU (closeLen s W)).1 k
    have h1 := ClosedSum.physTseq_le_one (b := b) (E := E) (s := s) y.1.1 k
    constructor <;> linarith
  · change ‖Modul.zB b E s h τ m W Vs (Sum.inr ij) ⌊(W : ℝ) * (s + 0)⌋₊ y‖ ≤ _
    rw [hj, Modul.zB, hJ, hKJ, Modul.cEntry_zero, sub_zero]
    change ‖b3ClosedKAt b E s h τ m W (closeLen s W) y ij.1 ij.2‖ ≤ _
    rw [b3ClosedKAt_start hτ y]
    simp only [Matrix.zero_apply, norm_zero]
    linarith

/-!
## Modulus and one-time tightness
-/

theorem frameDomain_mono {b E : ℝ} {τ m : Fin np → ℝ} {T T' s h : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) (hT : T ≤ T') : FrameDomain b E τ m T' s h K Vs := by
  obtain ⟨⟨hb0, hb, hE1, hE2, hinj, hτ0, hm, hτT⟩, hrest⟩ := hD
  exact ⟨⟨hb0, hb, hE1, hE2, hinj, hτ0, hm, fun j => (hτT j).trans_le hT⟩, hrest⟩

/-- **The modulus of every coordinate on `[0, T']`**, on the cap event (hypotheses at the horizon
`max (max T s) (s + T')`). -/
theorem fdd_modulus (hS : ComplexClosedSummed) (hL : ComplexClosedLindeberg) {b E : ℝ}
    {τ m : Fin np → ℝ} {T s h : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) (l : LIdx K np) (T' : ℝ) {η θ : ℝ} (hη : 0 < η)
    (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧
        y ∈ {y | ∃ t ∈ Icc 0 T', ∃ t' ∈ Icc 0 T', |t - t'| ≤ δ ∧
          η < ‖fddCoord b E s h τ m W (Vs W) l t y - fddCoord b E s h τ m W (Vs W) l t' y‖}} ≤
        ENNReal.ofReal θ := by
  have hC : ∀ c : CIdx K np, ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧
        y ∈ {y | ∃ t ∈ Icc 0 T', ∃ t' ∈ Icc 0 T', |t - t'| ≤ δ ∧
          η < ‖fddCoord b E s h τ m W (Vs W) (cToL c) t y -
            fddCoord b E s h τ m W (Vs W) (cToL c) t' y‖}} ≤ ENNReal.ofReal θ := by
    intro c
    set Tp := max (max T s) (s + T')
    have hDp := frameDomain_mono hD ((le_max_left T s).trans (le_max_left _ (s + T')))
    have hsTp : s ≤ Tp := (le_max_right T s).trans (le_max_left _ _)
    obtain ⟨δ, hδ, W₀, hW₀⟩ := Modul.modulusS hS hL hDp c le_rfl hsTp hη hθ
    refine ⟨δ, hδ, W₀, fun W hW => (measure_mono ?_).trans (hW₀ W hW)⟩
    rintro y ⟨hcap, t, ht, t', ht', htt, hlt⟩
    rw [fddCoord_cToL, fddCoord_cToL] at hlt
    have hle : ∀ x ∈ Icc (0 : ℝ) T', s + x ∈ Icc s Tp := fun x hx =>
      ⟨by linarith [hx.1], (add_le_add_right hx.2 s).trans (le_max_right _ _)⟩
    exact ⟨hcap, s + t, hle t ht, s + t', hle t' ht', by rwa [add_sub_add_left_eq_sub], hlt⟩
  rcases l with e | k | ij
  · exact hC (Sum.inl e)
  · refine ⟨1, one_pos, 0, fun W _ => ?_⟩
    have : {y : ProbedPath W np × ℝ | y.1.1 ∈ physCapEventC b E s h K W ∧
        y ∈ {y | ∃ t ∈ Icc (0 : ℝ) T', ∃ t' ∈ Icc (0 : ℝ) T', |t - t'| ≤ 1 ∧
          η < ‖fddCoord b E s h τ m W (Vs W) (Sum.inr (Sum.inl k)) t y -
            fddCoord b E s h τ m W (Vs W) (Sum.inr (Sum.inl k)) t' y‖}} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun y ⟨_, t, _, t', _, _, hy⟩ => ?_
      change η < ‖((physTseq b E s W y.1.1 k : ℝ) : ℂ) - ((physTseq b E s W y.1.1 k : ℝ) : ℂ)‖
        at hy
      rw [sub_self, norm_zero] at hy
      exact lt_irrefl _ (hη.trans hy)
    rw [this, measure_empty]; exact zero_le
  · exact hC (Sum.inr ij)

/-- **One-time tightness of every coordinate at `t ≥ 0`** on the cap event (start bound and
chaining). -/
theorem fdd_tight (hS : ComplexClosedSummed) (hL : ComplexClosedLindeberg) {b E : ℝ}
    {τ m : Fin np → ℝ} {T s h : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) (l : LIdx K np) {t : ℝ} (ht : 0 ≤ t) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧
        y ∈ {y | C < ‖fddCoord b E s h τ m W (Vs W) l t y‖}} ≤ ENNReal.ofReal θ := by
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, hsτ, -, -, hVs⟩ := id hD
  obtain ⟨δ, hδ, W₁, hW₁⟩ := fdd_modulus hS hL hD l t one_pos hθ
  obtain ⟨W₂, hW₂⟩ := eventually_atTop.1 (hVs.and (eventually_ge_atTop 1))
  set M : ℕ := ⌈t / δ⌉₊
  have hM : t ≤ 0 + M * δ := by
    have := mul_le_mul_of_nonneg_right (Nat.le_ceil (t / δ)) hδ.le
    rw [div_mul_cancel₀ _ hδ.ne'] at this
    linarith
  refine ⟨4 * K + 1 + M, max W₁ W₂, fun W hW => ?_⟩
  obtain ⟨hV, hW1⟩ := hW₂ W ((le_max_right _ _).trans hW)
  have hnull : closedLaw b W np {y | ¬ ∀ l : LIdx K np,
      ‖fddCoord b E s h τ m W (Vs W) l 0 y‖ ≤ 4 * K + 1} = 0 :=
    ae_iff.1 (ae_start_bound (m := m) hb hE1 hE2 hW1 hsτ hV)
  refine (measure_mono (t := {y | ¬ ∀ l : LIdx K np,
      ‖fddCoord b E s h τ m W (Vs W) l 0 y‖ ≤ 4 * K + 1} ∪
    {y | y.1.1 ∈ physCapEventC b E s h K W ∧
        y ∈ {y | ∃ u ∈ Icc 0 t, ∃ u' ∈ Icc 0 t, |u - u'| ≤ δ ∧
          1 < ‖fddCoord b E s h τ m W (Vs W) l u y - fddCoord b E s h τ m W (Vs W) l u' y‖}})
    ?_).trans ((measure_union_le _ _).trans ?_)
  · rintro y ⟨hcap, hy⟩
    by_contra hno
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_and, not_exists,
      not_lt] at hno
    obtain ⟨h0, h1⟩ := hno
    have hf : ∀ u ∈ Icc (0 : ℝ) t, ∀ u' ∈ Icc (0 : ℝ) t, |u - u'| ≤ δ →
        ‖fddCoord b E s h τ m W (Vs W) l u y - fddCoord b E s h τ m W (Vs W) l u' y‖ ≤ 1 :=
      fun u hu u' hu' huu => h1 hcap u hu u' hu' huu
    have hch := CapLaw.chain_bound hδ hf M t ⟨ht, le_rfl⟩ hM
    have h3 := norm_le_insert' (fddCoord b E s h τ m W (Vs W) l t y)
      (fddCoord b E s h τ m W (Vs W) l 0 y)
    have h4 := h0 l
    have hy' : 4 * (K : ℝ) + 1 + M < ‖fddCoord b E s h τ m W (Vs W) l t y‖ := hy
    linarith
  · rw [hnull, zero_add]
    exact hW₁ W ((le_max_left _ _).trans hW)

end BlockBand.SourceProcess.PhysApprox.B3.Fdd
