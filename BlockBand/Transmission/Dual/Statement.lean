module

public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# The dual boundary lemma: the statement

## The mathematical statement

For a finite `p` and an interior ordered start `z = (x, y)`, the `H_p`-transformed killed
kernel `Q_p` has its entire deficit carried by the paired-corner density `J_p` of the paired
deletion; `J_p ≥ 0` and `Q_p(t)J_p(s) = J_p(t+s)`. The path reaches its finite lifetime only at
the paired corner, with strictly ordered positive survivors a.s. Deleting the zero pair and
restarting, with an absorbing empty state, defines a unique conservative strong Markov law for
every finite `p`, with generator `𝒟_p` in each interior chamber; it has no same-species
collision, other finite-boundary loss, simultaneous multiple deletion, or explosion at
infinity. Moreover `𝒟_pR = 0` and `P(σ_K ≤ T) ≤ R₀/K`. The law proof uses only the qualitative
consequence `P(σ_K ≤ t) → 0`, which already follows from the class (`R` is continuous on
`[0, T]` along deletion paths, so `sup_{[0,T]} R < ∞` a.s.).

**Scope.** `DualBoundaryLawStatement` formalizes the *law clauses* of the lemma; the kernel
clauses and the strong Markov property at general stopping times are not stated here.

## Lean reading

* **Uniqueness in law** (`unique`) is the equality of the laws of the truncated state path
  `dualState N X Y : Ω → (ℝ≥0 → ℕ × (ℕ → ℝ) × (ℕ → ℝ))` (product σ-algebra), for any two
  realizations on any two filtered probability spaces. Truncation is needed: the coordinates
  of index `≥ N_t` are unconstrained by the class, so the untruncated law is not determined.
  `dualState` is measurable for every realization (`measurable_dualState_of_isDual`),
  so neither side of `unique` is a junk zero measure.

## Omissions

* **Strong Markov at arbitrary stopping times.** The class contains the strong Markov
  restart at every deletion time `σ_q`. The strong Markov property at a general stopping time
  needs a measurable start-point kernel `z ↦ law_z`; the duality proof uses only the stopped
  martingale problems.
* **Kernel clauses.** The statements about the killed kernel `Q_p` and the density `J_p` are not
  formalized.

Neither omission weakens a clause that is used: `TransmissionLawContract.law` needs exactly
`HasDualDeletionProcess` (here `exists_`); its duality proof uses the class, and of the
quantitative estimate only the qualitative consequence `P(σ_K ≤ t) → 0` of `conservative`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

/-!
## Vocabulary: the truncated state path
-/

/-- A dual state: the level `n` and the two coordinate sequences. -/
abbrev DualState := ℕ × (ℕ → ℝ) × (ℕ → ℝ)

/-- Truncation of a coordinate sequence at level `n`: entries of index `≥ n` are set to `0`. -/
def truncCoord (n : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun i => if i < n then x i else 0

/-- The truncated state path `t ↦ (N_t, X_t|_{<N_t}, Y_t|_{<N_t})` of a realization. Its law
is the object determined by the dual boundary lemma. -/
def dualState {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (ω : Ω) :
    ℝ≥0 → DualState :=
  fun t => (N t ω, truncCoord (N t ω) (X t ω), truncCoord (N t ω) (Y t ω))

/-!
## The statement
-/

/-- * `exists_`: for `D₀ > 0`, every `p` and every ordered interior start `(x, y)`, the
  conservative deletion law exists (`HasDualDeletionProcess`);
* `unique`: any two realizations (`IsDualDeletionProcess`, on any filtered probability
  spaces) have the same law of the truncated state path `dualState`;
* `conservative`: every realization satisfies `P(∃ t ≤ T, R_t ≥ K) ≤ R₀/K` with
  `R = Σ_{i < N}(x_i + y_i)` and `R₀ = Σ_i (x_i + y_i)`.
The kernel clauses and the strong Markov property at general stopping times are not part of the
statement (see the module docstring). -/
structure DualBoundaryLawStatement : Prop where
  exists_ : ∀ D0 : ℝ, 0 < D0 → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
    HasDualDeletionProcess D0 x y
  unique : ∀ D0 : ℝ, 0 < D0 → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
    ∀ (Ω₁ : Type) (m₁ : MeasurableSpace Ω₁) (𝓖₁ : Filtration ℝ≥0 m₁) (P₁ : Measure Ω₁)
      (N₁ : ℝ≥0 → Ω₁ → ℕ) (X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ)
      (Ω₂ : Type) (m₂ : MeasurableSpace Ω₂) (𝓖₂ : Filtration ℝ≥0 m₂) (P₂ : Measure Ω₂)
      (N₂ : ℝ≥0 → Ω₂ → ℕ) (X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ),
      IsDualDeletionProcess P₁ 𝓖₁ D0 x y N₁ X₁ Y₁ →
      IsDualDeletionProcess P₂ 𝓖₂ D0 x y N₂ X₂ Y₂ →
      P₁.map (dualState N₁ X₁ Y₁) = P₂.map (dualState N₂ X₂ Y₂)
  conservative : ∀ D0 : ℝ, 0 < D0 → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ),
      IsDualDeletionProcess P 𝓖 D0 x y N X Y →
      ∀ K T : ℝ, 0 < K →
        P {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ K ≤ dualTotal (N t ω) (X t ω) (Y t ω)} ≤
          ENNReal.ofReal ((∑ i, (x i + y i)) / K)

/-!
## Sanity lemmas for the statement
-/

section Sanity

variable {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

theorem truncCoord_of_lt {n i : ℕ} (x : ℕ → ℝ) (h : i < n) : truncCoord n x i = x i := by
  simp [truncCoord, h]

theorem truncCoord_zero (x : ℕ → ℝ) : truncCoord 0 x = 0 := by
  funext i; simp [truncCoord]

/-- `R` sees only the coordinates below the level, so it is a function of `dualState`. -/
theorem dualTotal_truncCoord (n : ℕ) (x y : ℕ → ℝ) :
    dualTotal n (truncCoord n x) (truncCoord n y) = dualTotal n x y := by
  unfold dualTotal
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.1 hi
  rw [truncCoord_of_lt x hi', truncCoord_of_lt y hi']

theorem dualTotal_dualState (ω : Ω) (t : ℝ≥0) :
    dualTotal (dualState N X Y ω t).1 (dualState N X Y ω t).2.1 (dualState N X Y ω t).2.2 =
      dualTotal (N t ω) (X t ω) (Y t ω) :=
  dualTotal_truncCoord _ _ _

theorem measurable_truncCoord_comp [MeasurableSpace Ω] {n : Ω → ℕ} {x : Ω → ℕ → ℝ}
    (hn : Measurable n) (hx : Measurable x) :
    Measurable fun ω => truncCoord (n ω) (x ω) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hs : MeasurableSet {ω | i < n ω} := hn (measurableSet_Ioi (a := i))
  exact Measurable.ite hs ((measurable_pi_apply i).comp hx) measurable_const

/-- The truncated state path is measurable once the coordinates are. -/
theorem measurable_dualState [MeasurableSpace Ω] (hN : ∀ t, Measurable (N t))
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t)) :
    Measurable (dualState N X Y) := by
  refine measurable_pi_iff.2 fun t => ?_
  exact (hN t).prodMk ((measurable_truncCoord_comp (hN t) (hX t)).prodMk
    (measurable_truncCoord_comp (hN t) (hY t)))

/-- For every realization the law in `unique` is the push-forward by a measurable map (no junk
measure). -/
theorem measurable_dualState_of_isDual
    {m : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ} {p : ℕ}
    {x y : Fin p → ℝ} (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y) :
    Measurable (dualState N X Y) :=
  measurable_dualState (fun t => (h.adapted t).1.mono (𝓖.le t) le_rfl)
    (fun t => (h.adapted t).2.1.mono (𝓖.le t) le_rfl)
    (fun t => (h.adapted t).2.2.mono (𝓖.le t) le_rfl)

/-- At the top level `q = N₀` the entrance value `dualEntranceValue` is the initial value
`f(Z₀)`, so the level-`p` clause of `IsDualDeletionProcess.martingale` is the usual martingale
problem `f(Z_t)1{N_t = p} - f(Z₀) - ∫_0^t 𝒟_p f(Z_u) 1{N_u = p} du`.
-/
theorem dualEntranceValue_of_start {q : ℕ} (f : DualCoord q → ℝ) (t : ℝ≥0) (ω : Ω)
    (h0 : N 0 ω = q) :
    dualEntranceValue f N X Y t ω = f (dualCoordOf q (X 0 ω) (Y 0 ω)) := by
  have hmem : (0 : ℝ≥0) ∈ {s : ℝ≥0 | N s ω ≤ q} := by simp [h0]
  have hent : dualEntrance N q ω = 0 :=
    le_antisymm (csInf_le (OrderBot.bddBelow _) hmem) zero_le
  have hex : ∃ u ≤ t, N u ω ≤ q := ⟨0, zero_le, h0.le⟩
  simp only [dualEntranceValue, hex, ↓reduceIte, hent]
  simp [dualLift, h0]

/-- The constant empty path is a deletion path. -/
theorem isDeletionPath_empty (x y : ℝ≥0 → ℕ → ℝ) : IsDeletionPath (fun _ => 0) x y where
  antitone := fun _ _ _ => le_rfl
  chamber := fun t => by
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  rightCont := fun _ => Eventually.of_forall fun _ => rfl
  cont := fun _ _ _ _ i hi => absurd hi (Nat.not_lt_zero i)
  deletion := fun τ hτ q hq _ => by
    have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ⟩
    obtain ⟨u, hu⟩ := hq.exists
    exact absurd hu.symm (Nat.succ_ne_zero q)

/-- **The `p = 0` case of `exists_`**: the constant empty path on a one-point space is a
realization of `IsDualDeletionProcess` (so `HasDualDeletionProcess` is satisfiable at `p = 0`).
-/
theorem hasDualDeletionProcess_zero (D0 : ℝ) (x y : Fin 0 → ℝ) :
    HasDualDeletionProcess D0 x y := by
  refine ⟨Unit, ⊤, ⊤, Measure.dirac (), fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
  exact
    { prob := inferInstance
      adapted := fun _ => ⟨measurable_const, measurable_const, measurable_const⟩
      start := Eventually.of_forall fun _ => ⟨rfl, fun i => i.elim0⟩
      paths := Eventually.of_forall fun _ => isDeletionPath_empty _ _
      martingale := fun q hq hqp => absurd (hq.trans hqp) (by omega) }

end Sanity

end BlockBand.Transmission.Dual
