module

public import BlockBand.Transmission.DualAtomless.A3Random
public import BlockBand.Transmission.Dual.GDelStep

/-!
# The random-start deletion process with a conditionally atomless lifetime

`DelFrom D₀ q` is the random-start existence statement proved by induction on `q`
(`delFrom_succ`). It is strengthened here:
* **`DelFromA D₀ q`**: `DelFrom D₀ q` (same witness shape) together with: for `q ≥ 1` and every
  measurable `c : S → ℝ≥0`, a.s. `ζ(ω) ≠ c(π ω)` (`ζ = dualExtinction N`). This is "the
  lifetime has no atom, conditionally on the old state".
* `dualExtinction_gN_top`, **`dualExtinction_gN_coe`**: for the glued process, `ζ = ⊤` if the
  first-stage deletion time `ρ` is infinite, and `ζ = ρ + ζ'` (`ζ'` the lifetime of the
  restart) if `ρ` is finite.
* **`delFromA_succ`**: `DelFromA D₀ k → DelFromA D₀ (k+1)` for `D₀ > 0`, with the witness of
  `delFrom_succ`. At `k = 0` the restart is empty, `ζ = ρ = ζ_chart`, and the atom clause is
  the random-start atomlessness `ae_zeta_ne`. At `k ≥ 1` it is the induction hypothesis at the
  `𝓖'₀`-measurable time `c' = c ∘ fst − ρ`, a function of the restart's old state `π'`.
* `delFromA_all : ∀ q, DelFromA D₀ q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualAtomless

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.G
open scoped NNReal ENNReal

/-- **The random-start deletion process with a conditionally atomless lifetime.** -/
def DelFromA (D0 : ℝ) (q : ℕ) : Prop :=
  ∀ (S : Type) (_ : MeasurableSpace S) (μ : Measure S), IsProbabilityMeasure μ →
    ∀ ξ : S → Fin (q + q) → ℝ, Measurable ξ → (∀ s, ξ s ∈ flatChamber q) →
      ∃ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω) (π : Ω → S)
        (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ),
        IsDualFrom P 𝓖 D0 q N X Y ∧ P.map π = μ ∧ MeasurableSpace.comap π inferInstance ≤ 𝓖 0 ∧
          (∀ ω, N 0 ω = q ∧ dualCoordOf q (X 0 ω) (Y 0 ω) = ofFlat q (ξ (π ω))) ∧
          (1 ≤ q → ∀ c : S → ℝ≥0, Measurable c →
            ∀ᵐ ω ∂P, dualExtinction N ω ≠ (c (π ω) : ℝ≥0∞))

theorem delFromA_zero (D0 : ℝ) : DelFromA D0 0 := by
  intro S _ μ hμ ξ hξ hξc
  obtain ⟨Ω, m, 𝓖, P, π, N, X, Y, h1, h2, h3, h4⟩ := delFrom_zero D0 S inferInstance μ hμ ξ hξ hξc
  exact ⟨Ω, m, 𝓖, P, π, N, X, Y, h1, h2, h3, h4, fun h => absurd h (by omega)⟩

/-!
## The lifetime of the glued process
-/

section Glued

variable {k : ℕ} {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S}
  [IsProbabilityMeasure μ] {ξ : S → Fin ((k + 1) + (k + 1)) → ℝ} (F : B1R D0 (k + 1) μ ξ)
  {Ω : Type} {π' : Ω → ΩR S (k + 1)} {N' : ℝ≥0 → Ω → ℕ}

theorem dualExtinction_gN_top {ω : Ω} (h : F.rho1 (π' ω) = ⊤) :
    dualExtinction (F.gN π' N') ω = ⊤ := by
  refine iInf₂_eq_top.2 fun t ht => absurd ht ?_
  rw [F.gN_of_lt π' N' (h ▸ WithTop.coe_lt_top t)]; omega

/-- **The glued lifetime is `ρ + ζ'`.** -/
theorem dualExtinction_gN_coe {ω : Ω} {r : ℝ≥0} (h : F.rho1 (π' ω) = r) :
    dualExtinction (F.gN π' N') ω = (r : ℝ≥0∞) + dualExtinction N' ω := by
  have hθ : F.theta π' ω = r := by simp only [B1R.theta, h]; rfl
  unfold dualExtinction
  simp_rw [ENNReal.add_iInf]
  refine le_antisymm (le_iInf₂ fun s hs => ?_) (le_iInf₂ fun t ht => ?_)
  · have hle : F.rho1 (π' ω) ≤ ((r + s : ℝ≥0) : WithTop ℝ≥0) := by
      rw [h]; exact WithTop.coe_le_coe.2 le_self_add
    have h0 : F.gN π' N' (r + s) ω = 0 := by
      rw [F.gN_of_le π' N' hle, hθ, add_tsub_cancel_left]; exact hs
    exact (iInf₂_le (r + s) h0).trans_eq (ENNReal.coe_add r s)
  · have hle : F.rho1 (π' ω) ≤ t := by
      by_contra hlt
      rw [F.gN_of_lt π' N' (not_le.1 hlt)] at ht; omega
    rw [F.gN_of_le π' N' hle, hθ] at ht
    have hrt : r ≤ t := by rw [h] at hle; exact WithTop.coe_le_coe.1 hle
    calc ⨅ s, ⨅ (_ : N' s ω = 0), (r : ℝ≥0∞) + s ≤ (r : ℝ≥0∞) + ((t - r : ℝ≥0) : ℝ≥0∞) :=
          iInf₂_le (t - r) ht
      _ = t := by rw [← ENNReal.coe_add, add_tsub_cancel_of_le hrt]

end Glued

theorem dualExtinction_eq_zero_of_level_zero {Ω : Type} {N : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (h : N 0 ω = 0) : dualExtinction N ω = 0 :=
  le_antisymm ((iInf₂_le (0 : ℝ≥0) h).trans_eq ENNReal.coe_zero) bot_le

/-!
## The induction step
-/

/-- **The gluing step with the atom clause.** -/
theorem delFromA_succ {D0 : ℝ} (hD0 : 0 < D0) (k : ℕ) (hk : DelFromA D0 k) :
    DelFromA D0 (k + 1) := by
  intro S _ μ hμ ξ hξ hξc
  obtain ⟨F⟩ := nonempty_b1R (μ := μ) (q := k + 1) hD0 hξ
  obtain ⟨Ω, m, 𝓖, P, π', N', X', Y', hD', hmap, hcomap, h0, hA⟩ :=
    hk (ΩR S (k + 1)) inferInstance (PR μ (k + 1)) inferInstance F.surv F.measurable_surv
      F.surv_mem
  have := hD'.prob
  have hπ := B1R.measurable_of_comap hcomap
  have hlev : ∀ t ω, N' t ω ≤ k := hD'.level_le
  refine ⟨Ω, m, F.gFilt hcomap hD0 hξ hξc, P, fun ω => (π' ω).1, F.gN π' N',
    F.gC π' N' F.sX X', F.gC π' N' F.sY Y',
    { prob := hD'.prob
      adapted := F.adapted_g hcomap hD0 hξ hξc hD'
      start := Eventually.of_forall (F.gN_zero π' N')
      bound := fun ω => (F.gN_zero π' N' ω).le
      paths := fun ω => F.isDeletionPath_g hξc (hD'.paths ω) (h0 ω)
      martingale := fun q hq hqk f hf hfc hfs => ?_ }, ?_, ?_,
    fun ω => ⟨F.gN_zero π' N' ω, F.dualCoordOf_g_zero π' N' X' Y' hξc ω⟩, fun _ c hc => ?_⟩
  · rcases Nat.lt_or_ge q (k + 1) with h | h
    · exact F.martingale_g_low hcomap hD0 hξ hξc hD' h0 hq (by omega) hf hfc hfs
    · obtain rfl : q = k + 1 := le_antisymm hqk h
      exact F.martingale_g_top hcomap hD0 hξ hξc hmap hlev hf hfc hfs
  · rw [show (fun ω => (π' ω).1) = Prod.fst ∘ π' from rfl, ← Measure.map_map measurable_fst hπ,
      hmap]
    show (μ.prod _).map Prod.fst = μ
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  · have h1 : Measurable[comapFilt hπ (𝓖R μ (k + 1)) 0] fun ω => (π' ω).1 :=
      (measurable_fst_zero μ (q := k + 1) measurable_id).comp (comap_measurable π')
    exact (h1.mono (le_glueFilt _ _ _ 0) le_rfl).comap_le
  · -- the atom clause
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have hz : ∀ᵐ x ∂PR μ (0 + 1), F.zeta x ≠ (c x.1 : WithTop ℝ≥0) :=
        ae_zeta_ne hD0 hξ hξc F hc
      rw [← hmap] at hz
      filter_upwards [ae_of_ae_map hπ.aemeasurable hz] with ω hω heq
      by_cases htop : F.rho1 (π' ω) = ⊤
      · rw [dualExtinction_gN_top F htop] at heq; exact ENNReal.coe_ne_top heq.symm
      · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 htop
        have h00 : N' 0 ω = 0 := Nat.le_zero.1 (hlev 0 ω)
        rw [dualExtinction_gN_coe F hr.symm, dualExtinction_eq_zero_of_level_zero h00,
          add_zero] at heq
        have hgood := (F.rho1_eq_coe hr.symm).1.1
        have hz' : F.zeta (π' ω) = r := by
          have := hr.symm; simpa only [B1R.rho1, hgood, ↓reduceIte] using this
        exact hω (hz'.trans (WithTop.coe_inj.2 (ENNReal.coe_inj.1 heq)))
    · set c' : ΩR S (k + 1) → ℝ≥0 := fun x => c x.1 - (F.rho1 x).untopA
      have hc' : Measurable c' :=
        (hc.comp measurable_fst).sub (F.measurable_rho1 hD0 hξ hξc).untopA
      filter_upwards [hA hk1 c' hc'] with ω hω heq
      by_cases htop : F.rho1 (π' ω) = ⊤
      · rw [dualExtinction_gN_top F htop] at heq; exact ENNReal.coe_ne_top heq.symm
      · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 htop
        rw [dualExtinction_gN_coe F hr.symm] at heq
        apply hω
        have hu : (F.rho1 (π' ω)).untopA = r := by rw [← hr]; rfl
        show dualExtinction N' ω = ((c (π' ω).1 - (F.rho1 (π' ω)).untopA : ℝ≥0) : ℝ≥0∞)
        rw [hu, ENNReal.coe_sub, ← heq, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]

/-- **`DelFromA` at every level.** -/
theorem delFromA_all {D0 : ℝ} (hD0 : 0 < D0) : ∀ q, DelFromA D0 q := fun q => by
  induction q with
  | zero => exact delFromA_zero D0
  | succ k ih => exact delFromA_succ hD0 k ih

end BlockBand.Transmission.DualAtomless
