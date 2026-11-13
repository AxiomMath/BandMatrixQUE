module

public import BlockBand.Transmission.Dual.GB1RGood

/-!
# The corner and the survivors of stage 1, measurably

* `gseq n ω = Yf n (e_n ω) ω` is measurable (`Yf n` is jointly measurable, `e_n` a stopping
  time) and equals `Z (e_n)`; since `e_n ↑ ζ` strictly (`tendsto_e_nhdsLT`), `gseq n ω → c`, the
  corner of Theorem G (`tendsto_gseq`);
* `corner ω = lim_n gseq n ω` on `E` (`0` off `E`) is measurable (`measurable_corner`), and on
  `E` it is the left limit of `Z` at `ζ` and a paired corner (`corner_spec`);
* **`surv`**: the survivors `rightPart (corner ∘ (slotEquiv 0).symm)` on `E`, the chamber point
  `chartQ q 0` off `E`; measurable and in `𝒞_q` at every `ω` (`measurable_surv`, `surv_mem`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {q : ℕ} {D0 : ℝ}
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : S → Fin ((q + 1) + (q + 1)) → ℝ}

theorem coe_untopA_ne_top {a : WithTop ℝ≥0} (h : a ≠ ⊤) : (a.untopA : WithTop ℝ≥0) = a := by
  obtain ⟨b, rfl⟩ := WithTop.ne_top_iff_exists.1 h
  rfl

namespace B1R

variable (F : B1R D0 (q + 1) μ ξ)

/-- The finite-lifetime good set. -/
def finE : Set (ΩR S (q + 1)) := F.good ∩ {ω | F.zeta ω < ⊤}

theorem measurableSet_finE : MeasurableSet F.finE := by
  refine F.measurableSet_good.inter ?_
  have e : {ω | F.zeta ω < ⊤} = ⋃ m : ℕ, {ω | F.zeta ω ≤ (m : ℝ≥0)} := by
    ext ω; simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 h.ne
      obtain ⟨m, hm⟩ := exists_nat_ge r
      exact ⟨m, hr ▸ WithTop.coe_le_coe.2 hm⟩
    · rintro ⟨m, hm⟩; exact hm.trans_lt (WithTop.coe_lt_top _)
  rw [e]
  exact MeasurableSet.iUnion fun m => (𝓖R μ (q + 1)).le _ _ (F.measurableSet_zeta_le _)

/-- `Yf n` at its exit time. -/
def gseq (n : ℕ) (ω : ΩR S (q + 1)) : Fin ((q + 1) + (q + 1)) → ℝ :=
  F.Yf n (F.e n ω).untopA ω

theorem measurable_gseq (n : ℕ) : Measurable (F.gseq n) := by
  have hprog : IsStronglyProgressive (𝓖R μ (q + 1)) (F.Yf n) :=
    StronglyAdapted.isStronglyProgressive_of_continuous (fun t => F.stronglyMeasurable_Yf n t)
      fun ω => F.continuous_Yf n ω
  exact (measurable_stoppedValue hprog (F.isStoppingTime_e n)).mono
    (F.isStoppingTime_e n).measurableSpace_le le_rfl

theorem tendsto_e_nhdsLT {ω : ΩR S (q + 1)} (hc : F.IsConsAt ω) {ζ : ℝ≥0}
    (hζ : F.zeta ω = ζ) : Tendsto (fun n => (F.e n ω).untopA) atTop (𝓝[<] ζ) := by
  have hlt : ∀ n, F.e n ω < ζ := fun n => hζ ▸ F.e_lt_zeta hc (hζ ▸ WithTop.coe_lt_top ζ) n
  have hfin : ∀ n, F.e n ω ≠ ⊤ := fun n => ne_top_of_lt (hlt n)
  have hcoe : ∀ n, (((F.e n ω).untopA : ℝ≥0) : WithTop ℝ≥0) = F.e n ω := fun n =>
    coe_untopA_ne_top (hfin n)
  have hmono : Monotone fun n => (F.e n ω).untopA := fun n m h => by
    rw [← WithTop.coe_le_coe, hcoe, hcoe]; exact (hc n m h).1
  have hbdd : BddAbove (range fun n => (F.e n ω).untopA) :=
    ⟨ζ, by
      rintro _ ⟨n, rfl⟩
      have h := (hcoe n).trans_lt (hlt n)
      exact (by exact_mod_cast h : (F.e n ω).untopA < ζ).le⟩
  have hsup : ⨆ n, (F.e n ω).untopA = ζ := by
    rw [← WithTop.coe_inj, WithTop.coe_iSup _ hbdd, ← hζ]
    simp only [hcoe]; rfl
  refine tendsto_nhdsWithin_iff.2 ⟨hsup ▸ tendsto_atTop_ciSup hmono hbdd,
    Eventually.of_forall fun n => by
      have h := (hcoe n).trans_lt (hlt n)
      exact (by exact_mod_cast h : (F.e n ω).untopA < ζ)⟩

theorem tendsto_gseq {ω : ΩR S (q + 1)} (hω : ω ∈ F.finE) :
    ∃ c, IsCorner q c ∧ Tendsto (fun t => F.Z t ω) (𝓝[<] (F.zeta ω).untopA) (𝓝 c) ∧
      Tendsto (fun n => F.gseq n ω) atTop (𝓝 c) := by
  obtain ⟨hc, hG⟩ := F.good_spec hω.1
  have hζ : F.zeta ω = ((F.zeta ω).untopA : ℝ≥0) := (coe_untopA_ne_top hω.2.ne).symm
  obtain ⟨c, hcor, hT⟩ := hG _ hζ
  refine ⟨c, hcor, hT, (hT.comp (F.tendsto_e_nhdsLT hc hζ)).congr fun n => ?_⟩
  have hfin : F.e n ω ≠ ⊤ := ne_top_of_le_ne_top hω.2.ne (F.e_le_zeta n ω)
  simp only [Function.comp_apply, gseq]
  exact F.Z_eq hc (coe_untopA_ne_top hfin).le

open scoped Classical in
/-- The corner at `ζ` (on `finE`; `0` elsewhere). -/
def corner (ω : ΩR S (q + 1)) : Fin ((q + 1) + (q + 1)) → ℝ :=
  if ω ∈ F.finE then limUnder atTop fun n => F.gseq n ω else 0

theorem corner_spec {ω : ΩR S (q + 1)} (hω : ω ∈ F.finE) : IsCorner q (F.corner ω) ∧
    Tendsto (fun t => F.Z t ω) (𝓝[<] (F.zeta ω).untopA) (𝓝 (F.corner ω)) := by
  obtain ⟨c, hcor, hT, hg⟩ := F.tendsto_gseq hω
  have : F.corner ω = c := by simp only [corner, hω, ↓reduceIte]; exact hg.limUnder_eq
  rw [this]; exact ⟨hcor, hT⟩

theorem measurable_corner : Measurable F.corner := by
  classical
  refine measurable_of_tendsto_metrizable (f := fun n ω => if ω ∈ F.finE then F.gseq n ω else 0)
    (fun n => Measurable.ite F.measurableSet_finE (F.measurable_gseq n) measurable_const)
    (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ F.finE
  · obtain ⟨c, -, -, hg⟩ := F.tendsto_gseq hω
    simp only [corner, hω, ↓reduceIte]
    rw [hg.limUnder_eq]; exact hg
  · simp only [corner, hω, ↓reduceIte]; exact tendsto_const_nhds

open scoped Classical in
/-- **The survivors** (a chamber point of level `q` at every `ω`). -/
def surv (ω : ΩR S (q + 1)) : Fin (q + q) → ℝ :=
  if ω ∈ F.finE then rightPart (F.corner ω ∘ (slotEquiv (0 : Fin (q + 1))).symm) else chartQ q 0

theorem surv_mem (ω : ΩR S (q + 1)) : F.surv ω ∈ flatChamber q := by
  unfold surv; split_ifs with hω
  · exact (F.corner_spec hω).1.2.2
  · exact chartQ_mem 0

theorem measurable_surv : Measurable F.surv := by
  classical
  have h : Measurable fun ω => rightPart (F.corner ω ∘ (slotEquiv (0 : Fin (q + 1))).symm) :=
    measurable_pi_iff.2 fun j => (measurable_pi_apply _).comp F.measurable_corner
  exact Measurable.ite F.measurableSet_finE h measurable_const

end B1R

end BlockBand.Transmission.Dual.G
