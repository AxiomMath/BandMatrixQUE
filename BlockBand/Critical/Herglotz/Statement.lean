module

public import BlockBand.Critical.Herglotz.Atomic
public import BlockBand.Critical.Herglotz.Canonical
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Cauchy

/-!
# Statement of the Herglotz tail lemma

Definitions of the hypotheses `HerglotzTailHypotheses`, the conclusion `HerglotzTailConclusion` and
the statement `HerglotzTailStatement`.

Law and topology conventions:

* Random objects live on a sequence of probability spaces `(Ω N, P N)`. The limit
  `(Ξ, C)` lives on its own probability space `(Ω', P')`. Convergence in law is Mathlib's
  `TendstoInDistribution`, i.e. weak convergence of the image laws. It includes a.e.
  measurability of the random variables.
* Matrices `Matrix (Fin r) (Fin r) ℂ` carry the product topology. Matrix expectations are
  entrywise Bochner integrals.
* `‖v‖² = Σ_i |v_i|²` is the Euclidean norm, not Mathlib's sup norm on `Fin r → ℂ`.
* Locally uniform convergence: for every compact `K ⊆ {Im z > 0}`, the restriction to `K` in
  `C(K, Matrix)` with the compact-open (= uniform) topology and its Borel σ-algebra. It is joint
  with the values at any finite family of real points (`JointValues`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped Matrix NNReal

namespace BlockBand.Critical.Herglotz

open CoareaNative.BlockBand (matrixImaginaryPart)

/-- Restriction to `K` as a continuous map (the zero map if `G` is not continuous on `K`; for the
functions of the lemma it is always continuous on compact subsets of `{Im z > 0}`). -/
def restrictTo {r : ℕ} (G : ℂ → Matrix (Fin r) (Fin r) ℂ) (K : Set ℂ) :
    C(K, Matrix (Fin r) (Fin r) ℂ) := by
  classical
  exact if h : ContinuousOn G K then ⟨K.domRestrict G, h.domRestrict⟩ else 0

/-- Values at `k` real points together with the restriction to a compact set `K`:
`(Fin k → Matrix) × C(K, Matrix)`, with the product of the product and compact-open topologies,
and its Borel σ-algebra. -/
def JointValues (r k : ℕ) (K : Set ℂ) : Type :=
  (Fin k → Matrix (Fin r) (Fin r) ℂ) × C(K, Matrix (Fin r) (Fin r) ℂ)

instance (r k : ℕ) (K : Set ℂ) : TopologicalSpace (JointValues r k K) :=
  inferInstanceAs (TopologicalSpace ((Fin k → Matrix (Fin r) (Fin r) ℂ) ×
    C(K, Matrix (Fin r) (Fin r) ℂ)))

instance (r k : ℕ) (K : Set ℂ) : MeasurableSpace (JointValues r k K) := borel _

instance (r k : ℕ) (K : Set ℂ) : BorelSpace (JointValues r k K) := ⟨rfl⟩

/-- `((G (x a))_a, G|_K)`. -/
def jointValues {r k : ℕ} (G : ℂ → Matrix (Fin r) (Fin r) ℂ) (x : Fin k → ℝ) (K : Set ℂ) :
    JointValues r k K :=
  ((fun a => G (x a)), restrictTo G K)

/-- The Euclidean squared norm `Σ_i |v_i|²` as a scale parameter. -/
def euclidSqNorm {r : ℕ} (v : Fin r → ℂ) : ℝ≥0 :=
  ⟨∑ i, ‖v i‖ ^ 2, Finset.sum_nonneg fun _ _ => sq_nonneg _⟩

/-- **Hypotheses of the Herglotz tail lemma** for random finite atomic Herglotz
functions `F N : Ω N → AtomicHerglotz r` and a decorated sine process `Ξ` on `(Ω', P')`.

* `measurable_eval` ("random"): `(ω, z) ↦ F_N(ω)(z)` is jointly measurable, entrywise.
* `poles` (hypothesis 1, "on every compact real interval their pole configurations and matrix
  residues converge to those of the canonical Cauchy series, including multiplicities"): for every
  finite family of compactly supported continuous tests `f_k` on `ℝ × Matrix`, the vague
  coordinates `Σ_{poles x} f_k(x, μ_N({x}))` converge jointly in law to
  `Σ_j f_k(x_j, π⁻¹ g_j g_j^*)`.
* `mean` (hypothesis 2): for each `Y > 0`, `E Im F_N(iY) → I_r` entrywise.
* `boundary` (hypothesis 3): for every real `x` and every deterministic `v ∈ ℂ^r`, the real
  boundary value `v^* F_N(x) v` converges in law to the real Cauchy law of center `0` and scale
  `‖v‖²` (Mathlib `cauchyMeasure 0 ‖v‖²`, density `‖v‖²/(π(t² + ‖v‖⁴))`). -/
structure HerglotzTailHypotheses (r : ℕ) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (F : ∀ N, Ω N → AtomicHerglotz r) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))) : Prop where
  measurable_eval : ∀ N (i j : Fin r),
    Measurable fun p : Ω N × ℂ => (F N p.1).eval p.2 i j
  poles : ∀ (m : ℕ)
      (f : Fin m → CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ),
    TendstoInDistribution (fun N ω k => (F N ω).atomSum (f k)) atTop
      (fun ω k => ∫ p, f k (p.1, canonicalResidue p.2) ∂(Ξ ω).measure) P P'
  mean : ∀ Y : ℝ, 0 < Y → ∀ i j : Fin r,
    Tendsto (fun N => ∫ ω, matrixImaginaryPart ((F N ω).eval ((Y : ℂ) * Complex.I)) i j ∂P N)
      atTop (𝓝 ((1 : Matrix (Fin r) (Fin r) ℂ) i j))
  boundary : ∀ (x : ℝ) (v : Fin r → ℂ),
    TendstoInDistribution (fun N ω => ((F N ω).quadForm v x).re) atTop id P
      (ProbabilityTheory.cauchyMeasure 0 (euclidSqNorm v))

/-- **Conclusion of the Herglotz tail lemma**: `F_N ⇒ 𝖢_r` locally uniformly in
the upper half-plane and jointly at every finite set of real points. For every `k`, real points
`x : Fin k → ℝ` and compact `K ⊆ {Im z > 0}`, the joint law of `((F_N(x_a))_a, F_N|_K)` converges
weakly to that of `((C(x_a))_a, C|_K)`. -/
def HerglotzTailConclusion (r : ℕ) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (F : ∀ N, Ω N → AtomicHerglotz r) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (C : Ω' → ℂ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ (k : ℕ) (x : Fin k → ℝ) (K : Set ℂ), IsCompact K → K ⊆ {z : ℂ | 0 < z.im} →
    TendstoInDistribution (fun N ω => jointValues (F N ω).eval x K) atTop
      (fun ω => jointValues (C ω) x K) P P'

/-- **The Herglotz tail lemma**, as a statement. For every
`r`, every sequence of random finite atomic `r × r` Herglotz functions `F_N` on probability spaces
`(Ω N, P N)`, and every realization `(Ω', P', Ξ, C)` of the canonical series `𝖢_r`
(`IsCanonicalCauchy`), hypotheses 1–3 (`HerglotzTailHypotheses`) imply the conclusion. No
stationarity of `F_N` and no independence of its remote tail is assumed. -/
def HerglotzTailStatement (r : ℕ) : Prop :=
  ∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (F : ∀ N, Ω N → AtomicHerglotz r)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))) (C : Ω' → ℂ → Matrix (Fin r) (Fin r) ℂ),
    IsCanonicalCauchy r P' Ξ C → HerglotzTailHypotheses r P F P' Ξ →
      HerglotzTailConclusion r P F P' C

end BlockBand.Critical.Herglotz
