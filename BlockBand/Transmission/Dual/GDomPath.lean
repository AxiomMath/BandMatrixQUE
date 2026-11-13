module

public import BlockBand.Transmission.Dual.GDomSeq
public import BlockBand.Transmission.Dual.GJLemma1

/-!
# The stop sequences of the laws `P^{H_p}` and `Q^{(j)}`

Level `p = q + 1`; `W : ℕ → Set` is an increasing sequence of open sets (later an exhaustion of
`𝒞_{q+1}`), `t₀` a horizon.
* `B1Family.cpath m ω`: the `m`-th flat path of a `B1Family` as a continuous path;
  `B1Family.stopSeq W t₀ r ω n = pstop (W n) t₀ (cpath (r n) ω)` with radii `r n`.
* `slotCPath`, `slotSeq`: the same for the combined labelled path of `Q^{(j)}`
  (`slotPath j (F₁.Yf a) (F₂.Yf b)` on `Ωq 1 × Ωq q`).
* Both are measurable, and are stop sequences (`IsStopSeq`, a.s.) as soon as the radii are
  monotone and large enough that `W n` (resp. its pair/rest projections) lies in the image of
  the chart ball of radius `r n` (resp. `a n`, `b n`): radius consistency `ae_consistent` plus
  `pstop_congr`, `pstop_pstop`. For the product this uses the projections of the compacts onto
  the pair and the rest (`exitTimeFrom_slotPath_le_left/right`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Levy BlockBand.Transmission.Dual
open scoped NNReal

variable {q : ℕ} {D0 : ℝ} {t₀ : ℝ≥0}

/-!
## A single family
-/

namespace B1Family

variable {z : Fin (q + q) → ℝ} (F : B1Family D0 q z)

/-- The `m`-th flat path as a continuous path. -/
def cpath (m : ℕ) (ω : Ωq q) : CPath (q + q) := ⟨fun t => F.Yf m t ω, F.continuous_Yf m ω⟩

theorem measurable_Yf' (m : ℕ) (t : ℝ≥0) : Measurable (F.Yf m t) :=
  (F.stronglyMeasurable_Yf m t).measurable.mono ((𝓖q q).le t) le_rfl

theorem measurable_cpath (m : ℕ) : Measurable (F.cpath m) :=
  Measurable.subtype_mk (measurable_pi_iff.2 fun t => F.measurable_Yf' m t)

/-- The stop sequence with radii `r`. -/
def stopSeq (W : ℕ → Set (Fin (q + q) → ℝ)) (t₀ : ℝ≥0) (r : ℕ → ℕ) (ω : Ωq q) :
    ℕ → CPath (q + q) := fun n => pstop (W n) t₀ (F.cpath (r n) ω)

theorem measurable_stopSeq {W : ℕ → Set (Fin (q + q) → ℝ)} (hW : ∀ n, IsOpen (W n))
    (r : ℕ → ℕ) : Measurable (F.stopSeq W t₀ r) :=
  measurable_pi_iff.2 fun n => (measurable_pstop (hW n) t₀).comp (F.measurable_cpath _)

/-- Radius consistency at a fixed `ω`. -/
def IsConsAt (ω : Ωq q) : Prop :=
  ∀ n m : ℕ, n ≤ m → F.e n ω ≤ F.e m ω ∧
    ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ F.e n ω → F.X n t ω = F.X m t ω

theorem ae_isConsAt (hD0 : 0 < D0) : ∀ᵐ ω ∂Pq q, F.IsConsAt ω := F.ae_consistent hD0

theorem Yf_eq_of_le {ω : Ωq q} (hc : F.IsConsAt ω) {m m' : ℕ} (h : m ≤ m') {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e m ω) : F.Yf m' t ω = F.Yf m t ω := by
  simp only [Yf]; rw [(hc m m' h).2 t ht]

theorem pexit_cpath_le {m : ℕ} {W : Set (Fin (q + q) → ℝ)}
    (hW : W ⊆ chartQ q '' Metric.ball 0 m) (ω : Ωq q) : pexit W (F.cpath m ω) ≤ F.e m ω :=
  F.exitTimeFrom_le_e hW ω

/-- **The stop sequence of a family is a stop sequence** (monotone large radii). -/
theorem isStopSeq_stopSeq (hD0 : 0 < D0) {W : ℕ → Set (Fin (q + q) → ℝ)}
    (hW : ∀ n, IsOpen (W n)) (hmono : Monotone W) {r : ℕ → ℕ} (hr : Monotone r)
    (hball : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n)) :
    IsStopSeq (Pq q) W t₀ (F.stopSeq W t₀ r) := by
  intro k n hkn
  filter_upwards [F.ae_isConsAt hD0] with ω hc
  show pstop (W k) t₀ (F.cpath (r k) ω) = pstop (W k) t₀ (pstop (W n) t₀ (F.cpath (r n) ω))
  rw [pstop_pstop (hW k) (hmono hkn)]
  refine (pstop_congr (hW k) t₀ fun u hu => ?_).symm
  exact F.Yf_eq_of_le hc (hr hkn)
    ((hu.trans (min_le_left _ _)).trans (F.pexit_cpath_le (hball k) ω))

end B1Family

/-!
## The combined labelled path of `Q^{(j)}`
-/

section Slot

variable {Ω₁ Ω₂ : Type*} {Y₁ : ℝ≥0 → Ω₁ → Fin (1 + 1) → ℝ} {Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ}

theorem slotPath_comp_symm (j : Fin (q + 1)) (t : ℝ≥0) (x : Ω₁ × Ω₂) :
    slotPath j Y₁ Y₂ t x ∘ (slotEquiv j).symm = prodPath Y₁ Y₂ t x := by
  funext i; simp [slotPath]

theorem left_slotPath (j : Fin (q + 1)) (t : ℝ≥0) (x : Ω₁ × Ω₂) :
    leftPart (slotPath j Y₁ Y₂ t x ∘ (slotEquiv j).symm) = Y₁ t x.1 := by
  rw [slotPath_comp_symm, leftPart_prodPath]

theorem right_slotPath (j : Fin (q + 1)) (t : ℝ≥0) (x : Ω₁ × Ω₂) :
    rightPart (slotPath j Y₁ Y₂ t x ∘ (slotEquiv j).symm) = Y₂ t x.2 := by
  rw [slotPath_comp_symm, rightPart_prodPath]

/-- The combined path leaves `W` no later than its pair leaves `U₁`. -/
theorem exitTimeFrom_slotPath_le_left {W : Set (Fin ((q + 1) + (q + 1)) → ℝ)}
    {U₁ : Set (Fin (1 + 1) → ℝ)} (j : Fin (q + 1))
    (hWU : ∀ w ∈ W, leftPart (w ∘ (slotEquiv j).symm) ∈ U₁) (x : Ω₁ × Ω₂) :
    exitTimeFrom W (slotPath j Y₁ Y₂) x ≤ exitTimeFrom U₁ Y₁ x.1 :=
  le_iInf₂ fun t ht => iInf₂_le t fun hmem => ht (by
    have := hWU _ hmem; rwa [left_slotPath] at this)

/-- The combined path leaves `W` no later than its rest leaves `U₂`. -/
theorem exitTimeFrom_slotPath_le_right {W : Set (Fin ((q + 1) + (q + 1)) → ℝ)}
    {U₂ : Set (Fin (q + q) → ℝ)} (j : Fin (q + 1))
    (hWU : ∀ w ∈ W, rightPart (w ∘ (slotEquiv j).symm) ∈ U₂) (x : Ω₁ × Ω₂) :
    exitTimeFrom W (slotPath j Y₁ Y₂) x ≤ exitTimeFrom U₂ Y₂ x.2 :=
  le_iInf₂ fun t ht => iInf₂_le t fun hmem => ht (by
    have := hWU _ hmem; rwa [right_slotPath] at this)

theorem continuous_slotPath (j : Fin (q + 1)) {x : Ω₁ × Ω₂}
    (h₁ : Continuous fun t => Y₁ t x.1) (h₂ : Continuous fun t => Y₂ t x.2) :
    Continuous fun t => slotPath j Y₁ Y₂ t x := by
  have hp : Continuous fun t => prodPath Y₁ Y₂ t x := by
    refine continuous_pi fun k => Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [prodPath, Fin.append_left]; exact (continuous_apply i).comp h₁
    · simp only [prodPath, Fin.append_right]; exact (continuous_apply i).comp h₂
  exact continuous_pi fun i => (continuous_apply _).comp hp

end Slot

variable {z₁ : Fin (1 + 1) → ℝ} {z₂ : Fin (q + q) → ℝ}

/-- The combined labelled path of radii `(a, b)` as a continuous path. -/
def slotCPath (j : Fin (q + 1)) (F₁ : B1Family D0 1 z₁) (F₂ : B1Family D0 q z₂) (a b : ℕ)
    (x : Ωq 1 × Ωq q) : CPath ((q + 1) + (q + 1)) :=
  ⟨fun t => slotPath j (F₁.Yf a) (F₂.Yf b) t x,
    continuous_slotPath j (F₁.continuous_Yf a x.1) (F₂.continuous_Yf b x.2)⟩

theorem measurable_slotCPath (j : Fin (q + 1)) (F₁ : B1Family D0 1 z₁) (F₂ : B1Family D0 q z₂)
    (a b : ℕ) : Measurable (slotCPath j F₁ F₂ a b) := by
  refine Measurable.subtype_mk (measurable_pi_iff.2 fun t => ?_)
  have hp : Measurable (prodPath (F₁.Yf a) (F₂.Yf b) t) :=
    (measurable_prodPath (𝓖₁ := 𝓖q 1) (𝓖₂ := 𝓖q q) (F₁.stronglyMeasurable_Yf a)
      (F₂.stronglyMeasurable_Yf b) t).mono ((prodFiltration (𝓖q 1) (𝓖q q)).le t) le_rfl
  exact measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp hp

/-- The stop sequence of `Q^{(j)}` with radii `(a, b)`. -/
def slotSeq (j : Fin (q + 1)) (F₁ : B1Family D0 1 z₁) (F₂ : B1Family D0 q z₂)
    (W : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)) (t₀ : ℝ≥0) (a b : ℕ → ℕ)
    (x : Ωq 1 × Ωq q) : ℕ → CPath ((q + 1) + (q + 1)) :=
  fun n => pstop (W n) t₀ (slotCPath j F₁ F₂ (a n) (b n) x)

theorem measurable_slotSeq (j : Fin (q + 1)) (F₁ : B1Family D0 1 z₁) (F₂ : B1Family D0 q z₂)
    {W : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)} (hW : ∀ n, IsOpen (W n)) (a b : ℕ → ℕ) :
    Measurable (slotSeq j F₁ F₂ W t₀ a b) :=
  measurable_pi_iff.2 fun n => (measurable_pstop (hW n) t₀).comp (measurable_slotCPath _ _ _ _ _)

/-- **The `Q^{(j)}` stop sequence is a stop sequence** (monotone large radii). -/
theorem isStopSeq_slotSeq (hD0 : 0 < D0) (j : Fin (q + 1)) (F₁ : B1Family D0 1 z₁)
    (F₂ : B1Family D0 q z₂) {W : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)}
    (hW : ∀ n, IsOpen (W n)) (hmono : Monotone W) {a b : ℕ → ℕ} (ha : Monotone a)
    (hb : Monotone b)
    (hball : ∀ n, ∀ w ∈ W n, leftPart (w ∘ (slotEquiv j).symm) ∈ chartQ 1 '' Metric.ball 0 (a n) ∧
      rightPart (w ∘ (slotEquiv j).symm) ∈ chartQ q '' Metric.ball 0 (b n)) :
    IsStopSeq ((Pq 1).prod (Pq q)) W t₀ (slotSeq j F₁ F₂ W t₀ a b) := by
  intro k n hkn
  filter_upwards [ae_fst (Q₂ := Pq q) (F₁.ae_isConsAt hD0),
    ae_snd (Q₁ := Pq 1) (F₂.ae_isConsAt hD0)] with x hc₁ hc₂
  show pstop (W k) t₀ (slotCPath j F₁ F₂ (a k) (b k) x) =
    pstop (W k) t₀ (pstop (W n) t₀ (slotCPath j F₁ F₂ (a n) (b n) x))
  rw [pstop_pstop (hW k) (hmono hkn)]
  refine (pstop_congr (hW k) t₀ fun u hu => ?_).symm
  have hu' : (u : WithTop ℝ≥0) ≤ exitTimeFrom (W k) (slotPath j (F₁.Yf (a k)) (F₂.Yf (b k))) x :=
    hu.trans (min_le_left _ _)
  have h₁ : (u : WithTop ℝ≥0) ≤ F₁.e (a k) x.1 :=
    (hu'.trans (exitTimeFrom_slotPath_le_left j (fun w hw => (hball k w hw).1) x)).trans
      (F₁.exitTimeFrom_le_e subset_rfl x.1)
  have h₂ : (u : WithTop ℝ≥0) ≤ F₂.e (b k) x.2 :=
    (hu'.trans (exitTimeFrom_slotPath_le_right j (fun w hw => (hball k w hw).2) x)).trans
      (F₂.exitTimeFrom_le_e subset_rfl x.2)
  show slotPath j (F₁.Yf (a n)) (F₂.Yf (b n)) u x = slotPath j (F₁.Yf (a k)) (F₂.Yf (b k)) u x
  simp only [slotPath, prodPath]
  rw [F₁.Yf_eq_of_le hc₁ (ha hkn) h₁, F₂.Yf_eq_of_le hc₂ (hb hkn) h₂]

end BlockBand.Transmission.Dual.G
